# Lazer builds whose gameplay logic matches the pinned 2026.1005.0-lazer

Written 2026-10-21. Pinned build: `2026.1005.0-lazer` = ppy/osu `9a10d935b0` (LAZER_COMMIT), osu-framework 2026.921.1.
Sources: the `/api/v2/changelog` streams `lazer` and `tachyon`, git history of ppy/osu and ppy/osu-framework
between neighbouring release tags (blobless partial clones, compared with `git log`/`git diff --stat`), and the
`client_version` that lazer writes into every `.osr` (`LegacyReplaySoloScoreInfo.ClientVersion`).

## score.build_id is a per-platform build row

The `build_id` on a score is **not** the changelog build id. The changelog says `2026.1005.0` = build 8969. Scores
carry 8963/8964/8967/8968 instead, and `/changelog/8967?key=id` returns 404. Each row is one client binary per
platform. The API doesn't expose the mapping, so `difftest/fetch_v2.py` learns it: for each new `build_id` it
downloads up to 2 replays and reads `client_version`. Observed so far (table `builds` in `data/index_v2.sqlite`):

| build_id | client_version | class |
|---|---|---|
| 8816 | 2026.711.0-lazer-windows | X |
| 8845 | 2026.726.0-lazer-windows | X |
| 8871 / 8873 / 8874 | 2026.804.2-lazer-{macos,windows,android} | X |
| 8936 / 8938 | 2026.921.0-lazer-{windows,macos} | **A** |
| 8963 / 8964 / 8967 / 8968 | 2026.1005.0-lazer-{linux,macos,windows,android} | **A** (pinned) |
| 8981 / 8983 / 8984 | 2026.1013.0-tachyon-{macos,linux,windows} | B |

All platform builds of one version come from the same git tag. The platform-specific code (desktop vs mobile
hosts and input handlers) only changes how *live* input is sampled. It does not change how a recorded replay is
judged. The recorded frames are the replay.

## Class A: gameplay-identical (used as ground truth)

`2026.918.0-tachyon`, `2026.920.0-lazer`, `2026.921.0-lazer`, `2026.1005.0-lazer`, on any platform.

Lineage: `2026.918.0-tachyon` → (+4 commits) `2026.920.0-lazer` → (+1) `2026.921.0-lazer` → (+1) `2026.1005.0-lazer`.
Each tag is an ancestor of the next.

| range | osu changes (full diffstat) | osu-framework |
|---|---|---|
| 918.0-tachyon → 920.0-lazer | ranked-play chat focus fix, "block PMs" setting UI, localisation source, `ppy.osu.Game.Resources` 2026.909.0→2026.918.0, framework bump. Files: `RankedPlayChatDisplay.cs`, `AlertsAndPrivacySettings.cs`, a test, `osu.Game.csproj`, `osu.{Android,iOS}.props` | 2026.917.0 → 2026.918.0: only `Audio/Track/Waveform.cs` (waveform preallocation; editor/visual) |
| 920.0 → 921.0-lazer | framework bump only (`osu.Game.csproj`, props) | 2026.918.0 → 2026.921.0: only `osu.Framework.csproj` (SPIRV shader-compiler package downgrade; rendering only) |
| 921.0 → 1005.0-lazer | framework bump only (`osu.Game.csproj`) | 2026.921.0 → 2026.921.1: image decode type restriction (`TextureUpload.cs`, `AppleTextureLoaderStore.cs`) and clipboard (`MacOS/SDL3/WindowsClipboard.cs`). Security hotfix; no input, clock, transform or gameplay code |

None of these touch `osu.Game.Rulesets.Osu/`, `osu.Game/Rulesets/{Scoring,Judgements,Objects,UI,Replays,Mods}/`,
`osu.Game/Beatmaps/`, `osu.Game/Scoring/`, `osu.Game/Screens/Play/`, or any framework input, timing or transform
code. The only resource change (Game.Resources) is samples and textures. Gameplay hit areas don't depend on it:
the argon and triangles skins are code, and a user's skin is unknown anyway (ISSUES G4). `2026.918.0-tachyon` has
not been seen in the feed yet.

I did not extend the set further back. `2026.911.0-tachyon → 918.0` touches `DrawableRuleset.cs`,
`RulesetInputManager.cs`, `PoolableDrawableWithLifetime.cs` and an osu-framework jump 2026.901.0→917.0, and would
need a line-by-line audit. `2026.804.2-lazer` and older lazer releases are many tachyon cycles behind.

## Class B: conditionally equivalent (collected under a 10% quota, analysed separately, never ground truth)

`2026.1001.0-tachyon`, `2026.1004.0-tachyon`, `2026.1005.1-tachyon`, `2026.1013.0-tachyon`. They branch off
`2026.921.0-lazer`, so `2026.1005.0-lazer` is *not* their ancestor. Changes in judgement-relevant paths since 921.0:

- **`ConvertHitObjectParser`: object positions are clamped to [0, 512] during parsing** (#38844, in 1001.0+). Same
  result as the pinned build only for maps whose x/y are all in [0, 512].
- `APIMod.ToMod()` was replaced by an extension method (#38986, 1013.0), and `Mod` now implements `IConfiguredMod`
  (#38961). These are intended to be behaviour-preserving, but mod-settings deserialisation now goes through new code.
- `ScoreProcessor`: parameter renames only. `DrawableRuleset`: an audio mixer for hitsound volume (#38990; audio only).
- Drain-time thresholds (#38987) and flashlight difficulty attributes (#38982): difficulty/pp only.
- osu-framework 2026.930.0 → 2026.1008.0 (SDL3 raw keyboard on Windows, which affects live input only;
  ThrottledFrameClock/VRR; a RectangleF interpolation typo fix; BASS update). Not audited line by line.

## Class X: everything else

Rejected. Their replays are deleted after probing.

## Default

If the build is unknown or unmapped, only class A counts. `fetch_v2.py` decides from the replay's own `client_version`
(minus the platform suffix), never from the build id alone.
