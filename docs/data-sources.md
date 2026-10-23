# Data sources for differential testing (replays + beatmaps)

Researched 2026-10-21 using docs plus a few small live calls. The API key is in `~/.osu_credentials`
(`OSU_API_V1_KEY`). It is never written into the repo or into logs.

## TL;DR
- **Real stable replays:** osu! API v1 `get_replay` works with our key. It returns only the base64 LZMA
  frame stream, and `difftest/fetch_v1.py` rebuilds full `.osr` files from it. The rate limit is 10/min,
  so about 14k replays/day.
- **v1 has only osu!stable scores.** No lazer-set scores appear in `get_scores`, `get_user_best` or
  `get_user_recent`, and `get_replay` on a lazer score id returns `{"error":"Replay not available."}`.
  Lazer reads stable replays as legacy scores and **adds the Classic mod** (`LegacyScoreDecoder`:
  version < 30000000 ⇒ `+CL`). Their server stats are stable judgements, so they are a sanity check
  only and must not be treated as the oracle. The oracle is headless lazer run on the replay.
- **Lazer replays** need v2 `GET /api/v2/scores/{id}/download` with an OAuth token. We have no v2
  credentials. Unauthenticated requests return 403 (api/v2) or 401 (web route). Untested option: a
  client-credentials token from an OAuth app registered in account settings would probably work, since
  the controller code allows API requests without a user.
- **Beatmaps:** `https://osu.ppy.sh/osu/{beatmap_id}` returns raw `.osu` text with no auth. We can also
  bulk download `data.ppy.sh/YYYY_MM_DD_osu_files.tar.bz2` (about 1.4 GB, all ranked/loved `.osu`).
- **data.ppy.sh dumps contain no replays.** They are MySQL table dumps only (see below).

## osu! API v1 (https://github.com/ppy/osu-api/wiki)
Global documented limit: "1200 requests per minute, with a burst capability of up to 200 beyond that".
No rate-limit headers are returned (checked: none in the response headers).

| endpoint | key params | notes |
|---|---|---|
| `get_beatmaps` | `since` (MySQL date, ranked-date ≥), `s`, `b`, `u`, `m`, `a` (include converts, default 0), `h` (md5), `mods`, `limit` ≤ 500 | gives `file_md5`, `difficultyrating`, `count_normal/slider/spinner`, `hit_length`, `max_combo`, `approved` (1 ranked, 2 approved, 3 qualified, 4 loved) |
| `get_scores` | `b` (required), `u`, `m`, `mods` (exact enabled_mods match), `type`, `limit` ≤ 100 | fields: `score_id, score, username, user_id, maxcombo, count50/100/300, countmiss, countkatu, countgeki, perfect, enabled_mods, date, rank, pp, replay_available` |
| `get_user_best` | `u`, `m`, `type`, `limit` ≤ 100 | same score fields plus `beatmap_id`; stable only |
| `get_user_recent` | `u`, `m`, `type`, `limit` ≤ 50 | last 24h; stable only (it was empty for a lazer-only player) |
| `get_replay` | `s` = score_id (or `b`+`u`[+`mods`]), `m`, `type` | **10 requests/minute**; "not intended for batch retrievals". Returns `{"content": <base64>, "encoding": "base64"}` or `{"error":"Replay not available."}` |

Observations from the live calls:
- `get_replay` content is the raw LZMA-alone stream: 5 property bytes, then int64 uncompressed size,
  then compressed data. Python can read it with `lzma.decompress(..., format=lzma.FORMAT_ALONE)`. The
  decompressed text is `w|x|y|keys,` frames ending in the `-12345|0|0|<rng seed>` frame. There is **no .osr header**.
- `replay_available` was `1` for nearly all top-50 scores we sampled (top 50/100 boards). Some
  mod-filtered results had `0`.
- v1 `score_id` is the *legacy* stable id. The public web page `https://osu.ppy.sh/scores/osu/{legacy_id}`
  (no auth) embeds `json-show` with the solo-score id, `legacy_score_id`, lazer-converted `statistics`
  (e.g. `{"great":1982,"ok":1}`), `maximum_statistics`, mods incl. `CL`, and standardised `total_score`.
  These numbers are converted from the stats, not replayed, but they are useful as a second check.
- The web endpoint `https://osu.ppy.sh/beatmaps/{id}/scores?mode=osu` (no auth, JSON) lists the top 50
  including **lazer scores** (`build_id` set, `legacy_score_id` null) with full lazer statistics
  (`slider_tail_hit`, `large_tick_hit`, `small_bonus`, `ignore_hit`, ...). These are the exact targets
  for our evaluator, but their replays need v2 auth.

### Reconstructing a full .osr (as done in `fetch_v1.py::build_osr`)
Field order matches `osu.Game/Scoring/Legacy/LegacyScoreDecoder.cs`. All values are little-endian.
A string is `0x0b` + ULEB128 length + UTF-8, or `0x00` for null.

| field | type | source |
|---|---|---|
| mode | byte | 0 |
| version | int32 | not in v1. We use the play date `yyyymmdd`, clamped ≥ 20140721. It must stay < 30000000 so lazer treats the replay as legacy (+CL). |
| beatmap md5 | string | `get_beatmaps.file_md5`. Lazer looks the beatmap up by this hash, so it must equal the md5 of the `.osu` we downloaded. The script checks it (`osu_status`). |
| player | string | `username` |
| replay md5 | string | not available. Lazer ignores it, so we write an approximation of stable's recipe. |
| n300, n100, n50, geki, katu, miss | uint16 ×6 | `count300/100/50/countgeki/countkatu/countmiss` |
| score | int32 | `score` |
| max combo | uint16 | `maxcombo` |
| perfect | bool | `perfect` |
| mods | int32 | `enabled_mods` |
| life bar | string | empty (not available) |
| timestamp | int64 .NET ticks | `date`, treated as UTC (unverified, but irrelevant for judging) |
| replay data | int32 len + bytes | decoded `get_replay` content, as is |
| online score id | int64 (version ≥ 20140721) | `score_id` |

Old stable files can carry trailing bytes, which lazer ignores. Note that for beatmap file version < 5,
lazer applies `EARLY_VERSION_TIMING_OFFSET` (+24 ms) to frames.

## Beatmap files
- `https://osu.ppy.sh/osu/{beatmap_id}` returns `text/plain` with `content-disposition: attachment`. It
  needs no auth and returns no rate-limit headers. There is no documented limit; the script uses
  1 request/s. The md5 of the download matched `file_md5` in every sampled case.
- data.ppy.sh `*_osu_files.tar.bz2` (2026_09_01: 1.43 GB) holds all ranked/approved/loved `.osu`
  files. Use it for a large crawl so we don't hit `/osu/` thousands of times.

## data.ppy.sh dumps (https://data.ppy.sh, licence: statistical analysis/testing only, no redistribution)
Monthly `YYYY_MM_DD_performance_{osu,taiko,catch,mania}_{top_1000,top_10000,random_10000}.tar.bz2`
(osu top_1000 is about 1.3 GB, top_10000 about 5.5 GB) and `*_osu_files.tar.bz2`. The full listing of
`2026_09_01_performance_taiko_top_1000` (layout is identical across rulesets) has 13 SQL files:
`osu_beatmap_difficulty(_attribs)`, `osu_beatmap_failtimes`, `osu_beatmap_performance_blacklist`,
`osu_beatmaps`, `osu_beatmapsets`, `osu_counts`, `osu_difficulty_attribs`, `osu_scores_<mode>_high`
(stable high scores), `osu_user_beatmap_playcount`, `osu_user_stats_<mode>`, `sample_users`, `scores`
(lazer `scores` table: `data` JSON with statistics, maximum_statistics, mods incl. settings; plus
`legacy_score_id`, `has_replay`, `build_id`).
**No replay files are included.** The `scores` table is still valuable. It gives (score id → lazer
statistics/mods) for top players, including lazer scores, and could drive a v2 download if we ever get
credentials.

## Other public replay sources
- **circleguard/circlecore** `tests/resources/` (GitHub): about 511 osu!std `.osr` (legit 88+53,
  stealing 306, timewarped 39, relax 5, auto/cursordance 15, ...). Mostly stable with the beatmap ids in
  the names. Good for edge cases such as timewarp (frame-time manipulation) and auto/cursordance (perfect
  plays). Beatmaps must be fetched separately by md5 (`get_beatmaps?h=`).
- **kszlim/osu-replay-parser** `tests/resources/`: 7 files, including `lazer_standard_format.osr`
  (lazer v30000000, osu!std), `replay.osr` (Cookiezi FREEDOM DiVE, v20140226) and an old replay-id format.
- No Kaggle or HuggingFace osu! replay dataset turned up in a quick search.
- **Lazer repo** (`lazer/`, pinned): **no osu!std `.osr`**. There are only
  `osu.Game.Tests/Resources/Replays/{taiko-replay, taiko-replay-with-legacy-online-id,
  taiko-replay-with-new-online-id, mania-replay}.osr`. The osu! ruleset tests build replays in code
  (`TestSceneLegacyHitPolicy`, `TestSceneLegacyReplayPlayback`, `TestSceneSliderInput` etc. use
  frame lists, which is a good source of hand-crafted edge cases). The `.osu` test files are:
  - `osu.Game.Rulesets.Osu.Tests/Resources/Testing/Beatmaps/`: `basic, colinear-perfect-curve,
    diffcalc-test, multi-segment-slider, nan-slider, old-stacking, repeat-slider, slider-paths-edge-case,
    slider-ticks, slider-ticks-edge-case, uneven-repeat-slider, very-fast-slider, zero-length-sliders,
    801165, 1124896, 1341554, 2593923` (most have `*-expected-conversion.json`)
  - `osu.Game.Rulesets.Osu.Tests/Resources/SampleLookups/osu-hitobject-beatmap-custom-sample-bank.osu`
  - `osu.Game.Tests/Resources/*.osu` (about 45 decoder tests, e.g. `Soleily - Renatus (Gamu) [Insane].osu`,
    `Within Temptation - The Unforgiving (Armin) [Marathon].osu`, `beatmap-version-4.osu`,
    `spinner-between-objects.osu`, `break-between-objects.osu`) and `Archives/*.osz`.
  - The `ppy.osu.Game.Resources` nuget only has the intro-track `.osz` files.

## Downloader: `difftest/fetch_v1.py` (stdlib only)
```
python3 difftest/fetch_v1.py all --count 50 --per-map 3 --max 150   # select/score/osu/replays, resumable
python3 difftest/fetch_v1.py discover --pages 20                    # grow the candidate pool
python3 difftest/fetch_v1.py replays --max 600                      # ~1h at 10/min
python3 difftest/fetch_v1.py verify                                 # parse all .osr, cross-check index
python3 difftest/fetch_v1.py export --out data/index.jsonl
python3 -I difftest/osr_check.py data/replays/*.osr                 # standalone parser
```
- `discover` pulls 500-map windows from `get_beatmaps since=<random date>` (m=0, a=0, approved 1/2).
- `select` round-robins over buckets of stars (<2..7+) × hit length (short/mid/long) × slider-heavy
  (≥50% sliders) / spinners (≥2).
- `scores` runs `get_scores` twice per map: the top 50, plus 50 filtered by one mod combo from a
  rotation (NM, HD, HR, DT, HDHR, HDDT, EZ, HT, NF, FL, SO, HRDT, ...). It marks `--per-map` wanted
  replays, distinct mods first.
- `replays` paces calls to 6.5 s, applies exponential backoff on 429/5xx/network errors, and records
  status `ok | unavailable | error` (errors are retried on the next run).
- State lives in `data/index.sqlite` (`beatmaps`, `scores` with all server stats + raw JSON). Writes are
  atomic (`.part` + rename), and files already on disk are skipped.
- Tested 2026-10-21 on 5 maps / 5 replays (mods 72, 600, 1624; 2.2★–5.2★). All 5 `.osr` decode and
  match the index, and all `.osu` md5s matched. **Still to do:** confirm lazer's `LegacyScoreDecoder`
  imports these files once the oracle harness exists.
