# End-to-end model: `OsuModel.Eval` (`.osu` + `.osr` → result)

`OsuModel.Eval.evaluate : Env → ByteArray → ByteArray → Options → Schedule → Except Rejection Result`
(`model/OsuModel/Eval.lean`) composes the beatmap model, the `.osr` decoder, the adapter and the simulation:

```
beatmap bytes ── LegacyBeatmapDecoder.decode ──────────────────────────────┐  (OsuModel.Beatmap)
.osr bytes ───── Osr.decode: container, LZMA (trusted), lazer score JSON ──┤  (OsuModel.Replay.Osr)
                 decode-time GetPlayableBeatmap(bitfield mods) — can only throw   (LegacyScoreDecoder.cs:94)
                 resolveMods (oracle --mods / --replace-mods / --no-classic; Autoplay check)
                 getPlayableBeatmap(gameplay mods) ─ toSimPlayable ─────────┤  (OsuModel.Eval.Adapter)
                 Replay.decode frame text (v<5 offset) ────────────────────┤  (OsuModel.Replay.Frames)
                 Config.ofMods, steps(schedule), Sim.run ──────────────────┘  (OsuModel.Sim)
```

* `Env` — the fixed environment (D10) as data: `OsuModel.Eval.defaultEnv` (`Eval/Env.lean`, the bits of
  `difftest/env-1024x768.json`).
* `Options` — the oracle's mod options (`oracle/Program.cs` `ResolveMods`): `modsOverride` (`--mods`, APIMods decoded
  with `APIMod.ToMod`; each replaces a decoded mod with the same acronym or is appended; unknown acronym → reject),
  `replaceMods`, `noClassic`. Then `Player`'s `DeepClone` (identity on the decoded settings).
* `Schedule` — `kind catchup|perframe|dense1ms` or `explicit refs` (D9; equivalence is claimed per schedule).
* `Result` — oracle schema fields: decoded / effective mods, `is_legacy_score`, true gameplay rate, schedule
  (r0, end, gameplay start, last frame time, reference and step counts), per fail semantics (live / ReplayPlayer,
  the latter `none` = "same_as_live" exactly when the oracle prints that) the score/health state, maximum
  statistics, and the processor-order judgement list.
* `Rejection` — `stage` + `reason` for every input on which lazer throws (see "Rejections").

Executable: `evaltest BEATMAP.osu REPLAY.osr [--schedule S|explicit:FILE] [--mods JSON] [--replace-mods]
[--no-classic] [--no-judgements] [--steps] [--timing] [--dump-playable PATH]` (`model/EvalTest/Main.lean`); prints the
oracle's JSON schema with doubles as raw IEEE bits (`"0x…"`) and mods as acronym lists + decoded settings.

## `.osr` decoding (`model/OsuModel/Replay/Osr.lean`)

| lazer (`osu.Game/…`, 2026.1005.0) | Lean |
|---|---|
| `IO/Legacy/SerializationReader.cs:28-63` `ReadString` (0 byte = null), `ReadByteArray` (<0 null), `ReadDateTime` (negative ticks → IOException; > MaxValue → ArgumentOutOfRange); BCL `BinaryReader` (`Read7BitEncodedInt` ≤5 bytes, `ReadBytes` short at EOF, EndOfStream) | `readString`, `readByteArray`, `readDateTime`, `read7BitEncodedInt`, `readBytes`, `readLE` |
| `Scoring/Legacy/LegacyScoreDecoder.cs:47-118` field order; `GetRuleset` (oracle: only id 0) | `readContainer` |
| `:56` `IsLegacyScore = version < FIRST_LAZER_VERSION (30000000)` (`LegacyScoreEncoder.cs:74`) | `DecodedScore.isLegacyScore` |
| `:88` `OsuRuleset.ConvertFromLegacyMods` (`osu.Game.Rulesets.Osu/OsuRuleset.cs:96-148`) | `convertFromLegacyMods` (NC⊃DT, PF⊃SD, CN⊃AT; default settings) |
| `:91-92` auto `ModClassic` for stable | `decode` (`bitfieldMods`) |
| `:94` decode-time `GetPlayableBeatmap(bitfield mods)` | `Eval.evaluate` (only its failure is observable; skipped when identical to the gameplay playable's mods; unseeded RD/TP dropped) |
| `:98` `beatmapOffset = BeatmapVersion < 5 ? 24 : 0` | `Replay.decode t beatmapVersion` |
| `:107-118` online id width by version, score info for version ≥ 30000001 | `readContainer` |
| `:120-121`, `:168-193` `readCompressedData` (≥5 property bytes, 8 size bytes, `LzmaStream`), `StreamReader.ReadToEnd` | `readCompressedText` (LZMA via `lzmaAloneDecode`, then `Beatmap.streamReaderDecode`; fast path for BOM-less valid UTF-8) |
| `:123-146` `JsonConvert.DeserializeObject<LegacyReplaySoloScoreInfo>`; `Mods = readScore.Mods.Select(m => m.ToMod(ruleset))` | `decodeScoreInfo`, `apiModToMod` (`Settings.toMod` = `APIMod.ToMod`), `checkScoreInfo` |
| `:268-352` frames | `OsuModel.Replay.decode` (`Replay/Frames.lean`, sim agent) |

**What in the lazer score JSON matters for evaluation:** only `mods` (acronyms + settings): it replaces the bitfield
mods entirely (absent key → empty list; a stable-style bitfield in a lazer replay is ignored then). `statistics`,
`maximum_statistics`, `rank`, `online_id`, `user_id`, `client_version`, `total_score_without_mods`, `pauses` only populate
the decoded `ScoreInfo`, which playback never reads (the ScoreProcessor recomputes everything; maxima come from the
simulated autoplay). They are type-checked only because a Newtonsoft failure aborts the import. `IsLegacyScore`
(version) matters: Classic auto-add, and Relax's `Update` is a no-op for non-legacy scores (`OsuModRelax.cs:75-76`).

### Trust boundary: LZMA

`c/lzma_shim.c` (`osu_lzma_alone_decode`, ~60 lines) calls the system liblzma (xz-utils 5.4.5, `liblzma-dev`,
statically linked into `evaltest` only; `lakefile.lean` target `lzma_shim.o`). Lazer uses SharpCompress' managed
`LzmaStream` on the same `.lzma` "alone" format. Assumed equal on well-formed streams (every corpus replay decodes
to identical frames — checked implicitly: the judgement lists match). On corrupt/truncated streams lazer may return
partial data or throw differently; the model rejects ("lzma: data error"/"truncated input"). Output is bounded
(256 MiB).

## Adapter (`model/OsuModel/Eval/Adapter.lean`)

`toSimPlayable : Beatmap.PlayableBeatmap → Sim.Playable`: field-by-field the C# getters the oracle's
`--dump-playable` reads (`oracle/Dump.cs:68-215`); `CreateJudgement()` max/min results from the kind, Classic slider
behaviour and the strict-tracking tail (`judgementOf`, with source lines). `playableJson` writes the adapter output in
the oracle's dump format (keys the sim reads; `fade_in`, `judgement`, `repeat_count`, `tick_distance*`,
`generate_ticks`, `end_position` are not part of the sim interface).

## Rejections (ISSUES G12)

The model rejects (stage, reason) exactly where it can determine that lazer throws, and in the documented
non-modelled cases:

| stage | cause | lazer |
|---|---|---|
| beatmap-decode | decoder errors (Beatmap model), non-osu! ruleset map | throws / converts (not modelled) |
| replay-decode | EOF in header, bad 7-bit length, negative/huge date ticks, ruleset ≠ 0 | same exception types |
| replay-decode | LZMA failure, < 13 payload bytes | IOException / SharpCompress (trusted boundary) |
| replay-decode | lazer score JSON: invalid JSON, trailing content, `mods`/`settings`/`statistics` null, wrong types | Newtonsoft / NullReference |
| replay-decode (decode-time playable) | `GetPlayableBeatmap` throws with the bitfield mods | throws |
| mods | unknown override acronym; Autoplay/Cinema | oracle ArgumentException |
| playable | `GetPlayableBeatmap` throws (e.g. TP sample lookups), unseeded RD/TP (G5) | throws / non-reproducible |
| replay-frames | `Parsing.ParseFloat/ParseInt` failures | FormatException / OverflowException |

Not modelled (lazer fails, model gives a result or fails differently): `OutOfMemoryException` / the 10 s
`GetPlayableBeatmap` timeout on pathological maps (resource limits of the environment, docs/model-beatmap.md
"Residuals"); exceptions in `PopulateMaximumStatistics` (difficulty calculation for legacy scores) and
`StandardisedScoreMigrationTools`; Newtonsoft's lenient JSON extensions (comments, trailing commas, single quotes,
numeric strings) — the model's JSON reader is strict.

## Test (`difftest/eval_diff.py`)

`run` feeds the same (beatmap, replay, options) to `oracle batch` (cached) and `evaltest`, compares input/schedule
fields, both fail semantics' final state and every judgement (i, n, type, result, RawTime bits, combo, health bits,
failed; ReplayPlayer: identity fields only — the sim records per-judgement combo/health for live only) and localises the
first difference (beatmap / replay-decode / sim). `playable` compares `evaltest --dump-playable` with
`oracle --dump-playable` on every emitted key, bit-exact. `jobs --corpus stable|v2 [--gen-mods POOL]` builds job lists
(random mod overrides from `modgen_sim.py`).

## Results (2026-10-21, lazer 2026.1005.0, evaltest built 14:47 with the sim at e2f362d)

Agreement = every compared field identical (judgement lists bit-exact incl. RawTime/health bits, statistics, score,
accuracy bits, rank, fail state of both semantics, schedule fields, decoded/effective mod acronyms).

| corpus | mods | schedule | jobs matching | judgements |
|---|---|---|---|---|
| stable replays (`data/replays`, Classic auto) | own (bitfield) | catchup | **300/300** (earlier sim build: 600/600, 512k) | 216,565 |
| stable replays | own | perframe | **300/300** | 216,565 |
| stable replays | own | dense1ms | **10/10** | 4,342 |
| stable replays | own + `--mods [NF]` | catchup | **100/100** | 62,682 |
| stable replays | own, `--no-classic` | catchup | **100/100** | 62,682 |
| stable replays | random M5 pool (rate/fail/DA/HR/MR/…, random settings), `--replace-mods` | catchup | **150/150** | 169,554 |
| stable replays | random M6 pool (RX/AP/AL/SG/SO/ST + rate/fail) | catchup | **150/150** (2/150 with the sim before e2f362d: RX+WU / RX+AS+ST tails, sim-side) | 169,543 |
| stable replays | random M7 pool (transform/position mods; sim M7 in progress) | catchup | **99/100** with the sim sources of 16:05 (90/100 with the 14:47 build; all mismatches contain TR; remaining one: NF+HR+AD+TR, sim-side) | 99,776 |
| lazer replays (`data/replays_v2`, JSON mods with settings) | own | catchup | **450/450** | 484,658 |
| lazer replays | own | perframe | **300/300** | 319,271 |
| lazer replays | random M5, `--replace-mods` | catchup | **100/100** | 103,856 |
| synthetic edge-case .osr (truncation, ruleset 1, negative date, corrupt LZMA, lazer JSON variants, bad overrides) | | catchup | 12/14 agree (8 both reject, 4 match); 2 documented divergences: Newtonsoft trailing comma (lazer accepts), unseeded RD (G5) | |

**Adapter losslessness** (`eval_diff.py playable`, oracle `--dump-playable` vs `evaltest --dump-playable`, every key
the sim reads, bit-exact): stable own mods 100/100, lazer own mods 100/100, random beatmap-side mods (HR, EZ, DA, MR,
ST, CL, HD, TC, GR, DF, WG, FR, SI, TR, DP, WU, WD, AS, DT, HT + seeded RD/TP) 100/100 (+60/60 again after `fade_in`
joined the sim interface), random M5 100/100, the 2 M6 and 10 M7 mismatch jobs 12/12. Hence every mismatch above is
sim-side (beatmap model and replay decoding are exonerated: the playable is bit-identical and decoded mods/frames
feed identical schedules: `steps`, `last_frame_time` agree). Same-binary check: `evaltest --sim-playable <oracle dump>`
gives exactly the adapter-path result on all 10 M7 mismatch jobs. Found on the way (sim-side, STATE "Requests"):
`Sim.magnetUpdate` index-out-of-bounds panics on MG/RP jobs (results still matched on the tested jobs).

The sim sources are compiled into `evaltest` as they are on disk (the sim agent edits them concurrently). All rows
were re-run with the 16:05 build (sim e2f362d + on-disk WIP): **2059/2060 jobs, 1,909,494 judgements bit-exact**; the
only mismatch is the M7 TR job above.

**Performance** (`evaltest` wall time per replay, whole pipeline incl. process start and JSON output, measured on the
shared 2-core VM at load 2–8): median 0.5–1.2 s, ~62 MB RSS; beatmap decode + playable + `.osr` decode + adapter (+
dump) ≈ 0.15 s median, the rest is the simulation; dense1ms ≈ 6 s. The oracle needs ~1.5–6 s per replay on the same
machine (catchup). Eval-side code follows the Lean perf rules (no float literals or `Nat.toFloat` in loops; byte-level
readers on `ByteArray`; UTF-8 fast path via `String.fromUTF8?`; arrays used linearly).

## Re-run on the final sim (HEAD 791e4a1 / 883e873 sim sources, 2026-10-21 evening; evaltest built in a HEAD worktree)

PANIC output on stderr fails a job; ReplayPlayer judgements are compared with combo/health/failed (`JRec.*RP`).

**BarrelRoll environment bug (eval-side, fixed in 95499c3).** All BR mismatches of the first pass (5/15 per-mod BR jobs,
the stable-ALL WU+BR job and perframe `7738055654` NF+TR+DF+BR+BM) had one cause: `Eval.defaultEnv` (`Eval/Env.lean`)
lacked the HitObjectContainer ancestor chains (`hoc_chain_first`/`hoc_chain` of `difftest/env-1024x768.json`; the
`Env` fields default to `#[]`), so `Sim.curHoc` recomposed an *empty* chain (identity) instead of the rotated playfield
chain. Because the replay-to-screen conversion and the hit/follow tests used the same wrong matrix, the geometry was
merely re-expressed in different float coordinates: results changed only through rounding (slider tails/ticks at the
follow-area boundary), which is why 10/15 BR jobs still matched. Localisation: `simtest` (same sim sources) on the
oracle's `--dump-playable` with the env file matched the oracle exactly where `evaltest` did not; a debugging trace
(per-step HOC and slider DrawInfo, screen-space mouse) of the NF+BR job `1661649/4857687379` was bit-identical to the
oracle's `ORACLE_DHO_STATES` env dump on all 38,065 steps (HOC), 10,100 slider samples and 31,935 mouse samples (the
oracle probes at step start = model state after the previous step). `Env.lean` now carries both chains and a `#guard`
that they recompose the dumped HOC DrawInfos bit-exactly. The sim (incl. the `brScale` "placeholder") is confirmed.

| corpus | mods | schedule | result |
|---|---|---|---|
| lazer replays (all cached oracle results) | own | catchup | **800/800** (839,003 judgements; re-run on 883e873 sources) |
| lazer replays (cached) | own | perframe | **388/388** after the env fix (387/388 before: `7738055654`, BR) |
| stable | random M5 / M6 / M7 | catchup | **60/60**, **60/60**, **60/60** |
| stable | ALL pool (random subsets of every sim mod) | catchup | **80/80** after the env fix (79/80 before: WU+BR) |
| stable | each M7 mod alone (+random CL/NF/HR), 15 each | catchup | **165/165** after the env fix (BR was 10/15) |
| stable | BR (random speed/direction) + random HR/NF/CL/DT/HD, fresh replays | catchup | **60/60** |
| former mismatch NF+HR+AD+TR | | catchup | **match** |

ReplayPlayer semantics fully compared (oracle printed a separate `replay_player`) on several hundred of these jobs; no PANIC.

## After the totality refactor (G17, e0e8215; evaltest built at 5c15cfb, 2026-10-22)

Same job lists, cached oracle results: stable per-M7-mod **165/165**, M5 **60/60**, M6 **60/60**, M7 **60/60**, ALL
**80/80**, BR stress **60/60**; lazer own mods catchup **800/800**, perframe **388/388** — 1,673/1,673 jobs, 1.89M
judgements, 0 PANIC, 0 new rejections.

**Lazer coverage beyond the first 800** (`data/wip/end-to-end-eval/cov/loop.sh`, detached, resumable; every
oracle-cached v2 catchup job not yet evaluated, plus 50 uncached jobs per round from the highest score ids, so the
server-agreement loop, which walks ids upwards, gets cache hits later): **2,962/2,962** lazer scores of the 5,141-score
v2 corpus bit-exact on catchup (3.05M judgements; 0 mismatches, 0 rejections) at the time of writing, still running.

**Performance note:** the G17 build is slower: `evaltest` user time 0.22→0.37 s, 0.59→0.85 s and 3.3→10.2 s on three
sampled lazer replays (the last: `5556876.osu` / `7737962141.osr`, NF+HT, 25,423 steps; same machine, back to back).
Reported to the sim owner (STATE "Requests").
