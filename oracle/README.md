# oracle — ground-truth osu!(lazer) replay evaluator

Headless C# harness that evaluates an osu!standard replay with **lazer's own code** at the pinned commit
(`../LAZER_COMMIT`, 2026.1005.0-lazer, osu-framework 2026.921.1). It implements `docs/lazer-map.md` §7.2 and
DECISIONS D7–D11. It is the reference that the Lean model and Rust implementation are diff-tested against.

## Build / run

```sh
export DOTNET_ROOT=$HOME/.dotnet PATH=$HOME/.dotnet:$PATH DOTNET_CLI_TELEMETRY_OPTOUT=1
# deployed build (ReadyToRun, linux-x64 only; see "Performance"). Build next to the live one, verify, then swap with mv:
cd ~/lazerproof/oracle && ../tools/heavy dotnet publish oracle.csproj -c Release -p:OracleR2R=true -o bin-next -m:1
#   (plain `dotnet build -c Release -m:1` still works and gives identical results, just slower startup/warm-up)
./oracle.sh run   --beatmap X.osu --replay Y.osr [--mods JSON] [options]   > out.json
./oracle.sh batch --list FILE [options]                                     > out.jsonl
./oracle.sh player --beatmap X.osu --replay Y.osr [--steps-out F]           # validation, see below
```

`batch` list lines: `beatmap.osu replay.osr [modsjson]` (modsjson = rest of the line; `#` comments allowed).
One host process evaluates all lines sequentially (JSONL, one line per job, flushed per job; errors produce
`{"beatmap","replay","error",...}` lines and the batch continues). For throughput run one batch process per core.

Options:

| option | meaning |
|---|---|
| `--schedule catchup\|perframe\|dense1ms\|explicit:FILE` | reference-clock schedule (default `catchup`, D9) |
| `--mods JSON` | lazer `APIMod` list, e.g. `[{"acronym":"DT","settings":{"speed_change":1.3}}]`. Each mod replaces a decoded mod with the same acronym, otherwise is appended. Settings go through `APIMod.ToMod` (bindable clamping/precision as in lazer). |
| `--replace-mods` | `--mods` (or the per-line mods) replaces the decoded mod list entirely |
| `--no-classic` | drop the `ModClassic` that `LegacyScoreDecoder` auto-adds to stable replays |
| `--trace` | add `trace.references` and `trace.steps` (every frame-stable step time) |
| `--no-judgements` | omit the per-judgement list (smaller JSONL) |
| `--timing` | add `wall_ms` (the only non-deterministic field; off by default) |
| `--no-step-check` | skip the step-sequence self-check |

Environment variable `ORACLE_DHO_STATES=1` (only with `--dump-env`): the env dump additionally gets `dho_states` (per
frame-stable step, at its start: every alive top-level DHO and slider head with index, kind, pooled instance id,
Position, Scale, Rotation, Alpha, State, IsPresent, IsAlive; sliders also Size/OriginPosition; spinners
RotationTracker.Tracking and TotalRotation) and `hoc_chain` (the HitObjectContainer's ancestor chain, computeDrawInfo
inputs, first probe and steady state). Debugging aid for the sim model (M7); default outputs unchanged.

Exit code 1 if any job errored. stdout carries only JSON; all logging goes to stderr.

## Wiring (what is real lazer code, what is ours)

Host: `HeadlessGameHost(realtime: false)`, `ExecutionMode.SingleThread`, `WindowedSize` 1024x768, fresh private
storage dir per process (deleted on exit), audio device "No sound". Game: `OsuGameBase` subclass, `DummyAPIAccess`
(offline), fonts skipped (as lazer's test runner does), root scaling container `ScalingContainer(ScalingMode.Everything)`
as in `OsuGame` (applies UIScale). Everything is default config (fresh storage): UIScale 1, Scaling Off,
IncreaseFirstObjectVisibility on, snaking in/out on, default skin (argon), BeatmapSkins on (but no beatmap skin is loaded).

Per job (`Gameplay.cs`, mirroring `Player.load`/`LoadComplete`/`OnEntering` and `ReplayPlayer`):

1. `.osu` decoded with `Decoder.GetDecoder<Beatmap>` → `TestWorkingBeatmap`. `.osr` decoded with a `LegacyScoreDecoder`
   subclass (real decoder: legacy mods → lazer mods, auto `ModClassic` for stable, frame fixups, offset for v<5 maps).
2. Mods resolved (`--mods` etc.), then `gameplayMods = mods.Select(m => m.DeepClone())` exactly as Player.
3. `GetPlayableBeatmap(rulesetInfo, gameplayMods)`; `ruleset.CreateDrawableRulesetWith`; `ScoreProcessor` (`Mods.Value`,
   `ApplyBeatmap`); `HealthProcessor` from the first `IApplicableHealthProcessor` (Classic → legacy health) else the
   ruleset's, `ApplyBeatmap`; `GameplayState`; `RulesetSkinProvidingContainer` (ruleset skin transformers, beatmap skin
   null); `BreakTracker(GameplayStartTime, ScoreProcessor){Breaks = working.Beatmap.Breaks}`;
   `ScalingContainer(ScalingMode.Gameplay)` → `DrawableRuleset` with `FrameStableComponents = [ScoreProcessor,
   HealthProcessor, ComboEffects, BreakTracker, StepRecorder]`.
4. `NewResult` → `HealthProcessor.ApplyResult; ScoreProcessor.ApplyResult; GameplayState.ApplyResult` (health first),
   `RevertResult` likewise, then the oracle's recorder (subscribed after, so it sees post-judgement state).
   `IApplicableToScoreProcessor`/`IApplicableToHealthProcessor` applied on the processors' `OnLoadComplete`.
   `HealthProcessor.Failed += onFail`.
5. LoadComplete (= Player.LoadComplete + OnEntering, same order, before the first frame-stable step):
   `DrawableRuleset.SetReplayScore(score)` (ReplayPlayer.PrepareReplay), `lastFrameTime`, `IApplicableToPlayer`
   (on a never-loaded `StubPlayer`; OsuModRelax/ModEasyWithExtraLives ignore it, Bloom/NoScope bind `IsBreakTime`),
   `IApplicableToTrack.ApplyToTrack(AdjustmentsFromMods)`.

The oracle container itself is the cached `IGameplayClock` (role of `GameplayClockContainer`): `CurrentTime` = current
reference time, `Rate` = `AggregateFrequency × AggregateTempo` of `AdjustmentsFromMods` (= track rate with user
playback rate 1, so `GetTrueGameplayRate()` and SpunOut's `Clock.Rate` are as in the game; live for TimeRamp),
`IsPaused` false, `StartTime` = `MasterGameplayClockContainer.findEarliestStartTime` (without storyboard),
`GameplayStartTime` from the DrawableRuleset. It also implements `ISamplePlaybackDisabler` (always disabled; see below).

## Stepping and schedules (D9)

The FrameStabilityContainer (FSC) loops `updateClock(); UpdateSubTree()` while catching up, bounded by **10 ms of wall
clock per host frame**. The oracle makes stepping independent of that bound: in each host frame, *before* the
DrawableRuleset updates, the driver checks whether the FSC has reached the current reference time `R`; only then does
it move `R` to the next schedule entry. With a fixed `R`, each FSC iteration is a pure function of (FSC time, frame
index, `R`), so however the iterations are split across host frames, the step sequence is a function of the reference
sequence alone. Every run re-derives the expected step sequence with an independent re-implementation of
`applyFrameStability` + `FramedReplayInputHandler.SetFrameFromTime` (`Schedule.cs`, `StepSimulator`) and reports
`schedule.step_check` (`"ok"` or the first mismatch). After the last reference is reached, children stop updating
(no extra step).

Reference sequences (`R0` = StartTime ≤ min(0, GameplayStartTime), `end` = latest end time of any (nested) object + 1000):

- `catchup` (canonical, D9): `[R0, end]`. Steps are "next replay frame, or +1000/60 ms if the gap exceeds
  `1000/60*1.2f`", i.e. what lazer does when catching up / fast-forwarding.
- `perframe`: `[R0, f0, f1, …, end]` (strictly increasing frame times > R0). Differs from catchup only for frame gaps in
  (16.67, 20] ms and in the last sub-step before a frame.
- `dense1ms`: `R0`, then every integer ms up to `end` (each frame still visited exactly once).
- `explicit:FILE`: one reference time per line (non-decreasing; equal entries = a host frame where the clock did not
  move, i.e. an extra step at the same time). Stops after the last entry (judgements after it are not produced;
  check `completed`). Feeding a recorded step list back as the explicit reference list reproduces exactly that step list.

## Fail semantics (D11)

- `live` (Player): `onFail` → `mods.OfType<IApplicableFailOverride>().All(m => m.PerformFail())` (short-circuit, mod
  order) → `GameplayState.HasFailed`, `Schedule(FailScore)` (next host frame, as Player). After the fail the
  HealthProcessor marks all results `FailedAtJudgement`, the ScoreProcessor ignores them, rank = F. Gameplay continues
  (judgements still listed, with `"failed": true`).
- `replay_player` (ReplayPlayer): failure allowed only once the frame-stable time ≥ last replay frame time, then
  `CheckModsAllowFailure` as above, and `PerformFail` = immediate `FailScore`.
  The two can only differ if the health processor ever attempted to fail; the oracle therefore re-runs the job (fresh
  decode, fresh mod instances) under ReplayPlayer semantics only when `live.fail_trigger_count > 0`; otherwise
  `"replay_player": "same_as_live"`.
- `fail_time` = frame-stable time of the failing judgement.

## Output schema (one JSON object per job)

```
oracle_version, lazer_commit, lazer_version, framework_version, runtime
environment: window_width/height, draw_width/height, ui_scale, scaling_mode, increase_first_object_visibility,
             beatmap_skins, beatmap_skin_loaded ("none"), storyboard ("not loaded"), skin, snaking_in/out_sliders
input: beatmap, replay, beatmap_md5, replay_beatmap_md5, beatmap_md5_match, is_legacy_score, mods_arg?, no_classic,
       replace_mods, decoded_mods [APIMod], mods [APIMod, effective, after DeepClone], true_gameplay_rate,
       hit_objects, warnings [...]
schedule: kind, r0, end, gameplay_start_time, last_frame_time, references, steps, host_frames, step_check
live / replay_player (or "same_as_live"):
  semantics, failed, fail_time, fail_trigger_count, rank, total_score, total_score_without_mods, accuracy,
  max_combo, final_combo, final_health, completed (ScoreProcessor.HasCompleted),
  statistics {HitResult: count, non-zero, enum order}, maximum_statistics {...},
  legacy_counts {300,100,50,miss} (ScoreInfo.GetCount300() etc.), judgement_count,
  judgements: [ {i: top-level object index, n: nested index (-1 = the object itself), type: HitObject class name,
                 result: HitResult, time: RawTime, offset: TimeOffset, combo: ComboAfterJudgement,
                 health: Health after the judgement, failed?: FailedAtJudgement} ]   (processor order)
trace?: {references: [...], steps: [...]}
wall_ms? (only with --timing)
```

All doubles are printed with `ToString("R")` (shortest round-trip), invariant culture; NaN/∞ as strings. Ordering is
deterministic (processor order for judgements, enum order for statistics).

## Validation against the real ReplayPlayer

`oracle player` pushes lazer's real `ReplayPlayer` (subclass that only adds a step recorder and a judgement listener)
onto an `OsuScreenStack` with the beatmap's virtual track, plays it to the end and prints its judgements, statistics,
score and step times (`--steps-out FILE` writes the step list). Running `oracle run --schedule explicit:FILE` on that
list must reproduce the real player exactly. Result on the initial corpus (5 stable replays, HD/HR/DT/NC/FL, 7k–32k
steps each): **5/5 identical** — same judgement list (order, HitObject type, HitResult, RawTime, combo and health after
every judgement), statistics, total score, accuracy and rank; `step_check` ok.

(Note: in the headless host the virtual track advances by the FastClock, ~33 ms per host frame, so this "real-time"
playback is itself just another schedule, not the one a user would see.)

## Results so far (2026-10-21, 5 replays)

- Determinism: repeated runs and a run under heavy CPU load (2 busy loops + allocation churn) are byte-identical
  including the full step trace. `host_frames` (how the 10 ms budget split the work) is the only field that varied, and
  is now only printed with `--timing`.
- Schedule sensitivity: catchup vs perframe: identical results on 5/5 (step times / judgement times differ on 4/5).
  catchup vs dense1ms: results differ on 4/5 (always slider tails: dense sampling finds tracking inside the
  [end−36, end] tail window more often; 1–4 tails per replay, i.e. Ok↔Great on the slider + SmallTickMiss↔Hit).
- Server (stable) stats agreement with catchup: 50s and misses 5/5, max combo 4/5, 300/100 1/5 (oracle has 1–3 extra
  100s from slider-tail misses, consistent with the schedule effect above; the real-time ReplayPlayer schedule and
  dense1ms both match the server on 3718998740).
- Throughput: ~0.6–0.75 replays/s in one batch process (~0.09 ms per frame-stable step warm, avg replay ≈ 18k
  steps); two concurrent processes on this 2-core VM do not increase total throughput. ~450 MB RSS, flat over 30 jobs.

## Performance (2026-10-21)

Profile (EventPipe sampling + per-thread /proc CPU, 14 stable replays, catchup): main thread ~70% of process CPU, of
which ~80% is `FrameStabilityContainer.UpdateSubTree` (the gameplay tree: DHO updates/transforms, input queues,
lifetime management) — untouchable by the rules. The rest: background tier-1 JIT thread ~30% of process CPU in short
batches; per job ~5% replay decode (LZMA), ~7% DrawableRuleset load, ~1.5% `PopulateMaximumStatistics`; GC pauses
~5–7%; JSON emit <0.3%. Under `perframe`/`dense1ms` (≈1 frame-stable step per host frame) the framework's
`GenerateDrawNodeSubtree` over the whole tree is ~40% of CPU (catchup: ~3%).

Applied (all in `oracle.csproj`, active only with `-p:OracleR2R=true`, i.e. the deployed publish build):

1. **ReadyToRun** precompilation of all assemblies (oracle, osu.Game, osu ruleset, osu.Framework, osuTK, ...).
   Safety: R2R code is produced by the same RyuJIT; the runtime only uses it where valid for the CPU and otherwise
   JITs, and hot methods are re-JITted at tier 1 exactly as before. x64 floating-point is scalar SSE2 IEEE in all
   tiers (the JIT never contracts to FMA), so code tier cannot change results — the old build already ran every
   method at a load-dependent mix of tier0/OSR/tier1 and was byte-identical under load (README "Results so far").
2. **linux-x64 RID** (framework-dependent): output 644MB → 271MB (no other platforms' native libs). The native libs
   are byte-identical to `runtimes/linux-x64/native/*` of the portable build (cmp-checked; versioned ffmpeg libs copied
   by the `CopyVersionedNativeLibs` target).
3. **TieredPGO off**: removes the instrumented tier (background JIT CPU ~20% of a short batch); steady state was
   unchanged within noise. Same safety argument as 1 (code tier/optimisation choice only).
   GC stays workstation non-concurrent (`DOTNET_GCHeapHardLimit` from oracle.sh). GC-timing changes are not
   observable: GC timing already varies run to run (tiering, escape analysis) without any output change.

Measured, rejected:
- `TieredCompilation=0`: 40% slower (no tier-1 rejit of R2R code). `GCgen0size=96MB`: within noise.
- **Skipping draw-node generation** (would be ~1.7x for perframe/dense1ms): NOT safe. `GenerateDrawNodeSubtree`
  mutates drawable state that gameplay can read: `CircularContainer.GenerateDrawNodeSubtree` sets `CornerRadius`
  (osu-framework Graphics/Containers/CircularContainer.cs:13-17), which feeds `Contains`/positional-input masking;
  `SmoothPath` validates its texture there (Lines/SmoothPath.cs:82-85); and `DrawNode.ApplyState` validates lazily
  cached layout/`DrawInfo` at a different time than gameplay would. Kept as is.
- Skipping `PopulateMaximumStatistics` / replay re-decode: would require modifying lazer's decoder; ~1.5%.

Verification (ORACLE_NOCACHE, old portable build vs new, 70 replays = 32 stable + 22 lazer (replays_v2) + 16 synthetic
(circles, sliders, lazer-format)): byte-identical JSONL with `--trace` for catchup, perframe, dense1ms (69MB);
44 `--mods` jobs (DT, DT 1.3x, NC, HT, HR, HD, EZ, EZ+HT, RX, AP, SD, PF, AC, FL, WU, MR, ST, HDHRDT, DA settings,
DA drain 10 / EZ+DA drain 9 fail cases with replay_player re-runs) with and without `--replace-mods` (perframe), seeded
TP/RD and NF+DT+HR; `--no-classic`. Only difference: unseeded TP picks a random seed per run (lazer behaviour; also
differs between two runs of the *same* build) — seeded TP/RD are identical. `oracle player` validation: 4/4 replays
(2 stable, 2 lazer) match `run --schedule explicit:` exactly.

Speed (same lists, interleaved old/new, machine load 4.5–6, 3 reps): 8-job batch user CPU 10.9 → 9.4 s (−13%),
startup ~1.4 → ~0.9 s, 0.84 → 0.86/s wall (noisy); 70-job batch user CPU 59.4 → 57.5 s (−3%), ~1.2/s both
(~120 µs per frame-stable step incl. per-job overhead; ~50–70 µs warm). RSS: 270–330MB (8 jobs), 590–740MB (70 jobs)
both builds. Bottom line: without touching gameplay or draw-node generation the oracle is gameplay-bound; the gain is
mainly for short batches (JIT warm-up) plus 370MB less disk.

## Deviations from the real Player (and why they don't matter, or how they are reported)

- No HUD, storyboard, background, overlays, break overlay, skip button, fail animation, results, leaderboard, replay
  analysis overlay (only cached when a `ReplayPlayer` is) — visual/UI only; none receives replay input (replay input goes
  only to the ruleset's own input manager).
- No Player enter scale animation (`ScaleTo(0.7)→1` over 750 ms). It affects screen-space transforms in real play for
  the first 750 ms of wall time after entering; objects are not hittable that early (GameplayStartTime is ≥ 2 s before
  the first object). Fail animation (frequency ramp) is also absent: results after a live fail are frozen anyway.
- Samples are permanently disabled via `ISamplePlaybackDisabler` (Player disables them while catching up/paused). Audio
  has no effect on judgement. Large speed-up.
- `StartTime` ignores storyboard events (storyboards are not loaded). It only affects the first step(s) before
  GameplayStartTime, where nothing is alive.
- Beatmap skin: not loaded (only the `.osu` is available). A beatmap skin could change skin-dependent drawable geometry
  (slider body radius → `OriginPosition` float rounding in hit tests, lazer-map §6.6). Default (argon) skin is used.
- ReplayPlayer's fail gate uses `GameplayClockContainer.CurrentTime` (the reference clock); we use the frame-stable time,
  which the reference clock tracks in real-time playback. Under `catchup` the reference is far ahead so the literal
  rule would make ReplayPlayer semantics identical to live.
- Mods requiring a real Player object beyond `IsBreakTime` would need more stubbing (none known among osu! mods).
  Autoplay/Cinema are rejected (they replace the replay).
- Not supported: rewinding (explicit schedules must be non-decreasing), spectator replay headers, lazer-replay
  statistics frames.

## Known limitations

- Results depend on the reference schedule (lazer-map §0.2): this is inherent to lazer, not an oracle artefact.
  `catchup` is the canonical choice; real-time ReplayPlayer playback produces yet another schedule.
- Speed: ~0.1 ms per frame-stable step once JIT-warm (a 5-min map ≈ 25k steps ≈ 2.5 s). The first job in a process
  pays ~3–5 s of JIT warm-up — use `batch`. `dense1ms` costs one host frame per ms (≈0.2 ms each, ~60 s for 5 min).
  The cost is the full drawable tree (skin pieces, transforms, cursor trail, input queues); removing visual drawables
  would be faster but would no longer be "lazer's own code".
- Each job also runs lazer's `LegacyScoreDecoder.PopulateMaximumStatistics`, which computes difficulty attributes
  (~0.1–0.3 s); it only fills the decoded ScoreInfo's maximum statistics and does not affect results.
- The online beatmap-metadata updater is replaced by a no-op (it downloads online.db.bz2); API is offline.
- Lazer-format (.osr version ≥ 30000000) replays are supported by the decoder but untested (none in the corpus yet).
- Stable replays are judged by lazer rules (with Classic): server (stable) counts differ legitimately.
