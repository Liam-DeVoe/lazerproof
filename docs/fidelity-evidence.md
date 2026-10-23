# Fidelity evidence: "Lean model = osu!lazer" (2026-10-23, fidelity reviewer, D68)

The refinement proofs establish **Rust = Lean spec**. Whether the **Lean spec = lazer** (pinned 2026.1005.0-lazer =
ppy/osu 9a10d935b0, osu-framework 2026.921.1, .NET 10.0.13, glibc 2.39, env D10) holds rests only on empirical
evidence. This file collects that evidence, says how current it is, lists the gaps and ranks the next checks.
Read-only review: the spec was not edited.

There are three different claims, and they must not be mixed up:

| claim | meaning | measured by |
|---|---|---|
| **(A) model = harness** | Lean/Rust output equals the headless oracle (lazer's own code in `oracle/`) for the same inputs, schedule and env | differential tests (nettest, bmtest, sim_diff, eval_diff, covfuzz) |
| **(B) harness = lazer playback** | the oracle's wiring (Gameplay.cs mirrors Player/ReplayPlayer; own clock, StubPlayer, fail logic, deterministic schedules) behaves like lazer's real `ReplayPlayer` | `oracle player` validation (real ReplayPlayer, recorded step list fed back as `explicit:`), oracle `step_check` |
| **(C) playback = live client** | replaying the `.osr` gives the stats the live client submitted | server agreement (D13). It measures (B)+(C) together. The model is not involved at all |

"Lean = lazer" in the project's sense (D7: ground truth = lazer replay playback) is (A) ∘ (B). (C) is a sanity
signal: it can expose a (B) bug, but most of its mismatches are inherent (60 fps / integer-ms replays, schedule D9).

## 1. Evidence table per layer

Spec commits that changed `model/OsuModel` after the bulk of the evidence (git log):
`e0e8215` G17 totality (10-21 22:21), `1b0a176` perf (byte-identical), `d7c2a91` D27 totality (Settings.assign
fuel, SimJson reader; 10-22 08:55), `f631caa` D48 dbg guard (10-22 14:59), `7ec6d6a` D55 AS sort fix (10-22 18:11;
**last spec change**). Net and Beatmap: unchanged since 10-21 except `d7c2a91` (Settings.assign only).

| layer | compared against real lazer/.NET code | cases | result | spec it ran against | still current? |
|---|---|---|---|---|---|
| **Net floats** (`model/OsuModel/Net`) | `nettest` C# generator calling real CoreCLR 10.0.13 / osuTK / osu.Framework dlls; `nettest lazer` calling lazer's `APIMod.ToMod` | 81.3M + 16.3M + 1.6M primitive checks; 10.1M library-op checks (Random, decimal, Bindable, easing, Interpolation, Matrix/DrawInfo); 54k `APIMod.ToMod` settings | 0 failures (sNaN-input / NaN-payload cases are classified as irrelevant, not failures) | 95fba0a (10-21) | **yes**: Net unchanged; VM glibc still `2.39-0ubuntu8.9` (checked today) |
| **Beatmap decode/convert NoMod** | `model/bmtest` (C#, ProjectReference to lazer, `GetDecoder`+`GetPlayableBeatmap`), full raw-bit dump of every gameplay field | 1625 real + test resources, 1500 version-rewritten (v3..v13, v128), 6000 fuzz, 7000 generated, 3000 introsort arrays | all bit-identical | 3055ddb (10-21) | transitively: no C# re-run after d7c2a91, but d7c2a91 touches only Settings.assign |
| **Beatmap mods** (APIMod decode + all hooks) | bmtest with `--mods single/random` (random settings incl. out-of-range, strings, nulls, unknown keys, duplicates, incompatible combos) | 48 acronyms x 400 maps; 3478 random-combo maps; 1200 reversioned; 3000 fuzz/gen (2 skipped, OOM both sides); RD/TP 300+203 | all bit-identical (except documented OOM skips) | 7bcaf5a (10-21) | **transitive only** after D27: Lean-new = Lean-old on the WU/WD settings grid (13,280 jobs), Lean-new = Rust-new on 1000+2000 NoMod, 2200 random mods, fuzz/gen 3000. Not re-run against C# |
| beatmap: aggregate check vs live server | server `maximum_statistics` vs oracle | 5913 lazer scores | equal on every score | n/a (harness) | (B)/(C) only |
| **Adapter** (Beatmap playable -> Sim playable) | `eval_diff playable`: oracle `--dump-playable` vs `evaltest --dump-playable`, every sim-read key | ~470 jobs (own mods stable/lazer, random beatmap-side mods incl. seeded RD/TP) | all bit-exact | 10-21 (c050906 + later) | yes (Adapter unchanged since 10-21) |
| **Replay decode** (.osr container, LZMA, lazer score JSON, frames) | eval_diff (whole pipeline) + covfuzz `floatdelta`/`oldversion` | every corpus replay (7417 lazer + ~700 stable decoded identically, implicitly); covfuzz 2 scenarios x 3 schedules; 14 hand-made corrupt/edge .osr | all match; 2/14 documented divergences (Newtonsoft trailing comma accepted by lazer; unseeded RD, G5) | 5c15cfb (=e0e8215) | yes, see the HEAD re-run below. Malformed-input coverage vs lazer is only 14 cases (Rust-vs-Lean fuzz does not count for (A)) |
| **Sim M0-M4** (circles, Classic, sliders, spinners, health/fail, score) | sim_diff (oracle playable dump + frames -> simtest) | syn 150 x3 schedules x2; 100 real catchup + perframe (101k judg.); syn3-5 x catchup/perframe/dense1ms; 20 real dense1ms; M4 incl. per-judgement health bits, both fail semantics | all match (only bug ever found: DifficultyRange association, fixed) | pre-G17 (10-21) | G17 regression: model-only re-run of all 35 M5-M8 corpora 1451/1451 (`--reuse-oracle`) at e0e8215 |
| **Sim M5** rate/fail/multiplier/rank/Classic | sim_diff `--gen-mods M5/M5fail` | 100 syn + 100 real catchup, 30+12 perframe/dense1ms, 30 real perframe fail | all match | 4ed0ad6.. (10-21) | via G17 re-run + e2e below |
| **Sim M6** RX AP AL SG SO ST TD | sim_diff focused pools; sensitivity check (`sim_mutate`) shows each mod changes 22-59 of 60 jobs | 60 per mod synthetic, 30 real catchup, 60 perframe, 17 dense1ms | all match (one fix: StrictTracking judged slider) | 10-21 | via G17 re-run + e2e |
| **Sim M7** GR DF SI TP TR WG HD DP MG RP BR (+pools, transforms, G1/G13/G14) | sim_diff per-mod pools; per-step DHO state dumps (`ORACLE_DHO_STATES`) | 40 synthetic per mod (ns1), TR+spinners 30, mixed 30+40 perframe, 4461 slider-steps geometry, 38k BR steps | all match | 7cffd29/171dd71 (10-21) | via G17 re-run + e2e. **Real-replay coverage is thin** (§2.1) |
| **Sim M8** all mods random; visual-only mods | `--gen-mods ALL`; visual_diff (oracle with/without the mod) | 60 real + 182 synthetic; 90/90 visual inert | all match | 10-21 | via e2e |
| **Lazer branch coverage** (D21) | coverlet on the oracle over 2675 jobs; the 5 reachable unexercised judgement branches targeted by covfuzz | 400 covfuzz jobs x 3 schedules (+820 exploratory) | 1200/1200 model = oracle; judgement core 81% lines / 70% branches, every uncovered line classified | evaltest 5c15cfb | yes |
| **Eval end-to-end** (`.osu`+`.osr` -> result) | eval_diff: every judgement (type, result, RawTime bits, combo, health bits, failed), statistics, score, accuracy bits, rank, both fail semantics, schedule fields | stable: 300 cu + 300 pf + 10 d1ms + overrides 150/150/100 + M5/M6/M7/ALL/per-M7/BR 485; lazer own mods 7417 catchup (coverage loop, to 10-22 06:21) + 388 perframe | all match (3 lazer scores: oracle OOM only; former BR mismatches were an eval env bug, 95499c3) | 5c15cfb (= e0e8215) | **re-run today at the HEAD spec, see below** |
| **D55 AS sort** | oracle vs Lean-new evaltest on all AS jobs | 65 (25 job-mod + 40 real AS) | 65/65, 67k judgements | 7ec6d6a | yes |

**Re-run at the current spec (today, 2026-10-23 00:40-00:55; cached oracle results, zero oracle cost).**
Binary: `data/wip/d49-reg/osu_eval_new`, the Rust evaluator built for the D55 regression (spec content = 7ec6d6a,
the last spec change; byte-identical to the Lean evaltest-new on 1,095 jobs, D55). Through `tools/heavy`,
`difftest/eval_diff.py run`, summaries in `data/wip/fidelity/*.summary.json`, lists `cu_list.txt`/`pf_list.txt`:

| corpus | schedule | jobs | match | judgements compared | ReplayPlayer re-runs fully compared |
|---|---|---|---|---|---|
| every oracle-cached lazer v2 score | catchup | 7,417 | **7,417** | 7,906,854 | 627 |
| every oracle-cached lazer v2 score (only 388 had been compared before) | perframe | 2,073 | **2,073** | 2,722,707 | 263 |

This removes the "predates D27/D48/D55" flag for the lazer-replay end-to-end evidence. The model here is the Rust
port, i.e. it shows Rust(7ec6d6a) = harness. With Rust = Lean (1,095-job regression at that spec, plus the proofs)
it gives Lean = harness. A Lean-evaltest HEAD re-run would make this direct (cheap, after the proofs).

**Evidence that predates later spec changes and was not re-run against lazer** (only behaviour-preservation
regressions against an earlier Lean or the Rust):
- Beatmap layer vs C# bmtest: last direct run 10-21; D27 (d7c2a91) checked Lean-new vs Lean-old (WU/WD grid) and
  vs Rust only.
- All sim_diff corpora (M0-M8, synthetic and real, with perframe/dense1ms): run against the oracle before G17; after
  G17 a model-only re-run with the stored oracle outputs (valid as long as the oracle is unchanged, which it is since
  a0244b1). Not re-run after d7c2a91/f631caa/7ec6d6a. f631caa only writes stderr debug data; d7c2a91 only touches
  Settings.assign/SimJson; 7ec6d6a was oracle-checked on the AS jobs. Risk: low.
- Stable-replay end-to-end rows (485 job-mod jobs etc.): 5c15cfb; D27/D48/D55 regressions compared Lean vs Rust on
  them (h_jobmods 485), not vs the oracle.
- covfuzz 1200: 5c15cfb + perf fix.

## 2. Gaps

### 2.1 Weak or missing comparisons (claim A)

1. **Explicit / irregular schedules are never diff-tested.** D9 claims equivalence "for every schedule". The model
   implements `Schedule.explicit` (Eval.lean:34, `simulateSteps`), but no harness (eval_diff, sim_diff,
   rust_*_diff, covfuzz) ever ran it against the oracle. Every comparison uses catchup, perframe or dense1ms:
   integer or frame-aligned references with no duplicate entries. Not covered: fractional sub-ms references,
   repeated equal references (an extra step at the same time), references between frames below 1 ms, long jumps
   (`> 1.2*16.67` catch-up splitting with odd remainders), schedules that stop before the end (`completed=false`).
   A real-time `ReplayPlayer` and live play produce exactly such schedules. The oracle side is validated by its
   `step_check` against the real FSC. The model's `simulateSteps` is a transcription of `oracle/Schedule.cs` that
   is tested only on the three regular kinds.
2. **dense1ms on real lazer replays.** It is the schedule closest to live play (it fixes 12/25 server mismatches),
   but model-vs-oracle dense1ms is mostly synthetic: covfuzz 400, M5/M6/M7 pools 12-17 jobs, 20 stable M4,
   10 stable own mods. There are essentially no lazer-v2 dense1ms comparisons (1 cached oracle job).
3. **M7 / rare mods on real play.** Real lazer v2 scores in the 8000-score corpus: GR 8, DF 4, SI 4, WG 4, TR 2,
   RP 2, MG 5, DP 17, BR 17, TP 1, WD 2, WU 14, FR 8. The M7 evidence is mostly 40 synthetic maps per mod plus
   stable replays played *with mods they were not recorded with*. Those replays do not chase moved or scaled
   objects, so the hit and tracking paths under transformed geometry are exercised far less than the miss paths.
   The sensitivity counts in model-sim.md (e.g. GR 22/40, DF 13/22, TP 23/40) show that the effect is visible but
   not dense.
4. **Settings value coverage.**
   - `modgen_sim.py` never generates DA `extended_limits` (it does generate AR -10..11, but these clamp without the
     flag). Only bmtest (beatmap side) and 94 real v2 scores exercise extended DA, e.g. AR > 10 preempt, OD > 10
     windows, CS > 10 radius.
   - The sim generator draws a mod set without duplicates (`rng.sample`). Duplicate mods (lazer applies any list)
     are tested only beatmap-side.
   - Range extremes appear only at the generator's ~10% "edge" rate (DT/HT 2.0/0.5, WU/WD/AS endpoints, DF 25,
     GR 0, BR 12, AC 0.999).
   - D21 notes that value coverage, unlike branch coverage, was never measured.
5. **Stable replay corpus.** 4490 stable replays exist; about 300-600 were compared end-to-end. This is the only
   corpus where the legacy Relax `Update` runs (RX is a no-op on lazer replays), along with Classic note-lock,
   legacy health and stable frame fixups on real play.
6. **Fail semantics on real fails.** The feed has only passed scores (G10). Fail paths are compared only on
   synthetic jobs, random fail mods on real replays (M5fail 30 perframe, M4, covfuzz onejudgement) and NF jobs
   that trigger failure (890 ReplayPlayer re-runs above).
7. **The ~580 earliest v2 scores were never compared end-to-end.** Their oracle cache entries predate the oracle
   fingerprint change (a0244b1) and the coverage loop stopped at 10-22 06:21. They include **8 of the 51
   server-suspicious ids**: 7737710092, 7737744394, 7737756477, 7737759694, 7737822303, 7737832649, 7737873103,
   7737892997. Some of these were validated per judgement by the tracking-trace tooling (sim level, 8 scores).
8. **Oracle OOMs.** 5 lazer scores have no lazer result because the oracle runs under
   `DOTNET_GCHeapHardLimit` (768 MB): 7738634568, 7738634727, 7738635629, 7737901342, 7737901269. This is a
   harness artefact; the real client has no such cap. The model gives a result on them that nobody has checked.
9. **Malformed inputs.** Model-vs-lazer behaviour on corrupt `.osr`/`.osu` rests on 14 hand-made `.osr` cases and the
   bmtest fuzz. The 7k-run `.osr` fuzz compared Rust with Lean only.
10. **Bezier subdivision fuel truncates silently (final-audit m9).** `bSplineToPiecewiseLinear`
    (Beatmap/PathApproximator.lean:111) runs `for _ in [0:100000000]` and, when the fuel runs out, emits the
    truncated output plus the last point. Every other fuel loop rejects. lazer has no bound
    (osu-framework PathApproximator.cs:105-140).
    - **Reachability.** Coordinates are bounded: `Parsing.MAX_COORDINATE_VALUE = 131072`
      (ConvertHitObjectParser.cs:58,344), and paths are relative to the head, so |coord| < 2^18. Each de Casteljau
      halving divides the control polygon's second differences by ≥ 4, i.e. the flatness measure (squared length,
      threshold 0.25) by ≥ 16. From ≤ 2·(2^20)^2 = 2^41 that takes ≤ 11 levels, which is ≤ ~4,100 iterations per
      Bezier piece. float32 rounding noise at |x| ≤ 2^18 (ulp 2^-5) is far below the tolerance, so subdivision
      cannot stall.
    - Plain `B|` sliders (one Bezier of degree n-1 per segment) therefore stay ≤ ~4,100 iterations per call,
      however many points they have.
    - The fuel can only run out for an explicit-degree B-spline segment (`B2|`, `B3|`, ...,
      ConvertHitObjectParser.cs:245-247). That needs ≳ 25k-50k control points in a single segment with
      near-maximal zigzag (a ~0.5 MB line), or ≳ 10^8 points at degree 1.
    - No ranked map comes close. Only a crafted or fuzzed map could reach it. On such a map lazer itself spends
      > 10^8 subdivision steps and hundreds of MB of output, so in the game it would most likely hit the 10 s
      `GetPlayableBeatmap` timeout or OOM.
    - **Classification:** a fidelity gap of the G12 kind (input on which lazer fails or is resource-bound). The
      model silently gives a result with a truncated path, which violates D15's "fuel exhaustion rejects".
    - **Recommended fix:** reject. Set a flag when the loop finishes with `toFlatten` non-empty, return
      `Except`/stage "playable" ("path approximation fuel exhausted"), mirror it in Rust, and patch the beatmap
      proof (`bspline_to_piecewise_linear` refinement). This is behaviour-preserving on every input that does not
      exhaust the fuel, so a D20(c) provability/totality fix.
    - Alternative: prove the fuel unreachable under a size bound (control points per segment < ~2·10^4) added to
      PlayableBounds/InputBounds. That requires a float contraction proof, which is much harder. Either way,
      record the bound in proof-pipeline §5.
    - **Fixed in D72 (reject).** `bSplineToPiecewiseLinear` returns a fuel-out flag (`toFlatten` non-empty at the
      end). `SliderPath.fuelOut` carries it through `compute`/`modifySlider`, and the hit-object parser and
      `getPlayableBeatmap` reject ("slider path approximation fuel exhausted"). Rust and the beatmap proofs are
      patched the same way (`b_spline_to_piecewise_linear_refines`, `any_path_fuel_out_refines`). Behaviour is
      unchanged on every input that doesn't exhaust the fuel (corpus identity, §2.3).

### 2.2 Known open discrepancies and their classification

| item | what | classification |
|---|---|---|
| ISSUES G16: 51 server-suspicious ids (0.86% of 5913; 35 triaged suspicious, 3 unverifiable, 13 untriaged heuristic), 906 mismatches untriaged | live server stats ≠ oracle playback, not explained by schedule-sensitive objects | **not a model bug** where checked: 42 of the 51 match model = oracle bit-exactly, 1 is an oracle OOM, 8 were never compared (§2.1-7). Their nature is claim (C), unknown per case. Demonstrated mechanisms (760 cases: note-lock integer-ms rounding 544, spinner aliasing 114, same-frame split 39, schedule 38, ...) are all replay-lossiness or live-vs-playback artefacts |
| G18 AL 7737902231 | server = playback only if 2 Alternate-blocked presses were accepted live | **unknown**, claim (C) or (B). Model = harness. The live code path is unidentified (ReplayRecorder vs InputInterceptor order). If lazer's live input handling differs from its own playback, no replay evaluator can reproduce it |
| HTNF 7737921480 | head Great on server, only press 2.4 px outside | unknown (C). 2.4 px is too large for float rounding |
| GR 7737710092 (+3 GR) | oracle schedules disagree with each other on circles; tails/ticks/combo | most likely schedule artefact (D9, frame-dependent geometry). Not demonstrated |
| AP 7737756477 | no constant fps 30-500 reproduces | schedule artefact by construction (AP advances one autoplay frame per Update); variable fps not shown |
| HDHR 7738056594 | needs one circle ≥ 6 ms later; replay has no frames 310-18815 ms | probably a data defect (late start/pause); unknown |
| DA 7738080249, DANF 7737892997 | one circle each; no single shift | unknown; DANF is not even model-compared yet |
| D9 schedule dependence | catchup ≠ live in ~35% of scores (mostly tails/ticks/spinner bonus) | **by design**: the model takes the schedule as input. A user-facing caveat: the canonical result is "lazer playback under catchup", not "the live score" |
| G8 integer-ms rounding, G15 spinner aliasing | replay lossiness | not model, not harness: properties of the `.osr` |
| G1/G13/G14/G17 | | closed |
| G2/G3 (culture header, JSON/UTF-32 maps), G4 (beatmap skin), G5 (unseeded RD/TP), G12 (lazer OOM/timeout) | | documented env/scope assumptions. G4 is an (A)∘(B)-vs-client question (§3) |
| Fail-gate deviation | the oracle's ReplayPlayer fail gate uses frame-stable time instead of `GameplayClockContainer.CurrentTime` (oracle README "Deviations") | **kept, TESTED row (D72 item 6, orchestrator-approved).** The model and osu_eval gate on frame-stable time, like `oracle run` (8/8 failgate cases identical). Lazer's real ReplayPlayer gates on the host-frame reference time and differs in 5/8 constructed cases where a trigger lands in a host frame straddling the last replay frame. Reference gating is not adopted: the catchup reference is past the last frame, so a naive reference gate opens at the first trigger (c12184: fail at 11,179 instead of ~12,551), and the right catchup semantics are unclear (D81). ReplayPlayer semantics only; live play and server scores are unaffected |

### 2.3 D72 patch regressions (2026-10-23)

The patch covers D80a, D80b, D79 N2, M2a, bezier fuel → reject, and the item-6 decision to keep the FST gate. Scripts are in `difftest/d72_*.py`; binaries were built from the patched branch and from the pre-patch main.
- **Oracle (D30, `difftest/d72_regress.py`).** 115 explicit-schedule fuzz cases, 8 failgate cases, repro0, plus the empty and decreasing repro lists:
  - 119 cases were match before and are match now.
  - Two former mismatches now match: repro0 and fuzz 7737946658 `stop`, the D80a fix.
  - Fuzz 7742268347 `dup`, which the oracle rejects, is now rejected by the model too.
  - The empty and decreasing lists are now rejected with the oracle's messages.
  - The 8 failgate cases all match `oracle run`, with the FST gate kept.
  - Two cases (7740906195_m `dup`/`gaps`) can't be checked from disk. The fuzz reused their work dir: run.json is from the SD job, while refs.txt was overwritten by the DA job. On those refs, new osu_eval = pre-patch osu_eval byte for byte, for both mod sets.
- **Rust corpus identity, new vs pre-patch osu_eval.**
  - `--batch` over the full corpus (v2_all, stable_all, h_jobmods, h_rest): 12,724/12,724 outputs byte-identical.
  - Per job: 2,099/2,099 identical. That includes the 572 early v2 entries (§2.1-7) and all 58 real-Player pilot jobs (explicit step lists from pilot, pilot30, pilot_x10, pilot_da, pilot_sd, failpath).
- **Lean vs Rust (D30).**
  - Sim (simtest): 98 chunks, 6,292 runs, 0 mismatch (4,612 identical, 1,680 both reject), 1.04M judgements.
  - Eval (evaltest vs osu_eval): 3,141 runs, 0 mismatch, 3.46M judgements. This covers v2 catchup 500, AS 65, h_jobmods 485, h_rest 45, stable 300, v2 dense1ms 194, v2 perframe 1,552.

## 3. "model ≠ lazer" vs "harness ≠ real client"

- **(A) model ≠ harness.** No open case. 0 mismatches on every comparison since the eval env fix (95499c3):
  about 20k end-to-end jobs (10.6M judgements in today's re-run alone), plus ~19k beatmaps and ~10^8 float checks. The
  weaknesses are coverage gaps (§2.1), not observed differences.
- **(B) harness ≠ lazer's real ReplayPlayer.** This is the weakest link, and nothing else measures it.
  - The harness re-wires `Player.load`/`LoadComplete` by hand: processors, mod application order, StubPlayer for
    `IApplicableToPlayer`, its own `IGameplayClock`, fail handling, disabled samples, no storyboard or beatmap
    skin, deterministic schedules.
  - The only check against lazer's real `ReplayPlayer` (`oracle player`: record its steps, replay them as
    `explicit:`, require identical judgements) ran on **9 replays**: 5 stable HD/HR/DT/NC/FL and 2 stable + 2
    lazer at the R2R swap, all on 10-21.
  - None had M6/M7/rate-ramp/AS/fail mods, which were added afterwards and whose wiring (P3 playfield updates, AP
    cursor injection, input interceptors, IApplicableToPlayer, health-processor choice, fail overrides) is exactly
    where the harness could deviate.
  - The oracle's `step_check` validates only the schedule re-implementation, not the wiring.
  - Server agreement can expose (B) bugs only indirectly, mixed with (C) noise.
- **(C) playback ≠ live client.** Server agreement measures this: 63.0% exact on catchup, ~99% exact or
  schedule-explained by heuristic, 0.86% suspicious. It also differs from the D10 environment:
  - **Screen and skin.** Hit tests depend on the 1024x768 float32 screen-space chain, UI scale and the skin's
    slider path radius (G4). Users play at other resolutions and skins, so playback on their machine can differ at
    the rounding level.
  - **Platform libm.** Class A includes Windows/macOS/Android builds. Their `Math.Sin/Cos/Atan2/Pow` come from
    the Windows CRT, Apple libm or bionic, not glibc 2.39 (perfect-curve arcs, spinner `atan2f`, BR rotation,
    easing). The pinned glibc makes the model = linux-x64 lazer by definition. Another platform's lazer can differ
    by an ulp.
  - **Live input.** Live input is sampled every frame (often 1000 Hz and above). The replay keeps ≤ 60 fps,
    integer-ms frames.

  None of these is a model error, and server agreement cannot separate them from a (B) bug. That is why
  validating (B) directly (check #1 below) is worth more than more server triage.

## 4. Recommended next checks (ranked by value per machine-hour)

The orchestrator (00:55) asked for no further runs while the proofs assemble. **Everything below waits until the
proofs finish** unless marked otherwise. The two zero-cost re-runs in §1 were done before that request.

| # | check | closes | cost | when |
|---|---|---|---|---|
| 1 | **Real-ReplayPlayer validation, broad.** `oracle player` on ~40 replays chosen for wiring risk: lazer RX/AP/AL/SG/SO/ST, stable RX (legacy Relax), MG/RP/DP/GR/DF/TR/WG/BR/SI/TP, WU/WD/AS/DT/HT, HD/FL/TC, fail cases (SD, PF, AC, EZ lives, low HP, DA drain 10) and NF. Then `oracle run --schedule explicit:steps` must be identical, **and** `evaltest --schedule explicit:steps` must match too | (B) for all mod paths; also gap 2.1-1 (explicit schedules from a real FSC) | ~1-2 machine-h (player mode runs the virtual track; 0.5 GB) | after proofs; a 5-replay pilot could run at nice 19 if MemAvailable > 3 GB |
| 2 | **Explicit-schedule fuzz.** Random reference lists: fractional sub-ms steps, duplicates, jitter around frame times, long jumps, early stop. sim_diff/eval_diff on synthetic synA-D + short real maps, 3 schedules per job, random ALL mods | 2.1-1 (D9 "∀ schedules") | ~1 h for ~300 jobs (keep mean spacing ≥ 2 ms) | after proofs |
| 3 | The 8 never-compared suspicious ids (2.1-7), then the other ~570 early v2 scores: oracle catchup (uncached) + osu_eval/evaltest | 2.1-7, finishes G16 "model = harness" | 8 jobs ≈ 5 min; 580 ≈ 45 min oracle | after proofs (the 8: first item in the next window) |
| 4 | Lean evaltest built at HEAD vs the cached catchup + perframe lists in `data/wip/fidelity/` (makes today's Rust re-run direct for the spec) | the predates flag, Lean side | 0 oracle; lake build ~10 min + ~3 h evaltest (or sample 1000) | after proofs |
| 5 | bmtest C# vs bmdump at HEAD: 1000 NoMod + 1000 random-mods + 400 WU/WD-heavy maps | beatmap predates flag (D27) | ~15 min | after proofs |
| 6 | Value-coverage sim fuzz: add DA `extended_limits` and duplicate-mod lists to modgen_sim, force setting endpoints, run on sp4/ns1 synthetic + 60 real, 3 schedules | 2.1-4 | ~1 h | after proofs |
| 7 | "Chasing" replays for M7: generate replays with lazer's own autoplay on the *modded* playable plus cursor/timing jitter, so they hit transformed objects; sim_diff per M7 mod | 2.1-3 | ~1-2 h | after proofs |
| 8 | Stable corpus end-to-end catchup (~3,900 not yet compared) | 2.1-5 (legacy RX/Classic on real play) | ~1.5-2 h oracle | after proofs |
| 9 | dense1ms on ~100 real lazer replays (short maps first) | 2.1-2 | ~2 h (oracle ~60 s/replay) | after proofs |
| 10 | Oracle re-run of the 5 OOM scores with `DOTNET_GCHeapHardLimit` ≥ 2 GB, HEAVY_EXCLUSIVE | 2.1-8 | ~10 min, but 2 GB | after proofs, exclusive window |
| 11 | ~~Bezier fuel: reject instead of truncate (spec + Rust + proof patch; D20(c))~~ | 2.1-10 | done (D72) | |
| 12 | Env variation: oracle with 1920x1080 and another UI scale (`--dump-env` -> Env data), 50 jobs model vs oracle | (A) beyond D10, quantifies the §3 env effect | needs a harness flag; ~1 h | later |
| 13 | Server triage backlog (906 untriaged) | (C) only | oracle_bg loop, already running at nice | running |

Not runnable here: other-platform libm (would need a Windows/macOS lazer); failed live scores (G10, not in the
public feed).

## Runs 2026-10-23 (D71/D76 cheap items, fidelity runner, nice 19, one heavy job at a time)

Model binary: `data/wip/d49-reg/osu_eval_new` (Rust, spec content = 7ec6d6a, the last spec change; = Lean evaltest
at that spec, D55). Oracle: current deployed build (fingerprint unchanged since a0244b1). Work dirs and per-job
results in `data/wip/fidrun/` (gitignored). Scripts: `difftest/fidrun_batches.sh` (chunked eval_diff runs with the
MemAvailable >= 2500 MB / iowait guard), `difftest/player_pilot.py` (real ReplayPlayer vs `oracle run explicit:` vs
model).

**D71(3), gap 2.1-7: the 8 never-compared server-suspicious ids** (7737710092 GR, 7737744394, 7737756477 AP,
7737759694, 7737822303, 7737832649, 7737873103 GR, 7737892997 DANF), model vs oracle, full eval_diff comparison:

| schedule | jobs | match | judgements | ReplayPlayer re-runs compared |
|---|---|---|---|---|
| catchup | 8 | **8** | 19,202 | 4 |
| perframe | 8 | **8** | 19,202 | 4 |
| dense1ms | 8 | **8** | 19,202 | 4 |

So all 51 server-suspicious ids are now model = harness (50 bit-exact, 1 oracle OOM). Their server mismatch is
(B)/(C), not (A).

**D71(3), the early v2 scores whose oracle cache predated a0244b1**: every `status='ok'` v2 job without a current
catchup cache entry: 575, minus the 3 oracle-OOM ids among them (7738634568, 7738634727, 7738635629; gap 2.1-8, still
open) = 572 jobs, fresh oracle runs in 12 chunks of <= 50: **572/572 match**, 608,979 judgements, 64 ReplayPlayer
re-runs fully compared. With the 7,417 of §1 and the 8 above, every one of the 8,000 v2 scores except the 5 OOMs is
now model = oracle on catchup (7,997 jobs).

**D71(1) pilot: lazer's real `ReplayPlayer` (`oracle player`)**, recorded step list fed back as `explicit:` to both
`oracle run` and the model. Chosen for wiring risk (input interceptor, transforms, rate ramp, fail mods, big mod
combo); all real lazer v2 replays with their own mods, plus 2 fail cases with added mods:

| replay | mods | steps (dup / fractional / gaps > 20 ms) | judgements | player = run | run = model |
|---|---|---|---|---|---|
| 7742698740 | PF AL | 5,480 (12 / 3,689 / 0) | 55 | yes | yes |
| 7738055654 | NF TR DF(25) BR(12) BM | 17,916 (34 / 9,176 / 0) | 520 | yes | yes |
| 7742028569 | EZ WD | 12,775 (30 / 7,415 / 41) | 370 | yes | yes |
| 7742250261 | HR SD DT HD FL ST AC | 3,717 (34 / 2,320 / 0) | 96 | yes | yes |
| 7738802307 | EZ NF DT FL CL RD(seeded) MR SG SO SI MU NS MG FR SY | 3,196 (1 / 1,975 / 4) | 81 | yes | yes |
| 7740906195 +SD | EZ SD | 7,690 | 53 | yes | yes |
| 7740906195 +DA drain 10 | EZ DA | 9,016 | 53 | yes | yes |

"player = run": identical step list (bitwise), every judgement (type, result, RawTime bits, combo, health bits),
statistics, total score, accuracy bits, rank, max combo, failed; `step_check` ok, `completed` true. "run = model": the
full eval_diff comparison (both fail semantics, schedule fields, per-judgement bits). Non-vacuous: the real-player
schedules have duplicate steps, fractional times and long gaps (not catchup/perframe/dense1ms), and differ from
catchup in 4-17 judgement RawTimes per replay (same statistics). In the +SD case the live semantics fail at 34,716 ms
(rank F) while the real ReplayPlayer does not fail (rank D, fail gate before the last frame at 62,812 ms); the
oracle's replay_player re-run and the model both reproduce the real ReplayPlayer exactly. Neither player run actually
failed (all scores passed), so the real Player's fail path *after* the gate (FailScore, fail overlay) is still not
exercised. Cost: 4-10 s per player run.

Effect on §2/§3: gap 2.1-7 closed; gap 2.1-1 (explicit schedules) now has 7 real-FSC explicit schedules with 0
mismatches; claim (B) now rests on 16 real-ReplayPlayer replays (9 + 7), incl. AL, TR, DF, BR, WD, ST, AC, SG, SO,
MG, SI, FR, RD, SD, PF, DA and EZ lives. Still uncovered by (B): RX/AP, WU/AS/DP/RP/GR/WG/TP/BL, stable RX, a real
ReplayPlayer fail. No mismatch of any kind was found.

### Runs 2026-10-23, part 2 (04:18-05:10): ReplayPlayer validation, broad; explicit-schedule fuzz (D71(1), D71(2))

**D71(1) continued: 43 more real-`ReplayPlayer` replays** (`data/wip/fidrun/pilot30`, `pilot_x10`), same method
(player steps fed as `explicit:` to `oracle run` and osu_eval). **43/43: player = oracle run and oracle run = model**
(486,915 steps, 18,688 judgements, `step_check` ok everywhere):
- lazer own mods (23): HR+RX; PF+DT2.0+DA+RX; AP+HR; DT+AP; WU; HR+WU; WD; EZ+NF+FL+ST+SI+WU(2.0)+RP+FR; DP;
  EZ+NF+NC2.0+FL+ST+RX+SO+BU+DP; RP; DT1.3+HD+DA(ext)+RD+RX+SO+BR+RP; RD+RX+TR+GR; EZ+HD+FL+GR; DT+HD+GR; HR+WG;
  NF+TP(seeded); HR+PF+DT+HD+BL; HR+TC+FL+AC; TC+AD+MG+SY; BR+AD+DP; SI; TR.
- stable replay 2568640163 + added mods (legacy Relax path): RX; AP; RX+HD+FL; AS(initial 1.3).
- lazer replay 7738137366 + added mods: AS; AS(0.8)+HD+FL; WU(0.5->2.0, adjust_pitch); WG+HD.
- 7738511622 `--replace-mods` DT+SD and DT+PF: live fails, ReplayPlayer gate holds (no real-player fail).
- 10 random short v2 replays (HR/HD/DT/NC/DC/NF/NoMod).

Running total: 59 real-ReplayPlayer replays this session plus 9 from 10-21, 0 mismatches. Still not against the real
player: a run that genuinely fails, see next item.

**Real-Player fail path: blocked by the harness tooling, not run.** 7739431096 (CL; the only v2 score whose oracle
`replay_player` re-run fails: frames end at 147.8 s, map runs to 172 s, 149 misses after the last frame) and the same
with HD+FL: `oracle player` never returns (killed at 900 s / 659 s, 100% CPU, no output). Cause (from the source, not
instrumented): after the fail `ReplayPlayer.PerformFail` -> `ReplayFailIndicator.Display()` ramps the track frequency
to 0 over 1000 ms (osu.Game ReplayFailIndicator.cs `TransformBindableTo(trackFreq, 0, audio_sweep_duration)`). The
gameplay clock then approaches failTime + 1000 only asymptotically, while `PlayerRunner.poll` (oracle/PlayerValidation.cs)
waits for `FrameStableTime >= maxEnd + 1000`. The real Player's fail path therefore needs an oracle change, e.g. also
emit when `GameplayState.HasFailed`/ScoreProcessor failed and the clock has stalled. That changes oracle.dll and so
the cache fingerprint (it would invalidate data/oracle-cache): orchestrator decision. Classification: harness tooling
(validation-mode exit condition). No result either way.

**D71(2) explicit-schedule fuzz** (`difftest/sched_fuzz.py`, seed 71, `data/wip/fidrun/fuzz`). It perturbs the 50
real-player step lists above (49 replays):
- `dup`: 10% of entries jittered by <= 0.49 ms, 5% duplicated, 3% sub-ms midpoints inserted.
- `gaps`: 30 windows of 16-100 ms deleted, then 3% duplicates.
- `stop`: like `dup`, truncated at 40-90% so `completed` is false; every third job.

`oracle run --schedule explicit:` against osu_eval, full eval_diff comparison: 117 runs, 1.27M references,
1.29M steps (catch-up splitting active on the gaps), 43,269 judgements, 16 ReplayPlayer re-runs compared:

| variant | runs | match | other |
|---|---|---|---|
| dup | 50 | 49 | 1 invalid input (below) |
| gaps | 50 | 50 | |
| stop | 17 | 16 | **1 mismatch (below)** |

- **MISMATCH (model ≠ lazer), score before the first judgement.** When the schedule stops before any judgement
  (`judgement_count` 0, `completed` false), lazer/oracle report `total_score_without_mods` = 1000000, but the model
  reports 0. Every other field agrees: `total_score` 0, accuracy 1, rank X.
  - Lazer source: `ScoreProcessor.Reset(storeResults)` (osu.Game/Rulesets/Scoring/ScoreProcessor.cs:438-470) first
    runs `updateScore()` on the simulated perfect play (so TotalScoreWithoutMods = the maximum, 1,000,000 + max
    bonus). It then resets `TotalScore.Value = 0` but **not** `TotalScoreWithoutMods`, which keeps the maximum until
    the first real judgement calls `updateScore()` again.
  - The model starts from `totalScoreWithoutMods := 0` (model/OsuModel/Sim/Scoring.lean:70).
  - Minimal repro (NoMod): `data/beatmaps/505083.osu data/replays_v2/7742845812.osr --schedule explicit:F`, where F
    holds the single line `0`. oracle: 1000000, osu_eval: 0. The fuzz case was 7737946658 (DC) `stop`.
  - Reachability: only with a schedule that ends before the first judgement. That is never the case for catchup,
    perframe or dense1ms (they always run to the end), and lazer rejects beatmaps with no objects. In real play it
    corresponds to quitting before the first object.
  - Classification: **model bug** (spec omits a lazer state quirk), tiny surface. Fix: initialise
    totalScoreWithoutMods to the stored maximum (TotalScoreWithoutMods after the max simulation) instead of 0. Not
    fixed here (spec change, D20/D30).
  - **Fixed in D72 (D80a).** `ScoreMax.initWithoutMods` is `(updateScore m0).totalScoreWithoutMods` on the
    max-simulation state (Sim/Scoring.lean `scoreMaxima`, Rust `score_maxima`), and `initState` starts from it. The
    repro now gives 1000000 = oracle, and the D30 regression (§2.3) matches.
- **Input-contract divergence (harness vs model): explicit lists that are not non-decreasing, or empty.** The oracle
  rejects them (oracle/Schedule.cs:55,58: "explicit schedule is empty" and "must be non-decreasing"), but the model
  accepts and simulates them. Eval.lean:31 states non-decreasing in its docstring but never checks it, and osu_eval
  `parse_explicit` doesn't either; e.g. refs `100, 50` give 169 steps. Found through a fuzzer bug (jitter put entry 2
  below entry 1, now clamped). The corrected list matches (536 judgements).
  - Lazer would *rewind* (FSC backwards, RevertResult) on a decreasing clock, which neither side models; the oracle
    declares it unsupported.
  - Classification: spec/harness contract gap. The model should reject (stage "sim"/"schedule") instead of giving a
    result for an input outside the model's domain. Low impact (the CLI user would have to supply such a list).
  - **Fixed in D72 (D80b, D79 N2).** Spec `explicitRefsCheck` (Eval.lean) and Rust `eval::explicit_refs_check` reject,
    at stage "sim", an empty list ("explicit schedule is empty"), a decreasing one ("explicit schedule must be
    non-decreasing") and a non-finite time ("explicit schedule: a reference time is not finite"; the Rust used to
    panic on `Infinity`). The fuzz `dup` case that the oracle rejects is now rejected by both.

Net effect: gap 2.1-1 is now covered by 50 real-FSC schedules plus 117 perturbed ones. The results are one model bug
on the zero-judgement edge and one rejection gap. Claim (B) covers every mod family listed in §4 #1 except a real
Player fail.

### Runs 2026-10-23, part 3 (05:15-05:45): real-Player fail path (D80c)

**Separate build.** `oracle_fail/` is a copy of `oracle/` (AssemblyName `oracle_fail`, output `oracle_fail/bin`,
wrapper `oracle_fail/oracle_fail.sh`). `oracle/bin` and the cache fingerprint are untouched (oracle.dll md5 f14ef22c…
before and after). The lazer, ruleset and framework dlls are byte-identical to `oracle/bin`. Changes are in
`PlayerValidation.cs` and `Gameplay.cs` only, and the oracle code paths are unchanged unless an env var is set:
- `PlayerRunner.poll`: once `HealthProcessor.HasFailed`/`GameplayState.HasFailed` holds, the runner emits when the
  frame-stable clock has not advanced for 120 consecutive host updates (`exit: fail_stall`), with a cap of 200k updates.
  The output gains `exit`, `fail_seen_fst`, `final_fst` and `record_count`. `ORACLE_FAIL_TRACE=1` traces each update
  after the fail.
- `ORACLE_FAIL_REFS_OUT=F` writes the host-frame reference times (`GameplayClockContainer.CurrentTime` at each step).
  `ORACLE_FAIL_GATE=reference` makes `run`'s ReplayPlayer gate read the reference clock instead of frame-stable time.
- `difftest/player_pilot.py`: `ORACLE_PLAYER=oracle_fail/oracle_fail.sh` swaps in this build for the player stage
  (the run stage keeps the normal oracle). `difftest/osr_truncate.py` cuts a replay's frames and keeps the header and
  trailer bytes. `difftest/fail_gate_check.py` runs the reference-schedule check below.

**Cause confirmed by instrumentation** (7739431096, CL). After `PerformFail`, the gameplay clock advances by a
geometrically shrinking delta: 33 ms per update, then 1.2 ms at update 100, 3e-4 at update 200, 1e-8 at update 500,
and 0 from about update 700. It converges to failTime + 1000 = 150,308.5553515868, so it never reaches the
`maxEnd + 1000` = 173,008 that the runner waited for. That was the 100% CPU hang. (Rate 1 is reported throughout: the
sweep acts on the track frequency.) With the stall exit, a player run takes 4-9 s.

**Player = oracle run = model on genuine fails, 8/8** (`data/wip/fidrun/failpath`). The method is that of parts 1-2:
the player's step list fed as `explicit:` to `oracle run` and to osu_eval. Totals: 115,365 steps and 5,970
judgements, `step_check` ok throughout. Every case matched bitwise (steps, every judgement including those after the
fail, statistics, score, accuracy, rank, `failed`), and run = model on the full eval_diff:
- 7739431096 CL: natural fail at 149,302.53 ms, rank F, 241,209. Also with +HD+FL (fail at 149,291.8). These were
  the two jobs that hung in part 2.
- Forced, frames truncated (`failpath/replays/*t.osr`): 7740829451t DT+HD+GR (HP-drain fail), 7742834759t
  EZ+HD+FL+GR+SD, 7742402030t WD+PF, 7743086189t DP (drain). All rank F, with 5-9 judgements after the fail inside
  the 1 s sweep.
- Controls: 7738511622 EZ+DT+SD and +PF. Live fails, but the ReplayPlayer gate holds (40/79 rejected triggers), so
  the player does not fail.

**The real Player reproduces the known fail-gate deviation (§2, "Fail-gate deviation") in 5 of 8 constructed
cases** (`data/wip/fidrun/failgate`). 7742402030 (WD) + PF was cut just after a non-perfect HitCircle hit at T, so the
last frame is T + 9-17 ms; T ∈ {12184, 16095, 21144, 24411, 25943, 26660, 30751, 32443}. When the FSC sub-steps
through T inside a host frame whose `GameplayClockContainer.CurrentTime` is already ≥ the last frame, lazer's
`ReplayPlayer.CheckModsAllowFailure` lets PF fail at T. The oracle and the model gate on the frame-stable time T, so
they reject that trigger and fail later, at the next miss. Results:
- Player vs `oracle run explicit:steps`: 5/8 differ. One example is total 150 vs 93: the player freezes before the
  next miss, which the run still applies (statistics Miss 1 vs 2).
- Player vs `oracle_fail run explicit:refs` with `ORACLE_FAIL_GATE=reference`: 8/8 identical apart from FSC
  sub-step placement (`steps differ`). The fail time is exactly T in the 5 differing cases.
- Gate on frame-stable time: = osu_eval 8/8.

This makes the documented (B) deviation a demonstrated model ≠ lazer difference for ReplayPlayer semantics. Live
semantics are unaffected, and in the natural corpus only 7739431096 fails under the replay gate, where the fail falls
outside such a straddling host frame. A plain gate swap does not suit the kind schedules: under `catchup`, the
reference-gated oracle opens the gate at the first trigger (fail at 11,179 instead of about 12,551 on c12184),
because the catchup reference is already past the last frame. The fix decision belongs to D72 or the orchestrator.

Observation: in the headless host the real player's step list is **not run-to-run deterministic**. Three runs of
7739431096 gave three different step lists, and the fail time moved by about 6 ms, presumably from the FSC's 10 ms
wall-clock catch-up budget. Each comparison therefore uses the steps recorded in the same run. `oracle run` stays
deterministic.

Net effect: the real Player's fail path (PerformFail → FailScore, the fail sweep, judgements during the sweep) now
agrees with the oracle and the model on every genuine fail tested (8 runs, 6 failing), except for the known
reference-vs-frame-stable gate when a trigger lands in a host frame that straddles the last replay frame.
