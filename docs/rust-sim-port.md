# Rust port of the Sim model (M0-M7, total)

`impl/osu_eval_core/src/sim/*` and `impl/osu_eval_core/src/replay/*` port the Lean simulation model
function by function, in the Aeneas subset (docs/proof-poc.md style rules, impl/STYLE.md). `impl/simtest_rs` is a
drop-in for the Lean `simtest` (same CLI and byte-identical JSON output).

## Pinned spec (ported incrementally)

| Rust commit | Lean spec commit | scope |
|---|---|---|
| 6da616b … 43ae79c | `3f88501` | M0-M4 core + NF/CL |
| c949ed3 (tag `rust-sim-m56`) | `3f88501` | + M5/M6 sim-side mods (all of that spec's `Config.ofMods`, AutoGen) |
| f0f6889 (verified: 6,540/6,540) | `7cffd29` | + M7: transform engine (`Sim/Transforms.lean` → `sim/transforms.rs`), pooled DHO instances, presence-gated subtree updates, slider body refresh (G1), rotation geometry, GR/DF/SI/TP/TR/WG/HD/CL-early-fade handlers, DP/MG/RP/BR, spinner-tick DHOs, per-judgement ReplayPlayer fields in the output |
| 5afe1a5 (verified: 2,980/2,980) | `171dd71` | + Autopilot's injected MouseMove also sets `cursorPos` (read by MG/RP in the same P3) |
| f3cc2a1 (verified: 10,492/10,492) | `e0e8215` | total simulation (G17): rejections as `Result<_, SimErr>` (section "Totality") |

Each step is verified against a Lean `simtest` built from the pinned commit in a separate worktree (copy of
`model/.lake`, then `lake build simtest`). Next diffs: `git diff e0e8215 -- model/OsuModel/Sim model/OsuModel/Replay model/SimTest`.
MG/RP are ported from the fixed `magnetUpdate` (e4d512b: the hoisted `headIdx` lookup for circles), never from a panicking
version; `rust_sim_diff.py` reports any Lean `PANIC` on stderr.

## Scope

All sim-side behaviour of the pinned spec: replay frame decode, FSC schedules, input/hover, float32 hit-test matrices
(now from each pooled DHO instance's current placement), lifetimes/alive dictionary order, hit policies, circles,
sliders, spinners, score + health processors with both fail semantics, and every mod `Config.ofMods` handles
(mods come as `beatmap::mod_settings::ModConfig`, i.e. the Beatmap port's `APIMod.ToMod`). Debug-only spec options
(`--trace-obj`, `--dbg-no-presence`, `--trace-tracking`, `--print-geom`, `--check-env`, the `dbg` stderr lines) are not
ported.

## Totality (Lean G17, `e0e8215`; DECISIONS D16)

The spec's `SimM = ReaderT Ctx (StateT St (Except String))` becomes `(c: &Ctx, s: &mut St) -> Result<T, SimErr>`
(`sim/err.rs`); Except-returning pure spec functions (`references`, `simulateSteps`, `steps`, `sliderGeom`,
`bodyRefresh`, `positionAt`, `curvePositionAt`, `isMouseInFollowArea`, `HealthSt.drain`, `computeDrainRate`,
`computeLegacyDrainRate`, `mkHealthCfg`, `AutoGen.*`, `timeRampRate`, `DynRate.setSpeed/initialSpeed`,
`inputBlockPeriods`, `mkCtx`, `initState`, `runWith`, `simulate`) return `Result` too (NetExn-valued where the
spec is `Except NetExn`). A Rust function returns `Result` iff some spec rejection is reachable through it; the rest
keep their plain signatures.
* `SimErr` has one variant per spec `throw` site (`lazer would throw: …` with the `NetExn`, `malformed …`, fuel
  exhaustion, and the non-index `internal:` ones). `simtest_rs` renders the spec's exact message
  (`{"error":"sim: …"}`, exit 1; Lean `Float` `toString` = `%f`/`NaN`/`inf`, `repr` of `Kind`/`NetExn`).
* `getA`/`setA`/`need` on arrays whose size is a simulation invariant (`objs`, `insts`, `nested`, `pools`,
  `headIdx`, `asSeen`, …) stay plain indexing: a violation is a Rust panic (Aeneas `fail`), unreachable, and a run
  whose spec result is `.ok` performs the same in-range accesses. `sliderData`/`need … "slider data"` is
  `Internal::MissingSliderData`.
* Evaluation order of rejections follows the spec: `mkCtx` = AutoGen, steps, health config, input-block periods,
  preceding end times, slider heads (all objects), slider tails; then `initState` (AS bindables, then every dynamic
  rate's initial speed); then the run.
* `crate::schedule` (the proof-POC `simulate_steps`, proven against the pre-G17 `proofs/OsuProofs/Spec/Schedule.lean`)
  is unchanged; the sim uses `sim::schedule::simulate_steps`, which rejects on `Math.Clamp` with out-of-order frame
  times and on fuel exhaustion.
* Former silent defaults that are now rejections: `exOr` on AS clamps/`Math.Sign`/`Average`, TimeRamp rate
  rounding, bindable setters; `slider.getD default`; a missing alive-dictionary entry on `becameDead`; the
  `HandleHit` depth bound; the `ComputeDrainRate`/legacy/ReportDelta/bonus-score fuel; empty slider path and short
  `cumulative_length`; inverted drain bounds; `Math.Sign(NaN)`; invalid input-block periods. The playable loader
  rejects an odd number of path coordinates and breaks that are not `[start, end]`.

## Correspondence

Every Lean `def` has a Rust `fn` with the snake_case name and a doc comment naming it; loops with `break`/early
`return` are split into small helper fns (e.g. `enumerate_up_to` + `push_nested_up_to`, `drain_pass`,
`legacy_pass`, `lifetime_first_update` / `lifetime_future_update`). `SimM := ReaderT Ctx (StateM St)` becomes
`(c: &Ctx, s: &mut St)`.

| Lean | Rust |
|---|---|
| `Sim/Basic.lean` | `sim/basic.rs` (+ `sim/netx.rs`: `F64.round/sign/copySign`, `F32.max/min/clamp/sign`, `Bindable.equalsD`) |
| `Sim/Playable.lean` (types) | `sim/playable.rs`; JSON loader in `simtest_rs/src/load.rs` (not translated) |
| `Sim/Schedule.lean` | `sim/schedule.rs` (+ `crate::schedule`, proven) |
| `Sim/Geometry.lean` | `sim/geometry.rs` |
| `Sim/Mods.lean` (Config, ofMods, multiplier) | `sim/mods.rs` |
| `Sim/AutoGen.lean` | `sim/autogen.rs` |
| `Sim/Transforms.lean` | `sim/transforms.rs` |
| `Sim/Scoring.lean` | `sim/scoring.rs` |
| `Sim/State.lean` | `sim/state.rs` |
| `Sim/Step.lean` | `sim/step.rs` |
| `Replay/Frames.lean` | `replay/frames.rs` (parsers: `crate::net::parse`, the Net port) |
| `SimTest/Main.lean` | `simtest_rs/src/main.rs` |

Representation choices (all bijective on reachable states):
* `HObj.typeName : String` → `type_id: u32` into a name table held by the shell.
* statistics `Array Nat` (100 entries by enum value) → `[u64; 18]` by ordinal (`hr_index`).
* action lists (`List Action` / `Array Action`, at most 3 distinct elements) → `ActList { items: [Action; 3], len }`.
* `freeList : List Nat` (head = most recently freed) → `Vec` with the head at the end.
* `receptorCornerRadiusPow` (closed term) → computed once into `Ctx.corner_pow`.
* `Int.emod (spanAt p) 2 == 1` → `span_at(p) % 2 != 0` (odd test, also for negative spans).

## Trusted primitives added to `float.rs` (additive)

`F64::{trunc, pow (glibc pow), from_i64, from_u64, to_i32_sat, to_i64_sat, parse_decimal}`,
`F32::{neg, le, is_nan, is_negative, abs, pow (powf), atan2 (atan2f), from_i64, to_i32_sat, parse_decimal}`.
`parse_decimal(neg, digits, exp10)` = `Parse.decToBits` (correctly rounded decimal → binary, via Rust's `dec2flt`,
which is correctly rounded for any input length; exponent beyond ±65536 with > 65536 digits is the only theoretical
divergence).

## Testing (`difftest/rust_sim_diff.py`)

Byte-identical stdout of Lean `simtest` (pinned build) vs `simtest_rs` per (playable, frames, schedule, mods).
Results: see "Results" below and STATE.md metric "rust sim port agreement".

## Results (2026-10-21; Lean `simtest` built from `3f88501`, `simtest_rs` from commit f4fc149 + scoring import cleanup)

Every run: byte-identical stdout (judgements with RawTime/health bits, combo, both fail semantics, score, accuracy,
rank, drain rate, multiplier). **12,240 / 12,240 runs identical, 0 mismatches, 3.76M judgements.**

| corpus (playables) | pairs | schedules | mod sets | runs | identical | judgements |
|---|---|---|---|---|---|---|
| synA circles (evaltest dumps, replay mods / NoMod) | 60 + 60 | catchup, perframe, dense1ms | "", CL, NF+CL, NF, CL(no note lock), CL(no classic health) | 2160 | 2160 | 86k |
| synB sliders (both dumps) | 60 + 60 | 3 | 6 | 2160 | 2160 | 193k |
| synC sliders+spinners, lazer replays (both dumps) | 60 + 60 | 3 | 6 | 2160 | 2160 | 310k |
| synD synthetic replays on real maps (both dumps) | 30 + 30 | 3 | 6 | 1080 | 1080 | 408k |
| oracle dumps: w_sp1_m4, w_sp2_m5, w_sp4_m6_pf (synthetic, with beatmap-side mods) | 190 | 3 | "", CL, NF+CL | 1710 | 1710 | 177k |
| oracle dumps: w_real_m5, w_real_m6 (real replays, beatmap-side mods) | 130 | 3 | 3 | 1170 | 1170 | 836k |
| real crawled replays (evaltest dumps) | 200 | 3 | 3 | 1800 | 1800 | 1.75M |

Throughput (real corpus, 200 replays, CL, one process, VM load average ≈ 9 on 2 cores — numbers are noisy):

| schedule | simtest_rs | Lean simtest | oracle (lazer, docs) |
|---|---|---|---|
| catchup | 15 replays/s | 1.1 replays/s | ~0.7 replays/s |
| perframe | 23 replays/s | 1.2 replays/s | |
| dense1ms | 3.1 replays/s | 0.13 replays/s | |

(simtest_rs includes JSON parsing of the ~0.4 MB playable dumps; single unloaded run of a 4.5k-frame replay: 20 ms
catchup, 130 ms dense1ms.)

## Results M7 (2026-10-21; Lean `simtest` built from `7cffd29`, `simtest_rs` from f0f6889)

Driver: `impl/tools/run_chunks.py data/wip/rust-sim/plan_m7{,a,b}.json` (results `data/wip/rust-sim/results_m7.jsonl`).
**6,540 / 6,540 runs byte-identical, 0 mismatches, 0 Lean PANICs, 1.12M judgements.**

| corpus | mod source | schedules | runs | identical | judgements |
|---|---|---|---|---|---|
| synA-D (synthetic, 60/60/60/30 pairs) | `M7` pool x2 per run + modsets "", CL | catchup, perframe, dense1ms | 2520 | 2520 | 333k |
| synA-D | `ALL` pool (every osu! mod, random settings) x2 | catchup, perframe | 840 | 840 | 111k |
| synC | each focused pool (M7hd/gr/si/tp/wg/tr/dp/mg/rp/br, M5, M6) | catchup, perframe | 1440 | 1440 | 207k |
| 18 oracle job-mod corpora (sim-mods agent dumps `w_ns_*`, `w_sp_*`, `w_sp4_m6ap`, `w_real_all`, `w_real_m6`; now kept in `data/wip/rust-sim/simmods`) | the job's own mods | catchup, perframe | 1380 | 1380 | 151k |
| real40 (real crawled replays) | `ALL` x1 + "", CL | catchup, perframe, dense1ms | 360 | 360 | 315k |

## Results 171dd71 (Lean `simtest` built from `171dd71`, `plan_171.json`, `results_171.jsonl`)

**2,980 / 2,980 identical, 0 PANICs, 537k judgements**: AP+(MG|RP)(+0-2 of CL/NF/DT/HT/HR/WD/AS, random settings)
job-mod corpora on synB/C/D + real40 (880 runs; the pre-port binary differs on 6/10 of the first synC jobs, so
the corpus is sensitive to the change), synA-D x M6ap and ALL pools (1,680), oracle w_ns_all/w_ns_m7mg/w_ns_m7rp/
w_real_all/w_sp4_m6ap (420).

## Results e0e8215 (2026-10-22; Lean `simtest` built from `e0e8215`, `simtest_rs` f3cc2a1)

`plan_e0{a,b,c}.json` → `data/wip/rust-sim/results_e0.jsonl`. **10,492 / 10,492 runs byte-identical (8,812 simulations +
1,680 identical rejections), 0 mismatches, 0 Lean PANICs, 1.91M judgements.** (The same plan on the binary before the
Aeneas restructuring: 5,028/5,028, `results_e0_pre.jsonl`.)

| corpus | mod source | schedules | runs | identical |
|---|---|---|---|---|
| rejection corpus `rej/` (24 base playables from synB/C/D + real40, 8 mutations: slider without tail / head, empty path, short `cumulative_length`, break after the last object, break ending past the next object's `V(h) - 1`, inverted drain bounds, NaN HP) | 8 mod lists ("", CL, AL, SG, AP, AS, NF+MG, DT+HD+TR) | catchup, perframe | 3,072 | 3,072 (1,680 rejections: 768 malformed slider, 384 empty path, 384 inverted drain clamp, 96 break without a following object, 48 invalid period) |
| AP + MG/RP job mods (synB/C/D, real40; 171dd71 corpus) | own | 2-3 | 880 | 880 |
| synA-D `M7` x2 + "", CL | generated | 3 | 2,520 | 2,520 |
| synA-D `ALL` | generated | 2 | 840 | 840 |
| synC focused pools (M7hd…M7br, M5, M6) | generated | 2 | 1,440 | 1,440 |
| 18 oracle job-mod corpora (`simmods/w_*`) | own | 2 | 1,380 | 1,380 |
| real40 `ALL` + "", CL | generated | 3 | 360 | 360 |

Not exercised by any corpus (implemented and reviewed against the spec only): fuel exhaustion (dense1ms > 1e8
references, FSC steps, AutoGen loops, ReportDelta, bonus score, drain-rate searches), `Math.Clamp` on out-of-order frame
times (the frame decoder's backwards-time filter precedes it), `Math.Sign(NaN)` in ComputeDrainRate / SpinnerSpinHistory /
AdaptiveSpeed, `cumulativeLength` shorter than the path (unreachable through `positionAt`'s binary search), and the
`internal:` rejections.

## Translatability (Charon + Aeneas)

**2026-10-21, total sim (Lean `e0e8215` port), 8 GB VM:** `HEAVY_EXCLUSIVE=1 OUT=… tools/heavy impl/charon_check.sh
--start-from crate::sim --start-from crate::replay` (Aeneas `-sequential`) translates every sim/replay function
**with 0 errors and 0 `sorry`** (Funs.lean 1.3 MB, 1338 definitions incl. loop bodies and the reachable net/beatmap
dependencies; 51 opaque float primitives). Peak RSS 2.6 GB, 6 min wall. The generated Lean is not yet type-checked
against the proofs package. Fixes needed for the `Result` port (rules for later diffs):
* An early exit (`?` or `return`) inside a loop is translated only when the loop is not nested in a branch of a
  surrounding `if`/`match`, and no early exit precedes it in the function (the rest of a function after an early
  `return`/`?` becomes a nested branch in LLBC). So: every loop that can reject is the first statement of its own
  helper function (initial values as parameters; return the loop state, e.g. the remaining fuel, and do post-loop
  checks in the caller): `move_frames`, `spinner_frames`, `slider_frames`, `bonus_spins`, `handle_hit_sto`,
  `generate_objects`, `as_init`/`initial_speeds`; one-iteration bodies with several `?` are helpers too
  (`move_frame_step`, `spinner_frame_step`, `slider_frame_step`, `bonus_spin`, `break_block_period`).
  Otherwise "Early returns inside of loops are not supported yet" / "Breaks to outer loops are not supported yet".
* `let x = if k == Head { slider_data(c, i)?.classic } else { false }` (a `?` on a borrowing call inside a
  value-returning `if`) → "Could not match the contexts": move the `if` into a helper (`is_classic_head`,
  `depth_slider_duration`).
* Indexing a global constant array of byte-string pairs (`COMBOS[ci]`) → "Unimplemented"; a `match` returning the
  literals → "There should be no bottoms in the value". Unrolled calls with literal arguments (`apply_combo`) work.
* `v[i] = x + 1` after a `?` (index assignment with an arithmetic right-hand side) → "Unimplemented binary operation";
  bind the value to a local first (small-crate test).

Earlier (M0-M4 only, 2-core VM):

`charon cargo --preset=aeneas --opaque crate::float --start-from crate::sim --start-from crate::replay` followed by
`aeneas -backend lean -split-files` translates **all 414 sim/replay functions without errors** (generated Lean not yet
type-checked against the proofs package). Translating the whole crate at once needs ~3 GB RSS in `charon-driver`
(earlyoom kills it on this VM), hence the per-module `--start-from`.

Aeneas failures found and fixed (rules to follow when porting later Lean diffs):
* A local shared borrow created *before* a loop and used inside it (`let o = &s.objs[i]; while … o.nested[k] …`)
  → "Could not match the contexts". Index directly in the loop or move the loop into a helper fn that takes the
  reference as a parameter (`os_all_judged`, `push_simulated`, `max_end_time`, `legacy_nested_loop`, …).
  The same error appears on a value-returning `if` chain while borrows from `slider_data(c, i)` are live
  (`slider_result` helper).
* `match slice[i] { Variant { field, .. } => …, _ => {} }` → "Not allowed to expand enumerations with several variants":
  match on `&slice[i]` in a helper with all variants listed (`classic_health_of`, `is_no_fail`).
* A loop that only conditionally overwrites a `usize` accumulator with a by-value param comparison
  (`last_idx_of_kind`) → "Could not compute a loop fixed point": accumulate into an `Option` from a copied field.
* `return` inside a `while` + `Vec` index assignment (`trigger_failure`) → "Unimplemented binary operation": use a
  `stop` flag.

Regression after the Aeneas fixes (commit 50e0b31): synA-D x 3 schedules x {"", CL, NF+CL, CL no-lock}, oracle w_sp2_m5 and
40 real x 3 schedules x {"", CL}: **3360/3360 identical**.
