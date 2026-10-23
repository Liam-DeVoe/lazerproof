# Decisions log (made autonomously; user away)

- D1: Lazer version = latest tagged release at project start; commit pinned in LAZER_COMMIT.
- D2: "Result" = per-object judgements (HitResult incl. ticks/slider ends/bonus), statistics counts, max combo,
  accuracy, standardised total score, pass/fail (with mods like SD/PF/fail). No pp/star rating.
- D3: Oracle = lazer's own code driven headlessly (no rendering), validated against real lazer play-back semantics.
  Real scores' server stats used as an additional check where available.
- D4: Repo local only, never pushed.
- D5: Non-provable parts (float-heavy path math, RNG mods) are modelled faithfully (bit-exact IEEE semantics) and
  covered by exhaustive differential testing; gaps documented, never silently simplified.
- D6 (tentative, see docs/verification-tools.md): Spec in Lean 4 (kernel-reducible Float since 4.33; we define
  .NET-semantics floor/ceil/round-half-even/f64<->f32 ourselves via bits). Rust impl proven against spec via
  Charon/Aeneas; floats via thin F32/F64 bit-wrapper types with trusted, exhaustively tested primitives.
  Transcendentals (pow/atan2/sin/cos/acos) are trusted primitives sharing glibc with .NET; pin glibc version.
  Lean model is natively compiled and itself diff-tested vs lazer early (and is a fallback evaluator).
- D7: Ground truth = lazer headless playback result of the replay, NOT the server-stored stats (live score can
  differ from replay playback). Server stats used only as a sanity signal.
- D8: Disk is tight (~9GB free). Mathlib/Aeneas install deferred until spec+impl exist; keep replay corpus
  compressed and bounded.
- D9: Lazer's judgement depends on the FrameStabilityContainer step schedule (framerate-dependent in real play).
  The model + impl take the *reference-clock trajectory* (hence the step-time schedule) as an explicit input, so
  equivalence holds for every schedule. Canonical schedule for scoring ("the" result): fixed far target, i.e.
  t_{k+1} = SetFrame(next replay frame, or t_k + 1000/60 if gap > 1.2f*1000/60) — what lazer does when catching up /
  fast-forwarding. Oracle also runs per-frame and dense-1ms schedules to measure schedule sensitivity.
- D10: Fixed environment: 1024x768 window, UI scale 1, default config (IncreaseFirstObjectVisibility=true, snaking on),
  default skin. Hit tests replicate the float32 screen-space pipeline for this environment.
- D11: Pass/fail reported with live-Player semantics (fail freezes score at failing judgement, respecting fail overrides);
  ReplayPlayer semantics also reported.
- D12 (see docs/proof-pipeline.md): Proof route = Rust impl translated by Charon/Aeneas (prebuilt release bundle) with a
  *filtered* Mathlib cache (only modules Aeneas imports; ~2.5GB total), proven to refine the Lean spec. Started only once
  the spec reaches M4 and disk allows. Fallback (if disk/Aeneas blocks): optimised Lean evaluator proven equal to the
  clear spec (no Mathlib), Rust as thin FFI shell. Spec code should follow the Lean perf rules in proof-pipeline.md
  where cheap (it is compiled and diff-tested at scale).
- D13: v1 replays are osu!stable scores; their server stats come from STABLE judgement, so oracle-vs-server mismatches
  there reflect lazer(+Classic) != stable, not model errors. The meaningful real-world check is LAZER scores (API v2
  /scores/{id}/download, scope public) vs their server stats: expect near-total agreement, with residual differences only
  in schedule-sensitive judgements (lazer records replays at <=60fps: ReplayRecorder.cs:33,80; live play samples every
  frame). Any non-schedule-sensitive mismatch there = our mental model is wrong. Requested v2 client creds from user.
- D14: D12 confirmed by POC (docs/proof-poc.md). Order: Rust port mirrors Lean defs 1:1 and is diff-tested vs Lean
  executables first (cheap); refinement proofs follow per module.
- D13a (2026-10-21, server-agreement agent): after the disk grew to 50 GB the v2 lazer-score crawl bound was raised
  5000 -> 8000 (crawl_v2_watchdog.sh; ~60 KB/score incl. .osu) and its stop threshold to 10 GB free (budget >= 8 GB).
  Triage (difftest/triage_v2.py) now defaults to pinned sim/evaltest copies in data/oracle_v2/pinned/ because other
  agents relink the live binaries; every triage run is still gated against the oracle's catchup result.
- D15 (G17): The Lean sim is total, with `Except String` as the rejection channel. Fuel exhaustion and internal invariant violations
  reject the input instead of truncating or returning a default. Wherever lazer itself throws (`Math.Clamp` with min>max, `Math.Sign(NaN)`,
  `Path.Vertices[0]` on an empty path, invalid `Period`), the model rejects with `lazer would throw`, consistent with G12. The mods-JSON
  reader stays `partial` (input parsing, no panics).
- D16 (2026-10-21, Rust sim port): the Rust port of the total sim (D15, Lean e0e8215) returns `Result<_, SimErr>` from every
  function through which a spec rejection is reachable; `SimErr` has one variant per spec `throw` site and `simtest_rs`
  renders the spec's exact message, so rejections are diff-tested byte for byte. The spec's `internal: index … out of
  range` accessors (`getA`/`setA`/`need` on invariant-sized arrays) stay Rust indexing (panic = Aeneas `fail`): they are
  unreachable, and refinement only needs "spec `.ok` => same in-range accesses". The proof-POC `crate::schedule` keeps
  the pre-G17 `simulateSteps` (its proof targets a frozen spec copy); the sim uses a rejecting copy in `sim::schedule`.
- D17 (2026-10-21, refinement proofs): proof iteration uses a long-lived file-driven Lean REPL (`proofs/scripts/Repl.lean`,
  ~1.6 GB RSS, idle most of the time) started with `nice` *outside* `tools/heavy`: holding a heavy slot for hours would
  starve other agents, and waiting for a slot starved the REPL (the semaphore is not fair). Every real build/audit
  (`lake build`, `check_all.sh`) still runs under `tools/heavy`. Refinement theorems over strings assume `ValidStr`
  (Unicode scalar values) and size bounds like `len < 2^62`; such guards are stated in the theorem, never assumed silently.
- D18 (2026-10-22, Rust end-to-end port): `impl/osu_eval_core/src/eval/` ports `Eval.lean`, `Eval/Adapter.lean`, `Eval/Env.lean`,
  `Replay/Osr.lean` and `Sim/ModsJson.lean` (the JSON reader Osr and `--mods` depend on) into one new module tree, rather than
  adding files to the sim port's `sim/`/`replay/` (other agents' areas). LZMA stays the trusted boundary: `crate::lzma`
  (opaque to Charon) is a line-by-line port of `model/c/lzma_shim.c` calling the same system liblzma 5.4.5 via
  `dlopen("liblzma.so.5")` (no build script, no new link dependency for simtest_rs/bmdump_rs; Lean links the static
  `liblzma.a` of the same package). Spec `String` messages are error enums with payload ids; texts live in untranslated
  `text` submodules (as `beatmap::errors::text`). Printing mirrors the Lean runtime, which canonicalises NaN in
  `Float.toBits` (checked: `0x7ff8000000000000` / `0x7fc00000`); `osu_eval` prints NaNs canonically. Not ported: the
  spec's debugging option `playableOverride` (`--sim-playable`).
- D19 (2026-10-22, refinement proofs): the proof REPL runs inside `systemd-run --user --scope -p MemoryMax=2800M` (it
  sits at ~2.4-2.6 GB with Mathlib+Aeneas+OsuProofs loaded; a few elaboration requests - `omega` over large contexts -
  grew to 6 GB and earlyoom killed the REPL, which could equally have hit another agent's job). The cap confines such
  runaways to the REPL. Risky proofs are first checked as standalone `lake env lean` runs under the same kind of cap.
  Decimal refinement theorems are guarded by decimal validity (mantissa < 2^96, scale <= 28); the chained callers
  (BindableNumber snapping) discharge the guards with spec-level validity lemmas (`DecimalValid.lean`), so no guard
  surfaces at the framework/mod-settings level.

- D20 (2026-10-22, orchestrator; user-approved) — Proofs are the critical path; machine time reprioritised.
  Meta review: proof throughput fell from ~95 to ~6 fns/h, all proofs hand-written (no @[progress] automation), and one
  Lean proof process costs ~4 GB (2.3 GB private), so proofs could not be parallelised. Decisions:
  (a) server-agreement oracle loop + triage backlog PAUSED (data/oracle_v2/STOP); eval coverage loop at nice 19;
      the lazer-coverage agent continues (targets unexercised branches).
  (b) proof work: automation first (@[progress] lemmas + batch auto-prover), split Generated per module to cut memory
      and allow 2-3 parallel proof agents, breadth before deep arithmetic (hard residue list).
  (c) Lean sim spec FROZEN at 1b0a176 for refinement proofs: any later change to model/OsuModel/{Sim,Replay,Eval*}
      must be justified by a lazer fidelity bug and come with Rust port + proof updates.
- D21 (2026-10-22, lazer coverage): coverage of the lazer and framework code run by the oracle is measured with
  coverlet.console (IL instrumentation). It runs on a separate plain Release build of the unchanged oracle.csproj
  (data/wip/lazer-coverage/covbin; incremental, so the lazer dlls are byte-identical and osu.Framework is the nuget dll),
  never on the deployed R2R binary or its cache. osu.Framework line info comes from the official nuget symbol package
  (.snupkg pdb, CI paths mapped to the osu-framework checkout at the same tag) rather than from a source build of the
  framework, so the measured dll is the one the oracle uses. Triage is driven by never-executed lines and never-entered
  methods; IL branch arms (`?.`, `??`, `is`, `foreach`, `switch`) are only used for single-line conditions. Results are
  in docs/lazer-coverage.md.
- D22 (2026-10-22, orchestrator) — Parallel proof agents. The lead proof agent made scripts/Repl.lean a multi-client
  server (one `import Aeneas`, ~2.3 GB anon; +0.1-0.3 GB per active client) because splitting Generated does not
  help (oleans mapped private+dirtied, not shared). Launched 4 slice agents on the shared server (clients sim, modset,
  decoder, objects); the lead keeps infra (server, Auto/* regeneration, check_all windows), loop automation, and the
  mods/processor/playable slice. No agent may start its own REPL / lake env lean (2.6 GB each).
- D23 (2026-10-22, orchestrator) — Memory goes to the shared proof REPL. The eval coverage loop (extending model-vs-lazer
  catchup coverage beyond 2962/2962 v2 scores; diminishing returns) is paused because its oracle batches (~0.9 GB)
  competed with the proof REPL near its cap. Resume when the proof server has headroom or proofs finish.
- D24 (2026-10-22, objects/slider-path proof agent) — Representation maps for the path/objects slice live in the hand
  proofs (Manual side), not in Auto/Abs: `vS l = (l.map bv2S).toArray` (Rust `Vec<Vec2>`/`&[Vec2]` ↦ spec `Array Vec2`,
  definitionally the `AbsTo` instance), `vvS`, `arcS`, etc. Theorems are `f args = ok (spec ..)` or
  `∃ r, f args = ok r ∧ <map r> = spec ..` with explicit length/size hypotheses where the Rust indexes (the spec's `a[i]!`
  defaults are never reached). Spec loops are rewritten with `forIn_range_idx` to `iterIdx` and matched in lockstep with
  the Aeneas loop by `loop_iterIdx'` (Beatmap/PathApproxBase.lean). Spec-side rewriting with `simp` is avoided once
  float `if`s are present (simp rewrites the condition but not the `Decidable` instance -> type-incorrect goals): the
  Rust side is normalised first (`pa_simp`), then the spec is unfolded and closed by `split`/`rfl`. Client dirs
  objects_N (fresh environment after a committed base changes).
- D25 (2026-10-22, sim proofs agent) — Sim+replay translation = a second module set on top of net+beatmap:
  `Generated/{SimTypes,SimFunsExternal,SimFuns}.lean` (proofs/scripts/install_sim_generated.py drops every Aeneas item
  already in Generated/{Types,Funs} after checking it is textually identical, so the 250 reachable net/beatmap items are
  shared, not duplicated; 2 new trusted primitives `F32.pow`/`F32.asin` in SimFunsExternal). Manual imports SimFuns and
  OsuModel.Sim.Step (header env of the shared REPL). The sim proof files (OsuProofs/Sim/*) use the AbsTo maps of
  Auto/Abs (Sim/Abs.lean adds the sim types) so auto_prove can reuse them; because Auto imports Manual they cannot be
  imported from Manual: each Sim file is imported directly from the root OsuProofs.lean (so check_all audits them).
  Representation: statistics 18-ordinal ↦ 100-entry array (`statsS`), `HObj.typeName` ↦ (`type_id`, name table
  parameter of `hobjS`). Rust changes for Lean elaboration (behaviour-identical, Rust-vs-Rust 10492/10492): `button_bit`,
  `config_add_mod` split in three, `handle_hit_sto` loop as recursion (Aeneas `loop` is not monotone inside a
  `partial_fixpoint` group), `netx::f64_round` = `net::mathops::f64_round`. REPL clients sim2, sim3, … (fresh env each).
- D26 (2026-10-22, mod_settings+names proof agent) — Representation for the mod-settings slice (hand proofs, Manual
  side): setting keys are `beatmap::names` ids, interpreted by `keyName k = keyNames.getD k ""` (`keyNames` = the
  44 Rust literals, same list/shape as gen_abs.py's `AbsTo U32 String`); enum tables by `enumTable`
  (`sectionNames`, `eventTypeNames`, then the AC/MR/BR/AD lists). Key-id lookups agree with the spec's string
  lookups under `KeysOk` (every id < 44; true for all lists built from `Settings.table`), via `keyName_inj`.
  Maps: `jvS`, `styS`, `svS`, `sdS`, `valsS`, `mcS`, `vstrS`; JSON strings carry `JOk` (valid scalars, length
  < 2^62; `JOk'` adds `< Usize.max` for the enum path). Statements: `f x = ok (spec ..)`, `exceptI` for
  `Result<_, NetExn>`, or `∃ r, f x = ok r ∧ map r = spec ..`. Helpers that exist only as local `let`s of the
  `partial def Settings.assign` are stated against named copies (`changedS`, `assignRuleS`, `toModTypeS`, `typeOfR`,
  `dblR`). `assign`/`toMod` themselves are residue: a `partial def` spec is opaque (docs/proof-status.md "Hard
  residue", suggested fix: same fuel on both sides). `proof_status.py` now keeps a hand-written "## Hard residue" tail.
- D27 (2026-10-22, totality agent) — Spec `partial def`s removed (provability fix under D20(c); behaviour-preserving, no
  lazer fidelity change). Audit of model/OsuModel (everything Net/Beatmap/Sim/Replay/Eval reach): the only opaque
  constructs were `Beatmap/ModSettings.lean` `Settings.assign` and `Sim/ModsJson.lean` `ws`/`strBody`/`value`; the rest is
  trusted by design (`@[extern]` libm via Lean core `Float.*`, the LZMA shim `lzmaAloneDecode`, D18). `while`/`repeat`
  are not opaque in Lean 4.35 (`Loop.forIn` = `repeatM`, unfolded by `Loop.forIn_eq_of_monadTail` for Id/Except/StateT/
  ReaderT), and `Array.qsort` is well-founded. Fixes: (a) `assign` = `assignF assignFuel` with explicit fuel
  (`assignF 0 … vals … = vals`; the nested call through `setD` gets `fuel`), `assignFuel = 4`. Bound: at most 2 levels are
  reachable (a WU/WD callback sets the other rate to the snapped `x ± 0.01`, strictly beyond `x`, so the second callback's
  test fails); checked exhaustively over every reachable WU/WD state by model/scripts/assign_depth.lean (49,928
  states: fuel 2 = fuel 64 on all, fuel 1 differs on 24,695). Rust: `assign_f(fuel, …)`, `set_d(fuel, …)`,
  `ASSIGN_FUEL`, `assign` = wrapper. (b) `ws` = `modify wsL`, `strBody acc` = `strBodyL acc` (structural on the
  remaining input), `value` = `valueF (remaining.length + 1)` with nesting fuel (structural on fuel; each nested
  call follows a consumed `[`/`{`/`,`, so remaining < fuel always; fuel 0 throws `internal: JSON nesting fuel exhausted`,
  unreachable). Rust: `value_f(s, p, fuel)` + fuel threaded through `array_value/array_items/object_value/
  object_member/object_items`, `JsonErr::Fuel`; `ws`/`str_body` stay position loops (they already mirrored the list
  recursion). The executable-only reader copy in BmDump/Main.lean stays `partial` (CLI, not mirrored/proved).
  (c) Same commit, orchestrator/objects-proof request: Rust `calculate_path_segment` returns `Option<F64>` (`None` for
  0/1-vertex segments) and `calculate_path` adds only `Some(ol)`, as the spec does (it was `+ D0`, equal except for an
  unreachable `-0` sum). Rust-only; spec unchanged.
  Regression (all byte-identical, 0 mismatch / 0 Lean PANIC): bmdump Lean-new vs Rust-new NoMod 1000 + 2000, random mods
  1200 + 1000, WU-only 400, WD-only 400, fuzz.py 1500, gen.py 1500 + random mods; WU/WD settings grid (13,280 jobs) Lean-new
  = Lean-old = Rust-new; simtest Lean-new vs simtest_rs-new and pinned Lean 1b0a176 vs simtest_rs-new 1110 + 1110
  (M5rate/M5/ALL gen-mods + w_real_m6); evaltest pinned 1b0a176 vs osu_eval-new 4179 (fuzz1 2000, fuzz2 1500, h job-mods
  485, v2 194; 1816 identical rejections), Lean evaltest-new vs osu_eval-new 2170, pinned vs Lean-new 500+ (fuzz2),
  pinned vs osu_eval-new with the slider change 814 (v2 100, h 120, fuzz1 --dump-playable 500). Aeneas on
  mods_json/mod_settings entry points: 0 errors, 0 sorry.
- D28 (2026-10-22, orchestrator) — Proof slices rebalanced. The lead proof agent held infra + loop automation + 72 open
  fns; a new agent (REPL client `mods`) takes mods + mod_random + mod_target_practice + open dotnet sorts/strings + the
  old POC fns (slider/schedule/hit_windows) on the current Generated. Lead keeps processor + playable, infra and loop
  automation (highest leverage). Proof files must be committed at least every ~30 min (sim slice had ~2 h untracked).
  Eval-layer proofs (src/eval: Osr/ModsJson/Adapter/Env/evaluate, translated by the Rust e2e agent) stay unowned
  until the sim core is underway.

## D28 (2026-10-22, mods proof agent) POC `schedule::simulate_steps` refines the total spec in guarded form
The spec `Sim.simulateSteps` became total over `Except` (G17: `Math.Clamp` on out-of-order frames and fuel
exhaustion throw), while the POC Rust `schedule.rs` keeps the old behaviour (clamp error -> unclamped time, no fuel
error). Rather than editing the frozen POC crate, `schedule.simulate_steps_refines` is stated as: if the spec returns
`ok s`, the Rust returns exactly `s` (Rust is defined on more inputs). Spec-side normal form `SpecSched.simulateSteps_ok`.
`dotnet.str_eq2` (no spec def) is stated as `= ok (decide (a.val = b.val))`; `binary_search_f64` assumes len < 2^31.
- D29 (2026-10-22, orchestrator) — Generated regenerations are batched. Provability-driven Rust/spec changes (D27
  assign fuel; slider_path calculate_path `+ ol` for 0/1-vertex segments) are owned by the spec-totality agent, which
  regresses them byte-identically and posts ONE "regenerate Generated for <commit>" request; the lead proof agent then
  regenerates once (HEAVY_EXCLUSIVE, announced window) and fixes fallout only in changed fns. No regen at 09:00.
- D30 (2026-10-22, orchestrator) — Rust edits made for provability need a byte-identical regression before commit
  (Rust sim vs pinned Lean simtest via run_chunks; osu_eval vs pinned evaltest sample). Triggered by 44d9c88
  (sim/scoring.rs update_rank helper, committed without a recorded regression); sim proof agent asked to run it now.
- D31 (2026-10-22, orchestrator) — Sim proofs split to shorten the long pole: agent `sim` keeps the core
  (basic/netx/scoring/state/step), new agent `sim2` takes schedule/geometry/playable/transforms/mods/autogen +
  replay/frames (files under proofs/OsuProofs/Sim2, prefix s2_). New agent `eval` takes src/eval/* and states the
  top-level end-to-end theorem (EndToEnd.lean) with remaining obligations as explicit hypotheses. Objects slice
  finished (69/71; sort_nested/apply_defaults wait on dotnet.list_sort in the mods slice). Proof theorems' size
  hypotheses (numBits = 64, sizes < 2^62 / < 2^32 control points) are platform/input assumptions to be collected
  in docs/proof-pipeline.md's trusted-assumption table.
- D32 (2026-10-22, orchestrator) — earlyoom no longer prefers `lean`/`lake`: under memory pressure (seen 09:34: Aeneas
  2.6 GB + shared REPL 3.4 GB, MemAvailable 1.2 GB) it must kill restartable batch jobs (aeneas, charon-driver,
  dotnet/oracle, bm*/simtest*/evaltest/osu_eval, cargo/rustc), not the shared proof REPL that holds 7 agents' sessions.
- D33 (2026-10-22, decoder proof agent) — conventions of the beatmap.{text,decoder,hit_object_parser} refinement
  proofs: (a) Rust `Result<T, DecodeError>` vs spec `DecodeM` is `hRel f` (both Ok with `f a = b`, or both
  errors; the message is informational because a failing line is dropped); decoder line handlers use `dec_hRel`
  (success with the new state, or failure with the Rust state unchanged). (b) Size preconditions are explicit
  hypotheses: slice lengths `< Usize.max` (every `Vec::push`/`split`), parser inputs `< 2^62` (number parsing),
  `dec_cpiOk` (control-point counts < 2^31) and pending-list lengths for `add_line_points`; the parse chain will
  inherit `numBits = 64`, `cps.len < 2^32` and the spec `calculatePath` size bound from `of_control_points`.
  (c) Legacy `String.splitOn` is characterised through Batteries' byte-position lemmas (copied as `OsuProofs.BStr`):
  one-char separators = `List.splitOn`, and `"//"` = the list splitter `dec_ss2` (two matcher states P0/P1).
  (d) Spec `do` blocks with `let mut` + `if` without `else` elaborate to `have __do_jp` join points that simp
  cannot rewrite with join lemmas (the lemma LHS `have`s are normalised away); such bodies are first proved equal to
  a straight-line chain by case analysis (size regions, then `split` on every match, leaves closed by
  rfl/omega/simp_all; `dec_htp_eq`, ~45 s), and the Rust steps are matched against the chain.
- D34 (2026-10-22, sim2 proof agent) — Statement conventions of the Sim2 slice (proofs/OsuProofs/Sim2/*,
  helpers `s2_*`): a Rust fn returning `Result<T, SimErr>` against a spec `Except String` is stated with
  `s2_rel abs spec rust` (Sim2/Schedule.lean): both `ok` with `abs r = s`, or both rejecting; the spec's message is
  not related to the `SimErr` variant (messages embed `repr`/`toString` of floats; the evaluator's accept/reject and
  every accepted value are covered). Spec loops in `Except` are related to `Option`-valued structural recursion with
  `s2_eo` (`ok ↦ some`, error ↦ `none`) as an equation (`s2_simulateSteps_eo`), so both directions (spec rejects ⇔
  Rust rejects) are proved, not only the guarded `ok ⇒` form of D28. `ActList` lemmas carry `len ≤ 3` (the invariant
  of every list built by `act_push`). Instances added by Sim2 are named (`s2_abs*`, `s2_lawfulAction`) to avoid
  clashes with the sim agent's files in the root import.
- D35 (2026-10-22, eval proof agent) — End-to-end layer proofs (src/eval, proofs/OsuProofs/Eval/*). (a) The eval
  translation is a THIRD module set Generated/{EvalTypes,EvalFuns} (+ hand-written EvalTypesExternal = the opaque
  `lzma::LzmaErr` enum, EvalFunsExternal = `lzma_alone_decode` defined as the spec's opaque `lzmaAloneDecode` on the
  same bytes; trusted, docs/proof-pipeline.md §4), installed by proofs/scripts/install_eval_generated.py exactly like
  SimFuns (items identical to Types/Funs/SimTypes/SimFuns dropped after a textual check; the script's name regex now
  also matches `impl_def` and names on the next line). (b) The eval Lean did not type-check from the committed Rust: 5
  behaviour-identical Rust edits are needed (data/wip/eval-proofs/rust_provability.patch: items loops as recursion in
  the value_f group, no derive(Clone) on the recursive V, `cont`/`beatmap` name clashes, a 36-deep `||` chain split).
  Per the "no Rust edits" rule they are a STATE request (D29/D30); until they land the committed EvalFuns is generated
  from HEAD + that patch (marked PROVISIONAL, not imported by the root, so check_all is unaffected) and proofs are
  developed against it (only mods_json array/object items differ in shape). (c) Representation: the JSON reader's
  remaining input = `(strS s).drop p`; `mods_json::V` ↦ `SimJson.V` by structural mutual recursion through
  Vec/Slice/ListN (`ev_vS`); JSON error ids ↦ the spec's exact messages (`ev_jeS`). Side conditions: input = valid
  scalar values, length + 8 ≤ usize::MAX and < 2^62 (strings inside values then satisfy `JOk'` for to_mod).
- D36 (2026-10-22, decoder proof agent) — trusted input-size assumptions of `beatmap.decoder.decode_refines`
  (for the docs/proof-pipeline.md assumption table): `numBits = 64`; `bytes.len < Usize.max`; for the decoded
  text, `(readLines cs).size + 1 < 2^31` and every line shorter than `N ≤ 2^61` (stated on the spec side,
  `hsize`); and `dec_pathOk N`: for every string shorter than `N`, the spec control points of hit-object
  field 5 number < 2^32 and `SliderPath.calculatePath` returns < 2^62 points (the hypotheses of
  `slider_path.of_control_points_refines`, lifted to all lines). No `sorry`, no extra axioms.
- D37 (2026-10-22, orchestrator) — step.rs split per the sim core agent's proposal: sim3a = slider tracking +
  spinner (Sim3/SA_*, s3a_), sim3b = transform-state hooks + mod update hooks (Sim3/SB_*, s3b_), both against the
  core agent's interface (AbsState/SimM/SimInv, objs/insts size effects). Core keeps hit policy, judgement
  application, lifetime, input phase and the loop. Decoder slice finished (57/57).
- D38 (2026-10-22, orchestrator) — Shared REPL memory watchdog. Two OOM kills of the shared REPL in <1 h (10:43, 11:34),
  each wiping ~8 agents' commit chains. The infra lead adds an RSS watchdog to Repl.lean that cancels the running
  request(s) (IO.CancelToken) above ~4.3 GB and returns an error .out, so a runaway simp/omega kills one request, not
  the server. Top priority for the infra lead.
- D39 (2026-10-22, orchestrator) — Infra lead handover. The original lead proof agent's session ended at 11:58 (processor
  complete; playable 3/5; 519/559 + 133/414 audited). A replacement infra lead (REPL client `infra`) owns the shared
  REPL server + watchdog follow-up (auto-drop of repeat offenders), the 2-hourly check_all windows (next ~13:00),
  D29 batched regens, Auto/* regeneration, trusted-assumption bookkeeping, and playable.get_playable_beatmap/load.
- D40 (2026-10-22, infra lead) — REPL watchdog v2 (deployed at the 13:00 restart). (a) Culprit = the longest-running
  request if it has run >= 10 s (runaway simp/omega/whnf grow over time; a just-started request is rarely the cause),
  else the newest. (b) Lean keeps freed pages, so RSS may stay above the limit after a cancellation (test: 779 MB ->
  896 MB after the cancel); to avoid a cascade of innocent cancellations, the next soft cancellation needs 300 MB of new
  growth over the post-cancel RSS (REPL_MEM_STEP_MB); above REPL_MEM_HARD_MB = 4750 (scope cap 5000M) every running
  request is cancelled. (c) Repeat offenders: culprit twice within 60 min -> its client env is dropped automatically
  (`watchdog_dropped.*`, note in the .out). (d) A stale `drop` file in an unserved client dir is consumed at scan time
  (before: such dirs were never served again). Watchdog log lines list all running requests with durations.
  Tested on an `Init`-header server in a 1G scope (soft cancel, repeat-offender drop, stale drop).
- D41 (2026-10-22, orchestrator) — REPL restarts are expensive (each forces ~8 agents to re-run commit chains; 3 restarts
  11:34-12:33 coincided with the rate falling 84/h -> 35/h). Infra lead: persist + auto-replay client commit chains on
  server start, and restart only in check_all windows or after a crash (batch infra changes into windows).
- D41 (2026-10-22, infra lead, orchestrator request) — Persistent REPL commit chains + restart policy. Each restart
  cost ~8 agents a manual re-commit (proof rate 84/h -> 35/h in the 11:30-12:30 hour). The server now copies every
  successful --commit request to `c_<client>/committed/NNNNN_<name>.lean` and replays the chain (in order, lazily:
  when the client is next served) after a restart or idle drop; failures are renamed `.failed` and logged in
  `c_<client>/replay.log`; an explicit/watchdog drop discards the chain. Migration: at the 13:00 restart the chains of
  the old server are seeded from answered --commit requests since its start/last drop (scripts/repl_seed_committed.py).
  Restarts only in check_all windows or after a crash; infra changes are batched into windows.
- D42 (2026-10-22, infra lead) — Watchdog measures RssAnon, not VmRSS (13:12 incident: VmRSS included ~2.7 GB of
  mmapped .olean pages after the chain replays, so the v2 watchdog sat above its hard limit and cancelled every request
  and replay for ~1 min, auto-dropping 5 clients; chains restored by hand, server restarted 13:13). Limits now soft
  3900 / hard 4500 MB anonymous (base ~2.3-2.5 GB). Cancelled replays keep their chain; replays never count as
  offenses. check_all audits everything that builds (exit 3 = PARTIAL, failed modules listed) so one agent's WIP no
  longer blocks a window; check_all may run with the server up (13:20: build is incremental, audit ~15 s, no OOM risk
  observed), so windows need no restart unless Repl.lean/header changes are pending.
- D43 (2026-10-22, sim3a proof agent) — conventions of the Sim3/SA_* slice (slider tracking + spinner, D37):
  (a) Rust helpers that implement a loop or a fragment *inside* a spec def (no own spec def) are stated against a
  named spec fragment that copies the elaborated spec code: `s3aAllInF` (first loop body of postProcessHeadJudgement),
  `s3aTickF`/`s3aBonusStep`/`s3aBonusLoopF` (updateBonusScore's inner `for` / loop iteration / `while` body,
  the last as a characterisation hypothesis on the actual body `F`), `s3aSpinStepS`/`s3aSpinFramesS` (the spinner
  branch of AutoGen.addClickFrames). The owner of the enclosing fn bridges by `rfl`/unfolding. (b) Callees owned by
  other slices that are not yet proved enter as explicit hypotheses rather than being re-proved here:
  `s3aHF` (sim core's hit_forcefully at the loop's states, for bonus_spin/bonus_spins) and `s3aAddFrameOk`
  (sim2's autogen add_frame, for spinner_frame_step/spinner_frames). (c) `Result<_, SimErr>` vs SimM: `s3aR`
  (Ok ↦ `.ok (f v, S')`, Err ↦ some `.error`); state updates are stated as one `Vec.set` of `objs[i]`
  (`s3a_modifyObj`) so objs/insts sizes and nested arrays are visibly preserved; SimInv carried by `s3a_inv_set`.
- D44 (2026-10-22, orchestrator) — Conditional/fragment theorems are tracked separately. Parallel slices state some
  refinements with hypotheses about other agents' unproved callees, or against local copies of spec loop bodies
  (e.g. sim3a's s3aAllInF/s3aBonusLoopF/s3aSpinStepS). proof-status reports PROVED / CONDITIONAL (with hypotheses) /
  FRAGMENT (with owed bridge); headline = PROVED only; "done" requires 0 CONDITIONAL and 0 FRAGMENT. Bridge owners:
  postProcessHeadJudgement/updateBonusScore/hit_forcefully -> sim core; add_frame/addClickFrames -> sim2.
- D45 (2026-10-22, infra lead) — D44 implementation: proof_status.py classifies each audited `_refines` theorem as
  proved / CONDITIONAL / FRAGMENT. CONDITIONAL is auto-detected from hypothesis types (`= ok`, `_refines`,
  `EvalAssumptions`, unless the subject is a parameter of the theorem: instance-law hypotheses of generic fns such as
  the dotnet sorts are parametric and discharged at each instantiation) or tagged `-- CONDITIONAL: ...`; FRAGMENT only
  by tag `-- FRAGMENT-OF: ...`; `-- NOT-CONDITIONAL:` overrides. Headline counts = proved only; metrics key
  "refinement proofs: conditional/fragment (D44)". My own gpb_main (Playable2) is deliberately not named `_refines`.
- D46 (2026-10-22, orchestrator) — Eval layer split: new agent `json` takes eval.mods_json (~26 open); `eval` keeps
  osr/adapter/env/evaluate/EndToEnd. Mods agent finished (entry points + sorts); new agent `gen` proves the RD/TP
  generator mods to discharge apply_to_beatmap's hRD/hTP.

## D47 (2026-10-22, eval agent): `osr.decode` proved modulo three narrow facts
`EvalAssumptions.osr` (all of `eval::osr::decode`) is replaced by `lzmaBound` (trusted shim bound), `utf8`
(`String.fromUTF8?` agrees with the model's `decodeUtf8`; spec-internal, provable) and `scoreInfo`
(`decode_score_info`, open until the mods_json parser is proved). Rationale: the spec's fast path uses Lean's
`String.fromUTF8?` while the Rust always runs `decode_utf8`; proving the agreement needs Lean-core UTF-8 internals and
is independent of the Rust. `default_env` is proved equal to `Eval.defaultEnv` up to chain type names other than
`OsuPlayfieldAdjustmentContainer` (`ev_envNorm`), which is exactly what the Rust representation (`is_pac`) keeps.
- D48 (2026-10-22, spec-totality agent; D20(c)-permitted provability fix, behaviour-preserving) — `St.dbg` is written only
  under `--trace-obj`. Audit of every `dbg := s.dbg.push` in model/OsuModel/Sim/*.lean: Step.lean theta (523, 625),
  relax (`changeState`, 1394) and the per-step spinner line in `run` (1583) were already guarded by
  `cfg.traceObj.isSome` / `if let some i := cfg.traceObj`; the only unguarded one was the circle/head `life …` engine
  cross-check in `Sim.updateState` (592), now `if !(closed == lifeEnd) && (← ctx).cfg.traceObj.isSome` (f631caa).
  Unblocks `update_state`/`update_state_from_result` in the interface form (`simStS` maps dbg to #[]; sim3b request).
  dbg is read only by SimTest/Main.lean (`IO.eprintln`, stderr); evaltest, Eval*, and the Rust (no dbg field) never see
  it, so stdout cannot change. Regression at f631caa (Lean simtest/evaltest built in a worktree vs simtest_rs/osu_eval
  built from the same tree): simtest 1700 runs (synA ALL gen-mods 240, synC M7 x {,CL} x 3 schedules 720, rej 300 pairs
  600, oracle w_real_all 60 + w_ns_all 80) 1364 identical + 336 identical rejections, 0 mismatch, 0 Lean panic;
  evaltest 1030 jobs (v2 catchup random 500, h_jobmods 485, h_rest 45) 1030 byte-identical, 0 panic/timeout.
  No Generated regen (the spec is not translated); proof agents re-check spec-side lemmas about updateState.
- D49 (2026-10-22, gen agent: Random / Target Practice generator mods) — Size side condition `GenOk` instead of
  per-call path bounds. Random rotates/flips sliders a data-dependent number of times (flip, computeModifiedPosition,
  clampSliderToPlayfield), each rebuilding the slider path from moved control points, so the per-call `MsOk`
  (ModsReflect) cannot be stated up front. `GenOk h` (Post/GenBase.lean) = the current path is in range
  (cumulative < 2^61, calculated < 2^62), < 2^32 control points, and for EVERY position map ψ the path rebuilt from the
  ψ-moved control points is in range (`GenPB`). It is closed under `modifySlider f` (control points compose:
  `genMapPos ψ (genMapPos φ c) = genMapPos (ψ∘φ) c`) and `setPosition`, so it is an invariant of the whole
  repositioning. It is a spec-level machine-range assumption (like InputBounds / D36), true for any real map (the
  path approximators are fuel-bounded per segment); not a refinement hypothesis (D44: no CONDITIONAL).
  Proof technique notes: monadic `for` loops in `DecodeM` via `gen_iterE` + lockstep `gen_loop_iterE` (Except
  analogue of `loop_iterR`, error-flag loops); spec loop bodies whose `do` elaboration duplicates continuations
  (RandomMod.apply: `split`'s internal simp exceeds maxSteps) are normalised with the `gen_case_ite` tactic
  (by_cases on the first closed `ite` + simp with a large step budget); Rust calls returning existentials are made
  rewritable by opaque choice functions (`gen_val`/`gen_valN`: `f x = ok (gen_fR x)`), never by `Exists.choose` of
  the refinement (simp loops on it).
- D50 (2026-10-22, orchestrator) — Build policy to unclog the heavy queue (15:34: 20 waiters, 34-min waits, 3 slots
  held by check_all + Charon + one 21-min lake build). Proof agents: a REPL check (req.sh) is sufficient to COMMIT a
  proof file; run `tools/heavy lake build` on your own new/changed files at most ONCE per ~60 min (batch several files
  in one call) and once before each announced check_all window. Never lake-build just to re-check something the REPL
  already accepted. Regression/Charon jobs keep their chunk rule (<=15 min per heavy call).
- D51 (2026-10-22, orchestrator) — Memory: at 15:45 the box thrashed (swap 2011/2047 MB full, Aeneas 1.1 GB swapped, ~30%
  iowait) with the shared REPL (3.3 GB) + Aeneas + 2 lake builds. Added /swapfile2 (4 GB, fstab) as an OOM buffer, and
  tools/heavy now makes commands containing charon/aeneas wait for 3000 MB MemAvailable in a normal slot (900 MB is
  only right for lake builds/regressions).
- D52 (2026-10-22, json agent) — eval.mods_json + score-info JSON proofs (Eval/Json{Value,Num,Mods,Score,Size,Utf8}.lean).
  (a) Statements are against the real spec; where a spec definition inlines a `do` block (`parseMods`' mapM lambda,
  `apiModToMod`'s acronym/settings matches, `decodeScoreInfo`'s object case, `checkScoreInfo`'s member loop) the proof
  names the piece (`js_modSpec`, `js_acrSpec`/`js_setSpec`, `js_simSpec`, `js_memberOk`) AND proves the bridge to the
  spec definition (`js_parseMods_eq`, `js_apiModToMod_eq`, `js_decodeScoreInfo_eq`, `js_check_spec`), so these are not
  D44 fragments. (b) Score-info errors are related only as "both reject" (their texts never reach the evaluator's
  output); `parse_mods` (the `--mods` CLI path) relates exact messages. (c) Lean 4.35 String API facts (`isNat`,
  `toNat!`, `toInt?`, `any`, `startsWith`, `map toLower`) are proved from core lemmas, not assumed. (d) 64-bit is a
  hypothesis of `parse_mods`/`decode_score_info` (string settings need `len < usize::MAX`), as everywhere else in Eval.
  (e) REPL acceptance is not enough when a proof rewrites with a hypothesis whose statement contains a `match` written
  in the proof file: the generated code's matcher is a different auxiliary constant, which `simp` sometimes failed to
  unify in `lake build` (parse_mod); proofs now case-split instead. Always re-check a whole file in a FRESH client.
- D52 (2026-10-22, infra lead, orchestrator request) — check_all never runs beside the shared REPL: check_all.sh stops
  the server (refuses to run if it cannot), holds /tmp/osu-heavy/check_all.lock, and restarts the server from an EXIT
  trap; repl_server.sh start refuses while the lock is held. A module with `sorry` is excluded like a failed one
  (exit 3, listed); a `_refines` theorem outside namespace OsuProofs is listed as unaudited instead of failing the
  audit. Reason: the 15:00 window's check_all took 60 min next to the REPL (3.8 GB) + Aeneas (thrash, 3 GB swap),
  the rerun with the REPL stopped took 2 min. The 15:00-15:20 rebuild cascade came from the D48 spec change
  (f631caa, model/OsuModel/Sim), not from olean churn: lake build is incremental. server.log rotation + per-request
  markers to attribute Lean PANIC messages (default `lean --run` behaviour: print and continue, not abort).
- D53 (2026-10-22 16:40, orchestrator meta-review) — A background subagent that ends its turn is finished; a Monitor cannot wake it. Agents must wait with blocking until-loops (`timeout 540 bash -c 'until …; do sleep 30; done'`), never end a turn on "waiting". Cause: the D35 landing agent ended at ~16:31 with its regression still running; resumed by the orchestrator. (Note: D52 was used twice, by the json agent and the infra lead; both stand, and the next number is D54.)
- D54 (2026-10-22, D35-landing agent) — The eval provability patch (D35(b), data/wip/eval-proofs/rust_provability.patch:
  mods_json items loops as `array_items_rec`/`object_items_rec` recursion, no derive(Clone) on `V`, osr `cont` ->
  `utf8_cont`, eval `beatmap` params -> `beatmap_bytes`, `is_hit_result_key` split in 4) is landed, plus one shell change
  it needs: the patch was NOT behaviour-identical on adversarial input. The per-item recursion overflowed the 8 MiB main
  stack on a 200k-item score-info array / 200k-member object (a ~10 KB .osr, LZMA), where Lean evaltest and the old Rust
  accept. Fix outside the translation: `osu_eval` main runs `real_main` on a thread with a 4 GiB reserved stack
  (fallback: main thread). This also fixes an older gap: 100k-deep `[[[…]]]` nesting crashed the old Rust too (Lean
  accepts); now byte-identical to Lean on arr1m/arr200k/obj200k/obj30k/deep100k (data/wip/d35-reg/wide). Residual limit
  (~26M items / ~11M nesting levels) is a trusted no-stack-exhaustion assumption, docs/proof-pipeline.md §5; not implied
  by InputBounds (open item for the json agent). Regression (D30), all byte-identical, 0 mismatch / 0 Lean panic /
  0 timeout: osu_eval-new vs pinned Lean evaltest 1b0a176: 7,030 runs (v2 catchup random 1000, h_jobmods 485, h_rest 45,
  fuzz1 2000 + fuzz2 1500 catchup, fuzz1 --dump-playable 2000; 2,880 identical rejections); osu_eval-new vs osu_eval-old
  (HEAD 6407b4e): 21,768 runs (all 7,756 v2 + 4,490 stable catchup, h_jobmods catchup + perframe, fuzz1/fuzz2 catchup,
  fuzz1 dumps, fuzz2 perframe, v2 perframe 1,552; 3,560 identical rejections). Chunks before 15:59 ran the build without
  the stack thread (same core; valid except for the wide/deep cases, checked separately with the final build).
  Charon+Aeneas --start-from crate::eval on the patched crate: 0 errors, 0 sorry; install_eval_generated.py output is
  byte-identical to the committed Generated/{EvalTypes,EvalFuns} (+ templates) after normalising the `Source:` prefix
  `osu_eval_core/src/` -> `src/` (cwd of the run), so no Generated change; PROVISIONAL status of D35 removed.
  lake build OsuProofs.Eval.{EndToEnd,ModsJson,JsonValue,Mod,Osr,Adapter}: OK.
- D55 (2026-10-22, AS-sort agent; D20(c) FIDELITY fix, spec + Rust; commit 7ec6d6a, whose message/comments said
  "D49" by mistake; D49 and D54 were taken, so D55) — `precedingEndTimes` sorts like lazer. Source:
  lazer osu.Game/Rulesets/Mods/ModAdaptiveSpeed.cs:190-205 (`ApplyToBeatmap`), line 193:
  `hitObjects.Select(x => x.GetEndTime()).Order().Distinct().ToList()`. `Order()` is LINQ `OrderBy(identity)` with
  `Comparer<double>.Default` (`double.CompareTo`: NaN below everything and equal to NaN, -0 = +0); .NET 10's
  System.Linq takes the unstable `ImplicitlyStableOrderedIterator` fast path only for `TypeIsImplicitlyStable` types
  (integral/bool/char, not double), so this is the STABLE EnumerableSorter (ties by source index, checked: both names
  present in the runtime's System.Linq.dll 10.0.13). `Distinct()` keeps the first of each `double.Equals` class.
  Spec (Sim/Step.lean precedingEndTimes): `Array.qsort (a < b)` (unstable, IEEE `<`) -> `stableSortBy ts
  (compareD a b < 0)` (existing Sim.Basic stable insertion sort; `compareD` = double.CompareTo). Rust
  (sim/step.rs insert_sorted_f64): `x.lt(v[i-1])` -> `compare_d(x, v[i-1]) < 0`; it is the same scan-from-the-end
  stable insertion as `stableSortBy`/`insPos`, fed the same sequence, so equal on ALL inputs (no qsort lemmas, no
  "no NaN / no ±0" hypothesis for `preceding_end_times_refines`; unblocks the sim core's mk_ctx). Real maps never
  give NaN end times reaching AS (crafted NaN-end playables are rejected earlier: drain-rate Math.Sign / step fuel),
  and equal non-zero doubles are indistinguishable, so the change is observable only with a -0/+0 pair.
  Regression (D30), all byte-identical, 0 mismatch / 0 Lean panic / 0 timeout (data/wip/d49-reg):
  simtest Lean-new vs simtest_rs-new 3,420 runs (AS real job-mod corpora 934, AS synthetic synA-D x 3 schedules 630,
  crafted ±0/NaN end-time playables 80, synB M5rate 240, rej 1,536; 880 identical rejections, 538k judgements);
  pinned Lean 1b0a176 vs Lean-new on the AS corpora 1,564/1,564 (no Lean output change on real data);
  evaltest-new vs osu_eval-new 1,095/1,095 (AS jobs 65, v2 catchup random 500, h_jobmods 485, h_rest 45);
  ORACLE vs Lean-new evaltest on the 65 AS jobs (25 h_jobmods + 40 v2 replays with AS settings): 65/65 match,
  67,395 judgements. Rust changed: sim Generated regen requested (D29).
- D57 (2026-10-22, json agent; numbered D56 by mistake when first committed in 4c09354, owner of the EvalAssumptions discharge) — Stack exhaustion (D54 residual limit: ~26M
  score-info JSON array items / ~11M nesting levels on the 4 GiB stack) is recorded as a TRUSTED execution-level
  assumption in the Eval/EndToEnd.lean docstring (alongside the D54 proof-pipeline §5 row), NOT as an InputBounds field.
  Reason: the Aeneas semantics has no stack, so a size bound in InputBounds would be an unused hypothesis that the proof
  never connects to the executable's behaviour (it would look like coverage without being any); and the JSON text is
  the LZMA-decompressed score info, so an honest input-level bound would have to be stated on the spec decoder's
  intermediate text anyway. The failure mode is an abort, never a wrong result. Also (same agent, same day):
  EvalAssumptions.config now takes `ms.len < 2^62 + 2^61` (config_of_mods_refines needs `2*len+2 < Usize.max`); the
  top-level override bound is tightened to `< 2^61`; the resolved-mods length follows from `js_resolveMods_len`
  (Eval/JsonResolve.lean: `|resolveMods d o| <= |d| + |override|`).
- D56 (2026-10-22 18:40, orchestrator) — No history rewriting on main (amend, rebase, reset, cherry-pick-and-reset): the post-commit hook mirrors every commit to Forgejo at once, so a rewrite diverges the mirror (as happened with ce492bf vs 13f85c8). Correct mistakes with a new commit.
- D58 (2026-10-22, infra lead) — One `lake build` at a time in the proofs workspace: tools/heavy wraps `lake build`
  (cwd under proofs/ or an `OsuProofs` target) in `flock /tmp/osu-heavy/lake-proofs.lock`, and check_all's build takes
  the same lock. Two concurrent lakes rebuilding the same module delete/rewrite each other's .olean files (18:11: the
  REPL restart failed on a missing PathApprox.olean; 18:30: E2EBase failed on a missing Post/Mods.olean). Builds of
  other workspaces (model/, impl/) are unaffected. (Numbering note: two entries are labelled D52; the infra one about
  check_all stopping the REPL is "D52 (infra)".)

- D59 (2026-10-22 19:0x, orchestrator) — sim3b's residue (wiggle, 4 mod hooks over `active`, playfield_update) is split across two new agents, sim3c (wiggle + hnw discharge + depth/magnet) and sim3d (relax/autopilot + playfield_update), so the critical path to runWith runs in parallel. Helper prefixes s3c_/s3d_.
- D60 (2026-10-22 19:35, orchestrator meta-review) — Parallelise the serial sim core chain: sim core hands one self-contained piece (preferably the rest of mkCtx) to the json/E2E agent through a "HANDOFF -> json" STATE request, and keeps the step loop itself.
- D61 (2026-10-22 20:35, orchestrator meta-review) — The status script must count proofs whose theorem names differ from `<aeneas>_refines`: the infra lead adds an alias table and posts a truly-open sim list ("RECON"); owners are assigned from it. Reason: under-counting hides real progress and makes it unclear what is unowned.
- D62 (2026-10-22 20:35, orchestrator) — Proposed split of sim core: sim core keeps the step loop (step_once/run/run_with/simulate, input_phase, lifetime, press propagation); a new agent, sim4, takes the per-object updates (spinner, slider, circle results, update_bonus_score bridge) once sim core confirms the list in STATE "OWNERSHIP".
- D63 (2026-10-22 20:50, orchestrator; answers infra RECON) — New status category COVERED: a helper with no standalone `_refines` (only a restated-body FRAGMENT), all of whose Rust call sites lie inside audited, unconditional parent refinements (checked against the Generated call graph). The headline counts PROVED only; the report shows "proved N, covered M"; end-to-end completeness needs proved + covered.
- D62 (confirmed 20:50) — sim4 launched for spinner/slider/bonus per-object updates, using sim core's OWNERSHIP list (STATE 20:40).
- D64 (2026-10-22 21:05, orchestrator; the user OK'd "push somewhat harder on agent usage") — The CPU was ~50% idle because the bottleneck was agent reasoning time, not the machine. Two more agents: sim5 (sim3c's helper list split: sort_by_lifetime_start, handle_hit_sto, initial_speeds, as_init(_one), err.lift_net, geometry.slider_geom, scoring.legacy_nested) and sim6 (the input press chain split off sim core: trigger_pressed, propagate_press, intercept_press, apply_bindings, legacy_blocked_by_earlier). That makes 9 live agents; agents claim functions in STATE before starting to avoid duplicates.
- D65 (2026-10-22 22:35, orchestrator; APPROVED by the user 22:4x, loop started) — The machine is ~50% idle now that proofs are bounded by agent reasoning, not CPU. Proposal: resume the server-agreement loop (paused under D20) at nice 19 with a memory guard (tools/oracle_bg.sh: rounds only when MemAvailable ≥ 2.8 GB and no check_all; earlyoom prefers dotnet). Status: 5113 scores, 63.1% exact, 35.2% schedule-explained, 46 suspicious (0.9%), 927 untriaged. My restart was blocked by the permission classifier (it reverses a user-approved pause), so it waits for the user. Start command: `mv data/oracle_v2/STOP data/oracle_v2/STOP.old; setsid nohup sh tools/oracle_bg.sh >> data/oracle_v2/loop.log 2>&1 < /dev/null &`.
- D66 (2026-10-22 23:05, orchestrator) — Thrash at 23:04 (48% iowait, 2.3 GB swap): the shared REPL (3.4 GB) plus 3 concurrent private `lean` runs from agents (0.3-0.8 GB each); oracle_bg triage was only 0.14 GB. Rule: every private/standalone lean/lake invocation goes through tools/heavy (memory-gated slots); the shared REPL is preferred. The oracle loop is paused temporarily (STOP) and resumes once the D66 effect is confirmed.
- D67 (2026-10-22 23:15, orchestrator; answers sim core's 22:5x design note) — Step-loop invariant design:
  (a) Transform budget = machine-integer overflow headroom (s2_tfOkS: tracker counters < U64.max, ts/tracker sizes < Usize.max), so it is an input-size assumption, not a behavioural one. `run`/`run_with`/`simulate` take an explicit global hypothesis `RunBudget` (initial budget B0 ≥ (#steps+1)·K(c), with K the per-step append bound) and the per-step invariant carries a decreasing budget. SimARInv gets a slack term for the non-judgement updates (update_dho first load, became_alive). In the end-to-end theorem RunBudget becomes a NAMED trusted size row in proof-pipeline §5 (justification: real inputs need fewer than 2^40 appends against 2^63 headroom), derived from InputBounds where possible. It must not be hidden inside EvalAssumptions.
  (b) simIK / simTK / s3d_IK are restricted to objects whose lifetime state is not Future (they are false initially: no instances, empty tick_insts).
  (c) Ownership after sim core finished: a new agent, simcore2, owns the step invariant (built on sim8's simLifeInv), the ApplyResult.lean edits for (a)/(b), and step_once, run, run_with, simulate, input_phase; it also discharges update_dho's hR from sim7/sim4. mk_ctx_wf goes to json (its offer, 4c46578). The input_phase frame conjuncts (slider_mouse_move, spinner_mouse_move in Sim3/SA_Mouse from the finished sim3a; update_hover; trigger_released) go to sim3d.
- D67c (2026-10-23 00:0x, orchestrator) — The completed_spins overflow premises (update_spinner cs + 2·10^6 ≤ 2^54; bonus cs·360 < 2^63; tracker/spun_out cs + 10^6 ≤ U64.max) are machine-integer headroom like the transform budget. They are folded into RunBudget: the step invariant carries cs ≤ 2·10^6·k, and RunBudget requires (#steps+1)·2·10^6 ≤ 2^54. Same named §5 size row. simcore2 may edit the finished sim4's files to thread D67b's hL.
- D68 (2026-10-23 00:35, orchestrator meta-review) — With the critical path down to 2 serial agents, spare agent capacity goes to the "extreme confidence" half of the goal: an adversarial final-proof audit (vacuity of hypotheses, honesty of counting, axioms, trusted base, coverage; docs/final-audit.md) and a fidelity-evidence review for Lean = lazer (docs/fidelity-evidence.md, ranked next checks). Both read-mostly, with no spec/proof edits; findings are acted on by owners.
- D69 (2026-10-23 00:47, orchestrator) — Thrash at 00:44 (35-45% iowait, 1.9 GB swap): a `lake build` started 4 parallel lean workers (~1.3 GB each) beside the 2.9 GB REPL. tools/heavy now sets LEAN_NUM_THREADS=2 (override with HEAVY_LAKE_THREADS) for `lake build`, which caps lake's job parallelism at 2 workers.
- D70 (2026-10-23 00:5x, orchestrator; acting on docs/final-audit.md 7b69eef: 0 critical / 3 major / 12 minor) —
  M1: RunBudget must be stated on real per-object costs (Wiggle's worst-case accounting made it false for 12/9419 corpus maps under dense1ms, 1 under catchup); acceptance test = it holds on the whole corpus (owner simcore2). Supersedes D67(a)'s "<2^40 appends" justification.
  M2: prove evaluate (ev_envNorm E) = evaluate E and state the headline at default_env (owner json).
  M3: the CLI shell (impl/osu_eval/src/main.rs) is a listed trusted row, plus a parse_mods -> hopts lemma (owner json).
  Minor: hypothesis allowlist for the named final theorem and a sorry grep in check_all; missing trusted-base rows (toolchain, heap OOM, stack fallback, lzma OOM, Generated freshness); ~6 PROVED reclassified COVERED (infra lead); bezier fuel truncation goes to the fidelity reviewer.
- D71 (2026-10-23 01:0x, orchestrator; from docs/fidelity-evidence.md 8c8336d) — Post-headline fidelity plan, queued until the proofs finish (memory). Ranked:
  (1) `oracle player` on ~40 wiring-risk replays (input/transform/rate-ramp/fail mods), with the recorded steps fed to both `oracle run` and evaltest as explicit schedules (~1-2 machine-h; closes "harness = real ReplayPlayer only checked on 9 replays" and "explicit schedules never diff-tested");
  (2) explicit-schedule fuzz (~1 h);
  (3) the 8 never-compared suspicious server scores (~5 min), then the ~570 early-v2 cache entries;
  (4) re-run beatmap model vs C# bmtest, sim_diff and the stable rows at the current spec;
  (5) bezier fuel exhaustion -> reject (spec + Rust + proof patch under D20(c); pathological B-spline only).
  The 5-replay nice-19 pilot is declined until the headline lands, because the machine is at its memory limit.
- D72 (2026-10-23 01:1x, orchestrator) — The audit M2(a) spec fix (blank the non-PAC type names in OsuModel's defaultEnv; behaviour-preserving, since the only read is the PAC equality test) is batched with D71(5) (bezier fuel -> reject) as one post-headline D20(c) spec change with regression (D30), so the spec doesn't churn during final assembly.
- D73 (2026-10-23 01:5x, orchestrator) — simcore2 finished: input_phase PROVED, update_dho discharged via sc2_upd, generic step_once/run/run_with in StepLoop, RunBudgetS/runBudgetOkE defined; root build OK, no sorry. Its residue is split three ways, in parallel:
  - simcore3: concrete simStepInv, initial invariant, playfield contract, update_order facts, RunBudgetS => per-step budget, then step_once/run/run_with/simulate.
  - proc: processors_phase frame plus the health nearest_index invariant (period_is_in_any bound, health frames through the judgement chain).
  - e2e2 (successor of json as E2E owner): cfg-field independence of the spec run/runWith, the ev_ctxWF premise additions, wiring run_with into osu_eval_refines with RunBudgetS as a named top-level hypothesis and §5 row, and the allowlist update.
  sim8 owns simLifeInv (+ alive→active, hands the update loop sc2J (b+|active|)).
- D74 (2026-10-23 02:3x, orchestrator; the user approved direct action) — tools/heavy exclusive mode: for HEAVY_EXCL_PATIENCE s (default 300) an exclusive job polls for all slots free at once WITHOUT holding the gate; only after that does it take the gate and block new jobs. Fixes the 02:12 starvation (exclusive charon_check held the gate 12+ min behind one long job; 5 proof jobs blocked).
- D75 (2026-10-23 02:4x, orchestrator) — Commit hygiene: agents share one index, so `git add X; git commit` also commits files other agents have staged (my 08d03a7 swept in proc's ProcEmit/ProcFrame/ApplyFrame/Press edits; the content was build-verified, so no harm). Rule for everyone: commit with explicit paths, `git commit -m "..." -- <your paths>`, which commits only those paths whatever else is staged.
- D76 (2026-10-23 03:35, orchestrator meta-review) — The critical path is down to 2 small proofs (sim8 lifeC, sim9 initLife), with the machine underused (load 1.5-3.4, 4.4 GB free). The cheapest D71 fidelity items start now at nice 19 with a MemAvailable ≥ 2.5 GB guard, one heavy job at a time: (3) the 8 never-compared suspicious scores, then the early-v2 cache entries; (1) a 5-replay ReplayPlayer pilot with explicit schedules. The proofs keep priority.
- D77 (2026-10-23 03:5x, orchestrator; answers sim9's F3) — The init-state counter headroom F3, Σ(nested+1)·(1+2·#AC) ≤ U64.max (AC = accuracy-challenge mods), is a machine-integer headroom fact of the same kind as RunBudgetS. It is folded into the run-budget size row, not a new trusted row: initLife takes F3 as a premise, e2e2 extends RunBudgetIn (the top-level named hypothesis) with the F3 conjunct, and the runbudget corpus checker verifies F3 on every corpus triple. On real inputs Σ(nested+1) is ~10^4 and #AC ≤ 1. One checked size row covers all counter headroom.
- D78 (2026-10-23 04:35, orchestrator meta-review) — Post-headline sequence: (1) audit pass 2 on the completed osu_eval_refines now (vacuity of RunBudgetIn/F3, SchedFramesIn, simCtx; pass-1 follow-ups), in parallel with the runbudget corpus result and the final check_all; (2) after the final check_all passes, the D72 spec patch (M2a defaultEnv names + bezier fuel -> reject) as one D20(c) change with regression and proof repair; (3) the fidelity extension continues (real-player coverage of the remaining mods + explicit-schedule fuzz); (4) a final summary report for the user (proved / trusted / tested). Optimisation (the user's 100x question) comes only after all of these.
- D79 (2026-10-23 04:5x, orchestrator; from audit pass 2, 3795824: 0 critical / 0 major / 8 minor) — N1 (allowlist also pins the definitions behind the headline), N3 (final check_all from a clean build), N4 (CLI row names the eval::*::text modules and ev_tn) and m10 go to the infra lead. N2 (an explicit schedule containing `Infinity`: the Rust panics where the spec rejects; outside the theorem via SchedFramesIn, and never a wrong score) and N5/M2a join the D72 post-headline spec+Rust patch: reject non-finite explicit schedule times in both spec and Rust (the spec already rejects; make the Rust reject identically, then try to derive SchedFramesIn instead of trusting it), blank the non-PAC names in defaultEnv, and make bezier fuel exhaustion reject.
- D80 (2026-10-23 05:0x, orchestrator; from fidelity-run part 2, 1b82e45) — (a) MISMATCH total_score_without_mods before the first judgement (lazer keeps the Reset(storeResults) perfect-play value, 1,000,000 on the repro; the model starts at 0; Sim/Scoring.lean:70) is a genuine model bug. It joins the D72 post-headline spec+Rust patch: initialise it exactly as lazer does, with a D30 regression from data/wip/fidrun/repro0 plus the fuzz `stop` cases, and proof repair. (b) Empty or decreasing explicit schedule lists: the spec and Rust reject them, matching oracle/Schedule.cs:55,58, in the same patch. (c) A genuine fail under the real Player hangs PlayerRunner (the track frequency ramps to 0 after the fail). Fix it with a SEPARATE oracle build/entrypoint used only for fail-path runs, so the oracle.dll cache stays valid, after the patch; until then the fail path is recorded as tested only through the harness and the ReplayPlayer gate. The headline (Rust refines the model) is unaffected; this is a fidelity correction. The D72 patch starts once e2e2 posts HEADLINE COMPLETE, so the headline is recorded at a fixed commit first.
- D81 (2026-10-23 05:3x, orchestrator; from fail-path run 4407d22) — The real lazer Player now runs failed plays (separate oracle_fail build; oracle.dll and the cache are untouched): 8/8 fail-path cases match bitwise. The known fail-gate deviation (fidelity-evidence §2) is confirmed against the real Player. ReplayPlayer.CheckModsAllowFailure opens the gate on the host-frame reference time (GameplayClockContainer.CurrentTime), while the model and `oracle run` use frame-stable time; 5/8 probe cases differ. This affects ReplayPlayer semantics only, not live play or server scores. It joins the D72 patch as a design item. The ReplayPlayer-mode gate becomes "the reference time of the host frame containing the sub-step ≥ last frame time", in both spec and Rust. Ground truth is `ORACLE_FAIL_GATE=reference oracle_fail run`, with the eight failgate cases as D30 regressions. Before committing, the patch agent must check that catchup/perframe/dense1ms results stay identical on the v2 corpus and on all non-failing replays. It must also decide and document what the catchup schedule's reference times are (its reference is past the last frame, so naive reference gating fails c12184 at 11,179). If the right catchup semantics are unclear, keep the FST gate for catchup and put the deviation in the trusted/tested table instead of guessing. The headless Player's step list is nondeterministic (10 ms wall-clock catch-up budget), so fidelity comparisons always use the steps recorded in that same run.
- D82 (2026-10-23 05:34, orchestrator meta-review) — Structural: the critical path is the runbudget exact queue, which runs serially (~6 min per triple, 22 left, ~2 h) while the machine sits at load 1.4. The checker has been asked to run 3 at a time through tools/heavy. The D72 patch (D72/D79/D80/D81) starts now in a git worktree instead of after the headline: the spec/proof changes are independent of the corpus budget check, and the merge into main waits for HEADLINE COMPLETE, so the headline is recorded at a fixed commit. Owners: runbudget checker, e2e2 (sign-off), D72 patch lead (worktree), oracle_bg (background). Areas net/beatmap/sim/eval: DONE. Fidelity extension: DONE (parts 1–3). Next after the D72 merge: the final report (proved / trusted / tested), then optimisation if the user wants it.
- D83 (2026-10-23 05:5x, orchestrator; user request) — The project is renamed to **lazerproof**. The CLI agent builds it as `lazerproof` now. Repo-wide rename, done in ONE window after the D72 patch merges and no agents are mid-build: `mv ~/lazerproof ~/lazerproof` with a compatibility symlink `~/lazerproof -> lazerproof`; sed the ~1300 path/name occurrences in 99 files (scripts, docs, crontab, the post-commit hook, tools/forgejo); make the tools/heavy lake-lock pattern match both paths (D58: a missed match would bypass the lake lock); `git worktree repair`; rename the Forgejo repo osu/lazerproof -> osu/lazerproof (Forgejo keeps a redirect) and update the remote; README title. Lean/Rust identifiers (OsuModel, OsuProofs, osu_eval_core) stay as they are: renaming them would invalidate the proofs, Generated/ and the headline allowlist for no user-visible gain. Doing it mid-run would break the tools/heavy lake-lock match for processes started under the old $PWD, so it waits.
- D84 (2026-10-23 06:0x, orchestrator; user approved) — The D83 rename is brought forward, together with a ONE-TIME history rewrite that drops oracle/bin-next. It is ppy's lazer build accidentally committed in 3f88501: 165 MB of the 195 MB in .git, and not redistributable. This is the only sanctioned exception to D56. Window: right after HEADLINE COMPLETE is recorded, with all agents at a checkpoint (the D72 lead pauses on its branch), oracle_bg stopped (STOP file) and the crontab paused. Steps:
  1. a full backup bundle of the old history;
  2. `git filter-repo --path oracle/bin-next --invert-paths`;
  3. scan the history for secrets and large files;
  4. `gc --aggressive`;
  5. mv to ~/lazerproof with a symlink at the old path;
  6. rewrite the path/name references, with the tools/heavy lake-lock pattern matching both paths;
  7. recreate the worktrees;
  8. rename the Forgejo repo and force-push;
  9. restore the crontab;
  10. verify: status_check, cargo build, lake no-op build, lazerproof offline;
  11. resume the agents.
  The headline is tagged `headline-v1` before the rewrite. Its hash changes after it, so the docs refer to the tag, and the bundle keeps the original hash.
- D85 (2026-10-23 06:3x, orchestrator) — D84 window executed:
  - backup bundle ~/backups/osu-verified-pre-rewrite-20261023T0616.bundle (old hashes, incl. e9326aa);
  - filter-repo dropped oracle/bin-next: 896 commits, .git 216 MB -> 4.5 MB; the main and D72 working trees are byte-identical to before;
  - history scan clean: no credential values, no tokens, no other binaries, beatmaps or replays;
  - repo moved to ~/lazerproof with a symlink at ~/osu-verified; 50 tracked files renamed; tools/heavy lake-lock matches both paths;
  - Forgejo repo renamed to osu/lazerproof (private), force-pushed, server-side gc 191 MB -> 4.2 MB;
  - crontab, post-commit hook, osu-status.service and the worktree pointers updated;
  - `lake build --no-build OsuProofs`: all 2102 up to date.
  Exception: model/OsuModel/Net/Framework.lean keeps one comment with the old path, because editing it would invalidate the oleans before the headline sign-off; it is renamed in the D72 merge, which rebuilds anyway. Lean/Rust identifiers are unchanged (D83).
- D86 (2026-10-23 06:35, orchestrator meta-review) — Portability (from the user running lazerproof on macOS: "cannot dlopen libm.so.6"). The Rust deliberately dlopens glibc's libm because the trusted float row is "glibc 2.39 x86-64 libm (FMA ifunc variants on FMA CPUs)". A fallback to the platform libm would silently break bit-exactness, so it is NOT allowed. Plan, proposed to the user and awaiting a go:
  (1) Now: an x86-64 Linux container wrapper; on Apple Silicon this must use `--platform linux/amd64`, because aarch64 glibc may differ.
  (2) Release: vendor the glibc 2.39 sources for the 23 libm functions used, built to reproduce the x86-64 FMA variants, statically linked, no dlopen. Also vendor or statically link liblzma. The trusted row becomes "vendored build ≡ glibc 2.39 x86-64", validated exhaustively for the f32 functions and with ≥1e9 random plus corpus-derived inputs per f64 function against the VM's glibc. No Lean proof changes.
Also fixed: tools/heavy and lazerproof run without flock on non-VM hosts (a4d2fda).
- D87 (2026-10-23 06:5x, orchestrator; user: "speed this up with subagents, this is your only task") — D86 (vendored libm) is parallelised: the lead does build.rs/float.rs/lzma.rs integration, and five helpers each own a disjoint vendor dir. H1 sin/cos/tan, H2 asin/acos/atan/atan2, H3 exp/log/log10/pow/cbrt/fmod, H4 the ten f32 functions, H5 the liblzma 5.4.5 decoder. The lead's ifunc finding: FMA variants for sin cos tan asin acos atan atan2 exp log pow sinf cosf expf logf powf; generic for the rest. Portable reproduction: GCC's contractions become explicit __builtin_fma, built with -ffp-contract=off. The D72 lead is paused, and small compiles/tests (<3 min, <500 MB) may bypass tools/heavy. The runbudget synth rerun and e2e2's check_all continue: the headline sign-off is nearly done and runs on its own slots.
- D88 (2026-10-23 07:3x, orchestrator; user: "just do A, I want proof, no probabilistic guarantees") — Performance work. Every optimisation is PROVED equal to the current proved reference (a Lean lemma per optimised function, or a direct re-proof of its refinement), so osu_eval_refines covers the fast evaluator. No unproved fast path and no test-only turbo mode. Build-profile changes that don't change semantics (LTO, codegen-units) are allowed, with byte-identical corpus output. A perf lead works in a worktree on: profile → docs/perf-plan.md → free wins → proved hotspot rewrites, biggest first; helpers launch per disjoint item after "[perf] PLAN READY". It merges after D72. Night priority order: (1) headline sign-off (e2e2 check_all), (2) D86 full validation, (3) resume D72 when CPU frees, (4) perf. Final report after the D72 merge.
- D89 (2026-10-23 07:34, orchestrator meta-review) — The headline is done, so the oracle_bg server-agreement loop is low value overnight: its statistics are established, and the user-reported cases confirm the known replay-vs-live class. It is paused (data/oracle_v2/STOP) to give the 4 cores to D72 (critical for the final report), the D86 full validation and the D88 perf work, in that priority. Restart it after the D72 merge if more server-agreement data is wanted. Owners: D72 lead (+ beatmap helper), D86 lead (validation), perf lead (D88). Finished: e2e2, runbudget, fidelity, all D86 helpers.
- D90 (2026-10-23 08:36, orchestrator meta-review) — Starvation: two perf helpers ran `HEAVY_EXCLUSIVE=1 tools/heavy impl/charon_check.sh`. An exclusive job needs all 3 slots at once, and D72's full lake build holds one for hours. So under the D74 addendum each exclusive waiter held the gate 300 s, backed off 120 s, and repeated, which blocked every other heavy job (5 waiting, load 2). Fix: tools/heavy now runs charon/aeneas one at a time under a dedicated `charon.lock` (taken before a slot, like the D58 lake lock) in a NORMAL slot, and drops HEAVY_EXCLUSIVE for them; the 3 GB MemAvailable guard (D51) still applies. The two waiters were killed (charon had not started) and their agents told to rerun. Rule for all agents: always call MAIN's /home/exedev/lazerproof/tools/heavy (worktree copies are stale), and never set HEAVY_EXCLUSIVE.
- D91 (2026-10-23 09:35, orchestrator meta-review) — check_all stops the shared proof REPL for its whole run. One started from a worktree (D72 at 09:20) does not restart main's REPL afterwards, so REPL users (H-P1s, the perf lead) stalled until the orchestrator restarted it at 09:34. Rule: perf helpers verify on their branches by building their touched modules, `#print axioms` on their new theorems, and corpus/D30 checks; they run NO full check_all. The perf lead runs check_all once after merging the helpers, and once at the final merge to main. Anyone who runs check_all from a worktree runs `~/lazerproof/proofs/scripts/repl_server.sh start` afterwards. status_check already flags "REPL not running" and the 10-min status check restarts it.
- D92 (2026-10-23 10:35, orchestrator meta-review) — About 3,000 lines of sorry-free proof drafts sit uncommitted in the perf worktrees (no branch commit for 2h20m). Rule: every agent commits WIP on its own branch at least every 30 min, or at every milestone (a file builds, a sorry is closed). The commit message is prefixed "WIP:"; WIP commits on worktree branches are fine and get no history rewrite. This protects against agent crashes, context loss and accidental worktree cleanup.
- D93 (2026-10-23 11:35, orchestrator meta-review) — Regression throughput: D72's corpus comparison runs one osu_eval process and one tools/heavy call per replay (2060 jobs in 3h45m), roughly 20× slower than `osu_eval --batch` (12.7k jobs in ~10 CPU-min via impl/tools/perf_corpus.py). Rule: Rust-vs-Rust corpus byte-identity checks use --batch (perf_corpus.py, or an equivalent chunked by heavy call). Lean-vs-Rust D30 regressions after a spec patch use a stratified sample (every mod combination × schedule, the failgate/fuzz/repro cases, plus ~500 random replays) unless the patch touches code reached only by rare inputs. perf_corpus.py moves to main with the perf merge.
- D94 (2026-10-23 12:xx, D72 patch lead; merge of branch worktree-agent-ab4030d638366f6d6) — The D72 post-headline patch has landed. Each item changes the spec and the Rust identically, with a D30 regression and proof repair:
  - **D80a.** `totalScoreWithoutMods` starts at lazer's `Reset(storeResults)` value: `ScoreMax.initWithoutMods` = `(updateScore m0).totalScoreWithoutMods` of the max simulation, passed to `initState`.
  - **D80b / D79-N2.** `explicitRefsCheck` rejects an empty, decreasing or non-finite explicit list at stage "sim". The Rust no longer panics on `Infinity`.
  - **SchedFramesIn.** It cannot be derived: it needs IEEE facts about Lean's kernel-opaque `Float`. It is replaced by a run-time check, `stepFramesOk` / `eval::step_frames_ok` (stage "sim"), so it is no longer a hypothesis of `osu_eval_refines`.
  - **M2a / N5.** `defaultEnv` blanks the non-PAC type names, and the headline is stated at `defaultEnv`.
  - **Bezier fuel.** Fuel exhaustion rejects ("slider path approximation fuel exhausted") instead of truncating.
  - **Item 6 (D81 fail gate).** The frame-stable-time gate is kept and documented as a TESTED deviation row (fidelity-evidence §2.2); reference gating is not adopted because the catchup semantics are unclear.
  - **Allowlist.** Re-recorded, with the diff in proof-pipeline §5.
  - **Regressions.** Listed in fidelity-evidence §2.3: oracle fuzz/failgate/repro all match or are expected rejections; corpus 12,724/12,724 and 2,099/2,099 byte-identical to pre-patch; sim/eval D30 0 mismatch.
- D95 (2026-10-23 12:35, orchestrator meta-review) — The final user report (D78 item 4) had no owner. A report writer now drafts docs/final-report.md from committed evidence only (proved / trusted / tested / known-different, server-agreement limits, portability, performance in replays/s). It fills PENDING entries as "[d72] MERGED … headline-v2" and the perf merge land. Remaining sequence: D72 check_all on main → headline-v2 tag; the perf lead merges main + H-P2, regenerates, re-checks corpus and D30, runs one check_all (deliberate allowlist re-record), merges to main; D86 finishes validation and updates §5.2 with the final numbers; the report is finalised.
- D96 (2026-10-23, D86 portability lead) — Vendored libm/liblzma landed and validated (b11d2a0 integration; vendor dirs by H1-H5 1a8f02b/18d66a8/5f4b024/34cbac2/3fdb98a; docs/proof-pipeline.md §5.2). (a) Variant: on FMA+AVX2 CPUs glibc's ifunc picks the `-mfma -mavx2` builds of sin cos tan asin acos atan atan2 exp log pow sinf cosf expf logf powf (GCC contracts a*b+c there), generic builds for log10 cbrt fmod tanf asinf acosf atanf atan2f. Reproduced portably as explicit `__builtin_fma` + `-ffp-contract=off` (no -m flags), x86 NaN bits made explicit. (b) build.rs calls `$CC` directly (no `cc` crate, so the workspace still has no crates.io deps); vendored always when target_os != linux, opt-in on Linux (`--features vendored` / `vendored-libm` / `vendored-lzma`); the Linux default stays dlopen so the proof pipeline and Charon are unchanged. `verify-libm` feature = validation build (every call compared in-process with dlopen'd glibc). (c) Validation: 0 mismatches. x86-64 gcc and clang: exhaustive f32 unary, ≥2.5e9 per f64 / binary f32 fn plus specials, 2.89e9 corpus calls across 20,476 byte-identical D30 runs. aarch64 gcc and clang under qemu: f32 exhaustive, 1e9 atan2f/powf, 1e8 per f64 fn, 1,486 corpus runs. No function is left dlopen-only. (d) Note: the dlopen build on an x86-64 CPU WITHOUT FMA/AVX2 uses glibc's SSE2 variants, which give different bits, so it does not match the trusted row; the vendored build does not depend on the CPU. Recommendation (not done, it changes the default the proofs were run with): make `vendored` the default on Linux too, or at least build lazerproof with it.
- D97 (2026-10-23 13:1x, orchestrator; resolves the D96 question) — `tools/lazerproof` always uses the vendored glibc 2.39 libm and xz build, on Linux too, built into its own target dir impl/target/lazerproof (`--features vendored`). It rebuilds when the Rust sources are newer than the binary. Reason: the dlopen build gives the trusted float bits only on FMA+AVX2 CPUs, where glibc's ifunc selects the *_fma variants; the vendored build gives them on any CPU and was validated bit-exact (D86: exhaustive f32, ≥2.5e9 per f64 function, 2.89e9 in-corpus calls, aarch64 under qemu). The proof pipeline, Charon and the D30 tooling keep the default dlopen build in impl/target, so no proof or allowlist change. Verified: the lazerproof binary contains the lp_* symbols and no libm.so.6 reference; outputs are unchanged on 3 test scores.
- D98 (2026-10-23 13:35, orchestrator meta-review) — With D72 and D86 done, the perf lead's serial lean build left 3 of 4 cores idle. Parallel work: helper P8 speeds up replay frame decoding (post-P1 profile 11.6%: num_to_f32 7.5%, plus the trusted decimal_string 5.4% via fmt::format) in its own worktree from 264e9d1, with the same rules (swap body + equality proof, no enlargement of the trusted base, corpus byte-identity, no per-branch check_all). Its result merges into the perf branch after the current perf merge to main, as a second perf merge. P4/P5 (step.rs allocation) stay with the lead, after its merge. oracle_bg stays paused (low value).
