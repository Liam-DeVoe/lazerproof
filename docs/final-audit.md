# Final-proof audit (D68), 2026-10-23 ~01:00 UTC

This audit was independent and adversarial. It checked whether the end-to-end theorem `eval.evaluate_refines_open`
(Eval/JsonFinal.lean), once `runWith` and RunBudget land, means what the project claims: "the Rust `osu_eval`
computes exactly the spec `OsuModel.Eval.evaluate`". Read-only: no proof or spec was edited. The state audited is
HEAD 7f61100 plus the uncommitted WIP in the tree (json's `ev_strictOk`, simcore2's D67b edits). The audit file
used was proofs/audit.txt from 00:02.

**Verdict.**
- The statement is strong: total correctness, every result field compared, accept/reject mismatches excluded.
- No hypothesis was found that is false on real inputs today. The axioms are standard and no sorry is used.
- Three MAJOR issues would make the finished claim weaker than advertised:
  - M1: RunBudget as drafted is false for Wiggle (WG) on long maps.
  - M2: the theorem is not instantiated at the binary's environment.
  - M3: the untranslated CLI shell (argument parsing and the JSON printer) is outside the theorem and is not
    listed as trusted.
- None of the three is a soundness bug, and none is critical.
- There are 12 minor items.

Findings: **0 critical, 3 major, 12 minor.**

---

## 1. Statement (`ev_topRel`, E2EBase.lean)

`∃ r, eval.evaluate env bm osr opts sched = ok r ∧ ev_topRel r (OsuModel.Eval.evaluate (abs env) (bytesS bm) (bytesS osr) (ev_optsS opts) (ev_schedS sched))`

- **Total correctness.** `= ok r` rules out Aeneas `fail` (overflow, out-of-bounds index, division by zero,
  `to_bits` of NaN) and divergence. So Rust release-mode wrapping arithmetic can never be reached on these inputs.
- **Ok / Ok.** The relation is `R = ev_resS r R.playable`, an equality over all 23 fields of
  `OsuModel.Eval.Result`. 22 of them come from the Rust result. Only `playable` is taken from the spec side,
  because the Rust result does not carry it. The `--dump-playable` path has its own theorem,
  `eval.playable_for_refines`.
- **Err / Err.** The relation compares `E.stage = ev_stageS e.stage`, and `ev_stageS` is injective (7 distinct
  strings).
- **Mixed cases** (Rust Ok and spec error, or the reverse) are `False`. So "same stage" never hides an
  accept/reject disagreement. The intermediate relations `ev_rjRel` and `ev_eRel` also map mixed cases to False.
- **Weakening 1 (minor m1): the rejection reason text is not compared.** `osu_eval` prints the reason in
  `{"rejected": ...}`, so the theorem does not imply byte-identical rejection lines (D33/D34, documented). The
  headline wording ("identical output") should say "identical results; same rejection stage".
- **Weakening 2 (minor m2): float fields are compared as Lean `Float`s.** FunsExternal maps every Rust NaN
  pattern to the model's single NaN (§4). If a NaN ever reached an output field, the printed hex (`hex_d` of the
  real bits) could differ from evaltest's. The audit did not look for a reachable NaN output field, and nothing
  proves that none exists.

## 2. Hypotheses and vacuity

Hypotheses of `eval.evaluate_refines_open`, plus what simcore2 and json say the final theorem will have:

| Hypothesis | True on real inputs? | Evidence |
|---|---|---|
| `O.runWith` (js_EvalOpen) | becomes a theorem | Being proved (simcore2). It must disappear from the final statement (see m11). |
| `O.lzmaBound` = `ev_lzmaBound` | consistent | `lzmaAloneDecode` is an opaque `@[extern]`, so the property is uninterpretable in the logic and cannot be refuted. model/c/lzma_shim.c caps the buffer at `max_out+1` and errors when `len > max_out` (lines 32-64), so it is true of the shim. Trusted, listed in §5. |
| `InputBounds.h64` | consistent (platform) | `System.Platform.numBits` is opaque (32 ∨ 64), so the hypothesis is neither provable nor refutable. True on x86-64. |
| `InputBounds.bmLen`, `osrLen` | yes | Lengths of real files are < 10 MB. |
| `InputBounds.decLines` (∃ N ≤ 2^61, `dec_pathOk N` ∧ lines < 2^31 − 1 ∧ each line < N) | yes | Take N = max line length + 1. For example 2742997.osu has 1150 lines and a longest line of 163 chars. `dec_pathOk N` needs, for every string shorter than N, < 2^32 control points and `calculatePath` < 2^62 points. The control points are ≤ the line length. The spec path is bounded by its fuel: bSpline gets 10^8 iterations × degree points per segment, a circular arc ≤ 2^31 (int-saturated), Catmull 100 per point. That is ≤ 10^8·cps + …, which is below 2^62 for any cps < 2^35. |
| `PlayableBounds.sliderPaths` | yes | Same fuel argument (`optimiseCatmull := true`). |
| `PlayableBounds.decodeTime` / `.gameplay` (`GpbBounds`: st/cpe/cpt/pp/nest/refl/stk/atb incl. `GenOk` ∀ψ) | yes | These are all size bounds. Measured on 2742997.osu + 7738504340.osr (WG DF MU): 758 objects, Σ(nested+1) = 1699 (< 2^31), path ≤ 286 points, cumulative length ≤ 143, nested ≤ 8, 5 breaks. `GenOk`'s "every position map ψ" clause is still bounded, because the path fuel bound does not depend on the positions. |
| `PlayableBounds.simCtx` (`ev_mkBoundsS`; the WIP adds `ev_strictOk`, derived) | yes | Frames: 18178 (< 2^32; and ≤ the decompressed text ≤ 2^28 always). Top kinds ∈ {circle, slider, spinner}: true by construction of `adaptObject` (model/OsuModel/Eval/Adapter.lean:89-100). "∀ ms G, AutoGen.generate P ms = ok G → G.size < 2^62": each generator loop has fuel 10^7 (AutoGen.lean:166/215/233), so G ≤ objects·(3·10^7 + c) < 2^62 for every mod list. |
| `hopts` (override mods `ev_mcOk`, length < 2^61) | yes | What `parse_mods` produces (but see M3). |
| `hsched` (explicit refs·10^8 + 4 < 2^61) | yes | refs < 2.3·10^10. |
| **RunBudget** (D67a/c; not committed yet; simcore2 draft, STATE 23:3x) | **NO for some real inputs (M1)** | See below. |
| Stack (D57, not a hypothesis) | trusted | §5 row. |

The spec values that the hypotheses quantify over are the Rust values for this input. For example
`osu_eval` and `evaltest` (the compiled Lean spec, data/wip/end-to-end-eval/bin/evaltest) give byte-identical
output on 7738504340 (md5 8178c46b…), so the measured sizes are the spec's own.

### M1 (MAJOR, would be partial vacuity): RunBudget with Wiggle's worst-case constant

- **simcore2's draft** (STATE 23:3x):
  - `K c n = objects.len·(n+n+4)`
  - `RunBudget c n B0 := steps.len·K ≤ B0 ∧ B0 + simUnj s0·(n+n+4) + objects.len·(4n+8) + 1 < Usize.max`
- **What n is.** `n` is the custom-state cost that discharges `simCSH`: `sim_ar_cs` uses
  `n = s3b_csCostFrom vis_mods 0`. `s3b_vmCost (.Wiggle _) = s3c_W = 2^31 + 2^25` (Sim3/SB_CS.lean:485,
  SC_Wiggle.lean:92). That is the int32 worst case of `n1 = preempt/100` and `n2 = duration/100`. The real value
  is about 10-100 per object.
- **Consequence with WG.** 2n+4 ≈ 2^32.05, so RunBudget needs steps·objects (+ judgements) < 2^64/2^32.05 ≈
  4.15·10^9. Steps at catchup are about 0.115 per ms of map length; at dense1ms about 1 per ms.
- **The WG replays in the corpus** (all 4 have status ok in index_v2) pass. The largest is 7738504340: catchup
  steps·objs = 2.5·10^7, dense1ms 2.2·10^8.
- **Other real maps fail.** Of the 9419 osu! beatmaps in data/beatmaps, 12 have last-object-time(ms)·objects >
  4.15·10^9, so WG + dense1ms is outside the theorem for them. 2147769.osu (12000 objects, 55 min) is outside it
  even under catchup: about 3.8·10^5 steps × 12000 ≈ 4.5·10^9.
- **Effect.** On those inputs the final theorem is vacuous. It is not wrong.
- **Fix (pick one):**
  - (a) Charge Wiggle its real per-call cost: `n_i = preempt_i/100 + duration_i/100` (+13 for the other
    handlers), so the per-step budget is Σ over alive objects of (2·n_i+4).
  - (b) Make the budget per instance. An instance's trackers only grow when its own object is updated, so
    `steps·(2·n_i+4) ≤ B_i` per instance, without the `objects.len` factor.
  - (c) At least use `#alive` instead of `objects.len` in K. Alive objects are ≤ ~30.
  - Whichever is chosen, state RunBudget on spec/input values (`steps` = the spec ctx's `steps.size`, or a bound
    from frames/refs), not on the Rust ctx. Make it a named §5 row with the numeric margin.
- Without WG, n ≤ 13 and RunBudget holds with a margin of about 2^20.

## 3. Counting honesty

- **The 6 `class_overrides` entries** (became_alive, on_killed, spinner_result, update_bonus_score,
  update_spinner, part_present):
  - The hypotheses are overflow headroom (`completed_spins` bounds, to be folded into RunBudget by D67c) or
    state/ctx well-formedness. That is acceptable as "PROVED".
  - But they also take engine contracts `E : s3b_TfEng P`, `X : simTfX P` and `U : simTfU P`. These are
    structures whose fields are `∃ o', callee = ok o' ∧ spec …`, i.e. callee refinements. proof_status's regex
    (`= ok`/`_refines` in the binder text, PROP_COND for `def … : Prop`) cannot see inside structure types.
  - `s3b_tfEng_s2 : s3b_TfEng s2_tfOk` exists. **No instance `simTfX s2_tfOk` or `simTfU s2_tfOk` exists yet**
    (grep). They are easy (`s2_tfOkS_UT`, `update_transforms_refines`), but the step loop must provide them.
  - (m4) Classify structure hypotheses that have `= ok` fields as CONDITIONAL unless an instance at the concrete P
    is audited.
- **All 23 alias rows (refines_aliases.txt):**
  - The 3 `proved` aliases are real refinements against spec defs: `s2_is_skip` (an inline `== "-12345"`),
    `sim_hr_index_spec` (`HitResult.toNat`) and `js_mk_ctx_full` (`OsuModel.Sim.mkCtx`, no open callees).
  - The 20 FRAGMENT aliases are only credited as COVERED through the call graph. That is sound, because a
    FRAGMENT tag alone never counts.
- **COVERED (35 entries):** the call-graph rule (all Rust callers proved or covered, reachable from a proved
  caller) is sound for end-to-end composition. Every covered entry's parent is proved against the real spec.
- **15 random PROVED entries:**
  - Checked: circle_position, apply_decode_defaults, replay_state_diff, check_hittable, binary_search_f64, fmod1,
    post_process_breaks, rotate_vector, block_vt, add_timing, f64_radians_to_degrees, step_times_of, break_lt,
    barrel_roll_update, add_difficulty.
  - 11 are unconditional refinements against the model def.
  - **4 are not against a spec def:**
    - `block_vt` is against `s3b_vtS`, a copy of a local `let vt`. It is bridged in input_block_periods, so it is
      really COVERED.
    - `break_lt` is against an inline expression of the spec's local `lt`. This is acceptable.
    - `barrel_roll_update` is stated against an explicit Rust-state update, not `.barrelRoll` of
      `playfieldUpdate`.
    - `step_times_of` is stated against `c.steps.map time` (Rust level).
- **"Verbatim copy + rfl bridge" cases:**
  - Bridged and used by a parent proof:
    - `s3d_csS` (`s3d_relax_eq : relaxUpdate = s3d_relaxS := rfl`, used at SD_Relax:449)
    - `s3d_hc` (`s3d_rhc` is used inside the relax_update proof)
    - `s3c_magF` (unfolded against the spec loop inside magnet_update_refines)
    - `s3c_dest0S`, `s3c_sliderZ`, `hop_preSpec`, `hop_holdS`
  - **NOT bridged; the theorem is used nowhere:** `receptor_ref_refines` (`s3c_recRefS`),
    `v_eq_bindable_refines` (`s3c_vEq`), `relax_requirements_refines` (`s3d_reqS`) and
    `repel_slider_clamp_refines` (`s3c_rscS`). Their parents (propagate_press, apply_bindings, relax_update,
    magnet_one) are proved and unfold the callee directly. So they are really COVERED, and nothing checks that the
    "verbatim" copy equals the spec.
- **(m3)** About 6 of 1061 PROVED are inflated. This does not affect the headline theorem.
- **(m10)** proof_status counts any audited theorem named `<fn>_refines` as proved, whatever its statement says.
  Suggested rule: the conclusion must mention an `OsuModel.*` constant, or a proof-local def X with a used
  `X = <spec> := rfl` lemma. Otherwise classify it FRAGMENT, which turns into COVERED automatically.

## 4. Axioms

- audit.txt (00:02): `eval.evaluate_refines` and `eval.evaluate_refines_open` depend on
  `[propext, Classical.choice, Quot.sound]`. There are 0 `sorryAx` and 0 `ofReduceBool`/`trustCompiler` entries.
  `#print axioms` is transitive, so it covers the full dependency cone. check_all's pattern
  `_refines(_\w+)?` includes `_refines_open`.
- No `axiom`, `native_decide`, `implemented_by`, `unsafe` or `skipKernelTC` appears in proofs/OsuProofs (outside
  the Generated templates) or in model/OsuModel. The only exception is the documented `@[extern] opaque
  lzmaAloneDecode`. The custom `elab` tactics produce kernel-checked terms.
- **(m5) A latent sorry:** Sim/InputPhase.lean:60 has `first | scalar_tac | (trace_state; sorry)`. The branch is
  not taken today (no "uses sorry" warning, and the audit is clean), but a Lean or Aeneas bump could silently
  activate it. check_all would then exclude the module, so it would not be unsound, only fragile. Replace it with
  `scalar_tac`.
- **(m11)** As long as the headline takes `O : js_EvalOpen` as a hypothesis, the axiom check is vacuous for the
  open part.
  - When runWith lands, add a named final theorem, e.g. `eval.evaluate_refines_final`, whose only hypotheses are
    `ev_lzmaBound`, `InputBounds`, `PlayableBounds`, `RunBudget`, `hopts` and `hsched`.
  - Have check_all compare its `#check` signature against a committed allowlist, so that a new hypothesis cannot
    be added silently.

## 5. Trusted base

| Item | Documented? |
|---|---|
| Lean kernel and core `Float` semantics as an opaque structure | Only for the rank-1 route (§3). **Not enumerated for the Rust route (m7).** |
| Charon + Aeneas translation (Rust → Lean), rustc/LLVM codegen, Aeneas Std library models (Vec/Slice/scalars) | Only implicitly ("everything else is generated by Aeneas or the library", §4). **Should be explicit (m7).** |
| 5 hand-written std items (F64/F32 clone, Option clone/eq, Vec::pop) | §4 |
| 56 + 2 float primitives, the NaN model, glibc 2.39 libm via dlopen, SSE2 | §4 (D6) |
| LZMA: the opaque function identified on both sides, plus `ev_lzmaBound`. Note: "out of memory" is a nondeterministic error modelled as deterministic. | §4/§5 (the OOM note is missing, minor) |
| Size rows `InputBounds`, `PlayableBounds.*` | §5 |
| RunBudget | to be added (D67a); see M1 |
| Stack (D57) | §5. **Missing:** main.rs falls back to the 8 MiB main stack when the 4 GiB reservation fails (main.rs:628-636), where the limit is about 200k items. It still aborts, never prints a wrong result. |
| Heap exhaustion (Rust aborts on allocation failure) | **missing** (m7). It aborts, never prints a wrong result. |
| Translation freshness (Generated = current impl/src) | Manual only: D54 compared byte-identical, and src has had no semantic change since 18:12 (checked: the last src commits are 6d9d39d/7ec6d6a plus 2 comment-only ones; EvalFuns 10:45, SimFuns 18:39, Funs 09:19 for d7c2a91, and no net/beatmap commits after it). **(m6) Not mechanised:** record a hash of `impl/osu_eval_core/src` at each regeneration and have check_all fail on a mismatch. |
| **CLI shell `impl/osu_eval/src/main.rs` (not translated)** | **No: M3** |

### M2 (MAJOR, statement gap): the environment

- **What the theorem says.** It holds `∀ env`, against the spec at `abs env`. The binary calls
  `evaluate(default_env(), …)` (main.rs:546).
- **What `default_env_refines` gives** (Eval/Osr.lean:2285): `abs default_env = ev_envNorm defaultEnv`, *not*
  `defaultEnv`. The Rust Env has only an `is_pac` flag, so `ev_envNorm` blanks every chain node's `typeName`
  except "OsuPlayfieldAdjustmentContainer".
- **The gap.** The spec reads `typeName` only in the `== PAC` test at Sim/Geometry.lean:53, so
  `evaluate (ev_envNorm E) = evaluate E` is true by inspection. It is **not proved**. The differential tests
  (evaltest vs lazer) use `defaultEnv` itself.
- **Fix (pick one):**
  - (a) Make the spec's `defaultEnv` (Eval/Env.lean) use "" for non-PAC names. This is behaviour-preserving
    (D20c), and then `ev_envNorm defaultEnv = defaultEnv` by `rfl`/`decide`.
  - (b) Prove the invariance lemma.
- Then state the corollary at `env := default_env`.

### M3 (MAJOR, trusted-base gap): the untranslated CLI shell

main.rs contains logic that sits between the user and the theorem:
- argv parsing: option fall-through, schedule names;
- `--mods` → `parse_mods` (proved separately, `eval.mods_json.parse_mods_refines`, but not composed with
  `evaluate`; nothing discharges `hopts` from it);
- `explicit:` file parsing (`parse_explicit`: trim + `double_parse` per line);
- the entire JSON printer (`hex_d`, `jstr`, `acr_json`, `mods_json`, `sem_json`, `rejected_line`, stage/reason
  text, `playable_json`);
- the batch mode.

**None of this is in §4/§5.** It is covered only by byte-identical differential testing against evaltest (D30/D54
regressions).

**Fix:**
- (a) Add a §5 row "CLI shell and output printer (main.rs, untranslated; evidence: byte-identical evaltest
  regressions)".
- (b) Prove a composition lemma: `parse_mods` output satisfies `ev_mcOk` and the length bounds. That discharges
  `hopts` for the CLI path, so the headline covers `--mods`.
- (c) Optionally, move `parse_explicit` and the result serialiser into osu_eval_core so that Aeneas translates
  them.

## 6. Coverage (Generated call graph from `eval.evaluate`)

- **Reachability.** 2323 definitions are reachable from `eval.evaluate` (Funs + SimFuns + EvalFuns + externals),
  scored against docs/proof-status.md of 00:00:
  - 1576 PROVED
  - 70 COVERED
  - 624 not counted: constants, `_loop`/`.body` helpers covered by their function's theorem, `.Insts.` clone
    boilerplate, and the hand-written std items
- **Open:** these are exactly the known runWith cone (all owned):
  - input_phase, step_once, run, run_with, the lifetime_* chain;
  - became_dead and update_slider (landed after the 00:00 audit, "stated (not in audit)");
  - update_dho, update_state and update_state_from_result (CONDITIONAL on step-loop premises);
  - mk_ctx (stale at 00:00, now `js_mk_ctx_full`).
- **FRAGMENT:** idx_list, idx_of_kind, input_lt, slider_body_update, strict_tracking_miss and
  update_slider_nested_kind. These become COVERED once their parents are unconditional.
- **The eval.* rows** are CONDITIONAL only through `A : EvalAssumptions`.

No reachable function is unowned. Once runWith is proved unconditionally, the headline theorem discharges every one
of them by composition. The per-function table is bookkeeping only.

## Minor items, summarised

1. m1: rejection reasons are not compared; say so in the headline claim.
2. m2: float equality is modulo NaN payload; either prove that no output field can be NaN or document it.
3. m3: about 6 PROVED entries are against unbridged copies or Rust-level characterizations. They are really
   COVERED: receptor_ref, v_eq_bindable, relax_requirements, repel_slider_clamp, barrel_roll_update,
   step_times_of.
4. m4: structure-typed engine hypotheses (s3b_TfEng/simTfX/simTfU) escape the CONDITIONAL classifier. The
   `simTfX s2_tfOk` / `simTfU s2_tfOk` instances are still owed.
5. m5: the latent `sorry` alternative at Sim/InputPhase.lean:60.
6. m6: translation freshness is not checked mechanically.
7. m7: §4/§5 should list Charon/Aeneas/rustc/kernel/Aeneas std, heap-exhaustion aborts, the 8 MiB stack fallback
   and the lzma OOM nondeterminism.
8. m8: several trusted `PlayableBounds.simCtx` conjuncts are provable and should be derived to shrink the TCB:
   - top kinds (by construction);
   - the autogen size (fuel 10^7 per loop and objects < 2^32);
   - frames < 2^32 (from `maxPayload`).
9. m9 (fidelity, for the fidelity reviewer): `bSplineToPiecewiseLinear` silently truncates when its 10^8 fuel
   runs out (PathApproximator.lean:111). Every other fuel loop rejects ("fuel exhausted"). lazer never stops
   there. This is only reachable on pathological sliders, but it is a silent divergence rather than a rejection.
10. m10: proof_status does not check what a `<fn>_refines` theorem actually states.
11. m11: pin the final theorem's hypothesis list (allowlist check in check_all), and drop `js_EvalOpen` from it.
12. m12: RunBudget must be stated on spec/input-level values and must appear as a separate named hypothesis, not
    inside EvalAssumptions or ev_ctxWF (D67a). If ev_ctxWF gains fields, mk_ctx_wf must prove them (json).

---

# Pass 2 (2026-10-23, ~04:45 UTC)

Re-audit of the completed headline `osu_eval_refines` (Eval/JsonTop.lean) at HEAD d1b4e4c. The new pieces are
dbfb7a3 (js_EvalOpen = {lzmaBound}), 34fb816 (StepTop), 99b1f19 (LifetimeUpd), 15bca27 (InitLife) and bff03df
(D77 F3). Read-only.

**Findings: 0 critical, 0 major, 8 minor.** All three pass-1 majors are resolved. M1 is resolved pending the
runbudget checker's final report. M2 and M3 were turned into explicit §5 trusted rows rather than proofs, which is
an acceptable resolution. No new hypothesis is false on real inputs.

## A. Axioms and the allowlist (task 3)

- **Axioms.** I loaded the current oleans with `tools/heavy lake env lean` on a file that imports
  `OsuProofs.Eval.JsonTop` and `OsuProofs`, at 04:37:
  - `#print axioms OsuProofs.osu_eval_refines` gives `[propext, Classical.choice, Quot.sound]`.
  - `#print OsuProofs.js_EvalOpen` gives exactly one field, `lzmaBound : ev_lzmaBound`.
  - So the full cone, including the now-proved runWith, step loop, lifetime and initLife, uses only standard
    axioms. Its only non-size hypothesis is the trusted LZMA bound.
  - Caveat (minor N3): proofs/audit.txt dates from 04:04 and predates dbfb7a3/34fb816, and `lake env lean` does
    not rebuild stale oleans. The next check_all window must re-confirm this from a clean build of HEAD.
- **Allowlist.** scripts/headline_signature.txt matches the theorem's `#check` (I compared by eye against the
  committed file). The sorry-token check is in check_all (exit 4), and no `sorry` token remains in
  proofs/OsuProofs outside Generated (pass-1 m5 resolved).
- **N1 (minor): the allowlist pins only the signature text, not the definitions of the named hypotheses.** The
  definitions of `js_EvalOpen`, `InputBounds`, `PlayableBounds`, `ev_mkBoundsS`, `RunBudgetIn`, `SchedFramesIn`
  and `ev_topRel`/`ev_resS` can change without the signature changing. This already happened once, in the safe
  direction: js_EvalOpen went from 3 fields to 1 with the allowlist unchanged. The reverse would also pass
  silently.
  - Fix: add `#print` of these definitions (and of `GpbBounds`, `LoadBounds`, `RunBudgetS`, `e2AccBudS`,
    `ev_simCtxOf`) to the allowlisted block. Alternatively, hash the elaborated definitions.

## B. Vacuity of the new hypotheses (task 1)

### RunBudgetIn (`RunBudgetS` on the spec ctx plus D77 `e2AccBudS`)

- **What changed.** `RunBudgetS` is now `(2U + unj + 1)(2n+4) + objs(4n+8) + 1 < 2^64 − 1 ∧ (U+1)·2·10^6 ≤ 2^54`.
  U = `runBudgetNeed` = the sum, over steps, of the active-list size. So the pass-1 factor `steps × objects` is
  now `Σ alive`, which is pass-1 fix (c). The Wiggle cost `n` is still the worst case `2^31+2^25`, but it now
  multiplies U, not steps·objects.
- **Corpus evidence.** The runbudget checker uses a cheap bound U ≤ steps·objects: 69353 of 69384 triples
  ((map, replay) × schedule × {own mods, +WG}) are cleared by it. The worst real case so far, computed exactly
  (rbcheck exact, exact.jsonl), is 2147769.osu + 7738496475.osr under dense1ms:
  - 3,297,117 steps, 12000 objects, **U = 14,541,791** (max active 18), unj = 24,334
  - lhs64 = 1.7·10^8 with n = 1 (HD)
  - With WG (n ≈ 2^31.02), the first conjunct needs 2U + unj < ~4.2·10^9, i.e. a margin of about 140×.
  - The second conjunct gives 2.9·10^13 ≤ 1.8·10^16, a margin of about 600×.
- **What a failure would take.** Under WG, a map would need U > ~2·10^9 (an average of ~600 alive objects for a
  55-minute dense1ms run). Without WG it would need U > 9·10^9. Neither is realistic.
- **Status.** M1 is resolved, conditional on the checker's final PASS (2 of the 33 residue triples were done at
  04:40). The checker computes U on a VERBATIM copy of the StepInv definitions, compared by
  tools/runbudget/check_defs.py, and a selftest compares the loop against the recursive definition. That is the
  right design.
- **`e2AccBudS`** is Σ(nested+1)·(1 + 2·#AccuracyChallenge) ≤ 2^64 − 1. Real values are ≤ ~25k·3. It could
  only fail with ~10^14 AC mods (an adversarial `--mods` list).

### SchedFramesIn (every spec step has `frameIndex ∈ [−1, frames.size)`)

- **When it can fail.** In `simulateSteps` (Sim/Schedule.lean:84-131) `idx` only increases when
  `frameTime(idx+1) ≤ proposed`, and `frameTime(size) = +∞`. So idx reaches `frames.size` iff a proposed time is
  +∞. idx never goes below −1, because `proposed < frameTime(-1) = −∞` is impossible. With no frames, idx stays −1.
- **Kind schedules (catchup/perframe/dense1ms): true on real inputs.** The references are r0, the frame times and
  endT (dense1ms: floor + 1 steps below endT). Frame times are sums of lazer-parse-limited deltas (≤ int.MaxValue
  each, ≤ 2^28 frames), so they are finite. The manual clock moves by ±16.67 ms or a min/max with finite values.
  Gameplay start and endT come from finite object times.
- **Explicit schedules (minor N2): false if a ref is +∞.** `parse_explicit` uses `double_parse`, which accepts
  `Infinity` (Net/Parse.lean:22,148). On such input the Rust indexes `frames[size]` (Aeneas `fail`, i.e. a panic
  and exit 101) while the spec rejects. That is a disagreement outside the theorem, but never a wrong score.
  - Cheap fix: reject non-finite explicit refs in both the spec and `parse_explicit`, or add the condition to the
    §5 CLI row.
- **Derivable?** Only with an IEEE fact ("finite ± 16.67, min/max of finite values stay finite", plus a bound on
  sums of bounded deltas) about the opaque `F64` operations. Lean's core `Float` arithmetic is opaque to the
  kernel, so this cannot be proved without a float model. Keeping it trusted is justified. The §5 text should
  state the kind-schedule argument above and the explicit +∞ case.

### PlayableBounds.simCtx (new conjunct `tk`: non-spinners have no spinner(-bonus) tick nested objects)

- **True on real inputs.** Nested kinds are created per object type (`createNestedHitObjects`; the adapter's
  `nestedKind` mapping). On the dumped playable of 7738504340 the (object, nested) kinds were only
  slider→{head, tail, tick, repeat}. No generator mod (RD/TP/ST/mirror) adds ticks.
- `ev_strictOk` is derived (`js_strict_of`), not trusted.
- **m8 (still open, minor):** top kinds, the autogen size, frames < 2^32 and now `tk` are provable by construction
  or by fuel, but they remain trusted conjuncts.

## C. Follow-up on the pass-1 findings (task 2)

| Pass 1 | Status |
|---|---|
| M1 RunBudget (WG) | **resolved** (Σ-alive accounting; corpus margin ≥ ~140× with WG), pending the runbudget final PASS |
| M2 Env | **documented**, not proved: JsonTop states the theorem at `ev_envNorm defaultEnv` and says so in its docstring; §5 row `Env.typeNames`. Residual minor N5: the cheap proof (blank non-PAC names in the spec `defaultEnv`, then `rfl`) is still open; evaltest/difftests run at the un-normalised `defaultEnv`. |
| M3 CLI | **documented** (§5 row `CLI shell`); `js_hopts_of_parse_mods` discharges `hopts` for `--mods` (the `< 2^61` count is in the CLI row; trivially true for an argv string). Residual minor N4: the four `text` modules (`eval::text`, `eval::osr::text`, `eval::mods_json::text`, `eval::adapter::text`) are excluded from the translation (translation_fresh.sh eval recipe), and `ev_tn` (E2EBase) is a hand copy of `adapter::text::type_name`. It is identical by inspection (11 entries plus `_ => ""`), and the judgement type names printed by `osu_eval` come from the Rust table. Name these modules and the `ev_tn` copy in the CLI row. |
| m1 / m2 (reason text, NaN payload) | documented in the JsonTop docstring and §5 |
| m3 (about 6 inflated PROVED) | **resolved**: receptor_ref, v_eq_bindable, relax_requirements, repel_slider_clamp, barrel_roll_update and block_vt are now COVERED; step_times_of is FRAGMENT (caller eval.evaluate) |
| m4 (structure-typed owed hypotheses) | **resolved** (56cfc4d); `sc2_tfU_s2 : simTfU s2_tfOk` and `sc2_tfX_s2 : simTfX s2_tfOk` exist (Sim/StepInv.lean) |
| m5 (latent sorry) | **resolved** (no sorry token; check_all exit 4) |
| m6 (freshness) | **resolved** (translation_fresh.sh, 02:42: all three sets identical) |
| m7 (trusted-base rows) | **resolved** (§5.1: kernel, Charon/Aeneas, Std models, rustc/LLVM, heap, stack fallback, lzma OOM, platform) |
| m8 (derive provable trusted conjuncts) | open (minor), now including `tk` |
| m9 (bezier fuel truncation, fidelity) | open (minor); tracked in docs/fidelity-evidence.md item 10 |
| m10 (statement-shape check in proof_status) | partially addressed: the reclassification was done by hand, with no automatic rule (minor) |
| m11 (allowlist) | **resolved** for the signature; see N1 for the definitions |
| m12 (RunBudget named, spec-level) | **resolved** (`RunBudgetIn` on `ev_simCtxOf` spec values, a named §5 row) |

## D. Could the final assembly have weakened anything? (task 4)

- **Context-quantified hypotheses.** `RunBudgetIn` and `SchedFramesIn` quantify `∀ C CTX, ev_simCtxOf … → …`.
  `ev_simCtxOf` is the functional graph of the spec's own staging, which is deterministic, so the quantification
  is over the one context `evaluate` builds. When the spec rejects before building a context, both hypotheses are
  trivially true. That is the safe direction: they get weaker, never stronger. Both use the same environment as
  the conclusion (`ev_envNorm defaultEnv`). OK.
- **`ev_ctxWF`** now has 13 fields: ar, fuel, objs_small, nested_small, tail, vis_first, play, strict,
  frames_small, acts, nsum, h64, tk. All of them are *conclusions* of `sim.step.mk_ctx_wf` (js_wf_build), not
  hypotheses. Each one is derived from `ev_mkBounds`, and therefore from the trusted `ev_mkBoundsS` row, which is
  true on real inputs (B above), or from `h64`. So no field can be unsatisfiable without the theorem failing to
  build.
- **runWith premises.** The field's premises are default debug fields (`e2_ofMods_dbg`), frame indices (from
  `hfi`), `RunBudgetS` (from `hrb`) and the config index facts (`e2CfgIdx`, proved by `e2_ofMods_idx` /
  `s9_ofMods_easy`). Each is discharged inside `osu_eval_refines` (the theorem typechecks with js_EvalOpen = {lzmaBound}).
- **The conclusion is unchanged:** `ev_topRel` with all 23 fields. Only the environment is normalised (N5).
- **Nothing new is trusted** beyond the rows listed above.

## Pass-2 minor items

1. N1: the allowlist does not pin the definitions of the named hypothesis structures.
2. N2: SchedFramesIn is false for explicit schedules containing `Infinity` (Rust panics, spec rejects).
   Document it or reject non-finite refs.
3. N3: re-confirm the headline's axioms from a clean check_all build of HEAD. audit.txt (04:04) predates the
   final commits; my check used the existing oleans.
4. N4: name the excluded `text` modules and the `ev_tn` hand copy in the §5 CLI row.
5. N5 (from M2): the Env invariance lemma, or blanking the names in `defaultEnv`, is still not done. Trusted row.
6. m8: derive the provable `ev_mkBoundsS` conjuncts (top kinds, `tk`, autogen size, frame count).
7. m9: bezier fuel truncation (fidelity).
8. m10: no automatic statement-shape rule in proof_status.
