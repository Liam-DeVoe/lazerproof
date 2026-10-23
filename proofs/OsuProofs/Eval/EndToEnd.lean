/-
TOP-LEVEL REFINEMENT THEOREM of the end-to-end evaluator (DECISIONS D35).

`OsuImpl.eval.evaluate` (the Aeneas translation of `impl/osu_eval_core/src/eval/mod.rs` `evaluate`: `.osu` bytes +
`.osr` bytes + options + schedule → result or rejection) refines the spec `OsuModel.Eval.evaluate`
(model/OsuModel/Eval.lean, `playableOverride = none`): `eval.evaluate_refines` below.

Hypotheses (all explicit, none are axioms):
* `InputBounds bm osr` — trusted platform / input-size assumptions (docs/proof-pipeline.md §5);
* `EvalAssumptions` — the `_refines` statements of the callees owned by other slices (beatmap decoder/playable,
  replay frames, sim config/schedule/ctx/run/rate) and the open part of this slice (`osr.decode`); see
  E2EBase.lean;
* `PlayableBounds bm osr opts` — trusted spec-level size bounds of the playable pipeline (decoded slider paths;
  `GpbBounds` for the decode-time and the gameplay mod lists; docs/proof-pipeline.md §5 rows `PlayableBounds.*`); the
  decoded control-point / hit-object counts are derived from `InputBounds` (Eval/JsonDecSize.lean);
* well-formed override mods (`ev_mcOk`, as every `ModConfig` built by `to_mod`; fewer than 2^62) and, for an explicit schedule,
  `refs.len * 10^8 + 4 < 2^61` (the step-fuel bound of `simulate_steps`); the override bound is `< 2^61`
  (with the decoded mods' `< 2^62`, the resolved list stays below `2^62 + 2^61`: `config_of_mods`' Vec bound).

TRUSTED (not a hypothesis, D57): the theorem is about the Aeneas semantics, which has no call stack. The compiled
`osu_eval` runs on a 4 GiB stack (D54); the recursive score-info JSON parser (`mods_json` `value_f` /
`array_items_rec` / `object_items_rec`) exhausts it only beyond about 26M array items or 11M nesting levels
(measured), i.e. only on a decompressed score-info text of more than about 2.2*10^7 characters (worst case: nesting). Executions on such
inputs (a stack-overflow abort, never a wrong result) are outside this theorem (docs/proof-pipeline.md §5 row).
-/
import OsuProofs.Eval.Mod
import OsuProofs.Eval.Adapter
import OsuProofs.Eval.JsonStrict
import OsuProofs.Eval.JsonResolve
import OsuProofs.Eval.JsonPBounds
import OsuProofs.Eval.E2Cong
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem ev_vec_mc_clone (v : alloc.vec.Vec beatmap.mod_settings.ModConfig) :
    alloc.vec.CloneVec.clone beatmap.mod_settings.ModConfig.Insts.CoreCloneClone v = ok v := by
  obtain ⟨s', hs, hss⟩ := eq_ok_of_spec (Slice.clone_spec (clone := beatmap.mod_settings.ModConfig.Insts.CoreCloneClone.clone)
    (s := v.slice) (by intro x _; exact ev_mc_clone x))
  rw [alloc.vec.CloneVec.clone, hs, ← hss]; simp

theorem ev_opt_vec_clone (o : Option (alloc.vec.Vec U32)) :
    core.option.Option.Insts.CoreCloneClone.clone (core.clone.CloneallocvecVec core.clone.CloneU32) o = ok o := by
  cases o <;> simp [core.option.Option.Insts.CoreCloneClone.clone, core.clone.CloneallocvecVec, clone_vec_u32]

@[simp] theorem ev_health_clone (h : sim.scoring.HealthSt) : sim.scoring.HealthSt.Insts.CoreCloneClone.clone h = ok h := by
  have hc : ∀ (s : alloc.vec.Vec U64), alloc.vec.CloneVec.clone core.clone.CloneU64 s = ok s := by
    intro s
    obtain ⟨s', hs, hss⟩ := eq_ok_of_spec (Slice.clone_spec (clone := core.clone.CloneU64.clone) (s := s.slice)
      (by intro x _; rfl))
    rw [alloc.vec.CloneVec.clone, hs, ← hss]; simp
  rcases h with ⟨a, b, c, d, e, f, g, r⟩
  cases g <;> simp [sim.scoring.HealthSt.Insts.CoreCloneClone.clone, float.F64.Insts.CoreCloneClone.clone,
    core.option.Option.Insts.CoreCloneClone.clone, hc, lift]

theorem ev_evaluate_compose (A : EvalAssumptions) (env : sim.geometry.Env) (bm osr : Slice U8)
    (hb : InputBounds bm osr) (opts : eval.Options)
    (hopts : ∀ ov, opts.mods_override = some ov → (∀ m ∈ ov.val, ev_mcOk m) ∧ ov.val.length < 2^61)
    (hpb : PlayableBounds bm osr opts)
    (sched : eval.Schedule) (hsched : ∀ refs, sched = .Explicit refs → refs.val.length * 100000000 + 4 < 2^61)
    (hrb : RunBudgetIn (abs env) bm osr opts sched) :
    ∃ r, eval.evaluate env bm osr opts sched = ok r ∧
      ev_topRel r (ev_specEval (abs env) (bytesS bm) (bytesS osr) (ev_optsS opts) (ev_schedS sched)) := by
  unfold eval.evaluate ev_specEval
  obtain ⟨r1, h1, rel1⟩ := eval.decode_beatmap_refines bm osr hb
  rw [h1]; simp only [bind_ok]
  revert rel1
  cases r1 with
  | Err e =>
    cases evS_beatmap (bytesS bm) with
    | ok _ => intro h; exact h.elim
    | error E => intro h; exact ⟨.Err e, rfl, h⟩
  | Ok d =>
  cases hEB : evS_beatmap (bytesS bm) with
  | error _ => intro h; exact h.elim
  | ok D =>
  intro hD; simp only [ev_rjRel] at hD; subst hD
  simp only
  -- .osr
  obtain ⟨r2, h2, rel2⟩ := eval.decode_osr_refines A osr hb.h64 hb.osrLen
  rw [h2]; simp only [bind_ok]
  revert rel2
  cases r2 with
  | Err e =>
    cases OsuModel.Eval.liftE "replay-decode" (OsuModel.Replay.Osr.decode (bytesS osr)) with
    | ok _ => intro h; exact h.elim
    | error E => intro h; exact ⟨.Err e, rfl, h⟩
  | Ok sc =>
  cases hEO : OsuModel.Eval.liftE "replay-decode" (OsuModel.Replay.Osr.decode (bytesS osr)) with
  | error _ => intro h; exact h.elim
  | ok SC =>
  intro hS; obtain ⟨hS, hok⟩ := hS; subst hS
  simp only
  obtain ⟨hokB, hokM, hokT, hokL⟩ := hok
  have hDec := js_evS_beatmap_ok hEB
  have hOsr := js_liftE_ok hEO
  -- decode-time mods
  obtain ⟨w, hw, hwv⟩ := eval.without_unseeded_refines (alloc.vec.Vec.deref sc.bitfield_mods) (by simpa using hokB)
  rw [hw]; simp only [bind_ok]
  have hwok : ∀ m ∈ w.val, ev_mcOk m := by
    intro m hm; rw [hwv] at hm; exact hokB m (by simpa using (List.mem_filter.mp hm).1)
  have hdtm : (ev_dsS sc).bitfieldMods.filter (!OsuModel.Eval.unseededRandom ·) = w.val.map mcS := by
    rw [hwv]; simp only [ev_dsS, ms_deref_val]
    exact (ev_filter_mcS _ (fun x => !OsuModel.Eval.unseededRandom x)).symm
  rw [hdtm]
  -- resolve
  obtain ⟨r3, h3, rel3, hok3⟩ := eval.resolve_mods_refines hb.h64 (alloc.vec.Vec.deref sc.mods) opts (by simpa using hokM)
    (by simpa using hokL) (fun ov h => ⟨(hopts ov h).1, by have := (hopts ov h).2; omega⟩)
  rw [h3]; simp only [bind_ok]
  simp only [ms_deref_val] at rel3
  have hm' : (ev_dsS sc).mods = sc.mods.val.map mcS := rfl
  rw [hm']
  revert rel3
  cases r3 with
  | Err e =>
    cases OsuModel.Eval.resolveMods (sc.mods.val.map mcS) (ev_optsS opts) with
    | ok _ => intro h; exact h.elim
    | error E => intro h; exact ⟨.Err e, rfl, h⟩
  | Ok v2 =>
  cases hRM : OsuModel.Eval.resolveMods (sc.mods.val.map mcS) (ev_optsS opts) with
  | error _ => intro h; exact h.elim
  | ok MODS =>
  intro hM; simp only [ev_rjRel] at hM; subst hM
  have hv2ok := hok3 v2 rfl
  simp only
  -- decode-time check
  obtain ⟨r4, h4, rel4⟩ := eval.decode_time_check_refines A d (alloc.vec.Vec.deref w) (alloc.vec.Vec.deref v2)
    (by simpa using hwok) (by simpa using hv2ok) (by
      have hL := hpb.decodeTime _ _ hDec hOsr
      rw [hdtm] at hL
      exact js_pbOk_of d _ _ (js_decode_beatmap_sz bm osr hb d h1) (hpb.sliderPaths _ hDec) hL
        (by first | rfl | simp [ms_deref_val]))
  simp only [ms_deref_val] at rel4
  rw [h4]; simp only [bind_ok]
  revert rel4
  cases r4 with
  | Err e =>
    cases evS_dtCheck (dec_dbS d) (w.val.map mcS) (v2.val.map mcS) with
    | ok _ => intro h; exact h.elim
    | error E => intro h; exact ⟨.Err e, rfl, h⟩
  | Ok u =>
  cases evS_dtCheck (dec_dbS d) (w.val.map mcS) (v2.val.map mcS) with
  | error _ => intro h; exact h.elim
  | ok U =>
  intro _
  simp only
  -- gameplay playable
  obtain ⟨r5, h5, rel5⟩ := eval.gameplay_playable_refines A d (alloc.vec.Vec.deref v2) (by simpa using hv2ok) (by
    have hL := hpb.gameplay _ _ _ hDec hOsr hRM
    exact js_pbOk_of d _ _ (js_decode_beatmap_sz bm osr hb d h1) (hpb.sliderPaths _ hDec) hL
      (by first | rfl | simp [ms_deref_val]))
  simp only [ms_deref_val] at rel5
  rw [h5]; simp only [bind_ok]
  revert rel5
  cases r5 with
  | Err e =>
    cases evS_gameplay (dec_dbS d) (v2.val.map mcS) with
    | ok _ => intro h; exact h.elim
    | error E => intro h; exact ⟨.Err e, rfl, h⟩
  | Ok pb =>
  cases hG : evS_gameplay (dec_dbS d) (v2.val.map mcS) with
  | error _ => intro h; exact h.elim
  | ok PB =>
  intro hP; simp only [ev_rjRel] at hP; subst hP
  simp only
  -- adapter
  obtain ⟨spb, h6, e6⟩ := eval.adapter.to_sim_playable_refines pb
  rw [h6]; simp only [bind_ok]
  rw [← e6]
  -- frames
  have hbv : (playableS ev_tn spb).beatmapVersion = spb.beatmap_version.val := rfl
  rw [hbv]
  obtain ⟨r7, h7, rel7, hfl⟩ := eval.decode_frames_refines A sc.frame_text spb.beatmap_version hokT
  rw [h7]; simp only [bind_ok]
  have hft : (ev_dsS sc).frameText = sc.frame_text.map vstrS := rfl
  rw [hft]
  revert rel7
  cases r7 with
  | Err e =>
    cases evS_frames (sc.frame_text.map vstrS) spb.beatmap_version.val with
    | ok _ => intro h; exact h.elim
    | error E => intro h; exact ⟨.Err e, rfl, h⟩
  | Ok fs =>
  cases hFr : evS_frames (sc.frame_text.map vstrS) spb.beatmap_version.val with
  | error _ => intro h; exact h.elim
  | ok FS =>
  intro hF; simp only [ev_rjRel] at hF; subst hF
  have hfsl := (hfl fs rfl).1
  have hfac := (hfl fs rfl).2
  simp only
  -- config, schedule leaves
  have hv2len : v2.val.length < 2^62 + 2^61 := by
    have hl := js_resolveMods_len _ _ _ hRM
    simp only [List.length_map] at hl
    have hov : ((ev_optsS opts).modsOverride.map List.length).getD 0 < 2^61 := by
      cases ho : opts.mods_override with
      | none => simp [ev_optsS, ho]
      | some ov => simp [ev_optsS, ho]; exact (hopts ov ho).2
    have := hokL; omega
  obtain ⟨c, hc, hcrel, hcwf⟩ := A.config (alloc.vec.Vec.deref v2) spb (decide ¬ sc.is_legacy_score = true) (by simpa using hv2ok)
    (by simpa using hv2len)
  simp only [ms_deref_val] at hcrel
  rw [hc]; simp only [bind_ok]
  obtain ⟨g, hg, eg⟩ := A.gst spb
  obtain ⟨r0, hr0, er0⟩ := A.r0 spb
  obtain ⟨e, he, ee⟩ := A.endT spb
  rw [hg, hr0, he]; simp only [bind_ok]
  have hlr : (!(ev_dsS sc).isLegacyScore) = decide ¬ sc.is_legacy_score = true := by simp [ev_dsS]
  rw [hlr]
  generalize hC : ({ OsuModel.Sim.Config.ofMods (List.map mcS v2.val) (playableS ev_tn spb) with
    lazerReplay := decide ¬ sc.is_legacy_score = true } : OsuModel.Sim.Config) = C at hcrel ⊢
  -- schedule + context
  have hmb : ev_mkBounds spb fs := ev_mkBounds_of hb.h64 spb fs (by
    have := hpb.simCtx _ _ _ _ _ hEB hOsr hRM hG (by rw [← e6]; exact hFr)
    rwa [← e6] at this) (js_strict_of pb spb h6) hfac
  obtain ⟨r8, h8, rel8, hwf8, hfr8⟩ := eval.sched_ctx_refines A hb.h64 env c spb fs sched C hcrel hfsl hmb hsched
  rw [h8]; simp only [bind_ok]
  revert rel8
  cases r8 with
  | Err e =>
    cases evS_sched (abs env) C (playableS ev_tn spb) (List.map abs fs.val).toArray (ev_schedS sched) with
    | ok _ => intro h; exact h.elim
    | error E => intro h; exact ⟨.Err e, rfl, h⟩
  | Ok nc =>
  obtain ⟨n, ctx⟩ := nc
  cases hSc : evS_sched (abs env) C (playableS ev_tn spb) (List.map abs fs.val).toArray (ev_schedS sched) with
  | error _ => intro h; exact h.elim
  | ok NC =>
  obtain ⟨N, CTX⟩ := NC
  rintro ⟨hN, hcc, hCc, hcp, hCp, hrel⟩
  have hsc : ev_simCtxOf (abs env) bm osr opts sched C CTX :=
    ⟨_, _, _, _, _, N, hEB, hOsr, hRM, hG, by rw [← e6]; exact hFr, by rw [← e6, hlr]; exact hC.symm,
      by rw [← e6]; exact hSc⟩
  have hdbg : CTX.cfg.traceObj = none ∧ CTX.cfg.dbgNoPresence = false := by
    rw [hCc, ← hC]; exact e2_ofMods_dbg _ _
  have hSt0 : CTX.steps = abs ctx.steps := by
    have := congrArg OsuModel.Sim.Ctx.steps hrel.2; simpa [simCtxS] using this.symm
  have hFr0 : CTX.frames = abs ctx.frames := by
    have := congrArg OsuModel.Sim.Ctx.frames hrel.2; simpa [simCtxS] using this.symm
  -- (D72) the frame-index range is checked by `sched_ctx` (`step_frames_ok`), no longer the trusted row SchedFramesIn
  have hfi' : ∀ st ∈ ctx.steps.val, -1 ≤ st.frame_index.val ∧ st.frame_index.val < (ctx.frames.val.length : Int) :=
    hfr8 n ctx rfl
  have hidx : e2CfgIdx CTX.cfg := by rw [hCc, ← hC]; exact e2_ofMods_idx _ _
  obtain ⟨r9, h9, rel9⟩ := A.runWith ctx CTX hrel (hwf8 n ctx rfl) hdbg.1 hdbg.2 hidx hfi'
    (fun S0 h => hrb.1 C CTX S0 hsc h) (hrb.2 C CTX hsc)
  rw [hCc, hCp] at rel9
  have hrc : ev_cfgRel ctx.cfg C := by rw [hcc]; exact hcrel
  have hrcwf : ev_cfgWF ctx.cfg := by rw [hcc]; exact hcwf
  obtain ⟨r10, h10, rel10⟩ := eval.true_gameplay_rate_refines A ctx.cfg C hrc hrcwf
  obtain ⟨v8, h8', hv8⟩ := eval.step_times_of_refines ctx
  have hctx := hrel.2
  revert rel9
  cases r9 with
  | Err x =>
    cases hRW : OsuModel.Sim.runWith CTX C (playableS ev_tn spb) with
    | ok _ => intro h; exact h.elim
    | error _ =>
      intro _
      simp only [hRW]
      exact ⟨.Err ⟨.Sim, .Sim x⟩, by simp [h9, eval.sim_rej, eval.reject],
        by simp [OsuModel.Eval.liftE, ev_topRel, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw, ev_stageS]⟩
  | Ok s6 =>
  cases hRW : OsuModel.Sim.runWith CTX C (playableS ev_tn spb) with
  | error _ => intro h; exact h.elim
  | ok S =>
  intro hS; simp only [ev_eRel] at hS; subst hS
  simp only [hRW]
  simp only [OsuModel.Eval.liftE, pure, Except.pure]
  revert rel10
  cases r10 with
  | Err x =>
    cases evS_rate C with
    | ok _ => intro h; exact h.elim
    | error _ => intro h; exact ⟨.Err x, by simp [h9, h10], by simpa [ev_rjRel, ev_topRel] using h⟩
  | Ok rate =>
  cases evS_rate C with
  | error _ => intro h; exact h.elim
  | ok RATE =>
  intro hR; simp only [ev_rjRel, id] at hR; subst hR
  refine ⟨.Ok ({ is_legacy_score := sc.is_legacy_score, replay_version := sc.container.version,
                  replay_beatmap_hash := sc.container.beatmap_hash, decoded_mods := sc.mods, mods := v2, true_gameplay_rate := rate,
                  hit_objects := alloc.vec.Vec.len spb.objects, frames := alloc.vec.Vec.len fs,
                  schedule_kind := (match sched with | .Kind k => some k | .Explicit _ => none), r0 := r0,
                  end_time := e, gameplay_start_time := g, last_frame_time := ctx.last_frame_time,
                  references := n, steps := alloc.vec.Vec.len ctx.steps, step_times := v8,
                  live := ({ score := s6.score, health := s6.health } : eval.SemResult),
                  replay_player := (if s6.health.fail_triggers = 0#u64 then none else some ({ score := s6.score_rp, health := s6.health_rp } : eval.SemResult)),
                  max_stats := ctx.smax.max_stats, judgements := s6.out, score_multiplier := ctx.cfg.score_multiplier } : eval.EvalResult), ?_, ?_⟩
  · cases sched <;> by_cases hz : s6.health.fail_triggers = 0#u64 <;>
      simp [h9, h10, h8', hz, ev_opt_vec_clone, ev_vec_mc_clone]
  · have hL : CTX.lastFrameTime = ctx.last_frame_time := by
      have := congrArg OsuModel.Sim.Ctx.lastFrameTime hctx; simpa [simCtxS] using this.symm
    have hSt : CTX.steps = abs ctx.steps := by
      have := congrArg OsuModel.Sim.Ctx.steps hctx; simpa [simCtxS] using this.symm
    have hSm : CTX.smax = abs ctx.smax := by
      have := congrArg OsuModel.Sim.Ctx.smax hctx; simpa [simCtxS] using this.symm
    have hSM : (OsuModel.Sim.Config.ofMods (List.map mcS v2.val) (playableS ev_tn spb)).scoreMultiplier =
        ctx.cfg.score_multiplier := by
      have h1 := congrArg OsuModel.Sim.Config.scoreMultiplier hC
      have h2 := congrArg OsuModel.Sim.Config.scoreMultiplier hcrel
      simp only [configS] at h2
      rw [hcc, h2, ← h1]
    simp only [ev_topRel]
    rw [hL, hSt, hSm, hSM, er0, ee, eg]
    have hz' : s6.health.fail_triggers.val = 0 ↔ s6.health.fail_triggers = 0#u64 :=
      ⟨fun h => UScalar.eq_of_val_eq (by simpa using h), fun h => by rw [h]; rfl⟩
    cases sched <;> by_cases hz : s6.health.fail_triggers = 0#u64 <;>
      simp [ev_resS, ev_semS, ev_dsS, ev_containerS, simStS, hz, hz', hv8, ev_schedName, ev_schedS, playableS, abs,
        hN, OsuModel.Eval.Schedule.name]

/-- **The end-to-end refinement theorem** (open obligations: `EvalAssumptions`). -/
theorem eval.evaluate_refines (A : EvalAssumptions) (env : sim.geometry.Env)
    (bm osr : Slice U8) (hb : InputBounds bm osr) (opts : eval.Options)
    (hopts : ∀ ov, opts.mods_override = some ov → (∀ m ∈ ov.val, ev_mcOk m) ∧ ov.val.length < 2^61)
    (hpb : PlayableBounds bm osr opts)
    (sched : eval.Schedule) (hsched : ∀ refs, sched = .Explicit refs → refs.val.length * 100000000 + 4 < 2^61)
    (hrb : RunBudgetIn (abs env) bm osr opts sched) :
    ∃ r, eval.evaluate env bm osr opts sched = ok r ∧
      ev_topRel r (OsuModel.Eval.evaluate (abs env) (bytesS bm) (bytesS osr) (ev_optsS opts) (ev_schedS sched)) := by
  rw [ev_specEval_eq]
  exact ev_evaluate_compose A env bm osr hb opts hopts hpb sched hsched hrb

end OsuProofs
