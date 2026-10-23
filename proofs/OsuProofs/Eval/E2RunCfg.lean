/-
e2e2: the Rust `run_with` relation (stated at `simCtxS`, whose config is `configS`: no `mods`, default debug fields)
transfers to the spec's `runWith` on the real context (`e2_runWith_bridge`), and RunBudgetS transfers between the two
contexts (`e2_runBudget_norm`). The spec congruences are in Eval/E2Cong.lean.
-/
import OsuProofs.Eval.E2EBase
import OsuProofs.Eval.E2Cong
import OsuProofs.Sim.StepInv
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem e2_cfg_norm (c : sim.mods.Config) (C : OsuModel.Sim.Config) (h : ev_cfgRel c C)
    (ht : C.traceObj = none) (hd : C.dbgNoPresence = false) : configS c = { C with mods := [] } := by
  rw [h]; cases C; simp only at ht hd; subst ht hd; rfl

theorem e2_ctx_norm (c : sim.state.Ctx) (CTX : OsuModel.Sim.Ctx) (h : ev_ctxRel c CTX)
    (ht : CTX.cfg.traceObj = none) (hd : CTX.cfg.dbgNoPresence = false) :
    simCtxS ev_tn (alloc.vec.Vec.new _) c = e2N CTX := by
  rw [h.2, e2_cfg_norm _ _ h.1 ht hd]; rfl

/-- the Rust-side spec run (`simCtxS`, `configS`) is the spec run on the real context -/
theorem e2_runWith_bridge (c : sim.state.Ctx) (CTX : OsuModel.Sim.Ctx) (h : ev_ctxRel c CTX)
    (ht : CTX.cfg.traceObj = none) (hd : CTX.cfg.dbgNoPresence = false) :
    OsuModel.Sim.runWith (simCtxS ev_tn (alloc.vec.Vec.new _) c) (abs c.cfg) (playableS ev_tn c.pb) =
      OsuModel.Sim.runWith CTX CTX.cfg CTX.pb := by
  have e := e2_ctx_norm c CTX h ht hd
  have hcfg : (abs c.cfg : OsuModel.Sim.Config) = (e2N CTX).cfg := by
    have := congrArg OsuModel.Sim.Ctx.cfg e; simpa [simCtxS] using this
  have hpb : playableS ev_tn c.pb = CTX.pb := by
    have := congrArg OsuModel.Sim.Ctx.pb e; simpa [simCtxS, e2N] using this
  rw [e, hcfg, hpb]; exact (e2_runWith CTX CTX.pb).symm

set_option maxHeartbeats 0 in
theorem e2_preDho (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) : sc2PreDho C S = sc2PreDho (e2N C) S := by
  e2_cong [OsuProofs.e2_forIn_array, OsuProofs.e2_forIn_range, OsuProofs.e2_forIn'_range, OsuProofs.e2_forIn_list,
    OsuProofs.e2_forIn'_list, OsuProofs.e2_mapM_array, OsuProofs.e2_mapM_list, OsuProofs.e2_foldlM_array,
    OsuProofs.e2_foldlM_list, OsuProofs.e2_loop_nat]
    using (fun n => (e2_applyResult C n).1), (fun n => (e2_applyResult C n).2)

theorem e2_unitsRun (C : OsuModel.Sim.Ctx) : ∀ (l : List (Nat × OsuModel.Sim.Step)) (S : OsuModel.Sim.St),
    sc2UnitsRun (e2N C) l S = sc2UnitsRun C l S := by
  intro l; induction l with
  | nil => intro S; rfl
  | cons p l ih =>
    intro S; obtain ⟨k, stp⟩ := p
    simp only [sc2UnitsRun]
    rw [← e2_preDho, ← e2_stepOnce]
    cases sc2PreDho C { S with k := k, t := stp.time } with
    | error _ => rfl
    | ok q =>
      simp only
      cases OsuModel.Sim.Sim.stepOnce C { S with k := k, t := stp.time } with
      | error _ => rfl
      | ok q2 => exact congrArg _ (ih q2.2)

theorem e2_runBudget_norm (C : OsuModel.Sim.Ctx) (S0 : OsuModel.Sim.St) : RunBudgetS (e2N C) S0 ↔ RunBudgetS C S0 := by
  unfold RunBudgetS runBudgetNeed
  rw [show (e2N C).steps = C.steps from rfl, e2_unitsRun]
  rfl

end OsuProofs
