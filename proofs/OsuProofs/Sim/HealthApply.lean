/-
`sim::step::{health_apply, acc_challenge, emit_one}` (Rust) refine `Sim.healthApply`, `Sim.accChallenge` and the
`one` of `Sim.emit` (HealthProcessor, then ScoreProcessor, then AC, for one fail semantics).
-/
import OsuProofs.Sim.ScoringEq
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

theorem sim.step.health_apply_refines (h0 : sim.scoring.HealthSt) (hc : sim.scoring.HealthCfg) (c : sim.mods.Config)
    (j : sim.scoring.JInfo) (t : F64) (rp : Bool) (lf : Option F64)
    (hk : ∀ k, sim.mods.FailOverride.Easy k ∈ c.fail_overrides.val → k.val < h0.retries.val.length)
    (ht : h0.fail_triggers.val + 1 ≤ U64.max) :
    ∃ r, sim.step.health_apply h0 hc c j t rp lf = ok r ∧
      OsuModel.Sim.Sim.healthApply (abs h0) (abs hc) (abs c) (abs j) (abs t) (abs rp) (abs lf) = .ok (abs r.1, r.2) := by
  cases hf : h0.has_failed
  · obtain ⟨cr, inc, hif, eif⟩ := sim.scoring.increase_for_refines h0 hc j false
    rcases h0 with ⟨hh, hfl, crr, ni, ft, fld, fti, rts⟩
    simp only at hf; subst hf
    let h1 : sim.scoring.HealthSt := ⟨OsuModel.Sim.clamp01 (hh + inc), false, cr, ni, ft, fld, fti, rts⟩
    obtain ⟨tf, htf, etf⟩ := sim.step.trigger_failure_refines c h1 t rp lf hk ht
    unfold sim.step.health_apply OsuModel.Sim.Sim.healthApply
    simp only [hif, sim_health_clone, float.F64.add, sim_clamp01_eq, bind_ok, Bool.false_eq_true, ite_false,
      sim_default_fail_condition_eq, sim_any_fail_condition_eq]
    rw [eif]
    have e1 : ∀ A : OsuModel.Sim.HealthSt, A = abs (⟨hh, false, crr, ni, ft, fld, fti, rts⟩ : sim.scoring.HealthSt) →
        ({ ({ A with comboResult := cr.val } : OsuModel.Sim.HealthSt) with health := OsuModel.Sim.clamp01 (A.health + inc) } : OsuModel.Sim.HealthSt) = abs h1 := by
      intro A hA; subst hA; rfl
    simp only [e1 _ rfl]
    simp only [uncurry_apply_pair]
    rw [show (⟨OsuModel.Sim.clamp01 (hh + inc), false, cr, ni, ft, fld, fti, rts⟩ : sim.scoring.HealthSt) = h1 from rfl]
    simp only [htf, bind_ok]
    by_cases hb : OsuModel.Sim.defaultFailCondition (abs h1) (abs j) = true
    · have etf' : OsuModel.Sim.Sim.triggerFailure (abs c) (abs h1) t rp (abs lf) = .ok (abs tf) := etf
      simp [hb, etf', Except.bind, pure, Except.pure]
    · by_cases hb1 : (abs c : OsuModel.Sim.Config).failConds.any (OsuModel.Sim.Sim.failCondition (abs j)) = true
      · have etf' : OsuModel.Sim.Sim.triggerFailure (abs c) (abs h1) t rp (abs lf) = .ok (abs tf) := etf
        simp [hb, hb1, etf', Except.bind, pure, Except.pure]
      · simp [hb, hb1, Except.bind, pure, Except.pure]
  · refine ⟨(h0, true), by simp [sim.step.health_apply, hf], ?_⟩
    simp [OsuModel.Sim.Sim.healthApply, abs, hf]

end OsuProofs
