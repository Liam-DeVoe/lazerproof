/-
`sim::step::{emit_one, emit}` (Rust) refine `Sim.emit` (`DrawableRuleset.NewResult` -> HealthProcessor.ApplyResult,
ScoreProcessor.ApplyResult, AccuracyChallenge, for both fail semantics; appends the judgement record).
-/
import OsuProofs.Sim.AccChallenge
import OsuProofs.Sim.ScoreApply2
import OsuProofs.Sim.Hit
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result

namespace OsuProofs

section
open OsuImpl OsuModel.Net

theorem sim.step.health_apply_props (h0 : sim.scoring.HealthSt) (hc : sim.scoring.HealthCfg) (c : sim.mods.Config)
    (j : sim.scoring.JInfo) (t : F64) (rp : Bool) (lf : Option F64)
    (hk : ∀ k, sim.mods.FailOverride.Easy k ∈ c.fail_overrides.val → k.val < h0.retries.val.length)
    (ht : h0.fail_triggers.val + 1 ≤ U64.max) (r : sim.scoring.HealthSt × Bool)
    (hr : sim.step.health_apply h0 hc c j t rp lf = ok r) :
    r.1.retries.val.length = h0.retries.val.length ∧ r.1.fail_triggers.val ≤ h0.fail_triggers.val + 1 := by
  cases hf : h0.has_failed
  · obtain ⟨cr, inc, hif, eif⟩ := sim.scoring.increase_for_refines h0 hc j false
    rcases h0 with ⟨hh, hfl, crr, ni, ft, fld, fti, rts⟩
    simp only at hf; subst hf
    let h1 : sim.scoring.HealthSt := ⟨OsuModel.Sim.clamp01 (hh + inc), false, cr, ni, ft, fld, fti, rts⟩
    unfold sim.step.health_apply at hr
    simp only [hif, sim_health_clone, float.F64.add, sim_clamp01_eq, bind_ok, Bool.false_eq_true, ite_false,
      sim_default_fail_condition_eq, sim_any_fail_condition_eq, uncurry_apply_pair] at hr
    rw [show (⟨OsuModel.Sim.clamp01 (hh + inc), false, cr, ni, ft, fld, fti, rts⟩ : sim.scoring.HealthSt) = h1
      from rfl] at hr
    split at hr
    · obtain ⟨tf, htf, -⟩ := sim.step.trigger_failure_refines c h1 t rp lf hk ht
      obtain ⟨p1, p2⟩ := sim.step.trigger_failure_props c h1 t rp lf hk ht tf htf
      rw [htf] at hr; simp at hr; subst hr; exact ⟨p1, p2⟩
    · split at hr
      · obtain ⟨tf, htf, -⟩ := sim.step.trigger_failure_refines c h1 t rp lf hk ht
        obtain ⟨p1, p2⟩ := sim.step.trigger_failure_props c h1 t rp lf hk ht tf htf
        rw [htf] at hr; simp at hr; subst hr; exact ⟨p1, p2⟩
      · simp at hr; subst hr; simp [h1]
  · simp [sim.step.health_apply, hf] at hr; subst hr; simp

end
section
open OsuImpl OsuModel.Net

/-- Guards of one `emit_one`: EZ lives in range, fail-trigger and score counters below `U64.max`. -/
def simEmitOk (c : sim.state.Ctx) (hs : sim.scoring.HealthSt) (ss : sim.scoring.ScoreSt) : Prop :=
  (∀ k, sim.mods.FailOverride.Easy k ∈ c.cfg.fail_overrides.val → k.val < hs.retries.val.length) ∧
  hs.fail_triggers.val + 1 + 2 * c.cfg.acc_challenges.val.length ≤ U64.max ∧
  ss.judged_hits.val + 1 ≤ U64.max ∧ (∀ k, k < 18 → (ss.stats.val.getD k 0#u64).val + 1 ≤ U64.max) ∧
  ss.combo.val + 1 ≤ U64.max ∧ ss.current_accuracy_judgement_count.val + 1 ≤ U64.max

/-- `emit_one` = the local `one` of `Sim.emit` (health, score, AC for one fail semantics). -/
theorem sim.step.emit_one_refines (c : sim.state.Ctx) (j : sim.scoring.JInfo) (t : F64) (hs : sim.scoring.HealthSt)
    (ss : sim.scoring.ScoreSt) (rp : Bool) (hok : simEmitOk c hs ss) :
    ∃ r, sim.step.emit_one c j t hs ss rp = ok r ∧
      ((do
        let (h1, fl) ← OsuModel.Sim.Sim.healthApply (abs hs) (abs c.hcfg) (abs c.cfg) (abs j) t rp (abs c.last_frame_time)
        let (ss', combo) := (abs ss : OsuModel.Sim.ScoreSt).apply (abs c.smax) (abs j) fl false
        let h2 ← OsuModel.Sim.Sim.accChallenge (abs c.cfg) h1 (abs ss) ss' t rp (abs c.last_frame_time)
        return (h2, ss', fl, combo)) : Except String _) = .ok (abs r.1, abs r.2.1, r.2.2.1, r.2.2.2.val) := by
  obtain ⟨hk, ht, h3, h4, h5, h6⟩ := hok
  obtain ⟨⟨h1, fl⟩, e1, s1⟩ := sim.step.health_apply_refines hs c.hcfg c.cfg j t rp c.last_frame_time hk (by omega)
  obtain ⟨p1, p2⟩ := sim.step.health_apply_props hs c.hcfg c.cfg j t rp c.last_frame_time hk (by omega) _ e1
  simp only at p1 p2
  obtain ⟨⟨ss2, combo⟩, e2, s2⟩ := sim.scoring.score_apply_refines ss c.smax j fl false h3 h4 h5 h6
  obtain ⟨h2, e3, s3⟩ := sim.step.acc_challenge_refines c.cfg h1 ss ss2 t rp c.last_frame_time
    (by rw [p1]; exact hk) (by omega)
  refine ⟨(h2, ss2, fl, combo), by simp [sim.step.emit_one, e1, e2, e3], ?_⟩
  simp only at s1 s2 s3
  rw [show OsuModel.Sim.Sim.healthApply (abs hs) (abs c.hcfg) (abs c.cfg) (abs j) t rp (abs c.last_frame_time) =
    .ok (abs h1, fl) from s1]
  simp only [Except.bind, Bind.bind, pure, Except.pure]
  rw [s2]; simp only
  rw [s3]

end
section
open OsuImpl OsuModel.Net

@[simp] theorem sim_abs_opt_id {α} (x : Option α) : (abs x : Option α) = x := by cases x <;> rfl

theorem simM_readerT_pure {α} (a : α) (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) :
    (ReaderT.pure a : OsuModel.Sim.SimM α) C S = .ok (a, S) := rfl

theorem sim.step.emit_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (r : sim.step.Ref)
    (ty : sim.basic.HitResult) (t : F64) (hr : simRefOk c r)
    (hl : simEmitOk c s.health s.score) (hrp : simEmitOk c s.health_rp s.score_rp)
    (hout : s.out.val.length < Usize.max) :
    ∃ s', sim.step.emit c s r ty t = ok s' ∧
      OsuModel.Sim.Sim.emit (abs r) (abs ty) t (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') := by
  obtain ⟨hh, eh⟩ := sim_hobj_of_eq tn fo c r hr
  set h := simHobj c r with hhdef
  let j : sim.scoring.JInfo := ⟨h.kind, h.max_result, h.min_result, ty,
    F64.min t (h.end_time + h.max_judgement_offset), h.end_time,
    F64.min (t - h.end_time) h.max_judgement_offset, h.new_combo, h.last_in_combo⟩
  -- live semantics
  obtain ⟨hk, ht, h3, h4, h5, h6⟩ := hl
  obtain ⟨⟨hl1, fl⟩, e1, s1⟩ := sim.step.health_apply_refines s.health c.hcfg c.cfg j t false c.last_frame_time hk (by omega)
  obtain ⟨p1, p2⟩ := sim.step.health_apply_props s.health c.hcfg c.cfg j t false c.last_frame_time hk (by omega) _ e1
  simp only at p1 p2
  obtain ⟨⟨sl, combo⟩, e2, s2⟩ := sim.scoring.score_apply_refines s.score c.smax j fl false h3 h4 h5 h6
  obtain ⟨hl2, e3, s3⟩ := sim.step.acc_challenge_refines c.cfg hl1 s.score sl t false c.last_frame_time
    (by rw [p1]; exact hk) (by omega)
  -- ReplayPlayer semantics
  obtain ⟨hk', ht', h3', h4', h5', h6'⟩ := hrp
  obtain ⟨⟨hr1, fr⟩, e1', s1'⟩ := sim.step.health_apply_refines s.health_rp c.hcfg c.cfg j t true c.last_frame_time hk' (by omega)
  obtain ⟨p1', p2'⟩ := sim.step.health_apply_props s.health_rp c.hcfg c.cfg j t true c.last_frame_time hk' (by omega) _ e1'
  simp only at p1' p2'
  obtain ⟨⟨sr, comboR⟩, e2', s2'⟩ := sim.scoring.score_apply_refines s.score_rp c.smax j fr false h3' h4' h5' h6'
  obtain ⟨hr2, e3', s3'⟩ := sim.step.acc_challenge_refines c.cfg hr1 s.score_rp sr t true c.last_frame_time
    (by rw [p1']; exact hk') (by omega)
  let rec' : sim.state.JRec := ⟨r.top, r.nested, h.kind, h.type_id, ty, t, combo, hl2.health, fl, comboR, hr2.health, fr⟩
  refine ⟨{ s with score := sl, health := hl2, score_rp := sr, health_rp := hr2, out := vpush s.out rec' hout }, ?_, ?_⟩
  · simp only [j] at e1 e2 e3 e1' e2' e3'
    simp [sim.step.emit, hh, net.min_refines, sim.step.emit_one, e1, e2, e3, e1', e2', e3', vec_push_ok s.out _ hout, rec']
  · simp only [sim_abs_opt_id, abs_id] at s1 s3 s1' s3'
    unfold OsuModel.Sim.Sim.emit
    simp only [simM_bind, eh, OsuModel.Sim.Sim.ctx, simM_read, OsuModel.Sim.Sim.st, simM_get, Except.bind]
    erw [s1]
    simp only [Bind.bind, Except.bind]
    erw [s2]
    simp only
    erw [s3]
    simp only [OsuModel.Sim.Sim.liftExcept, pure, Except.pure, simM_pure, simM_bind, Except.bind, simM_readerT_pure]
    erw [s1']
    simp only [Bind.bind, Except.bind]
    erw [s2']
    simp only
    erw [s3']
    simp only [OsuModel.Sim.Sim.liftExcept, pure, Except.pure, simM_pure, simM_set, Except.bind, simM_readerT_pure]
    simp [simStS, rec', jrecS, hobjS]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end

end OsuProofs
