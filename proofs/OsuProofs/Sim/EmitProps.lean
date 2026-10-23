/-
Postconditions of `sim::step::{acc_challenge, emit_one, emit}` (counter growth bounds, retries length, out length +1)
used by the well-formedness invariant of the `apply_result` / `handle_hit` fuel induction.
-/
import OsuProofs.Sim.Emit
import OsuProofs.Sim.Maxima
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

open Aeneas Aeneas.Std Result
namespace OsuProofs
open OsuImpl OsuModel.Net

theorem sim.step.acc_challenge_props (c : sim.mods.Config) (h : sim.scoring.HealthSt) (old new : sim.scoring.ScoreSt)
    (t : F64) (rp : Bool) (lf : Option F64)
    (hk : ∀ e, sim.mods.FailOverride.Easy e ∈ c.fail_overrides.val → e.val < h.retries.val.length)
    (ht : h.fail_triggers.val + 2 * c.acc_challenges.val.length ≤ U64.max) (r : sim.scoring.HealthSt)
    (hr : sim.step.acc_challenge c h old new t rp lf = ok r) :
    r.retries.val.length = h.retries.val.length ∧
      r.fail_triggers.val ≤ h.fail_triggers.val + 2 * c.acc_challenges.val.length := by
  obtain ⟨h1, e1, s1, l1, t1⟩ := sim_acc_pass c t rp lf true new.accuracy h hk (by omega)
  obtain ⟨h2, e2, s2, l2, t2⟩ := sim_acc_pass c t rp lf false new.maximum_accuracy
    (if Framework.Bindable.equalsD old.accuracy new.accuracy then h else h1)
    (by split <;> [exact hk; (rw [l1]; exact hk)]) (by split <;> omega)
  set hm := (if Framework.Bindable.equalsD old.accuracy new.accuracy then h else h1) with hhm
  have hres : sim.step.acc_challenge c h old new t rp lf =
      ok (if Framework.Bindable.equalsD old.maximum_accuracy new.maximum_accuracy then hm else h2) := by
    unfold sim.step.acc_challenge sim.step.acc_challenge_loop0
    rw [loop_unfold]
    have p0 : sim.step.acc_challenge_loop0.body old new t rp lf c h 0#usize = ok (.cont (c, hm, 1#usize)) := by
      cases he : Framework.Bindable.equalsD old.accuracy new.accuracy <;>
        simp [sim.step.acc_challenge_loop0.body, sim.netx.equals_d_refines, he, hhm, e1, simCfgT, sim_a01]
    simp only [p0, bind_ok]
    rw [loop_unfold]
    have p1 : sim.step.acc_challenge_loop0.body old new t rp lf c hm 1#usize =
        ok (.cont (c, (if Framework.Bindable.equalsD old.maximum_accuracy new.maximum_accuracy then hm else h2), 2#usize)) := by
      cases he : Framework.Bindable.equalsD old.maximum_accuracy new.maximum_accuracy <;>
        simp [sim.step.acc_challenge_loop0.body, sim.netx.equals_d_refines, he, e2, simCfgT, sim_a12]
    simp only [p1, bind_ok]
    rw [loop_unfold]
    simp [sim.step.acc_challenge_loop0.body]
  rw [hres] at hr
  cases Result.ok_injective hr
  have hmr : hm.retries.val.length = h.retries.val.length ∧ hm.fail_triggers.val ≤ h.fail_triggers.val + c.acc_challenges.val.length := by
    simp only [hhm]; split <;> [exact ⟨rfl, by omega⟩; exact ⟨l1, t1⟩]
  split
  · exact ⟨hmr.1, by omega⟩
  · exact ⟨by rw [l2, hmr.1], by omega⟩
end OsuProofs

open Aeneas Aeneas.Std Result
namespace OsuProofs
open OsuImpl OsuModel.Net

theorem sim_apply_counters (s : OsuModel.Sim.ScoreSt) (m : OsuModel.Sim.ScoreMax) (j : OsuModel.Sim.JInfo) (fl sm : Bool) :
    (s.apply m j fl sm).1.judgedHits = s.judgedHits + 1 ∧ (s.apply m j fl sm).1.combo ≤ s.combo + 1 ∧
      (s.apply m j fl sm).1.currentAccuracyJudgementCount ≤ s.currentAccuracyJudgementCount + 1 ∧
      (s.apply m j fl sm).1.stats.size = s.stats.size ∧
      ∀ i (h : i < s.stats.size) (h' : i < (s.apply m j fl sm).1.stats.size),
        (s.apply m j fl sm).1.stats[i] ≤ s.stats[i] + 1 := by
  have u1 : ∀ (x : OsuModel.Sim.ScoreSt), (x.updateScore m).judgedHits = x.judgedHits := fun _ => rfl
  have u2 : ∀ (x : OsuModel.Sim.ScoreSt), (x.updateScore m).combo = x.combo := fun _ => rfl
  have u3 : ∀ (x : OsuModel.Sim.ScoreSt), (x.updateScore m).currentAccuracyJudgementCount = x.currentAccuracyJudgementCount :=
    fun _ => rfl
  have u4 : ∀ (x : OsuModel.Sim.ScoreSt), (x.updateScore m).stats = x.stats := fun _ => rfl
  have hst : (s.apply m j fl sm).1.stats = if fl then s.stats else s.stats.modify j.ty.toNat (· + 1) := by
    unfold OsuModel.Sim.ScoreSt.apply
    cases fl
    · dsimp only
      simp only [Bool.false_eq_true, if_false, apply_ite OsuModel.Sim.ScoreSt.stats, u4, ite_self]
    · rfl
  have hj : (s.apply m j fl sm).1.judgedHits = s.judgedHits + 1 := by
    unfold OsuModel.Sim.ScoreSt.apply
    cases fl
    · dsimp only
      simp only [Bool.false_eq_true, if_false, apply_ite OsuModel.Sim.ScoreSt.judgedHits, u1, ite_self]
    · rfl
  have hc : (s.apply m j fl sm).1.combo ≤ s.combo + 1 := by
    unfold OsuModel.Sim.ScoreSt.apply
    cases fl
    · dsimp only
      simp only [Bool.false_eq_true, if_false, apply_ite OsuModel.Sim.ScoreSt.combo, u2, ite_self]
      split_ifs <;> omega
    · exact Nat.le_succ _
  have ha : (s.apply m j fl sm).1.currentAccuracyJudgementCount ≤ s.currentAccuracyJudgementCount + 1 := by
    unfold OsuModel.Sim.ScoreSt.apply
    cases fl
    · dsimp only
      simp only [Bool.false_eq_true, if_false, apply_ite OsuModel.Sim.ScoreSt.currentAccuracyJudgementCount, u3, ite_self]
      split_ifs <;> omega
    · exact Nat.le_succ _
  refine ⟨hj, hc, ha, ?_, ?_⟩
  · rw [hst]; split <;> simp
  · intro i h h'
    simp only [hst]
    split
    · exact Nat.le_succ _
    · rw [Array.getElem_modify]; split <;> omega
end OsuProofs

open Aeneas Aeneas.Std Result
namespace OsuProofs
open OsuImpl OsuModel.Net

/-- the score counters grow by at most one per `emit_one` -/
def simScoreStep (a b : sim.scoring.ScoreSt) : Prop :=
  b.judged_hits.val = a.judged_hits.val + 1 ∧ b.combo.val ≤ a.combo.val + 1 ∧
    b.current_accuracy_judgement_count.val ≤ a.current_accuracy_judgement_count.val + 1 ∧
    ∀ k, k < 18 → (b.stats.val.getD k 0#u64).val ≤ (a.stats.val.getD k 0#u64).val + 1

theorem sim_score_step_of (ss ss2 : sim.scoring.ScoreSt) (m : OsuModel.Sim.ScoreMax) (j : OsuModel.Sim.JInfo) (fl : Bool)
    (h : (abs ss2 : OsuModel.Sim.ScoreSt) = ((abs ss : OsuModel.Sim.ScoreSt).apply m j fl false).1) :
    simScoreStep ss ss2 := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := sim_apply_counters (abs ss) m j fl false
  rw [← h] at c1 c2 c3 c4 c5
  refine ⟨c1, c2, c3, ?_⟩
  intro k hk
  rw [sim_statsS_get _ k hk, sim_statsS_get _ k hk]
  have hsz : ∀ x : Std.Array U64 18#usize, (statsS x).size = 100 := by intro x; simp [statsS]
  have hk' : (if k = 17 then 99 else k) < 100 := by split <;> omega
  rw [getElem!_pos (statsS ss2.stats) _ (by rw [hsz]; exact hk'), getElem!_pos (statsS ss.stats) _ (by rw [hsz]; exact hk')]
  exact c5 _ (by show _ < (statsS ss.stats).size; rw [hsz]; exact hk') (by show _ < (statsS ss2.stats).size; rw [hsz]; exact hk')

theorem sim.step.emit_one_props (c : sim.state.Ctx) (j : sim.scoring.JInfo) (t : F64) (hs : sim.scoring.HealthSt)
    (ss : sim.scoring.ScoreSt) (rp : Bool) (hok : simEmitOk c hs ss) (r : sim.scoring.HealthSt × sim.scoring.ScoreSt × Bool × U64)
    (hr : sim.step.emit_one c j t hs ss rp = ok r) :
    r.1.retries.val.length = hs.retries.val.length ∧
      r.1.fail_triggers.val ≤ hs.fail_triggers.val + 1 + 2 * c.cfg.acc_challenges.val.length ∧
      simScoreStep ss r.2.1 := by
  obtain ⟨hk, ht, h3, h4, h5, h6⟩ := hok
  obtain ⟨⟨h1, fl⟩, e1, s1⟩ := sim.step.health_apply_refines hs c.hcfg c.cfg j t rp c.last_frame_time hk (by omega)
  obtain ⟨p1, p2⟩ := sim.step.health_apply_props hs c.hcfg c.cfg j t rp c.last_frame_time hk (by omega) _ e1
  simp only at p1 p2
  obtain ⟨⟨ss2, combo⟩, e2, s2⟩ := sim.scoring.score_apply_refines ss c.smax j fl false h3 h4 h5 h6
  obtain ⟨h2, e3, s3⟩ := sim.step.acc_challenge_refines c.cfg h1 ss ss2 t rp c.last_frame_time
    (by rw [p1]; exact hk) (by omega)
  obtain ⟨q1, q2⟩ := sim.step.acc_challenge_props c.cfg h1 ss ss2 t rp c.last_frame_time (by rw [p1]; exact hk)
    (by omega) h2 e3
  have : r = (h2, ss2, fl, combo) := by
    have e : sim.step.emit_one c j t hs ss rp = ok (h2, ss2, fl, combo) := by simp [sim.step.emit_one, e1, e2, e3]
    rw [e] at hr; exact (Result.ok_injective hr).symm
  subst this
  refine ⟨by simp only; rw [q1, p1], by simp only; omega, ?_⟩
  simp only at s2
  exact sim_score_step_of ss ss2 _ _ fl (congrArg Prod.fst s2).symm
end OsuProofs
open Aeneas Aeneas.Std Result
namespace OsuProofs
open OsuImpl OsuModel.Net

/-- `emit` only changes the processors and appends one record -/
theorem sim.step.emit_props (c : sim.state.Ctx) (s : sim.state.St) (r : sim.step.Ref) (ty : sim.basic.HitResult) (t : F64)
    (hr : simRefOk c r) (hl : simEmitOk c s.health s.score) (hrp : simEmitOk c s.health_rp s.score_rp)
    (hout : s.out.val.length < Usize.max)
    (s' : sim.state.St) (he : sim.step.emit c s r ty t = ok s') :
    ∃ (hl' hr' : sim.scoring.HealthSt) (sl sr : sim.scoring.ScoreSt) (v : alloc.vec.Vec sim.state.JRec),
      s' = { s with score := sl, health := hl', score_rp := sr, health_rp := hr', out := v } ∧ v.val.length = s.out.val.length + 1 ∧
      hl'.retries.val.length = s.health.retries.val.length ∧
      hl'.fail_triggers.val ≤ s.health.fail_triggers.val + 1 + 2 * c.cfg.acc_challenges.val.length ∧
      hr'.retries.val.length = s.health_rp.retries.val.length ∧
      hr'.fail_triggers.val ≤ s.health_rp.fail_triggers.val + 1 + 2 * c.cfg.acc_challenges.val.length ∧
      simScoreStep s.score sl ∧ simScoreStep s.score_rp sr := by
  obtain ⟨hh, _⟩ := sim_hobj_of_eq (fun _ => "") (alloc.vec.Vec.new Usize) c r hr
  unfold sim.step.emit at he
  simp only [hh, bind_ok, float.F64.add, net.min_refines, float.F64.sub] at he
  generalize hj : (⟨(simHobj c r).kind, (simHobj c r).max_result, (simHobj c r).min_result, ty,
    F64.min t ((simHobj c r).end_time + (simHobj c r).max_judgement_offset), (simHobj c r).end_time,
    F64.min (t - (simHobj c r).end_time) (simHobj c r).max_judgement_offset, (simHobj c r).new_combo,
    (simHobj c r).last_in_combo⟩ : sim.scoring.JInfo) = j at he
  obtain ⟨r1, h1, e1⟩ := sim.step.emit_one_refines c j t s.health s.score false hl
  obtain ⟨r2, h2, e2⟩ := sim.step.emit_one_refines c j t s.health_rp s.score_rp true hrp
  obtain ⟨a1, a2, a3⟩ := sim.step.emit_one_props c j t s.health s.score false hl r1 h1
  obtain ⟨b1, b2, b3⟩ := sim.step.emit_one_props c j t s.health_rp s.score_rp true hrp r2 h2
  obtain ⟨x1, x2, x3, x4⟩ := r1
  obtain ⟨y1, y2, y3, y4⟩ := r2
  rw [h1, h2] at he
  simp only [bind_ok, vec_push_ok _ _ hout, ok.injEq] at he
  obtain rfl := Result.ok_injective he
  exact ⟨x1, y1, x2, y2, _, rfl, by simp, a1, a2, b1, b2, a3, b3⟩
end OsuProofs
