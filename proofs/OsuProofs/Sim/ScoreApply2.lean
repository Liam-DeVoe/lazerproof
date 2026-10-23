/-
`sim::scoring::score_apply` (Rust) refines `ScoreSt.apply` (`JudgementProcessor.ApplyResult` + ScoreProcessor).
-/
import OsuProofs.Sim.ScoreApply
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

theorem sim_hr_index_spec (r : sim.basic.HitResult) : ∃ i, sim.basic.hr_index r = ok i ∧ i.val < 18 ∧
    OsuModel.Sim.HitResult.toNat (hrS r) = (if i.val = 17 then 99 else i.val) := by
  cases r <;> simp [sim.basic.hr_index, hrS, OsuModel.Sim.HitResult.toNat]

theorem sim_statsS_set (a : Std.Array U64 18#usize) (i : Usize) (hi : i.val < 18) (x : U64) :
    statsS (Std.Array.set a i x) = (statsS a).modify (if i.val = 17 then 99 else i.val) (fun _ => x.val) := by
  apply Array.ext
  · simp [statsS]
  · intro n h1 h2
    have hl : a.val.length = 18 := by simp
    simp only [statsS, Array.getElem_ofFn, Array.getElem_modify, Std.Array.set_val_eq]
    by_cases e99 : n = 99
    · subst e99; split_ifs <;> simp_all [List.getD_eq_getElem?_getD, List.getElem?_set] <;> omega
    · by_cases e17 : n < 17
      · split_ifs <;> simp_all [List.getD_eq_getElem?_getD, List.getElem?_set] <;> omega
      · split_ifs <;> simp_all <;> omega

theorem sim_hr_pred_eq {f : sim.basic.HitResult → Result Bool} {g : OsuModel.Sim.HitResult → Bool}
    (h : ∀ r, ∃ b, f r = ok b ∧ g (abs r) = abs b) (r : sim.basic.HitResult) : f r = ok (g (hrS r)) := by
  obtain ⟨b, hb, e⟩ := h r; rw [hb]; exact congrArg ok e.symm
theorem sim_base_score_eq (r : sim.basic.HitResult) : ∃ n, sim.scoring.base_score r = ok n ∧
    n.val = OsuModel.Sim.baseScore (hrS r) := by
  obtain ⟨n, hn, e⟩ := sim.scoring.base_score_refines r; exact ⟨n, hn, e.symm⟩

theorem sim_statsS_incr (a : Std.Array U64 18#usize) (i : Usize) (hi : i.val < 18) (x : U64)
    (hx : x.val = (a.val.getD i.val 0#u64).val + 1) :
    statsS (Std.Array.set a i x) = (statsS a).modify (if i.val = 17 then 99 else i.val) (· + 1) := by
  apply Array.ext
  · simp [statsS]
  · intro k h1 h2
    have hl : a.val.length = 18 := by simp
    have hk : k < 100 := by simpa [statsS] using h1
    simp only [statsS, Array.getElem_ofFn, Array.getElem_modify, Std.Array.set_val_eq]
    by_cases h17 : i.val = 17 <;> by_cases hk99 : k = 99 <;> by_cases hk17 : k < 17 <;>
      by_cases hki : i.val = k <;>
      simp_all [List.getD_eq_getElem?_getD, List.getElem?_set] <;> omega

theorem sim_max_ite (a b : U64) : (a.val).max b.val = (if a < b then b else a).val := by
  split_ifs with h
  · have : a.val < b.val := h
    simp [Nat.max_def]; omega
  · have : ¬ a.val < b.val := h
    simp [Nat.max_def]; omega

/-- `update_score` as a function (for `simp`): its value and the spec relation. -/
noncomputable def simUpdI (s : sim.scoring.ScoreSt) (m : sim.scoring.ScoreMax) : sim.scoring.ScoreSt :=
  Classical.choose (sim.scoring.update_score_refines s m)
theorem sim_update_score_eq (s : sim.scoring.ScoreSt) (m : sim.scoring.ScoreMax) :
    sim.scoring.update_score s m = ok (simUpdI s m) := (Classical.choose_spec (sim.scoring.update_score_refines s m)).1
theorem sim_updI_abs (s : sim.scoring.ScoreSt) (m : sim.scoring.ScoreMax) :
    abs (simUpdI s m) = OsuModel.Sim.ScoreSt.updateScore (abs s) (abs m) :=
  (Classical.choose_spec (sim.scoring.update_score_refines s m)).2.symm

/-- Guarded: the counters below `U64.max` (a replay has far fewer judgements). -/
theorem sim.scoring.score_apply_refines (s : sim.scoring.ScoreSt) (m : sim.scoring.ScoreMax) (j : sim.scoring.JInfo)
    (fl simu : Bool) (hj : s.judged_hits.val + 1 ≤ U64.max)
    (hst : ∀ k, k < 18 → (s.stats.val.getD k 0#u64).val + 1 ≤ U64.max) (hc : s.combo.val + 1 ≤ U64.max)
    (hn : s.current_accuracy_judgement_count.val + 1 ≤ U64.max) :
    ∃ r, sim.scoring.score_apply s m j fl simu = ok r ∧
      OsuModel.Sim.ScoreSt.apply (abs s) (abs m) (abs j) fl simu = (abs r.1, r.2.val) := by
  obtain ⟨jh, hjh, ejh⟩ := eq_ok_of_spec (U64.add_spec (x := s.judged_hits) (y := 1#u64) (by simpa using hj))
  cases fl
  · obtain ⟨i, hi, hil, hin⟩ := sim_hr_index_spec j.ty
    have hl : s.stats.val.length = 18 := by simp
    have hidx : Std.Array.index_usize s.stats i = ok (s.stats.val[i.val]'(by omega)) := by
      simp [Std.Array.index_usize, hl, hil]
    have hb1 : (s.stats.val[i.val]'(by omega)).val + 1 ≤ U64.max := by
      have := hst i.val hil; simpa [List.getD_eq_getElem?_getD, hl, hil] using this
    obtain ⟨st1, hst1, est1⟩ := eq_ok_of_spec (U64.add_spec (x := s.stats.val[i.val]'(by omega)) (y := 1#u64) hb1)
    obtain ⟨c1, hc1, ec1⟩ := eq_ok_of_spec (U64.add_spec (x := s.combo) (y := 1#u64) (by simpa using hc))
    obtain ⟨n1, hn1, en1⟩ := eq_ok_of_spec (U64.add_spec (x := s.current_accuracy_judgement_count) (y := 1#u64)
      (by simpa using hn))
    obtain ⟨bm, hbm, ebm⟩ := sim_base_score_eq j.max_result
    obtain ⟨bt, hbt, ebt⟩ := sim_base_score_eq j.ty
    unfold sim.scoring.score_apply
    simp only [hjh, hi, hidx, hst1, Std.Array.index_mut_usize, bind_ok, hc1, hn1, hbm, hbt,
      sim_hr_pred_eq sim.basic.increases_combo_refines, sim_hr_pred_eq sim.basic.breaks_combo_refines,
      sim_hr_pred_eq sim.basic.affects_accuracy_refines, sim_hr_pred_eq sim.basic.is_bonus_refines,
      sim_hr_pred_eq sim.basic.is_scorable_refines, sim_scoring_F64_0_5, float.F64.from_u64, float.F64.add,
      float.F64.mul, float.F64.pow, sim_ite_ok, sim_update_score_eq, uncurry_apply_pair, Bool.false_eq_true,
      ite_false]
    simp only [bind_tc_ok, bind_ok, uncurry_apply_pair]
    unfold OsuModel.Sim.ScoreSt.apply
    have hst' : (abs s : OsuModel.Sim.ScoreSt).stats.modify (hrS j.ty).toNat (· + 1) = statsS (Std.Array.set s.stats i st1) := by
      rw [sim_statsS_incr _ _ hil st1 (by rw [est1]; simp [List.getD_eq_getElem?_getD, hl, hil]), ← hin]; rfl
    cases hA : (hrS j.max_result).affectsAccuracy <;> cases hB : (hrS j.ty).isBonus <;>
      cases hS : (hrS j.ty).isScorable <;> cases hI : (hrS j.ty).increasesCombo <;>
      cases hK : (hrS j.ty).breaksCombo <;> cases hT : (hrS j.ty).affectsAccuracy <;> cases simu <;>
      simp only [hA, hB, hS, hI, hK, hT, Bool.false_eq_true, ite_true, ite_false] <;>
      refine ⟨_, rfl, ?_⟩ <;>
      (try simp only [sim_updI_abs]) <;>
      (try simp only [hA, hB, hS, hI, hK, hT, Bool.false_eq_true, ite_true, ite_false]) <;>
      rw [Prod.mk.injEq] <;> refine ⟨?_, by simp [abs, scoreS, hI, hK, ec1]⟩ <;>
      first
        | (refine congrArg (OsuModel.Sim.ScoreSt.updateScore · (abs m)) ?_
           simp [abs, scoreS, hA, hB, hS, hI, hK, hT, ec1, en1, ebm, ebt, est1, ejh, sim_max_ite, ← hst'])
        | simp [abs, scoreS, hA, hB, hS, hI, hK, hT, ec1, en1, ebm, ebt, est1, ejh, sim_max_ite, ← hst']
    all_goals (split_ifs <;> simp_all [Nat.max_def] <;> omega)
  · refine ⟨({ s with judged_hits := jh, last_time_absolute := some j.time_absolute }, 0#u64),
      by simp [sim.scoring.score_apply, hjh], ?_⟩
    simp [OsuModel.Sim.ScoreSt.apply, abs, scoreS, ejh]

end OsuProofs
