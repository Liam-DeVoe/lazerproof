/-
`sim::step` processor layer (Rust) refines `OsuModel.Sim.Sim` (Step.lean): lifetimes from hit-state transforms,
`timeAbsolute`, fail conditions, `triggerFailure`, `healthApply`, `accChallenge`.
-/
import OsuProofs.Sim.Health
import OsuProofs.LoopsR
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

@[simp] theorem sim_step_F64_0 : sim.step.F64_0 = ok (0 : F64) := by simp [sim.step.F64_0]
@[simp] theorem sim_step_F64_1 : sim.step.F64_1 = ok (1 : F64) := by simp [sim.step.F64_1]
@[simp] theorem sim_step_F64_100 : sim.step.F64_100 = ok (100 : F64) := by simp [sim.step.F64_100]
@[simp] theorem sim_step_F64_800 : sim.step.F64_800 = ok (800 : F64) := by simp [sim.step.F64_800]
@[simp] theorem sim_step_F64_240 : sim.step.F64_240 = ok (240 : F64) := by simp [sim.step.F64_240]

/-- `latestTransformEndTime s [e]` (every use has one transform). -/
theorem sim.step.latest_transform_end_time_refines (s e : F64) :
    ∃ r, sim.step.latest_transform_end_time s e = ok r ∧
      OsuModel.Sim.Sim.latestTransformEndTime (abs s) [abs e] = abs r := by
  by_cases h : s < e <;> simp [sim.step.latest_transform_end_time, OsuModel.Sim.Sim.latestTransformEndTime, abs, h]

theorem sim.step.seq_start_refines (ct t : F64) :
    ∃ r, sim.step.seq_start ct t = ok r ∧ OsuModel.Sim.Sim.seqStart (abs ct) (abs t) = abs r := by
  simp [sim.step.seq_start, OsuModel.Sim.Sim.seqStart, abs]

theorem sim.step.circle_lifetime_end_refines (ct t : F64) (st : Option Bool) :
    ∃ r, sim.step.circle_lifetime_end ct t st = ok r ∧
      OsuModel.Sim.Sim.circleLifetimeEnd (abs ct) (abs t) (abs st) = abs r := by
  rcases st with _ | _ | _ <;>
    simp [sim.step.circle_lifetime_end, OsuModel.Sim.Sim.circleLifetimeEnd, sim.step.seq_start,
      OsuModel.Sim.Sim.seqStart, sim.step.latest_transform_end_time, OsuModel.Sim.Sim.latestTransformEndTime, abs] <;>
    try (split_ifs <;> simp)

theorem sim.step.slider_lifetime_end_refines (ct t : F64) :
    ∃ r, sim.step.slider_lifetime_end ct t = ok r ∧
      OsuModel.Sim.Sim.sliderLifetimeEnd (abs ct) (abs t) = abs r := by
  simp [sim.step.slider_lifetime_end, OsuModel.Sim.Sim.sliderLifetimeEnd, sim.step.seq_start,
    OsuModel.Sim.Sim.seqStart, sim.step.latest_transform_end_time, OsuModel.Sim.Sim.latestTransformEndTime, abs]
  try (split_ifs <;> simp)

theorem sim.step.time_absolute_refines (h : sim.playable.HObj) (raw : F64) :
    ∃ r, sim.step.time_absolute h raw = ok r ∧ OsuModel.Sim.Sim.timeAbsolute (abs h) (abs raw) = abs r := by
  simp [sim.step.time_absolute, OsuModel.Sim.Sim.timeAbsolute, net.min_refines, abs, hobjS]

theorem sim.step.fail_condition_refines (j : sim.scoring.JInfo) (fc : sim.mods.FailCond) :
    ∃ b, sim.step.fail_condition j fc = ok b ∧ OsuModel.Sim.Sim.failCondition (abs j) (abs fc) = abs b := by
  rcases j with ⟨k, mx, mn, ty, ta, et, tof, nc, lc⟩
  cases fc with
  | SuddenDeath tl =>
    cases ty <;> cases k <;> cases tl <;>
      simp [sim.step.fail_condition, OsuModel.Sim.Sim.failCondition, abs, hrS, kindS, sim.basic.affects_combo,
        sim.basic.is_hit, OsuModel.Sim.HitResult.affectsCombo, OsuModel.Sim.HitResult.isHit] <;> rfl
  | Perfect =>
    obtain ⟨a1, h1, e1⟩ := sim.basic.affects_accuracy_refines mn
    obtain ⟨a2, h2, e2⟩ := sim.basic.affects_accuracy_refines mx
    obtain ⟨a3, h3, e3⟩ := sim.basic.affects_accuracy_refines ty
    obtain ⟨c1, g1, f1⟩ := sim.basic.affects_combo_refines mn
    obtain ⟨c2, g2, f2⟩ := sim.basic.affects_combo_refines mx
    obtain ⟨c3, g3, f3⟩ := sim.basic.affects_combo_refines ty
    simp only [abs, id] at e1 e2 e3 f1 f2 f3
    simp [sim.step.fail_condition, OsuModel.Sim.Sim.failCondition, abs, h1, h2, h3, g1, g2, g3, e1, e2, e3,
      f1, f2, f3]
    cases a1 <;> cases a2 <;> cases a3 <;> cases c1 <;> cases c2 <;> cases c3 <;> simp
  | TargetPractice =>
    cases ty <;>
      simp [sim.step.fail_condition, OsuModel.Sim.Sim.failCondition, abs, hrS, sim.basic.affects_combo,
        sim.basic.is_hit, OsuModel.Sim.HitResult.affectsCombo, OsuModel.Sim.HitResult.isHit]

theorem sim_any_map_foldl {X Y : Type} (f : X → Y) (p : Y → Bool) (l : List X) :
    ∀ acc, ((l.map f).any p || acc) = l.foldl (fun acc x => acc || p (f x)) acc := by
  induction l with
  | nil => intro acc; simp
  | cons x t ih => intro acc; simp [← ih]; cases p (f x) <;> simp

/-- `c.failConds.any (failCondition j)`. -/
theorem sim.step.any_fail_condition_refines (c : sim.mods.Config) (j : sim.scoring.JInfo) :
    ∃ b, sim.step.any_fail_condition c j = ok b ∧
      (abs c : OsuModel.Sim.Config).failConds.any (OsuModel.Sim.Sim.failCondition (abs j)) = abs b := by
  let P := fun (fc : sim.mods.FailCond) => OsuModel.Sim.Sim.failCondition (abs j) (abs fc)
  have hfc : ∀ fc, sim.step.fail_condition j fc = ok (P fc) := fun fc => by
    obtain ⟨b, h, e⟩ := sim.step.fail_condition_refines j fc; refine h.trans ?_; congr 1; exact e.symm
  obtain ⟨v, hl, hv⟩ := loop_fold_gen' (fun x => sim.step.any_fail_condition_loop.body c j x.1 x.2) (·.1)
    c.fail_conds.val.length (by have := c.fail_conds.property; omega)
    (fun _ => True) (fun x => x.2)
    (fun k acc => acc || P (c.fail_conds.val[k]!)) (fun y acc => y = acc)
    (by loop_step [sim.step.any_fail_condition_loop.body, hfc, Bool.or_comm])
    (by loop_end [sim.step.any_fail_condition_loop.body])
    (0#usize, false) trivial (by simp)
  refine ⟨v, by unfold sim.step.any_fail_condition sim.step.any_fail_condition_loop; exact hl, ?_⟩
  simp only at hv
  rw [hv, show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero]
  have := sim_any_map_foldl (fun x => (abs x : OsuModel.Sim.FailCond)) (OsuModel.Sim.Sim.failCondition (abs j))
    c.fail_conds.val false
  simp only [Bool.or_false] at this
  rw [foldl_iterR] at this
  simp only [abs, configS, List.any_toArray, id] at this ⊢
  rw [this]; rfl

end OsuProofs
