/-
Sim3b part 3: mod update hooks of `playfieldUpdate` (InputBlocking, BarrelRoll, ...) and the break periods of
`inputBlockPeriods` (`block_vt`, `block_period`, `first_object_after`, `break_block_period`).
The local `let`s of `Sim.inputBlockPeriods` (`vt`, `period`, the per-break body) are stated against named copies
`s3b_vtS`, `s3b_periodS`, `s3b_breakPeriodS` (same text, D26 style).
-/
import OsuProofs.Sim3.SB_Dyn
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

/-- `vt` of `inputBlockPeriods` -/
def s3b_vtS (h : OsuModel.Sim.HObj) : F64 := h.start - (match h.hitWindows with | some hw => hw.meh | none => 0)
/-- `period` of `inputBlockPeriods` -/
def s3b_periodS (a b : F64) : Except String (F64 × F64) :=
  if a < b then pure (a, b) else throw "InputBlockingMod: invalid period (start >= end), lazer throws"
/-- the body of `inputBlockPeriods`' break loop for the break `(bs, be)` -/
def s3b_breakPeriodS (pb : OsuModel.Sim.Playable) (bs be : F64) : Except String (F64 × F64) :=
  match pb.objects.find? (fun o => be ≤ o.h.start) with
  | some o => s3b_periodS bs (s3b_vtS o.h - 1)
  | none => throw "InputBlockingMod: break without a following object, lazer throws"

/-- Rust `Result<T, SimErr>` vs spec `Except String` (both ok and related, or both reject) -/
def s3b_erel {α β : Type} (f : α → β) : core.result.Result α sim.err.SimErr → Except String β → Prop
  | .Ok a, .ok b => f a = b
  | .Err _, .error _ => True
  | _, _ => False

theorem sim.step.block_vt_refines (tn) (h : sim.playable.HObj) :
    sim.step.block_vt h = ok (s3b_vtS (hobjS tn h)) := by
  unfold sim.step.block_vt s3b_vtS
  cases hw : h.hit_windows <;> simp [hw, hobjS, float.F64.sub, sim.step.F64_0] <;> rfl

theorem sim.step.block_period_refines (a b : F64) :
    ∃ r, sim.step.block_period a b = ok r ∧ s3b_erel (fun p => (abs p : F64 × F64)) r (s3b_periodS a b) := by
  unfold sim.step.block_period s3b_periodS
  by_cases h : a < b
  · exact ⟨.Ok ⟨a, b⟩, by simp [float.F64.lt, h], by simp [h, s3b_erel, abs, pure, Except.pure]⟩
  · exact ⟨.Err .PeriodInvalid, by simp [float.F64.lt, h], by simp [h, s3b_erel, throw, throwThe, MonadExceptOf.throw]⟩

theorem sim.step.first_object_after_refines (pb : sim.playable.Playable) (be : F64) :
    ∃ r : Option Usize, sim.step.first_object_after pb be = ok r ∧
      r.map (·.val) = pb.objects.val.findIdx? (fun o => decide (be ≤ o.h.start)) := by
  have hmax := pb.objects.property
  obtain ⟨y, hl, hy⟩ := loop_iterR (fun x => sim.step.first_object_after_loop.body pb be x.1 x.2)
    (fun j acc => if decide (be ≤ (pb.objects.val[j]!).h.start) then .done (some j) else .yield acc)
    pb.objects.val.length (fun x => x.1.val) (fun x acc => x.2 = none ∧ acc = none)
    (fun y acc => y.map (·.val) = acc)
    (by
      rintro ⟨i, r⟩ acc ⟨hr, hacc⟩ hi
      simp only at hr hacc hi ⊢
      subst hr; subst hacc
      have hil : i < alloc.vec.Vec.len pb.objects := by rw [vec_lt_len_iff]; exact hi
      obtain ⟨i2, hi2, hi2v⟩ := usize_add_one i (by omega)
      have hget : pb.objects.val[i.val]! = pb.objects.val[i.val]'hi := getElem!_pos pb.objects.val i.val hi
      constructor
      · intro s' hf
        rw [hget] at hf
        by_cases hc : be ≤ (pb.objects.val[i.val]'hi).h.start
        · simp [hc] at hf
        · simp [hc] at hf
          refine ⟨(i2, none), ?_, hi2v, rfl, hf.symm⟩
          simp [sim.step.first_object_after_loop.body, hil, core.option.Option.is_none, vec_index_eq _ _ hi,
            float.F64.le, hc, hi2]
      · intro s' hf
        rw [hget] at hf
        by_cases hc : be ≤ (pb.objects.val[i.val]'hi).h.start
        · simp [hc] at hf
          subst hf
          refine ⟨some i, Or.inr ⟨(i2, some i), ?_, ?_⟩, rfl⟩
          · simp [sim.step.first_object_after_loop.body, hil, core.option.Option.is_none, vec_index_eq _ _ hi,
              float.F64.le, hc, hi2]
          · by_cases hi2l : i2 < alloc.vec.Vec.len pb.objects
            · simp [sim.step.first_object_after_loop.body, hi2l, core.option.Option.is_none]
            · simp [sim.step.first_object_after_loop.body, hi2l]
        · simp [hc] at hf)
    (by
      rintro ⟨i, r⟩ acc ⟨hr, hacc⟩ hge
      simp only at hr hacc hge
      subst hr; subst hacc
      have : ¬ i < alloc.vec.Vec.len pb.objects := by rw [vec_lt_len_iff]; omega
      exact ⟨none, by simp [sim.step.first_object_after_loop.body, this], rfl⟩)
    (0#usize, none) none ⟨rfl, rfl⟩ (by simp)
  refine ⟨y, by unfold sim.step.first_object_after sim.step.first_object_after_loop; exact hl, ?_⟩
  rw [hy, findIdx_iterR]; rfl

/-- `ModBarrelRoll.Update` (the `.barrelRoll` arm of `Sim.playfieldUpdate`) -/
theorem sim.step.barrel_roll_update_refines (c : sim.state.Ctx) (s : sim.state.St) :
    sim.step.barrel_roll_update c s = ok (match c.cfg.barrel_roll with
      | none => s
      | some (speed, ccw) =>
        { s with br_rot := F32.ofInt ((if ccw then -1 else 1) * 360) * F64.toF32 (s.t / 60000 * speed) }) := by
  unfold sim.step.barrel_roll_update
  rcases c.cfg.barrel_roll with _ | ⟨speed, ccw⟩
  · rfl
  · have m1 : (1#i64 * 360#i64 : Result I64) = ok 360#i64 := by
      first | rfl | decide | (simp [HMul.hMul, Mul.mul, IScalar.mul]) | scalar_tac
    have m2 : ((-1)#i64 * 360#i64 : Result I64) = ok (-360)#i64 := by
      first | rfl | decide | (simp [HMul.hMul, Mul.mul, IScalar.mul]) | scalar_tac
    cases ccw <;> simp [float.F32.from_i64, float.F64.div, float.F64.mul, float.F64.to_f32, float.F32.mul,
      fb64_4678479150791524352, m1, m2]

end OsuProofs
