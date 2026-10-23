/-
`sim::basic`, `sim::playable` leaves (Rust) refine `OsuModel.Sim` Basic/Playable: float32 Vec2/Mat3/DrawInfo
arithmetic, `HitResult` predicates, hit windows (`resultFor`, `canBeHit`).
Statement form (as the automation, OsuProofs/Auto/Gen.lean): `∃ r, f a = ok r ∧ spec (abs a) = abs r`, plus an
`@[step]` wrapper.
-/
import OsuProofs.Sim.NetX
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

@[simp] theorem sim_basic_F32_0 : sim.basic.F32_0 = ok (0 : F32) := by
  unfold sim.basic.F32_0; simp; decide +kernel
@[simp] theorem sim_basic_F32_1 : sim.basic.F32_1 = ok (1 : F32) := by
  unfold sim.basic.F32_1; simp; decide +kernel
@[simp] theorem sim_basic_F32_2 : sim.basic.F32_2 = ok (2 : F32) := by
  unfold sim.basic.F32_2; simp; decide +kernel
@[simp] theorem sim_basic_VEC2_ZERO : sim.basic.VEC2_ZERO = ok ⟨0, 0⟩ := by
  simp [sim.basic.VEC2_ZERO]
@[simp] theorem sim_basic_VEC2_ONE : sim.basic.VEC2_ONE = ok ⟨1, 1⟩ := by
  simp [sim.basic.VEC2_ONE]
@[simp] theorem sim_basic_FLOAT_EPSILON : sim.basic.FLOAT_EPSILON = ok (Float32.ofBits 0x3A83126F) := by
  unfold sim.basic.FLOAT_EPSILON; simp
@[simp] theorem sim_basic_ALMOST_EQUALS_EPS : sim.basic.ALMOST_EQUALS_EPS = ok (Float.ofBits 0x3E7AD7F29ABCAF48) := by
  unfold sim.basic.ALMOST_EQUALS_EPS; simp
@[simp] theorem sim_basic_MAT3_IDENTITY : sim.basic.MAT3_IDENTITY = ok ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩ := by
  simp [sim.basic.MAT3_IDENTITY]

/-! ## Vec2 -/
theorem sim.basic.Vec2.add_refines (a b : sim.basic.Vec2) :
    ∃ r, sim.basic.Vec2.add a b = ok r ∧ OsuModel.Sim.Vec2.add (abs a) (abs b) = abs r := by
  simp [sim.basic.Vec2.add, OsuModel.Sim.Vec2.add, abs]
theorem sim.basic.Vec2.sub_refines (a b : sim.basic.Vec2) :
    ∃ r, sim.basic.Vec2.sub a b = ok r ∧ OsuModel.Sim.Vec2.sub (abs a) (abs b) = abs r := by
  simp [sim.basic.Vec2.sub, OsuModel.Sim.Vec2.sub, abs]
theorem sim.basic.Vec2.neg_refines (a : sim.basic.Vec2) :
    ∃ r, sim.basic.Vec2.neg a = ok r ∧ OsuModel.Sim.Vec2.neg (abs a) = abs r := by
  simp [sim.basic.Vec2.neg, OsuModel.Sim.Vec2.neg, abs]
theorem sim.basic.Vec2.scale_refines (a : sim.basic.Vec2) (s : F32) :
    ∃ r, sim.basic.Vec2.scale a s = ok r ∧ OsuModel.Sim.Vec2.scale (abs a) s = abs r := by
  simp [sim.basic.Vec2.scale, OsuModel.Sim.Vec2.scale, abs]
theorem sim.basic.Vec2.mul_refines (a b : sim.basic.Vec2) :
    ∃ r, sim.basic.Vec2.mul a b = ok r ∧ OsuModel.Sim.Vec2.mul (abs a) (abs b) = abs r := by
  simp [sim.basic.Vec2.mul, OsuModel.Sim.Vec2.mul, abs]
theorem sim.basic.Vec2.cdiv_refines (a b : sim.basic.Vec2) :
    ∃ r, sim.basic.Vec2.cdiv a b = ok r ∧ OsuModel.Sim.Vec2.cdiv (abs a) (abs b) = abs r := by
  simp [sim.basic.Vec2.cdiv, OsuModel.Sim.Vec2.cdiv, abs]
theorem sim.basic.Vec2.eq_refines (a b : sim.basic.Vec2) :
    ∃ r, sim.basic.Vec2.eq a b = ok r ∧ OsuModel.Sim.Vec2.eq (abs a) (abs b) = abs r := by
  by_cases h : a.x == b.x <;> simp [sim.basic.Vec2.eq, OsuModel.Sim.Vec2.eq, abs, h]
theorem sim.basic.Vec2.length_squared_refines (a : sim.basic.Vec2) :
    ∃ r, sim.basic.Vec2.length_squared a = ok r ∧ OsuModel.Sim.Vec2.lengthSquared (abs a) = abs r := by
  simp [sim.basic.Vec2.length_squared, OsuModel.Sim.Vec2.lengthSquared, abs]

/-! ## Mat3 / DrawInfo -/
theorem sim.basic.translate_from_left_refines (m : sim.basic.Mat3) (v : sim.basic.Vec2) :
    ∃ r, sim.basic.translate_from_left m v = ok r ∧ OsuModel.Sim.Mat3.translateFromLeft (abs m) (abs v) = abs r := by
  simp [sim.basic.translate_from_left, OsuModel.Sim.Mat3.translateFromLeft, abs]
theorem sim.basic.translate_from_right_refines (m : sim.basic.Mat3) (v : sim.basic.Vec2) :
    ∃ r, sim.basic.translate_from_right m v = ok r ∧ OsuModel.Sim.Mat3.translateFromRight (abs m) (abs v) = abs r := by
  simp [sim.basic.translate_from_right, OsuModel.Sim.Mat3.translateFromRight, abs]
theorem sim.basic.scale_from_left_refines (m : sim.basic.Mat3) (v : sim.basic.Vec2) :
    ∃ r, sim.basic.scale_from_left m v = ok r ∧ OsuModel.Sim.Mat3.scaleFromLeft (abs m) (abs v) = abs r := by
  simp [sim.basic.scale_from_left, OsuModel.Sim.Mat3.scaleFromLeft, abs]
theorem sim.basic.scale_from_right_refines (m : sim.basic.Mat3) (v : sim.basic.Vec2) :
    ∃ r, sim.basic.scale_from_right m v = ok r ∧ OsuModel.Sim.Mat3.scaleFromRight (abs m) (abs v) = abs r := by
  simp [sim.basic.scale_from_right, OsuModel.Sim.Mat3.scaleFromRight, abs]
theorem sim.basic.mat3_transform_refines (m : sim.basic.Mat3) (p : sim.basic.Vec2) :
    ∃ r, sim.basic.mat3_transform m p = ok r ∧ OsuModel.Sim.Mat3.transform (abs m) (abs p) = abs r := by
  simp [sim.basic.mat3_transform, OsuModel.Sim.Mat3.transform, abs]
theorem sim.basic.to_screen_refines (d : sim.basic.DrawInfo) (p : sim.basic.Vec2) :
    ∃ r, sim.basic.to_screen d p = ok r ∧ OsuModel.Sim.DrawInfo.toScreen (abs d) (abs p) = abs r := by
  simp [sim.basic.to_screen, sim.basic.mat3_transform, OsuModel.Sim.DrawInfo.toScreen,
    OsuModel.Sim.Mat3.transform, abs]
theorem sim.basic.to_local_refines (d : sim.basic.DrawInfo) (p : sim.basic.Vec2) :
    ∃ r, sim.basic.to_local d p = ok r ∧ OsuModel.Sim.DrawInfo.toLocal (abs d) (abs p) = abs r := by
  simp [sim.basic.to_local, sim.basic.mat3_transform, OsuModel.Sim.DrawInfo.toLocal,
    OsuModel.Sim.Mat3.transform, abs]

/-! ## HitResult -/
theorem sim.basic.affects_combo_refines (r : sim.basic.HitResult) :
    ∃ b, sim.basic.affects_combo r = ok b ∧ OsuModel.Sim.HitResult.affectsCombo (abs r) = abs b := by
  cases r <;> simp [sim.basic.affects_combo, OsuModel.Sim.HitResult.affectsCombo, abs, hrS]
theorem sim.basic.is_hit_refines (r : sim.basic.HitResult) :
    ∃ b, sim.basic.is_hit r = ok b ∧ OsuModel.Sim.HitResult.isHit (abs r) = abs b := by
  cases r <;> simp [sim.basic.is_hit, OsuModel.Sim.HitResult.isHit, abs, hrS]
theorem sim.basic.increases_combo_refines (r : sim.basic.HitResult) :
    ∃ b, sim.basic.increases_combo r = ok b ∧ OsuModel.Sim.HitResult.increasesCombo (abs r) = abs b := by
  cases r <;> simp [sim.basic.increases_combo, sim.basic.affects_combo, sim.basic.is_hit,
    OsuModel.Sim.HitResult.increasesCombo, OsuModel.Sim.HitResult.affectsCombo, OsuModel.Sim.HitResult.isHit, abs, hrS]
theorem sim.basic.breaks_combo_refines (r : sim.basic.HitResult) :
    ∃ b, sim.basic.breaks_combo r = ok b ∧ OsuModel.Sim.HitResult.breaksCombo (abs r) = abs b := by
  cases r <;> simp [sim.basic.breaks_combo, sim.basic.affects_combo, sim.basic.is_hit,
    OsuModel.Sim.HitResult.breaksCombo, OsuModel.Sim.HitResult.affectsCombo, OsuModel.Sim.HitResult.isHit, abs, hrS]
theorem sim.basic.is_bonus_refines (r : sim.basic.HitResult) :
    ∃ b, sim.basic.is_bonus r = ok b ∧ OsuModel.Sim.HitResult.isBonus (abs r) = abs b := by
  cases r <;> simp [sim.basic.is_bonus, OsuModel.Sim.HitResult.isBonus, abs, hrS]
theorem sim.basic.is_tick_refines (r : sim.basic.HitResult) :
    ∃ b, sim.basic.is_tick r = ok b ∧ OsuModel.Sim.HitResult.isTick (abs r) = abs b := by
  cases r <;> simp [sim.basic.is_tick, OsuModel.Sim.HitResult.isTick, abs, hrS]
theorem sim.basic.hr_to_nat_refines (r : sim.basic.HitResult) :
    ∃ n, sim.basic.hr_to_nat r = ok n ∧ OsuModel.Sim.HitResult.toNat (abs r) = abs n := by
  cases r <;> simp [sim.basic.hr_to_nat, sim.basic.hr_index, OsuModel.Sim.HitResult.toNat, abs, hrS] <;> rfl
theorem sim.basic.is_scorable_refines (r : sim.basic.HitResult) :
    ∃ b, sim.basic.is_scorable r = ok b ∧ OsuModel.Sim.HitResult.isScorable (abs r) = abs b := by
  cases r <;> simp [sim.basic.is_scorable, sim.basic.hr_to_nat, sim.basic.hr_index,
    OsuModel.Sim.HitResult.isScorable, OsuModel.Sim.HitResult.toNat, abs, hrS] <;> decide
theorem sim.basic.affects_accuracy_refines (r : sim.basic.HitResult) :
    ∃ b, sim.basic.affects_accuracy r = ok b ∧ OsuModel.Sim.HitResult.affectsAccuracy (abs r) = abs b := by
  cases r <;> simp [sim.basic.affects_accuracy, sim.basic.is_scorable, sim.basic.is_bonus, sim.basic.hr_to_nat,
    sim.basic.hr_index, OsuModel.Sim.HitResult.affectsAccuracy, OsuModel.Sim.HitResult.isScorable,
    OsuModel.Sim.HitResult.isBonus, OsuModel.Sim.HitResult.toNat, abs, hrS] <;> decide

theorem sim.basic.almost_equals_d_refines (a b : F64) :
    ∃ r, sim.basic.almost_equals_d a b = ok r ∧ OsuModel.Sim.almostEqualsD (abs a) (abs b) = abs r := by
  simp [sim.basic.almost_equals_d, OsuModel.Sim.almostEqualsD, abs]

/-! ## Playable -/
theorem sim.playable.is_circle_like_refines (k : sim.playable.Kind) :
    ∃ b, sim.playable.is_circle_like k = ok b ∧ OsuModel.Sim.Kind.isCircleLike (abs k) = abs b := by
  cases k <;> simp [sim.playable.is_circle_like, OsuModel.Sim.Kind.isCircleLike, abs, kindS]
theorem sim.playable.result_for_refines (hw : sim.playable.HitWindows) (t : F64) :
    ∃ r, sim.playable.result_for hw t = ok r ∧ OsuModel.Sim.HitWindows.resultFor (abs hw) (abs t) = abs r := by
  simp only [sim.playable.result_for, OsuModel.Sim.HitWindows.resultFor, abs, float.F64.abs, float.F64.le,
    bind_tc_ok]
  split_ifs <;> simp_all [hrS]
theorem sim.playable.can_be_hit_refines (hw : sim.playable.HitWindows) (t : F64) :
    ∃ b, sim.playable.can_be_hit hw t = ok b ∧ OsuModel.Sim.HitWindows.canBeHit (abs hw) (abs t) = abs b := by
  simp [sim.playable.can_be_hit, OsuModel.Sim.HitWindows.canBeHit, abs]

/-! ## DrawInfo.applyTransform (rotation 0 / with rotation) -/
/-- The local `fix` of `DrawInfo.applyTransform` (zero-scale clamping). -/
def simFixScale (s : F32) : F32 :=
  let eps : F32 := Float32.ofBits 0x3A83126F
  if F32.abs s < eps then (if s == 0 then eps else if s < 0 then -eps else eps) else s
theorem sim.basic.fix_scale_refines (s : F32) :
    ∃ r, sim.basic.fix_scale s = ok r ∧ simFixScale (abs s) = abs r := by
  simp only [sim.basic.fix_scale, simFixScale, abs, sim_basic_FLOAT_EPSILON, sim_basic_F32_0, float.F32.abs,
    float.F32.lt, float.F32.eq, float.F32.neg, bind_tc_ok]
  split_ifs <;> simp_all

/-- `DrawInfo.applyTransform` with its local `fix` named (`simFixScale`); definitionally the spec. -/
def simApplyTransform (di : OsuModel.Sim.DrawInfo) (translation scale origin : OsuModel.Sim.Vec2) : OsuModel.Sim.DrawInfo :=
  Id.run do
  let mut m := di.matrix
  let mut mi := di.inverse
  if !(translation.eq OsuModel.Sim.Vec2.zero) then
    m := m.translateFromLeft translation
    mi := mi.translateFromRight (-translation)
  if !(scale.eq ⟨1, 1⟩) then
    let s : OsuModel.Sim.Vec2 := ⟨simFixScale scale.x, simFixScale scale.y⟩
    m := m.scaleFromLeft s
    mi := mi.scaleFromRight ⟨1 / s.x, 1 / s.y⟩
  if !(origin.eq OsuModel.Sim.Vec2.zero) then
    m := m.translateFromLeft (-origin)
    mi := mi.translateFromRight origin
  return ⟨m, mi⟩
theorem simApplyTransform_eq (di : OsuModel.Sim.DrawInfo) (t s o : OsuModel.Sim.Vec2) :
    OsuModel.Sim.DrawInfo.applyTransform di t s o = simApplyTransform di t s o := rfl

set_option maxHeartbeats 1000000 in
theorem sim.basic.apply_transform_refines (d : sim.basic.DrawInfo) (tr sc o : sim.basic.Vec2) :
    ∃ r, sim.basic.apply_transform d tr sc o = ok r ∧
      OsuModel.Sim.DrawInfo.applyTransform (abs d) (abs tr) (abs sc) (abs o) = abs r := by
  obtain ⟨fx, hfx, efx⟩ := sim.basic.fix_scale_refines sc.x
  obtain ⟨fy, hfy, efy⟩ := sim.basic.fix_scale_refines sc.y
  simp only [abs, id] at efx efy
  rw [simApplyTransform_eq]
  simp only [sim.basic.apply_transform, simApplyTransform, hfx, hfy]
  cases e1 : (tr.x == 0) <;> cases e2 : (tr.y == 0) <;> cases e3 : (sc.x == 1) <;> cases e4 : (sc.y == 1) <;>
  cases e5 : (o.x == 0) <;> cases e6 : (o.y == 0) <;>
  simp [e1, e2, e3, e4, e5, e6, efx, efy, sim.basic.Vec2.eq, sim.basic.Vec2.neg, sim.basic.translate_from_left,
    sim.basic.translate_from_right, sim.basic.scale_from_left, sim.basic.scale_from_right, OsuModel.Sim.Vec2.eq,
    OsuModel.Sim.Vec2.zero, OsuModel.Sim.Vec2.neg, OsuModel.Sim.Mat3.translateFromLeft,
    OsuModel.Sim.Mat3.translateFromRight, OsuModel.Sim.Mat3.scaleFromLeft, OsuModel.Sim.Mat3.scaleFromRight, abs,
    Neg.neg] <;> rfl

theorem sim.basic.rot_l_refines (m : sim.basic.Mat3) (rad : F32) :
    ∃ r, sim.basic.rot_l m rad = ok r ∧ OsuModel.Sim.DrawInfo.rotL (abs m) (abs rad) = abs r := by
  simp [sim.basic.rot_l, OsuModel.Sim.DrawInfo.rotL, abs]
theorem sim.basic.rot_r_refines (m : sim.basic.Mat3) (rad : F32) :
    ∃ r, sim.basic.rot_r m rad = ok r ∧ OsuModel.Sim.DrawInfo.rotR (abs m) (abs rad) = abs r := by
  simp [sim.basic.rot_r, OsuModel.Sim.DrawInfo.rotR, abs]

theorem sim.basic.fmod1_refines (x : F64) :
    ∃ r, sim.basic.fmod1 x = ok r ∧ OsuModel.Sim.fmod1 (abs x) = abs r := by
  have z : (0 : F64).isNaN = false := by decide
  simp only [sim.basic.fmod1, OsuModel.Sim.fmod1, abs, id, netx_F64_INTEGER_BOUNDARY, netx_F64_ZERO, netx_F64_NAN,
    netx_F64_POS_INF, float.F64.abs, float.F64.lt, float.F64.trunc, float.F64.sub, float.F64.eq, float.F64.is_nan,
    bind_tc_ok]
  by_cases h1 : F64.abs x < F64.integerBoundary
  · have hn := (FloatFacts.f64_abs_lt _ _ h1).1
    try simp only [h1, decide_true, ite_true]
    split_ifs <;> simp_all [sim.netx.f64_copy_sign_refines _ _ z hn]
  · try simp only [h1, decide_false, ite_false]
    by_cases h2 : x.isNaN = true
    · simp [h2, h1]
    · have hn : x.isNaN = false := by simpa using h2
      by_cases h3 : (F64.abs x == F64.posInf) = true <;>
        simp [h1, h2, h3, hn, sim.netx.f64_copy_sign_refines _ _ z hn]

end OsuProofs
