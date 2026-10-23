/-
`net::osutk` (Rust) refines `OsuModel.Net.OsuTK` (osuTK Vector2/Vector3/Matrix3/MathHelper).
All straight-line float code: each proof unfolds both sides to the same IEEE expression.
-/
import OsuProofs.Repr
import OsuProofs.Spec.FloatFacts
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Net.OsuTK

namespace OsuProofs
open OsuImpl

@[simp] theorem osutk_F32_ONE : net.osutk.F32_ONE = ok (1 : F32) := by
  unfold net.osutk.F32_ONE; simp; decide +kernel
@[simp] theorem osutk_F32_ZERO : net.osutk.F32_ZERO = ok (0 : F32) := by
  unfold net.osutk.F32_ZERO; simp; decide +kernel
@[simp] theorem osutk_HALF_F : net.osutk.HALF_F = ok MathHelper.inverseSqrtFast.half := by
  unfold net.osutk.HALF_F; simp [MathHelper.inverseSqrtFast.half]
@[simp] theorem osutk_THREE_HALVES_F : net.osutk.THREE_HALVES_F = ok MathHelper.inverseSqrtFast.threeHalves := by
  unfold net.osutk.THREE_HALVES_F; simp [MathHelper.inverseSqrtFast.threeHalves]

theorem net.osutk.v2_refines (x y : F32) : net.osutk.v2 x y = ok (v2I ⟨x, y⟩) := by
  simp [net.osutk.v2, v2I]
theorem net.osutk.v2_add_refines (a b : net.osutk.Vector2) :
    net.osutk.v2_add a b = ok (v2I (Vector2.add (v2S a) (v2S b))) := by
  simp [net.osutk.v2_add, Vector2.add, v2S, v2I]
theorem net.osutk.v2_sub_refines (a b : net.osutk.Vector2) :
    net.osutk.v2_sub a b = ok (v2I (Vector2.sub (v2S a) (v2S b))) := by
  simp [net.osutk.v2_sub, Vector2.sub, v2S, v2I]
theorem net.osutk.v2_neg_refines (a : net.osutk.Vector2) :
    net.osutk.v2_neg a = ok (v2I (Vector2.neg (v2S a))) := by
  simp [net.osutk.v2_neg, Vector2.neg, v2S, v2I]
theorem net.osutk.v2_scale_refines (a : net.osutk.Vector2) (s : F32) :
    net.osutk.v2_scale a s = ok (v2I (Vector2.scale (v2S a) s)) := by
  simp [net.osutk.v2_scale, Vector2.scale, v2S, v2I]
theorem net.osutk.v2_mul_refines (a b : net.osutk.Vector2) :
    net.osutk.v2_mul a b = ok (v2I (Vector2.mul (v2S a) (v2S b))) := by
  simp [net.osutk.v2_mul, Vector2.mul, v2S, v2I]
theorem net.osutk.v2_div_s_refines (a : net.osutk.Vector2) (s : F32) :
    net.osutk.v2_div_s a s = ok (v2I (Vector2.divS (v2S a) s)) := by
  simp [net.osutk.v2_div_s, Vector2.divS, v2S, v2I]
theorem net.osutk.v2_divide_refines (a b : net.osutk.Vector2) :
    net.osutk.v2_divide a b = ok (v2I (Vector2.divide (v2S a) (v2S b))) := by
  simp [net.osutk.v2_divide, Vector2.divide, v2S, v2I]
theorem net.osutk.v2_eq_refines (a b : net.osutk.Vector2) :
    net.osutk.v2_eq a b = ok (Vector2.eq (v2S a) (v2S b)) := by
  simp [net.osutk.v2_eq, Vector2.eq, v2S]
theorem net.osutk.v2_length_squared_refines (a : net.osutk.Vector2) :
    net.osutk.v2_length_squared a = ok (Vector2.lengthSquared (v2S a)) := by
  simp [net.osutk.v2_length_squared, Vector2.lengthSquared, v2S]
theorem net.osutk.v2_length_refines (a : net.osutk.Vector2) :
    net.osutk.v2_length a = ok (Vector2.length (v2S a)) := by
  simp [net.osutk.v2_length, Vector2.length, v2S]
theorem net.osutk.v2_perpendicular_right_refines (a : net.osutk.Vector2) :
    net.osutk.v2_perpendicular_right a = ok (v2I (Vector2.perpendicularRight (v2S a))) := by
  simp [net.osutk.v2_perpendicular_right, Vector2.perpendicularRight, v2S, v2I]
theorem net.osutk.v2_perpendicular_left_refines (a : net.osutk.Vector2) :
    net.osutk.v2_perpendicular_left a = ok (v2I (Vector2.perpendicularLeft (v2S a))) := by
  simp [net.osutk.v2_perpendicular_left, Vector2.perpendicularLeft, v2S, v2I]
theorem net.osutk.v2_normalized_refines (a : net.osutk.Vector2) :
    net.osutk.v2_normalized a = ok (v2I (Vector2.normalized (v2S a))) := by
  simp [net.osutk.v2_normalized, Vector2.normalized, net.osutk.v2_length_refines, v2S, v2I]
theorem net.osutk.v2_distance_refines (a b : net.osutk.Vector2) :
    net.osutk.v2_distance a b = ok (Vector2.distance (v2S a) (v2S b)) := by
  simp [net.osutk.v2_distance, Vector2.distance, v2S]
theorem net.osutk.v2_distance_squared_refines (a b : net.osutk.Vector2) :
    net.osutk.v2_distance_squared a b = ok (Vector2.distanceSquared (v2S a) (v2S b)) := by
  simp [net.osutk.v2_distance_squared, Vector2.distanceSquared, v2S]
theorem net.osutk.v2_dot_refines (a b : net.osutk.Vector2) :
    net.osutk.v2_dot a b = ok (Vector2.dot (v2S a) (v2S b)) := by
  simp [net.osutk.v2_dot, Vector2.dot, v2S]
theorem net.osutk.v2_perp_dot_refines (a b : net.osutk.Vector2) :
    net.osutk.v2_perp_dot a b = ok (Vector2.perpDot (v2S a) (v2S b)) := by
  simp [net.osutk.v2_perp_dot, Vector2.perpDot, v2S]
theorem net.osutk.v2_lerp_refines (a b : net.osutk.Vector2) (t : F32) :
    net.osutk.v2_lerp a b t = ok (v2I (Vector2.lerp (v2S a) (v2S b) t)) := by
  simp [net.osutk.v2_lerp, Vector2.lerp, v2S, v2I]
theorem net.osutk.clamp_c_refines (x l h : F32) :
    net.osutk.clamp_c x l h = ok (if x < l then l else if h < x then h else x) := by
  simp only [net.osutk.clamp_c, float.F32.lt]; split_ifs <;> simp_all
theorem net.osutk.v2_clamp_refines (v lo hi : net.osutk.Vector2) :
    net.osutk.v2_clamp v lo hi = ok (v2I (Vector2.clamp (v2S v) (v2S lo) (v2S hi))) := by
  by_cases h1 : v.x < lo.x <;> by_cases h2 : hi.x < v.x <;> by_cases h3 : v.y < lo.y <;>
    by_cases h4 : hi.y < v.y <;>
    simp [net.osutk.v2_clamp, Vector2.clamp, net.osutk.clamp_c_refines, v2S, v2I, h1, h2, h3, h4]
theorem net.osutk.v2_component_min_refines (a b : net.osutk.Vector2) :
    net.osutk.v2_component_min a b = ok (v2I (Vector2.componentMin (v2S a) (v2S b))) := by
  by_cases hx : a.x < b.x <;> by_cases hy : a.y < b.y <;>
    simp [net.osutk.v2_component_min, Vector2.componentMin, v2S, v2I, hx, hy]
theorem net.osutk.v2_component_max_refines (a b : net.osutk.Vector2) :
    net.osutk.v2_component_max a b = ok (v2I (Vector2.componentMax (v2S a) (v2S b))) := by
  by_cases hx : b.x < a.x <;> by_cases hy : b.y < a.y <;>
    simp [net.osutk.v2_component_max, Vector2.componentMax, v2S, v2I, hx, hy]
theorem net.osutk.v3_add_refines (a b : net.osutk.Vector3) :
    net.osutk.v3_add a b = ok (v3I (Vector3.add (v3S a) (v3S b))) := by
  simp [net.osutk.v3_add, Vector3.add, v3S, v3I]
theorem net.osutk.v3_sub_refines (a b : net.osutk.Vector3) :
    net.osutk.v3_sub a b = ok (v3I (Vector3.sub (v3S a) (v3S b))) := by
  simp [net.osutk.v3_sub, Vector3.sub, v3S, v3I]
theorem net.osutk.v3_scale_refines (a : net.osutk.Vector3) (s : F32) :
    net.osutk.v3_scale a s = ok (v3I (Vector3.scale (v3S a) s)) := by
  simp [net.osutk.v3_scale, Vector3.scale, v3S, v3I]
theorem net.osutk.m3_mult_refines (l r : net.osutk.Matrix3) :
    net.osutk.m3_mult l r = ok (m3I (Matrix3.mult (m3S l) (m3S r))) := by
  simp [net.osutk.m3_mult, net.osutk.m3_row, Matrix3.mult, m3S, m3I, v3S, v3I]
/-- The bit trick of `InverseSqrtFast`: `0x5f375a86 - (i >> 1)` on `int` (arithmetic shift). -/
theorem isf_spec (b : UInt32) : Int32.toUInt32 1597463174 - (ShiftRight.shiftRight b.toInt32 1).toUInt32
    = UInt32.ofBitVec (1597463174#32 - b.toBitVec.sshiftRight 1) := by
  apply UInt32.toBitVec_inj.mp
  have : (b.toInt32 >>> (1 : Int32)).toBitVec = b.toBitVec.sshiftRight 1 := by
    simp [Int32.toBitVec_shiftRight, BitVec.sshiftRight']
  rw [UInt32.toBitVec_sub, UInt32.toBitVec_ofBitVec]
  exact congrArg (1597463174#32 - ·) this

/-- NaN: the Rust returns its argument before `to_bits` (partial on NaN); the spec computes NaN. -/
theorem net.osutk.inverse_sqrt_fast_refines (x : F32) :
    net.osutk.inverse_sqrt_fast x = ok (MathHelper.inverseSqrtFast x) := by
  cases h : x.isNaN
  · simp [net.osutk.inverse_sqrt_fast, h, f32_to_bits_eq x h, net.osutk.HALF_F, net.osutk.THREE_HALVES_F,
      MathHelper.inverseSqrtFast, HShiftRight.hShiftRight, IScalar.shiftRight_IScalar, IScalar.shiftRight,
      core.num.I32.wrapping_sub, IScalar.wrapping_sub, IScalar.hcast, UScalar.hcast, lift,
      MathHelper.inverseSqrtFast.threeHalves, MathHelper.inverseSqrtFast.half, u32_ofNat_val, isf_spec]
  · have hx := FloatFacts.f32_isNaN_eq x h
    subst hx
    simp [net.osutk.inverse_sqrt_fast, h]
    decide
theorem net.osutk.length_fast_refines (a : net.osutk.Vector2) :
    net.osutk.length_fast a = ok (MathHelper.lengthFast (v2S a)) := by
  simp [net.osutk.length_fast, MathHelper.lengthFast, net.osutk.inverse_sqrt_fast_refines, v2S]
theorem net.osutk.normalize_fast_refines (a : net.osutk.Vector2) :
    net.osutk.normalize_fast a = ok (v2I (MathHelper.normalizeFast (v2S a))) := by
  simp [net.osutk.normalize_fast, MathHelper.normalizeFast, net.osutk.inverse_sqrt_fast_refines, v2S, v2I]
theorem net.osutk.degrees_to_radians_f_refines (d : F32) :
    net.osutk.degrees_to_radians_f d = ok (MathHelper.degreesToRadiansF d) := by
  simp [net.osutk.degrees_to_radians_f, net.osutk.DEG_TO_RAD_F, MathHelper.degreesToRadiansF, MathHelper.degToRadF]
theorem net.osutk.radians_to_degrees_f_refines (d : F32) :
    net.osutk.radians_to_degrees_f d = ok (MathHelper.radiansToDegreesF d) := by
  simp [net.osutk.radians_to_degrees_f, net.osutk.RAD_TO_DEG_F, MathHelper.radiansToDegreesF, MathHelper.radToDegF]
theorem net.osutk.degrees_to_radians_d_refines (d : F64) :
    net.osutk.degrees_to_radians_d d = ok (MathHelper.degreesToRadiansD d) := by
  simp [net.osutk.degrees_to_radians_d, net.osutk.DEG_TO_RAD_D, MathHelper.degreesToRadiansD, MathHelper.degToRadD]
theorem net.osutk.radians_to_degrees_d_refines (d : F64) :
    net.osutk.radians_to_degrees_d d = ok (MathHelper.radiansToDegreesD d) := by
  simp [net.osutk.radians_to_degrees_d, net.osutk.RAD_TO_DEG_D, MathHelper.radiansToDegreesD, MathHelper.radToDegD]

end OsuProofs
