/-
`net::framework` (Rust) refines `OsuModel.Net.Framework` (osu-framework `Precision`, easing,
`Interpolation`, `Vector2Extensions`, `MatrixExtensions`, `DrawInfo.ApplyTransform`).
Part A: everything except the `BindableNumber` state machine (which needs `net::decimal`).
-/
import OsuProofs.Net.SysMisc
import OsuProofs.Net.OsuTK
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Net.OsuTK OsuModel.Net.Framework

namespace OsuProofs
open OsuImpl

def easingS : net.framework.Easing → Easing
  | .None => .none
  | .Out => .out
  | .In => .in_
  | .InQuad => .inQuad
  | .OutQuad => .outQuad
  | .InOutQuad => .inOutQuad
  | .InCubic => .inCubic
  | .OutCubic => .outCubic
  | .InOutCubic => .inOutCubic
  | .InQuart => .inQuart
  | .OutQuart => .outQuart
  | .InOutQuart => .inOutQuart
  | .InQuint => .inQuint
  | .OutQuint => .outQuint
  | .InOutQuint => .inOutQuint
  | .InSine => .inSine
  | .OutSine => .outSine
  | .InOutSine => .inOutSine
  | .InExpo => .inExpo
  | .OutExpo => .outExpo
  | .InOutExpo => .inOutExpo
  | .InCirc => .inCirc
  | .OutCirc => .outCirc
  | .InOutCirc => .inOutCirc
  | .InElastic => .inElastic
  | .OutElastic => .outElastic
  | .OutElasticHalf => .outElasticHalf
  | .OutElasticQuarter => .outElasticQuarter
  | .InOutElastic => .inOutElastic
  | .InBack => .inBack
  | .OutBack => .outBack
  | .InOutBack => .inOutBack
  | .InBounce => .inBounce
  | .OutBounce => .outBounce
  | .InOutBounce => .inOutBounce
  | .OutPow10 => .outPow10

/-! ## constants (each `from_bits` literal is the spec literal, by kernel evaluation) -/
@[simp] theorem fw_FLOAT_EPSILON : net.framework.FLOAT_EPSILON = ok Precision.FLOAT_EPSILON := by
  simp [net.framework.FLOAT_EPSILON, Precision.FLOAT_EPSILON]
@[simp] theorem fw_DOUBLE_EPSILON : net.framework.DOUBLE_EPSILON = ok Precision.DOUBLE_EPSILON := by
  simp [net.framework.DOUBLE_EPSILON, Precision.DOUBLE_EPSILON]
@[simp] theorem fw_PI : net.framework.PI = ok (EasingConst.pi : F64) := by
  simp [net.framework.PI, EasingConst.pi] <;> decide
@[simp] theorem fw_K1 : net.framework.K1 = ok (1 : F64) := by
  simp [net.framework.K1] <;> decide
@[simp] theorem fw_K2 : net.framework.K2 = ok (2 : F64) := by
  simp [net.framework.K2] <;> decide
@[simp] theorem fw_K4 : net.framework.K4 = ok (4 : F64) := by
  simp [net.framework.K4] <;> decide
@[simp] theorem fw_K8 : net.framework.K8 = ok (8 : F64) := by
  simp [net.framework.K8] <;> decide
@[simp] theorem fw_K10 : net.framework.K10 = ok (10 : F64) := by
  simp [net.framework.K10] <;> decide
@[simp] theorem fw_K16 : net.framework.K16 = ok (16 : F64) := by
  simp [net.framework.K16] <;> decide
@[simp] theorem fw_K20 : net.framework.K20 = ok (20 : F64) := by
  simp [net.framework.K20] <;> decide
@[simp] theorem fw_K11 : net.framework.K11 = ok (11 : F64) := by
  simp [net.framework.K11] <;> decide
@[simp] theorem fw_K0_3 : net.framework.K0_3 = ok (0.3 : F64) := by
  simp [net.framework.K0_3] <;> decide
@[simp] theorem fw_K1_5 : net.framework.K1_5 = ok (1.5 : F64) := by
  simp [net.framework.K1_5] <;> decide
@[simp] theorem fw_K1_525 : net.framework.K1_525 = ok (1.525 : F64) := by
  simp [net.framework.K1_525] <;> decide
@[simp] theorem fw_K2_5 : net.framework.K2_5 = ok (2.5 : F64) := by
  simp [net.framework.K2_5] <;> decide
@[simp] theorem fw_K2_25 : net.framework.K2_25 = ok (2.25 : F64) := by
  simp [net.framework.K2_25] <;> decide
@[simp] theorem fw_K2_625 : net.framework.K2_625 = ok (2.625 : F64) := by
  simp [net.framework.K2_625] <;> decide
@[simp] theorem fw_K2_75 : net.framework.K2_75 = ok (2.75 : F64) := by
  simp [net.framework.K2_75] <;> decide
@[simp] theorem fw_BACK_CONST : net.framework.BACK_CONST = ok (EasingConst.back_const : F64) := by
  simp [net.framework.BACK_CONST, EasingConst.back_const] <;> decide
@[simp] theorem fw_C7_5625 : net.framework.C7_5625 = ok (EasingConst.c7_5625 : F64) := by
  simp [net.framework.C7_5625, EasingConst.c7_5625] <;> decide
@[simp] theorem fw_C0_75 : net.framework.C0_75 = ok (EasingConst.c0_75 : F64) := by
  simp [net.framework.C0_75, EasingConst.c0_75] <;> decide
@[simp] theorem fw_C0_9375 : net.framework.C0_9375 = ok (EasingConst.c0_9375 : F64) := by
  simp [net.framework.C0_9375, EasingConst.c0_9375] <;> decide
@[simp] theorem fw_C0_984375 : net.framework.C0_984375 = ok (EasingConst.c0_984375 : F64) := by
  simp [net.framework.C0_984375, EasingConst.c0_984375] <;> decide
@[simp] theorem fw_HALF : net.framework.HALF = ok (EasingConst.half : F64) := by
  simp [net.framework.HALF, EasingConst.half] <;> decide
@[simp] theorem fw_QUARTER : net.framework.QUARTER = ok (EasingConst.quarter : F64) := by
  simp [net.framework.QUARTER, EasingConst.quarter] <;> decide
@[simp] theorem fw_elastic_const : net.framework.elastic_const = ok EasingConst.elastic_const := by
  simp [net.framework.elastic_const, EasingConst.elastic_const, EasingConst.elastic_const, EasingConst.elastic_const2, EasingConst.back_const2, EasingConst.bounce_const, EasingConst.ec2_15, EasingConst.half, EasingConst.quarter]
@[simp] theorem fw_elastic_const2 : net.framework.elastic_const2 = ok EasingConst.elastic_const2 := by
  simp [net.framework.elastic_const2, EasingConst.elastic_const2, EasingConst.elastic_const, EasingConst.elastic_const2, EasingConst.back_const2, EasingConst.bounce_const, EasingConst.ec2_15, EasingConst.half, EasingConst.quarter]
@[simp] theorem fw_back_const2 : net.framework.back_const2 = ok EasingConst.back_const2 := by
  simp [net.framework.back_const2, EasingConst.back_const2, EasingConst.elastic_const, EasingConst.elastic_const2, EasingConst.back_const2, EasingConst.bounce_const, EasingConst.ec2_15, EasingConst.half, EasingConst.quarter]
@[simp] theorem fw_back_const_p1 : net.framework.back_const_p1 = ok EasingConst.back_const_p1 := by
  simp [net.framework.back_const_p1, EasingConst.back_const_p1, EasingConst.elastic_const, EasingConst.elastic_const2, EasingConst.back_const2, EasingConst.bounce_const, EasingConst.ec2_15, EasingConst.half, EasingConst.quarter]
@[simp] theorem fw_back_const2_p1 : net.framework.back_const2_p1 = ok EasingConst.back_const2_p1 := by
  simp [net.framework.back_const2_p1, EasingConst.back_const2_p1, EasingConst.elastic_const, EasingConst.elastic_const2, EasingConst.back_const2, EasingConst.bounce_const, EasingConst.ec2_15, EasingConst.half, EasingConst.quarter]
@[simp] theorem fw_bounce_const : net.framework.bounce_const = ok EasingConst.bounce_const := by
  simp [net.framework.bounce_const, EasingConst.bounce_const, EasingConst.elastic_const, EasingConst.elastic_const2, EasingConst.back_const2, EasingConst.bounce_const, EasingConst.ec2_15, EasingConst.half, EasingConst.quarter]
@[simp] theorem fw_b2 : net.framework.b2 = ok EasingConst.b2 := by
  simp [net.framework.b2, EasingConst.b2, EasingConst.elastic_const, EasingConst.elastic_const2, EasingConst.back_const2, EasingConst.bounce_const, EasingConst.ec2_15, EasingConst.half, EasingConst.quarter]
@[simp] theorem fw_b25 : net.framework.b25 = ok EasingConst.b25 := by
  simp [net.framework.b25, EasingConst.b25, EasingConst.elastic_const, EasingConst.elastic_const2, EasingConst.back_const2, EasingConst.bounce_const, EasingConst.ec2_15, EasingConst.half, EasingConst.quarter]
@[simp] theorem fw_b15 : net.framework.b15 = ok EasingConst.b15 := by
  simp [net.framework.b15, EasingConst.b15, EasingConst.elastic_const, EasingConst.elastic_const2, EasingConst.back_const2, EasingConst.bounce_const, EasingConst.ec2_15, EasingConst.half, EasingConst.quarter]
@[simp] theorem fw_b225 : net.framework.b225 = ok EasingConst.b225 := by
  simp [net.framework.b225, EasingConst.b225, EasingConst.elastic_const, EasingConst.elastic_const2, EasingConst.back_const2, EasingConst.bounce_const, EasingConst.ec2_15, EasingConst.half, EasingConst.quarter]
@[simp] theorem fw_b2625 : net.framework.b2625 = ok EasingConst.b2625 := by
  simp [net.framework.b2625, EasingConst.b2625, EasingConst.elastic_const, EasingConst.elastic_const2, EasingConst.back_const2, EasingConst.bounce_const, EasingConst.ec2_15, EasingConst.half, EasingConst.quarter]
@[simp] theorem fw_one_m_ec2 : net.framework.one_m_ec2 = ok EasingConst.one_m_ec2 := by
  simp [net.framework.one_m_ec2, EasingConst.one_m_ec2, EasingConst.elastic_const, EasingConst.elastic_const2, EasingConst.back_const2, EasingConst.bounce_const, EasingConst.ec2_15, EasingConst.half, EasingConst.quarter]
@[simp] theorem fw_ec2_15 : net.framework.ec2_15 = ok EasingConst.ec2_15 := by
  simp [net.framework.ec2_15, EasingConst.ec2_15, EasingConst.elastic_const, EasingConst.elastic_const2, EasingConst.back_const2, EasingConst.bounce_const, EasingConst.ec2_15, EasingConst.half, EasingConst.quarter]
@[simp] theorem fw_one_m_ec2_15 : net.framework.one_m_ec2_15 = ok EasingConst.one_m_ec2_15 := by
  simp [net.framework.one_m_ec2_15, EasingConst.one_m_ec2_15, EasingConst.elastic_const, EasingConst.elastic_const2, EasingConst.back_const2, EasingConst.bounce_const, EasingConst.ec2_15, EasingConst.half, EasingConst.quarter]
@[simp] theorem fw_expo_offset : net.framework.expo_offset = ok EasingConst.expo_offset := by
  simp [net.framework.expo_offset, EasingConst.expo_offset, EasingConst.elastic_const, EasingConst.elastic_const2, EasingConst.back_const2, EasingConst.bounce_const, EasingConst.ec2_15, EasingConst.half, EasingConst.quarter]
@[simp] theorem fw_elastic_offset_full : net.framework.elastic_offset_full = ok EasingConst.elastic_offset_full := by
  simp [net.framework.elastic_offset_full, EasingConst.elastic_offset_full, EasingConst.elastic_const, EasingConst.elastic_const2, EasingConst.back_const2, EasingConst.bounce_const, EasingConst.ec2_15, EasingConst.half, EasingConst.quarter]
@[simp] theorem fw_elastic_offset_half : net.framework.elastic_offset_half = ok EasingConst.elastic_offset_half := by
  simp [net.framework.elastic_offset_half, EasingConst.elastic_offset_half, EasingConst.elastic_const, EasingConst.elastic_const2, EasingConst.back_const2, EasingConst.bounce_const, EasingConst.ec2_15, EasingConst.half, EasingConst.quarter]
@[simp] theorem fw_elastic_offset_quarter : net.framework.elastic_offset_quarter = ok EasingConst.elastic_offset_quarter := by
  simp [net.framework.elastic_offset_quarter, EasingConst.elastic_offset_quarter, EasingConst.elastic_const, EasingConst.elastic_const2, EasingConst.back_const2, EasingConst.bounce_const, EasingConst.ec2_15, EasingConst.half, EasingConst.quarter]
@[simp] theorem fw_in_out_elastic_offset : net.framework.in_out_elastic_offset = ok EasingConst.in_out_elastic_offset := by
  simp [net.framework.in_out_elastic_offset, EasingConst.in_out_elastic_offset, EasingConst.elastic_const, EasingConst.elastic_const2, EasingConst.back_const2, EasingConst.bounce_const, EasingConst.ec2_15, EasingConst.half, EasingConst.quarter]

/-! ## Precision -/
theorem net.framework.definitely_bigger_f_refines (a b e : F32) :
    net.framework.definitely_bigger_f a b e = ok (Precision.definitelyBiggerF a b e) := by
  simp [net.framework.definitely_bigger_f, Precision.definitelyBiggerF]
theorem net.framework.definitely_bigger_d_refines (a b e : F64) :
    net.framework.definitely_bigger_d a b e = ok (Precision.definitelyBiggerD a b e) := by
  simp [net.framework.definitely_bigger_d, Precision.definitelyBiggerD]
theorem net.framework.almost_bigger_f_refines (a b e : F32) :
    net.framework.almost_bigger_f a b e = ok (Precision.almostBiggerF a b e) := by
  simp [net.framework.almost_bigger_f, Precision.almostBiggerF]
theorem net.framework.almost_bigger_d_refines (a b e : F64) :
    net.framework.almost_bigger_d a b e = ok (Precision.almostBiggerD a b e) := by
  simp [net.framework.almost_bigger_d, Precision.almostBiggerD]
theorem net.framework.almost_equals_f_refines (a b e : F32) :
    net.framework.almost_equals_f a b e = ok (Precision.almostEqualsF a b e) := by
  simp [net.framework.almost_equals_f, Precision.almostEqualsF]
theorem net.framework.almost_equals_d_refines (a b e : F64) :
    net.framework.almost_equals_d a b e = ok (Precision.almostEqualsD a b e) := by
  simp [net.framework.almost_equals_d, Precision.almostEqualsD]
theorem net.framework.almost_equals_v_refines (a b : net.osutk.Vector2) (e : F32) :
    net.framework.almost_equals_v a b e = ok (Precision.almostEqualsV (v2S a) (v2S b) e) := by
  simp [net.framework.almost_equals_v, Precision.almostEqualsV, net.framework.almost_equals_f_refines, v2S]

/-! ## Easing -/
theorem net.framework.out_bounce_refines (t : F64) : net.framework.out_bounce t = ok (outBounce t) := by
  unfold net.framework.out_bounce outBounce
  by_cases h1 : t < EasingConst.bounce_const <;> by_cases h2 : t < EasingConst.b2 <;>
    by_cases h3 : t < EasingConst.b25 <;> simp [h1, h2, h3]

theorem net.framework.apply_easing_refines (e : net.framework.Easing) (t : F64) :
    net.framework.apply_easing e t = ok (applyEasing (easingS e) t) := by
  cases e <;> simp [net.framework.apply_easing, easingS, applyEasing, net.framework.out_bounce_refines]


/-! ## Interpolation -/
theorem v2_add_def (a b : Vector2) : a + b = Vector2.add a b := rfl
theorem v2_sub_def (a b : Vector2) : a - b = Vector2.sub a b := rfl
theorem v2_smul_def (t : F32) (a : Vector2) : t * a = Vector2.scale a t := rfl

theorem net.framework.lerp_refines (a b t : F64) : net.framework.lerp a b t = ok (Interpolation.lerp a b t) := by
  simp [net.framework.lerp, Interpolation.lerp]

theorem net.framework.damp_refines (a b base ex : F64) :
    net.framework.damp a b base ex = ok (exceptI id (Interpolation.damp a b base ex)) := by
  have z : Float.ofBits 0 = (0 : F64) := by decide
  by_cases h1 : base < 0 <;> by_cases h2 : 1 < base <;>
    simp [net.framework.damp, Interpolation.damp, net.framework.lerp_refines, z, h1, h2, exceptI, exnI]

theorem net.framework.damp_continuously_refines (a b h e : F64) :
    net.framework.damp_continuously a b h e = ok (Interpolation.dampContinuously a b h e) := by
  simp [net.framework.damp_continuously, Interpolation.dampContinuously, net.framework.lerp_refines,
    Interpolation.lerp, Interpolation.half, EasingConst.half]

theorem net.framework.value_at_d_refines (time v1 v2 st et : F64) (e : net.framework.Easing) :
    net.framework.value_at_d time v1 v2 st et e = ok (Interpolation.valueAtD time v1 v2 st et (easingS e)) := by
  have z : Float.ofBits 0 = (0 : F64) := by decide
  unfold net.framework.value_at_d Interpolation.valueAtD
  by_cases h1 : (v1 == v2) = true <;> by_cases h2 : (time - st == 0) = true <;>
    by_cases h3 : (et - st == 0) = true <;>
    simp [z, h1, h2, h3, net.framework.apply_easing_refines]

theorem net.framework.value_at_f_refines (time : F64) (v1 v2 : F32) (st et : F64) (e : net.framework.Easing) :
    net.framework.value_at_f time v1 v2 st et e = ok (Interpolation.valueAtF time v1 v2 st et (easingS e)) := by
  simp [net.framework.value_at_f, Interpolation.valueAtF, net.framework.value_at_d_refines]

theorem net.framework.value_at_v_refines (time : F64) (v1 v2 : net.osutk.Vector2) (st et : F64)
    (e : net.framework.Easing) :
    net.framework.value_at_v time v1 v2 st et e = ok (v2I (Interpolation.valueAtV time (v2S v1) (v2S v2) st et (easingS e))) := by
  have z : Float32.ofBits 0 = (0 : F32) := by decide
  unfold net.framework.value_at_v Interpolation.valueAtV
  by_cases h1 : (F64.toF32 (et - st) == 0) = true <;> by_cases h2 : (F64.toF32 (time - st) == 0) = true <;>
    simp [z, h1, h2, net.framework.apply_easing_refines, net.osutk.v2_add_refines, net.osutk.v2_sub_refines,
      net.osutk.v2_scale_refines, v2S, v2I, v2_add_def, v2_sub_def, v2_smul_def, Vector2.add,
      Vector2.sub, Vector2.scale]

/-- Aeneas `I32` ↦ Lean `Int32` (same bits). -/
def i32S (x : I32) : Int32 := Int32.ofBitVec x.bv

theorem i32S_toInt (x : I32) : (i32S x).toInt = x.val := by
  simp [i32S, Int32.toInt_ofBitVec]

theorem net.framework.value_at_i_refines (time : F64) (v1 v2 : I32) (st et : F64) (e : net.framework.Easing) :
    net.framework.value_at_i time v1 v2 st et e =
      ok (i32I (Interpolation.valueAtI time (i32S v1) (i32S v2) st et (easingS e))) := by
  simp [net.framework.value_at_i, Interpolation.valueAtI, lift, F64.ofInt32, i32S_toInt,
    net.framework.value_at_d_refines, net.mathops.f64_round_refines, i32I]

/-! ## Vector2Extensions / MatrixExtensions -/
theorem net.framework.transform_refines (p : net.osutk.Vector2) (m : net.osutk.Matrix3) :
    net.framework.transform p m = ok (v2I (Vector2Extensions.transform (v2S p) (m3S m))) := by
  simp [net.framework.transform, Vector2Extensions.transform, v2S, v2I, m3S, v3S]
theorem net.framework.distance_refines (a b : net.osutk.Vector2) :
    net.framework.distance a b = ok (Vector2Extensions.distance (v2S a) (v2S b)) := by
  simp [net.framework.distance, Vector2Extensions.distance, v2S]
theorem net.framework.distance_squared_refines (a b : net.osutk.Vector2) :
    net.framework.distance_squared a b = ok (Vector2Extensions.distanceSquared (v2S a) (v2S b)) := by
  simp [net.framework.distance_squared, Vector2Extensions.distanceSquared, v2S]


theorem v3_add_def (a b : Vector3) : a + b = Vector3.add a b := rfl
theorem v3_sub_def (a b : Vector3) : a - b = Vector3.sub a b := rfl
theorem v3_smul_def (a : Vector3) (t : F32) : a * t = Vector3.scale a t := rfl

theorem net.framework.translate_from_left_refines (m : net.osutk.Matrix3) (v : net.osutk.Vector2) :
    net.framework.translate_from_left m v = ok (m3I (MatrixExtensions.translateFromLeft (m3S m) (v2S v))) := by
  simp [net.framework.translate_from_left, MatrixExtensions.translateFromLeft, net.osutk.v3_add_refines,
    net.osutk.v3_scale_refines, m3S, m3I, v3S, v3I, v2S, v3_add_def, v3_smul_def, Vector3.add, Vector3.scale]
theorem net.framework.tfr_row_refines (a : net.osutk.Vector3) (v : net.osutk.Vector2) :
    net.framework.tfr_row a v = ok ⟨a.x + a.z * v.x, a.y + a.z * v.y, a.z⟩ := by
  simp [net.framework.tfr_row]
theorem net.framework.translate_from_right_refines (m : net.osutk.Matrix3) (v : net.osutk.Vector2) :
    net.framework.translate_from_right m v = ok (m3I (MatrixExtensions.translateFromRight (m3S m) (v2S v))) := by
  simp [net.framework.translate_from_right, MatrixExtensions.translateFromRight, net.framework.tfr_row_refines,
    m3S, m3I, v3S, v3I, v2S]
theorem net.framework.rotate_from_left_refines (m : net.osutk.Matrix3) (r : F32) :
    net.framework.rotate_from_left m r = ok (m3I (MatrixExtensions.rotateFromLeft (m3S m) r)) := by
  simp [net.framework.rotate_from_left, MatrixExtensions.rotateFromLeft, net.osutk.v3_add_refines,
    net.osutk.v3_sub_refines, net.osutk.v3_scale_refines, m3S, m3I, v3S, v3I, v3_add_def, v3_sub_def,
    v3_smul_def, Vector3.add, Vector3.sub, Vector3.scale, F32.cos, F32.sin]
theorem net.framework.rfr_row_refines (a : net.osutk.Vector3) (c s : F32) :
    net.framework.rfr_row a c s = ok ⟨a.x * c - a.y * s, a.y * c + a.x * s, a.z⟩ := by
  simp [net.framework.rfr_row]
theorem net.framework.rotate_from_right_refines (m : net.osutk.Matrix3) (r : F32) :
    net.framework.rotate_from_right m r = ok (m3I (MatrixExtensions.rotateFromRight (m3S m) r)) := by
  simp [net.framework.rotate_from_right, MatrixExtensions.rotateFromRight, net.framework.rfr_row_refines,
    m3S, m3I, v3S, v3I, F32.cos, F32.sin]
theorem net.framework.scale_from_left_refines (m : net.osutk.Matrix3) (v : net.osutk.Vector2) :
    net.framework.scale_from_left m v = ok (m3I (MatrixExtensions.scaleFromLeft (m3S m) (v2S v))) := by
  simp [net.framework.scale_from_left, MatrixExtensions.scaleFromLeft, net.osutk.v3_scale_refines,
    m3S, m3I, v3S, v3I, v2S, v3_smul_def, Vector3.scale]
theorem net.framework.sfr_row_refines (a : net.osutk.Vector3) (v : net.osutk.Vector2) :
    net.framework.sfr_row a v = ok ⟨a.x * v.x, a.y * v.y, a.z⟩ := by
  simp [net.framework.sfr_row]
theorem net.framework.scale_from_right_refines (m : net.osutk.Matrix3) (v : net.osutk.Vector2) :
    net.framework.scale_from_right m v = ok (m3I (MatrixExtensions.scaleFromRight (m3S m) (v2S v))) := by
  simp [net.framework.scale_from_right, MatrixExtensions.scaleFromRight, net.framework.sfr_row_refines,
    m3S, m3I, v3S, v3I, v2S]
theorem net.framework.shear_from_left_refines (m : net.osutk.Matrix3) (v : net.osutk.Vector2) :
    net.framework.shear_from_left m v = ok (m3I (MatrixExtensions.shearFromLeft (m3S m) (v2S v))) := by
  simp [net.framework.shear_from_left, MatrixExtensions.shearFromLeft, net.osutk.v3_add_refines,
    net.osutk.v3_scale_refines, m3S, m3I, v3S, v3I, v2S, v3_add_def, v3_smul_def, Vector3.add, Vector3.scale]
theorem net.framework.shfr_row_refines (a : net.osutk.Vector3) (v : net.osutk.Vector2) (xy : F32) :
    net.framework.shfr_row a v xy = ok ⟨a.x + a.y * v.x, a.y + (a.x * v.y + a.y * xy), a.z⟩ := by
  simp [net.framework.shfr_row]
theorem net.framework.shear_from_right_refines (m : net.osutk.Matrix3) (v : net.osutk.Vector2) :
    net.framework.shear_from_right m v = ok (m3I (MatrixExtensions.shearFromRight (m3S m) (v2S v))) := by
  simp [net.framework.shear_from_right, MatrixExtensions.shearFromRight, net.framework.shfr_row_refines,
    m3S, m3I, v3S, v3I, v2S]
theorem net.framework.mult_refines (l r : net.osutk.Matrix3) :
    net.framework.mult l r = ok (m3I (Matrix3.mult (m3S l) (m3S r))) := by
  simp [net.framework.mult, net.osutk.m3_mult_refines]

/-! ## DrawInfo -/
def diS (d : net.framework.DrawInfo) : DrawInfo := ⟨m3S d.matrix, m3S d.matrix_inverse⟩
def diI (d : DrawInfo) : net.framework.DrawInfo := ⟨m3I d.matrix, m3I d.matrixInverse⟩

theorem net.framework.clamp_scale_comp_refines (s : F32) :
    net.framework.clamp_scale_comp s = ok (DrawInfo.clampScaleComp s) := by
  have z : Float32.ofBits 0 = (0 : F32) := by decide
  have o : Float32.ofBits 1065353216 = (1 : F32) := by decide
  have no : -(1 : F32) = -1 := rfl
  unfold net.framework.clamp_scale_comp DrawInfo.clampScaleComp
  by_cases h1 : F32.abs s < Precision.FLOAT_EPSILON <;> by_cases h2 : (s == 0) = true <;>
    by_cases h3 : s < 0 <;> simp [z, o, h1, h2, h3]

@[simp] theorem osutk_V2_ZERO : net.osutk.V2_ZERO = ok (v2I Vector2.zero) := by
  simp [net.osutk.V2_ZERO, v2I, Vector2.zero]
@[simp] theorem osutk_V2_ONE : net.osutk.V2_ONE = ok (v2I Vector2.one) := by
  simp [net.osutk.V2_ONE, v2I, Vector2.one]

theorem net.framework.apply_transform_refines (di : net.framework.DrawInfo) (tr sc : net.osutk.Vector2) (rot : F32)
    (sh orig : net.osutk.Vector2) :
    net.framework.apply_transform di tr sc rot sh orig =
      ok (diI (DrawInfo.applyTransform (diS di) (v2S tr) (v2S sc) rot (v2S sh) (v2S orig))) := by
  have z : Float32.ofBits 0 = (0 : F32) := by decide
  unfold net.framework.apply_transform DrawInfo.applyTransform
  by_cases h1 : (v2S tr).eq Vector2.zero = true <;> by_cases h2 : (rot == 0) = true <;>
    by_cases h3 : (v2S sh).eq Vector2.zero = true <;> by_cases h4 : (v2S sc).eq Vector2.one = true <;>
    by_cases h5 : (v2S orig).eq Vector2.zero = true <;>
    simp [z, h1, h2, h3, h4, h5, net.osutk.v2_eq_refines, net.osutk.v2_neg_refines, net.osutk.v2_divide_refines,
      net.framework.translate_from_left_refines, net.framework.translate_from_right_refines,
      net.framework.rotate_from_left_refines, net.framework.rotate_from_right_refines,
      net.framework.shear_from_left_refines, net.framework.shear_from_right_refines,
      net.framework.scale_from_left_refines, net.framework.scale_from_right_refines,
      net.framework.clamp_scale_comp_refines, net.sysmisc.f32_degrees_to_radians_refines, diS, diI, v2_neg_def]

theorem net.framework.clamp_d_refines (v lo hi : F64) :
    net.framework.clamp_d v lo hi = ok (exceptI id (Bindable.clampD v lo hi)) := by
  by_cases h : hi < lo <;> simp [net.framework.clamp_d, Bindable.clampD, h, exceptI, exnI, max_refines, min_refines]
theorem net.framework.clamp_f_refines (v lo hi : F32) :
    net.framework.clamp_f v lo hi = ok (exceptI id (Bindable.clampF v lo hi)) := by
  by_cases h : hi < lo <;> simp [net.framework.clamp_f, Bindable.clampF, h, exceptI, exnI,
    net.mathops.f32_max_refines, net.mathops.f32_min_refines]
theorem net.framework.equals_d_refines (a b : F64) :
    net.framework.equals_d a b = ok (Bindable.equalsD a b) := by
  by_cases h1 : (a == b) = true <;> by_cases h2 : a.isNaN = true <;>
    simp [net.framework.equals_d, Bindable.equalsD, h1, h2]
theorem net.framework.equals_f_refines (a b : F32) :
    net.framework.equals_f a b = ok (Bindable.equalsF a b) := by
  by_cases h1 : (a == b) = true <;> by_cases h2 : a.isNaN = true <;>
    simp [net.framework.equals_f, Bindable.equalsF, h1, h2]

def easingI : Easing → net.framework.Easing
  | .none => .None
  | .out => .Out
  | .in_ => .In
  | .inQuad => .InQuad
  | .outQuad => .OutQuad
  | .inOutQuad => .InOutQuad
  | .inCubic => .InCubic
  | .outCubic => .OutCubic
  | .inOutCubic => .InOutCubic
  | .inQuart => .InQuart
  | .outQuart => .OutQuart
  | .inOutQuart => .InOutQuart
  | .inQuint => .InQuint
  | .outQuint => .OutQuint
  | .inOutQuint => .InOutQuint
  | .inSine => .InSine
  | .outSine => .OutSine
  | .inOutSine => .InOutSine
  | .inExpo => .InExpo
  | .outExpo => .OutExpo
  | .inOutExpo => .InOutExpo
  | .inCirc => .InCirc
  | .outCirc => .OutCirc
  | .inOutCirc => .InOutCirc
  | .inElastic => .InElastic
  | .outElastic => .OutElastic
  | .outElasticHalf => .OutElasticHalf
  | .outElasticQuarter => .OutElasticQuarter
  | .inOutElastic => .InOutElastic
  | .inBack => .InBack
  | .outBack => .OutBack
  | .inOutBack => .InOutBack
  | .inBounce => .InBounce
  | .outBounce => .OutBounce
  | .inOutBounce => .InOutBounce
  | .outPow10 => .OutPow10
theorem net.framework.easing_of_index_refines (n : U64) :
    net.framework.easing_of_index n = ok (easingI (Easing.ofIndex n.val)) := by
  unfold net.framework.easing_of_index
  split
  all_goals first
    | rfl
    | skip
  simp only [UScalar.eq_equiv_bv_eq, ← BitVec.toNat_inj] at *
  have hv : n.val = n.bv.toNat := rfl
  have : n.val = 0 ∨ 36 ≤ n.val := by simp at *; omega
  rcases this with h | h
  · rw [h]; rfl
  · have : Easing.ofIndex n.val = .none := by
      unfold Easing.ofIndex; rw [List.getD_eq_default]; simp [Easing.all]; omega
    rw [this]; rfl

end OsuProofs
