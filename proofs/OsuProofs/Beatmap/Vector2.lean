/-
`beatmap::vector2` (Rust) refines `OsuModel.Beatmap.Vec2` / `Beatmap.Precision`. The Rust reuses
`net::osutk::Vector2`; the spec has its own (field-identical) `Beatmap.Vec2` (maps `bv2S`/`bv2I`).
-/
import OsuProofs.Net.Random
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

@[simp] theorem bv2S_x (v : net.osutk.Vector2) : (bv2S v).x = v.x := rfl
@[simp] theorem bv2S_y (v : net.osutk.Vector2) : (bv2S v).y = v.y := rfl
@[simp] theorem bv2I_x (v : Vec2) : (bv2I v).x = v.x := rfl
@[simp] theorem bv2I_y (v : Vec2) : (bv2I v).y = v.y := rfl
@[simp] theorem bv2S_mk (a b : F32) : bv2S ⟨a, b⟩ = ⟨a, b⟩ := rfl

@[simp] theorem bm_DOUBLE_EPSILON : beatmap.vector2.DOUBLE_EPSILON = ok Precision.DOUBLE_EPSILON := by
  simp [beatmap.vector2.DOUBLE_EPSILON, Precision.DOUBLE_EPSILON] <;> decide
@[simp] theorem bm_FLOAT_EPSILON : beatmap.vector2.FLOAT_EPSILON = ok Precision.FLOAT_EPSILON := by
  simp [beatmap.vector2.FLOAT_EPSILON, Precision.FLOAT_EPSILON] <;> decide

theorem beatmap.vector2.almost_equals_f64_refines (a b : F64) :
    beatmap.vector2.almost_equals_f64 a b = ok (Precision.almostEqualsF64 a b) := by
  simp [beatmap.vector2.almost_equals_f64, Precision.almostEqualsF64]
theorem beatmap.vector2.almost_equals_f32_refines (a b : F32) :
    beatmap.vector2.almost_equals_f32 a b = ok (Precision.almostEqualsF32 a b) := by
  simp [beatmap.vector2.almost_equals_f32, Precision.almostEqualsF32]
theorem beatmap.vector2.definitely_bigger_f64_refines (a b : F64) :
    beatmap.vector2.definitely_bigger_f64 a b = ok (Precision.definitelyBiggerF64 a b) := by
  simp [beatmap.vector2.definitely_bigger_f64, Precision.definitelyBiggerF64]
theorem beatmap.vector2.normalized_refines (a : net.osutk.Vector2) :
    beatmap.vector2.normalized a = ok (bv2I (Vec2.normalized (bv2S a))) := by
  simp [beatmap.vector2.normalized, net.osutk.v2_normalized_refines, OsuTK.Vector2.normalized, Vec2.normalized,
    OsuTK.Vector2.length, Vec2.length, v2I, bv2I]
theorem beatmap.vector2.length_refines (a : net.osutk.Vector2) :
    beatmap.vector2.length a = ok (Vec2.length (bv2S a)) := by
  simp [beatmap.vector2.length, net.osutk.v2_length_refines, OsuTK.Vector2.length, Vec2.length]
theorem beatmap.vector2.eq_refines (a b : net.osutk.Vector2) :
    beatmap.vector2.eq a b = ok (Vec2.eq (bv2S a) (bv2S b)) := by
  simp [beatmap.vector2.eq, net.osutk.v2_eq_refines, OsuTK.Vector2.eq, Vec2.eq]
theorem beatmap.vector2.scale_refines (a : net.osutk.Vector2) (s : F32) :
    beatmap.vector2.scale a s = ok (bv2I (Vec2.scale (bv2S a) s)) := by
  simp [beatmap.vector2.scale, net.osutk.v2_scale_refines, OsuTK.Vector2.scale, Vec2.scale, v2I, bv2I]
theorem beatmap.vector2.sub_refines (a b : net.osutk.Vector2) :
    beatmap.vector2.sub a b = ok (bv2I (Vec2.sub (bv2S a) (bv2S b))) := by
  simp [beatmap.vector2.sub, net.osutk.v2_sub_refines, OsuTK.Vector2.sub, Vec2.sub, v2I, bv2I]
theorem beatmap.vector2.add_refines (a b : net.osutk.Vector2) :
    beatmap.vector2.add a b = ok (bv2I (Vec2.add (bv2S a) (bv2S b))) := by
  simp [beatmap.vector2.add, net.osutk.v2_add_refines, OsuTK.Vector2.add, Vec2.add, v2I, bv2I]
theorem beatmap.vector2.div_refines (a : net.osutk.Vector2) (s : F32) :
    beatmap.vector2.div a s = ok (bv2I (Vec2.div (bv2S a) s)) := by
  simp [beatmap.vector2.div, net.osutk.v2_div_s_refines, OsuTK.Vector2.divS, Vec2.div, v2I, bv2I]
theorem beatmap.vector2.length_squared_refines (a : net.osutk.Vector2) :
    beatmap.vector2.length_squared a = ok (Vec2.lengthSquared (bv2S a)) := by
  simp [beatmap.vector2.length_squared, net.osutk.v2_length_squared_refines, OsuTK.Vector2.lengthSquared,
    Vec2.lengthSquared]
theorem beatmap.vector2.distance_refines (a b : net.osutk.Vector2) :
    beatmap.vector2.distance a b = ok (Vec2.distance (bv2S a) (bv2S b)) := by
  simp [beatmap.vector2.distance, net.osutk.v2_distance_refines, OsuTK.Vector2.distance, Vec2.distance]
theorem beatmap.vector2.dot_refines (a b : net.osutk.Vector2) :
    beatmap.vector2.dot a b = ok (Vec2.dot (bv2S a) (bv2S b)) := by
  simp [beatmap.vector2.dot, net.osutk.v2_dot_refines, OsuTK.Vector2.dot, Vec2.dot]
theorem beatmap.vector2.splat_refines (v : F32) :
    beatmap.vector2.splat v = ok (bv2I (Vec2.splat v)) := by
  simp [beatmap.vector2.splat, Vec2.splat, bv2I]
theorem beatmap.vector2.distance_fw_refines (a b : net.osutk.Vector2) :
    beatmap.vector2.distance_fw a b = ok (Vec2.distanceFw (bv2S a) (bv2S b)) := by
  simp [beatmap.vector2.distance_fw, net.framework.distance_refines, Framework.Vector2Extensions.distance,
    Vec2.distanceFw]
theorem beatmap.vector2.neg_refines (a : net.osutk.Vector2) :
    beatmap.vector2.neg a = ok (bv2I (Vec2.neg (bv2S a))) := by
  simp [beatmap.vector2.neg, net.osutk.v2_neg_refines, OsuTK.Vector2.neg, Vec2.neg, v2I, bv2I]

@[simp] theorem bm_vector2_ZERO : beatmap.vector2.ZERO = ok (bv2I Vec2.zero) := by
  simp [beatmap.vector2.ZERO, bv2I, Vec2.zero, v2I, OsuTK.Vector2.zero]

end OsuProofs
