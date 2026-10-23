/-
Straight-line helpers of `beatmap::mod_random` and `beatmap::mods` point maps (Rust) refining
`OsuModel.Beatmap.Mods.Reposition` / `Mods`.
-/
import OsuProofs.Beatmap.Vector2
import OsuProofs.Beatmap.ControlPoints
import OsuProofs.LoopsR
import OsuProofs.Net.Random
import OsuProofs.Beatmap.DotNet
import OsuProofs.Net.MathOps
set_option linter.unusedSimpArgs false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

theorem beatmap.mod_random.atan2f_refines (y x : F32) :
    beatmap.mod_random.atan2f y x = ok (Mods.Reposition.atan2f y x) := by
  simp [beatmap.mod_random.atan2f, float.F32.atan2, Mods.Reposition.atan2f]

theorem beatmap.mod_random.rotate_vector_refines (vv : net.osutk.Vector2) (rotation : F32) :
    beatmap.mod_random.rotate_vector vv rotation = ok (bv2I (Mods.Reposition.rotateVector (bv2S vv) rotation)) := by
  simp [beatmap.mod_random.rotate_vector, beatmap.mod_random.atan2f_refines, beatmap.vector2.length_refines,
    float.F32.add, float.F32.mul, float.F32.cos, float.F32.sin, Mods.Reposition.rotateVector, bv2I]

/-- The spec map of a Rust `PointMap` (the lambdas passed to `modifySlider`). -/
def pmS : beatmap.mods.PointMap → Vec2 → Vec2
  | .NegX => fun p => ⟨-p.x, p.y⟩
  | .NegY => fun p => ⟨p.x, -p.y⟩
  | .Rotate r => fun p => Mods.Reposition.rotateVector p r

theorem beatmap.mods.apply_point_map_refines (f : beatmap.mods.PointMap) (p : net.osutk.Vector2) :
    beatmap.mods.apply_point_map f p = ok (bv2I (pmS f (bv2S p))) := by
  cases f <;> simp [beatmap.mods.apply_point_map, pmS, float.F32.neg, bv2I,
    beatmap.mod_random.rotate_vector_refines]

theorem scpp_ok (old new : net.osutk.Vector2) :
    beatmap.mods.set_control_point_pos old new = ok (bv2I (Mods.setControlPointPos (bv2S old) (bv2S new))) := by
  unfold beatmap.mods.set_control_point_pos Mods.setControlPointPos
  rw [beatmap.vector2.eq_refines]; simp only [bind_ok]
  split <;> simp

theorem beatmap.mods.new_control_point_pos_refines (p : net.osutk.Vector2) :
    beatmap.mods.new_control_point_pos p = ok (bv2I (Mods.newControlPointPos (bv2S p))) := by
  simp [beatmap.mods.new_control_point_pos, scpp_ok, Mods.newControlPointPos]

instance : Inhabited beatmap.types.PathControlPoint := ⟨{ position := { x := default, y := default }, ptype := none }⟩

/-- One control point of `modifySlider` (Rust side representation). -/
def mcpS (f : beatmap.mods.PointMap) (p : beatmap.types.PathControlPoint) : beatmap.types.PathControlPoint :=
  let c := Mods.newControlPointPos (bv2S p.position)
  { p with position := bv2I (Mods.newControlPointPos (Mods.setControlPointPos c (pmS f c))) }

theorem modify_slider_loop_ok (f : beatmap.mods.PointMap) (old : alloc.vec.Vec beatmap.types.PathControlPoint) :
    ∃ r, beatmap.mods.modify_slider_loop f old (alloc.vec.Vec.with_capacity _ (alloc.vec.Vec.len old)) 0#usize = ok r ∧
      r.val = old.val.map (mcpS f) := by
  have := loop_push_map (fun (x : alloc.vec.Vec beatmap.types.PathControlPoint × Usize) =>
      beatmap.mods.modify_slider_loop.body f old x.1 x.2) old.val.length (fun i => mcpS f old.val[i]!)
    (by
      intro ts i hi hmax
      have hil : i < alloc.vec.Vec.len old := by show i.val < (alloc.vec.Vec.len old).val; simpa using hi
      obtain ⟨w, hw, hwv⟩ := push_eq ts (mcpS f (old.val[i.val]'hi)) (by omega)
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := old.property; omega)
      refine ⟨w, i1, ?_, by rw [hwv, getElem!_pos old.val i.val hi], hi1v⟩
      simp only [beatmap.mods.modify_slider_loop.body, hil, if_true, vec_index_eq old i hi, bind_ok,
        beatmap.mods.new_control_point_pos_refines, beatmap.mods.apply_point_map_refines, scpp_ok, bv2S_I]
      rw [show ({ (old.val[i.val]'hi) with position := bv2I (Mods.newControlPointPos (Mods.setControlPointPos
          (Mods.newControlPointPos (bv2S (old.val[i.val]'hi).position))
          (pmS f (Mods.newControlPointPos (bv2S (old.val[i.val]'hi).position))))) } : beatmap.types.PathControlPoint) =
          mcpS f (old.val[i.val]'hi) from rfl, hw]
      simp [hi1])
    (by
      intro ts i hi
      have hil : ¬ i < alloc.vec.Vec.len old := by show ¬ i.val < (alloc.vec.Vec.len old).val; simp; omega
      simp [beatmap.mods.modify_slider_loop.body, hil])
    (alloc.vec.Vec.with_capacity _ (alloc.vec.Vec.len old)) 0#usize (by simp) (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new])
  obtain ⟨r, hl, hr⟩ := this
  refine ⟨r, by unfold beatmap.mods.modify_slider_loop; exact hl, ?_⟩
  rw [hr]; simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
  apply List.ext_getElem (by simp)
  intro k h1 h2; simp at h2; simp [List.getElem?_eq_getElem h2]

theorem mr_BASE_SIZE : beatmap.mod_random.BASE_SIZE = ok (bv2I Mods.Reposition.BASE_SIZE) := by
  unfold beatmap.mod_random.BASE_SIZE
  simp [float.F32.from_bits, bv2I, Mods.Reposition.BASE_SIZE] <;> decide

theorem beatmap.mod_target_practice.clamp_to_playfield_refines (p : net.osutk.Vector2) (rad : F32) :
    beatmap.mod_target_practice.clamp_to_playfield p rad =
      ok (bv2I (Mods.TargetPractice.clampToPlayfield (bv2S p) rad)) := by
  unfold beatmap.mod_target_practice.clamp_to_playfield Mods.TargetPractice.clampToPlayfield
  simp only [float.F32.lt, float.F32.sub, mr_BASE_SIZE, bind_ok, bv2S_x, bv2S_y, bv2I_x, bv2I_y, decide_eq_true_eq]
  split_ifs <;> simp_all [bv2I] <;> (split_ifs <;> simp_all [bv2I])

theorem beatmap.mod_target_practice.timing_point_index_at_refines (cpi : beatmap.control_points.ControlPointInfo)
    (time : F64) (h : cpi.timing_points.val.length < 2^31) :
    ∃ o, beatmap.mod_target_practice.timing_point_index_at cpi time = ok o ∧
      o.map (·.val) = Mods.TargetPractice.timingPointIndexAt (cpS cpi) time := by
  obtain ⟨o, ho, hov, hob⟩ := beatmap.control_points.binary_search_idx_refines
    beatmap.control_points.TimingPoint.Insts.Osu_eval_coreBeatmapControl_pointsHasTime (·.time) (fun _ => rfl)
    tpS (·.time) (fun _ => rfl) (alloc.vec.Vec.deref cpi.timing_points) time (by simpa [alloc.vec.Vec.deref] using h)
  have hd : (alloc.vec.Vec.deref cpi.timing_points).val = cpi.timing_points.val := by simp [alloc.vec.Vec.deref]
  rw [hd] at hov
  unfold beatmap.mod_target_practice.timing_point_index_at Mods.TargetPractice.timingPointIndexAt
  dsimp only
  rw [ho]; simp only [bind_ok, cpS]; rw [← hov]
  cases o with
  | none =>
    by_cases hz : 0 < cpi.timing_points.val.length
    · have hz' : alloc.vec.Vec.len cpi.timing_points > 0#usize := by show (0#usize).val < _; simpa using hz
      exact ⟨some 0#usize, by simp [hz'], by simp [hz]⟩
    · have hz' : ¬ alloc.vec.Vec.len cpi.timing_points > 0#usize := by show ¬ (0#usize).val < _; simpa using hz
      exact ⟨none, by simp [hz'], by simp [hz]⟩
  | some i => exact ⟨some i, rfl, rfl⟩

theorem mr_two_pi : beatmap.mod_random.two_pi = ok Mods.Reposition.TWO_PI := by
  have h2 : beatmap.mod_random.F2 = ok (2 : F32) := by
    unfold beatmap.mod_random.F2; simp [float.F32.from_bits] <;> decide
  have hp : beatmap.mod_random.PI = ok Mods.Reposition.PI := by
    unfold beatmap.mod_random.PI; simp [float.F32.from_bits, Mods.Reposition.PI]
  simp [beatmap.mod_random.two_pi, h2, hp, float.F32.mul, Mods.Reposition.TWO_PI]

theorem beatmap.mod_random.angle_difference_refines (a1 a2 : F32) :
    beatmap.mod_random.angle_difference a1 a2 = ok (Mods.Reposition.angleDifference a1 a2) := by
  simp [beatmap.mod_random.angle_difference, mr_two_pi, float.F32.sub, float.F32.abs,
    beatmap.dotnet.fmod_f32_refines, net.mathops.f32_min_refines, Mods.Reposition.angleDifference]

theorem beatmap.mod_random.random_gaussian_refines (std_dev : F32) (rng : net.random.State) (hs : stOk rng) :
    ∃ f st', beatmap.mod_random.random_gaussian std_dev rng = ok (f, st') ∧ stOk st' ∧
      (f, stS st') = (Mods.RandomMod.randomGaussian std_dev).run (stS rng) := by
  obtain ⟨a, r1, h1, hs1, he1⟩ := net.random.next_double_refines rng hs
  obtain ⟨b, r2, h2, hs2, he2⟩ := net.random.next_double_refines r1 hs1
  have hd1 : beatmap.mod_random.D1 = ok (1 : F64) := by
    unfold beatmap.mod_random.D1; simp [float.F64.from_bits] <;> decide
  have hd2 : beatmap.mod_random.D2 = ok (2 : F64) := by
    unfold beatmap.mod_random.D2; simp [float.F64.from_bits] <;> decide
  have hpi : beatmap.mod_random.DPI = ok (Float.ofBits 0x400921FB54442D18) := by
    unfold beatmap.mod_random.DPI; simp [float.F64.from_bits]
  have hneg2 : (Float.ofBits 13835058055282163712 : F64) = -2 := by decide
  have hf0 : beatmap.mod_random.F0 = ok (0 : F32) := by
    unfold beatmap.mod_random.F0; simp [float.F32.from_bits] <;> decide
  refine ⟨?f, r2, ?h1, hs2, ?h2⟩
  case h1 =>
    unfold beatmap.mod_random.random_gaussian
    simp [h1, h2, bind_ok, hd1, hd2, hpi, hneg2, hf0, float.F64.sub, float.F64.mul, float.F64.log, float.F64.sqrt,
      float.F64.sin, float.F64.to_f32, float.F32.mul, float.F32.add]
    rfl
  case h2 =>
    simp [Mods.RandomMod.randomGaussian, Mods.RandomMod.nextDouble, ← he1, ← he2]
    rfl

theorem beatmap.mod_random.random_offset_refines (sharpness std_dev : F32) (rng : net.random.State) (hs : stOk rng) :
    ∃ f st', beatmap.mod_random.random_offset sharpness std_dev rng = ok (f, st') ∧ stOk st' ∧
      (f, stS st') = (Mods.RandomMod.randomOffset sharpness std_dev).run (stS rng) := by
  have c1 : (Float32.ofBits 1069547520 : F32) = 1.5 := by decide
  have c2 : (Float32.ofBits 1092616192 : F32) = 10 := by decide
  have c3 : (Float32.ofBits 1088421888 : F32) = 7 := by decide
  unfold beatmap.mod_random.random_offset Mods.RandomMod.randomOffset
  simp only [float.F32.from_bits, float.F32.mul, float.F32.sub, float.F32.div, bind_ok]
  simp only [show (1069547520#u32 : U32).bv.toNat.toUInt32 = 1069547520 from rfl,
    show (1092616192#u32 : U32).bv.toNat.toUInt32 = 1092616192 from rfl,
    show (1088421888#u32 : U32).bv.toNat.toUInt32 = 1088421888 from rfl]
  rw [c1, c2, c3]
  exact beatmap.mod_random.random_gaussian_refines _ rng hs

end OsuProofs
