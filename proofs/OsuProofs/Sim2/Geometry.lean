/-
`sim::geometry` (Rust) refines `OsuModel.Sim` Geometry (float32 DrawInfo chains, receptor/slider/spinner geometry,
slider path position lookup, follow-area test). Also `sim::basic::apply_transform_r` (needed here; not in the sim
agent's Sim/Basic.lean). Equation-form `@[simp]` lemmas `f args = ok (inv (spec (abs args)))` (inverse maps
`s2_v2R`, `s2_diR`, `s2_sgR`, `s2_spgR`) let `simp` chain the compositions.
-/
import OsuProofs.Sim2.Frames
import OsuProofs.Sim.Basic
import OsuProofs.Sim.Consts
import OsuProofs.Sim.Eqs
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

/-! ## Abstraction maps (geometry) -/
/-- the sim core's `ChainNode` map (Sim/AbsState.lean), named -/
def s2_chainS (n : sim.geometry.ChainNode) : OsuModel.Sim.ChainNode := abs n
@[simp] theorem s2_geo_consts :
    sim.geometry.OBJECT_RADIUS = ok (64 : F32) ∧ sim.geometry.F32_128 = ok (128 : F32) ∧
    sim.geometry.F32_0_5 = ok (0.5 : F32) ∧ sim.geometry.F32_0_8 = ok (0.8 : F32) ∧ sim.geometry.F32_0_2 = ok (0.2 : F32) ∧
    sim.geometry.F64_0 = ok (0 : F64) ∧ sim.geometry.F64_1 = ok (1 : F64) := by
  simp [sim.geometry.OBJECT_RADIUS, sim.geometry.F32_128, sim.geometry.F32_0_5, sim.geometry.F32_0_8,
    sim.geometry.F32_0_2, sim.geometry.F64_0, sim.geometry.F64_1]
  exact ⟨by decide, by decide⟩

/-- `DrawInfo.applyTransformR` with the local `fix` named (`simFixScale`); definitionally the spec. -/
def s2_applyTransformR (di : OsuModel.Sim.DrawInfo) (translation scale : OsuModel.Sim.Vec2) (rotation : F32)
    (origin : OsuModel.Sim.Vec2) : OsuModel.Sim.DrawInfo :=
  if rotation == 0 then simApplyTransform di translation scale origin else Id.run do
  let mut m := di.matrix
  let mut mi := di.inverse
  if !(translation.eq OsuModel.Sim.Vec2.zero) then
    m := m.translateFromLeft translation
    mi := mi.translateFromRight (-translation)
  let rad := SysMisc.F32.degreesToRadians rotation
  m := OsuModel.Sim.DrawInfo.rotL m rad
  mi := OsuModel.Sim.DrawInfo.rotR mi (-rad)
  if !(scale.eq ⟨1, 1⟩) then
    let s : OsuModel.Sim.Vec2 := ⟨simFixScale scale.x, simFixScale scale.y⟩
    m := m.scaleFromLeft s
    mi := mi.scaleFromRight ⟨1 / s.x, 1 / s.y⟩
  if !(origin.eq OsuModel.Sim.Vec2.zero) then
    m := m.translateFromLeft (-origin)
    mi := mi.translateFromRight origin
  return ⟨m, mi⟩
theorem s2_applyTransformR_eq (di : OsuModel.Sim.DrawInfo) (t s : OsuModel.Sim.Vec2) (r : F32) (o : OsuModel.Sim.Vec2) :
    OsuModel.Sim.DrawInfo.applyTransformR di t s r o = s2_applyTransformR di t s r o := rfl

set_option maxHeartbeats 2000000 in
theorem sim.basic.apply_transform_r_refines (d : sim.basic.DrawInfo) (tr sc : sim.basic.Vec2) (rot : F32) (o : sim.basic.Vec2) :
    ∃ r, sim.basic.apply_transform_r d tr sc rot o = ok r ∧
      OsuModel.Sim.DrawInfo.applyTransformR (abs d) (abs tr) (abs sc) (abs rot) (abs o) = abs r := by
  rw [s2_applyTransformR_eq]
  by_cases h0 : (rot == 0) = true
  · obtain ⟨r, hr, er⟩ := sim.basic.apply_transform_refines d tr sc o
    refine ⟨r, ?_, ?_⟩
    · simp [sim.basic.apply_transform_r, float.F32.eq, h0, hr]
    · simp only [s2_applyTransformR, abs, id] at er ⊢; rw [if_pos h0, ← simApplyTransform_eq]; exact er
  · have h0' : (rot == 0) = false := by simpa using h0
    obtain ⟨fx, hfx, efx⟩ := sim.basic.fix_scale_refines sc.x
    obtain ⟨fy, hfy, efy⟩ := sim.basic.fix_scale_refines sc.y
    simp only [abs, id] at efx efy
    simp only [sim.basic.apply_transform_r, s2_applyTransformR, hfx, hfy, h0', float.F32.eq, sim_basic_F32_0,
      Bool.false_eq_true, ite_false, bind_ok, net.sysmisc.f32_degrees_to_radians_refines, abs, id]
    cases e1 : (tr.x == 0) <;> cases e2 : (tr.y == 0) <;> cases e3 : (sc.x == 1) <;> cases e4 : (sc.y == 1) <;>
    cases e5 : (o.x == 0) <;> cases e6 : (o.y == 0) <;>
    simp [e1, e2, e3, e4, e5, e6, efx, efy, sim.basic.Vec2.eq, sim.basic.Vec2.neg, sim.basic.translate_from_left,
      sim.basic.translate_from_right, sim.basic.scale_from_left, sim.basic.scale_from_right, OsuModel.Sim.Vec2.eq,
      OsuModel.Sim.Vec2.zero, OsuModel.Sim.Vec2.neg, OsuModel.Sim.Mat3.translateFromLeft,
      OsuModel.Sim.Mat3.translateFromRight, OsuModel.Sim.Mat3.scaleFromLeft, OsuModel.Sim.Mat3.scaleFromRight,
      sim.basic.rot_l, sim.basic.rot_r, OsuModel.Sim.DrawInfo.rotL, OsuModel.Sim.DrawInfo.rotR, float.F32.neg,
      Neg.neg] <;> rfl

theorem sim.geometry.centre_of_refines (size : sim.basic.Vec2) :
    ∃ r, sim.geometry.centre_of size = ok r ∧ OsuModel.Sim.centreOf (abs size) = abs r := by
  simp [sim.geometry.centre_of, OsuModel.Sim.centreOf, abs]

theorem sim.geometry.child_draw_info_refines (parent : sim.basic.DrawInfo) (dp ap sc o : sim.basic.Vec2) :
    ∃ r, sim.geometry.child_draw_info parent dp ap sc o = ok r ∧
      OsuModel.Sim.childDrawInfo (abs parent) (abs dp) (abs ap) (abs sc) (abs o) = abs r := by
  obtain ⟨r, hr, er⟩ := sim.basic.apply_transform_refines parent ⟨dp.x + ap.x + 0, dp.y + ap.y + 0⟩ sc ⟨o.x - 0, o.y - 0⟩
  refine ⟨r, ?_, ?_⟩
  · simp [sim.geometry.child_draw_info, sim.basic.Vec2.add, sim.basic.Vec2.sub, hr]
  · rw [← er]; rfl

theorem sim.geometry.child_draw_info_r_refines (parent : sim.basic.DrawInfo) (dp ap sc : sim.basic.Vec2) (rot : F32)
    (o : sim.basic.Vec2) :
    ∃ r, sim.geometry.child_draw_info_r parent dp ap sc rot o = ok r ∧
      OsuModel.Sim.childDrawInfoR (abs parent) (abs dp) (abs ap) (abs sc) (abs rot) (abs o) = abs r := by
  obtain ⟨r, hr, er⟩ := sim.basic.apply_transform_r_refines parent ⟨dp.x + ap.x + 0, dp.y + ap.y + 0⟩ sc rot ⟨o.x - 0, o.y - 0⟩
  refine ⟨r, ?_, ?_⟩
  · simp [sim.geometry.child_draw_info_r, sim.basic.Vec2.add, sim.basic.Vec2.sub, hr]
  · rw [← er]; rfl

/-! Inverse maps (spec ↦ Rust) for the geometry records, so that refinement lemmas can be stated as
equations `f args = ok (inv (spec (abs args)))` that `simp` chains through compositions. -/
def s2_v2R (v : OsuModel.Sim.Vec2) : sim.basic.Vec2 := ⟨v.x, v.y⟩
def s2_m3R (m : OsuModel.Sim.Mat3) : sim.basic.Mat3 := ⟨m.m11, m.m12, m.m13, m.m21, m.m22, m.m23, m.m31, m.m32, m.m33⟩
def s2_diR (d : OsuModel.Sim.DrawInfo) : sim.basic.DrawInfo := ⟨s2_m3R d.matrix, s2_m3R d.inverse⟩
@[simp] theorem s2_abs_v2R (v : OsuModel.Sim.Vec2) : (abs (s2_v2R v) : OsuModel.Sim.Vec2) = v := rfl
@[simp] theorem s2_abs_diR (d : OsuModel.Sim.DrawInfo) : (abs (s2_diR d) : OsuModel.Sim.DrawInfo) = d := rfl
@[simp] theorem s2_diR_abs (d : sim.basic.DrawInfo) : s2_diR (abs d) = d := rfl
@[simp] theorem s2_abs_v2mk (a b : F32) : (abs (⟨a, b⟩ : sim.basic.Vec2) : OsuModel.Sim.Vec2) = ⟨a, b⟩ := rfl
@[simp] theorem s2_v2R_abs (v : sim.basic.Vec2) : s2_v2R (abs v) = v := rfl

theorem s2_eq_of_ex {α β : Type} [AbsTo α β] {m : Result α} {spec : β} (inv : β → α) (hinv : ∀ a : α, inv (abs a) = a)
    (h : ∃ r, m = ok r ∧ spec = abs r) : m = ok (inv spec) := by
  obtain ⟨r, hr, e⟩ := h; rw [hr, e, hinv]

@[simp] theorem s2_child_draw_info_eq (parent : sim.basic.DrawInfo) (dp ap sc o : sim.basic.Vec2) :
    sim.geometry.child_draw_info parent dp ap sc o =
      ok (s2_diR (OsuModel.Sim.childDrawInfo (abs parent) (abs dp) (abs ap) (abs sc) (abs o))) :=
  s2_eq_of_ex s2_diR (fun _ => rfl) (sim.geometry.child_draw_info_refines parent dp ap sc o)
@[simp] theorem s2_child_draw_info_r_eq (parent : sim.basic.DrawInfo) (dp ap sc : sim.basic.Vec2) (rot : F32) (o : sim.basic.Vec2) :
    sim.geometry.child_draw_info_r parent dp ap sc rot o =
      ok (s2_diR (OsuModel.Sim.childDrawInfoR (abs parent) (abs dp) (abs ap) (abs sc) (abs rot) (abs o))) :=
  s2_eq_of_ex s2_diR (fun _ => rfl) (sim.geometry.child_draw_info_r_refines parent dp ap sc rot o)
@[simp] theorem s2_centre_of_eq (size : sim.basic.Vec2) :
    sim.geometry.centre_of size = ok (s2_v2R (OsuModel.Sim.centreOf (abs size))) :=
  s2_eq_of_ex s2_v2R (fun _ => rfl) (sim.geometry.centre_of_refines size)
@[simp] theorem s2_obj_dims : sim.geometry.OBJECT_DIMENSIONS = ok ⟨128, 128⟩ := by
  simp [sim.geometry.OBJECT_DIMENSIONS]
@[simp] theorem s2_vec2_half : sim.geometry.VEC2_HALF = ok ⟨0.5, 0.5⟩ := by
  simp [sim.geometry.VEC2_HALF]

theorem sim.geometry.receptor_from_dho_refines (parent : sim.basic.DrawInfo) (dho_pos dho_anchor : sim.basic.Vec2) (scale : F32) :
    ∃ r, sim.geometry.receptor_from_dho parent dho_pos dho_anchor scale = ok r ∧
      OsuModel.Sim.receptorFromDho (abs parent) (abs dho_pos) (abs dho_anchor) (abs scale) = abs r := by
  refine ⟨s2_diR (OsuModel.Sim.receptorFromDho (abs parent) (abs dho_pos) (abs dho_anchor) (abs scale)), ?_, by simp⟩
  simp [sim.geometry.receptor_from_dho, sim.basic.Vec2.mul, float.F32.mul, OsuModel.Sim.receptorFromDho,
    OsuModel.Sim.objectDimensions, OsuModel.Sim.centreOf, OsuModel.Sim.Vec2.mul, s2_v2R, OsuModel.Sim.Vec2.zero]

def s2_sgR (g : OsuModel.Sim.SliderGeom) : sim.geometry.SliderGeom :=
  ⟨g.pathRadius, s2_v2R g.size, s2_v2R g.origin, s2_diR g.drawInfo, s2_diR g.headReceptor⟩
def s2_spgR (g : OsuModel.Sim.SpinnerGeom) : sim.geometry.SpinnerGeom := ⟨s2_diR g.aspect, s2_v2R g.trackerSize⟩
@[simp] theorem s2_abs_sgR (g : OsuModel.Sim.SliderGeom) : (abs (s2_sgR g) : OsuModel.Sim.SliderGeom) = g := rfl
@[simp] theorem s2_abs_spgR (g : OsuModel.Sim.SpinnerGeom) : (abs (s2_spgR g) : OsuModel.Sim.SpinnerGeom) = g := rfl

@[simp] theorem s2_receptor_from_dho_eq (parent : sim.basic.DrawInfo) (dho_pos dho_anchor : sim.basic.Vec2) (scale : F32) :
    sim.geometry.receptor_from_dho parent dho_pos dho_anchor scale =
      ok (s2_diR (OsuModel.Sim.receptorFromDho (abs parent) (abs dho_pos) (abs dho_anchor) (abs scale))) :=
  s2_eq_of_ex s2_diR (fun _ => rfl) (sim.geometry.receptor_from_dho_refines parent dho_pos dho_anchor scale)

theorem sim.geometry.circle_receptor_refines (env : sim.geometry.Env) (h : sim.playable.HObj) :
    ∃ r, sim.geometry.circle_receptor env h = ok r ∧ OsuModel.Sim.circleReceptor (abs env) (abs h) = abs r := by
  refine ⟨s2_diR (OsuModel.Sim.circleReceptor (abs env) (abs h)), ?_, by simp⟩
  simp [sim.geometry.circle_receptor, OsuModel.Sim.circleReceptor, OsuModel.Sim.Vec2.zero]; rfl

theorem sim.geometry.receptor_from_placement_refines (parent : sim.basic.DrawInfo) (pl : sim.geometry.Placement)
    (dho_anchor : sim.basic.Vec2) (scale : F32) :
    ∃ r, sim.geometry.receptor_from_placement parent pl dho_anchor scale = ok r ∧
      OsuModel.Sim.receptorFromPlacement (abs parent) (abs pl) (abs dho_anchor) (abs scale) = abs r := by
  refine ⟨s2_diR (OsuModel.Sim.receptorFromPlacement (abs parent) (abs pl) (abs dho_anchor) (abs scale)), ?_, by simp⟩
  simp [sim.geometry.receptor_from_placement, sim.basic.Vec2.mul, float.F32.mul, OsuModel.Sim.receptorFromPlacement,
    OsuModel.Sim.objectDimensions, OsuModel.Sim.centreOf, OsuModel.Sim.Vec2.mul, s2_v2R, OsuModel.Sim.Vec2.zero]
  rfl

@[simp] theorem s2_receptor_from_placement_eq (parent : sim.basic.DrawInfo) (pl : sim.geometry.Placement)
    (dho_anchor : sim.basic.Vec2) (scale : F32) :
    sim.geometry.receptor_from_placement parent pl dho_anchor scale =
      ok (s2_diR (OsuModel.Sim.receptorFromPlacement (abs parent) (abs pl) (abs dho_anchor) (abs scale))) :=
  s2_eq_of_ex s2_diR (fun _ => rfl) (sim.geometry.receptor_from_placement_refines parent pl dho_anchor scale)

theorem sim.geometry.slider_geom_p_refines (hoc : sim.basic.DrawInfo) (apr : F32) (h : sim.playable.HObj)
    (pl : sim.geometry.Placement) (size origin rel : sim.basic.Vec2) (headPl : sim.geometry.Placement) (env : sim.geometry.Env)
    (henv : env.hoc = hoc ∧ env.argon_path_radius = apr) :
    ∃ r, sim.geometry.slider_geom_p hoc apr h pl size origin rel headPl = ok r ∧
      OsuModel.Sim.sliderGeomP (abs env) (abs h) (abs pl) (abs size) (abs origin) (abs rel) (abs headPl) = abs r := by
  obtain ⟨h1, h2⟩ := henv; subst h1 h2
  refine ⟨s2_sgR (OsuModel.Sim.sliderGeomP (abs env) (abs h) (abs pl) (abs size) (abs origin) (abs rel) (abs headPl)), ?_, by simp⟩
  simp [sim.geometry.slider_geom_p, sim.basic.Vec2.mul, float.F32.mul, OsuModel.Sim.sliderGeomP, s2_sgR, s2_v2R,
    OsuModel.Sim.Vec2.zero, OsuModel.Sim.Vec2.mul]
  repeat' constructor

theorem sim.geometry.spinner_geom_p_refines (hoc : sim.basic.DrawInfo) (hoc_size : sim.basic.Vec2) (pl : sim.geometry.Placement)
    (env : sim.geometry.Env) (henv : env.hoc = hoc ∧ env.hoc_size = hoc_size) :
    ∃ r, sim.geometry.spinner_geom_p hoc hoc_size pl = ok r ∧ OsuModel.Sim.spinnerGeomP (abs env) (abs pl) = abs r := by
  obtain ⟨h1, h2⟩ := henv; subst h1 h2
  refine ⟨s2_spgR (OsuModel.Sim.spinnerGeomP (abs env) (abs pl)), ?_, by simp⟩
  simp [sim.geometry.spinner_geom_p, sim.basic.Vec2.mul, float.F32.mul, float.F32.div, OsuModel.Sim.spinnerGeomP,
    s2_spgR, s2_v2R, OsuModel.Sim.Vec2.zero, OsuModel.Sim.Vec2.mul, OsuModel.Sim.centreOf]
  repeat' constructor

theorem sim.geometry.radians_to_degrees_refines (x : F32) :
    ∃ r, sim.geometry.radians_to_degrees x = ok r ∧ OsuModel.Sim.radiansToDegrees (abs x) = abs r := by
  simp [sim.geometry.radians_to_degrees, OsuModel.Sim.radiansToDegrees, sim.geometry.F32_180, sim.geometry.F32_PI,
    float.F32.mul, float.F32.div, OsuModel.Sim.f32_180]
  rw [show (18e1 : F32) = 180 by decide +kernel]

theorem sim.geometry.follow_radius_refines (h : sim.playable.HObj) (expanded : Bool) :
    ∃ r, sim.geometry.follow_radius h expanded = ok r ∧ OsuModel.Sim.followRadius (abs h) (abs expanded) = abs r := by
  cases expanded <;> simp [sim.geometry.follow_radius, OsuModel.Sim.followRadius, sim.geometry.F32_2_4, float.F64.to_f32,
    float.F32.mul, OsuModel.Sim.f32_2_4, abs, hobjS]

theorem sim.geometry.mouse_in_slider_refines (g : sim.geometry.SliderGeom) (screen : sim.basic.Vec2) :
    ∃ r, sim.geometry.mouse_in_slider g screen = ok r ∧ OsuModel.Sim.mouseInSlider (abs g) (abs screen) = abs r := by
  simp [sim.geometry.mouse_in_slider, OsuModel.Sim.mouseInSlider, sim.basic.to_local, sim.basic.mat3_transform,
    OsuModel.Sim.DrawInfo.toLocal, OsuModel.Sim.Mat3.transform, sim.basic.Vec2.sub, abs]
  rfl

theorem sim.geometry.compare_d_refines (a b : F64) :
    ∃ r, sim.geometry.compare_d a b = ok r ∧ OsuModel.Sim.compareD (abs a) (abs b) = abs r := by
  unfold sim.geometry.compare_d OsuModel.Sim.compareD
  by_cases h1 : a < b
  · simp [float.F64.lt, h1, abs]
  · by_cases h2 : b < a
    · simp [float.F64.lt, h1, h2, abs]
    · by_cases h3 : (a == b) = true
      · simp [float.F64.lt, float.F64.eq, h1, h2, h3, abs]
      · cases ha : a.isNaN <;> cases hb : b.isNaN <;> simp [float.F64.lt, float.F64.eq, float.F64.is_nan, h1, h2, h3, ha, hb, abs]

theorem sim.geometry.span_at_refines (sd : sim.playable.SliderData) (progress : F64) :
    ∃ r, sim.geometry.span_at sd progress = ok r ∧ OsuModel.Sim.SliderData.spanAt (abs sd) (abs progress) = abs r := by
  simp [sim.geometry.span_at, OsuModel.Sim.SliderData.spanAt, float.F64.from_u64, float.F64.mul, float.F64.to_i32_sat, abs, i32S]

theorem sim.geometry.spinner_geom_refines (env : sim.geometry.Env) (h : sim.playable.HObj) :
    ∃ r, sim.geometry.spinner_geom env h = ok r ∧ OsuModel.Sim.spinnerGeom (abs env) (abs h) = abs r := by
  obtain ⟨r, hr, er⟩ := sim.geometry.spinner_geom_p_refines env.hoc env.hoc_size ⟨h.pos, ⟨1, 1⟩, 0⟩ env ⟨rfl, rfl⟩
  refine ⟨r, ?_, ?_⟩
  · simp [sim.geometry.spinner_geom, hr]
  · rw [← er]; rfl

theorem sim.geometry.distance_refines (sd : sim.playable.SliderData) :
    ∃ r, sim.geometry.distance sd = ok r ∧ OsuModel.Sim.SliderData.distance (abs sd) = abs r := by
  unfold sim.geometry.distance OsuModel.Sim.SliderData.distance
  by_cases h : sd.cum_len.val.length = 0
  · have h' : ¬ (alloc.vec.Vec.len sd.cum_len > 0#usize) := by scalar_tac
    have e : sd.cum_len.val = [] := List.eq_nil_of_length_eq_zero h
    simp [h', abs, e, Array.back?]
  · have h' : alloc.vec.Vec.len sd.cum_len > 0#usize := by scalar_tac
    obtain ⟨m, hm, hmv⟩ := usize_sub_one (alloc.vec.Vec.len sd.cum_len) (by simp; omega)
    have hml : m.val < sd.cum_len.val.length := by simp at hmv; omega
    simp [h', hm, vec_index_usize_ok _ _ hml, abs, Array.back?]
    simp at hmv
    simp [hmv, List.getElem?_eq_getElem (by omega : sd.cum_len.val.length - 1 < sd.cum_len.val.length)]

theorem s2_tmod2 (x : Int) : (x.tmod 2 ≠ 0) ↔ (x % 2 = 1) := by
  have h1 : x.tmod 2 = 0 ↔ (2 : Int) ∣ x := (Int.dvd_iff_tmod_eq_zero).symm
  have h2 : (2 : Int) ∣ x ↔ x % 2 = 0 := Int.dvd_iff_emod_eq_zero
  rw [ne_eq, h1, h2]; omega

theorem sim.geometry.progress_at_refines (sd : sim.playable.SliderData) (progress : F64) :
    ∃ r, sim.geometry.progress_at sd progress = ok r ∧ OsuModel.Sim.SliderData.progressAt (abs sd) (abs progress) = abs r := by
  obtain ⟨p, hp, ep⟩ := sim.basic.fmod1_refines (progress * F64.ofInt sd.span_count.val)
  obtain ⟨sp, hsp, esp⟩ := sim.geometry.span_at_refines sd progress
  have hm := IScalar.rem_spec sp (y := 2#i32) (by simp)
  obtain ⟨m, hm1, hm2⟩ := eq_ok_of_spec hm
  unfold sim.geometry.progress_at OsuModel.Sim.SliderData.progressAt
  simp only [float.F64.from_u64, float.F64.mul, hp, hsp, hm1, bind_ok]
  simp only [abs, id] at ep esp ⊢
  rw [esp]
  have key : (m != 0#i32) = ((i32S sp).toInt % 2 == 1) := by
    rw [i32S_toInt, Bool.eq_iff_iff]
    simp only [bne_iff_ne, ne_eq, beq_iff_eq]
    have hm2' : m.val = sp.val.tmod 2 := by rw [hm2]; rfl
    rw [← s2_tmod2, ← hm2']
    constructor
    · intro h h'; apply h; exact IScalar.eq_of_val_eq (by simp [h'])
    · intro h h'; apply h; rw [h']; simp
  rw [key, ← ep]
  cases ((i32S sp).toInt % 2 == 1) <;> simp [sim.geometry.F64_1, float.F64.sub]

theorem sim.geometry.receptor_effective_corner_radius_refines :
    sim.geometry.receptor_effective_corner_radius = ok OsuModel.Sim.receptorEffectiveCornerRadius := by
  simp [sim.geometry.receptor_effective_corner_radius, OsuModel.Sim.receptorEffectiveCornerRadius,
    sim.geometry.RECEPTOR_CORNER_EXPONENT, OsuModel.Sim.receptorCornerExponent, OsuModel.Sim.objectRadius,
    float.F32.mul, float.F32.div, float.F32.add]
attribute [simp] sim.geometry.receptor_effective_corner_radius_refines

theorem sim.geometry.receptor_corner_radius_pow_refines :
    sim.geometry.receptor_corner_radius_pow = ok OsuModel.Sim.receptorCornerRadiusPow := by
  simp [sim.geometry.receptor_corner_radius_pow, OsuModel.Sim.receptorCornerRadiusPow,
    sim.geometry.RECEPTOR_CORNER_EXPONENT, OsuModel.Sim.receptorCornerExponent, float.F32.to_f64, float.F64.pow]
attribute [simp] sim.geometry.receptor_corner_radius_pow_refines

/-- `corner_pow` is the run's `Ctx.corner_pow` = `receptorCornerRadiusPow` (computed once by `receptor_corner_radius_pow`). -/
theorem sim.geometry.receptor_contains_refines (di : sim.basic.DrawInfo) (screen : sim.basic.Vec2) (corner_pow : F64)
    (hc : corner_pow = OsuModel.Sim.receptorCornerRadiusPow) :
    ∃ r, sim.geometry.receptor_contains di screen corner_pow = ok r ∧
      OsuModel.Sim.receptorContains (abs di) (abs screen) = abs r := by
  subst hc
  unfold sim.geometry.receptor_contains OsuModel.Sim.receptorContains
  simp only [sim.geometry.RECEPTOR_CORNER_EXPONENT, sim_basic_F32_2, sim.geometry.receptor_effective_corner_radius_refines,
    sim_basic_F32_0, float.F32.eq, bind_ok, OsuModel.Sim.f32zero, OsuModel.Sim.f32_128]
  by_cases h0 : (OsuModel.Sim.receptorEffectiveCornerRadius == 0) = true
  · simp only [h0, ite_true]
    simp [sim.basic.to_local, sim.basic.mat3_transform, OsuModel.Sim.DrawInfo.toLocal, OsuModel.Sim.Mat3.transform,
      abs, float.F32.le, s2_geo_consts]
    simp only [Bool.and_assoc]; rfl
  · simp only [h0, ite_false, Bool.false_eq_true]
    simp [sim.basic.to_local, sim.basic.mat3_transform, OsuModel.Sim.DrawInfo.toLocal, OsuModel.Sim.Mat3.transform,
      abs, float.F32.le, float.F32.neg, float.F32.sub, float.F32.add, float.F32.pow, float.F32.to_f64, float.F64.le,
      sim.netx.f32_max_refines, OsuModel.Sim.receptorCornerExponent]
    rfl

@[simp] theorem s2_apply_transform_r_eq (d : sim.basic.DrawInfo) (tr sc : sim.basic.Vec2) (rot : F32) (o : sim.basic.Vec2) :
    sim.basic.apply_transform_r d tr sc rot o =
      ok (s2_diR (OsuModel.Sim.DrawInfo.applyTransformR (abs d) (abs tr) (abs sc) (abs rot) (abs o))) :=
  s2_eq_of_ex s2_diR (fun _ => rfl) (sim.basic.apply_transform_r_refines d tr sc rot o)

/-- one `composeChain` step (spec) -/
def s2_ccStep (prs : Option (F32 × OsuModel.Sim.Vec2)) (di : OsuModel.Sim.DrawInfo) (n : OsuModel.Sim.ChainNode) :
    OsuModel.Sim.DrawInfo :=
  let (rot, sc) := match prs with
    | some (r, s) => if n.typeName == "OsuPlayfieldAdjustmentContainer" then (r, s) else (n.rot, n.scale)
    | none => (n.rot, n.scale)
  di.applyTransformR n.pos sc rot n.origin

theorem s2_composeChain_eq (nodes : _root_.Array OsuModel.Sim.ChainNode) (prs : Option (F32 × OsuModel.Sim.Vec2)) :
    OsuModel.Sim.composeChain nodes prs = nodes.foldl (s2_ccStep prs) ⟨OsuModel.Sim.Mat3.identity, OsuModel.Sim.Mat3.identity⟩ := by
  unfold OsuModel.Sim.composeChain
  simp only [Id.run]
  rw [Array.forIn_pure_yield_eq_foldl]; rfl

theorem s2_pac_ne : ("OsuPlayfieldAdjustmentContainer" == "") = false := by decide

theorem sim.geometry.compose_chain_refines (nodes : Slice sim.geometry.ChainNode) (prs : Option (F32 × sim.basic.Vec2)) :
    ∃ r, sim.geometry.compose_chain nodes prs = ok r ∧
      OsuModel.Sim.composeChain (abs nodes) (abs prs) = abs r := by
  have hmax := nodes.property
  let prsS : Option (F32 × OsuModel.Sim.Vec2) := abs prs
  obtain ⟨y, hl, hv⟩ := loop_fold_gen' (fun x => sim.geometry.compose_chain_loop.body nodes x.1 x.2.1 x.2.2) (·.2.2)
    nodes.val.length (by omega)
    (fun t => t.1 = prs) (fun t => (abs t.2.1 : OsuModel.Sim.DrawInfo))
    (fun k d => s2_ccStep prsS d ((nodes.val.map s2_chainS)[k]!)) (fun y d => (abs y : OsuModel.Sim.DrawInfo) = d)
    (by
      intro t hI hlt j1 hj1 hj1v
      obtain ⟨p, d, i⟩ := t
      simp only at hI hlt hj1 hj1v ⊢; subst hI
      have hlt' : i < Slice.len nodes := by rw [slice_lt_len_iff]; exact hlt
      refine ⟨(p, s2_diR (s2_ccStep (abs p) (abs d) (s2_chainS (nodes.val[i.val]'hlt))), j1), ?_, rfl, ?_, rfl⟩
      · cases p with
        | none => simp [sim.geometry.compose_chain_loop.body, hlt', slice_index_ok _ _ hlt, hj1]; rfl
        | some q =>
          obtain ⟨qr, qs⟩ := q
          cases hp : (nodes.val[i.val]'hlt).is_pac <;>
            simp [sim.geometry.compose_chain_loop.body, hlt', slice_index_ok _ _ hlt, hj1, hp, s2_ccStep, s2_chainS, abs, simPacName,
              s2_pac_ne] <;> rfl
      · simp [s2_getElem!_map _ _ _ hlt, prsS])
    (by
      intro t hI hge
      obtain ⟨p, d, i⟩ := t
      refine ⟨d, ?_, rfl⟩
      simp [sim.geometry.compose_chain_loop.body, slice_lt_len_iff, Nat.not_lt.mpr hge])
    (prs, ⟨⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩⟩, 0#usize) rfl (by simp)
  refine ⟨y, ?_, ?_⟩
  · unfold sim.geometry.compose_chain; simp only [sim_basic_MAT3_IDENTITY, bind_ok]
    unfold sim.geometry.compose_chain_loop; exact hl
  · have ea : (abs nodes : _root_.Array OsuModel.Sim.ChainNode) = (nodes.val.map s2_chainS).toArray := rfl
    rw [hv, s2_composeChain_eq, ea, List.foldl_toArray' (h := rfl), foldl_iterR]
    simp [prsS]; rfl

/-- one step of the path-bounds loop of `sliderGeom`/`bodyRefresh` -/
def s2_bstep (r : F32) (s : F32 × F32 × F32 × F32) (v : OsuModel.Sim.Vec2) : F32 × F32 × F32 × F32 :=
  (F32.min s.1 (v.x - r), F32.min s.2.1 (v.y - r), F32.max s.2.2.1 (v.x + r), F32.max s.2.2.2 (v.y + r))
def s2_bS (b : sim.geometry.Bounds) : F32 × F32 × F32 × F32 := (b.min_x, b.min_y, b.max_x, b.max_y)

theorem sim.geometry.path_bounds_refines (path : Slice sim.basic.Vec2) (r : F32) :
    ∃ b, sim.geometry.path_bounds path r = ok b ∧
      (abs path : _root_.Array OsuModel.Sim.Vec2).foldl (s2_bstep r) (0, 0, 0, 0) = s2_bS b := by
  have hmax := path.property
  obtain ⟨y, hl, hv⟩ := loop_fold_gen' (fun x => sim.geometry.path_bounds_loop.body path r x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (·.2.2.2.2) path.val.length (by omega)
    (fun _ => True) (fun t => (t.1, t.2.1, t.2.2.1, t.2.2.2.1))
    (fun k s => s2_bstep r s ((path.val.map (fun v => (abs v : OsuModel.Sim.Vec2)))[k]!)) (fun y s => y = s)
    (by
      intro t _ hlt j1 hj1 hj1v
      obtain ⟨a, b, c, d, i⟩ := t
      simp only at hlt hj1 hj1v ⊢
      have hlt' : i < Slice.len path := by rw [slice_lt_len_iff]; exact hlt
      refine ⟨_, by simp [sim.geometry.path_bounds_loop.body, hlt', slice_index_ok _ _ hlt, hj1, float.F32.sub,
        float.F32.add, sim.netx.f32_min_refines, sim.netx.f32_max_refines]; rfl, rfl, ?_, trivial⟩
      simp [s2_bstep, s2_getElem!_map _ _ _ hlt, abs])
    (by
      intro t _ hge
      obtain ⟨a, b, c, d, i⟩ := t
      refine ⟨(a, b, c, d), ?_, rfl⟩
      simp [sim.geometry.path_bounds_loop.body, slice_lt_len_iff, Nat.not_lt.mpr hge])
    (0, 0, 0, 0, 0#usize) trivial (by simp)
  obtain ⟨a, b, c, d⟩ := y
  refine ⟨⟨a, b, c, d⟩, ?_, ?_⟩
  · unfold sim.geometry.path_bounds; simp only [sim_basic_F32_0, bind_ok]
    unfold sim.geometry.path_bounds_loop at *
    rw [hl]; simp
  · have ea : (abs path : _root_.Array OsuModel.Sim.Vec2) = (path.val.map (fun v => (abs v : OsuModel.Sim.Vec2))).toArray := rfl
    rw [ea, List.foldl_toArray' (h := rfl), foldl_iterR]
    simp only [s2_bS]; rw [hv]; simp

theorem s2_bodyRefresh_eq (sd : OsuModel.Sim.SliderData) (r : F32) :
    OsuModel.Sim.bodyRefresh sd r =
      (let b := sd.path.foldl (s2_bstep r) (0, 0, 0, 0)
       let size : OsuModel.Sim.Vec2 := if sd.path.size > 0 then ⟨b.2.2.1 - b.1, b.2.2.2 - b.2.1⟩ else OsuModel.Sim.Vec2.zero
       let tl : OsuModel.Sim.Vec2 := if sd.path.size > 0 then ⟨b.1, b.2.1⟩ else OsuModel.Sim.Vec2.zero
       match sd.path[0]? with
       | some v0 => pure (size, v0 - tl)
       | none => throw OsuModel.Sim.emptyPathMsg) := by
  unfold OsuModel.Sim.bodyRefresh
  dsimp only
  rw [Array.forIn_pure_yield_eq_foldl]
  simp only [pure_bind]
  cases sd.path[0]? <;> rfl

theorem sim.geometry.body_refresh_refines (sd : sim.playable.SliderData) (r : F32) :
    ∃ x, sim.geometry.body_refresh sd r = ok x ∧ s2_rel abs (OsuModel.Sim.bodyRefresh (abs sd) r) x := by
  obtain ⟨b, hb, eb⟩ := sim.geometry.path_bounds_refines (alloc.vec.Vec.deref sd.path) r
  have ep : (abs sd : OsuModel.Sim.SliderData).path = (abs (alloc.vec.Vec.deref sd.path) : _root_.Array OsuModel.Sim.Vec2) := by
    simp [abs, alloc.vec.Vec.deref]
  rw [s2_bodyRefresh_eq, ep, eb]
  unfold sim.geometry.body_refresh
  simp only [hb, bind_ok]
  by_cases h0 : sd.path.val.length = 0
  · have h1 : ¬ (alloc.vec.Vec.len sd.path > 0#usize) := by scalar_tac
    have h2 : alloc.vec.Vec.len sd.path = 0#usize := by scalar_tac
    have e : sd.path.val = [] := List.eq_nil_of_length_eq_zero h0
    refine ⟨.Err sim.err.SimErr.EmptyPath, by simp [h1, h2], ?_⟩
    simp [s2_rel, abs, alloc.vec.Vec.deref, e, throw, throwThe, MonadExceptOf.throw]
  · have h1 : alloc.vec.Vec.len sd.path > 0#usize := by scalar_tac
    have h2 : ¬ (alloc.vec.Vec.len sd.path = 0#usize) := by scalar_tac
    have hp : 0 < sd.path.val.length := by omega
    refine ⟨_, by simp [h1, h2, float.F32.sub, vec_index_usize_ok _ _ (show (0#usize).val < sd.path.val.length by simpa using hp),
      sim.basic.Vec2.sub]; rfl, ?_⟩
    simp [s2_rel, abs, alloc.vec.Vec.deref, List.getElem?_eq_getElem hp, s2_bS, pure, Except.pure, hp,
      OsuModel.Sim.Vec2.sub]
    rfl

theorem s2_i64_neg (x : I64) (h : 0 ≤ x.val) : ∃ n : I64, (-. x) = ok n ∧ n.val = -x.val := by
  have hne : x ≠ IScalar.min .I64 := by
    intro e; simp [IScalar.min, I64.min] at e; scalar_tac
  obtain ⟨n, hn, hv⟩ := eq_ok_of_spec (HNeg.hNeg.step x hne)
  exact ⟨n, hn, by simpa using hv⟩

theorem s2_bsearch_loop (h64 : System.Platform.numBits = 64) (a : Slice F64) (v : F64) (hn : a.val.length < 2^62) :
    ∀ (k : Nat) (lo hi : I64) (fuel : U64) (hlo : 0 ≤ lo.val) (hhi : hi.val + 1 ≤ a.val.length) (hle : lo.val ≤ hi.val + 1),
      (hi.val + 1 - lo.val).toNat = k → k + 1 ≤ fuel.val →
      ∃ r, sim.geometry.binary_search_d_loop a v lo hi fuel = ok r ∧
        r.val = OsuModel.Sim.bsearchBy (abs a : _root_.Array F64) (OsuModel.Sim.compareD · v) lo.val.toNat
          (hi.val + 1).toNat (by simp [abs]; omega) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro lo hi fuel hlo hhi hle hk hf
    unfold sim.geometry.binary_search_d_loop
    rw [loop_unfold]
    by_cases hc : lo.val ≤ hi.val
    · have hc' : lo ≤ hi := by scalar_tac
      have hfp : fuel > 0#u64 := by scalar_tac
      obtain ⟨fuel1, hf1, hf1v⟩ : ∃ z, fuel - 1#u64 = ok z ∧ z.val = fuel.val - 1 := by
        obtain ⟨z, hz, hv, _⟩ := eq_ok_of_spec (U64.sub_spec (x := fuel) (y := 1#u64) (by simp; omega))
        exact ⟨z, hz, by simpa using hv⟩
      obtain ⟨d, hd, hdv⟩ := eq_ok_of_spec (IScalar.sub_spec (x := hi) (y := lo) (by scalar_tac) (by scalar_tac))
      obtain ⟨q, hq, hqv⟩ := IScalar.div_spec (x := d) (y := 2#i64) (by simp) (by scalar_tac)
      have hq2 : q.val = (hi.val - lo.val) / 2 := by
        rw [hqv, hdv]; simp; rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
      obtain ⟨m, hm, hmv⟩ := eq_ok_of_spec (IScalar.add_spec (x := lo) (y := q) (by scalar_tac) (by scalar_tac))
      have hmc : (IScalar.hcast .Usize m).val = m.val.toNat := by
        rw [IScalar.hcast_val_eq]; simp only [UScalarTy.Usize_numBits_eq, h64]; omega
      have hml : (IScalar.hcast .Usize m).val < a.val.length := by rw [hmc]; omega
      obtain ⟨c, hcmp, ec⟩ := sim.geometry.compare_d_refines (a.val[(IScalar.hcast .Usize m).val]'hml) v
      simp only [abs, id] at ec
      have hmid : (IScalar.hcast .Usize m).val = lo.val.toNat + ((hi.val + 1).toNat - 1 - lo.val.toNat) / 2 := by
        rw [hmc, hmv, hq2]; omega
      have hA : ∀ (j : Nat) (hj : j < (abs a : _root_.Array F64).size) (hj' : j < a.val.length),
          (abs a : _root_.Array F64)[j] = a.val[j] := by intro j hj hj'; simp [abs]
      have hb : sim.geometry.binary_search_d_loop.body a v lo hi fuel =
          ((if c = 0#i32 then ok (ControlFlow.done m) else if c < 0#i32 then (do let lo1 ← m + 1#i64; ok (ControlFlow.cont (lo1, hi, fuel1)))
            else (do let hi1 ← m - 1#i64; ok (ControlFlow.cont (lo, hi1, fuel1)))) : Result (ControlFlow (I64 × I64 × U64) I64)) := by
        simp only [sim.geometry.binary_search_d_loop.body, hc', hfp, ite_true, hf1, hd, hq, hm, lift, bind_ok,
          index_eq a _ hml, hcmp]
      rw [OsuModel.Sim.bsearchBy, dif_pos (by omega)]
      dsimp only
      rw [hb]
      have eA : (abs a : _root_.Array F64)[lo.val.toNat + ((hi.val + 1).toNat - 1 - lo.val.toNat) / 2]'(by simp [abs]; omega)
          = a.val[(IScalar.hcast .Usize m).val]'hml := by simp [abs, hmid]
      rw [eA, ec]
      by_cases h0 : c.val = 0
      · have hc0 : c = 0#i32 := IScalar.eq_of_val_eq (by simp [h0])
        refine ⟨m, by simp [hc0], ?_⟩
        simp [h0]; omega
      · have hc0 : ¬ c = 0#i32 := fun e => h0 (by simp [e])
        by_cases hneg : c.val < 0
        · have hcn : c < 0#i32 := by scalar_tac
          obtain ⟨m1, hm1, hm1v⟩ := i64_add_one m (by scalar_tac) (by scalar_tac)
          obtain ⟨r, hr, er⟩ := ih (hi.val + 1 - m1.val).toNat (by omega) m1 hi fuel1 (by omega) hhi (by omega) rfl (by omega)
          refine ⟨r, ?_, ?_⟩
          · simp only [hc0, hcn, ite_true, ite_false, hm1, bind_ok]; exact hr
          · rw [er]; simp only [h0, hneg, beq_iff_eq, decide_true, ite_true, ite_false]
            congr 1; omega
        · have hcn : ¬ c < 0#i32 := by scalar_tac
          obtain ⟨m1, hm1, hm1v⟩ := i64_sub_one m (by scalar_tac) (by scalar_tac)
          obtain ⟨r, hr, er⟩ := ih (m1.val + 1 - lo.val).toNat (by omega) lo m1 fuel1 hlo (by omega) (by omega) rfl (by omega)
          refine ⟨r, ?_, ?_⟩
          · simp only [hc0, hcn, ite_false, hm1, bind_ok]; exact hr
          · rw [er]; simp only [h0, hneg, beq_iff_eq, decide_false, ite_false, Bool.false_eq_true]
            congr 1; omega
    · have hc' : ¬ (lo ≤ hi) := by scalar_tac
      obtain ⟨n1, hn1, hn1v⟩ := s2_i64_neg lo hlo
      obtain ⟨n2, hn2, hn2v⟩ := i64_sub_one n1 (by scalar_tac) (by scalar_tac)
      refine ⟨n2, ?_, ?_⟩
      · simp [sim.geometry.binary_search_d_loop.body, hc', hn1, hn2]
      · rw [OsuModel.Sim.bsearchBy]
        rw [dif_neg (by omega)]
        simp [hn2v, hn1v]; omega

theorem sim.geometry.binary_search_d_refines (h64 : System.Platform.numBits = 64) (a : Slice F64) (v : F64)
    (hn : a.val.length < 2^62) :
    ∃ r, sim.geometry.binary_search_d a v = ok r ∧ OsuModel.Sim.binarySearchD (abs a) (abs v) = abs r := by
  have hc1 : (UScalar.hcast .I64 (Slice.len a)).val = a.val.length := by
    rw [UScalar.hcast_val_eq]; simp only [Slice.len_val]
    rw [Int.bmod_def]
    have e : ((a.val.length : Nat) : Int) % (2 ^ IScalarTy.I64.numBits : Nat) = a.val.length :=
      Int.emod_eq_of_lt (by omega) (by simp; omega)
    rw [e]; split <;> simp at * <;> omega
  have hc2 : (UScalar.cast .U64 (Slice.len a)).val = a.val.length := by
    rw [UScalar.cast_val_eq]; simp; omega
  obtain ⟨hi, hhi, hhiv⟩ := i64_sub_one (UScalar.hcast .I64 (Slice.len a)) (by scalar_tac) (by scalar_tac)
  obtain ⟨fu, hfu, hfuv⟩ : ∃ z, UScalar.cast .U64 (Slice.len a) + 2#u64 = ok z ∧ z.val = a.val.length + 2 := by
    obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (U64.add_spec (x := UScalar.cast .U64 (Slice.len a)) (y := 2#u64) (by scalar_tac))
    exact ⟨z, hz, by simp [hv, hc2]⟩
  obtain ⟨r, hr, er⟩ := s2_bsearch_loop h64 a v hn a.val.length 0#i64 hi fu (by simp) (by rw [hhiv, hc1]; omega) (by simp; rw [hhiv, hc1]; omega) (by simp; rw [hhiv, hc1]; omega) (by rw [hfuv]; omega)
  refine ⟨r, ?_, ?_⟩
  · simp only [sim.geometry.binary_search_d, lift, bind_ok, hhi, hfu]; exact hr
  · simp only [OsuModel.Sim.binarySearchD, OsuModel.Sim.bsearch, abs, id] at er ⊢
    rw [er]; congr 1 <;> simp <;> omega

theorem s2_bsearchBy_bounds {α : Type} (a : _root_.Array α) (cmp : α → Int) :
    ∀ (n lo hi : Nat) (h : hi ≤ a.size), hi - lo = n → lo ≤ hi →
      -(hi : Int) - 1 ≤ OsuModel.Sim.bsearchBy a cmp lo hi h ∧ OsuModel.Sim.bsearchBy a cmp lo hi h < hi := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro lo hi h hn hle
    rw [OsuModel.Sim.bsearchBy]
    split
    · dsimp only
      split
      · omega
      · split
        · have := ih (hi - (lo + (hi - 1 - lo) / 2 + 1)) (by omega) (lo + (hi - 1 - lo) / 2 + 1) hi h rfl (by omega); omega
        · have := ih ((lo + (hi - 1 - lo) / 2) - lo) (by omega) lo (lo + (hi - 1 - lo) / 2) (by omega) rfl (by omega); omega
    · omega

theorem s2_binarySearchD_bounds (a : _root_.Array F64) (v : F64) :
    -(a.size : Int) - 1 ≤ OsuModel.Sim.binarySearchD a v ∧ OsuModel.Sim.binarySearchD a v < a.size :=
  s2_bsearchBy_bounds a _ a.size 0 a.size (Nat.le_refl _) (by simp) (by simp)

set_option maxRecDepth 10000 in
theorem sim.geometry.position_at_refines (h64 : System.Platform.numBits = 64) (sd : sim.playable.SliderData) (progress : F64)
    (hc : sd.cum_len.val.length < 2^62) (hp : sd.path.val.length < 2^62) :
    ∃ x, sim.geometry.position_at sd progress = ok x ∧
      s2_rel abs (OsuModel.Sim.SliderData.positionAt (abs sd) (abs progress)) x := by
  have hU := usize_max_64 h64
  obtain ⟨dist, hdist, edist⟩ := sim.geometry.distance_refines sd
  simp only [abs_id] at edist
  let cl : F64 := if progress < 0 then 0 else if 1 < progress then 1 else progress
  have hcl : ∀ {X : Type} (k : F64 → Result X), (do
      let b ← float.F64.lt progress (0 : F64)
      let c ← (if b then ok (0 : F64) else do
        let b1 ← float.F64.lt (1 : F64) progress
        if b1 then ok (1 : F64) else ok progress : Result F64)
      k c) = k cl := by
    intro X k
    by_cases h1 : progress < 0 <;> by_cases h2 : 1 < progress <;> simp [float.F64.lt, h1, h2, cl]
  obtain ⟨i0, hi0, ei0⟩ := sim.geometry.binary_search_d_refines h64 (alloc.vec.Vec.deref sd.cum_len) (cl * dist)
    (by simpa [alloc.vec.Vec.deref] using hc)
  have hcum : (abs sd : OsuModel.Sim.SliderData).cumLen = (abs (alloc.vec.Vec.deref sd.cum_len) : _root_.Array F64) := by
    simp [abs, alloc.vec.Vec.deref]
  have hb := s2_binarySearchD_bounds (abs (alloc.vec.Vec.deref sd.cum_len) : _root_.Array F64) (cl * dist)
  simp only [abs_id] at ei0
  rw [ei0] at hb
  have hsz : (abs (alloc.vec.Vec.deref sd.cum_len) : _root_.Array F64).size = sd.cum_len.val.length := by
    simp [abs, alloc.vec.Vec.deref]
  rw [hsz] at hb
  simp only [abs] at hb
  obtain ⟨iR, hiR, eiR⟩ : ∃ iR : I64, (if i0 < 0#i64 then (do let i1 ← -. i0; i1 - 1#i64) else ok i0) = ok iR ∧
      iR.val = (if i0.val < 0 then -i0.val - 1 else i0.val) := by
    by_cases hneg : i0.val < 0
    · have hl : i0 < 0#i64 := by scalar_tac
      have hne : i0 ≠ IScalar.min .I64 := by intro e; have := hb.1; simp [IScalar.min] at e; scalar_tac
      obtain ⟨n1, hn1, hn1v⟩ := eq_ok_of_spec (HNeg.hNeg.step i0 hne)
      obtain ⟨n2, hn2, hn2v⟩ := i64_sub_one n1 (by scalar_tac) (by scalar_tac)
      exact ⟨n2, by simp [hl, hn1, hn2], by simp [hneg, hn2v, hn1v]⟩
    · have hl : ¬ i0 < 0#i64 := by scalar_tac
      exact ⟨i0, by simp [hl], by simp [hneg]⟩
  unfold sim.geometry.position_at OsuModel.Sim.SliderData.positionAt
  simp only [s2_geo_consts, bind_ok, hdist, float.F64.mul]
  rw [hcl]
  simp only [hi0, hiR, bind_ok]
  have ecl : (if (abs progress : F64) < OsuModel.Sim.f64zero then OsuModel.Sim.f64zero
      else if OsuModel.Sim.f64one < (abs progress : F64) then OsuModel.Sim.f64one else (abs progress : F64)) = cl := by
    simp only [abs_id, OsuModel.Sim.f64zero, OsuModel.Sim.f64one]; rfl
  have ei : (abs i0 : Int) = i0.val := rfl
  simp only [ecl, edist, hcum, ei0, ei]
  simp only [← eiR]
  have hpsz : (abs sd : OsuModel.Sim.SliderData).path.size = sd.path.val.length := by simp [abs]
  have hpget : ∀ (j : Nat) (h1 : j < (abs sd : OsuModel.Sim.SliderData).path.size) (h2 : j < sd.path.val.length),
      (abs sd : OsuModel.Sim.SliderData).path[j] = abs (sd.path.val[j]) := by intro j h1 h2; simp [abs]
  by_cases hA : sd.path.val.length = 0
  · have hA' : alloc.vec.Vec.len sd.path = 0#usize := by scalar_tac
    refine ⟨.Ok ⟨0, 0⟩, by simp [hA'], ?_⟩
    rw [dif_pos (by rw [hpsz]; exact hA)]
    simp [s2_rel, pure, Except.pure, OsuModel.Sim.Vec2.zero]
  · have hA' : ¬ alloc.vec.Vec.len sd.path = 0#usize := by scalar_tac
    rw [dif_neg (by rw [hpsz]; exact hA)]
    have h0l : 0 < sd.path.val.length := by omega
    by_cases hB : iR.val ≤ 0
    · have hB' : iR ≤ 0#i64 := by scalar_tac
      refine ⟨.Ok (sd.path.val[0]'h0l), by simp [hA', hB', vec_index_usize_ok _ _ (show (0#usize).val < sd.path.val.length by simpa using h0l)], ?_⟩
      rw [dif_pos hB]
      simp [s2_rel, pure, Except.pure, hpget 0 (by rw [hpsz]; exact h0l) h0l]
    · have hB' : ¬ iR ≤ 0#i64 := by scalar_tac
      rw [dif_neg hB]
      have hn64 : (UScalar.hcast .I64 (alloc.vec.Vec.len sd.path)).val = sd.path.val.length := by
        rw [UScalar.hcast_val_eq]; simp only [alloc.vec.Vec.len_val]
        rw [Int.bmod_def]
        have e : ((sd.path.val.length : Nat) : Int) % (2 ^ IScalarTy.I64.numBits : Nat) = sd.path.val.length :=
          Int.emod_eq_of_lt (by omega) (by simp; omega)
        rw [e]; split <;> simp at * <;> omega
      by_cases hC : iR.val ≥ sd.path.val.length
      · have hC' : iR ≥ UScalar.hcast .I64 (alloc.vec.Vec.len sd.path) := by
          rw [ge_iff_le, IScalar.le_equiv, hn64]; exact_mod_cast hC
        obtain ⟨m, hm, hmv⟩ := usize_sub_one (alloc.vec.Vec.len sd.path) (by simp; omega)
        have hml : m.val < sd.path.val.length := by simp at hmv; omega
        refine ⟨.Ok (sd.path.val[m.val]'hml), ?_, ?_⟩
        · simp only [hA', hB', ite_false, lift, bind_ok]; rw [if_pos hC']
          simp [hm, vec_index_usize_ok _ _ hml]
        · rw [dif_pos (by rw [hpsz]; exact_mod_cast hC)]
          simp at hmv
          simp [s2_rel, pure, Except.pure, hmv]
          simp [abs]
      · have hC' : ¬ iR ≥ UScalar.hcast .I64 (alloc.vec.Vec.len sd.path) := by
          rw [ge_iff_le, IScalar.le_equiv, hn64]; omega
        rw [dif_neg (by rw [hpsz]; omega)]
        obtain ⟨i2, hi2, hi2v⟩ := i64_sub_one iR (by scalar_tac) (by scalar_tac)
        have hkc : (IScalar.hcast .Usize i2).val = (iR.val - 1).toNat := by
          rw [IScalar.hcast_val_eq]; simp only [UScalarTy.Usize_numBits_eq, h64]; omega
        have hk0 : (IScalar.hcast .Usize i2).val < sd.path.val.length := by omega
        obtain ⟨k1, hk1e, hk1v⟩ := usize_add_one (IScalar.hcast .Usize i2) (by omega)
        have hk1 : k1.val < sd.path.val.length := by omega
        have hcg : ∀ j : Nat, (abs (alloc.vec.Vec.deref sd.cum_len) : _root_.Array F64)[j]? = sd.cum_len.val[j]? := by
          intro j; simp [abs, alloc.vec.Vec.deref]
        simp only [hcg]
        simp only [hA', hB', ite_false, lift, bind_ok]; rw [if_neg hC']
        have eV : ∀ (j : Usize) (h : j.val < sd.path.val.length),
            alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.basic.Vec2) sd.path j = ok (sd.path.val[j.val]'h) := by
          intro j h; simp [vec_index_usize_ok _ _ h]
        have eC : ∀ (j : Usize) (h : j.val < sd.cum_len.val.length),
            alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice float.F64) sd.cum_len j = ok (sd.cum_len.val[j.val]'h) := by
          intro j h; simp [vec_index_usize_ok _ _ h]
        simp only [hi2, bind_ok, eV _ hk0, hk1e, eV _ hk1]
        have hk1n : k1.val = (iR.val - 1).toNat + 1 := by omega
        simp only [← hk1n]
        simp only [← hkc]
        have pg0 := hpget (IScalar.hcast .Usize i2).val (by rw [hpsz]; exact hk0) hk0
        have pg1 := hpget k1.val (by rw [hpsz]; exact hk1) hk1
        by_cases hD1 : sd.cum_len.val.length ≤ (IScalar.hcast .Usize i2).val
        · have hD1' : IScalar.hcast .Usize i2 ≥ alloc.vec.Vec.len sd.cum_len := by scalar_tac
          refine ⟨.Err (sim.err.SimErr.CumLen (IScalar.hcast .Usize i2)), by simp [hD1'], ?_⟩
          rw [List.getElem?_eq_none hD1]; simp [s2_rel, throw, throwThe, MonadExceptOf.throw]
        · have hD1' : ¬ IScalar.hcast .Usize i2 ≥ alloc.vec.Vec.len sd.cum_len := by scalar_tac
          have hlt0 : (IScalar.hcast .Usize i2).val < sd.cum_len.val.length := by omega
          rw [List.getElem?_eq_getElem hlt0]
          by_cases hD2 : sd.cum_len.val.length ≤ k1.val
          · have hD2' : k1 ≥ alloc.vec.Vec.len sd.cum_len := by scalar_tac
            refine ⟨.Err (sim.err.SimErr.CumLen k1), by simp [hD1', hD2'], ?_⟩
            rw [List.getElem?_eq_none hD2]; simp [s2_rel, throw, throwThe, MonadExceptOf.throw]
          · have hD2' : ¬ k1 ≥ alloc.vec.Vec.len sd.cum_len := by scalar_tac
            have hlt1 : k1.val < sd.cum_len.val.length := by omega
            rw [List.getElem?_eq_getElem hlt1]
            obtain ⟨ae, hae, eae⟩ := sim.basic.almost_equals_d_refines (sd.cum_len.val[(IScalar.hcast .Usize i2).val]'hlt0)
              (sd.cum_len.val[k1.val]'hlt1)
            simp only [abs_id] at eae
            simp only [hD1', hD2', ite_false, eC _ hlt0, eC _ hlt1, hae, bind_ok]
            rw [eae, pg0, pg1]
            cases ae
            · simp [s2_rel, pure, Except.pure, float.F64.sub, float.F64.div, float.F64.to_f32, sim.basic.Vec2.sub,
                sim.basic.Vec2.scale, sim.basic.Vec2.add]
              rfl
            · simp [s2_rel, pure, Except.pure]

theorem sim.geometry.curve_position_at_refines (h64 : System.Platform.numBits = 64) (sd : sim.playable.SliderData)
    (progress : F64) (hc : sd.cum_len.val.length < 2^62) (hp : sd.path.val.length < 2^62) :
    ∃ x, sim.geometry.curve_position_at sd progress = ok x ∧
      s2_rel abs (OsuModel.Sim.SliderData.curvePositionAt (abs sd) (abs progress)) x := by
  obtain ⟨p, hp1, ep⟩ := sim.geometry.progress_at_refines sd progress
  obtain ⟨x, hx, ex⟩ := sim.geometry.position_at_refines h64 sd p hc hp
  refine ⟨x, by simp [sim.geometry.curve_position_at, hp1, hx], ?_⟩
  simp only [abs_id] at ep ex ⊢
  unfold OsuModel.Sim.SliderData.curvePositionAt
  rw [ep]; exact ex

theorem sim.geometry.is_mouse_in_follow_area_refines (h64 : System.Platform.numBits = 64) (h : sim.playable.HObj)
    (sd : sim.playable.SliderData) (g : sim.geometry.SliderGeom) (mouse : Option sim.basic.Vec2) (t : F64) (expanded : Bool)
    (hc : sd.cum_len.val.length < 2^62) (hp : sd.path.val.length < 2^62) :
    ∃ x, sim.geometry.is_mouse_in_follow_area h sd g mouse t expanded = ok x ∧
      s2_rel abs (OsuModel.Sim.isMouseInFollowArea (abs h) (abs sd) (abs g) (abs mouse) (abs t) (abs expanded)) x := by
  cases mouse with
  | none =>
    refine ⟨.Ok false, by simp [sim.geometry.is_mouse_in_follow_area], ?_⟩
    simp [OsuModel.Sim.isMouseInFollowArea, s2_rel, abs, pure, Except.pure]
  | some pos =>
    obtain ⟨rad, hrad, erad⟩ := sim.geometry.follow_radius_refines h expanded
    let fp0 : F64 := (t - h.start) / sd.duration
    let fp : F64 := if fp0 < 0 then 0 else if 1 < fp0 then 1 else fp0
    have hfp : ∀ {X : Type} (k : F64 → Result X), (do
        let b ← float.F64.lt fp0 (0 : F64)
        let c ← (if b then ok (0 : F64) else do
          let b1 ← float.F64.lt (1 : F64) fp0
          if b1 then ok (1 : F64) else ok fp0 : Result F64)
        k c) = k fp := by
      intro X k
      by_cases h1 : fp0 < 0 <;> by_cases h2 : 1 < fp0 <;> simp [float.F64.lt, h1, h2, fp]
    obtain ⟨cp, hcp, ecp⟩ := sim.geometry.curve_position_at_refines h64 sd fp hc hp
    obtain ⟨m, hm, em⟩ := sim.geometry.mouse_in_slider_refines g pos
    unfold sim.geometry.is_mouse_in_follow_area
    simp only [hrad, bind_ok, float.F64.sub, float.F64.div, s2_geo_consts]
    rw [hfp]
    simp only [hcp, bind_ok]
    have espec : OsuModel.Sim.isMouseInFollowArea (abs h) (abs sd) (abs g) (abs (some pos)) (abs t) (abs expanded) =
        (do let follow ← OsuModel.Sim.SliderData.curvePositionAt (abs sd) fp
            return (OsuModel.Sim.mouseInSlider (abs g) (abs pos) - follow).lengthSquared ≤
              OsuModel.Sim.followRadius (abs h) expanded * OsuModel.Sim.followRadius (abs h) expanded) := by
      simp only [OsuModel.Sim.isMouseInFollowArea]
      rfl
    rw [espec]
    simp only [abs_id] at ecp erad
    revert ecp
    cases OsuModel.Sim.SliderData.curvePositionAt (abs sd) fp with
    | error e =>
      intro ecp
      cases cp with
      | Ok v => exact absurd ecp (by simp [s2_rel])
      | Err e' =>
        refine ⟨.Err e', by simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], ?_⟩
        simp [s2_rel, Bind.bind, Except.bind]
    | ok v =>
      intro ecp
      cases cp with
      | Err e' => exact absurd ecp (by simp [s2_rel])
      | Ok c =>
        simp only [s2_rel] at ecp
        refine ⟨_, by simp [core.result.Result.Insts.CoreOpsTry.branch, hm, sim.basic.Vec2.sub, sim.basic.Vec2.length_squared,
          float.F32.mul, float.F32.le]; rfl, ?_⟩
        simp only [s2_rel, Bind.bind, Except.bind, pure, Except.pure, ← ecp, em, erad]
        simp [abs, OsuModel.Sim.Vec2.lengthSquared]
        rfl

end OsuProofs

namespace OsuProofs
open OsuImpl

open OsuModel.Sim in
/-- the tail of `sliderGeom` after the bounds (verbatim) -/
def s2_sgTail (env : Env) (h : HObj) (r : OsuModel.Net.F32) (size origin : Vec2) : SliderGeom :=
  let di := childDrawInfo env.hoc h.stacked Vec2.zero ⟨1, 1⟩ origin
  let hcSize : Vec2 := ⟨1 * size.x, 1 * size.y⟩
  let hc := childDrawInfo di Vec2.zero (Vec2.mul Vec2.zero size) ⟨1, 1⟩ Vec2.zero
  let relAnchor := Vec2.cdiv origin size
  let head := receptorFromDho hc Vec2.zero (Vec2.mul relAnchor hcSize) h.scale
  { pathRadius := r, size, origin, drawInfo := di, headReceptor := head }

theorem s2_sliderGeom_eq (env : OsuModel.Sim.Env) (h : OsuModel.Sim.HObj) (sd : OsuModel.Sim.SliderData) :
    OsuModel.Sim.sliderGeom env h sd =
      (let r := env.argonPathRadius * h.scale
       let b := sd.path.foldl (s2_bstep r) (0, 0, 0, 0)
       let size : OsuModel.Sim.Vec2 := if sd.path.size > 0 then ⟨b.2.2.1 - b.1, b.2.2.2 - b.2.1⟩ else OsuModel.Sim.Vec2.zero
       let tl : OsuModel.Sim.Vec2 := if sd.path.size > 0 then ⟨b.1, b.2.1⟩ else OsuModel.Sim.Vec2.zero
       match sd.path[0]? with
       | some v0 => pure (s2_sgTail env h r size (v0 - tl))
       | none => throw OsuModel.Sim.emptyPathMsg) := by
  unfold OsuModel.Sim.sliderGeom
  dsimp only
  rw [Array.forIn_pure_yield_eq_foldl]
  simp only [pure_bind]
  cases sd.path[0]? <;> rfl

@[simp] theorem s2_cdiv_eq (a b : sim.basic.Vec2) :
    sim.basic.Vec2.cdiv a b = ok (s2_v2R (OsuModel.Sim.Vec2.cdiv (abs a) (abs b))) :=
  s2_eq_of_ex s2_v2R (fun _ => rfl) (sim.basic.Vec2.cdiv_refines a b)

theorem sim.geometry.slider_geom_refines (env : sim.geometry.Env) (h : sim.playable.HObj) (sd : sim.playable.SliderData) :
    ∃ x, sim.geometry.slider_geom env h sd = ok x ∧ s2_rel abs (OsuModel.Sim.sliderGeom (abs env) (abs h) (abs sd)) x := by
  obtain ⟨b, hb, eb⟩ := sim.geometry.path_bounds_refines (alloc.vec.Vec.deref sd.path) (env.argon_path_radius * h.scale)
  have ep : (abs sd : OsuModel.Sim.SliderData).path = (abs (alloc.vec.Vec.deref sd.path) : _root_.Array OsuModel.Sim.Vec2) := by
    simp [abs, alloc.vec.Vec.deref]
  have er : (abs env : OsuModel.Sim.Env).argonPathRadius * (abs h : OsuModel.Sim.HObj).scale = env.argon_path_radius * h.scale := rfl
  rw [s2_sliderGeom_eq]
  dsimp only
  rw [er, ep, eb]
  unfold sim.geometry.slider_geom
  simp only [float.F32.mul, hb, bind_ok]
  by_cases h0 : sd.path.val.length = 0
  · have h1 : ¬ (alloc.vec.Vec.len sd.path > 0#usize) := by scalar_tac
    have h2 : alloc.vec.Vec.len sd.path = 0#usize := by scalar_tac
    have e : sd.path.val = [] := List.eq_nil_of_length_eq_zero h0
    refine ⟨.Err sim.err.SimErr.EmptyPath, by simp [h1, h2], ?_⟩
    simp [s2_rel, abs, alloc.vec.Vec.deref, e, throw, throwThe, MonadExceptOf.throw]
  · have h1 : alloc.vec.Vec.len sd.path > 0#usize := by scalar_tac
    have h2 : ¬ (alloc.vec.Vec.len sd.path = 0#usize) := by scalar_tac
    have hp : 0 < sd.path.val.length := by omega
    refine ⟨_, by simp [h1, h2, float.F32.sub, vec_index_usize_ok _ _ (show (0#usize).val < sd.path.val.length by simpa using hp),
      sim.basic.Vec2.sub, sim.basic.Vec2.mul, float.F32.mul, sim_basic_VEC2_ZERO, sim_basic_VEC2_ONE, sim_basic_F32_1,
      s2_child_draw_info_eq, s2_cdiv_eq, s2_receptor_from_dho_eq]; rfl, ?_⟩
    have hsz : (abs (alloc.vec.Vec.deref sd.path) : _root_.Array OsuModel.Sim.Vec2).size > 0 := by
      simp [abs, alloc.vec.Vec.deref]; omega
    have h0' : (abs (alloc.vec.Vec.deref sd.path) : _root_.Array OsuModel.Sim.Vec2)[0]? = some (abs (sd.path.val[0]'hp)) := by
      simp [abs, alloc.vec.Vec.deref, List.getElem?_eq_getElem hp]
    rw [h0', if_pos hsz, if_pos hsz]
    simp only [s2_rel, pure, Except.pure]
    rw [← s2_abs_sgR (s2_sgTail _ _ _ _ _)]
    congr 1
end OsuProofs
