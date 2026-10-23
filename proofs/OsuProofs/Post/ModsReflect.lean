/-
`beatmap::mods` geometry (`modify_slider`, `set_position`, `reflect_*`, `mirror`) and `apply_to_hit_object`
(Rust) refine `Mods.modifySlider` / `setPosition` / `reflect*` / `mirror` / `ModConfig.hooks.applyToHitObject`
(mods proof agent; abs-style). Slider paths rebuilt from moved control points must stay small (`MsOk`).
-/
import OsuProofs.Post.Playable
import OsuProofs.Post.ModsB
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

/-- the control points `Mods.modifySlider f` rebuilds the path from -/
def msCps (f : Vec2 → Vec2) (cps : Array PathControlPoint) : Array PathControlPoint :=
  let cps := cps.map fun p =>
    let c := Mods.newControlPointPos p.position
    { p with position := Mods.setControlPointPos c (f c) }
  cps.map fun p => { p with position := Mods.newControlPointPos p.position }

def msSpec (f : Vec2 → Vec2) (s : SliderData) : SliderPathSpec :=
  { controlPoints := msCps f s.path.spec.controlPoints, expectedDistance := s.path.spec.expectedDistance,
    optimiseCatmull := true }

/-- size side conditions of `Mods.modifySlider f h` (the rebuilt slider path stays in the machine ranges) -/
def MsOk (f : Vec2 → Vec2) (h : OsuHitObject) : Prop :=
  ∀ s, h.kind = .slider s → s.path.spec.controlPoints.size < 2^32 ∧
    (SliderPath.calculatePath (msSpec f s)).1.size < 2^62 ∧
    (SliderPath.ofControlPoints (msCps f s.path.spec.controlPoints) s.path.spec.expectedDistance true).cumulativeLength.size < 2^61 ∧
    (SliderPath.ofControlPoints (msCps f s.path.spec.controlPoints) s.path.spec.expectedDistance true).calculatedPath.size < 2^62

def msStep (f : beatmap.mods.PointMap) (p : beatmap.types.PathControlPoint) : beatmap.types.PathControlPoint :=
  { p with position := bv2I (Mods.newControlPointPos (Mods.setControlPointPos (Mods.newControlPointPos (bv2S p.position))
      (pmS f (Mods.newControlPointPos (bv2S p.position))))) }

theorem msr_scpp (old new : net.osutk.Vector2) :
    beatmap.mods.set_control_point_pos old new = ok (bv2I (Mods.setControlPointPos (bv2S old) (bv2S new))) := by
  obtain ⟨r, hr, hrv⟩ := beatmap.mods.set_control_point_pos_refines old new
  rw [hr]; congr 1
  have : (abs old : Vec2) = bv2S old := rfl
  have h2 : (abs new : Vec2) = bv2S new := rfl
  have h3 : (abs r : Vec2) = bv2S r := rfl
  rw [this, h2, h3] at hrv; rw [hrv]; rfl

theorem msr_loop (f : beatmap.mods.PointMap) (old : alloc.vec.Vec beatmap.types.PathControlPoint) :
    ∃ r, beatmap.mods.modify_slider_loop f old (alloc.vec.Vec.with_capacity beatmap.types.PathControlPoint
      (alloc.vec.Vec.len old)) 0#usize = ok r ∧ r.val = old.val.map (msStep f) := by
  obtain ⟨r, hr, hrv⟩ := loop_push_map (fun x => beatmap.mods.modify_slider_loop.body f old x.1 x.2) old.val.length
    (fun i => msStep f (old.val[i]!))
    (by
      intro ts i hlt hmax
      have hl : i.val < old.val.length := hlt
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := old.property; omega)
      obtain ⟨w, hw, hwv⟩ := push_eq ts (msStep f (old.val[i.val]'hl)) (by omega)
      refine ⟨w, i1, ?_, by rw [hwv, getElem!_pos old.val i.val hl], hi1v⟩
      simp only [beatmap.mods.modify_slider_loop.body, vec_lt_len_iff, hl, if_true, vec_index_eq _ _ hl, bind_ok,
        beatmap.mods.new_control_point_pos_refines, beatmap.mods.apply_point_map_refines, msr_scpp, hi1]
      have : bv2S (bv2I (Mods.newControlPointPos (bv2S (old.val[i.val]'hl).position))) =
        Mods.newControlPointPos (bv2S (old.val[i.val]'hl).position) := rfl
      simp only [this]
      have h2 : ∀ v : Vec2, bv2S (bv2I v) = v := fun v => rfl
      simp only [h2]
      simp only [msStep] at hw
      rw [hw, bind_ok])
    (by
      intro ts i hle
      have : ¬ i < alloc.vec.Vec.len old := by show ¬ i.val < (alloc.vec.Vec.len old).val; simp; omega
      simp [beatmap.mods.modify_slider_loop.body, this])
    (alloc.vec.Vec.with_capacity beatmap.types.PathControlPoint (alloc.vec.Vec.len old)) 0#usize (by simp)
    (by have := old.property; simp [alloc.vec.Vec.with_capacity]; try omega)
  refine ⟨r, by unfold beatmap.mods.modify_slider_loop; exact hr, ?_⟩
  rw [hrv]; simp [alloc.vec.Vec.with_capacity]
  apply List.ext_getElem (by simp)
  intro n h1 h2
  have hn : n < old.val.length := by simpa using h2
  simp [List.getElem?_eq_getElem hn]

theorem msr_cps (f : beatmap.mods.PointMap) (l : List beatmap.types.PathControlPoint) :
    pcpsS (l.map (msStep f)) = msCps (pmS f) (pcpsS l) := by
  simp only [pcpsS, msCps, msStep, List.map_map, List.map_toArray]
  congr 1

theorem beatmap.mods.modify_slider_refines (f : beatmap.mods.PointMap) (h : beatmap.objects.OsuHitObject)
    (hms : MsOk (pmS f) (abs h)) (h64 : System.Platform.numBits = 64) :
    ∃ r, beatmap.mods.modify_slider f h = ok r ∧ Mods.modifySlider (pmS f) (abs h) = abs r := by
  have hkd : (abs h : OsuHitObject).kind = abs h.kind := rfl
  unfold beatmap.mods.modify_slider Mods.modifySlider
  cases hk : h.kind with
  | Circle => exact ⟨h, rfl, by rw [hkd, hk]; rfl⟩
  | Spinner sp => exact ⟨h, rfl, by rw [hkd, hk]; rfl⟩
  | Slider s =>
    have hsa : (abs h : OsuHitObject).kind = .slider (abs s) := by rw [hkd, hk]; rfl
    obtain ⟨hn, hsz, hc1, hc2⟩ := hms (abs s) hsa
    have hps : (abs s : SliderData).path = spS s.path := by
      show (abs s.path : SliderPath) = _; exact ob_abs_sliderPath _
    simp only [msSpec] at hsz
    rw [hps] at hn hsz hc1 hc2
    obtain ⟨cps, hcps, hcpsv⟩ := msr_loop f s.path.spec.control_points
    have hcS : pcpsS cps.val = msCps (pmS f) (spS s.path).spec.controlPoints := by
      rw [hcpsv, msr_cps]; rfl
    obtain ⟨sp, hsp, hspv⟩ := beatmap.slider_path.of_control_points_refines cps s.path.spec.expected_distance true h64
      (by have : cps.val.length = s.path.spec.control_points.val.length := by rw [hcpsv]; simp
          rw [this]; simpa [spS, spsS, pcpsS] using hn)
      (by rw [hcS]; simpa [spS, spsS] using hsz)
    have hok : obPathOk sp := by
      have e : spS sp = SliderPath.ofControlPoints (msCps (pmS f) (spS s.path).spec.controlPoints)
          (spS s.path).spec.expectedDistance true := by rw [hspv, hcS]; rfl
      constructor
      · have e1 : sp.cumulative_length.val.length = (spS sp).cumulativeLength.size := by simp [spS]
        rw [e1, e]; exact hc1
      · have e2 : sp.calculated_path.val.length = (spS sp).calculatedPath.size := by simp [spS]
        rw [e2, e]; exact hc2
    obtain ⟨r, hr, hrv⟩ := beatmap.playable.update_nested_positions_refines
      { h with kind := .Slider { s with path := { sp with fuel_out := sp.fuel_out || s.path.fuel_out } } }
      (by intro s' hs'; cases hs'; exact hok) h64
    have hb : (if sp.fuel_out then ok true else ok s.path.fuel_out : Result Bool) = ok (sp.fuel_out || s.path.fuel_out) := by
      cases sp.fuel_out <;> rfl
    refine ⟨r, by simp only [hcps, bind_ok, hsp, hb, hr], ?_⟩
    rw [hsa]; dsimp only
    rw [← hrv]; congr 1
    show _ = ({ (abs h : OsuHitObject) with kind := .slider { (abs s : SliderData) with
      path := abs ({ sp with fuel_out := sp.fuel_out || s.path.fuel_out } : beatmap.slider_path.SliderPath) } } : OsuHitObject)
    rw [ob_abs_sliderPath]
    have hsp' : spS ({ sp with fuel_out := sp.fuel_out || s.path.fuel_out } : beatmap.slider_path.SliderPath) =
        { spS sp with fuelOut := (spS sp).fuelOut || (spS s.path).fuelOut } := rfl
    rw [hsp', hspv, hcS, hps]; rfl

theorem beatmap.mods.set_position_refines (h : beatmap.objects.OsuHitObject) (p : net.osutk.Vector2)
    (hp : ∀ s, h.kind = .Slider s → obPathOk s.path) (h64 : System.Platform.numBits = 64) :
    ∃ r, beatmap.mods.set_position h p = ok r ∧ Mods.setPosition (abs h) (bv2S p) = abs r := by
  obtain ⟨r, hr, hrv⟩ := beatmap.playable.update_nested_positions_refines { h with position := p } hp h64
  exact ⟨r, hr, hrv⟩

theorem msr_unp_kind (h : OsuHitObject) : (updateNestedPositions h).kind = h.kind := by
  unfold updateNestedPositions; split <;> rfl

theorem msr_ok_setpos (f : Vec2 → Vec2) (h : OsuHitObject) (p : Vec2) :
    MsOk f (Mods.setPosition h p) ↔ MsOk f h := by
  unfold MsOk Mods.setPosition; rw [msr_unp_kind]

theorem beatmap.mods.reflect_vertically_refines (h : beatmap.objects.OsuHitObject)
    (hp : ∀ s, h.kind = .Slider s → obPathOk s.path) (hms : MsOk (pmS .NegY) (abs h))
    (h64 : System.Platform.numBits = 64) :
    ∃ r, beatmap.mods.reflect_vertically h = ok r ∧ Mods.reflectVertically (abs h) = abs r := by
  obtain ⟨h1, hh1, hh1v⟩ := beatmap.mods.set_position_refines h { h.position with y := (384 : F32) - h.position.y } hp h64
  obtain ⟨r, hr, hrv⟩ := beatmap.mods.modify_slider_refines .NegY h1
    (by rw [← hh1v, msr_ok_setpos]; exact hms) h64
  refine ⟨r, by simp only [beatmap.mods.reflect_vertically, cst_beatmap_mods_BASE_H, bind_ok, float.F32.sub, hh1, hr], ?_⟩
  rw [← hrv, ← hh1v]; rfl

theorem beatmap.mods.reflect_horizontally_refines (h : beatmap.objects.OsuHitObject)
    (hp : ∀ s, h.kind = .Slider s → obPathOk s.path) (hms : MsOk (pmS .NegX) (abs h))
    (h64 : System.Platform.numBits = 64) :
    ∃ r, beatmap.mods.reflect_horizontally h = ok r ∧ Mods.reflectHorizontally (abs h) = abs r := by
  obtain ⟨h1, hh1, hh1v⟩ := beatmap.mods.set_position_refines h { h.position with x := (512 : F32) - h.position.x } hp h64
  obtain ⟨r, hr, hrv⟩ := beatmap.mods.modify_slider_refines .NegX h1
    (by rw [← hh1v, msr_ok_setpos]; exact hms) h64
  refine ⟨r, by simp only [beatmap.mods.reflect_horizontally, cst_beatmap_mods_BASE_W, bind_ok, float.F32.sub, hh1, hr], ?_⟩
  rw [← hrv, ← hh1v]; rfl

/-- slider paths within the machine ranges (spec side of `obPathOk`) -/
def PathsOk (h : OsuHitObject) : Prop :=
  ∀ s, h.kind = .slider s → s.path.cumulativeLength.size < 2^61 ∧ s.path.calculatedPath.size < 2^62

theorem msr_paths_ok (h : beatmap.objects.OsuHitObject) (hp : PathsOk (abs h)) :
    ∀ s, h.kind = .Slider s → obPathOk s.path := by
  intro s hs
  have hsa : (abs h : OsuHitObject).kind = .slider (abs s) := by
    show (abs h.kind : ObjectKind) = _; rw [hs]; rfl
  obtain ⟨h1, h2⟩ := hp _ hsa
  have hps : (abs s : SliderData).path = spS s.path := by
    show (abs s.path : SliderPath) = _; exact ob_abs_sliderPath _
  rw [hps] at h1 h2
  simp [spS] at h1 h2
  exact ⟨h1, h2⟩

/-- side conditions of `Mods.mirror` / `reflectVertically` on `h` -/
def ReflOk (h : OsuHitObject) : Prop :=
  PathsOk h ∧ MsOk (pmS .NegX) h ∧ MsOk (pmS .NegY) h ∧ MsOk (pmS .NegY) (Mods.reflectHorizontally h) ∧
    PathsOk (Mods.reflectHorizontally h)

theorem beatmap.mods.mirror_refines (refl : I32) (h : beatmap.objects.OsuHitObject) (ho : ReflOk (abs h))
    (h64 : System.Platform.numBits = 64) :
    ∃ r, beatmap.mods.mirror refl h = ok r ∧ Mods.mirror (i32S refl) (abs h) = abs r := by
  obtain ⟨hp, hx, hy, hxy, hpx⟩ := ho
  have hp' := msr_paths_ok h hp
  unfold beatmap.mods.mirror Mods.mirror
  by_cases h0 : refl = 0#i32
  · subst h0
    obtain ⟨r, hr, hrv⟩ := beatmap.mods.reflect_horizontally_refines h hp' hx h64
    exact ⟨r, by simp [hr], by rw [← hrv]; rfl⟩
  by_cases h1 : refl = 1#i32
  · subst h1
    obtain ⟨r, hr, hrv⟩ := beatmap.mods.reflect_vertically_refines h hp' hy h64
    exact ⟨r, by simp [hr], by rw [← hrv]; rfl⟩
  by_cases h2 : refl = 2#i32
  · subst h2
    obtain ⟨r1, hr1, hrv1⟩ := beatmap.mods.reflect_horizontally_refines h hp' hx h64
    obtain ⟨r, hr, hrv⟩ := beatmap.mods.reflect_vertically_refines r1 (msr_paths_ok r1 (by rw [← hrv1]; exact hpx))
      (by rw [← hrv1]; exact hxy) h64
    exact ⟨r, by simp [hr1, hr], by rw [← hrv, ← hrv1]; rfl⟩
  refine ⟨h, by simp [h0, h1, h2], ?_⟩
  have hv0 : i32S refl ≠ 0 := by
    intro e; apply h0; apply IScalar.eq_of_val_eq
    have := congrArg Int32.toInt e; rw [i32S_toInt] at this; simpa using this
  have hv1 : i32S refl ≠ 1 := by
    intro e; apply h1; apply IScalar.eq_of_val_eq
    have := congrArg Int32.toInt e; rw [i32S_toInt] at this; simpa using this
  have hv2 : i32S refl ≠ 2 := by
    intro e; apply h2; apply IScalar.eq_of_val_eq
    have := congrArg Int32.toInt e; rw [i32S_toInt] at this; simpa using this
  split
  all_goals first | rfl | (exfalso; contradiction)

theorem msr_kREF : keyName beatmap.names.K_REFLECTION.val = "reflection" := by
  simp [beatmap.names.K_REFLECTION, keyName, keyNames]
theorem msr_kNSHA : keyName beatmap.names.K_NO_SLIDER_HEAD_ACCURACY.val = "no_slider_head_accuracy" := by
  simp [beatmap.names.K_NO_SLIDER_HEAD_ACCURACY, keyName, keyNames]

theorem beatmap.mods.apply_to_hit_object_refines (m : beatmap.mod_settings.ModConfig) (hv : AcrOk m)
    (hk : KeysOk m.settings.val) (h : beatmap.objects.OsuHitObject) (ho : ReflOk (abs h))
    (h64 : System.Platform.numBits = 64) :
    ∃ r, beatmap.mods.apply_to_hit_object m h = ok r ∧
      ((mcS m).hooks.applyToHitObject.getD id) (abs h) = abs r := by
  unfold beatmap.mods.apply_to_hit_object
  simp only [lift, bind_ok, mods_acr m hv _ _ _ _ se_HR, mods_acr m hv _ _ _ _ se_MR, mods_acr m hv _ _ _ _ se_CL]
  unfold ModConfig.hooks
  by_cases hkn : m.known = true
  · simp only [hkn, Bool.not_true, Bool.false_eq_true, if_false, Bool.true_and]
    have hmk : (mcS m).known = true := hkn
    simp only [hmk, Bool.not_true, Bool.false_eq_true, if_false]
    have hacr : (mcS m).acronym = vstrS m.acronym := rfl
    rw [hacr]
    generalize hA : vstrS m.acronym = A
    by_cases a_HR : A = "HR"
    · subst a_HR
      obtain ⟨r, hr, hrv⟩ := beatmap.mods.reflect_vertically_refines h (msr_paths_ok h ho.1) ho.2.2.1 h64
      exact ⟨r, by simp [hr], hrv⟩
    by_cases a_MR : A = "MR"
    · subst a_MR
      obtain ⟨i, hi, hiv⟩ := beatmap.mod_settings.get_int_refines m hk beatmap.names.K_REFLECTION
      rw [msr_kREF] at hiv
      obtain ⟨r, hr, hrv⟩ := beatmap.mods.mirror_refines i h ho h64
      refine ⟨r, by simp [hi, hr], ?_⟩
      show Mods.mirror ((mcS m).getInt "reflection") (abs h) = _
      rw [← hiv, hrv]
    by_cases a_CL : A = "CL"
    · subst a_CL
      obtain ⟨r, hr, hrv⟩ := beatmap.mods.classic_hit_object_refines
        ((mcS m).getBool (keyName beatmap.names.K_NO_SLIDER_HEAD_ACCURACY.val)) h
      refine ⟨r, by simp [beatmap.mod_settings.get_bool_refines m hk, hr], ?_⟩
      show Mods.classicHitObject ((mcS m).getBool "no_slider_head_accuracy") (abs h) = _
      rw [← hrv, msr_kNSHA]; rfl
    refine ⟨h, by simp [a_HR, a_MR, a_CL], ?_⟩
    split
    all_goals first | rfl | (exfalso; contradiction)
  · have : m.known = false := by simpa using hkn
    have hmk : (mcS m).known = false := this
    simp only [this, Bool.false_and, Bool.false_eq_true, if_false, hmk, Bool.not_false, if_true]
    exact ⟨h, rfl, rfl⟩

theorem msr_spec_clone (p : beatmap.slider_path.SliderPathSpec) :
    beatmap.slider_path.SliderPathSpec.Insts.CoreCloneClone.clone p = ok p := by
  simp [beatmap.slider_path.SliderPathSpec.Insts.CoreCloneClone.clone, hop_pcp_clone, pl_opt_clone, lift,
    core.clone.impls.CloneBool.clone]

/-- `SliderPath.compute` of each slider's spec stays in the machine ranges -/
def StOk (h : OsuHitObject) : Prop :=
  ∀ s, h.kind = .slider s → s.path.spec.controlPoints.size < 2^32 ∧ (SliderPath.calculatePath s.path.spec).1.size < 2^62

theorem beatmap.mods.strict_tracking_slider_refines (h : beatmap.objects.OsuHitObject) (hst : StOk (abs h))
    (h64 : System.Platform.numBits = 64) :
    ∃ r, beatmap.mods.strict_tracking_slider h = ok r ∧ Mods.strictTrackingSlider (abs h) = abs r := by
  have hkd : (abs h : OsuHitObject).kind = abs h.kind := rfl
  unfold beatmap.mods.strict_tracking_slider Mods.strictTrackingSlider
  cases hk : h.kind with
  | Circle => exact ⟨h, by simp [pl_ho_clone], by rw [hkd, hk]; rfl⟩
  | Spinner sp => exact ⟨h, by simp [pl_ho_clone], by rw [hkd, hk]; rfl⟩
  | Slider s =>
    have hsa : (abs h : OsuHitObject).kind = .slider (abs s) := by rw [hkd, hk]; rfl
    have hps : (abs s : SliderData).path = spS s.path := by
      show (abs s.path : SliderPath) = _; exact ob_abs_sliderPath _
    obtain ⟨hn, hsz⟩ := hst _ hsa
    rw [hps] at hn hsz
    obtain ⟨sp, hsp, hspv⟩ := beatmap.slider_path.compute_refines s.path.spec h64
      (by simpa [spS, spsS, pcpsS] using hn) (by simpa [spS] using hsz)
    have hz : float.F64.from_bits 0#u64 = ok (0 : F64) := by simp [float.F64.from_bits]; decide
    obtain ⟨o, ho, hov⟩ := beatmap.objects.object_default_refines (beatmap.objects.ObjectKind.Slider
      ({ s with path := sp, velocity := 0, tick_distance := 0, generate_ticks := true, classic_slider_behaviour := false, strict_tracking := true } : beatmap.objects.SliderData))
      h.start_time h.position
    refine ⟨{ o with new_combo := h.new_combo, combo_offset := h.combo_offset },
      by simp only [msr_spec_clone, bind_ok, hsp, hz, ho], ?_⟩
    rw [hsa]; dsimp only
    have e : (abs ({ o with new_combo := h.new_combo, combo_offset := h.combo_offset } : beatmap.objects.OsuHitObject) :
        OsuHitObject) = { (abs o : OsuHitObject) with newCombo := abs h.new_combo, comboOffset := abs h.combo_offset } := rfl
    rw [e, ← hov]
    have hsp' : (abs sp : SliderPath) = SliderPath.compute (spS s.path).spec := by
      rw [ob_abs_sliderPath, hspv]; rfl
    simp only [ob_abs_slider]
    have h3 : SliderPath.compute (abs s : SliderData).path.spec = abs sp := by rw [hps, hsp']
    rw [h3]; rfl

theorem msr_st_nonslider (h : OsuHitObject) (hs : h.isSlider = false) : Mods.strictTrackingSlider h = h := by
  unfold Mods.strictTrackingSlider OsuHitObject.isSlider at *
  split <;> simp_all

theorem msr_st_loop (pb : beatmap.playable.PlayableBeatmap) (hst : ∀ h ∈ pb.hit_objects.val, StOk (abs h))
    (h64 : System.Platform.numBits = 64) :
    ∃ v, beatmap.mods.strict_tracking_loop pb 0#usize = ok (pb.format_version, pb.difficulty, pb.base_difficulty,
        pb.stack_leniency, pb.audio_lead_in, pb.control_points, pb.breaks, v, pb.epoch, pb.mod_states) ∧
      v.val.map (abs : _ → OsuHitObject) = (pb.hit_objects.val.map abs).map Mods.strictTrackingSlider := by
  obtain ⟨y, hl, hv⟩ := loop_fold_gen' (fun x => beatmap.mods.strict_tracking_loop.body x.1 x.2) (·.2)
    pb.hit_objects.val.length (by have := pb.hit_objects.property; omega)
    (fun x => x.1 = { pb with hit_objects := x.1.hit_objects } ∧ x.1.hit_objects.val.length = pb.hit_objects.val.length ∧
      x.1.hit_objects.val.drop x.2.val = pb.hit_objects.val.drop x.2.val)
    (fun x => x.1.hit_objects.val.map (abs : _ → OsuHitObject))
    (fun k L => L.modify k Mods.strictTrackingSlider)
    (fun y L => y = (pb.format_version, pb.difficulty, pb.base_difficulty, pb.stack_leniency, pb.audio_lead_in,
      pb.control_points, pb.breaks, y.2.2.2.2.2.2.2.1, pb.epoch, pb.mod_states) ∧ y.2.2.2.2.2.2.2.1.val.map abs = L)
    (by
      rintro ⟨q, k⟩ ⟨hq, hI, hsame⟩ hlt j1 hj1 hj1v
      simp only at hq hI hsame hlt ⊢
      have hl : k.val < q.hit_objects.val.length := by omega
      have hm := list_modify_set (q.hit_objects.val.map (abs : _ → OsuHitObject)) k.val (by simpa using hl)
        Mods.strictTrackingSlider
      have hok : StOk (abs (q.hit_objects.val[k.val]'hl)) := by
        have h1 : q.hit_objects.val[k.val]'hl = (q.hit_objects.val.drop k.val)[0]'(by simp; omega) := by simp
        have hmem : ∀ x ∈ q.hit_objects.val.drop k.val, x ∈ pb.hit_objects.val := by
          rw [hsame]; exact fun x hx => List.mem_of_mem_drop hx
        have h2 := hmem _ (List.getElem_mem (l := q.hit_objects.val.drop k.val) (n := 0) (by simp; omega))
        rw [h1]; exact hst _ h2
      have hdrop : q.hit_objects.val.drop (k.val + 1) = pb.hit_objects.val.drop (k.val + 1) := by
        have := congrArg (List.drop 1) hsame; simpa [List.drop_drop, Nat.add_comm] using this
      cases hsl : (abs (q.hit_objects.val[k.val]'hl) : OsuHitObject).isSlider
      · refine ⟨({ q with hit_objects := q.hit_objects }, j1), ?_, rfl, ?_, ?_⟩
        · simp [beatmap.mods.strict_tracking_loop.body, vec_lt_len_iff, hl, hj1, vec_index_eq _ _ hl,
            beatmap.objects.is_slider_refines, hsl]
        · simp only at hm ⊢
          rw [hm, List.getElem_map, msr_st_nonslider _ hsl, ← List.getElem_map (f := (abs : _ → OsuHitObject)), List.set_getElem_self]
          simpa using hl
        · exact ⟨by rw [hq], hI, by simp only [hj1v]; exact hdrop⟩
      · obtain ⟨o1, ho1, ho1v⟩ := beatmap.mods.strict_tracking_slider_refines (q.hit_objects.val[k.val]'hl) hok h64
        refine ⟨({ q with hit_objects := alloc.vec.Vec.set q.hit_objects k o1 }, j1), ?_, rfl, ?_, ?_⟩
        · simp [beatmap.mods.strict_tracking_loop.body, vec_lt_len_iff, hl, hj1, vec_index_eq _ _ hl,
            beatmap.objects.is_slider_refines, hsl, ho1, vec_index_mut_eq _ _ hl, uncurry_apply_pair]
        · simp only at hm ⊢
          rw [hm]; simp [vec_set_val', List.map_set, ho1v]
        · refine ⟨by rw [hq], by simp [vec_set_val', hI], ?_⟩
          simp only [vec_set_val', hj1v]
          rw [List.drop_set_of_lt (by omega)]; exact hdrop)
    (by
      rintro ⟨q, k⟩ ⟨hq, hI, -⟩ hle
      simp only at hq hI hle ⊢
      have hl : ¬ k < alloc.vec.Vec.len q.hit_objects := by
        show ¬ k.val < (alloc.vec.Vec.len q.hit_objects).val; simp; omega
      refine ⟨(q.format_version, q.difficulty, q.base_difficulty, q.stack_leniency, q.audio_lead_in, q.control_points,
          q.breaks, q.hit_objects, q.epoch, q.mod_states),
        by simp only [beatmap.mods.strict_tracking_loop.body, hl, if_false], ?_, rfl⟩
      rw [hq])
    (pb, 0#usize) ⟨rfl, rfl, rfl⟩ (by simp)
  simp only at hl hv
  obtain ⟨hy1, hy2⟩ := hv
  have := iterR_modify_map Mods.strictTrackingSlider (pb.hit_objects.val.map (abs : _ → OsuHitObject))
  simp only [List.length_map] at this
  rw [show (0#usize : Usize).val = 0 from rfl, this] at hy2
  refine ⟨y.2.2.2.2.2.2.2.1, ?_, hy2⟩
  unfold beatmap.mods.strict_tracking_loop
  rw [hl, hy1]

theorem beatmap.mods.strict_tracking_refines (pb : beatmap.playable.PlayableBeatmap)
    (hst : ∀ h ∈ pb.hit_objects.val, StOk (abs h)) (h64 : System.Platform.numBits = 64) :
    ∃ r, beatmap.mods.strict_tracking pb = ok r ∧ Mods.strictTracking (abs pb) = abs r := by
  obtain ⟨v, hl, hv⟩ := msr_st_loop pb hst h64
  refine ⟨{ pb with hit_objects := v }, by simp only [beatmap.mods.strict_tracking, hl, bind_ok, uncurry_apply_pair], ?_⟩
  unfold Mods.strictTracking
  have e : (abs ({ pb with hit_objects := v } : beatmap.playable.PlayableBeatmap) : PlayableBeatmap) =
      { (abs pb : PlayableBeatmap) with hitObjects := (v.val.map (abs : _ → OsuHitObject)).toArray } := rfl
  have hho : (abs pb : PlayableBeatmap).hitObjects = (pb.hit_objects.val.map (abs : _ → OsuHitObject)).toArray := rfl
  rw [e, hv]
  split
  · rename_i h0
    have hp0 : pb.hit_objects.val = [] := by rw [hho] at h0; simpa using h0
    have hv0 : (v.val.map (abs : _ → OsuHitObject)).toArray = #[] := by rw [hv, hp0]; rfl
    have hh0 : (abs pb : PlayableBeatmap).hitObjects = #[] := by rw [hho, hp0]; rfl
    rw [hp0]; simp only [List.map_nil]
    rw [show (([] : List OsuHitObject).toArray) = #[] from rfl, ← hh0]
  · rw [hho]; simp

theorem beatmap.mods.apply_after_conversion_refines (m : beatmap.mod_settings.ModConfig) (hv : AcrOk m)
    (pb : beatmap.playable.PlayableBeatmap) (hst : ∀ h ∈ pb.hit_objects.val, StOk (abs h))
    (h64 : System.Platform.numBits = 64) :
    ∃ r, beatmap.mods.apply_after_conversion m pb = ok r ∧
      ((mcS m).hooks.applyAfterConversion.getD id) (abs pb) = abs r := by
  unfold beatmap.mods.apply_after_conversion
  simp only [lift, bind_ok, mods_acr m hv _ _ _ _ se_ST]
  unfold ModConfig.hooks
  by_cases hkn : m.known = true
  · simp only [hkn, Bool.true_and]
    have hmk : (mcS m).known = true := hkn
    simp only [hmk, Bool.not_true, Bool.false_eq_true, if_false]
    have hacr : (mcS m).acronym = vstrS m.acronym := rfl
    rw [hacr]
    generalize hA : vstrS m.acronym = A
    by_cases a_ST : A = "ST"
    · subst a_ST
      obtain ⟨r, hr, hrv⟩ := beatmap.mods.strict_tracking_refines pb hst h64
      exact ⟨r, by simp [hr], hrv⟩
    refine ⟨pb, by simp [a_ST], ?_⟩
    split
    all_goals first | rfl | (exfalso; contradiction)
  · have : m.known = false := by simpa using hkn
    have hmk : (mcS m).known = false := this
    simp only [this, Bool.false_and, Bool.false_eq_true, if_false, hmk, Bool.not_false, if_true]
    exact ⟨pb, rfl, rfl⟩

end OsuProofs
