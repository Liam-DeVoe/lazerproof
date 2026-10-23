/-
`beatmap::objects::apply_defaults` (Rust) refines `applyDefaults` (mods proof agent; abs-style).
-/
import OsuProofs.Post.ObjectsSort
import OsuProofs.Beatmap.Objects
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

theorem oa_loop0 (cpi : beatmap.control_points.ControlPointInfo) (d : beatmap.types.Difficulty) (st sd : F64)
    (nested : alloc.vec.Vec beatmap.objects.NestedObject) (hcpi : cpi.effect_points.val.length < 2^31) :
    ∃ r, beatmap.objects.apply_defaults_loop0 cpi d st nested sd 0#usize = ok r ∧
      (abs r : Array NestedObject) = (abs nested : Array NestedObject).map (applyNestedDefaults (abs cpi) (abs d) st sd) := by
  obtain ⟨v, hl, hv⟩ := loop_fold_gen' (fun x => beatmap.objects.apply_defaults_loop0.body cpi d st sd x.1 x.2) (·.2)
    nested.val.length (by have := nested.property; omega)
    (fun x => x.1.val.length = nested.val.length) (fun x => x.1.val.map (abs : _ → NestedObject))
    (fun k L => L.modify k (applyNestedDefaults (abs cpi) (abs d) st sd)) (fun y L => y.val.map abs = L)
    (by
      intro t hI hlt j1 hj1 hj1v
      have hl : t.2.val < t.1.val.length := by omega
      obtain ⟨n1, hn1, hn1v⟩ := beatmap.objects.apply_nested_defaults_refines cpi d st sd (t.1.val[t.2.val]'hl) hcpi
      refine ⟨(alloc.vec.Vec.set t.1 t.2 n1, j1), ?_, rfl, ?_, ?_⟩
      · simp [beatmap.objects.apply_defaults_loop0.body, vec_lt_len_iff, hl, hj1, vec_index_mut_eq _ _ hl, hn1,
          uncurry_apply_pair]
      · have hm := list_modify_set (t.1.val.map (abs : _ → NestedObject)) t.2.val (by simpa using hl)
          (applyNestedDefaults (abs cpi) (abs d) st sd)
        simp only at hm ⊢
        rw [hm]; simp [vec_set_val', List.map_set, hn1v]
      · simp [vec_set_val', hI])
    (by loop_end [beatmap.objects.apply_defaults_loop0.body])
    (nested, 0#usize) rfl (by simp)
  simp only at hl hv
  have := iterR_modify_map (applyNestedDefaults (abs cpi) (abs d) st sd) (nested.val.map (abs : _ → NestedObject))
  simp only [List.length_map] at this
  rw [show (0#usize : Usize).val = 0 from rfl, this] at hv
  refine ⟨v, by unfold beatmap.objects.apply_defaults_loop0; exact hl, ?_⟩
  have e1 : (abs v : Array NestedObject) = (v.val.map (abs : _ → NestedObject)).toArray := rfl
  have e2 : (abs nested : Array NestedObject) = (nested.val.map (abs : _ → NestedObject)).toArray := rfl
  rw [e1, e2, hv]; simp

theorem oa_loop1 (cpi : beatmap.control_points.ControlPointInfo) (d : beatmap.types.Difficulty) (st sd : F64)
    (nested : alloc.vec.Vec beatmap.objects.NestedObject) (hcpi : cpi.effect_points.val.length < 2^31) :
    ∃ r, beatmap.objects.apply_defaults_loop1 cpi d st nested sd 0#usize = ok r ∧
      (abs r : Array NestedObject) = (abs nested : Array NestedObject).map (applyNestedDefaults (abs cpi) (abs d) st sd) := by
  obtain ⟨v, hl, hv⟩ := loop_fold_gen' (fun x => beatmap.objects.apply_defaults_loop1.body cpi d st sd x.1 x.2) (·.2)
    nested.val.length (by have := nested.property; omega)
    (fun x => x.1.val.length = nested.val.length) (fun x => x.1.val.map (abs : _ → NestedObject))
    (fun k L => L.modify k (applyNestedDefaults (abs cpi) (abs d) st sd)) (fun y L => y.val.map abs = L)
    (by
      intro t hI hlt j1 hj1 hj1v
      have hl : t.2.val < t.1.val.length := by omega
      obtain ⟨n1, hn1, hn1v⟩ := beatmap.objects.apply_nested_defaults_refines cpi d st sd (t.1.val[t.2.val]'hl) hcpi
      refine ⟨(alloc.vec.Vec.set t.1 t.2 n1, j1), ?_, rfl, ?_, ?_⟩
      · simp [beatmap.objects.apply_defaults_loop1.body, vec_lt_len_iff, hl, hj1, vec_index_mut_eq _ _ hl, hn1,
          uncurry_apply_pair]
      · have hm := list_modify_set (t.1.val.map (abs : _ → NestedObject)) t.2.val (by simpa using hl)
          (applyNestedDefaults (abs cpi) (abs d) st sd)
        simp only at hm ⊢
        rw [hm]; simp [vec_set_val', List.map_set, hn1v]
      · simp [vec_set_val', hI])
    (by loop_end [beatmap.objects.apply_defaults_loop1.body])
    (nested, 0#usize) rfl (by simp)
  simp only at hl hv
  have := iterR_modify_map (applyNestedDefaults (abs cpi) (abs d) st sd) (nested.val.map (abs : _ → NestedObject))
  simp only [List.length_map] at this
  rw [show (0#usize : Usize).val = 0 from rfl, this] at hv
  refine ⟨v, by unfold beatmap.objects.apply_defaults_loop1; exact hl, ?_⟩
  have e1 : (abs v : Array NestedObject) = (v.val.map (abs : _ → NestedObject)).toArray := rfl
  have e2 : (abs nested : Array NestedObject) = (nested.val.map (abs : _ → NestedObject)).toArray := rfl
  rw [e1, e2, hv]; simp

theorem oa_loop2 (cpi : beatmap.control_points.ControlPointInfo) (d : beatmap.types.Difficulty) (st sd : F64)
    (nested : alloc.vec.Vec beatmap.objects.NestedObject) (hcpi : cpi.effect_points.val.length < 2^31) :
    ∃ r, beatmap.objects.apply_defaults_loop2 cpi d st nested sd 0#usize = ok r ∧
      (abs r : Array NestedObject) = (abs nested : Array NestedObject).map (applyNestedDefaults (abs cpi) (abs d) st sd) := by
  obtain ⟨v, hl, hv⟩ := loop_fold_gen' (fun x => beatmap.objects.apply_defaults_loop2.body cpi d st sd x.1 x.2) (·.2)
    nested.val.length (by have := nested.property; omega)
    (fun x => x.1.val.length = nested.val.length) (fun x => x.1.val.map (abs : _ → NestedObject))
    (fun k L => L.modify k (applyNestedDefaults (abs cpi) (abs d) st sd)) (fun y L => y.val.map abs = L)
    (by
      intro t hI hlt j1 hj1 hj1v
      have hl : t.2.val < t.1.val.length := by omega
      obtain ⟨n1, hn1, hn1v⟩ := beatmap.objects.apply_nested_defaults_refines cpi d st sd (t.1.val[t.2.val]'hl) hcpi
      refine ⟨(alloc.vec.Vec.set t.1 t.2 n1, j1), ?_, rfl, ?_, ?_⟩
      · simp [beatmap.objects.apply_defaults_loop2.body, vec_lt_len_iff, hl, hj1, vec_index_mut_eq _ _ hl, hn1,
          uncurry_apply_pair]
      · have hm := list_modify_set (t.1.val.map (abs : _ → NestedObject)) t.2.val (by simpa using hl)
          (applyNestedDefaults (abs cpi) (abs d) st sd)
        simp only at hm ⊢
        rw [hm]; simp [vec_set_val', List.map_set, hn1v]
      · simp [vec_set_val', hI])
    (by loop_end [beatmap.objects.apply_defaults_loop2.body])
    (nested, 0#usize) rfl (by simp)
  simp only at hl hv
  have := iterR_modify_map (applyNestedDefaults (abs cpi) (abs d) st sd) (nested.val.map (abs : _ → NestedObject))
  simp only [List.length_map] at this
  rw [show (0#usize : Usize).val = 0 from rfl, this] at hv
  refine ⟨v, by unfold beatmap.objects.apply_defaults_loop2; exact hl, ?_⟩
  have e1 : (abs v : Array NestedObject) = (v.val.map (abs : _ → NestedObject)).toArray := rfl
  have e2 : (abs nested : Array NestedObject) = (nested.val.map (abs : _ → NestedObject)).toArray := rfl
  rw [e1, e2, hv]; simp


theorem oa_ho_abs (x : beatmap.objects.OsuHitObject) : (abs x : OsuHitObject) =
    { kind := abs x.kind, startTime := abs x.start_time, position := abs x.position, stackHeight := abs x.stack_height,
      scale := abs x.scale, timePreempt := abs x.time_preempt, timeFadeIn := abs x.time_fade_in, newCombo := abs x.new_combo,
      comboOffset := abs x.combo_offset, comboIndex := abs x.combo_index,
      comboIndexWithOffsets := abs x.combo_index_with_offsets, indexInCurrentCombo := abs x.index_in_current_combo,
      lastInCombo := abs x.last_in_combo, kiai := abs x.kiai, hitWindows := abs x.hit_windows, nested := abs x.nested } := rfl

/-- the Rust object after the common/kind defaults (before the nested objects) -/
def oaObj (h : beatmap.objects.OsuHitObject) (d : beatmap.types.Difficulty) (cpi : beatmap.control_points.ControlPointInfo)
    (k : beatmap.objects.ObjectKind) (hw : beatmap.objects.HitWindows) : beatmap.objects.OsuHitObject :=
  { kind := k, start_time := h.start_time, position := h.position, stack_height := h.stack_height,
    scale := calculateScaleFromCircleSize d.circle_size true, time_preempt := timePreemptFor d.approach_rate,
    time_fade_in := timeFadeInFor (timePreemptFor d.approach_rate), new_combo := h.new_combo,
    combo_offset := h.combo_offset, combo_index := h.combo_index, combo_index_with_offsets := h.combo_index_with_offsets,
    index_in_current_combo := h.index_in_current_combo, last_in_combo := h.last_in_combo,
    kiai := (epI ((cpS cpi).effectPointAt (h.start_time + 1))).kiai, hit_windows := some hw, nested := h.nested }

theorem oaObj_fold (h : beatmap.objects.OsuHitObject) (d : beatmap.types.Difficulty)
    (cpi : beatmap.control_points.ControlPointInfo) (k : beatmap.objects.ObjectKind) (hw : beatmap.objects.HitWindows) :
    ({ kind := k, start_time := h.start_time, position := h.position, stack_height := h.stack_height, scale := calculateScaleFromCircleSize d.circle_size true, time_preempt := timePreemptFor d.approach_rate, time_fade_in := timeFadeInFor (timePreemptFor d.approach_rate), new_combo := h.new_combo, combo_offset := h.combo_offset, combo_index := h.combo_index, combo_index_with_offsets := h.combo_index_with_offsets, index_in_current_combo := h.index_in_current_combo, last_in_combo := h.last_in_combo, kiai := (epI ((cpS cpi).effectPointAt (h.start_time + 1))).kiai, hit_windows := some hw, nested := h.nested} :
      beatmap.objects.OsuHitObject) = oaObj h d cpi k hw := rfl

theorem oaObj_fold' (h : beatmap.objects.OsuHitObject) (d : beatmap.types.Difficulty)
    (cpi : beatmap.control_points.ControlPointInfo) (k : beatmap.objects.ObjectKind) (hw : beatmap.objects.HitWindows)
    (n : alloc.vec.Vec beatmap.objects.NestedObject) :
    ({ kind := k, start_time := h.start_time, position := h.position, stack_height := h.stack_height, scale := calculateScaleFromCircleSize d.circle_size true, time_preempt := timePreemptFor d.approach_rate, time_fade_in := timeFadeInFor (timePreemptFor d.approach_rate), new_combo := h.new_combo, combo_offset := h.combo_offset, combo_index := h.combo_index, combo_index_with_offsets := h.combo_index_with_offsets, index_in_current_combo := h.index_in_current_combo, last_in_combo := h.last_in_combo, kiai := (epI ((cpS cpi).effectPointAt (h.start_time + 1))).kiai, hit_windows := some hw, nested := n} :
      beatmap.objects.OsuHitObject) = { oaObj h d cpi k hw with nested := n } := rfl

theorem oa_abs_obj (h : beatmap.objects.OsuHitObject) (d : beatmap.types.Difficulty)
    (cpi : beatmap.control_points.ControlPointInfo) (k : beatmap.objects.ObjectKind) (hw : beatmap.objects.HitWindows) :
    ({ kind := abs k, startTime := (abs h : OsuHitObject).startTime, position := (abs h : OsuHitObject).position, stackHeight := (abs h : OsuHitObject).stackHeight, scale := (commonDefaults (abs d)).scale, timePreempt := (commonDefaults (abs d)).timePreempt, timeFadeIn := (commonDefaults (abs d)).timeFadeIn, newCombo := (abs h : OsuHitObject).newCombo, comboOffset := (abs h : OsuHitObject).comboOffset, comboIndex := (abs h : OsuHitObject).comboIndex, comboIndexWithOffsets := (abs h : OsuHitObject).comboIndexWithOffsets, indexInCurrentCombo := (abs h : OsuHitObject).indexInCurrentCombo, lastInCombo := (abs h : OsuHitObject).lastInCombo, kiai := ((abs cpi : ControlPointInfo).effectPointAt ((abs h : OsuHitObject).startTime + 1)).kiai, hitWindows := some (abs hw), nested := (abs h : OsuHitObject).nested } : OsuHitObject) =
      abs (oaObj h d cpi k hw) := by
  rw [oa_ho_abs]; simp only [OsuHitObject.mk.injEq]
  and_intros
  all_goals try rfl

theorem oa_hw_empty : (abs beatmap.objects.HitWindows.Empty : HitWindows) = .empty := rfl
theorem oa_hw_osu (a b c : F64) : (abs (beatmap.objects.HitWindows.Osu a b c) : HitWindows) = .osu a b c := rfl

theorem oa_abs_obj2 (h : beatmap.objects.OsuHitObject) (d : beatmap.types.Difficulty)
    (cpi : beatmap.control_points.ControlPointInfo) (k : beatmap.objects.ObjectKind) (hw : beatmap.objects.HitWindows) :
    ({ kind := abs k, startTime := h.start_time, position := (abs h : OsuHitObject).position, stackHeight := (abs h : OsuHitObject).stackHeight, scale := (commonDefaults (abs d)).scale, timePreempt := (commonDefaults (abs d)).timePreempt, timeFadeIn := (commonDefaults (abs d)).timeFadeIn, newCombo := (abs h : OsuHitObject).newCombo, comboOffset := (abs h : OsuHitObject).comboOffset, comboIndex := (abs h : OsuHitObject).comboIndex, comboIndexWithOffsets := (abs h : OsuHitObject).comboIndexWithOffsets, indexInCurrentCombo := (abs h : OsuHitObject).indexInCurrentCombo, lastInCombo := (abs h : OsuHitObject).lastInCombo, kiai := ((cpS cpi).effectPointAt (h.start_time + 1)).kiai, hitWindows := some (abs hw), nested := (abs h : OsuHitObject).nested } : OsuHitObject) =
      abs (oaObj h d cpi k hw) := by
  rw [← oa_abs_obj, ob_abs_cpi]; rfl

set_option maxHeartbeats 1600000 in
theorem beatmap.objects.apply_defaults_refines (cpi : beatmap.control_points.ControlPointInfo)
    (d : beatmap.types.Difficulty) (h : beatmap.objects.OsuHitObject)
    (hce : cpi.effect_points.val.length < 2^31) (hct : cpi.timing_points.val.length < 2^31)
    (hp : ∀ s, h.kind = .Slider s → obPathOk s.path) (h64 : System.Platform.numBits = 64)
    (hN : ∀ r, applyDefaults (abs cpi) (abs d) (abs h) = .ok r → r.nested.size < 2^31) :
    ∃ e o, beatmap.objects.apply_defaults cpi d h = ok (e, o) ∧
      hRel (fun _ => (abs o : OsuHitObject)) e (applyDefaults (abs cpi) (abs d) (abs h)) := by
  obtain ⟨ohw, hohw, hohwv⟩ := beatmap.objects.osu_hit_windows_refines (F32.toF64 d.overall_difficulty)
  have hod : (abs d : Difficulty).overallDifficulty = d.overall_difficulty := rfl
  have hst : (abs h : OsuHitObject).startTime = h.start_time := rfl
  have hhw : (abs h : OsuHitObject).hitWindows = h.hit_windows.map abs := rfl
  have hkd : (abs h : OsuHitObject).kind = abs h.kind := rfl
  have hep := beatmap.control_points.effect_point_at_refines cpi (h.start_time + 1) hce
  obtain ⟨oa, ob, oc, rfl⟩ : ∃ a b c, ohw = .Osu a b c := by
    cases ohw with
    | Empty => simp [osuHitWindows, abs] at hohwv
    | Osu a b c => exact ⟨a, b, c, rfl⟩
  obtain ⟨sn0, hsn0, hsn0v, hsn0l⟩ := beatmap.objects.sort_nested_refines (alloc.vec.Vec.new beatmap.objects.NestedObject)
    (by simp)
  choose L0 hL0 hL0v using fun sd (nested : alloc.vec.Vec beatmap.objects.NestedObject) => oa_loop0 cpi d h.start_time sd nested hce
  choose L1 hL1 hL1v using fun sd (nested : alloc.vec.Vec beatmap.objects.NestedObject) => oa_loop1 cpi d h.start_time sd nested hce
  choose L2 hL2 hL2v using fun sd (nested : alloc.vec.Vec beatmap.objects.NestedObject) => oa_loop2 cpi d h.start_time sd nested hce
  choose SD hSD hSDv using fun s => beatmap.objects.spinner_defaults_refines d s
  choose SN hSN hSNv using fun H s => beatmap.objects.spinner_nested_refines H s
  unfold beatmap.objects.apply_defaults applyDefaults
  simp only [ob_cd_eq, bind_ok, float.F32.to_f64, hohw, bmc_beatmap_objects_D1, float.F64.add, hep, uncurry_apply_pair]
  cases hk : h.kind with
  | Circle =>
    cases hw : h.hit_windows with
    | none =>
      simp only [hw, hk, hohw, bind_ok, uncurry_apply_pair, hsn0, beatmap.objects.span_duration_refines, hL0]
      refine ⟨_, _, rfl, ?_⟩
      simp only [hkd, hk, ob_abs_circle, hhw, hw, Option.map_none, Option.map_some, hod, ← hohwv, pure_bind]
      show (abs _ : OsuHitObject) = _
      rw [oa_ho_abs]
      simp only [OsuHitObject.mk.injEq]
      and_intros
      all_goals try rfl
      all_goals first | (rw [hohwv]; rfl) | (rw [hL0v, ← hsn0v]; congr 2)
    | some w =>
      cases w with
      | Empty =>
        simp only [hw, hk, hohw, bind_ok, uncurry_apply_pair, hsn0, beatmap.objects.span_duration_refines, hL0]
        refine ⟨_, _, rfl, ?_⟩
        simp only [hkd, hk, ob_abs_circle, hhw, hw, Option.map_none, Option.map_some, hod, ← hohwv, pure_bind]
        show (abs _ : OsuHitObject) = _
        rw [oa_ho_abs]
        simp only [OsuHitObject.mk.injEq]
        and_intros
        all_goals try rfl
        all_goals first | (rw [hohwv]; rfl) | (rw [hL0v, ← hsn0v]; congr 2)
      | Osu wa wb wc =>
        simp only [hw, hk, hohw, bind_ok, uncurry_apply_pair, hsn0, beatmap.objects.span_duration_refines, hL0]
        refine ⟨_, _, rfl, ?_⟩
        simp only [hkd, hk, ob_abs_circle, hhw, hw, Option.map_none, Option.map_some, hod, ← hohwv, pure_bind]
        show (abs _ : OsuHitObject) = _
        rw [oa_ho_abs]
        simp only [OsuHitObject.mk.injEq]
        and_intros
        all_goals try rfl
        all_goals first | (rw [hohwv]; rfl) | (rw [hL0v, ← hsn0v]; congr 2)
  | Slider s =>
    have htp := beatmap.control_points.timing_point_at_refines cpi h.start_time hct
    cases hw : h.hit_windows with
    | none =>
      simp only [hw, hk, bind_ok, uncurry_apply_pair, htp, bmc_beatmap_objects_BASE_SCORING_DISTANCE,
        beatmap.objects.get_precision_adjusted_beat_length_refines, float.F64.mul, float.F64.div, hohw]
      have hinf : float.F64.from_bits 9218868437227405312#u64 = ok F64.posInf := by
        simp [float.F64.from_bits]; rfl
      have hsa : (abs h : OsuHitObject).kind = .slider (abs s) := by rw [hkd, hk]; rfl
      unfold applyDefaults at hN
      simp only [hkd, hk, hhw, hw, Option.map_none, Option.map_some, hod, oa_hw_osu, oa_hw_empty, ← hohwv, pure_bind,
        ob_abs_slider, ob_abs_cpi, hst] at hN ⊢
      have hgt : (abs s : SliderData).generateTicks = s.generate_ticks := rfl
      rw [hgt] at hN ⊢
      have hV : BASE_SCORING_DISTANCE.toF64 * (abs d : Difficulty).sliderMultiplier / getPrecisionAdjustedBeatLength (abs s : SliderData).sliderVelocityMultiplier ((cpS cpi).timingPointAt h.start_time) = F32.toF64 100 * d.slider_multiplier / getPrecisionAdjustedBeatLength s.slider_velocity_multiplier (abs (tpI ((cpS cpi).timingPointAt h.start_time))) := rfl
      rw [hV] at hN ⊢
      generalize F32.toF64 100 * d.slider_multiplier / getPrecisionAdjustedBeatLength s.slider_velocity_multiplier (abs (tpI ((cpS cpi).timingPointAt h.start_time))) = V at hN ⊢
      have hT : V * ((cpS cpi).timingPointAt h.start_time).beatLength / (abs d : Difficulty).sliderTickRate * (abs s : SliderData).tickDistanceMultiplier = V * (tpI ((cpS cpi).timingPointAt h.start_time)).beat_length / d.slider_tick_rate * s.tick_distance_multiplier := rfl
      rw [hT] at hN ⊢
      have hTv : ∃ T, (if s.generate_ticks = true then ok (V * (tpI ((cpS cpi).timingPointAt h.start_time)).beat_length / d.slider_tick_rate * s.tick_distance_multiplier) else float.F64.from_bits 9218868437227405312#u64) = ok T ∧ (if s.generate_ticks = true then V * (tpI ((cpS cpi).timingPointAt h.start_time)).beat_length / d.slider_tick_rate * s.tick_distance_multiplier else F64.posInf) = T := by
        cases s.generate_ticks
        · simp only [Bool.false_eq_true, if_false]; exact ⟨_, hinf, rfl⟩
        · simp only [if_true]; exact ⟨_, rfl, rfl⟩
      obtain ⟨T, hT1, hT2⟩ := hTv
      rw [hT2] at hN ⊢
      simp only [hT1, bind_ok, uncurry_apply_pair]
      simp only [oaObj_fold]
      have hS : ({ path := (abs s : SliderData).path, repeatCount := (abs s : SliderData).repeatCount, velocity := V, tickDistance := T, tickDistanceMultiplier := (abs s : SliderData).tickDistanceMultiplier, sliderVelocityMultiplier := (abs s : SliderData).sliderVelocityMultiplier, generateTicks := s.generate_ticks, classicSliderBehaviour := (abs s : SliderData).classicSliderBehaviour, strictTracking := (abs s : SliderData).strictTracking } : SliderData) = abs ({ s with velocity := V, tick_distance := T } : beatmap.objects.SliderData) := rfl
      rw [hS] at hN ⊢
      have hpS : obPathOk ({ s with velocity := V, tick_distance := T } : beatmap.objects.SliderData).path := hp s hk
      generalize ({ s with velocity := V, tick_distance := T } : beatmap.objects.SliderData) = S' at hN hpS ⊢
      rw [← ob_abs_slider, show HitWindows.empty = abs beatmap.objects.HitWindows.Empty from rfl] at hN ⊢
      simp only [oa_abs_obj2] at hN ⊢
      have hph : ∀ s'', (oaObj h d cpi (.Slider S') .Empty).kind = .Slider s'' → obPathOk s''.path := by
        intro s'' e; simp only [oaObj, beatmap.objects.ObjectKind.Slider.injEq] at e; subst e; exact hpS
      generalize oaObj h d cpi (.Slider S') .Empty = O at hN hph ⊢
      obtain ⟨r, hr, hrv⟩ := beatmap.objects.slider_nested_refines O S' hpS hph h64
      cases hsn : sliderNested (abs O) (abs S') with
      | error msg =>
        rw [hsn] at hrv
        cases r with
        | Ok v => exact absurd hrv (by simp [hRel])
        | Err e => exact ⟨.Err e, O, by rw [hr, bind_ok], trivial⟩
      | ok arr =>
        rw [hsn] at hrv hN
        cases r with
        | Err e => exact absurd hrv (by simp [hRel])
        | Ok v =>
          have hva : (abs v : Array NestedObject) = arr := hrv
          have hb : v.val.length < 2^31 := by
            have := hN _ rfl
            simp only [Array.size_map, sort_nested_size, ← hva] at this
            simpa [abs] using this
          obtain ⟨n1, hn1, hn1v, -⟩ := beatmap.objects.sort_nested_refines _ hb
          refine ⟨_, _, by rw [hr, bind_ok]; simp only [hn1, bind_ok, beatmap.objects.span_duration_refines, hL1]; rfl, ?_⟩
          show (abs _ : OsuHitObject) = _
          rw [oa_ho_abs]; simp only [OsuHitObject.mk.injEq]
          and_intros
          all_goals first | rfl | trivial | (rw [hL1v, ← hn1v, hva]; rfl)
    | some w =>
      cases w with
      | Empty =>
        simp only [hw, hk, bind_ok, uncurry_apply_pair, htp, bmc_beatmap_objects_BASE_SCORING_DISTANCE,
          beatmap.objects.get_precision_adjusted_beat_length_refines, float.F64.mul, float.F64.div, hohw]
        have hinf : float.F64.from_bits 9218868437227405312#u64 = ok F64.posInf := by
          simp [float.F64.from_bits]; rfl
        have hsa : (abs h : OsuHitObject).kind = .slider (abs s) := by rw [hkd, hk]; rfl
        unfold applyDefaults at hN
        simp only [hkd, hk, hhw, hw, Option.map_none, Option.map_some, hod, oa_hw_osu, oa_hw_empty, ← hohwv, pure_bind,
          ob_abs_slider, ob_abs_cpi, hst] at hN ⊢
        have hgt : (abs s : SliderData).generateTicks = s.generate_ticks := rfl
        rw [hgt] at hN ⊢
        have hV : BASE_SCORING_DISTANCE.toF64 * (abs d : Difficulty).sliderMultiplier / getPrecisionAdjustedBeatLength (abs s : SliderData).sliderVelocityMultiplier ((cpS cpi).timingPointAt h.start_time) = F32.toF64 100 * d.slider_multiplier / getPrecisionAdjustedBeatLength s.slider_velocity_multiplier (abs (tpI ((cpS cpi).timingPointAt h.start_time))) := rfl
        rw [hV] at hN ⊢
        generalize F32.toF64 100 * d.slider_multiplier / getPrecisionAdjustedBeatLength s.slider_velocity_multiplier (abs (tpI ((cpS cpi).timingPointAt h.start_time))) = V at hN ⊢
        have hT : V * ((cpS cpi).timingPointAt h.start_time).beatLength / (abs d : Difficulty).sliderTickRate * (abs s : SliderData).tickDistanceMultiplier = V * (tpI ((cpS cpi).timingPointAt h.start_time)).beat_length / d.slider_tick_rate * s.tick_distance_multiplier := rfl
        rw [hT] at hN ⊢
        have hTv : ∃ T, (if s.generate_ticks = true then ok (V * (tpI ((cpS cpi).timingPointAt h.start_time)).beat_length / d.slider_tick_rate * s.tick_distance_multiplier) else float.F64.from_bits 9218868437227405312#u64) = ok T ∧ (if s.generate_ticks = true then V * (tpI ((cpS cpi).timingPointAt h.start_time)).beat_length / d.slider_tick_rate * s.tick_distance_multiplier else F64.posInf) = T := by
          cases s.generate_ticks
          · simp only [Bool.false_eq_true, if_false]; exact ⟨_, hinf, rfl⟩
          · simp only [if_true]; exact ⟨_, rfl, rfl⟩
        obtain ⟨T, hT1, hT2⟩ := hTv
        rw [hT2] at hN ⊢
        simp only [hT1, bind_ok, uncurry_apply_pair]
        simp only [oaObj_fold]
        have hS : ({ path := (abs s : SliderData).path, repeatCount := (abs s : SliderData).repeatCount, velocity := V, tickDistance := T, tickDistanceMultiplier := (abs s : SliderData).tickDistanceMultiplier, sliderVelocityMultiplier := (abs s : SliderData).sliderVelocityMultiplier, generateTicks := s.generate_ticks, classicSliderBehaviour := (abs s : SliderData).classicSliderBehaviour, strictTracking := (abs s : SliderData).strictTracking } : SliderData) = abs ({ s with velocity := V, tick_distance := T } : beatmap.objects.SliderData) := rfl
        rw [hS] at hN ⊢
        have hpS : obPathOk ({ s with velocity := V, tick_distance := T } : beatmap.objects.SliderData).path := hp s hk
        generalize ({ s with velocity := V, tick_distance := T } : beatmap.objects.SliderData) = S' at hN hpS ⊢
        rw [← ob_abs_slider, show HitWindows.empty = abs beatmap.objects.HitWindows.Empty from rfl] at hN ⊢
        simp only [oa_abs_obj2] at hN ⊢
        have hph : ∀ s'', (oaObj h d cpi (.Slider S') .Empty).kind = .Slider s'' → obPathOk s''.path := by
          intro s'' e; simp only [oaObj, beatmap.objects.ObjectKind.Slider.injEq] at e; subst e; exact hpS
        generalize oaObj h d cpi (.Slider S') .Empty = O at hN hph ⊢
        obtain ⟨r, hr, hrv⟩ := beatmap.objects.slider_nested_refines O S' hpS hph h64
        cases hsn : sliderNested (abs O) (abs S') with
        | error msg =>
          rw [hsn] at hrv
          cases r with
          | Ok v => exact absurd hrv (by simp [hRel])
          | Err e => exact ⟨.Err e, O, by rw [hr, bind_ok], trivial⟩
        | ok arr =>
          rw [hsn] at hrv hN
          cases r with
          | Err e => exact absurd hrv (by simp [hRel])
          | Ok v =>
            have hva : (abs v : Array NestedObject) = arr := hrv
            have hb : v.val.length < 2^31 := by
              have := hN _ rfl
              simp only [Array.size_map, sort_nested_size, ← hva] at this
              simpa [abs] using this
            obtain ⟨n1, hn1, hn1v, -⟩ := beatmap.objects.sort_nested_refines _ hb
            refine ⟨_, _, by rw [hr, bind_ok]; simp only [hn1, bind_ok, beatmap.objects.span_duration_refines, hL1]; rfl, ?_⟩
            show (abs _ : OsuHitObject) = _
            rw [oa_ho_abs]; simp only [OsuHitObject.mk.injEq]
            and_intros
            all_goals first | rfl | trivial | (rw [hL1v, ← hn1v, hva]; rfl)
      | Osu wa wb wc =>
        simp only [hw, hk, bind_ok, uncurry_apply_pair, htp, bmc_beatmap_objects_BASE_SCORING_DISTANCE,
          beatmap.objects.get_precision_adjusted_beat_length_refines, float.F64.mul, float.F64.div, hohw]
        have hinf : float.F64.from_bits 9218868437227405312#u64 = ok F64.posInf := by
          simp [float.F64.from_bits]; rfl
        have hsa : (abs h : OsuHitObject).kind = .slider (abs s) := by rw [hkd, hk]; rfl
        unfold applyDefaults at hN
        simp only [hkd, hk, hhw, hw, Option.map_none, Option.map_some, hod, oa_hw_osu, oa_hw_empty, ← hohwv, pure_bind,
          ob_abs_slider, ob_abs_cpi, hst] at hN ⊢
        have hgt : (abs s : SliderData).generateTicks = s.generate_ticks := rfl
        rw [hgt] at hN ⊢
        have hV : BASE_SCORING_DISTANCE.toF64 * (abs d : Difficulty).sliderMultiplier / getPrecisionAdjustedBeatLength (abs s : SliderData).sliderVelocityMultiplier ((cpS cpi).timingPointAt h.start_time) = F32.toF64 100 * d.slider_multiplier / getPrecisionAdjustedBeatLength s.slider_velocity_multiplier (abs (tpI ((cpS cpi).timingPointAt h.start_time))) := rfl
        rw [hV] at hN ⊢
        generalize F32.toF64 100 * d.slider_multiplier / getPrecisionAdjustedBeatLength s.slider_velocity_multiplier (abs (tpI ((cpS cpi).timingPointAt h.start_time))) = V at hN ⊢
        have hT : V * ((cpS cpi).timingPointAt h.start_time).beatLength / (abs d : Difficulty).sliderTickRate * (abs s : SliderData).tickDistanceMultiplier = V * (tpI ((cpS cpi).timingPointAt h.start_time)).beat_length / d.slider_tick_rate * s.tick_distance_multiplier := rfl
        rw [hT] at hN ⊢
        have hTv : ∃ T, (if s.generate_ticks = true then ok (V * (tpI ((cpS cpi).timingPointAt h.start_time)).beat_length / d.slider_tick_rate * s.tick_distance_multiplier) else float.F64.from_bits 9218868437227405312#u64) = ok T ∧ (if s.generate_ticks = true then V * (tpI ((cpS cpi).timingPointAt h.start_time)).beat_length / d.slider_tick_rate * s.tick_distance_multiplier else F64.posInf) = T := by
          cases s.generate_ticks
          · simp only [Bool.false_eq_true, if_false]; exact ⟨_, hinf, rfl⟩
          · simp only [if_true]; exact ⟨_, rfl, rfl⟩
        obtain ⟨T, hT1, hT2⟩ := hTv
        rw [hT2] at hN ⊢
        simp only [hT1, bind_ok, uncurry_apply_pair]
        simp only [oaObj_fold]
        have hS : ({ path := (abs s : SliderData).path, repeatCount := (abs s : SliderData).repeatCount, velocity := V, tickDistance := T, tickDistanceMultiplier := (abs s : SliderData).tickDistanceMultiplier, sliderVelocityMultiplier := (abs s : SliderData).sliderVelocityMultiplier, generateTicks := s.generate_ticks, classicSliderBehaviour := (abs s : SliderData).classicSliderBehaviour, strictTracking := (abs s : SliderData).strictTracking } : SliderData) = abs ({ s with velocity := V, tick_distance := T } : beatmap.objects.SliderData) := rfl
        rw [hS] at hN ⊢
        have hpS : obPathOk ({ s with velocity := V, tick_distance := T } : beatmap.objects.SliderData).path := hp s hk
        generalize ({ s with velocity := V, tick_distance := T } : beatmap.objects.SliderData) = S' at hN hpS ⊢
        rw [← ob_abs_slider, hohwv] at hN ⊢
        simp only [oa_abs_obj2] at hN ⊢
        have hph : ∀ s'', (oaObj h d cpi (.Slider S') (.Osu oa ob oc)).kind = .Slider s'' → obPathOk s''.path := by
          intro s'' e; simp only [oaObj, beatmap.objects.ObjectKind.Slider.injEq] at e; subst e; exact hpS
        generalize oaObj h d cpi (.Slider S') (.Osu oa ob oc) = O at hN hph ⊢
        obtain ⟨r, hr, hrv⟩ := beatmap.objects.slider_nested_refines O S' hpS hph h64
        cases hsn : sliderNested (abs O) (abs S') with
        | error msg =>
          rw [hsn] at hrv
          cases r with
          | Ok v => exact absurd hrv (by simp [hRel])
          | Err e => exact ⟨.Err e, O, by rw [hr, bind_ok], trivial⟩
        | ok arr =>
          rw [hsn] at hrv hN
          cases r with
          | Err e => exact absurd hrv (by simp [hRel])
          | Ok v =>
            have hva : (abs v : Array NestedObject) = arr := hrv
            have hb : v.val.length < 2^31 := by
              have := hN _ rfl
              simp only [Array.size_map, sort_nested_size, ← hva] at this
              simpa [abs] using this
            obtain ⟨n1, hn1, hn1v, -⟩ := beatmap.objects.sort_nested_refines _ hb
            refine ⟨_, _, by rw [hr, bind_ok]; simp only [hn1, bind_ok, beatmap.objects.span_duration_refines, hL1]; rfl, ?_⟩
            show (abs _ : OsuHitObject) = _
            rw [oa_ho_abs]; simp only [OsuHitObject.mk.injEq]
            and_intros
            all_goals first | rfl | trivial | (rw [hL1v, ← hn1v, hva]; rfl)
  | Spinner s =>
    cases hw : h.hit_windows with
    | none =>
      simp only [hw, hk, bind_ok, uncurry_apply_pair, hSD, hSN, beatmap.objects.span_duration_refines, hL2, hohw]
      simp only [oaObj_fold]
      unfold applyDefaults at hN
      simp only [hkd, hk, hhw, hw, Option.map_none, Option.map_some, hod, oa_hw_osu, oa_hw_empty, ← hohwv, pure_bind, ob_abs_spinner] at hN ⊢
      rw [hSDv, ← ob_abs_spinner, show HitWindows.empty = abs beatmap.objects.HitWindows.Empty from rfl] at hN ⊢
      simp only [oa_abs_obj] at hN ⊢
      generalize oaObj h d cpi (beatmap.objects.ObjectKind.Spinner (SD s)) beatmap.objects.HitWindows.Empty = O at hN ⊢
      have hb : (SN O (SD s)).val.length < 2^31 := by
        have := hN _ rfl
        simp only [Array.size_map, sort_nested_size, hSNv] at this
        simpa [abs] using this
      obtain ⟨n1, hn1, hn1v, -⟩ := beatmap.objects.sort_nested_refines _ hb
      refine ⟨_, _, by rw [hn1, bind_ok], ?_⟩
      show (abs _ : OsuHitObject) = _
      rw [oa_ho_abs]; simp only [OsuHitObject.mk.injEq]
      and_intros
      all_goals first | rfl | trivial | (rw [hL2v, ← hn1v, ← hSNv]; rfl)
    | some w =>
      cases w with
      | Empty =>
        simp only [hw, hk, bind_ok, uncurry_apply_pair, hSD, hSN, beatmap.objects.span_duration_refines, hL2, hohw]
        simp only [oaObj_fold]
        unfold applyDefaults at hN
        simp only [hkd, hk, hhw, hw, Option.map_none, Option.map_some, hod, oa_hw_osu, oa_hw_empty, ← hohwv, pure_bind, ob_abs_spinner] at hN ⊢
        rw [hSDv, ← ob_abs_spinner, show HitWindows.empty = abs beatmap.objects.HitWindows.Empty from rfl] at hN ⊢
        simp only [oa_abs_obj] at hN ⊢
        generalize oaObj h d cpi (beatmap.objects.ObjectKind.Spinner (SD s)) beatmap.objects.HitWindows.Empty = O at hN ⊢
        have hb : (SN O (SD s)).val.length < 2^31 := by
          have := hN _ rfl
          simp only [Array.size_map, sort_nested_size, hSNv] at this
          simpa [abs] using this
        obtain ⟨n1, hn1, hn1v, -⟩ := beatmap.objects.sort_nested_refines _ hb
        refine ⟨_, _, by rw [hn1, bind_ok], ?_⟩
        show (abs _ : OsuHitObject) = _
        rw [oa_ho_abs]; simp only [OsuHitObject.mk.injEq]
        and_intros
        all_goals first | rfl | trivial | (rw [hL2v, ← hn1v, ← hSNv]; rfl)
      | Osu wa wb wc =>
        simp only [hw, hk, bind_ok, uncurry_apply_pair, hSD, hSN, beatmap.objects.span_duration_refines, hL2, hohw]
        simp only [oaObj_fold]
        unfold applyDefaults at hN
        simp only [hkd, hk, hhw, hw, Option.map_none, Option.map_some, hod, oa_hw_osu, oa_hw_empty, ← hohwv, pure_bind, ob_abs_spinner] at hN ⊢
        rw [hSDv, ← ob_abs_spinner, hohwv] at hN ⊢
        simp only [oa_abs_obj] at hN ⊢
        generalize oaObj h d cpi (beatmap.objects.ObjectKind.Spinner (SD s)) (beatmap.objects.HitWindows.Osu oa ob oc) = O at hN ⊢
        have hb : (SN O (SD s)).val.length < 2^31 := by
          have := hN _ rfl
          simp only [Array.size_map, sort_nested_size, hSNv] at this
          simpa [abs] using this
        obtain ⟨n1, hn1, hn1v, -⟩ := beatmap.objects.sort_nested_refines _ hb
        refine ⟨_, _, by rw [hn1, bind_ok], ?_⟩
        show (abs _ : OsuHitObject) = _
        rw [oa_ho_abs]; simp only [OsuHitObject.mk.injEq]
        and_intros
        all_goals first | rfl | trivial | (rw [hL2v, ← hn1v, ← hSNv]; rfl)

end OsuProofs
