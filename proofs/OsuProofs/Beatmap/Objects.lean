/-
`beatmap::objects` (Rust) refines `OsuModel.Beatmap` objects (`Objects.lean`): derived getters and ApplyDefaults.
Stated with the generated `abs` maps (Auto/Abs.lean, Auto/Base.lean), like the Post layer, so callers in
Post/* can use them directly. `abs (p : SliderPath) = spS p` bridges to Beatmap/SliderPath.lean.
-/
import OsuProofs.Auto.Gen
import OsuProofs.Beatmap.SliderPath
import OsuProofs.Beatmap.SliderEvents
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

theorem ob_abs_sliderPath (p : beatmap.slider_path.SliderPath) : (abs p : SliderPath) = spS p := by
  simp only [abs, spS, spsS, pcpsS, vS, List.map_id', Option.map_id', id]
  congr 3 <;> try simp

theorem ob_i32_cast_i64 (x : I32) : (IScalar.cast .I64 x).val = x.val := by
  rw [IScalar.cast_val_eq]; have := x.hBounds; simp at this ⊢

theorem ob_span_count (s : beatmap.objects.SliderData) :
    beatmap.objects.span_count s = ok (i32I (SliderData.spanCount (abs s))) := by
  obtain ⟨r, hr, hrv⟩ := beatmap.objects.span_count_refines s
  rw [hr, hrv]; rfl

theorem beatmap.objects.end_time_refines (h : beatmap.objects.OsuHitObject) :
    beatmap.objects.end_time h = ok (OsuHitObject.endTime (abs h)) := by
  unfold beatmap.objects.end_time OsuHitObject.endTime
  cases hk : h.kind with
  | Circle => simp [abs, hk]
  | Spinner s => simp [abs, hk]
  | Slider s =>
    simp only [ob_span_count, bind_ok, lift, float.F64.from_i64, ob_i32_cast_i64, beatmap.slider_path.distance_refines,
      float.F64.mul, float.F64.div, float.F64.add]
    have hks : (abs h : OsuHitObject).kind = .slider (abs s) := by
      show (abs h.kind : ObjectKind) = _; rw [hk]; rfl
    have hst : (abs h : OsuHitObject).startTime = h.start_time := rfl
    rw [hks, hst]
    have hp : (abs s : SliderData).path = abs s.path := rfl
    have hv : (abs s : SliderData).velocity = s.velocity := rfl
    simp only [hp, hv, ob_abs_sliderPath]
    rfl

theorem beatmap.objects.progress_at_refines (s : beatmap.objects.SliderData) (progress : F64) :
    beatmap.objects.progress_at s progress = ok (SliderData.progressAt (abs s) progress) := by
  unfold beatmap.objects.progress_at SliderData.progressAt
  simp only [ob_span_count, bind_ok, lift, float.F64.from_i64, ob_i32_cast_i64, float.F64.mul,
    beatmap.dotnet.fmod1_refines, float.F64.to_i32_sat]
  have hof : F64.ofInt ↑(i32I (SliderData.spanCount (abs s))) = F64.ofInt32 (SliderData.spanCount (abs s)) := rfl
  rw [hof]
  generalize hsa : F64.toInt32 (progress * F64.ofInt32 (SliderData.spanCount (abs s))) = sa
  obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (IScalar.rem_spec (⟨sa.toBitVec⟩ : I32) (y := 2#i32) (by simp))
  rw [hz, bind_ok]
  have hc : (z = 1#i32) ↔ ((sa % 2 == 1) = true) := by
    have e : z.val = (sa % 2).toInt := by rw [hzv, Int32.toInt_mod]; rfl
    constructor
    · intro h
      have : (sa % 2).toInt = (1 : Int32).toInt := by rw [← e, h]; rfl
      simp [Int32.toInt_inj.mp this]
    · intro h; apply IScalar.eq_of_val_eq; rw [e]; simp at h; rw [h]; rfl
  by_cases h1 : z = 1#i32
  · rw [if_pos h1, if_pos (hc.mp h1), bmc_beatmap_objects_D1, bind_ok, float.F64.sub]
  · rw [if_neg h1, if_neg (fun h => h1 (hc.mpr h))]

/-- Size side condition of slider path queries (`position_at`: `binary_search_f64` and the `i64` index casts). -/
def obPathOk (p : beatmap.slider_path.SliderPath) : Prop :=
  p.cumulative_length.val.length < 2^61 ∧ p.calculated_path.val.length < 2^62

theorem beatmap.objects.curve_position_at_refines (s : beatmap.objects.SliderData) (progress : F64)
    (hp : obPathOk s.path) (h64 : System.Platform.numBits = 64) :
    beatmap.objects.curve_position_at s progress = ok (bv2I (SliderData.curvePositionAt (abs s) progress)) := by
  unfold beatmap.objects.curve_position_at SliderData.curvePositionAt
  rw [beatmap.objects.progress_at_refines, bind_ok, beatmap.slider_path.position_at_refines _ _ hp.1 hp.2 h64,
    show (abs s : SliderData).path = abs s.path from rfl, ob_abs_sliderPath]

theorem beatmap.objects.end_position_refines (h : beatmap.objects.OsuHitObject)
    (hp : ∀ s, h.kind = .Slider s → obPathOk s.path) (h64 : System.Platform.numBits = 64) :
    beatmap.objects.end_position h = ok (bv2I (OsuHitObject.endPosition (abs h))) := by
  unfold beatmap.objects.end_position OsuHitObject.endPosition
  cases hk : h.kind with
  | Circle =>
    have hks : (abs h : OsuHitObject).kind = .circle := by show (abs h.kind : ObjectKind) = _; rw [hk]; rfl
    rw [hks]; rfl
  | Spinner s =>
    have hks : (abs h : OsuHitObject).kind = .spinner (abs s) := by show (abs h.kind : ObjectKind) = _; rw [hk]; rfl
    rw [hks]; rfl
  | Slider s =>
    have hks : (abs h : OsuHitObject).kind = .slider (abs s) := by show (abs h.kind : ObjectKind) = _; rw [hk]; rfl
    rw [hks]
    simp only [bmc_beatmap_objects_D1, bind_ok, beatmap.objects.curve_position_at_refines s 1 (hp s hk) h64,
      beatmap.vector2.add_refines, bv2S_I]
    rfl

theorem beatmap.objects.difficulty_range_refines (d mn md mx : F64) :
    beatmap.objects.difficulty_range d mn md mx = ok (difficultyRange d mn md mx) := by
  unfold beatmap.objects.difficulty_range difficultyRange
  obtain ⟨r, hr, hrv⟩ := beatmap.objects.difficulty_range1_refines d
  simp only [bmc_beatmap_objects_D5, bind_ok, float.F64.lt, hr, float.F64.sub, float.F64.mul, float.F64.add]
  have hr' : r = difficultyRange1 d := by simpa [abs] using hrv.symm
  subst hr'
  by_cases h1 : (5 : F64) < d <;> by_cases h2 : d < 5 <;> simp [h1, h2]

theorem ob_c80a : Float.ofBits (U64.bv 4635329916471083008#u64).toNat.toUInt64 = (80 : F64) := by decide
theorem ob_c50a : Float.ofBits (U64.bv 4632233691727265792#u64).toNat.toUInt64 = (50 : F64) := by decide
theorem ob_c20a : Float.ofBits (U64.bv 4626322717216342016#u64).toNat.toUInt64 = (20 : F64) := by decide
theorem ob_c140a : Float.ofBits (U64.bv 4639129828656676864#u64).toNat.toUInt64 = (140 : F64) := by decide
theorem ob_c100a : Float.ofBits (U64.bv 4636737291354636288#u64).toNat.toUInt64 = (100 : F64) := by decide
theorem ob_c60a : Float.ofBits (U64.bv 4633641066610819072#u64).toNat.toUInt64 = (60 : F64) := by decide
theorem ob_c200a : Float.ofBits (U64.bv 4641240890982006784#u64).toNat.toUInt64 = (200 : F64) := by decide
theorem ob_c150a : Float.ofBits (U64.bv 4639481672377565184#u64).toNat.toUInt64 = (150 : F64) := by decide

def obHwI : HitWindows → beatmap.objects.HitWindows
  | .empty => .Empty
  | .osu g o m => .Osu g o m
@[simp] theorem ob_abs_hwI (w : HitWindows) : (abs (obHwI w) : HitWindows) = w := by cases w <;> rfl

theorem ob_osu_hit_windows (od : F64) : beatmap.objects.osu_hit_windows od = ok (obHwI (osuHitWindows od)) := by
  unfold beatmap.objects.osu_hit_windows
  simp only [beatmap.objects.difficulty_range_refines, bind_ok, float.F64.from_bits, float.F64.floor, float.F64.sub,
    bmc_beatmap_objects_D_HALF]
  simp only [osuHitWindows, obHwI, ob_c80a, ob_c50a, ob_c20a, ob_c140a, ob_c100a, ob_c60a, ob_c200a, ob_c150a]

theorem beatmap.objects.osu_hit_windows_refines (od : F64) :
    ∃ r, beatmap.objects.osu_hit_windows od = ok r ∧ osuHitWindows od = abs r :=
  ⟨_, ob_osu_hit_windows od, by simp⟩

theorem ob_dr1 (d : F64) : beatmap.objects.difficulty_range1 d = ok (difficultyRange1 d) := by
  obtain ⟨r, hr, hrv⟩ := beatmap.objects.difficulty_range1_refines d
  rw [hr]; simpa [abs] using hrv.symm

theorem beatmap.objects.calculate_scale_from_circle_size_refines (cs : F32) (fudge : Bool) :
    beatmap.objects.calculate_scale_from_circle_size cs fudge = ok (calculateScaleFromCircleSize cs fudge) := by
  unfold beatmap.objects.calculate_scale_from_circle_size calculateScaleFromCircleSize
  simp only [bmc_beatmap_objects_F32_ONE, bmc_beatmap_objects_F32_0_7, bmc_beatmap_objects_F32_2, bind_ok,
    float.F32.to_f64, ob_dr1, float.F64.mul, float.F64.sub, float.F64.to_f32, float.F32.div, float.F32.mul]
  have e : (1.0 : F32) = 1 := by decide
  rw [e]
  cases fudge <;> simp [bmc_beatmap_objects_F32_FUDGE]

theorem ob_i32_from_i64 (x : Int32) : (IScalar.cast .I64 (⟨x.toBitVec⟩ : I32)).val = x.toInt := by
  rw [ob_i32_cast_i64]; rfl

theorem beatmap.objects.time_preempt_for_refines (ar : F32) :
    beatmap.objects.time_preempt_for ar = ok (timePreemptFor ar) := by
  unfold beatmap.objects.time_preempt_for timePreemptFor
  simp only [float.F32.to_f64, bmc_beatmap_objects_D1800, bmc_beatmap_objects_D1200, bmc_beatmap_objects_D450, bind_ok,
    beatmap.objects.difficulty_range_refines, float.F64.to_i32_sat, lift, ob_i32_from_i64, float.F64.from_i64]
  rfl

theorem beatmap.objects.time_fade_in_for_refines (p : F64) :
    beatmap.objects.time_fade_in_for p = ok (timeFadeInFor p) := by
  unfold beatmap.objects.time_fade_in_for timeFadeInFor
  simp only [bmc_beatmap_objects_D450, bmc_beatmap_objects_D1, bmc_beatmap_objects_D400, bind_ok, float.F64.div,
    min_refines, float.F64.mul]

theorem beatmap.objects.common_defaults_refines (d : beatmap.types.Difficulty) :
    ∃ r, beatmap.objects.common_defaults d = ok r ∧ commonDefaults (abs d) = abs r := by
  refine ⟨⟨timePreemptFor d.approach_rate, timeFadeInFor (timePreemptFor d.approach_rate),
    calculateScaleFromCircleSize d.circle_size true⟩, by simp only [beatmap.objects.common_defaults, beatmap.objects.time_preempt_for_refines, bind_ok,
    beatmap.objects.time_fade_in_for_refines, beatmap.objects.calculate_scale_from_circle_size_refines], ?_⟩
  rfl

theorem beatmap.objects.nested_stack_offset_refines (n : beatmap.objects.NestedObject) :
    beatmap.objects.nested_stack_offset n = ok (bv2I (NestedObject.stackOffset (abs n))) := by
  unfold beatmap.objects.nested_stack_offset NestedObject.stackOffset
  simp only [lift, bind_ok, float.F32.from_i64, ob_i32_cast_i64, float.F32.mul, bmc_beatmap_objects_F32_M6_4,
    beatmap.vector2.splat_refines]
  rfl

theorem beatmap.objects.stack_offset_refines (h : beatmap.objects.OsuHitObject) :
    beatmap.objects.stack_offset h = ok (bv2I (OsuHitObject.stackOffset (abs h))) := by
  unfold beatmap.objects.stack_offset OsuHitObject.stackOffset
  cases hk : h.kind with
  | Circle =>
    have hks : (abs h : OsuHitObject).kind = .circle := by show (abs h.kind : ObjectKind) = _; rw [hk]; rfl
    rw [hks]
    simp only [lift, bind_ok, float.F32.from_i64, ob_i32_cast_i64, float.F32.mul, bmc_beatmap_objects_F32_M6_4,
      beatmap.vector2.splat_refines]
    rfl
  | Slider s =>
    have hks : (abs h : OsuHitObject).kind = .slider (abs s) := by show (abs h.kind : ObjectKind) = _; rw [hk]; rfl
    rw [hks]
    simp only [lift, bind_ok, float.F32.from_i64, ob_i32_cast_i64, float.F32.mul, bmc_beatmap_objects_F32_M6_4,
      beatmap.vector2.splat_refines]
    rfl
  | Spinner s =>
    have hks : (abs h : OsuHitObject).kind = .spinner (abs s) := by show (abs h.kind : ObjectKind) = _; rw [hk]; rfl
    rw [hks, bm_vector2_ZERO]

theorem ob_kind_abs (h : beatmap.objects.OsuHitObject) : (abs h : OsuHitObject).kind = abs h.kind := rfl
@[simp] theorem ob_abs_circle : (abs beatmap.objects.ObjectKind.Circle : ObjectKind) = .circle := rfl
@[simp] theorem ob_abs_slider (s : beatmap.objects.SliderData) :
    (abs (beatmap.objects.ObjectKind.Slider s) : ObjectKind) = .slider (abs s) := rfl
@[simp] theorem ob_abs_spinner (s : beatmap.objects.SpinnerData) :
    (abs (beatmap.objects.ObjectKind.Spinner s) : ObjectKind) = .spinner (abs s) := rfl

theorem beatmap.objects.duration_refines (h : beatmap.objects.OsuHitObject) :
    beatmap.objects.duration h = ok (OsuHitObject.duration (abs h)) := by
  unfold beatmap.objects.duration OsuHitObject.duration
  cases hk : h.kind with
  | Circle => simp only [ob_kind_abs, hk, ob_abs_circle, beatmap.objects.end_time_refines, bind_ok, float.F64.sub]; rfl
  | Slider s => simp only [ob_kind_abs, hk, ob_abs_slider, beatmap.objects.end_time_refines, bind_ok, float.F64.sub]; rfl
  | Spinner s => simp only [ob_kind_abs, hk, ob_abs_spinner]; rfl

theorem beatmap.objects.span_duration_refines (h : beatmap.objects.OsuHitObject) :
    beatmap.objects.span_duration h = ok (OsuHitObject.spanDuration (abs h)) := by
  unfold beatmap.objects.span_duration OsuHitObject.spanDuration
  cases hk : h.kind with
  | Circle => simp only [ob_kind_abs, hk, ob_abs_circle, beatmap.objects.duration_refines]
  | Slider s =>
    simp only [ob_kind_abs, hk, ob_abs_slider, beatmap.objects.duration_refines, bind_ok, ob_span_count, lift,
      ob_i32_cast_i64, float.F64.from_i64, float.F64.div]
    rfl
  | Spinner s => simp only [ob_kind_abs, hk, ob_abs_spinner, beatmap.objects.duration_refines]

theorem beatmap.objects.stacked_position_refines (h : beatmap.objects.OsuHitObject) :
    beatmap.objects.stacked_position h = ok (bv2I (OsuHitObject.stackedPosition (abs h))) := by
  simp only [beatmap.objects.stacked_position, OsuHitObject.stackedPosition, beatmap.objects.stack_offset_refines,
    bind_ok, beatmap.vector2.add_refines, bv2S_I]
  rfl

theorem beatmap.objects.stacked_end_position_refines (h : beatmap.objects.OsuHitObject)
    (hp : ∀ s, h.kind = .Slider s → obPathOk s.path) (h64 : System.Platform.numBits = 64) :
    beatmap.objects.stacked_end_position h = ok (bv2I (OsuHitObject.stackedEndPosition (abs h))) := by
  simp only [beatmap.objects.stacked_end_position, OsuHitObject.stackedEndPosition,
    beatmap.objects.end_position_refines h hp h64, beatmap.objects.stack_offset_refines,
    bind_ok, beatmap.vector2.add_refines, bv2S_I]
  rfl

theorem beatmap.objects.nested_stacked_position_refines (n : beatmap.objects.NestedObject) :
    beatmap.objects.nested_stacked_position n = ok (bv2I (NestedObject.stackedPosition (abs n))) := by
  simp only [beatmap.objects.nested_stacked_position, NestedObject.stackedPosition,
    beatmap.objects.nested_stack_offset_refines, bind_ok, beatmap.vector2.add_refines, bv2S_I]
  rfl

theorem beatmap.objects.nested_radius_refines (n : beatmap.objects.NestedObject) :
    beatmap.objects.nested_radius n = ok (NestedObject.radius (abs n)) := by
  simp only [beatmap.objects.nested_radius, NestedObject.radius, bmc_beatmap_objects_OBJECT_RADIUS, bind_ok,
    float.F32.mul, float.F32.to_f64]
  rfl

theorem beatmap.objects.is_circle_refines (h : beatmap.objects.OsuHitObject) :
    beatmap.objects.is_circle h = ok (OsuHitObject.isCircle (abs h)) := by
  unfold beatmap.objects.is_circle OsuHitObject.isCircle
  cases hk : h.kind <;> simp only [ob_kind_abs, hk, ob_abs_circle, ob_abs_slider, ob_abs_spinner]
theorem beatmap.objects.is_slider_refines (h : beatmap.objects.OsuHitObject) :
    beatmap.objects.is_slider h = ok (OsuHitObject.isSlider (abs h)) := by
  unfold beatmap.objects.is_slider OsuHitObject.isSlider
  cases hk : h.kind <;> simp only [ob_kind_abs, hk, ob_abs_circle, ob_abs_slider, ob_abs_spinner]
theorem beatmap.objects.is_spinner_refines (h : beatmap.objects.OsuHitObject) :
    beatmap.objects.is_spinner h = ok (OsuHitObject.isSpinner (abs h)) := by
  unfold beatmap.objects.is_spinner OsuHitObject.isSpinner
  cases hk : h.kind <;> simp only [ob_kind_abs, hk, ob_abs_circle, ob_abs_slider, ob_abs_spinner]

theorem beatmap.objects.object_default_refines (kind : beatmap.objects.ObjectKind) (st : F64) (pos : net.osutk.Vector2) :
    ∃ r, beatmap.objects.object_default kind st pos = ok r ∧
      ({ kind := abs kind, startTime := st, position := bv2S pos } : OsuHitObject) = abs r := by
  simp only [beatmap.objects.object_default, bmc_beatmap_objects_F32_ONE, bmc_beatmap_objects_D600,
    bmc_beatmap_objects_D400, bind_ok, ok.injEq, exists_eq_left']
  rfl

theorem beatmap.objects.nested_default_refines (kind : beatmap.objects.NestedKind) (st : F64) :
    ∃ r, beatmap.objects.nested_default kind st = ok r ∧
      ({ kind := abs kind, startTime := st } : NestedObject) = abs r := by
  simp only [beatmap.objects.nested_default, bmc_beatmap_objects_F32_ONE, bmc_beatmap_objects_D600,
    bmc_beatmap_objects_D400, bmc_beatmap_objects_D0, bm_vector2_ZERO, bind_ok, ok.injEq, exists_eq_left']
  rfl

theorem beatmap.objects.get_precision_adjusted_beat_length_refines (svm : F64) (tp : beatmap.control_points.TimingPoint) :
    beatmap.objects.get_precision_adjusted_beat_length svm tp =
      ok (getPrecisionAdjustedBeatLength svm (abs tp)) := by
  unfold beatmap.objects.get_precision_adjusted_beat_length getPrecisionAdjustedBeatLength
  simp only [bmc_beatmap_objects_D_M100, bmc_beatmap_objects_D0, bmc_beatmap_objects_D1, bmc_beatmap_objects_F10,
    bmc_beatmap_objects_F1000, bmc_beatmap_objects_D100, bind_ok, float.F64.div, float.F64.neg, float.F64.to_f32,
    float.F32.to_f64, float.F64.mul]
  have e : (100.0 : F64) = 100 := by decide
  rw [e]
  have hb : (abs tp : TimingPoint).beatLength = tp.beat_length := rfl
  rw [hb]
  generalize -100 / svm = a
  by_cases h1 : a < 0
  · simp only [float.F64.lt, h1, decide_true, ite_true, float.F32.lt]
    generalize (-a).toF32 = v
    by_cases h2 : v < 10
    · simp [h2]
    · by_cases h3 : (1000 : F32) < v <;> simp [h2, h3]
  · simp [float.F64.lt, h1]

theorem ob_c90 : Float.ofBits (U64.bv 4636033603912859648#u64).toNat.toUInt64 = (90 : F64) := by decide
theorem ob_c225 : Float.ofBits (U64.bv 4642120500284227584#u64).toNat.toUInt64 = (225 : F64) := by decide
theorem ob_c250 : Float.ofBits (U64.bv 4643000109586448384#u64).toNat.toUInt64 = (250 : F64) := by decide
theorem ob_c380 : Float.ofBits (U64.bv 4645392646888488960#u64).toNat.toUInt64 = (380 : F64) := by decide
theorem ob_c430 : Float.ofBits (U64.bv 4646272256190709760#u64).toNat.toUInt64 = (430 : F64) := by decide

theorem ob_wrapping_sub (a b : Int32) :
    core.num.I32.wrapping_sub (⟨a.toBitVec⟩ : I32) (⟨b.toBitVec⟩ : I32) = (⟨(a - b).toBitVec⟩ : I32) := by
  simp [core.num.I32.wrapping_sub, IScalar.wrapping_sub]

theorem beatmap.objects.spinner_defaults_refines (d : beatmap.types.Difficulty) (s : beatmap.objects.SpinnerData) :
    ∃ r, beatmap.objects.spinner_defaults d s = ok r ∧ spinnerDefaults (abs d) (abs s) = abs r := by
  unfold beatmap.objects.spinner_defaults spinnerDefaults
  simp only [float.F32.to_f64, float.F64.from_bits, ob_c90, ob_c150a, ob_c225, ob_c250, ob_c380, ob_c430,
    beatmap.objects.difficulty_range_refines, bmc_beatmap_objects_D60, bmc_beatmap_objects_D1000,
    bmc_beatmap_objects_DURATION_ERROR, float.F64.div, float.F64.mul, float.F64.add, float.F64.to_i32_sat, lift, bind_ok]
  have hod : (abs d : Difficulty).overallDifficulty = d.overall_difficulty := rfl
  have hdu : (abs s : SpinnerData).duration = s.duration := rfl
  rw [hod, hdu]
  generalize F64.toInt32 (difficultyRange (F32.toF64 d.overall_difficulty) 250 380 430 / 60 * (s.duration / 1000) + 1e-4) = B
  generalize F64.toInt32 (difficultyRange (F32.toF64 d.overall_difficulty) 90 150 225 / 60 * (s.duration / 1000) + 1e-4) = A
  have h2 : (2#i32 : I32) = ⟨(2 : Int32).toBitVec⟩ := rfl
  rw [ob_wrapping_sub, h2, ob_wrapping_sub]
  by_cases hn : B - A - 2 < 0
  · have hn' : (⟨(B - A - 2).toBitVec⟩ : I32) < 0#i32 := by
      show (⟨(B - A - 2).toBitVec⟩ : I32).val < (0#i32).val
      have e : (⟨(B - A - 2).toBitVec⟩ : I32).val = (B - A - 2).toInt := rfl
      rw [e]; rw [Int32.lt_iff_toInt_lt] at hn; exact hn
    rw [if_pos hn']
    refine ⟨_, rfl, ?_⟩
    simp only [hn, ite_true]; rfl
  · have hn' : ¬ (⟨(B - A - 2).toBitVec⟩ : I32) < 0#i32 := by
      show ¬ (⟨(B - A - 2).toBitVec⟩ : I32).val < (0#i32).val
      have e : (⟨(B - A - 2).toBitVec⟩ : I32).val = (B - A - 2).toInt := rfl
      rw [e]; rw [Int32.lt_iff_toInt_lt] at hn; exact hn
    rw [if_neg hn']
    refine ⟨_, rfl, ?_⟩
    simp only [hn, ite_false]; rfl

theorem ob_abs_cpi (c : beatmap.control_points.ControlPointInfo) : (abs c : ControlPointInfo) = cpS c := by
  simp only [abs, cpS, List.map_id', id]
  rfl

theorem ob_cd_eq (d : beatmap.types.Difficulty) : beatmap.objects.common_defaults d =
    ok ⟨timePreemptFor d.approach_rate, timeFadeInFor (timePreemptFor d.approach_rate),
      calculateScaleFromCircleSize d.circle_size true⟩ := by
  simp only [beatmap.objects.common_defaults, beatmap.objects.time_preempt_for_refines, bind_ok,
    beatmap.objects.time_fade_in_for_refines, beatmap.objects.calculate_scale_from_circle_size_refines]

theorem ob_gt0 (x : I32) : (x > 0#i32) ↔ (i32S x > 0) := by
  show (0#i32).val < x.val ↔ _
  rw [gt_iff_lt, Int32.lt_iff_toInt_lt, i32S_toInt]; simp

@[simp] theorem ob_nk_head : (abs beatmap.objects.NestedKind.Head : NestedKind) = .head := rfl
@[simp] theorem ob_nk_tick : (abs beatmap.objects.NestedKind.Tick : NestedKind) = .tick := rfl
@[simp] theorem ob_nk_repeat : (abs beatmap.objects.NestedKind.Repeat : NestedKind) = .repeat := rfl
@[simp] theorem ob_nk_tail : (abs beatmap.objects.NestedKind.Tail : NestedKind) = .tail := rfl
@[simp] theorem ob_nk_st : (abs beatmap.objects.NestedKind.SpinnerTick : NestedKind) = .spinnerTick := rfl
@[simp] theorem ob_nk_sbt : (abs beatmap.objects.NestedKind.SpinnerBonusTick : NestedKind) = .spinnerBonusTick := rfl

theorem beatmap.objects.apply_nested_defaults_refines (cpi : beatmap.control_points.ControlPointInfo)
    (d : beatmap.types.Difficulty) (ss sd : F64) (n : beatmap.objects.NestedObject)
    (hcpi : cpi.effect_points.val.length < 2^31) :
    ∃ r, beatmap.objects.apply_nested_defaults cpi d ss sd n = ok r ∧
      applyNestedDefaults (abs cpi) (abs d) ss sd (abs n) = abs r := by
  unfold beatmap.objects.apply_nested_defaults applyNestedDefaults
  rw [ob_cd_eq, bind_ok, bmc_beatmap_objects_D1, bind_ok, float.F64.add, bind_ok,
    beatmap.control_points.effect_point_at_refines cpi _ hcpi, bind_ok, ob_abs_cpi]
  have hst : (abs n : NestedObject).startTime = n.start_time := rfl
  rw [hst]
  have hkd : (abs n : NestedObject).kind = abs n.kind := rfl
  cases hk : n.kind with
  | Head =>
    obtain ⟨hw, hhw, hhwv⟩ := beatmap.objects.osu_hit_windows_refines (F32.toF64 d.overall_difficulty)
    simp only [hk, float.F32.to_f64, hhw, bind_ok]
    refine ⟨_, rfl, ?_⟩
    simp only [hkd, hk, ob_nk_head]
    have hod : (abs d : Difficulty).overallDifficulty = d.overall_difficulty := rfl
    rw [hod, hhwv]; rfl
  | Tick =>
    simp only [hk]
    have hsi : (abs n : NestedObject).spanIndex = i32S n.span_index := rfl
    by_cases hr : n.span_index > 0#i32
    · rw [if_pos hr]
      simp only [bmc_beatmap_objects_D200, bmc_beatmap_objects_D2, bind_ok, float.F64.sub, float.F64.div, float.F64.add]
      refine ⟨_, rfl, ?_⟩
      simp only [hkd, hk, ob_nk_tick, hsi, if_pos ((ob_gt0 _).mp hr)]; rfl
    · rw [if_neg hr]
      simp only [bmc_beatmap_objects_F_0_66, float.F32.to_f64, float.F64.mul, bmc_beatmap_objects_D2, bind_ok,
        float.F64.sub, float.F64.div, float.F64.add]
      refine ⟨_, rfl, ?_⟩
      simp only [hkd, hk, ob_nk_tick, hsi, if_neg (fun h => hr ((ob_gt0 _).mpr h))]; rfl
  | Repeat =>
    simp only [hk]
    have hri : (abs n : NestedObject).repeatIndex = i32S n.repeat_index := rfl
    by_cases hr : n.repeat_index > 0#i32
    · rw [if_pos hr]
      simp only [bmc_beatmap_objects_D0, bmc_beatmap_objects_D2, bind_ok, float.F64.mul]
      refine ⟨_, rfl, ?_⟩
      simp only [hkd, hk, ob_nk_repeat, hri, if_pos ((ob_gt0 _).mp hr)]; rfl
    · rw [if_neg hr]
      simp only [bind_ok, float.F64.sub, float.F64.add]
      refine ⟨_, rfl, ?_⟩
      simp only [hkd, hk, ob_nk_repeat, hri, if_neg (fun h => hr ((ob_gt0 _).mpr h))]; rfl
  | Tail =>
    simp only [hk]
    have hri : (abs n : NestedObject).repeatIndex = i32S n.repeat_index := rfl
    by_cases hr : n.repeat_index > 0#i32
    · rw [if_pos hr]
      simp only [bmc_beatmap_objects_D0, bmc_beatmap_objects_D2, bind_ok, float.F64.mul]
      refine ⟨_, rfl, ?_⟩
      simp only [hkd, hk, ob_nk_tail, hri, if_pos ((ob_gt0 _).mp hr)]; rfl
    · rw [if_neg hr]
      simp only [bind_ok, float.F64.sub, float.F64.add]
      refine ⟨_, rfl, ?_⟩
      simp only [hkd, hk, ob_nk_tail, hri, if_neg (fun h => hr ((ob_gt0 _).mpr h))]; rfl
  | SpinnerTick => exact ⟨_, rfl, by simp only [hkd, hk, ob_nk_st]; rfl⟩
  | SpinnerBonusTick => exact ⟨_, rfl, by simp only [hkd, hk, ob_nk_sbt]; rfl⟩

def obSnBody (h : OsuHitObject) (s : SpinnerData) (iN : Nat) (out : Array NestedObject) : ForInStep (Array NestedObject) :=
  .yield (out.push { kind := if Int32.ofNat iN < s.spinsRequired + 2 then .spinnerTick else .spinnerBonusTick, startTime := h.startTime + (F32.ofInt32 (Int32.ofNat iN + 1) / F32.ofInt32 (s.maximumBonusSpins + s.spinsRequired + 2)).toF64 * s.duration, spinnerDuration := s.duration })

theorem beatmap.objects.spinner_nested_refines (h : beatmap.objects.OsuHitObject) (s : beatmap.objects.SpinnerData) :
    ∃ r, beatmap.objects.spinner_nested h s = ok r ∧ spinnerNested (abs h) (abs s) = abs r := by
  unfold beatmap.objects.spinner_nested spinnerNested
  simp only [lift, bind_ok, Id.run_bind, forIn_range_idx, id_run_eq]
  generalize hS : iterIdx _ 0 _ _ = S
  have hS' : iterIdx (fun i b => obSnBody (abs h) (abs s) i b) 0 (((abs s : SpinnerData).maximumBonusSpins +
      (abs s : SpinnerData).spinsRequired + 2).toNatClampNeg - 0) #[] = S := hS
  have hwa : ∀ a b : I32, i32S (core.num.I32.wrapping_add a b) = i32S a + i32S b := fun _ _ => rfl
  generalize hA : (abs s : SpinnerData).maximumBonusSpins + (abs s : SpinnerData).spinsRequired + 2 = A at hS'
  have hA' : i32S (core.num.I32.wrapping_add (core.num.I32.wrapping_add s.maximum_bonus_spins s.spins_required) 2#i32) = A := by
    rw [hwa, hwa, ← hA]; rfl
  generalize hT : core.num.I32.wrapping_add (core.num.I32.wrapping_add s.maximum_bonus_spins s.spins_required) 2#i32 = T at hA' ⊢
  obtain ⟨nn, hn, hnn0, hnn2⟩ : ∃ nn : I32, (if T < 0#i32 then ok 0#i32 else ok T : Result I32) = ok nn ∧
      0 ≤ nn.val ∧ nn.val.toNat = A.toNatClampNeg := by
    by_cases h : T.val < 0
    · have h' : T < 0#i32 := by show T.val < (0#i32).val; simpa using h
      refine ⟨0#i32, by simp [h'], by simp, ?_⟩
      rw [← hA']; simp [Int32.toNatClampNeg, i32S_toInt]; omega
    · have h' : ¬ T < 0#i32 := by show ¬ T.val < (0#i32).val; simpa using h
      refine ⟨T, by simp [h'], by omega, ?_⟩
      rw [← hA']; simp [Int32.toNatClampNeg, i32S_toInt]
  rw [hn, bind_ok, float.F32.from_i64, bind_ok]
  rw [← hnn2] at hS'
  have hnb := nn.hBounds
  simp at hnb
  unfold beatmap.objects.spinner_nested_loop
  refine Exists.imp (fun y H => ⟨H.1, ?hv⟩) (loop_iterIdx' _ _ nn.val.toNat
    (fun (x : alloc.vec.Vec beatmap.objects.NestedObject × I32) k (b : Array NestedObject) =>
      x.2.val = k ∧ (x.1.val.map abs).toArray = b ∧ x.1.val.length = k ∧ k ≤ nn.val.toNat)
    (fun (y : alloc.vec.Vec beatmap.objects.NestedObject) (c : Array NestedObject) => (y.val.map abs).toArray = c)
    ?hstep ?hend (alloc.vec.Vec.new _, 0#i32) 0 #[] ⟨by simp, by simp, by simp, by omega⟩ hS')
  case hv => obtain ⟨_, h1⟩ := H; rw [← h1]; rfl
  case hend =>
    rintro ⟨o, i⟩ k b ⟨h1, h2, h3, h4⟩ hk
    dsimp only at h1 h2 h3 h4
    have hlt : ¬ i < nn := by show ¬ i.val < nn.val; omega
    exact ⟨o, by simp [beatmap.objects.spinner_nested_loop.body, hlt], h2⟩
  case hstep =>
    rintro ⟨o, i⟩ k b ⟨h1, h2, h3, h4⟩ hk
    dsimp only at h1 h2 h3 h4
    subst h2
    left
    have hlt : i < nn := by show i.val < nn.val; omega
    have hsp : i32S i = Int32.ofNat k := se_i32S_ofNat i k h1
    obtain ⟨i5, hi5, hi5v⟩ := i32_add_one i (by omega) (by omega)
    have hkind : (if i < core.num.I32.wrapping_add s.spins_required 2#i32 then ok beatmap.objects.NestedKind.SpinnerTick
        else ok beatmap.objects.NestedKind.SpinnerBonusTick : Result _) =
        ok (if Int32.ofNat k < (abs s : SpinnerData).spinsRequired + 2 then beatmap.objects.NestedKind.SpinnerTick
          else beatmap.objects.NestedKind.SpinnerBonusTick) := by
      have hc : (i < core.num.I32.wrapping_add s.spins_required 2#i32) ↔ Int32.ofNat k < (abs s : SpinnerData).spinsRequired + 2 := by
        have e : (abs s : SpinnerData).spinsRequired + 2 = i32S (core.num.I32.wrapping_add s.spins_required 2#i32) := rfl
        rw [← hsp, e, i32S_lt]; rfl
      by_cases h : Int32.ofNat k < (abs s : SpinnerData).spinsRequired + 2
      · rw [if_pos (hc.mpr h), if_pos h]
      · rw [if_neg (fun e => h (hc.mp e)), if_neg h]
    let kd := if Int32.ofNat k < (abs s : SpinnerData).spinsRequired + 2 then beatmap.objects.NestedKind.SpinnerTick
          else beatmap.objects.NestedKind.SpinnerBonusTick
    let stV := h.start_time + F32.toF64 (F32.ofInt (core.num.I32.wrapping_add i 1#i32).val / F32.ofInt T.val) * s.duration
    obtain ⟨nd, hnd, hndv⟩ := beatmap.objects.nested_default_refines kd stV
    obtain ⟨o1, ho1, ho1v⟩ := push_eq o { nd with spinner_duration := s.duration } (by have := usize_ge_32; omega)
    refine ⟨_, rfl, (o1, i5), ?_, ?_⟩
    · simp only [beatmap.objects.spinner_nested_loop.body, hlt, ite_true, lift, bind_ok, se_cast_i64, float.F32.from_i64,
        float.F32.div, float.F32.to_f64, float.F64.mul, float.F64.add, hkind, hi5]
      rw [show beatmap.objects.nested_default kd stV = ok nd from hnd, bind_ok, ho1, bind_ok]
    · refine ⟨by simp [hi5v, h1], ?_, by rw [ho1v]; simp; omega, by omega⟩
      dsimp only
      rw [ho1v, List.map_append, List.map_cons, List.map_nil, ← List.push_toArray]
      congr 1
      have hab : (abs { nd with spinner_duration := s.duration } : NestedObject) =
          { (abs nd : NestedObject) with spinnerDuration := s.duration } := rfl
      rw [hab, ← hndv]
      have e1 : F32.ofInt32 (Int32.ofNat k + 1) = F32.ofInt (core.num.I32.wrapping_add i 1#i32).val := by
        rw [← i32S_toInt, se_wrapping_add1, hsp]; rfl
      have e2 : F32.ofInt32 ((abs s : SpinnerData).maximumBonusSpins + (abs s : SpinnerData).spinsRequired + 2) =
          F32.ofInt T.val := by rw [hA, ← hA', ← i32S_toInt]; rfl
      rw [e1, e2]
      have ek : (abs kd : NestedKind) = (if Int32.ofNat k < (abs s : SpinnerData).spinsRequired + 2 then .spinnerTick
          else .spinnerBonusTick) := by simp only [kd]; split <;> rfl
      rw [ek]; rfl

theorem ob_forIn_list_ex {ε α β : Type} (f : α → β → Except ε (ForInStep β)) (g : β → α → β)
    (hf : ∀ a s, f a s = .ok (.yield (g s a))) : ∀ (l : List α) (b : β), forIn (m := Except ε) l b f = .ok (l.foldl g b) := by
  intro l
  induction l with
  | nil => intro b; rfl
  | cons a l ih => intro b; rw [List.forIn_cons, hf]; exact ih (g b a)

/-- One event of the spec's `sliderNested` loop. -/
def obSlStep (h : OsuHitObject) (s : SliderData) (P : SliderPath) (out : Array NestedObject) (e : SliderEventDescriptor) : Array NestedObject :=
  match e.type with
  | .tick => out.push { kind := .tick, startTime := e.time, position := h.position + P.positionAt e.pathProgress, stackHeight := h.stackHeight, pathProgress := e.pathProgress, spanIndex := e.spanIndex, spanStartTime := e.spanStartTime }
  | .head => out.push { kind := .head, startTime := e.time, position := h.position, stackHeight := h.stackHeight, classicSliderBehaviour := s.classicSliderBehaviour }
  | .tail => out.push { kind := .tail, startTime := e.time, position := h.endPosition, stackHeight := h.stackHeight, repeatIndex := e.spanIndex, classicSliderBehaviour := s.classicSliderBehaviour, strictTrackingTail := s.strictTracking }
  | .repeat => out.push { kind := .repeat, startTime := h.startTime + F64.ofInt32 (e.spanIndex + 1) * h.spanDuration, position := h.position + P.positionAt e.pathProgress, stackHeight := h.stackHeight, pathProgress := e.pathProgress, repeatIndex := e.spanIndex }
  | .legacyLastTick => out

theorem beatmap.objects.slider_nested_refines (h : beatmap.objects.OsuHitObject) (s : beatmap.objects.SliderData)
    (hp : obPathOk s.path) (hph : ∀ s', h.kind = .Slider s' → obPathOk s'.path) (h64 : System.Platform.numBits = 64) :
    ∃ r, beatmap.objects.slider_nested h s = ok r ∧
      hRel (fun v => (v.val.map abs).toArray) r (sliderNested (abs h) (abs s)) := by
  unfold beatmap.objects.slider_nested sliderNested
  rw [beatmap.objects.span_duration_refines, bind_ok, beatmap.slider_path.distance_refines, bind_ok, ob_span_count,
    bind_ok]
  obtain ⟨r, hr, hrv⟩ := beatmap.slider_event_generator.generate_refines h.start_time
    (OsuHitObject.spanDuration (abs h)) s.velocity s.tick_distance (SliderPath.distance (spS s.path))
    (i32I (SliderData.spanCount (abs s))) h64
  rw [hr, bind_ok]
  have e1 : (abs h : OsuHitObject).startTime = h.start_time := rfl
  have e2 : (abs s : SliderData).velocity = s.velocity := rfl
  have e3 : (abs s : SliderData).tickDistance = s.tick_distance := rfl
  have e4 : (abs s : SliderData).path = spS s.path := ob_abs_sliderPath s.path
  rw [e1, e2, e3, e4]
  simp only [i32S_i32I] at hrv
  cases r with
  | Err er =>
    revert hrv
    cases SliderEventGenerator.generate h.start_time (OsuHitObject.spanDuration (abs h)) s.velocity s.tick_distance
      (SliderPath.distance (spS s.path)) (SliderData.spanCount (abs s)) with
    | ok _ => simp [hRel]
    | error _ => intro _; exact ⟨_, rfl, trivial⟩
  | Ok evs =>
    revert hrv
    cases hg : SliderEventGenerator.generate h.start_time (OsuHitObject.spanDuration (abs h)) s.velocity s.tick_distance
      (SliderPath.distance (spS s.path)) (SliderData.spanCount (abs s)) with
    | error _ => simp [hRel]
    | ok evS =>
      intro hev
      simp only [hRel] at hev
      subst hev
      simp only [except_bind_ok]
      generalize hF : forIn (m := Except String) (ρ := Array SliderEventDescriptor) (sedsS evs.val) _ _ = F
      have hF' : F = .ok ((evs.val.map sedS).foldl (obSlStep (abs h) (abs s) (spS s.path)) #[]) := by
        rw [← hF, show sedsS evs.val = (evs.val.map sedS).toArray from rfl, List.forIn_toArray]
        apply ob_forIn_list_ex
        intro e o; rcases e with ⟨ty, _, _, _, _⟩; cases ty <;> rfl
      rw [hF']
      simp only [except_bind_ok]
      have hmax := usize_max64 h64
      have hev := alloc.vec.Vec.property evs
      unfold beatmap.objects.slider_nested_loop
      have H := loop_ok (fun (x : alloc.vec.Vec beatmap.objects.NestedObject × Usize) =>
          beatmap.objects.slider_nested_loop.body h.kind h.start_time h.position h.stack_height h.scale h.time_preempt
            h.time_fade_in h.new_combo h.combo_offset h.combo_index h.combo_index_with_offsets h.index_in_current_combo
            h.last_in_combo h.kiai h.hit_windows h.nested s.path s.classic_slider_behaviour s.strict_tracking evs x.1 x.2)
        (fun x => evs.val.length - x.2.val)
        (fun x => x.2.val ≤ evs.val.length ∧
          (x.1.val.map abs).toArray = ((evs.val.take x.2.val).map sedS).foldl (obSlStep (abs h) (abs s) (spS s.path)) #[] ∧
          x.1.val.length ≤ x.2.val)
        (fun (y : alloc.vec.Vec beatmap.objects.NestedObject) =>
          (y.val.map abs).toArray = (evs.val.map sedS).foldl (obSlStep (abs h) (abs s) (spS s.path)) #[]) (by
          rintro ⟨o, i⟩ ⟨h1, h2, h3⟩
          dsimp only at h1 h2 h3 ⊢
          by_cases hc : i.val < evs.val.length
          · right
            have hc' : i < alloc.vec.Vec.len evs := by show i.val < (alloc.vec.Vec.len evs).val; simpa using hc
            obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
            have htk : (evs.val.take i1.val).map sedS = (evs.val.take i.val).map sedS ++ [sedS (evs.val[i.val]'hc)] := by
              rw [hi1v, List.take_add_one, List.getElem?_eq_getElem hc]
              simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]
            have hrec : ({ kind := h.kind, start_time := h.start_time, position := h.position, stack_height := h.stack_height, scale := h.scale, time_preempt := h.time_preempt, time_fade_in := h.time_fade_in, new_combo := h.new_combo, combo_offset := h.combo_offset, combo_index := h.combo_index, combo_index_with_offsets := h.combo_index_with_offsets, index_in_current_combo := h.index_in_current_combo, last_in_combo := h.last_in_combo, kiai := h.kiai, hit_windows := h.hit_windows, nested := h.nested } : beatmap.objects.OsuHitObject) = h := rfl
            simp only [beatmap.objects.slider_nested_loop.body, hc', ite_true, vec_index_eq' evs i hc, bind_ok, hrec]
            have hb : o.val.length < Usize.max := by rw [hmax]; omega
            generalize evs.val[i.val]'hc = e at htk ⊢
            rcases e with ⟨ty, tm, si, sst, pp⟩
            cases ty with
            | LegacyLastTick =>
              refine ⟨(o, i1), by simp [hi1], ⟨by simp [hi1v]; omega, ?_, by simp [hi1v]; omega⟩, by simp [hi1v]; omega⟩
              dsimp only; rw [htk, List.foldl_append, ← h2]; rfl
            | Head =>
              obtain ⟨nd, hnd, hndv⟩ := beatmap.objects.nested_default_refines .Head tm
              obtain ⟨o1, ho1, ho1v⟩ := push_eq o { nd with position := h.position, stack_height := h.stack_height, classic_slider_behaviour := s.classic_slider_behaviour } hb
              refine ⟨(o1, i1), by simp only [hnd, bind_ok, ho1, hi1], ⟨by simp [hi1v]; omega, ?_, by simp [hi1v, ho1v]; omega⟩, by simp [hi1v]; omega⟩
              dsimp only; rw [htk, List.foldl_append, ← h2, ho1v, List.map_append, List.map_cons, List.map_nil, ← List.push_toArray]
              simp only [List.foldl_cons, List.foldl_nil, obSlStep, sedS, setS]
              congr 1
              show ({ (abs nd : NestedObject) with position := bv2S h.position, stackHeight := i32S h.stack_height, classicSliderBehaviour := s.classic_slider_behaviour }) = _
              rw [← hndv]; rfl
            | Tick =>
              obtain ⟨nd, hnd, hndv⟩ := beatmap.objects.nested_default_refines .Tick tm
              obtain ⟨o1, ho1, ho1v⟩ := push_eq o { nd with position := bv2I ((bv2S h.position).add (SliderPath.positionAt (spS s.path) pp)), stack_height := h.stack_height, path_progress := pp, span_index := si, span_start_time := sst } hb
              refine ⟨(o1, i1), ?_, ⟨by simp [hi1v]; omega, ?_, by simp [hi1v, ho1v]; omega⟩, by simp [hi1v]; omega⟩
              · simp only [hnd, bind_ok, beatmap.slider_path.position_at_refines _ _ hp.1 hp.2 h64,
                  beatmap.vector2.add_refines, bv2S_I]
                rw [ho1, bind_ok, hi1, bind_ok]
              · dsimp only; rw [htk, List.foldl_append, ← h2, ho1v, List.map_append, List.map_cons, List.map_nil, ← List.push_toArray]
                simp only [List.foldl_cons, List.foldl_nil, obSlStep, sedS, setS]
                congr 1
                show ({ (abs nd : NestedObject) with position := bv2S (bv2I ((bv2S h.position).add (SliderPath.positionAt (spS s.path) pp))), stackHeight := i32S h.stack_height, pathProgress := pp, spanIndex := i32S si, spanStartTime := sst }) = _
                rw [← hndv, bv2S_I]; rfl
            | Repeat =>
              let st := h.start_time + F64.ofInt (core.num.I32.wrapping_add si 1#i32).val * OsuHitObject.spanDuration (abs h)
              obtain ⟨nd, hnd, hndv⟩ := beatmap.objects.nested_default_refines .Repeat st
              obtain ⟨o1, ho1, ho1v⟩ := push_eq o { nd with position := bv2I ((bv2S h.position).add (SliderPath.positionAt (spS s.path) pp)), stack_height := h.stack_height, path_progress := pp, repeat_index := si } hb
              refine ⟨(o1, i1), ?_, ⟨by simp [hi1v]; omega, ?_, by simp [hi1v, ho1v]; omega⟩, by simp [hi1v]; omega⟩
              · simp only [lift, bind_ok, se_cast_i64, float.F64.from_i64, hrec, beatmap.objects.span_duration_refines,
                  float.F64.mul, float.F64.add]
                rw [show beatmap.objects.nested_default .Repeat st = ok nd from hnd, bind_ok]
                simp only [beatmap.slider_path.position_at_refines _ _ hp.1 hp.2 h64, bind_ok, beatmap.vector2.add_refines, bv2S_I]
                rw [ho1, bind_ok, hi1, bind_ok]
              · dsimp only; rw [htk, List.foldl_append, ← h2, ho1v, List.map_append, List.map_cons, List.map_nil, ← List.push_toArray]
                simp only [List.foldl_cons, List.foldl_nil, obSlStep, sedS, setS]
                congr 1
                show ({ (abs nd : NestedObject) with position := bv2S (bv2I ((bv2S h.position).add (SliderPath.positionAt (spS s.path) pp))), stackHeight := i32S h.stack_height, pathProgress := pp, repeatIndex := i32S si }) = _
                rw [← hndv, bv2S_I]
                have : F64.ofInt32 (i32S si + 1) = F64.ofInt (core.num.I32.wrapping_add si 1#i32).val := by
                  rw [← se_wrapping_add1]; simp [F64.ofInt32, i32S_toInt]
                rw [this]; rfl
            | Tail =>
              obtain ⟨nd, hnd, hndv⟩ := beatmap.objects.nested_default_refines .Tail tm
              obtain ⟨o1, ho1, ho1v⟩ := push_eq o { nd with position := bv2I (OsuHitObject.endPosition (abs h)), stack_height := h.stack_height, repeat_index := si, classic_slider_behaviour := s.classic_slider_behaviour, strict_tracking_tail := s.strict_tracking } hb
              refine ⟨(o1, i1), ?_, ⟨by simp [hi1v]; omega, ?_, by simp [hi1v, ho1v]; omega⟩, by simp [hi1v]; omega⟩
              · rw [hnd, bind_ok]
                simp only [hrec, beatmap.objects.end_position_refines h hph h64, bind_ok]
                rw [ho1, bind_ok, hi1, bind_ok]
              · dsimp only; rw [htk, List.foldl_append, ← h2, ho1v, List.map_append, List.map_cons, List.map_nil, ← List.push_toArray]
                simp only [List.foldl_cons, List.foldl_nil, obSlStep, sedS, setS]
                congr 1
                show ({ (abs nd : NestedObject) with position := bv2S (bv2I (OsuHitObject.endPosition (abs h))), stackHeight := i32S h.stack_height, repeatIndex := i32S si, classicSliderBehaviour := s.classic_slider_behaviour, strictTrackingTail := s.strict_tracking }) = _
                rw [← hndv, bv2S_I]; rfl
          · left
            have hc' : ¬ i < alloc.vec.Vec.len evs := by show ¬ i.val < (alloc.vec.Vec.len evs).val; simpa using hc
            refine ⟨o, by simp [beatmap.objects.slider_nested_loop.body, hc'], ?_⟩
            rw [h2]; have : i.val = evs.val.length := by omega
            rw [this, List.take_length])
        (alloc.vec.Vec.new _, 0#usize) ⟨by simp, by simp, by simp⟩
      obtain ⟨y, hy, hyv⟩ := H
      exact ⟨.Ok y, by rw [hy, bind_ok], hyv⟩

end OsuProofs
