/-
`beatmap::slider_path` (Rust) refines `OsuModel.Beatmap.SliderPath` (osu! `SliderPath` cache: calculatePath,
calculateLength, PositionAt). Maps: `spsS`/`spS` (field-wise; control points via `pcpsS` of HitObjectParser).
-/
import OsuProofs.Beatmap.PathApprox
import OsuProofs.Beatmap.HitObjectParser
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl
open OsuModel.Beatmap.PathApproximator

def spsS (s : beatmap.slider_path.SliderPathSpec) : SliderPathSpec :=
  { controlPoints := pcpsS s.control_points.val, expectedDistance := s.expected_distance,
    optimiseCatmull := s.optimise_catmull }
def spS (p : beatmap.slider_path.SliderPath) : SliderPath :=
  { spec := spsS p.spec, calculatedPath := vS p.calculated_path.val, cumulativeLength := p.cumulative_length.val.toArray,
    calculatedLength := p.calculated_length, fuelOut := p.fuel_out }

theorem sp_f64_default : (default : F64) = 0 := by decide

theorem beatmap.slider_path.distance_refines (p : beatmap.slider_path.SliderPath) :
    beatmap.slider_path.distance p = ok (SliderPath.distance (spS p)) := by
  unfold beatmap.slider_path.distance SliderPath.distance
  by_cases h : p.cumulative_length.val.length = 0
  · have h' : alloc.vec.Vec.len p.cumulative_length = 0#usize := by apply UScalar.eq_of_val_eq; simpa using h
    simp [h', spS, h]
  · have h' : ¬ alloc.vec.Vec.len p.cumulative_length = 0#usize := fun e => h (by simpa using congrArg UScalar.val e)
    obtain ⟨i, hi, hiv⟩ := usize_sub_one (alloc.vec.Vec.len p.cumulative_length) (by simp; omega)
    simp at hiv
    have hl : i.val < p.cumulative_length.val.length := by omega
    simp only [h', ite_false, hi, bind_ok, vec_index_eq' p.cumulative_length i hl]
    simp [spS, h, Array.back!, hiv]
    rw [List.getElem?_eq_getElem (by omega)]; rfl

theorem beatmap.slider_path.get_f64_refines (a : Slice F64) (i : Usize) :
    beatmap.slider_path.get_f64 a i = ok (a.val.toArray[i.val]!) := by
  unfold beatmap.slider_path.get_f64
  by_cases h : i.val < a.val.length
  · have h' : i < Slice.len a := by show i.val < (Slice.len a).val; simpa using h
    simp [h', index_eq a i h, h]
  · have h' : ¬ i < Slice.len a := by show ¬ i.val < (Slice.len a).val; simpa using h
    simp [h', h, sp_f64_default]

theorem beatmap.slider_path.progress_to_distance_refines (p : beatmap.slider_path.SliderPath) (progress : F64) :
    beatmap.slider_path.progress_to_distance p progress = ok (SliderPath.progressToDistance (spS p) progress) := by
  unfold beatmap.slider_path.progress_to_distance SliderPath.progressToDistance
  simp only [bmc_beatmap_slider_path_D0, bmc_beatmap_slider_path_D1, bind_ok, float.F64.lt,
    beatmap.slider_path.distance_refines, float.F64.mul]
  by_cases h1 : progress < 0 <;> by_cases h2 : (1 : F64) < progress <;> simp [h1, h2]

theorem beatmap.slider_path.interpolate_vertices_refines (p : beatmap.slider_path.SliderPath) (i : I64) (d : F64)
    (hl : p.calculated_path.val.length < 2^62) :
    beatmap.slider_path.interpolate_vertices p i d = ok (bv2I (SliderPath.interpolateVertices (spS p) i.val d)) := by
  unfold beatmap.slider_path.interpolate_vertices SliderPath.interpolateVertices
  have hsz : (spS p).calculatedPath.size = p.calculated_path.val.length := by simp [spS]
  by_cases h0 : p.calculated_path.val.length = 0
  · have h' : alloc.vec.Vec.len p.calculated_path = 0#usize := by apply UScalar.eq_of_val_eq; simpa using h0
    simp [h', hsz, h0, bm_vector2_ZERO]
  have h' : ¬ alloc.vec.Vec.len p.calculated_path = 0#usize := fun e => h0 (by simpa using congrArg UScalar.val e)
  have hsz0 : ((spS p).calculatedPath.size == 0) = false := by simp [hsz, h0]
  rw [if_neg h', if_neg (show ¬ (((spS p).calculatedPath.size == 0) = true) by simp [hsz0])]
  by_cases hi0 : i.val ≤ 0
  · have hi0' : i <= 0#i64 := (show i.val ≤ (0#i64).val by rw [show (0#i64).val = 0 from rfl]; exact hi0)
    rw [if_pos hi0', if_pos hi0, vec_index_eq' _ 0#usize (by simp; omega)]
    simp only [spS]; rw [vS_get! _ 0 (by omega), bv2I_S]; simp
  have hi0' : ¬ i <= 0#i64 := by
    intro h; apply hi0; have : i.val ≤ (0#i64).val := h; rw [show (0#i64).val = 0 from rfl] at this; exact this
  rw [if_neg hi0']
  simp only [hi0, ite_false]
  have hc : (UScalar.hcast .I64 (alloc.vec.Vec.len p.calculated_path)).val = p.calculated_path.val.length := by
    rw [usize_hcast_i64 _ (by simpa using hl)]; simp
  simp only [lift, bind_ok]
  by_cases hge : p.calculated_path.val.length ≤ i.val
  · have hge' : i >= UScalar.hcast .I64 (alloc.vec.Vec.len p.calculated_path) := by
      show (UScalar.hcast .I64 (alloc.vec.Vec.len p.calculated_path)).val ≤ i.val; rw [hc]; exact hge
    rw [if_pos hge']
    have hge2 : (p.calculated_path.val.length : Int) ≤ i.val := hge
    simp only [hsz, hge2, ite_true]
    obtain ⟨j, hj, hjv⟩ := usize_sub_one (alloc.vec.Vec.len p.calculated_path) (by simp; omega)
    simp at hjv
    rw [hj, bind_ok, vec_index_eq' _ j (by omega)]
    simp [spS, Array.back!, vS, hjv]
    rw [List.getElem?_eq_getElem (by omega)]; simp
  · have hge' : ¬ i >= UScalar.hcast .I64 (alloc.vec.Vec.len p.calculated_path) := by
      show ¬ (UScalar.hcast .I64 (alloc.vec.Vec.len p.calculated_path)).val ≤ i.val; rw [hc]; exact hge
    rw [if_neg hge']
    have hge2 : ¬ (p.calculated_path.val.length : Int) ≤ i.val := hge
    simp only [hsz, hge2, ite_false]
    have hiu : (IScalar.hcast .Usize i).val = i.val.toNat := by
      rw [IScalar.hcast_val_eq]; congr 1; apply Int.emod_eq_of_lt (by omega)
      have := alloc.vec.Vec.property p.calculated_path; rw [Usize.max_def] at this; simp [Usize.numBits] at this ⊢
      have h2 : (1 : Nat) ≤ 2^System.Platform.numBits := Nat.one_le_two_pow
      have : (p.calculated_path.val.length : Int) ≤ 2^System.Platform.numBits - 1 := by exact_mod_cast (by omega : p.calculated_path.val.length ≤ 2^System.Platform.numBits - 1)
      omega
    obtain ⟨i4, hi4, hi4v⟩ := usize_sub_one (IScalar.hcast .Usize i) (by omega)
    have e4 : i4.val < p.calculated_path.val.length := by omega
    have eu : (IScalar.hcast .Usize i).val < p.calculated_path.val.length := by omega
    rw [hi4, bind_ok, vec_index_eq' _ _ e4, bind_ok, vec_index_eq' _ _ eu, bind_ok,
      beatmap.slider_path.get_f64_refines, bind_ok, beatmap.slider_path.get_f64_refines, bind_ok,
      beatmap.vector2.almost_equals_f64_refines, bind_ok]
    simp only [deref_val]
    have hkv : i4.val = i.val.toNat - 1 := by omega
    have ed0 : (p.cumulative_length.val.toArray)[i4.val]! = (spS p).cumulativeLength[i.val.toNat - 1]! := by rw [hkv]; rfl
    have ed1 : (p.cumulative_length.val.toArray)[(IScalar.hcast .Usize i).val]! = (spS p).cumulativeLength[i.val.toNat]! := by
      rw [hiu]; rfl
    have ep0 : p.calculated_path.val[i4.val]'e4 = bv2I ((spS p).calculatedPath[i.val.toNat - 1]!) := by
      simp only [spS]; rw [vS_get! _ _ (by omega)]; simp [hkv]
    have ep1 : p.calculated_path.val[(IScalar.hcast .Usize i).val]'eu = bv2I ((spS p).calculatedPath[i.val.toNat]!) := by
      simp only [spS]; rw [vS_get! _ _ (by omega)]; simp [hiu]
    rw [ed0, ed1, ep0, ep1]
    split
    · rfl
    · simp only [bind_ok, float.F64.sub, float.F64.div, float.F64.to_f32, beatmap.vector2.sub_refines,
        beatmap.vector2.scale_refines, beatmap.vector2.add_refines, bv2S_I]
      rfl

theorem sp_i64_ok_add (a b : I64) (h1 : -2^61 ≤ a.val ∧ a.val ≤ 2^61) (h2 : -2^61 ≤ b.val ∧ b.val ≤ 2^61) :
    ∃ z, a + b = ok z ∧ z.val = a.val + b.val := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (I64.add_spec (x := a) (y := b) (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
  exact ⟨z, hz, by simpa using hv⟩
theorem sp_i64_ok_sub (a b : I64) (h1 : -2^61 ≤ a.val ∧ a.val ≤ 2^61) (h2 : -2^61 ≤ b.val ∧ b.val ≤ 2^61) :
    ∃ z, a - b = ok z ∧ z.val = a.val - b.val := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (I64.sub_spec (x := a) (y := b) (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
  exact ⟨z, hz, by simpa using hv⟩

def spBsR (a : Slice F64) (x : I64 × I64 × Option I64 × Usize) (k : Nat) (b : Option Int × Int × Int) : Prop :=
  x.2.2.2.val = k ∧ x.2.2.1 = none ∧ b = (none, x.1.val, x.2.1.val) ∧ 0 ≤ x.1.val ∧ x.1.val ≤ a.val.length ∧
    -1 ≤ x.2.1.val ∧ x.2.1.val ≤ a.val.length - 1
def spBsFin (a : Slice F64) (y : I64 × Option I64) (c : Option Int × Int × Int) : Prop :=
  y.2.map (·.val) = c.1 ∧ y.1.val = c.2.1 ∧ 0 ≤ y.1.val ∧ y.1.val ≤ a.val.length ∧
    ∀ r ∈ y.2, 0 ≤ r.val ∧ r.val < a.val.length

theorem sp_bs_step (a : Slice F64) (v : F64) (hl : a.val.length < 2^61) (h64 : System.Platform.numBits = 64)
    (f : Nat → Option Int × Int × Int → Id (ForInStep (Option Int × Int × Int)))
    (hf : ∀ k (s : Option Int × Int × Int), f k s =
      if s.2.1 ≤ s.2.2 then
        if (compareF64 a.val.toArray[(s.2.1 + (s.2.2 - s.2.1) / 2).toNat]! v == 0) = true then
          .done (some (s.2.1 + (s.2.2 - s.2.1) / 2), s.2.1, s.2.2)
        else if compareF64 a.val.toArray[(s.2.1 + (s.2.2 - s.2.1) / 2).toNat]! v < 0 then
          .yield (none, s.2.1 + (s.2.2 - s.2.1) / 2 + 1, s.2.2)
        else .yield (none, s.2.1, s.2.1 + (s.2.2 - s.2.1) / 2 - 1)
      else .yield (none, s.2.1, s.2.2)) :
    ∀ x k b, spBsR a x k b → k < a.val.length + 1 →
      (∃ c, (f k b : ForInStep _) = .yield c ∧ ∃ x', (fun (x : I64 × I64 × Option I64 × Usize) =>
        beatmap.dotnet.binary_search_f64_loop.body a v x.1 x.2.1 x.2.2.1 x.2.2.2) x = ok (.cont x') ∧ spBsR a x' (k+1) c) ∨
      (∃ c, (f k b : ForInStep _) = .done c ∧ ∃ y, loop (fun (x : I64 × I64 × Option I64 × Usize) =>
        beatmap.dotnet.binary_search_f64_loop.body a v x.1 x.2.1 x.2.2.1 x.2.2.2) x = ok y ∧ spBsFin a y c) := by
  rintro ⟨lo, hi, res, it⟩ k b ⟨hk, hres, hb, h0, h1, h2, h3⟩ hkl
  dsimp only at hk hres hb h0 h1 h2 h3 ⊢
  subst hres hb
  rw [hf]
  have hnone : core.option.Option.is_none (none : Option I64) = true := rfl
  have hmax := usize_max64 h64
  obtain ⟨n1, hn1, hn1v⟩ := usize_add_one (Slice.len a) (by simp; omega)
  have hit : it < n1 := by show it.val < n1.val; simp at hn1v; omega
  obtain ⟨it1, hit1, hit1v⟩ := usize_add_one it (by simp at hn1v; omega)
  by_cases hle : lo.val ≤ hi.val
  · have hle' : lo <= hi := hle
    obtain ⟨d, hd, hdv⟩ := sp_i64_ok_sub hi lo (by omega) (by omega)
    obtain ⟨q, hq, hqv⟩ := IScalar.div_spec (x := d) (y := 2#i64) (by simp) (by simp)
    have hq' : q.val = (hi.val - lo.val) / 2 := by
      rw [hqv]; simp [hdv]; rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
    obtain ⟨m, hm, hmv⟩ := sp_i64_ok_add lo q (by omega) (by rw [hq']; omega)
    have hmlo : lo.val ≤ m.val := by rw [hmv, hq']; omega
    have hmhi : m.val ≤ hi.val := by rw [hmv, hq']; omega
    have hmc : (IScalar.hcast .Usize m).val = m.val.toNat := by
      rw [IScalar.hcast_val_eq]; congr 1; apply Int.emod_eq_of_lt (by omega); simp [h64]; omega
    have hidx : (IScalar.hcast .Usize m).val < a.val.length := by rw [hmc]; omega
    obtain ⟨cr, hcr, hcrv⟩ := beatmap.dotnet.compare_f64_refines (a.val[(IScalar.hcast .Usize m).val]'hidx) v
    have hget : a.val.toArray[(lo.val + (hi.val - lo.val) / 2).toNat]! = a.val[(IScalar.hcast .Usize m).val]'hidx := by
      have e : (lo.val + (hi.val - lo.val) / 2).toNat = (IScalar.hcast .Usize m).val := by rw [hmc, hmv, hq']
      rw [e, getElem!_pos (a.val.toArray) _ (by simpa using hidx)]; simp
    simp only [hle, decide_true, ite_true, hget, ← hcrv]
    by_cases hc0 : cr.val = 0
    · right
      have hc0' : cr = 0#i32 := by apply IScalar.eq_of_val_eq; simpa using hc0
      refine ⟨(some (lo.val + (hi.val - lo.val) / 2), lo.val, hi.val), by simp [hc0], (lo, some m), ?_, ?_⟩
      · rw [loop_unfold]
        simp only [beatmap.dotnet.binary_search_f64_loop.body, hnone, ite_true, hn1, bind_ok, hit, hle', hd, hq, hm,
          lift, index_eq a _ hidx, hcr, hc0', hit1, uncurry_apply_pair]
        rw [loop_unfold]
        simp [beatmap.dotnet.binary_search_f64_loop.body]
      · refine ⟨by simp [hmv, hq'], rfl, h0, h1, ?_⟩
        intro r hr; simp at hr; subst hr; omega
    · left
      have hc0' : ¬ cr = 0#i32 := fun e => hc0 (by rw [e]; simp)
      by_cases hneg : cr.val < 0
      · have hneg' : cr < 0#i32 := by show cr.val < (0#i32).val; simpa using hneg
        obtain ⟨m1, hm1, hm1v⟩ := sp_i64_ok_add m 1#i64 (by omega) (by simp)
        refine ⟨_, by simp [hc0, hneg]; rfl, (m1, hi, none, it1), ?_, ?_⟩
        · simp only [beatmap.dotnet.binary_search_f64_loop.body, hnone, ite_true, hn1, bind_ok, hit, hle', hd, hq, hm,
            lift, index_eq a _ hidx, hcr, hc0', ite_false, hneg', hm1, hit1, uncurry_apply_pair]
        · refine ⟨by simp [hit1v, hk], rfl, by simp [hm1v, hmv, hq'], ?_, ?_, ?_, ?_⟩
          all_goals dsimp only
          all_goals (simp at hm1v; omega)
      · have hneg' : ¬ cr < 0#i32 := by show ¬ cr.val < (0#i32).val; simpa using hneg
        obtain ⟨m1, hm1, hm1v⟩ := sp_i64_ok_sub m 1#i64 (by omega) (by simp)
        refine ⟨_, by simp [hc0, hneg]; rfl, (lo, m1, none, it1), ?_, ?_⟩
        · simp only [beatmap.dotnet.binary_search_f64_loop.body, hnone, ite_true, hn1, bind_ok, hit, hle', hd, hq, hm,
            lift, index_eq a _ hidx, hcr, hc0', ite_false, hneg', hm1, hit1, uncurry_apply_pair]
        · refine ⟨by simp [hit1v, hk], rfl, by simp [hm1v, hmv, hq'], ?_, ?_, ?_, ?_⟩
          all_goals dsimp only
          all_goals (simp at hm1v; omega)
  · left
    have hle' : ¬ lo <= hi := hle
    refine ⟨_, by simp [hle]; rfl, (lo, hi, none, it1), ?_, ?_⟩
    · simp only [beatmap.dotnet.binary_search_f64_loop.body, hnone, ite_true, hn1, bind_ok, hit, hle', ite_false, hit1, uncurry_apply_pair]
    · exact ⟨by simp [hit1v, hk], rfl, rfl, h0, h1, h2, h3⟩

theorem sp_bs_f64_eq (a : Slice F64) (v : F64) (hl : a.val.length < 2^61)
    (h64 : System.Platform.numBits = 64) :
    ∃ r, beatmap.dotnet.binary_search_f64 a v = ok r ∧ r.val = binarySearchF64 a.val.toArray v ∧
      -(a.val.length : Int) - 1 ≤ r.val ∧ r.val < a.val.length := by
  unfold beatmap.dotnet.binary_search_f64 binarySearchF64
  have hc : (UScalar.hcast .I64 (Slice.len a)).val = a.val.length := by
    rw [usize_hcast_i64 _ (by simp; omega)]; simp
  obtain ⟨hi, hhi, hhiv⟩ := sp_i64_ok_sub (UScalar.hcast .I64 (Slice.len a)) 1#i64 (by rw [hc]; omega) (by simp)
  rw [hc] at hhiv
  simp only [lift, bind_ok, hhi]
  simp only [Id.run_bind, forIn_range_idx]
  generalize hS : iterIdx _ 0 _ _ = S
  have hsz : a.val.toArray.size = a.val.length := by simp
  rw [hsz] at hS
  obtain ⟨⟨lo, res⟩, hl1, hF⟩ := loop_iterIdx' (fun (x : I64 × I64 × Option I64 × Usize) =>
      beatmap.dotnet.binary_search_f64_loop.body a v x.1 x.2.1 x.2.2.1 x.2.2.2) _ (a.val.length + 1)
    (spBsR a) (spBsFin a) (sp_bs_step a v hl h64 _ (fun _ _ => rfl)) (by
      rintro ⟨lo, hi, res, it⟩ k b ⟨hk, hres, hb, h0, h1, h2, h3⟩ hkl
      dsimp only at hk hres hb h0 h1 h2 h3 ⊢
      subst hres hb
      obtain ⟨n1, hn1, hn1v⟩ := usize_add_one (Slice.len a) (by rw [usize_max64 h64]; simp; omega)
      have hit : ¬ it.val < n1.val := by simp at hn1v; omega
      exact ⟨(lo, none), by simp [beatmap.dotnet.binary_search_f64_loop.body, hn1, hit], rfl, rfl, h0, h1, by simp⟩)
    (0#i64, hi, none, 0#usize) 0 _ ⟨by simp, rfl, by simp [hhiv], by simp, by simp, by simp [hhiv],
      by simp [hhiv]⟩ hS
  obtain ⟨hF1, hF2, hF3, hF4, hF5⟩ := hF
  dsimp only at hl1 hF1 hF2 hF3 hF4
  unfold beatmap.dotnet.binary_search_f64_loop
  rw [hl1]
  simp only [bind_ok, uncurry_apply_pair, id_run_eq]
  cases res with
  | none =>
    rw [Option.map_none] at hF1
    obtain ⟨n, hn, hnv⟩ := eq_ok_of_spec (IScalar.neg_step lo (by intro h; rw [IScalar.min] at h; simp at h; omega))
    have hnv' : n.val = - lo.val := by simpa using hnv
    obtain ⟨r, hr, hrv⟩ := sp_i64_ok_sub n 1#i64 (by omega) (by simp)
    refine ⟨r, ?_, ?_, by simp at hrv ⊢; omega, by simp at hrv ⊢; omega⟩
    · show (do let i2 ← IScalar.neg lo; i2 - 1#i64) = ok r
      rw [hn, bind_ok, hr]
    · rw [← hF1, hrv, hnv', hF2]; simp; rfl
  | some r =>
    obtain ⟨hr0, hr1⟩ := hF5 r rfl
    refine ⟨r, by simp, ?_, by omega, hr1⟩
    rw [Option.map_some] at hF1
    rw [← hF1]; rfl

theorem beatmap.slider_path.index_of_distance_refines (p : beatmap.slider_path.SliderPath) (d : F64)
    (hl : p.cumulative_length.val.length < 2^61) (h64 : System.Platform.numBits = 64) :
    ∃ r, beatmap.slider_path.index_of_distance p d = ok r ∧ r.val = SliderPath.indexOfDistance (spS p) d := by
  obtain ⟨i, hi, hiv, hi0, hi1⟩ := sp_bs_f64_eq (alloc.vec.Vec.deref p.cumulative_length) d
    (by rw [deref_val]; exact hl) h64
  rw [deref_val] at hiv hi0 hi1
  unfold beatmap.slider_path.index_of_distance SliderPath.indexOfDistance
  simp only []
  rw [hi, bind_ok]
  have hcum : (spS p).cumulativeLength = p.cumulative_length.val.toArray := rfl
  rw [hcum, ← hiv]
  by_cases hn : i.val < 0
  · have hn' : i < 0#i64 := by show i.val < (0#i64).val; simpa using hn
    obtain ⟨n, hn2, hnv⟩ := eq_ok_of_spec (IScalar.neg_step i (by intro h; rw [IScalar.min] at h; simp at h; omega))
    have hnv' : n.val = - i.val := by simpa using hnv
    obtain ⟨r, hr, hrv⟩ := sp_i64_ok_sub n 1#i64 (by omega) (by simp)
    refine ⟨r, ?_, ?_⟩
    · rw [if_pos hn']; show (do let i2 ← IScalar.neg i; i2 - 1#i64) = ok r
      rw [hn2, bind_ok, hr]
    · rw [if_pos hn, hrv, hnv']; simp
  · have hn' : ¬ i < 0#i64 := by show ¬ i.val < (0#i64).val; simpa using hn
    exact ⟨i, by rw [if_neg hn'], by rw [if_neg hn]⟩

theorem beatmap.slider_path.position_at_refines (p : beatmap.slider_path.SliderPath) (progress : F64)
    (hl : p.cumulative_length.val.length < 2^61) (hl2 : p.calculated_path.val.length < 2^62)
    (h64 : System.Platform.numBits = 64) :
    beatmap.slider_path.position_at p progress = ok (bv2I (SliderPath.positionAt (spS p) progress)) := by
  obtain ⟨r, hr, hrv⟩ := beatmap.slider_path.index_of_distance_refines p (SliderPath.progressToDistance (spS p) progress) hl h64
  unfold beatmap.slider_path.position_at SliderPath.positionAt
  rw [beatmap.slider_path.progress_to_distance_refines, bind_ok, hr, bind_ok,
    beatmap.slider_path.interpolate_vertices_refines _ _ _ hl2, hrv]

/-- Spec body of `optimiseCatmullPath` (definitionally the spec's `for` body). -/
def spOcBody (sp : Array Vec2) (i : Nat) (s : Array Vec2 × F64 × Option Vec2 × F64) :
    ForInStep (Array Vec2 × F64 × Option Vec2 × F64) :=
  match s.2.2.1 with
  | none => .yield (s.1.push sp[i]!, s.2.1, some sp[i]!, s.2.2.2)
  | some ls =>
    if (decide (6 < (ls.distance sp[i]!).toF64) || (i + 1) % 100 == 0 || i == sp.size - 1) = true then
      .yield (s.1.push sp[i]!, s.2.1 + ((s.2.2.2 + (sp[i - 1]!.distance sp[i]!).toF64) - (ls.distance sp[i]!).toF64), none, 0)
    else .yield (s.1, s.2.1, s.2.2.1, s.2.2.2 + (sp[i - 1]!.distance sp[i]!).toF64)

theorem beatmap.slider_path.optimise_catmull_path_refines (sp : Slice net.osutk.Vector2) :
    ∃ r, beatmap.slider_path.optimise_catmull_path sp = ok r ∧
      (vS r.1.val, r.2) = SliderPath.optimiseCatmullPath (vS sp.val) := by
  unfold beatmap.slider_path.optimise_catmull_path SliderPath.optimiseCatmullPath
  rw [bmc_beatmap_slider_path_D0, bind_ok]
  simp only [Id.run_bind, forIn_range_idx, id_run_eq]
  generalize hS : iterIdx _ 0 _ _ = S
  have hS' : iterIdx (fun i s => spOcBody (vS sp.val) i s) 0 ((vS sp.val).size - 0) (#[], 0, none, 0) = S := by
    rw [← hS]; rfl
  rw [vS_size] at hS'
  unfold beatmap.slider_path.optimise_catmull_path_loop
  refine Exists.imp (fun y H => ⟨H.1, ?hv⟩) (loop_iterIdx' _ _ sp.val.length
    (fun (x : alloc.vec.Vec net.osutk.Vector2 × F64 × Option net.osutk.Vector2 × F64 × Usize) k
      (b : Array Vec2 × F64 × Option Vec2 × F64) =>
      x.2.2.2.2.val = k ∧ vS x.1.val = b.1 ∧ x.2.1 = b.2.1 ∧ x.2.2.1.map bv2S = b.2.2.1 ∧ x.2.2.2.1 = b.2.2.2 ∧
      (x.2.2.1.isSome → 1 ≤ k) ∧ x.1.val.length ≤ k)
    (fun (y : alloc.vec.Vec net.osutk.Vector2 × F64) (c : Array Vec2 × F64 × Option Vec2 × F64) =>
      vS y.1.val = c.1 ∧ y.2 = c.2.1)
    ?hstep ?hend (alloc.vec.Vec.new _, 0, none, 0, 0#usize) 0 (#[], 0, none, 0)
    ⟨by first | rfl | simp, by first | rfl | simp [vS], rfl, rfl, rfl, by first | rfl | simp, by first | rfl | simp⟩
    hS')
  case hv => obtain ⟨_, h1, h2⟩ := H; rw [h1, h2]; rfl
  case hend =>
    rintro ⟨pa, ln, ls, rm, i⟩ k b ⟨hi, h1, h2, h3, h4, h5, h6⟩ hk
    dsimp only at hi h1 h2 h3 h4 h5 h6
    have hlt : ¬ i < Slice.len sp := by show ¬ i.val < (Slice.len sp).val; simp; omega
    exact ⟨(pa, ln), by simp [beatmap.slider_path.optimise_catmull_path_loop.body, hlt], h1, h2⟩
  case hstep =>
    rintro ⟨pa, ln, ls, rm, i⟩ k ⟨b1, b2, b3, b4⟩ ⟨hi, h1, h2, h3, h4, h5, h6⟩ hk
    dsimp only at hi h1 h2 h3 h4 h5 h6
    subst hi h1 h2 h3 h4
    left
    dsimp only
    unfold spOcBody
    have hlt : i < Slice.len sp := by show i.val < (Slice.len sp).val; simpa using hk
    have hil : i.val < sp.val.length := hk
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := Slice.length_ineq sp; omega)
    have hpush : pa.val.length < Usize.max := by have := Slice.length_ineq sp; omega
    have hgi : (vS sp.val)[i.val]! = bv2S (sp.val[i.val]'hil) := vS_get! _ _ hil
    cases ls with
    | none =>
      obtain ⟨p1, hp1, hp1v⟩ := push_eq pa (sp.val[i.val]'hil) hpush
      refine ⟨_, rfl, (p1, ln, some (sp.val[i.val]'hil), rm, i1), ?_, ?_⟩
      · simp only [beatmap.slider_path.optimise_catmull_path_loop.body, hlt, ite_true, index_eq sp i hil, bind_ok, hp1,
          uncurry_apply_pair, hi1]
      · refine ⟨by simp [hi1v], ?_, rfl, ?_, rfl, by simp, by rw [hp1v]; simp; omega⟩
        · dsimp only; rw [hp1v, vS_push, hgi]
        · dsimp only; simp [hgi]
    | some l =>
      have hi1' : 1 ≤ i.val := h5 rfl
      obtain ⟨i2, hi2, hi2v⟩ := usize_sub_one i hi1'
      have hil2 : i2.val < sp.val.length := by omega
      have hgi2 : (vS sp.val)[i.val - 1]! = bv2S (sp.val[i2.val]'hil2) := by rw [vS_get! _ _ (by omega)]; simp [hi2v]
      simp only [Option.map_some]
      rw [hgi, hgi2, vS_size]
      let v := sp.val[i.val]'hil
      let v1 := sp.val[i2.val]'hil2
      let dist := F32.toF64 (Vec2.distance (bv2S l) (bv2S v))
      let rem2 := rm + F32.toF64 (Vec2.distance (bv2S v1) (bv2S v))
      have hd0 := bmc_beatmap_slider_path_D6
      have hvi : Slice.index_usize sp i = ok v := index_eq sp i hil
      have hvi2 : Slice.index_usize sp i2 = ok v1 := index_eq sp i2 hil2
      obtain ⟨i4, hi4, hi4v⟩ := eq_ok_of_spec (UScalar.rem_spec i1 (y := 100#usize) (by simp))
      obtain ⟨i6, hi6, hi6v⟩ := usize_sub_one (Slice.len sp) (by simp; omega)
      have hlt' : i < Slice.len sp := hlt
      have hi4' : i4.val = (i.val + 1) % 100 := by rw [hi4v, hi1v]; simp
      have hi6' : i6.val = sp.val.length - 1 := by simp at hi6v; omega
      have hpre : beatmap.slider_path.optimise_catmull_path_loop.body 0 sp pa ln (some l) rm i =
          (do
            let r ← (if 6 < dist then (do let p ← pa.push v; ok (p, ln + (rem2 - dist), (none : Option net.osutk.Vector2), (0 : F64)))
              else if i4 = 0#usize then (do let p ← pa.push v; ok (p, ln + (rem2 - dist), none, 0))
              else if i = i6 then (do let p ← pa.push v; ok (p, ln + (rem2 - dist), none, 0))
              else ok (pa, ln, some l, rem2))
            let (p2, l2, s2, r2) := r
            ok (.cont (p2, l2, s2, r2, i1))) := by
        simp only [beatmap.slider_path.optimise_catmull_path_loop.body, hlt', ite_true, hvi, bind_ok,
          beatmap.vector2.distance_refines, float.F32.to_f64, hi2, hvi2, float.F64.add, hd0, float.F64.lt,
          decide_eq_true_eq, hi1, hi4, hi6, float.F64.sub]
        rfl
      by_cases hC : (decide (6 < dist) || (i.val + 1) % 100 == 0 || i.val == sp.val.length - 1) = true
      · obtain ⟨p1, hp1, hp1v⟩ := push_eq pa v hpush
        have hbody : beatmap.slider_path.optimise_catmull_path_loop.body 0 sp pa ln (some l) rm i =
            ok (.cont (p1, ln + (rem2 - dist), none, 0, i1)) := by
          rw [hpre]
          by_cases h6 : 6 < dist
          · rw [if_pos h6, hp1]; simp [uncurry_apply_pair]
          · rw [if_neg h6]
            by_cases h100 : i4 = 0#usize
            · rw [if_pos h100, hp1]; simp [uncurry_apply_pair]
            · rw [if_neg h100]
              have h6' : i = i6 := by
                apply UScalar.eq_of_val_eq
                simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hC
                rcases hC with (h | h) | h
                · exact absurd h h6
                · exact absurd (UScalar.eq_of_val_eq (by rw [hi4']; simpa using h)) h100
                · rw [hi6']; exact h
              rw [if_pos h6', hp1]; simp [uncurry_apply_pair]
        refine ⟨_, by rw [if_pos hC], _, hbody, ?_⟩
        refine ⟨by simp [hi1v], ?_, rfl, rfl, rfl, by simp, by rw [hp1v]; simp; omega⟩
        dsimp only; rw [hp1v, vS_push]
      · have hbody : beatmap.slider_path.optimise_catmull_path_loop.body 0 sp pa ln (some l) rm i =
            ok (.cont (pa, ln, some l, rem2, i1)) := by
          rw [hpre]
          simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, not_or] at hC
          obtain ⟨⟨h6, h100⟩, hlast⟩ := hC
          have h100' : ¬ i4 = 0#usize := fun e => h100 (by have := congrArg UScalar.val e; rw [hi4'] at this; simpa using this)
          have hlast' : ¬ i = i6 := fun e => hlast (by have := congrArg UScalar.val e; rw [hi6'] at this; exact this)
          rw [if_neg h6, if_neg h100', if_neg hlast']; simp [uncurry_apply_pair]
        refine ⟨_, by rw [if_neg hC], _, hbody, ?_⟩
        refine ⟨by simp [hi1v], rfl, rfl, rfl, rfl, by simp, by dsimp only; omega⟩

theorem beatmap.slider_path.sub_bspline_refines (sub : Slice net.osutk.Vector2) (d : Option I32)
    (h64 : System.Platform.numBits = 64) (hl : sub.val.length < 2^32) :
    ∃ r, beatmap.slider_path.sub_bspline sub d = ok r ∧
      (vS r.1.val, r.2) =
        let b := bSplineToPiecewiseLinear (vS sub.val)
          (match d.map i32S with | some d => d.toNatClampNeg | none => (vS sub.val).size)
        (b.1, (0 : F64), b.2) := by
  unfold beatmap.slider_path.sub_bspline
  cases d with
  | none =>
    obtain ⟨⟨v, fo⟩, hv, hvv⟩ := beatmap.path_approximator.b_spline_to_piecewise_linear_refines sub (Slice.len sub) h64 hl
    refine ⟨(v, 0, fo), by simp [hv], ?_⟩
    have e : (vS sub.val).size = (Slice.len sub).val := by simp [vS_size]
    simp only [Option.map_none]
    rw [e, ← hvv]
  | some d =>
    by_cases hn : d.val < 0
    · have hn' : d < 0#i32 := by show d.val < (0#i32).val; simpa using hn
      obtain ⟨⟨v, fo⟩, hv, hvv⟩ := beatmap.path_approximator.b_spline_to_piecewise_linear_refines sub 0#usize h64 hl
      refine ⟨(v, 0, fo), by simp [hn', hv], ?_⟩
      have e : (0#usize).val = (i32S d).toNatClampNeg := by
        simp [Int32.toNatClampNeg, i32S_toInt]; omega
      simp only [Option.map_some]
      rw [← e, ← hvv]
    · have hn' : ¬ d < 0#i32 := by show ¬ d.val < (0#i32).val; simpa using hn
      obtain ⟨⟨v, fo⟩, hv, hvv⟩ := beatmap.path_approximator.b_spline_to_piecewise_linear_refines sub (IScalar.hcast .Usize d) h64 hl
      refine ⟨(v, 0, fo), by simp [hn', hv], ?_⟩
      have e : (IScalar.hcast .Usize d).val = (i32S d).toNatClampNeg := by
        rw [IScalar.hcast_val_eq]
        have := d.hBounds
        simp [Int32.toNatClampNeg, i32S_toInt, h64] at this ⊢
        rw [Int.emod_eq_of_lt (by omega) (by omega)]
      simp only [Option.map_some]
      rw [← e, ← hvv]

theorem beatmap.slider_path.calculate_sub_path_refines (sub : Slice net.osutk.Vector2) (pt : beatmap.types.PathType)
    (oc : Bool) (h64 : System.Platform.numBits = 64) (hl : sub.val.length < 2^32) :
    ∃ r, beatmap.slider_path.calculate_sub_path sub pt oc = ok r ∧
      (vS r.1.val, r.2) = SliderPath.calculateSubPath (vS sub.val) (ptS pt) oc := by
  unfold beatmap.slider_path.calculate_sub_path SliderPath.calculateSubPath
  cases pt with
  | Catmull =>
    obtain ⟨c, hc, hcv⟩ := beatmap.path_approximator.catmull_to_piecewise_linear_refines sub h64 hl
    simp only [ptS, hc, bind_ok]
    cases oc
    · refine ⟨(c, 0, false), by simp, ?_⟩; simp [hcv]
    · obtain ⟨⟨r1, r2⟩, hr, hrv⟩ := beatmap.slider_path.optimise_catmull_path_refines (alloc.vec.Vec.deref c)
      rw [deref_val, hcv] at hrv
      exact ⟨(r1, r2, false), by simp [hr], by simp [← hrv]⟩
  | BSpline d =>
    obtain ⟨r, hr, hrv⟩ := beatmap.slider_path.sub_bspline_refines sub d h64 hl
    exact ⟨r, hr, by rw [hrv]; cases d <;> rfl⟩
  | Linear =>
    obtain ⟨v, hv, hvv⟩ := beatmap.path_approximator.linear_to_piecewise_linear_refines sub
    exact ⟨(v, 0, false), by simp [hv], by simp [ptS, hvv]⟩
  | PerfectCurve =>
    obtain ⟨bn, hbn, hbnv⟩ := beatmap.slider_path.sub_bspline_refines sub none h64 hl
    simp only [Option.map_none] at hbnv
    simp only [ptS]
    by_cases h3 : sub.val.length = 3
    · have h3' : ¬ (Slice.len sub != 3#usize) = true := by simp; exact h3
      have h3s : ¬ ((vS sub.val).size != 3) = true := by simp [h3]
      rw [if_neg h3', if_neg h3s]
      obtain ⟨pr, hpr, hprv⟩ := beatmap.path_approximator.circular_arc_properties_refines sub (by omega)
      rw [hpr, bind_ok, ← hprv]
      by_cases hv : pr.is_valid = true
      · rw [if_pos hv, if_neg (show ¬ ((!(arcS pr).isValid) = true) by simp [arcS, hv]),
          beatmap.path_approximator.arc_point_count_refines, bind_ok]
        have e : (i32I (arcPointCount (arcS pr))).val = (arcPointCount (arcS pr)).toInt := rfl
        by_cases hk : 1000 ≤ (arcPointCount (arcS pr)).toInt
        · have hk' : i32I (arcPointCount (arcS pr)) >= 1000#i32 := by
            show (1000#i32).val ≤ (i32I (arcPointCount (arcS pr))).val; rw [e]; simpa using hk
          have hk2 : arcPointCount (arcS pr) ≥ 1000 := by rw [ge_iff_le, Int32.le_iff_toInt_le]; simpa using hk
          rw [if_pos hk', if_pos hk2]
          exact ⟨bn, hbn, hbnv⟩
        · have hk' : ¬ i32I (arcPointCount (arcS pr)) >= 1000#i32 := by
            show ¬ (1000#i32).val ≤ (i32I (arcPointCount (arcS pr))).val; rw [e]; simpa using hk
          have hk2 : ¬ arcPointCount (arcS pr) ≥ 1000 := by rw [ge_iff_le, Int32.le_iff_toInt_le]; simpa using hk
          rw [if_neg hk', if_neg hk2]
          obtain ⟨c, hc, hcv⟩ := beatmap.path_approximator.circular_arc_to_piecewise_linear_refines sub h64 (by omega) hl
          rw [hc, bind_ok, ← hcv]
          by_cases hz : c.val.length = 0
          · have hz' : alloc.vec.Vec.len c = 0#usize := by apply UScalar.eq_of_val_eq; simpa using hz
            rw [if_pos hz', if_pos (by simp [hz])]
            exact ⟨bn, hbn, hbnv⟩
          · have hz' : ¬ alloc.vec.Vec.len c = 0#usize := fun e => hz (by simpa using congrArg UScalar.val e)
            rw [if_neg hz', if_neg (by simp [hz])]
            exact ⟨(c, 0, false), by simp, rfl⟩
      · have hv' : pr.is_valid = false := by simpa using hv
        rw [if_neg hv, if_pos (show ((!(arcS pr).isValid) = true) by simp [arcS, hv'])]
        exact ⟨bn, hbn, hbnv⟩
    · have h3' : (Slice.len sub != 3#usize) = true := by simp; exact h3
      have h3s : ((vS sub.val).size != 3) = true := by simp [h3]
      rw [if_pos h3', if_pos h3s]
      exact ⟨bn, hbn, hbnv⟩

/-- `next_segment_end` (no spec counterpart: the spec's `calculatePath` scans inline) returns `from` when
`from ≥ n`, else the first `r ≥ from` whose control point has a type or is the last one. -/
theorem beatmap.slider_path.next_segment_end_refines (sp : beatmap.slider_path.SliderPathSpec) (fr : Usize) :
    ∃ r, beatmap.slider_path.next_segment_end sp fr = ok r ∧
      (sp.control_points.val.length ≤ fr.val → r = fr) ∧
      (fr.val < sp.control_points.val.length → fr.val ≤ r.val ∧ ∃ hr : r.val < sp.control_points.val.length,
        (∀ j (hj : j < sp.control_points.val.length), fr.val ≤ j → j < r.val → (sp.control_points.val[j]'hj).ptype = none) ∧
        ((sp.control_points.val[r.val]'hr).ptype ≠ none ∨ r.val = sp.control_points.val.length - 1)) := by
  unfold beatmap.slider_path.next_segment_end beatmap.slider_path.next_segment_end_loop
  have hcp := alloc.vec.Vec.property sp.control_points
  generalize sp.control_points = cps at *
  have H := loop_ok (fun (x : Usize × Bool) => beatmap.slider_path.next_segment_end_loop.body cps (alloc.vec.Vec.len cps) x.1 x.2)
    (fun x => cps.val.length + 1 - x.1.val - (if x.2 then 1 else 0))
    (fun x => (cps.val.length ≤ fr.val → x = (fr, false)) ∧ (fr.val < cps.val.length → fr.val ≤ x.1.val ∧
       ∃ hr : x.1.val < cps.val.length,
        (∀ j (hj : j < cps.val.length), fr.val ≤ j → j < x.1.val → (cps.val[j]'hj).ptype = none) ∧
        (x.2 = true → (cps.val[x.1.val]'hr).ptype ≠ none ∨ x.1.val = cps.val.length - 1)))
    (fun (r : Usize) => (cps.val.length ≤ fr.val → r = fr) ∧ (fr.val < cps.val.length → fr.val ≤ r.val ∧
       ∃ hr : r.val < cps.val.length,
        (∀ j (hj : j < cps.val.length), fr.val ≤ j → j < r.val → (cps.val[j]'hj).ptype = none) ∧
        ((cps.val[r.val]'hr).ptype ≠ none ∨ r.val = cps.val.length - 1)))
    (by
      rintro ⟨i, found⟩ ⟨hP1, hP2⟩
      simp only at hP1 hP2 ⊢
      unfold beatmap.slider_path.next_segment_end_loop.body
      cases found
      · simp only [Bool.false_eq_true, if_false]
        by_cases hin : i < alloc.vec.Vec.len cps
        · rw [if_pos hin]
          have hin' : i.val < cps.val.length := by simpa [alloc.vec.Vec.len] using hin
          have hfr : fr.val < cps.val.length := by
            by_contra hc; have := hP1 (by omega); simp at this; subst this; omega
          obtain ⟨h1, _, h2, _⟩ := hP2 hfr
          have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice beatmap.types.PathControlPoint) cps i
              = ok (cps.val[i.val]'hin') := by
            simp [alloc.vec.Vec.index]; exact index_eq _ i hin'
          rw [hidx]; try simp only [bind_tc_ok, bind_ok]
          right
          by_cases hn : (cps.val[i.val]'hin').ptype = none
          · have hb : core.option.Option.is_none (cps.val[i.val]'hin').ptype = true := by
              simp [core.option.Option.is_none, hn]
            rw [if_pos hb]
            obtain ⟨z, hz, hzv⟩ := usize_sub_one (alloc.vec.Vec.len cps) (by simp [alloc.vec.Vec.len]; omega)
            replace hzv : z.val = cps.val.length - 1 := by rw [hzv]; rfl
            rw [hz]; try simp only [bind_tc_ok, bind_ok]
            by_cases hl : i.val < cps.val.length - 1
            · rw [if_pos (show i < z by scalar_tac)]
              obtain ⟨i2, ha, hav⟩ : ∃ i2, i + 1#usize = ok i2 ∧ i2.val = i.val + 1 :=
                eq_ok_of_spec (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
              rw [ha]; try simp only [bind_tc_ok, bind_ok]
              refine ⟨_, rfl, ⟨fun h => by omega, fun _ => ⟨by simp; omega, by simp; omega, fun j hj hj1 hj2 => ?_, fun h => by simp at h⟩⟩, by simp; omega⟩
              by_cases hji : j = i.val
              · subst hji; exact hn
              · exact h2 j hj hj1 (by simp at hj2; omega)
            · rw [if_neg (show ¬ (i < z) by scalar_tac)]
              refine ⟨_, rfl, ⟨fun h => by omega, fun _ => ⟨h1, hin', h2, fun _ => Or.inr (by dsimp only; omega)⟩⟩, by simp; omega⟩
          · have hb : core.option.Option.is_none (cps.val[i.val]'hin').ptype = false := by
              simp [core.option.Option.is_none]; cases h : (cps.val[i.val]'hin').ptype <;> simp_all
            rw [if_neg (by rw [hb]; simp)]
            refine ⟨_, rfl, ⟨fun h => by omega, fun _ => ⟨h1, hin', h2, fun _ => Or.inl hn⟩⟩, by simp; omega⟩
        · rw [if_neg hin]
          left; refine ⟨i, rfl, ?_, ?_⟩
          · intro h; have := hP1 h; simp at this; exact this
          · intro h; obtain ⟨_, hr, _⟩ := hP2 h; exfalso; apply hin; simp [alloc.vec.Vec.len]; scalar_tac
      · simp only [if_true]
        left; refine ⟨i, rfl, ?_, ?_⟩
        · intro h; have := hP1 h; simp at this
        · intro h; obtain ⟨h1, hr, h2, h3⟩ := hP2 h; exact ⟨h1, hr, h2, h3 rfl⟩)
    (fr, false) (by
      refine ⟨fun _ => rfl, fun h => ⟨le_refl _, h, fun j _ h1 h2 => absurd h2 (by simp; omega), fun h => by simp at h⟩⟩)
  exact H

theorem sp_cl_loop0 (p : alloc.vec.Vec net.osutk.Vector2) (ol : F64) (c0 : alloc.vec.Vec F64) (hc0 : c0.val = [0])
    (hl : p.val.length < 2^62) {S : F64 × Array F64}
    (hS : iterIdx (fun i (s : F64 × Array F64) => (pure (ForInStep.yield
        (s.1 + ((vS p.val)[i + 1]! - (vS p.val)[i]!).length.toF64,
         s.2.push (s.1 + ((vS p.val)[i + 1]! - (vS p.val)[i]!).length.toF64)) : Id _)))
      0 ((vS p.val).size - 1 - 0) (ol, #[0]) = S) :
    ∃ y, beatmap.slider_path.calculate_length_loop0 p ol c0 0#usize = ok y ∧
      y.1 = S.1 ∧ y.2.val.toArray = S.2 ∧ y.2.val.length = p.val.length - 1 + 1 := by
  rw [vS_size] at hS
  unfold beatmap.slider_path.calculate_length_loop0
  obtain ⟨n1, hn1, hn1v⟩ := beatmap.dotnet.nat_sub_refines (alloc.vec.Vec.len p) 1#usize
  simp at hn1v
  exact loop_iterIdx' _ _ (p.val.length - 1)
    (fun (x : F64 × alloc.vec.Vec F64 × Usize) k (b : F64 × Array F64) =>
      x.2.2.val = k ∧ x.1 = b.1 ∧ x.2.1.val.toArray = b.2 ∧ x.2.1.val.length = k + 1 ∧ k ≤ p.val.length - 1)
    (fun (y : F64 × alloc.vec.Vec F64) (c : F64 × Array F64) =>
      y.1 = c.1 ∧ y.2.val.toArray = c.2 ∧ y.2.val.length = p.val.length - 1 + 1)
    (by
      rintro ⟨cl, cum, i⟩ k ⟨b1, b2⟩ ⟨hi, h1, h2, h3, h4⟩ hk
      dsimp only at hi h1 h2 h3 h4 ⊢
      subst hi h1 h2
      left
      have hlt : i < n1 := by show i.val < n1.val; omega
      have hil : i.val < p.val.length := by omega
      have hil1 : i.val + 1 < p.val.length := by omega
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by scalar_tac)
      have hil1' : i1.val < p.val.length := by omega
      have hX : ((vS p.val)[i.val + 1]! - (vS p.val)[i.val]!) = (bv2S (p.val[i1.val]'hil1')).sub (bv2S (p.val[i.val]'hil)) := by
        rw [vS_get! _ _ hil1, vS_get! _ _ hil]; simp only [hi1v]; rfl
      rw [hX]
      obtain ⟨c1, hc1, hc1v⟩ := push_eq cum (cl + ((bv2S (p.val[i1.val]'hil1')).sub (bv2S (p.val[i.val]'hil))).length.toF64) (by scalar_tac)
      refine ⟨_, rfl, (cl + ((bv2S (p.val[i1.val]'hil1')).sub (bv2S (p.val[i.val]'hil))).length.toF64, c1, i1), ?_, ?_⟩
      · simp only [beatmap.slider_path.calculate_length_loop0.body, hn1, bind_tc_ok, bind_ok, hlt, ite_true, hi1,
          vec_index_eq' p i1 hil1', vec_index_eq' p i hil, beatmap.vector2.sub_refines, beatmap.vector2.length_refines,
          float.F32.to_f64, float.F64.add, bv2S_I, hc1]
      · refine ⟨by simp [hi1v], rfl, ?_, by rw [hc1v]; simp; omega, by omega⟩
        rw [hc1v]; simp)
    (by
      rintro ⟨cl, cum, i⟩ k b ⟨hi, h1, h2, h3, h4⟩ hk
      dsimp only at hi h1 h2 h3 h4
      have hlt : ¬ i < n1 := by show ¬ i.val < n1.val; omega
      refine ⟨(cl, cum), by simp only [beatmap.slider_path.calculate_length_loop0.body, hn1, bind_tc_ok, bind_ok, hlt, ite_false], h1, h2, by rw [h3]; omega⟩)
    (ol, c0, 0#usize) 0 (ol, #[0]) ⟨rfl, rfl, by simp [hc0], by simp [hc0], by omega⟩ hS
theorem sp_cl_loop21 : @beatmap.slider_path.calculate_length_loop2 = @beatmap.slider_path.calculate_length_loop1 := by
  funext a b c d e f
  unfold beatmap.slider_path.calculate_length_loop2 beatmap.slider_path.calculate_length_loop1
    beatmap.slider_path.calculate_length_loop2.body beatmap.slider_path.calculate_length_loop1.body
  rfl
theorem sp_cl_loop31 : @beatmap.slider_path.calculate_length_loop3 = @beatmap.slider_path.calculate_length_loop1 := by
  funext a b c d e f
  unfold beatmap.slider_path.calculate_length_loop3 beatmap.slider_path.calculate_length_loop1
    beatmap.slider_path.calculate_length_loop3.body beatmap.slider_path.calculate_length_loop1.body
  rfl
theorem sp_vec_pop {α} (v : alloc.vec.Vec α) : ∃ o w, alloc.vec.Vec.pop alloc.alloc.Global v = ok (o, w) ∧ w.val = v.val.dropLast := by
  unfold alloc.vec.Vec.pop
  exact ⟨_, _, rfl, by simp⟩

theorem sp_cl_loop1 (ed : F64) (p : alloc.vec.Vec net.osutk.Vector2) (c : alloc.vec.Vec F64) (pei : I64)
    (lim : Usize) (e : Nat) (hlim : lim.val = e) (hpei : pei.val = (p.val.length : Int) - 1)
    (hc : c.val.length + 1 = max p.val.length 1) (hl : p.val.length < 2^62)
    {S : Array Vec2 × Array F64 × Int}
    (hS : iterIdx (fun _ (s : Array Vec2 × Array F64 × Int) =>
        (if (decide (s.2.1.size > 0) && decide (ed ≤ s.2.1.back!)) = true then
          pure (ForInStep.yield (s.1.pop, s.2.1.pop, s.2.2 - 1))
        else pure (ForInStep.yield (s.1, s.2.1, s.2.2)) : Id _))
      0 (e - 0) (vS p.val, c.val.toArray, pei.val) = S) :
    ∃ y, beatmap.slider_path.calculate_length_loop1 p c ed pei 0#usize lim = ok y ∧
      vS y.1.val = S.1 ∧ y.2.1.val.toArray = S.2.1 ∧ y.2.2.val = S.2.2 ∧
      y.2.2.val = (y.1.val.length : Int) - 1 ∧ y.2.1.val.length + 1 = max y.1.val.length 1 ∧ y.1.val.length < 2^62 := by
  unfold beatmap.slider_path.calculate_length_loop1
  exact loop_iterIdx' _ _ e
    (fun (x : alloc.vec.Vec net.osutk.Vector2 × alloc.vec.Vec F64 × I64 × Usize) k (b : Array Vec2 × Array F64 × Int) =>
      x.2.2.2.val = k ∧ vS x.1.val = b.1 ∧ x.2.1.val.toArray = b.2.1 ∧ x.2.2.1.val = b.2.2 ∧
      x.2.2.1.val = (x.1.val.length : Int) - 1 ∧ x.2.1.val.length + 1 = max x.1.val.length 1 ∧
      x.1.val.length < 2^62 ∧ k ≤ e)
    (fun (y : alloc.vec.Vec net.osutk.Vector2 × alloc.vec.Vec F64 × I64) (b : Array Vec2 × Array F64 × Int) =>
      vS y.1.val = b.1 ∧ y.2.1.val.toArray = b.2.1 ∧ y.2.2.val = b.2.2 ∧
      y.2.2.val = (y.1.val.length : Int) - 1 ∧ y.2.1.val.length + 1 = max y.1.val.length 1 ∧ y.1.val.length < 2^62)
    (by
      rintro ⟨pa, cu, pe, k⟩ i ⟨b1, b2, b3⟩ ⟨hk, h1, h2, h3, h4, h5, h6, h7⟩ hi
      dsimp only at hk h1 h2 h3 h4 h5 h6 h7 ⊢
      subst hk h1 h2 h3
      left
      have hlt : k < lim := by show k.val < lim.val; omega
      obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by scalar_tac)
      by_cases hcl : cu.val.length = 0
      · have hcl' : ¬ (alloc.vec.Vec.len cu > 0#usize) := by show ¬ (0#usize).val < (alloc.vec.Vec.len cu).val; simp [hcl]
        refine ⟨(vS pa.val, cu.val.toArray, pe.val), by simp [hcl]; rfl, (pa, cu, pe, k1), ?_, by simp [hk1v], rfl, rfl, rfl, h4, h5, h6, by omega⟩
        simp only [beatmap.slider_path.calculate_length_loop1.body, hlt, ite_true, hcl', ite_false, bind_ok, bind_tc_ok,
          uncurry_apply_pair, hk1]
      · have hcl' : alloc.vec.Vec.len cu > 0#usize := by show (0#usize).val < (alloc.vec.Vec.len cu).val; simp; omega
        obtain ⟨j, hj, hjv⟩ := usize_sub_one (alloc.vec.Vec.len cu) (by simp; omega)
        simp at hjv
        have hjl : j.val < cu.val.length := by omega
        have hback : cu.val.toArray.back! = cu.val[j.val]'hjl := by
          simp [Array.back!, hjv]; rw [List.getElem?_eq_getElem (by omega)]; rfl
        by_cases hle : ed ≤ cu.val[j.val]'hjl
        · have hpl : 2 ≤ pa.val.length := by omega
          obtain ⟨o1, c2, hc2, hc2v⟩ := sp_vec_pop cu
          obtain ⟨o2, p2, hp2, hp2v⟩ := sp_vec_pop pa
          obtain ⟨pe2, hpe2, hpe2v⟩ : ∃ z, pe - 1#i64 = ok z ∧ z.val = pe.val - 1 :=
            eq_ok_of_spec (I64.sub_spec (x := pe) (y := 1#i64) (by scalar_tac) (by scalar_tac))
          refine ⟨((vS pa.val).pop, cu.val.toArray.pop, pe.val - 1), by simp [hcl, hback, hle, (show 0 < cu.val.length by omega)]; try rfl, (p2, c2, pe2, k1), ?_, by simp [hk1v], ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
          · simp only [beatmap.slider_path.calculate_length_loop1.body, hlt, ite_true, hcl', bind_ok, bind_tc_ok,
              uncurry_apply_pair, hk1, hj, vec_index_eq' cu j hjl, float.F64.le, hle, decide_true, hc2, hp2, hpe2]
          · rw [hp2v]; simp [vS, List.map_dropLast]
          · rw [hc2v]; simp
          · rw [hpe2v]
          · rw [hpe2v, hp2v, h4]; simp; omega
          · rw [hp2v, hc2v]; simp; omega
          · rw [hp2v]; simp; omega
        · refine ⟨(vS pa.val, cu.val.toArray, pe.val), by simp [hcl, hback, hle, (show 0 < cu.val.length by omega)]; try rfl, (pa, cu, pe, k1), ?_, by simp [hk1v], rfl, rfl, rfl, h4, h5, h6, by omega⟩
          simp only [beatmap.slider_path.calculate_length_loop1.body, hlt, ite_true, hcl', bind_ok, bind_tc_ok,
            uncurry_apply_pair, hk1, hj, vec_index_eq' cu j hjl, float.F64.le, hle, decide_false, ite_false, Bool.false_eq_true])
    (by
      rintro ⟨pa, cu, pe, k⟩ i b ⟨hk, h1, h2, h3, h4, h5, h6, h7⟩ hi
      dsimp only at hk h1 h2 h3 h4 h5 h6 h7
      have hlt : ¬ k < lim := by show ¬ k.val < lim.val; omega
      exact ⟨(pa, cu, pe), by simp only [beatmap.slider_path.calculate_length_loop1.body, hlt, ite_false], h1, h2, h3, h4, h5, h6⟩)
    (p, c, pei, 0#usize) 0 (vS p.val, c.val.toArray, pei.val) ⟨rfl, rfl, rfl, rfl, hpei, hc, hl, by omega⟩ hS

theorem sp_hcast_usize (x : I64) (h64 : System.Platform.numBits = 64) (h0 : 0 ≤ x.val) (h1 : x.val < 2^62) :
    (IScalar.hcast .Usize x).val = x.val.toNat := by
  rw [IScalar.hcast_val_eq]
  have : (2:Int)^62 ≤ 2^UScalarTy.Usize.numBits := by simp [UScalarTy.Usize_numBits_eq, h64]
  rw [Int.emod_eq_of_lt h0 (by omega)]

theorem sp_len_lt (n : Nat) (h64 : System.Platform.numBits = 64) (h : n < 2^62) : n < Usize.max := by
  have : Usize.max = 2^64 - 1 := by simp [Usize.max, Usize.numBits, h64]
  omega

theorem sp_id_bind {α β : Type} (x : α) (f : α → Id β) : (x >>= f : Id β) = f x := rfl

theorem sp_cl_tail (sp : beatmap.slider_path.SliderPathSpec) (path : alloc.vec.Vec net.osutk.Vector2)
    (cumulative_length4 : alloc.vec.Vec F64) (path_end_index1 : I64) (ed calculated_length : F64)
    (h64 : System.Platform.numBits = 64)
    (hpe : path_end_index1.val = (path.val.length : Int) - 1) (hc : cumulative_length4.val.length + 1 = max path.val.length 1)
    (hl : path.val.length < 2^62) :
    ∃ r, (if path_end_index1 ≤ 0#i64 then do
            let cumulative_length5 ← cumulative_length4.push 0
            ok ({ spec := sp, calculated_path := path, cumulative_length := cumulative_length5, calculated_length := calculated_length, fuel_out := false } : beatmap.slider_path.SliderPath)
          else do
            let e ← lift (IScalar.hcast UScalarTy.Usize path_end_index1)
            let v2 ←
              alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice net.osutk.Vector2) path e
            let i6 ← e - 1#usize
            let v3 ←
              alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice net.osutk.Vector2) path i6
            let v4 ← beatmap.vector2.sub v2 v3
            let dir ← beatmap.vector2.normalized v4
            let i8 ← cumulative_length4.len - 1#usize
            let last ←
              alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice float.F64) cumulative_length4
                  i8
            let v5 ←
              alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice net.osutk.Vector2) path i6
            let f1 ← float.F64.sub ed last
            let f2 ← float.F64.to_f32 f1
            let v6 ← beatmap.vector2.scale dir f2
            let v7 ← beatmap.vector2.add v5 v6
            let (_, index_mut_back) ←
              alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice net.osutk.Vector2) path e
            let cumulative_length5 ← cumulative_length4.push ed
            ok
                ({ spec := sp, calculated_path := index_mut_back v7, cumulative_length := cumulative_length5, calculated_length := calculated_length, fuel_out := false } :
                  beatmap.slider_path.SliderPath)) = ok r ∧
      spS r = (if path_end_index1.val ≤ 0 then
          { spec := spsS sp, calculatedPath := vS path.val, cumulativeLength := cumulative_length4.val.toArray.push 0, calculatedLength := calculated_length }
        else
          { spec := spsS sp, calculatedPath := (vS path.val).set! path_end_index1.val.toNat ((vS path.val)[path_end_index1.val.toNat - 1]! + ((vS path.val)[path_end_index1.val.toNat]! - (vS path.val)[path_end_index1.val.toNat - 1]!).normalized * (ed - cumulative_length4.val.toArray.back!).toF32), cumulativeLength := cumulative_length4.val.toArray.push ed, calculatedLength := calculated_length } : SliderPath):= by
  by_cases h0 : path_end_index1.val ≤ 0
  · have h0' : path_end_index1 ≤ 0#i64 := (show path_end_index1.val ≤ (0#i64).val by simpa using h0)
    obtain ⟨c5, hc5, hc5v⟩ := push_eq cumulative_length4 0 (by scalar_tac)
    refine ⟨_, by rw [if_pos h0', hc5, bind_ok], ?_⟩
    rw [if_pos h0]; simp [spS, hc5v]
  · have h0' : ¬ path_end_index1 ≤ 0#i64 := fun h => h0 (by have : path_end_index1.val ≤ (0#i64).val := h; simpa using this)
    rw [if_neg h0', if_neg h0]
    have hcast := sp_hcast_usize path_end_index1 h64 (by omega) (by omega)
    set e := IScalar.hcast UScalarTy.Usize path_end_index1
    have hel : e.val < path.val.length := by omega
    obtain ⟨i6, hi6, hi6v⟩ := usize_sub_one e (by omega)
    have hil6 : i6.val < path.val.length := by omega
    obtain ⟨i8, hi8, hi8v⟩ := usize_sub_one (alloc.vec.Vec.len cumulative_length4) (by simp; omega)
    simp at hi8v
    have hil8 : i8.val < cumulative_length4.val.length := by omega
    have hpos : 0 < cumulative_length4.val.length := by omega
    obtain ⟨c5, hc5, hc5v⟩ := push_eq cumulative_length4 ed (by scalar_tac)
    simp only [lift, bind_ok, vec_index_eq' path e hel, hi6, vec_index_eq' path i6 hil6, beatmap.vector2.sub_refines,
      beatmap.vector2.normalized_refines, hi8, vec_index_eq' cumulative_length4 i8 hil8, float.F64.sub, float.F64.to_f32,
      beatmap.vector2.scale_refines, beatmap.vector2.add_refines, bind_tc_ok, alloc.vec.Vec.index_mut_slice_index,
      vec_index_mut_usize_eq path e hel, uncurry_apply_pair, hc5, bv2S_I]
    refine ⟨_, rfl, ?_⟩
    have he : path_end_index1.val.toNat = e.val := by omega
    simp only [spS, hc5v, he, vS_get! _ _ hel, vS_get! _ _ (show e.val - 1 < path.val.length by omega)]
    have hb : cumulative_length4.val.toArray.back! = cumulative_length4.val[i8.val]'hil8 := by
      simp [Array.back!, hi8v]; rw [List.getElem?_eq_getElem (by omega)]; rfl
    have hsv : (path.set e (bv2I ((bv2S (path.val[i6.val]'hil6)).add (((bv2S (path.val[e.val]'hel)).sub (bv2S (path.val[i6.val]'hil6))).normalized.scale (F64.toF32 (ed - cumulative_length4.val[i8.val]'hil8)))))).val
        = path.val.set e.val (bv2I ((bv2S (path.val[i6.val]'hil6)).add (((bv2S (path.val[e.val]'hel)).sub (bv2S (path.val[i6.val]'hil6))).normalized.scale (F64.toF32 (ed - cumulative_length4.val[i8.val]'hil8))))) := by
      simp [alloc.vec.Vec.set]
    rw [hsv, vS_set, hb]
    simp only [show e.val - 1 = i6.val by omega, bv2S_I, List.push_toArray]
    rfl

set_option hygiene false in
macro "sp_cl_pop" : tactic => `(tactic| (
  simp only [hc3, bind_ok, uncurry_apply_pair, lift, hpe, float.F64.lt, decide_eq_true_eq]
  rw [hsz, hc3a]
  by_cases hlt2 : ed < cl
  · rw [if_pos hlt2, if_pos hlt2]
    obtain ⟨lim, hlim, hlimv⟩ := usize_add_one (alloc.vec.Vec.len p0) (by have := sp_len_lt _ h64 hl; simp; omega)
    rw [hlim, bind_ok]
    generalize hS2 : iterIdx _ 0 _ _ = S'
    rw [← hpev] at hS2
    obtain ⟨⟨pa, cu, pe1⟩, hy2, e1, e2, e3, e4, e5, e6⟩ := sp_cl_loop1 ed p0 c3 pe lim (p0.val.length + 1) (by simp [hlimv]) hpev hc3l hl hS2
    rw [hy2, bind_ok]
    rw [sp_id_bind]; try dsimp only
    rw [← e1, ← e2, ← e3]
    have T := sp_cl_tail sp pa cu pe1 ed cl h64 e4 e5 e6
    simp only [lift, bind_ok] at T
    exact T
  · rw [if_neg hlt2, if_neg hlt2]
    rw [← hpev]
    have T := sp_cl_tail sp p0 c3 pe ed cl h64 hpev hc3l hl
    simp only [lift, bind_ok] at T
    exact T))

theorem beatmap.slider_path.calculate_length_refines (sp : beatmap.slider_path.SliderPathSpec)
    (p0 : alloc.vec.Vec net.osutk.Vector2) (ol : F64) (hl : p0.val.length < 2^62)
    (h64 : System.Platform.numBits = 64) :
    ∃ r, beatmap.slider_path.calculate_length sp p0 ol = ok r ∧
      spS r = SliderPath.calculateLength (spsS sp) (vS p0.val) ol := by
  unfold beatmap.slider_path.calculate_length SliderPath.calculateLength
  simp only [forIn_range_idx, id_run_eq]
  generalize hS : iterIdx _ 0 _ _ = S
  obtain ⟨c0, hc0, hc0v⟩ := push_eq (alloc.vec.Vec.with_capacity F64 (alloc.vec.Vec.len p0)) 0 (by simp [alloc.vec.Vec.with_capacity]; scalar_tac)
  simp only [alloc.vec.Vec.with_capacity] at hc0v
  rw [bmc_beatmap_slider_path_D0, bind_ok, hc0, bind_ok]
  obtain ⟨⟨cl, cum⟩, hy, h1, h2, h3⟩ := sp_cl_loop0 p0 ol c0 (by simpa using hc0v) hl hS
  rw [hy, bind_ok]
  obtain ⟨S1, S2⟩ := S
  dsimp only at h1 h2 h3 ⊢
  subst h1 h2
  rw [sp_cl_loop21, sp_cl_loop31]
  rw [show (spsS sp).expectedDistance = sp.expected_distance from rfl]
  cases hed : sp.expected_distance with
  | none => exact ⟨_, rfl, rfl⟩
  | some ed =>
    simp only [float.F64.eq, bind_ok, uncurry_apply_pair]
    have hsz : (vS p0.val).size = p0.val.length := vS_size _
    rw [sp_id_bind]; try dsimp only
    by_cases heq : (cl == ed) = true
    · rw [if_pos heq, if_pos heq]; exact ⟨_, rfl, rfl⟩
    rw [if_neg heq, if_neg heq]
    obtain ⟨o1, c3, hc3, hc3v⟩ := sp_vec_pop cum
    have hi4 : (UScalar.hcast .I64 (alloc.vec.Vec.len p0)).val = p0.val.length := usize_hcast_i64 _ (by simpa using hl)
    obtain ⟨pe, hpe, hpev⟩ : ∃ z, (UScalar.hcast .I64 (alloc.vec.Vec.len p0)) - 1#i64 = ok z ∧ z.val = (UScalar.hcast .I64 (alloc.vec.Vec.len p0)).val - 1 :=
      eq_ok_of_spec (I64.sub_spec (x := UScalar.hcast .I64 (alloc.vec.Vec.len p0)) (y := 1#i64) (by rw [hi4]; scalar_tac) (by rw [hi4]; scalar_tac))
    rw [hi4] at hpev
    have hc3l : c3.val.length + 1 = max p0.val.length 1 := by rw [hc3v]; simp; omega
    have hc3a : cum.val.toArray.pop = c3.val.toArray := by rw [hc3v]; simp
    by_cases hA : (decide ((vS p0.val).size ≥ 2) && (vS p0.val)[(vS p0.val).size - 1]!.eq (vS p0.val)[(vS p0.val).size - 2]! && decide (cl < ed)) = true
    · rw [if_pos hA]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hA
      obtain ⟨⟨h2, heqv⟩, hlt⟩ := hA
      rw [hsz] at h2 heqv
      have hn : p0.len ≥ 2#usize := by show (2#usize).val ≤ (alloc.vec.Vec.len p0).val; simp; omega
      obtain ⟨j1, hj1, hj1v⟩ := usize_sub_one (alloc.vec.Vec.len p0) (by simp; omega)
      obtain ⟨j2, hj2, hj2v⟩ : ∃ z, alloc.vec.Vec.len p0 - 2#usize = ok z ∧ z.val = p0.val.length - 2 := by
        obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (Usize.sub_spec (x := alloc.vec.Vec.len p0) (y := 2#usize) (by simp; omega))
        simp at hzv; exact ⟨z, hz, hzv.1⟩
      simp at hj1v
      rw [vS_get! _ _ (by omega), vS_get! _ _ (by omega)] at heqv
      simp only [show p0.val.length - 1 = j1.val by omega, show p0.val.length - 2 = j2.val by omega] at heqv
      obtain ⟨c4, hc4, hc4v⟩ := push_eq cum cl (sp_len_lt _ h64 (by omega))
      rw [if_pos hn]
      simp only [hj1, bind_ok, vec_index_eq' p0 j1 (by omega), hj2, vec_index_eq' p0 j2 (by omega), beatmap.vector2.eq_refines,
        float.F64.lt, decide_eq_true_eq]
      rw [if_pos heqv, if_pos hlt, hc4, bind_ok]
      refine ⟨_, rfl, ?_⟩
      simp [spS, hc4v]; rfl
    · rw [if_neg hA]
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hA
      by_cases hn : p0.len ≥ 2#usize
      · have h2 : 2 ≤ p0.val.length := by have : (2#usize).val ≤ (alloc.vec.Vec.len p0).val := hn; simpa using this
        obtain ⟨j1, hj1, hj1v⟩ := usize_sub_one (alloc.vec.Vec.len p0) (by simp; omega)
        obtain ⟨j2, hj2, hj2v⟩ : ∃ z, alloc.vec.Vec.len p0 - 2#usize = ok z ∧ z.val = p0.val.length - 2 := by
          obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (Usize.sub_spec (x := alloc.vec.Vec.len p0) (y := 2#usize) (by simp; omega))
          simp at hzv; exact ⟨z, hz, hzv.1⟩
        simp at hj1v
        rw [if_pos hn]
        simp only [hj1, bind_ok, vec_index_eq' p0 j1 (by omega), hj2, vec_index_eq' p0 j2 (by omega), beatmap.vector2.eq_refines,
          float.F64.lt, decide_eq_true_eq]
        by_cases hb1 : (bv2S (p0.val[j1.val]'(by omega))).eq (bv2S (p0.val[j2.val]'(by omega))) = true
        · rw [if_pos hb1]
          have hlt : ¬ cl < ed := by
            refine hA ⟨by try simp only [hsz]; omega, ?_⟩
            try simp only [hsz]
            rw [vS_get! _ _ (by omega), vS_get! _ _ (by omega)]
            simp only [show p0.val.length - 1 = j1.val by omega, show p0.val.length - 2 = j2.val by omega]; exact hb1
          rw [if_neg hlt]
          sp_cl_pop
        · rw [if_neg hb1]
          sp_cl_pop
      · rw [if_neg hn]
        sp_cl_pop

/-- One `calculatePath` segment `cps[start..=i]` appended to `path`; `some ol` iff the spec adds `ol`. -/
def spSeg (cps : Array PathControlPoint) (oc : Bool) (start i : Nat) (path : Array Vec2) :
    Array Vec2 × Option F64 × Bool :=
  let sv := (cps.map (·.position)).extract start (i + 1)
  if (sv.size == 1) = true then (path.push sv[0]!, none, false)
  else if sv.size > 1 then
    let r := SliderPath.calculateSubPath sv (cps[start]!.type.getD .linear) oc
    let sk := if (decide (path.size > 0) && decide (r.1.size > 0) && path.back!.eq r.1[0]!) = true then 1 else 0
    (iterIdx (fun j (p : Array Vec2) => (pure (.yield (p.push r.1[j]!)) : Id _)) sk (r.1.size - sk) path, some r.2.1, r.2.2)
  else (path, none, false)

def spCpBody (cps : Array PathControlPoint) (oc : Bool) (i : Nat) (s : Array Vec2 × F64 × Bool × Nat) :
    ForInStep (Array Vec2 × F64 × Bool × Nat) :=
  if (cps[i]!.type.isNone && decide (i < cps.size - 1)) = true then .yield s
  else
    let r := spSeg cps oc s.2.2.2 i s.1
    .yield (r.1, (match r.2.1 with | none => s.2.1 | some x => s.2.1 + x), s.2.2.1 || r.2.2, i)

theorem sp_iterIdx_congr {β : Type} {f g : Nat → β → Id (ForInStep β)} (h : ∀ i s, f i s = g i s) (a n : Nat) (b : β) :
    iterIdx f a n b = iterIdx g a n b := by
  have : f = g := funext fun i => funext fun s => h i s
  rw [this]

theorem sp_calculatePath_eq (sp : SliderPathSpec) :
    SliderPath.calculatePath sp = if sp.controlPoints.size = 0 then (#[], 0, false) else
      let S := iterIdx (fun i s => (spCpBody sp.controlPoints sp.optimiseCatmull i s : Id _)) 0 sp.controlPoints.size
        (#[], 0, false, 0)
      (S.1, S.2.1, S.2.2.1) := by
  unfold SliderPath.calculatePath
  simp only [forIn_range_idx, id_run_eq]
  by_cases h0 : sp.controlPoints.size = 0
  · simp [h0]; rfl
  rw [if_neg (by simpa using h0), if_neg h0]
  rw [sp_iterIdx_congr (g := fun i s => (spCpBody sp.controlPoints sp.optimiseCatmull i s : Id _))]
  · rw [sp_id_bind, Nat.sub_zero]; rfl
  · intro i s
    simp only [spCpBody, spSeg]
    split_ifs <;> first | rfl | (simp only [Bool.or_false]; rfl) | simp

theorem sp_iterIdx_add {β : Type} (f : Nat → β → Id (ForInStep β)) (hy : ∀ i b, ∃ c, (f i b : ForInStep β) = .yield c) :
    ∀ (a n i : Nat) (b : β), iterIdx f i (a + n) b = iterIdx f (i + a) n (iterIdx f i a b) := by
  intro a
  induction a with
  | zero => intro n i b; simp [iterIdx_zero]
  | succ a ih =>
    intro n i b
    obtain ⟨c, hc⟩ := hy i b
    rw [show a + 1 + n = (a + n) + 1 by omega, iterIdx_succ, iterIdx_succ, hc]
    simp only
    rw [ih n (i+1) c, show i + 1 + a = i + (a + 1) by omega]

/-- Simulation where one Aeneas iteration covers `k ≥ 1` iterations of a yield-only spec loop. -/
theorem sp_loop_iterIdx_multi {α γ β : Type} (body : α → Result (ControlFlow α γ))
    (f : Nat → β → Id (ForInStep β)) (hy : ∀ i b, ∃ c, (f i b : ForInStep β) = .yield c)
    (e : Nat) (R : α → Nat → β → Prop) (Fin : γ → β → Prop)
    (hstep : ∀ x i b, R x i b → i < e →
      ∃ k, 1 ≤ k ∧ i + k ≤ e ∧ ∃ x', body x = ok (.cont x') ∧ R x' (i + k) (iterIdx f i k b))
    (hend : ∀ x i b, R x i b → e ≤ i → ∃ y, body x = ok (.done y) ∧ Fin y b) :
    ∀ x i b, R x i b → i ≤ e → ∃ y, loop body x = ok y ∧ Fin y (iterIdx f i (e - i) b) := by
  intro x i b
  induction hm : e - i using Nat.strong_induction_on generalizing x i b with
  | _ n ih =>
    intro hR hie
    by_cases hlt : i < e
    · obtain ⟨k, hk1, hke, x', hb, hR'⟩ := hstep x i b hR hlt
      obtain ⟨y, hy', hF⟩ := ih (e - (i + k)) (by omega) x' (i + k) _ rfl hR' hke
      refine ⟨y, by rw [loop_unfold, hb]; simpa using hy', ?_⟩
      rw [show n = k + (e - (i + k)) by omega, sp_iterIdx_add f hy]
      exact hF
    · obtain ⟨y, hb, hF⟩ := hend x i b hR (by omega)
      have : n = 0 := by omega
      subst this
      exact ⟨y, by rw [loop_unfold, hb]; simp, by rw [iterIdx_zero]; exact hF⟩

theorem sp_iterIdx_skip {β : Type} (f : Nat → β → Id (ForInStep β)) (s : β) :
    ∀ (n a : Nat), (∀ j, a ≤ j → j < a + n → (f j s : ForInStep β) = .yield s) → iterIdx f a n s = s := by
  intro n
  induction n with
  | zero => intro a _; rfl
  | succ n ih =>
    intro a h
    rw [iterIdx_succ, h a (le_refl _) (by omega)]
    exact ih (a+1) (fun j h1 h2 => h j (by omega) (by omega))

theorem sp_cps_loop1 (path sub : alloc.vec.Vec net.osutk.Vector2) (j : Usize)
    (hl : path.val.length + (sub.val.length - j.val) ≤ Usize.max) {S : Array Vec2}
    (hS : iterIdx (fun j (p : Array Vec2) => (pure (.yield (p.push (vS sub.val)[j]!)) : Id _)) j.val ((vS sub.val).size - j.val) (vS path.val) = S) :
    ∃ y, beatmap.slider_path.calculate_path_segment_loop1 path sub j = ok y ∧ vS y.val = S := by
  rw [vS_size] at hS
  unfold beatmap.slider_path.calculate_path_segment_loop1
  exact loop_iterIdx' _ _ sub.val.length
    (fun (x : alloc.vec.Vec net.osutk.Vector2 × Usize) k (b : Array Vec2) =>
      x.2.val = k ∧ vS x.1.val = b ∧ x.1.val.length + (sub.val.length - k) = path.val.length + (sub.val.length - j.val) ∧ j.val ≤ k)
    (fun (y : alloc.vec.Vec net.osutk.Vector2) (b : Array Vec2) => vS y.val = b)
    (by
      rintro ⟨p, k⟩ i b ⟨hk, h1, h2, h3⟩ hi
      dsimp only at hk h1 h2 h3 ⊢
      subst hk h1
      left
      have hlt : k < alloc.vec.Vec.len sub := by show k.val < (alloc.vec.Vec.len sub).val; simpa using hi
      obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := alloc.vec.Vec.property sub; scalar_tac)
      obtain ⟨p1, hp1, hp1v⟩ := push_eq p (sub.val[k.val]'hi) (by omega)
      refine ⟨_, rfl, (p1, k1), ?_, by simp [hk1v], ?_, by rw [hp1v]; simp <;> omega, by omega⟩
      · simp only [beatmap.slider_path.calculate_path_segment_loop1.body, hlt, ite_true, vec_index_eq' sub k hi, bind_ok, hp1, hk1]
      · rw [hp1v, vS_push, vS_get! _ _ hi])
    (by
      rintro ⟨p, k⟩ i b ⟨hk, h1, h2, h3⟩ hi
      dsimp only at hk h1 h2 h3
      have hlt : ¬ k < alloc.vec.Vec.len sub := by show ¬ k.val < (alloc.vec.Vec.len sub).val; simp; omega
      exact ⟨p, by simp only [beatmap.slider_path.calculate_path_segment_loop1.body, hlt, ite_false], h1⟩)
    (path, j) j.val (vS path.val) ⟨rfl, rfl, by dsimp only <;> omega, le_refl _⟩ hS

theorem sp_cps_loop0 (sp : beatmap.slider_path.SliderPathSpec) (start i : Usize) (hsi : start.val ≤ i.val)
    (hin : i.val < sp.control_points.val.length) :
    ∃ y, beatmap.slider_path.calculate_path_segment_loop0 sp i (alloc.vec.Vec.new _) start = ok y ∧ y.1 = sp ∧
      vS y.2.val = ((pcpsS sp.control_points.val).map (·.position)).extract start.val (i.val + 1) := by
  unfold beatmap.slider_path.calculate_path_segment_loop0
  have hcp := alloc.vec.Vec.property sp.control_points
  obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by scalar_tac)
  have H := loop_ok (fun (x : alloc.vec.Vec net.osutk.Vector2 × Usize) => beatmap.slider_path.calculate_path_segment_loop0.body sp i x.1 x.2)
    (fun x => i.val + 1 - x.2.val)
    (fun x => start.val ≤ x.2.val ∧ x.2.val ≤ i.val + 1 ∧
      x.1.val = ((sp.control_points.val.drop start.val).take (x.2.val - start.val)).map (·.position))
    (fun y => y.1 = sp ∧ y.2.val = ((sp.control_points.val.drop start.val).take (i.val + 1 - start.val)).map (·.position))
    (by
      rintro ⟨sv, k⟩ ⟨h1, h2, h3⟩
      dsimp only at h1 h2 h3 ⊢
      by_cases hk : k.val < i.val + 1
      · right
        have hlt : k < i1 := by show k.val < i1.val; omega
        have hkl : k.val < sp.control_points.val.length := by omega
        obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by scalar_tac)
        obtain ⟨s1, hs1, hs1v⟩ := push_eq sv (sp.control_points.val[k.val]'hkl).position (by rw [h3]; simp; scalar_tac)
        refine ⟨(s1, k1), ?_, ⟨by dsimp only; omega, by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
        · simp only [beatmap.slider_path.calculate_path_segment_loop0.body, hi1, bind_ok, hlt, ite_true,
            vec_index_eq' sp.control_points k hkl, hs1, hk1]
        · dsimp only
          rw [hs1v, h3, hk1v, show k.val + 1 - start.val = (k.val - start.val) + 1 by omega, List.take_add_one]
          simp [List.getElem?_drop, show start.val + (k.val - start.val) = k.val by omega, List.getElem?_eq_getElem hkl]
      · left
        have hlt : ¬ k < i1 := by show ¬ k.val < i1.val; omega
        refine ⟨(sp, sv), ?_, rfl, ?_⟩
        · simp only [beatmap.slider_path.calculate_path_segment_loop0.body, hi1, bind_ok, hlt, ite_false]
        · dsimp only; rw [h3, show k.val = i.val + 1 by omega])
    (alloc.vec.Vec.new _, start) ⟨le_refl _, by dsimp only; omega, by simp⟩
  obtain ⟨y, hy, hy1, hy2⟩ := H
  refine ⟨y, hy, hy1, ?_⟩
  rw [hy2]
  simp [vS, pcpsS, pcpS, List.map_take, List.map_drop]
  rfl
theorem sp_seg_ptS (o : Option beatmap.types.PathType) :
    ptS (match o with | none => beatmap.types.PathType.Linear | some t => t) = (o.map ptS).getD .linear := by
  cases o <;> rfl

theorem sp_iterIdx_push_size (r : Array Vec2) :
    ∀ n a (p : Array Vec2), (iterIdx (fun j (p : Array Vec2) => (pure (.yield (p.push r[j]!)) : Id _)) a n p).size = p.size + n := by
  intro n
  induction n with
  | zero => intro a p; rfl
  | succ n ih => intro a p; rw [iterIdx_succ]; exact (ih (a+1) (p.push r[a]!)).trans (by simp; omega)

theorem sp_match_ok (o : Option beatmap.types.PathType) :
    (match o with | none => ok beatmap.types.PathType.Linear | some t => ok t : Result beatmap.types.PathType) =
      ok (match o with | none => beatmap.types.PathType.Linear | some t => t) := by
  cases o <;> rfl

theorem sp_seg_tail (path sub : alloc.vec.Vec net.osutk.Vector2) (ol : F64) (fo : Bool) (b : Bool)
    (hsz : (iterIdx (fun j (p : Array Vec2) => (pure (.yield (p.push (vS sub.val)[j]!)) : Id _)) (if b = true then 1 else 0)
      ((vS sub.val).size - if b = true then 1 else 0) (vS path.val)).size ≤ Usize.max) :
    ∃ r, (do
          let j ← if b = true then ok 1#usize else ok 0#usize
          let path ← beatmap.slider_path.calculate_path_segment_loop1 path sub j
          ok (path, some ol, fo)) = ok r ∧
      (vS r.1.val, r.2) = (iterIdx (fun j (p : Array Vec2) => (pure (.yield (p.push (vS sub.val)[j]!)) : Id _)) (if b = true then 1 else 0)
      ((vS sub.val).size - if b = true then 1 else 0) (vS path.val), some ol, fo) := by
  rw [sp_iterIdx_push_size, vS_size, vS_size] at hsz
  cases b
  · obtain ⟨y, hy, hyv⟩ := sp_cps_loop1 path sub 0#usize (by simp at hsz ⊢; omega) (S := iterIdx (fun j (p : Array Vec2) => (pure (.yield (p.push (vS sub.val)[j]!)) : Id _)) 0 ((vS sub.val).size - 0) (vS path.val)) rfl
    simp only [Bool.false_eq_true, ite_false, bind_ok, hy]
    exact ⟨_, rfl, by rw [hyv]⟩
  · obtain ⟨y, hy, hyv⟩ := sp_cps_loop1 path sub 1#usize (by simp at hsz ⊢; omega) (S := iterIdx (fun j (p : Array Vec2) => (pure (.yield (p.push (vS sub.val)[j]!)) : Id _)) 1 ((vS sub.val).size - 1) (vS path.val)) rfl
    simp only [ite_true, bind_ok, hy]
    exact ⟨_, rfl, by rw [hyv]⟩

theorem beatmap.slider_path.calculate_path_segment_refines (sp : beatmap.slider_path.SliderPathSpec) (start i : Usize)
    (path : alloc.vec.Vec net.osutk.Vector2) (h64 : System.Platform.numBits = 64) (hsi : start.val ≤ i.val)
    (hin : i.val < sp.control_points.val.length) (hn : sp.control_points.val.length < 2^32)
    (hsz : (spSeg (pcpsS sp.control_points.val) sp.optimise_catmull start.val i.val (vS path.val)).1.size ≤ Usize.max) :
    ∃ r, beatmap.slider_path.calculate_path_segment sp start i path = ok r ∧
      (vS r.1.val, r.2) = spSeg (pcpsS sp.control_points.val) sp.optimise_catmull start.val i.val (vS path.val) := by
  obtain ⟨⟨sp1, sv⟩, h0, hsp, hsv⟩ := sp_cps_loop0 sp start i hsi hin
  dsimp only at hsp hsv; subst sp1
  have hsl : sv.val.length = i.val + 1 - start.val := by
    have := congrArg Array.size hsv; simp [vS_size, pcpsS] at this; omega
  have hstl : start.val < sp.control_points.val.length := by omega
  unfold spSeg at hsz ⊢
  simp only [] at hsz ⊢
  rw [← hsv] at hsz ⊢
  unfold beatmap.slider_path.calculate_path_segment
  rw [h0, bind_ok]; simp only [uncurry_apply_pair]
  rw [vec_index_eq' sp.control_points start hstl, bind_ok]
  have hpt : ((pcpsS sp.control_points.val)[start.val]!).type.getD .linear =
      ptS (match (sp.control_points.val[start.val]'hstl).ptype with | none => beatmap.types.PathType.Linear | some t => t) := by
    rw [sp_seg_ptS]; simp [pcpsS, pcpS, hstl]
  rw [hpt] at hsz ⊢
  cases hpo : (sp.control_points.val[start.val]'hstl).ptype
  all_goals simp only [hpo, bind_ok] at hsz ⊢
  case' none => generalize beatmap.types.PathType.Linear = st at hsz ⊢
  case' some st => skip
  all_goals
    have hsvS : (vS sv.val).size = sv.val.length := vS_size _
    rw [hsvS] at hsz ⊢
    by_cases h1 : sv.val.length = 1
    · have h1' : alloc.vec.Vec.len sv = 1#usize := by apply UScalar.eq_of_val_eq; simpa using h1
      rw [if_pos h1'] 
      simp only [h1, beq_self_eq_true, ite_true] at hsz ⊢
      obtain ⟨p1, hp1, hp1v⟩ := push_eq path (sv.val[(0#usize).val]'(by simp; omega)) (by simp [vS_size] at hsz; omega)
      rw [vec_index_eq' sv 0#usize (by simp; omega), bind_ok, hp1, bind_ok]
      refine ⟨_, rfl, ?_⟩
      rw [hp1v, vS_push, vS_get! _ _ (by omega)]; rfl
    · have h1' : ¬ alloc.vec.Vec.len sv = 1#usize := fun e => h1 (by simpa using congrArg UScalar.val e)
      have h2 : alloc.vec.Vec.len sv > 1#usize := by show (1#usize).val < (alloc.vec.Vec.len sv).val; simp; omega
      rw [if_neg h1', if_pos h2]
      have h1b : ¬ ((sv.val.length == 1) = true) := by simpa using h1
      have h2b : sv.val.length > 1 := by omega
      rw [if_neg h1b, if_pos h2b] at hsz ⊢
      obtain ⟨⟨sub, ol, fo⟩, hsub, hsubS⟩ := beatmap.slider_path.calculate_sub_path_refines (alloc.vec.Vec.deref sv) st sp.optimise_catmull h64
        (by rw [deref_val]; omega)
      rw [deref_val] at hsubS
      rw [← hsubS] at hsz ⊢
      rw [hsub, bind_ok]; simp only [uncurry_apply_pair]
      by_cases hp : path.val.length = 0
      · have hp' : ¬ alloc.vec.Vec.len path > 0#usize := by show ¬ (0#usize).val < (alloc.vec.Vec.len path).val; simp [hp]
        have hc : (decide ((vS path.val).size > 0) && decide ((vS sub.val).size > 0) && (vS path.val).back!.eq (vS sub.val)[0]!) = false := by
          simp [vS_size, hp]
        rw [hc] at hsz ⊢; rw [if_neg hp', bind_ok]
        exact sp_seg_tail path sub ol fo false hsz
      by_cases hs : sub.val.length = 0
      · have hp' : alloc.vec.Vec.len path > 0#usize := by show (0#usize).val < (alloc.vec.Vec.len path).val; simp; omega
        have hs' : ¬ alloc.vec.Vec.len sub > 0#usize := by show ¬ (0#usize).val < (alloc.vec.Vec.len sub).val; simp [hs]
        have hc : (decide ((vS path.val).size > 0) && decide ((vS sub.val).size > 0) && (vS path.val).back!.eq (vS sub.val)[0]!) = false := by
          simp [vS_size, hs]
        rw [hc] at hsz ⊢; rw [if_pos hp', if_neg hs', bind_ok]
        exact sp_seg_tail path sub ol fo false hsz
      have hp' : alloc.vec.Vec.len path > 0#usize := by show (0#usize).val < (alloc.vec.Vec.len path).val; simp; omega
      have hs' : alloc.vec.Vec.len sub > 0#usize := by show (0#usize).val < (alloc.vec.Vec.len sub).val; simp; omega
      obtain ⟨i6, hi6, hi6v⟩ := usize_sub_one (alloc.vec.Vec.len path) (by simp; omega)
      simp at hi6v
      have hc : (decide ((vS path.val).size > 0) && decide ((vS sub.val).size > 0) && (vS path.val).back!.eq (vS sub.val)[0]!) =
          Vec2.eq (bv2S (path.val[i6.val]'(by omega))) (bv2S (sub.val[(0#usize).val]'(by simp; omega))) := by
        have hb : (vS path.val).back! = bv2S (path.val[i6.val]'(by omega)) := by
          rw [Array.back!, vS_size, ← vS_get! _ _ (by omega)]; congr 1; omega
        simp only [vS_size, hb, vS_get! _ _ (show 0 < sub.val.length by omega)]
        simp [show 0 < path.val.length by omega, show 0 < sub.val.length by omega]
      rw [hc] at hsz ⊢
      rw [if_pos hp', if_pos hs', hi6, bind_ok, vec_index_eq' path i6 (by omega), bind_ok, vec_index_eq' sub 0#usize (by simp; omega),
        bind_ok, beatmap.vector2.eq_refines, bind_ok]
      exact sp_seg_tail path sub ol fo _ hsz

theorem sp_pcps_type (l : List beatmap.types.PathControlPoint) (j : Nat) (h : j < l.length) :
    (pcpsS l)[j]!.type = (l[j]'h).ptype.map ptS := by
  simp [pcpsS, pcpS, h]

theorem sp_cp_yield (cps : Array PathControlPoint) (oc : Bool) (i : Nat) (s : Array Vec2 × F64 × Bool × Nat) :
    ∃ c, (spCpBody cps oc i s : ForInStep _) = .yield c := by
  unfold spCpBody; split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem sp_seg_mono (cps : Array PathControlPoint) (oc : Bool) (start i : Nat) (path : Array Vec2) :
    path.size ≤ (spSeg cps oc start i path).1.size := by
  unfold spSeg; simp only []
  split
  · simp
  · split
    · rw [sp_iterIdx_push_size]; omega
    · exact le_refl _

theorem sp_cp_mono (cps : Array PathControlPoint) (oc : Bool) :
    ∀ m a (c : Array Vec2 × F64 × Bool × Nat), c.1.size ≤ (iterIdx (fun i s => (spCpBody cps oc i s : Id _)) a m c).1.size := by
  intro m
  induction m with
  | zero => intro a c; exact le_refl _
  | succ m ih =>
    intro a c
    rw [iterIdx_succ]
    obtain ⟨c', hc', hle⟩ : ∃ c', spCpBody cps oc a c = .yield c' ∧ c.1.size ≤ c'.1.size := by
      unfold spCpBody; split
      · exact ⟨_, rfl, le_refl _⟩
      · exact ⟨_, rfl, sp_seg_mono cps oc c.2.2.2 a c.1⟩
    simp only [hc']
    exact le_trans hle (ih _ _)

def spOptAdd (ol : F64) (o : Option F64) : F64 := match o with | none => ol | some x => ol + x

theorem beatmap.slider_path.calculate_path_refines (sp : beatmap.slider_path.SliderPathSpec)
    (h64 : System.Platform.numBits = 64) (hn : sp.control_points.val.length < 2^32)
    (hsz : (SliderPath.calculatePath (spsS sp)).1.size ≤ Usize.max) :
    ∃ r, beatmap.slider_path.calculate_path sp = ok r ∧ (vS r.1.val, r.2) = SliderPath.calculatePath (spsS sp) := by
  rw [sp_calculatePath_eq] at hsz ⊢
  have hC : (spsS sp).controlPoints = pcpsS sp.control_points.val := rfl
  have hO : (spsS sp).optimiseCatmull = sp.optimise_catmull := rfl
  rw [hC, hO] at hsz ⊢
  have hCs : (pcpsS sp.control_points.val).size = sp.control_points.val.length := by simp [pcpsS]
  rw [hCs] at hsz ⊢
  unfold beatmap.slider_path.calculate_path
  rw [bmc_beatmap_slider_path_D0, bind_ok]
  by_cases h0 : sp.control_points.val.length = 0
  · have h0' : alloc.vec.Vec.len sp.control_points = 0#usize := by apply UScalar.eq_of_val_eq; simpa using h0
    rw [if_pos h0', if_pos h0]; exact ⟨_, rfl, rfl⟩
  have h0' : ¬ alloc.vec.Vec.len sp.control_points = 0#usize := fun e => h0 (by simpa using congrArg UScalar.val e)
  rw [if_neg h0', if_neg h0] at *
  simp only [] at hsz ⊢
  set n := sp.control_points.val.length with hn_def
  set C := pcpsS sp.control_points.val
  set f := (fun i s => (spCpBody C sp.optimise_catmull i s : Id _)) with hf
  obtain ⟨i0, hi0, hi0a, hi0b⟩ := beatmap.slider_path.next_segment_end_refines sp 0#usize
  rw [hi0, bind_ok]
  obtain ⟨hi0le, hi0lt, hi0skip, hi0end⟩ := hi0b (by simp; omega)
  have hskip : ∀ (a b : Nat) (c : Array Vec2 × F64 × Bool × Nat), (∀ j (hj : j < n), a ≤ j → j < b → (sp.control_points.val[j]'hj).ptype = none) →
      b ≤ n - 1 → iterIdx f a (b - a) c = c := by
    intro a b c hj hb
    apply sp_iterIdx_skip
    intro j h1 h2
    have hjn : j < n := by omega
    simp only [hf, spCpBody]
    rw [if_pos (by rw [sp_pcps_type _ _ hjn, hj j hjn h1 (by omega)]; simp; omega)]
  have hpre : iterIdx f 0 n (#[], 0, false, 0) = iterIdx f i0.val (n - i0.val) (#[], 0, false, 0) := by
    have := sp_iterIdx_add f (fun i b => sp_cp_yield C sp.optimise_catmull i b) i0.val (n - i0.val) 0 (#[], 0, false, 0)
    rw [show i0.val + (n - i0.val) = n by omega, Nat.zero_add] at this
    rw [this, show i0.val = i0.val - 0 from rfl, hskip 0 i0.val _ (fun j hj _ h2 => hi0skip j hj (by simp) h2)
      (by omega)]
  rw [hpre] at hsz ⊢
  unfold beatmap.slider_path.calculate_path_loop
  have hmain := sp_loop_iterIdx_multi
    (fun (x : alloc.vec.Vec net.osutk.Vector2 × F64 × Bool × Usize × Usize) =>
      beatmap.slider_path.calculate_path_loop.body sp.control_points sp.expected_distance sp.optimise_catmull
        (alloc.vec.Vec.len sp.control_points) x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    f (fun i b => sp_cp_yield C sp.optimise_catmull i b) n
    (fun (x : alloc.vec.Vec net.osutk.Vector2 × F64 × Bool × Usize × Usize) k (b : Array Vec2 × F64 × Bool × Nat) =>
      x.2.2.2.2.val = k ∧ vS x.1.val = b.1 ∧ x.2.1 = b.2.1 ∧ x.2.2.1 = b.2.2.1 ∧ x.2.2.2.1.val = b.2.2.2 ∧
      x.2.2.2.1.val ≤ k ∧ k ≤ n ∧
      (∀ hk : k < n, (sp.control_points.val[k]'hk).ptype ≠ none ∨ k = n - 1) ∧
      (iterIdx f k (n - k) b).1.size ≤ Usize.max)
    (fun (y : alloc.vec.Vec net.osutk.Vector2 × F64 × Bool) (c : Array Vec2 × F64 × Bool × Nat) =>
      (vS y.1.val, y.2.1, y.2.2) = (c.1, c.2.1, c.2.2.1))
    ?hstep ?hend (alloc.vec.Vec.new _, 0, false, 0#usize, i0) i0.val (#[], 0, false, 0)
    ⟨rfl, by simp [vS], rfl, rfl, rfl, by simp, by omega, fun hk => hi0end, hsz⟩ (by omega)
  case hend =>
    rintro ⟨pa, ol, fo, st, i⟩ k b ⟨hk, h1, h2, h2f, h3, h4, h5, h6, h7⟩ hkn
    dsimp only at hk h1 h2 h2f h3 h4 h5 h6 h7
    have hlt : ¬ i < alloc.vec.Vec.len sp.control_points := by show ¬ i.val < (alloc.vec.Vec.len sp.control_points).val; simp; omega
    exact ⟨(pa, ol, fo), by simp only [beatmap.slider_path.calculate_path_loop.body, hlt, ite_false], by rw [h1, h2, h2f]⟩
  case hstep =>
    rintro ⟨pa, ol, fo, st, i⟩ k ⟨b1, b2, bf, b3⟩ ⟨hk, h1, h2, h2f, h3, h4, h5, h6, h7⟩ hkn
    dsimp only at hk h1 h2 h2f h3 h4 h5 h6 h7 ⊢
    subst hk h1 h2 h2f h3
    have hin : i.val < n := hkn
    have hlt : i < alloc.vec.Vec.len sp.control_points := by show i.val < (alloc.vec.Vec.len sp.control_points).val; simp; omega
    have hend := h6 hin
    have hfi : f i.val (vS pa.val, ol, fo, st.val) = .yield ((spSeg C sp.optimise_catmull st.val i.val (vS pa.val)).1,
        (match (spSeg C sp.optimise_catmull st.val i.val (vS pa.val)).2.1 with | none => ol | some x => ol + x),
        fo || (spSeg C sp.optimise_catmull st.val i.val (vS pa.val)).2.2, i.val) := by
      simp only [hf, spCpBody]
      rw [if_neg (by rw [sp_pcps_type _ _ hin]; rcases hend with h | h
                     · cases hp : (sp.control_points.val[i.val]'hin).ptype
                       · exact absurd hp h
                       · simp
                     · simp; omega)]
    have h7' := h7
    rw [show n - i.val = (n - i.val - 1) + 1 by omega, iterIdx_succ, hfi] at h7'
    have hszseg := le_trans (sp_cp_mono C sp.optimise_catmull (n - i.val - 1) (i.val + 1) _) h7'
    obtain ⟨⟨p2, olo, fo2⟩, hseg, hsegv⟩ := beatmap.slider_path.calculate_path_segment_refines sp st i pa h64 h4 hin hn hszseg
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by scalar_tac)
    obtain ⟨i2, hi2, hi2a, hi2b⟩ := beatmap.slider_path.next_segment_end_refines sp i1
    have hi2le : i.val + 1 ≤ i2.val := by
      by_cases hc : i1.val < n
      · have hh := (hi2b hc).1; omega
      · have := congrArg UScalar.val (hi2a (by omega)); omega
    have hi2n : i2.val ≤ n := by
      by_cases hc : i1.val < n
      · obtain ⟨_, hr2, _⟩ := hi2b hc; omega
      · have := congrArg UScalar.val (hi2a (by omega)); omega
    have hseq : iterIdx f i.val (i2.val - i.val) (vS pa.val, ol, fo, st.val) =
        ((spSeg C sp.optimise_catmull st.val i.val (vS pa.val)).1,
          (match (spSeg C sp.optimise_catmull st.val i.val (vS pa.val)).2.1 with | none => ol | some x => ol + x),
          fo || (spSeg C sp.optimise_catmull st.val i.val (vS pa.val)).2.2, i.val) := by
      rw [show i2.val - i.val = (i2.val - (i.val + 1)) + 1 by omega, iterIdx_succ, hfi]
      dsimp only
      by_cases hc : i1.val < n
      · obtain ⟨_, hr, hsk, _⟩ := hi2b hc
        apply hskip
        · intro j hj h1 h2; exact hsk j hj (by omega) h2
        · omega
      · rw [show i2.val - (i.val + 1) = 0 by have := congrArg UScalar.val (hi2a (by omega)); omega]; rfl
    refine ⟨i2.val - i.val, by omega, by omega, (p2, spOptAdd ol olo, fo || fo2, i, i2), ?_, ?_⟩
    · simp only [beatmap.slider_path.calculate_path_loop.body, hlt, ite_true]
      have hseg' : beatmap.slider_path.calculate_path_segment { control_points := sp.control_points, expected_distance := sp.expected_distance, optimise_catmull := sp.optimise_catmull } st i pa = ok (p2, olo, fo2) := hseg
      have hi2' : beatmap.slider_path.next_segment_end { control_points := sp.control_points, expected_distance := sp.expected_distance, optimise_catmull := sp.optimise_catmull } i1 = ok i2 := hi2
      rw [hseg', bind_ok]; simp only [uncurry_apply_pair]
      cases olo <;> cases fo <;> simp [float.F64.add, hi1, hi2', spOptAdd]
    · rw [hseq]
      dsimp only
      simp only [show i.val + (i2.val - i.val) = i2.val by omega]
      refine ⟨trivial, by rw [← hsegv], by rw [← hsegv]; rfl, by rw [← hsegv], trivial, by omega, by omega, ?_, ?_⟩
      · intro hk
        have hc : i1.val < n := by omega
        obtain ⟨_, _, _, h⟩ := hi2b hc
        exact h
      · have := sp_iterIdx_add f (fun i b => sp_cp_yield C sp.optimise_catmull i b) (i2.val - i.val) (n - i2.val) i.val (vS pa.val, ol, fo, st.val)
        rw [show i2.val - i.val + (n - i2.val) = n - i.val by omega, show i.val + (i2.val - i.val) = i2.val by omega, hseq] at this
        rw [← this]; exact h7
  obtain ⟨y, hy, hyF⟩ := hmain
  exact ⟨y, hy, hyF⟩

theorem beatmap.slider_path.compute_refines (sp : beatmap.slider_path.SliderPathSpec)
    (h64 : System.Platform.numBits = 64) (hn : sp.control_points.val.length < 2^32)
    (hsz : (SliderPath.calculatePath (spsS sp)).1.size < 2^62) :
    ∃ r, beatmap.slider_path.compute sp = ok r ∧ spS r = SliderPath.compute (spsS sp) := by
  obtain ⟨⟨p, ol, fo⟩, hp, hpv⟩ := beatmap.slider_path.calculate_path_refines sp h64 hn (le_of_lt (sp_len_lt _ h64 hsz))
  have hpl : p.val.length < 2^62 := by
    have := congrArg (fun x => x.1.size) hpv; simp only [vS_size] at this; omega
  obtain ⟨r, hr, hrv⟩ := beatmap.slider_path.calculate_length_refines sp p ol hpl h64
  refine ⟨{ r with fuel_out := fo }, ?_, ?_⟩
  · unfold beatmap.slider_path.compute; rw [hp, bind_ok]; simp only [uncurry_apply_pair]; rw [hr, bind_ok]
  · unfold SliderPath.compute; rw [← hpv]
    show spS { r with fuel_out := fo } = { SliderPath.calculateLength (spsS sp) (vS p.val) ol with fuelOut := fo }
    rw [← hrv]; rfl

theorem beatmap.slider_path.of_control_points_refines (cps : alloc.vec.Vec beatmap.types.PathControlPoint)
    (expected : Option F64) (oc : Bool) (h64 : System.Platform.numBits = 64) (hn : cps.val.length < 2^32)
    (hsz : (SliderPath.calculatePath { controlPoints := pcpsS cps.val, expectedDistance := expected, optimiseCatmull := oc }).1.size < 2^62) :
    ∃ r, beatmap.slider_path.of_control_points cps expected oc = ok r ∧
      spS r = SliderPath.ofControlPoints (pcpsS cps.val) expected oc := by
  unfold beatmap.slider_path.of_control_points SliderPath.ofControlPoints
  exact beatmap.slider_path.compute_refines { control_points := cps, expected_distance := expected, optimise_catmull := oc } h64 hn hsz

end OsuProofs
