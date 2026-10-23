/-
(ii) A loop over a slice building a `Vec`: `slider::cumulative_lengths` refines the length loop of
`OsuModel.Beatmap.SliderPath.calculateLength` (the result when `ExpectedDistance` is absent).
-/
import OsuProofs.Prims
import OsuModel.Beatmap.SliderPath
import OsuProofs.Spec.Slider
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl OsuProofs.SpecSlider

/-- Representation map: impl `Vec2` ↦ spec `Vec2` (same two `F32` fields). -/
def vSpec (v : slider.Vec2) : Vec2 := ⟨v.x, v.y⟩

theorem K0_slider_eq : slider.K0 = ok (0 : F64) := by
  unfold slider.K0; exact from_bits_lit _ _ (by decide +kernel)

theorem slider.vsub_refines (a b : slider.Vec2) : slider.vsub a b = ok ⟨a.x - b.x, a.y - b.y⟩ := by
  simp [slider.vsub, float.F32.sub]

theorem slider.length_refines (a : slider.Vec2) : slider.length a = ok (Vec2.length (vSpec a)) := by
  simp [slider.length, Vec2.length, vSpec, float.F32.mul, float.F32.add, float.F32.to_f64,
    float.F64.sqrt, float.F64.to_f32]

theorem getElem!_spec (path : Slice slider.Vec2) (i : Nat) (h : i < path.val.length) :
    ((path.val.map vSpec).toArray)[i]! = vSpec (path.val[i]'h) := by
  simp [h]

/-- One-step unfolding of the Aeneas loop, keeping the recursive call folded. -/
theorem cum_loop_unfold (path : Slice slider.Vec2) (c : F64) (cum : alloc.vec.Vec F64) (i : Usize) :
    slider.cumulative_lengths_loop path c cum i =
      (do
        let r ← slider.cumulative_lengths_loop.body path c cum i
        match r with
        | .cont x => slider.cumulative_lengths_loop path x.1 x.2.1 x.2.2
        | .done y => ok y) := by
  unfold slider.cumulative_lengths_loop; rw [loop]
  simp only []
  congr 1; funext x; cases x <;> rfl

/-- Loop invariant: the Aeneas loop from index `i` is the fold over the remaining indices. -/
theorem loop_refines (path : Slice slider.Vec2) :
    ∀ (k : Nat) (i : Usize) (c : F64) (cum : alloc.vec.Vec F64),
      path.val.length - (i.val + 1) = k → (i.val < path.val.length ∨ i.val = 0) → cum.val.length = i.val + 1 →
      ∃ v, slider.cumulative_lengths_loop path c cum i =
          ok (v, ((List.range' i.val (path.val.length - 1 - i.val)).foldl
                    (cumStep (path.val.map vSpec).toArray) (c, cum.val)).1) ∧
        v.val = ((List.range' i.val (path.val.length - 1 - i.val)).foldl
                    (cumStep (path.val.map vSpec).toArray) (c, cum.val)).2 := by
  intro k
  induction k with
  | zero =>
    intro i c cum hk hi hcum
    have hn := Slice.length_ineq path
    have hn1 : 1 ≤ Usize.max := by have := Usize.bounds_eq; simp [U32.max_eq, U64.max_eq] at this; omega
    have hb : i.val + 1 ≤ Usize.max := by omega
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i hb
    have hrange : path.val.length - 1 - i.val = 0 := by omega
    unfold slider.cumulative_lengths_loop
    rw [loop]
    simp only [slider.cumulative_lengths_loop.body, hi1, bind_tc_ok, bind_ok]
    have hnlt : ¬ (i1 < Slice.len path) := by
      intro hlt
      have : i1.val < (Slice.len path).val := hlt
      simp only [Slice.len_val, Slice.length] at this; omega
    simp only [hnlt, if_false, bind_tc_ok, bind_ok, hrange, List.range'_zero, List.foldl_nil]
    exact ⟨cum, rfl, rfl⟩
  | succ k ih =>
    intro i c cum hk hi hcum
    have hn := Slice.length_ineq path
    have hn1 : 1 ≤ Usize.max := by have := Usize.bounds_eq; simp [U32.max_eq, U64.max_eq] at this; omega
    have hilt : i.val + 1 < path.val.length := by omega
    have hb : i.val + 1 ≤ Usize.max := by omega
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i hb
    have hlt : i1 < Slice.len path := by
      show i1.val < (Slice.len path).val
      simp only [Slice.len_val, Slice.length]; omega
    have hi1l : i1.val < path.val.length := by omega
    have hil : i.val < path.val.length := by omega
    let c1 := c + F32.toF64 (Vec2.length (vSpec ⟨(path.val[i1.val]'hi1l).x - (path.val[i.val]'hil).x,
      (path.val[i1.val]'hi1l).y - (path.val[i.val]'hil).y⟩))
    have hpush : cum.val.length < Usize.max := by omega
    obtain ⟨cum1, hcum1, hcum1v⟩ := push_eq cum c1 hpush
    obtain ⟨v, hv, hvv⟩ := ih i1 c1 cum1 (by omega) (Or.inl hi1l) (by simp [hcum1v]; omega)
    have hrange : path.val.length - 1 - i.val = (path.val.length - 1 - i1.val) + 1 := by omega
    have hstep : cumStep (path.val.map vSpec).toArray (c, cum.val) i.val = (c1, cum1.val) := by
      simp only [cumStep, hcum1v, c1]
      rw [show i.val + 1 = i1.val from hi1v.symm, getElem!_spec path _ hi1l, getElem!_spec path _ hil]
      rfl
    refine ⟨v, ?_, ?_⟩
    · rw [cum_loop_unfold]
      simp only [slider.cumulative_lengths_loop.body, hi1, bind_tc_ok, bind_ok, hlt, if_true,
        index_eq path i1 hi1l, index_eq path i hil, slider.vsub_refines, slider.length_refines,
        float.F32.to_f64, float.F64.add]
      rw [hcum1]
      simp only [bind_ok]
      rw [hv, hrange, List.range'_succ, List.foldl_cons, hstep, hi1v]
    · rw [hvv, hrange, List.range'_succ, List.foldl_cons, hstep, hi1v]

theorem slider.cumulative_lengths_refines (sp : SliderPathSpec) (h : sp.expectedDistance = none)
    (path : Slice slider.Vec2) (opt : F64) :
    ∃ v, slider.cumulative_lengths path opt =
        ok (v, (SliderPath.calculateLength sp (path.val.map vSpec).toArray opt).calculatedLength) ∧
      v.val = (SliderPath.calculateLength sp (path.val.map vSpec).toArray opt).cumulativeLength.toList := by
  obtain ⟨hcum, hcalc⟩ := calculateLength_none sp h (path.val.map vSpec).toArray opt
  obtain ⟨cum0, hcum0, hcum0v⟩ := push_eq (alloc.vec.Vec.new F64) (0 : F64) (by simp; have := Usize.bounds_eq; simp [U32.max_eq, U64.max_eq] at this; omega)
  obtain ⟨v, hv, hvv⟩ := loop_refines path (path.val.length - 1) 0#usize opt cum0 (by simp)
    (Or.inr (by simp)) (by simp [hcum0v])
  refine ⟨v, ?_, ?_⟩
  · simp only [slider.cumulative_lengths, K0_slider_eq, bind_tc_ok, bind_ok, hcum0, hv, hcalc,
      hcum0v]
    simp
  · rw [hvv, hcum, hcum0v]; simp
end OsuProofs
