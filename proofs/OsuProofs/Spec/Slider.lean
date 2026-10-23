/-
Spec-side normal form of the length loop of `SliderPath.calculateLength` (no Aeneas import).
-/
import OsuModel.Beatmap.SliderPath
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs.SpecSlider

/-- One iteration of the spec loop, with the accumulator as a list. -/
def cumStep (P : Array Vec2) (r : F64 × List F64) (i : Nat) : F64 × List F64 :=
  let c := r.1 + F32.toF64 (P[i + 1]! - P[i]!).length
  (c, r.2 ++ [c])

/-- The spec, without `ExpectedDistance`, is a left fold of `cumStep`. -/
theorem calculateLength_none (sp : SliderPathSpec) (h : sp.expectedDistance = none)
    (P : Array Vec2) (opt : F64) :
    (SliderPath.calculateLength sp P opt).cumulativeLength.toList =
        ((List.range' 0 (P.size - 1)).foldl (cumStep P) (opt, [0])).2 ∧
    (SliderPath.calculateLength sp P opt).calculatedLength =
        ((List.range' 0 (P.size - 1)).foldl (cumStep P) (opt, [0])).1 := by
  have hom := List.foldl_hom (l := List.range' 0 (P.size - 1)) (init := (opt, [0]))
    (fun (r : F64 × List F64) => ((r.1, r.2.toArray) : F64 × Array F64))
    (g₁ := cumStep P)
    (g₂ := fun (r : F64 × Array F64) (i : Nat) =>
      ((r.1 + F32.toF64 (P[i + 1]! - P[i]!).length,
        r.2.push (r.1 + F32.toF64 (P[i + 1]! - P[i]!).length)) : F64 × Array F64))
    (by intro x y; simp [cumStep])
  unfold SliderPath.calculateLength
  simp only [h, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl] at *
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] at *
  simp only [pure, bind]
  rw [show (#[0] : Array F64) = [0].toArray from rfl, hom]
  simp

end OsuProofs.SpecSlider
