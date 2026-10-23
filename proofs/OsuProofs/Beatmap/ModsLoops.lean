/-
Loop functions of `beatmap::mods` (Rust) refining `OsuModel.Beatmap.Mods`, via the lockstep
lemmas of `LoopsR` (`loop_whileR` for `while`, `loop_iterR` for `for j in [lo:hi]`).
-/
import OsuProofs.LoopsR
import OsuProofs.Prims
import OsuProofs.Repr
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

theorem lmax_loop0 (xs : Slice F64) (F : Unit → Nat × F64 → Id (ForInStep (Nat × F64)))
    (hF : ∀ s, F () s = if (s.2.isNaN && decide (s.1 + 1 < xs.val.length)) = true then
        pure (ForInStep.yield (s.1 + 1, xs.val.toArray[s.1 + 1]!)) else pure (ForInStep.done (s.1, s.2)))
    (i : Usize) (v : F64) (hi : i.val < xs.val.length) :
    ∃ y, beatmap.mods.linq_max_f64_loop0 xs i v = ok y ∧
      (y.1.val, y.2) = forIn (m := Id) Lean.Loop.mk (i.val, v) F ∧ y.1.val < xs.val.length := by
  have := loop_whileR (fun (x : Usize × F64) => beatmap.mods.linq_max_f64_loop0.body xs x.1 x.2) F
    (fun s => xs.val.length - s.1) (fun t s => t.1.val = s.1 ∧ t.2 = s.2 ∧ s.1 < xs.val.length)
    (fun y s => y.1.val = s.1 ∧ y.2 = s.2 ∧ s.1 < xs.val.length)
    (by
      rintro ⟨ti, tv⟩ ⟨si, sv⟩ ⟨h1, h2, h3⟩
      simp only at h1 h2 h3 ⊢
      subst h1 h2
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one ti (by have := xs.property; omega)
      constructor
      · intro s' hs'
        rw [hF] at hs'
        by_cases hc : (tv.isNaN && decide (ti.val + 1 < xs.val.length)) = true
        · rw [if_pos hc] at hs'; cases hs'
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          refine ⟨by omega, (i1, xs.val[ti.val + 1]), ?_, by simp [hi1v], ?_, by simp [hi1v]; omega⟩
          · have hl : i1 < Slice.len xs := by show i1.val < (Slice.len xs).val; simp [hi1v]; omega
            simp [beatmap.mods.linq_max_f64_loop0.body, float.F64.is_nan, hc.1, hc.2, hi1, hl,
              index_eq xs i1 (by omega), hi1v]
          · simp only; rw [getElem!_pos _ _ (by simpa using hc.2)]; simp
        · rw [if_neg hc] at hs'; cases hs'
      · intro s' hs'
        rw [hF] at hs'
        by_cases hc : (tv.isNaN && decide (ti.val + 1 < xs.val.length)) = true
        · rw [if_pos hc] at hs'; cases hs'
        · rw [if_neg hc] at hs'; cases hs'
          refine ⟨(ti, tv), Or.inl ?_, rfl, rfl, h3⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hc
          by_cases hn : tv.isNaN = true
          · have hl : ¬ i1 < Slice.len xs := by
              show ¬ i1.val < (Slice.len xs).val; simp [hi1v]; have := hc hn; omega
            simp [beatmap.mods.linq_max_f64_loop0.body, float.F64.is_nan, hn, hi1, hl, hi1v, hc hn]
          · simp [beatmap.mods.linq_max_f64_loop0.body, float.F64.is_nan, hn])
    (i, v) (i.val, v) ⟨rfl, rfl, hi⟩
  obtain ⟨y, hl, h1, h2, h3⟩ := this
  refine ⟨y, by unfold beatmap.mods.linq_max_f64_loop0; exact hl, ?_, by omega⟩
  exact Prod.ext h1 h2

theorem lmax_loop1 (xs : Slice F64) (G : Nat → F64 → Id (ForInStep F64))
    (hG : ∀ j s, G j s = if s < xs.val.toArray[j]! then pure (ForInStep.yield xs.val.toArray[j]!) else pure (ForInStep.yield s))
    (j : Usize) (v : F64) (hj : j.val ≤ xs.val.length) :
    beatmap.mods.linq_max_f64_loop1 xs v j = ok (iterR G j.val (xs.val.length - j.val) v) := by
  have := loop_iterR (fun (x : F64 × Usize) => beatmap.mods.linq_max_f64_loop1.body xs x.1 x.2) G xs.val.length
    (fun x => x.2.val) (fun t s => t.1 = s ∧ t.2.val ≤ xs.val.length) (fun y s => y = s)
    (by
      rintro ⟨tv, tj⟩ s ⟨h1, h2⟩ hk
      simp only at h1 h2 hk ⊢
      subst h1
      obtain ⟨j1, hj1, hj1v⟩ := usize_add_one tj (by have := xs.property; omega)
      have hl : tj < Slice.len xs := by show tj.val < (Slice.len xs).val; simpa using hk
      have hg : xs.val.toArray[tj.val]! = xs.val[tj.val] := by
        rw [getElem!_pos _ _ (by simpa using hk)]; simp only [List.getElem_toArray]; rfl
      constructor
      · intro s' hs'
        rw [hG, hg] at hs'
        refine ⟨(s', j1), ?_, hj1v, rfl, by simp only [hj1v]; omega⟩
        by_cases hc : tv < xs.val[tj.val]
        · rw [if_pos hc] at hs'; cases hs'
          simp [beatmap.mods.linq_max_f64_loop1.body, hl, index_eq xs tj hk, float.F64.lt, hc, hj1]
          split <;> simp_all
        · rw [if_neg hc] at hs'; cases hs'
          simp [beatmap.mods.linq_max_f64_loop1.body, hl, index_eq xs tj hk, float.F64.lt, hc, hj1]
          intro h'; exact absurd h' hc
      · intro s' hs'
        rw [hG] at hs'; split at hs' <;> cases hs')
    (by
      rintro ⟨tv, tj⟩ s ⟨h1, h2⟩ hk
      simp only at h1 h2 hk ⊢
      subst h1
      have hl : ¬ tj < Slice.len xs := by show ¬ tj.val < (Slice.len xs).val; simp; omega
      exact ⟨tv, by simp [beatmap.mods.linq_max_f64_loop1.body, hl], rfl⟩)
    (v, j) v ⟨rfl, hj⟩ hj
  obtain ⟨y, hl, hq⟩ := this
  simp only at hq; subst hq
  unfold beatmap.mods.linq_max_f64_loop1; exact hl

/-- `xs.Max()` (Rust indexes `xs[0]`, so `xs` must be non-empty; LINQ throws on empty input). -/
theorem beatmap.mods.linq_max_f64_refines (xs : Slice F64) (h : 0 < xs.val.length) :
    beatmap.mods.linq_max_f64 xs = ok (Mods.linqMaxF64 xs.val.toArray) := by
  unfold Mods.linqMaxF64
  simp only [Id.run]
  obtain ⟨y, hy, hy1, hy2⟩ := lmax_loop0 xs (fun _ (s : Nat × F64) =>
      if (s.2.isNaN && decide (s.1 + 1 < xs.val.toArray.size)) = true then
        pure (ForInStep.yield (s.1 + 1, xs.val.toArray[s.1 + 1]!)) else pure (ForInStep.done (s.1, s.2)))
    (fun s => rfl) 0#usize xs.val[0] (by simpa using h)
  have h0 : xs.val.toArray[0]! = xs.val[0] := by rw [getElem!_pos _ _ (by simpa using h)]; simp
  have hy1' : (y.1.val, y.2) = forIn (m := Id) Lean.Loop.mk (0, xs.val[0]) (fun _ (s : Nat × F64) =>
      if (s.2.isNaN && decide (s.1 + 1 < xs.val.toArray.size)) = true then
        pure (ForInStep.yield (s.1 + 1, xs.val.toArray[s.1 + 1]!)) else pure (ForInStep.done (s.1, s.2))) := by
    simpa using hy1
  rw [h0, ← hy1']
  obtain ⟨yi, yv⟩ := y
  simp only at hy hy2 ⊢
  obtain ⟨j1, hj1, hj1v⟩ := usize_add_one yi (by have := xs.property; omega)
  have h2 := lmax_loop1 xs (fun j (s : F64) =>
      if s < xs.val.toArray[j]! then pure (ForInStep.yield xs.val.toArray[j]!) else pure (ForInStep.yield s))
    (fun j s => rfl) j1 yv (by omega)
  simp only [beatmap.mods.linq_max_f64, index_eq xs 0#usize (by simpa using h), bind_ok]
  rw [show xs.val[(0#usize : Usize).val] = xs.val[0] from rfl, hy]
  simp [hj1, h2, hj1v]
  rw [← forIn_range'_iterR]; rfl

end OsuProofs
