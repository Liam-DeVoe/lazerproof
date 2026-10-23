/-
`beatmap::dotnet` (Rust) refines `OsuModel.Beatmap` .NET helpers: ordinal string equality
`str_eq2`, `List<double>.BinarySearch` (`binarySearchF64`, lockstep `loop_iterR`); sorts follow.
-/
import OsuProofs.LoopsR
import OsuProofs.Prims
import OsuProofs.Net.Parse
import OsuProofs.Beatmap.DotNet
import OsuProofs.Beatmap.ControlPoints
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

theorem dns_str_eq2_loop (a b : Slice U32) (hl : a.val.length = b.val.length) :
    ∀ (i : Usize) (o : Bool), i.val ≤ a.val.length →
      beatmap.dotnet.str_eq2_loop a b i o = ok (o && decide (a.val.drop i.val = b.val.drop i.val)) := by
  intro i
  induction hk : a.val.length - i.val using Nat.strong_induction_on generalizing i with
  | _ k ih =>
    intro o hle
    unfold beatmap.dotnet.str_eq2_loop
    rw [loop_unfold]
    by_cases hlt : i.val < a.val.length
    · have hl' : i < Slice.len a := by show i.val < (Slice.len a).val; simpa using hlt
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := a.property; omega)
      have hb : i.val < b.val.length := by omega
      have e := ih (a.val.length - i1.val) (by omega) i1 rfl
      unfold beatmap.dotnet.str_eq2_loop at e
      have hbody : beatmap.dotnet.str_eq2_loop.body a b i o =
          ok (.cont (i1, o && decide (a.val[i.val] = b.val[i.val]))) := by
        by_cases hc : a.val[i.val] = b.val[i.val]
        · simp [beatmap.dotnet.str_eq2_loop.body, hl', index_eq a i hlt, index_eq b i hb, hi1, hc]
          intro _; exact congrArg UScalar.val hc
        · simp [beatmap.dotnet.str_eq2_loop.body, hl', index_eq a i hlt, index_eq b i hb, hi1, hc]
          intro h; exfalso; exact hc (UScalar.eq_of_val_eq h)
      simp only [hbody, bind_ok]
      have key : (a.val.drop i.val = b.val.drop i.val) ↔
          (a.val[i.val] = b.val[i.val] ∧ a.val.drop (i.val + 1) = b.val.drop (i.val + 1)) := by
        rw [List.drop_eq_getElem_cons hlt, List.drop_eq_getElem_cons hb, List.cons.injEq]; exact Iff.rfl
      rw [e _ (by omega), hi1v]
      cases o <;> by_cases hc : a.val[i.val] = b.val[i.val] <;> simp [hc, key]
    · have hl' : ¬ i < Slice.len a := by show ¬ i.val < (Slice.len a).val; simpa using hlt
      simp only [beatmap.dotnet.str_eq2_loop.body, hl', if_false, bind_ok]
      simp [List.drop_eq_nil_of_le (show a.val.length ≤ i.val by omega),
        List.drop_eq_nil_of_le (show b.val.length ≤ i.val by omega)]

/-- Ordinal string equality (no spec def: the spec compares `String`s with `==`). -/
theorem beatmap.dotnet.str_eq2_refines (a b : Slice U32) :
    beatmap.dotnet.str_eq2 a b = ok (decide (a.val = b.val)) := by
  unfold beatmap.dotnet.str_eq2
  dsimp only
  by_cases hl : a.val.length = b.val.length
  · have hl' : (Slice.len a != Slice.len b) = false := by
      rw [bne_eq_false_iff_eq]; apply UScalar.eq_of_val_eq; simp [hl]
    rw [hl']; simp only [Bool.false_eq_true, if_false]
    rw [dns_str_eq2_loop a b hl 0#usize true (by simp)]; simp
  · have hl' : (Slice.len a != Slice.len b) = true := by
      rw [bne_iff_ne, ne_eq]; intro h; apply hl; have := congrArg UScalar.val h; simpa using this
    rw [hl']; simp only [if_true]
    congr 1; symm; simp only [decide_eq_false_iff_not]
    intro h; apply hl; rw [h]

theorem dns_i64_sub (x y : I64) (h1 : -9223372036854775808 ≤ x.val - y.val) (h2 : x.val - y.val ≤ 9223372036854775807) :
    ∃ z, x - y = ok z ∧ z.val = x.val - y.val := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (IScalar.sub_spec (x := x) (y := y)
    (by simp [IScalar.min, I64.min_eq] at *; omega) (by simp [IScalar.max, I64.max_eq] at *; omega))
  exact ⟨z, hz, by simpa using hv⟩

theorem dns_i64_add (x y : I64) (h1 : -9223372036854775808 ≤ x.val + y.val) (h2 : x.val + y.val ≤ 9223372036854775807) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (IScalar.add_spec (x := x) (y := y)
    (by simp [IScalar.min, I64.min_eq] at *; omega) (by simp [IScalar.max, I64.max_eq] at *; omega))
  exact ⟨z, hz, by simpa using hv⟩

theorem dns_i64_div2 (x : I64) (h : 0 ≤ x.val) : ∃ z, x / 2#i64 = ok z ∧ z.val = x.val / 2 := by
  obtain ⟨z, hz, hv⟩ := IScalar.div_spec (x := x) (y := 2#i64) (by simp) (by simp)
  refine ⟨z, hz, ?_⟩
  rw [hv]; have : (2#i64 : I64).val = 2 := by decide
  rw [this, Int.tdiv_eq_ediv_of_nonneg h]

/-- The spec loop body of `binarySearchF64` (state: (returned, lo, hi)). -/
def bsF (a : Array F64) (v : F64) (_ : Nat) (s : Option Int × Int × Int) : Id (ForInStep (Option Int × Int × Int)) :=
  if s.2.1 ≤ s.2.2 then
    if (compareF64 a[(s.2.1 + (s.2.2 - s.2.1) / 2).toNat]! v == 0) = true then
      pure (ForInStep.done (some (s.2.1 + (s.2.2 - s.2.1) / 2), s.2.1, s.2.2))
    else if compareF64 a[(s.2.1 + (s.2.2 - s.2.1) / 2).toNat]! v < 0 then
      pure (ForInStep.yield (none, s.2.1 + (s.2.2 - s.2.1) / 2 + 1, s.2.2))
    else pure (ForInStep.yield (none, s.2.1, s.2.1 + (s.2.2 - s.2.1) / 2 - 1))
  else pure (ForInStep.yield (none, s.2.1, s.2.2))

theorem dns_usize_max : 2^32 - 1 ≤ Usize.max := by
  have := Usize.bounds_eq; simp [U32.max_eq, U64.max_eq] at this; omega

theorem dns_bs_spec (a : Array F64) (v : F64) :
    binarySearchF64 a v = (match (iterR (bsF a v) 0 (a.size + 1) (none, 0, (a.size : Int) - 1)).1 with
      | some r => r | none => -(iterR (bsF a v) 0 (a.size + 1) (none, 0, (a.size : Int) - 1)).2.1 - 1) := by
  unfold binarySearchF64
  simp only [Id.run]
  rw [forIn_range_iterR, Nat.sub_zero]
  have e : (fun (x : Nat) (s : Option Int × Int × Int) =>
      if s.2.1 ≤ s.2.2 then
        if (compareF64 a[(s.2.1 + (s.2.2 - s.2.1) / 2).toNat]! v == 0) = true then
          (pure (ForInStep.done (some (s.2.1 + (s.2.2 - s.2.1) / 2), s.2.1, s.2.2)) : Id _)
        else if compareF64 a[(s.2.1 + (s.2.2 - s.2.1) / 2).toNat]! v < 0 then
          pure (ForInStep.yield (none, s.2.1 + (s.2.2 - s.2.1) / 2 + 1, s.2.2))
        else pure (ForInStep.yield (none, s.2.1, s.2.1 + (s.2.2 - s.2.1) / 2 - 1))
      else pure (ForInStep.yield (none, s.2.1, s.2.2))) = bsF a v := rfl
  rw [e]
  cases iterR (bsF a v) 0 (a.size + 1) (none, 0, (a.size : Int) - 1) with
  | mk o p => cases o <;> rfl

theorem dns_bs_loop (a : Slice F64) (v : F64) (hn : a.val.length < 2^31) :
    ∀ (lo hi : I64) (it : Usize), 0 ≤ lo.val → lo.val ≤ a.val.length → -1 ≤ hi.val → hi.val < a.val.length →
      it.val ≤ a.val.length + 1 →
      ∃ y, beatmap.dotnet.binary_search_f64_loop a v lo hi none it = ok y ∧
        y.1.val = (iterR (bsF a.val.toArray v) it.val (a.val.length + 1 - it.val) (none, lo.val, hi.val)).2.1 ∧
        y.2.map (·.val) = (iterR (bsF a.val.toArray v) it.val (a.val.length + 1 - it.val) (none, lo.val, hi.val)).1 ∧
        0 ≤ y.1.val ∧ y.1.val ≤ a.val.length := by
  intro lo hi it hlo hlo2 hhi hhi2 hit
  have := loop_iterR (fun (x : I64 × I64 × Option I64 × Usize) =>
      beatmap.dotnet.binary_search_f64_loop.body a v x.1 x.2.1 x.2.2.1 x.2.2.2)
    (bsF a.val.toArray v) (a.val.length + 1) (fun x => x.2.2.2.val)
    (fun t s => t.2.2.1 = none ∧ s = (none, t.1.val, t.2.1.val) ∧ 0 ≤ t.1.val ∧ t.1.val ≤ a.val.length ∧
      -1 ≤ t.2.1.val ∧ t.2.1.val < a.val.length ∧ t.2.2.2.val ≤ a.val.length + 1)
    (fun y s => y.1.val = s.2.1 ∧ y.2.map (·.val) = s.1 ∧ 0 ≤ y.1.val ∧ y.1.val ≤ a.val.length)
    (by
      rintro ⟨lo, hi, res, it⟩ s ⟨hr, hs, h1, h2, h3, h4, h5⟩ hk
      simp only at hr hs h1 h2 h3 h4 h5 hk ⊢
      subst hr hs
      have hU : a.val.length + 1 ≤ Usize.max := by have := dns_usize_max; omega
      obtain ⟨n1, hn1, hn1v⟩ := usize_add_one (Slice.len a) (by simpa using hU)
      obtain ⟨it1, hit1, hit1v⟩ := usize_add_one it (by omega)
      have hitl : it < n1 := by show it.val < n1.val; rw [hn1v]; simpa using hk
      by_cases hle : lo.val ≤ hi.val
      · have hle' : lo ≤ hi := by simpa using hle
        obtain ⟨d, hd, hdv⟩ := dns_i64_sub hi lo (by omega) (by omega)
        obtain ⟨q, hq, hqv⟩ := dns_i64_div2 d (by omega)
        have hq1 : 0 ≤ q.val := by rw [hqv]; omega
        have hq2 : q.val ≤ hi.val - lo.val := by rw [hqv, hdv]; omega
        obtain ⟨m, hm, hmv⟩ := dns_i64_add lo q (by omega) (by omega)
        obtain ⟨u, hu, huv⟩ := eq_ok_of_spec (IScalar.hcast_inBounds_spec .Usize m
          (by have h1 := dns_usize_max; rw [UScalar.max_USize_eq]; constructor <;> omega))
        have hul : u.val < a.val.length := by omega
        obtain ⟨c, hc, hcv⟩ := beatmap.dotnet.compare_f64_refines (a.val[u.val]'hul) v
        have hmid : lo.val + (hi.val - lo.val) / 2 = m.val := by omega
        have hget : a.val.toArray[m.val.toNat]! = a.val[u.val]'hul := by
          rw [getElem!_pos _ _ (by simp; omega)]; simp; congr 1; omega
        have hfs : bsF a.val.toArray v it.val (none, lo.val, hi.val) =
            (if (compareF64 (a.val[u.val]'hul) v == 0) = true then pure (ForInStep.done (some m.val, lo.val, hi.val))
             else if compareF64 (a.val[u.val]'hul) v < 0 then pure (ForInStep.yield (none, m.val + 1, hi.val))
             else pure (ForInStep.yield (none, lo.val, m.val - 1))) := by
          simp only [bsF, hle, if_true, hmid, hget]
        rw [hfs]
        have hblock : beatmap.dotnet.binary_search_f64_loop.body a v lo hi none it =
            (do
              let k ← (if c = 0#i32 then ok (lo, hi, some m)
                else do
                  let (i6, i7) ← if c < 0#i32 then do let lo2 ← m + 1#i64; ok (lo2, hi)
                    else do let hi2 ← m - 1#i64; ok (lo, hi2)
                  ok (i6, i7, (none : Option I64)))
              ok (ControlFlow.cont (k.1, k.2.1, k.2.2, it1))) := by
          simp only [beatmap.dotnet.binary_search_f64_loop.body, core.option.Option.is_none, Option.isNone_none,
            if_true, hn1, bind_ok, hitl, hle', hit1, hd, hq, hm, hu, index_eq a u hul, hc]
          rfl
        have hcz : ((compareF64 (a.val[u.val]'hul) v == 0) = true) ↔ c = 0#i32 := by
          rw [beq_iff_eq, ← hcv]; constructor
          · intro h; exact IScalar.eq_of_val_eq (by simpa using h)
          · intro h; rw [h]; rfl
        have hcn : (compareF64 (a.val[u.val]'hul) v < 0) ↔ c < 0#i32 := by
          rw [← hcv]; constructor <;> intro h <;> simpa using h
        have hone : (1#i64 : I64).val = 1 := by decide
        by_cases hc0 : c = 0#i32
        · have hs : ((compareF64 (a.val[u.val]'hul) v == 0) = true) := hcz.mpr hc0
          simp only [hs, if_true]
          constructor
          · intro s' h'; cases h'
          · intro s' h'
            cases h'
            refine ⟨(lo, some m), Or.inr ⟨(lo, hi, some m, it1), ?_, ?_⟩, rfl, rfl, h1, h2⟩
            · rw [hblock]; simp [hc0]
            · simp [beatmap.dotnet.binary_search_f64_loop.body, core.option.Option.is_none]
        · have hs : ¬ ((compareF64 (a.val[u.val]'hul) v == 0) = true) := fun h => hc0 (hcz.mp h)
          simp only [hs, if_false, Bool.false_eq_true]
          by_cases hlt : c < 0#i32
          · have hs2 : compareF64 (a.val[u.val]'hul) v < 0 := hcn.mpr hlt
            simp only [hs2, if_true]
            obtain ⟨l2, hl2, hl2v⟩ := dns_i64_add m 1#i64 (by rw [hone]; omega) (by rw [hone]; omega)
            constructor
            · intro s' h'; cases h'
              refine ⟨(l2, hi, none, it1), ?_, by simp [hit1v], rfl, ?_⟩
              · rw [hblock]; simp [hc0, hlt, hl2]
              · refine ⟨by rw [hl2v, hone], by rw [hl2v, hone]; omega, by rw [hl2v, hone]; omega, h3, h4, by dsimp only; omega⟩
            · intro s' h'; cases h'
          · have hs2 : ¬ compareF64 (a.val[u.val]'hul) v < 0 := fun h => hlt (hcn.mp h)
            simp only [hs2, if_false]
            obtain ⟨h2', hh2, hh2v⟩ := dns_i64_sub m 1#i64 (by rw [hone]; omega) (by rw [hone]; omega)
            constructor
            · intro s' h'; cases h'
              refine ⟨(lo, h2', none, it1), ?_, by simp [hit1v], rfl, ?_⟩
              · rw [hblock]; simp [hc0, hlt, hh2]
              · refine ⟨by rw [hh2v, hone], h1, h2, by rw [hh2v, hone]; omega, by rw [hh2v, hone]; omega, by dsimp only; omega⟩
            · intro s' h'; cases h'
      · have hle' : ¬ lo ≤ hi := by simpa using hle
        simp only [bsF, hle, if_false]
        constructor
        · intro s' h'; cases h'
          refine ⟨(lo, hi, none, it1), ?_, by simp [hit1v], rfl, rfl, h1, h2, h3, h4, by dsimp only; omega⟩
          have hitlv : it.val < n1.val := hitl
          simp [beatmap.dotnet.binary_search_f64_loop.body, core.option.Option.is_none, hn1, hitl, hitlv, hle', hit1]
        · intro s' h'; cases h')
    (by
      rintro ⟨lo, hi, res, it⟩ s ⟨hr, hs, h1, h2, h3, h4, h5⟩ hk
      simp only at hr hs h1 h2 h3 h4 h5 hk ⊢
      subst hr hs
      have hU : a.val.length + 1 ≤ Usize.max := by have := dns_usize_max; omega
      obtain ⟨n1, hn1, hn1v⟩ := usize_add_one (Slice.len a) (by simpa using hU)
      have hitl : ¬ it < n1 := by show ¬ it.val < n1.val; rw [hn1v]; simp; omega
      have hitlv : ¬ it.val < n1.val := hitl
      exact ⟨(lo, none), by simp [beatmap.dotnet.binary_search_f64_loop.body, core.option.Option.is_none, hn1, hitl, hitlv],
        rfl, rfl, h1, h2⟩)
    (lo, hi, none, it) (none, lo.val, hi.val) ⟨rfl, rfl, hlo, hlo2, hhi, hhi2, hit⟩ hit
  obtain ⟨y, hl, hq1, hq2, hq3, hq4⟩ := this
  exact ⟨y, by unfold beatmap.dotnet.binary_search_f64_loop; exact hl, hq1, hq2, hq3, hq4⟩

/-- `List<double>.BinarySearch` (the slice length bound keeps the `i64`/`usize` arithmetic in range). -/
theorem beatmap.dotnet.binary_search_f64_refines (a : Slice F64) (v : F64) (hn : a.val.length < 2^31) :
    ∃ r, beatmap.dotnet.binary_search_f64 a v = ok r ∧ r.val = binarySearchF64 a.val.toArray v := by
  obtain ⟨n, hnc, hnv⟩ := eq_ok_of_spec (UScalar.hcast_inBounds_spec .I64 (Slice.len a)
    (by simp [IScalar.max, I64.max_eq]; omega))
  have hone : (1#i64 : I64).val = 1 := by decide
  obtain ⟨hi, hhi, hhiv⟩ := dns_i64_sub n 1#i64 (by rw [hone, hnv]; simp; omega) (by rw [hone, hnv]; simp; omega)
  have hlen : (Slice.len a).val = a.val.length := by simp
  obtain ⟨y, hy, hy1, hy2, hy3, hy4⟩ := dns_bs_loop a v hn 0#i64 hi 0#usize (by decide) (by simp) (by rw [hhiv, hone, hnv, hlen]; omega)
    (by rw [hhiv, hone, hnv, hlen]; omega) (by simp)
  rw [dns_bs_spec]
  have e0 : ((0#i64 : I64).val) = 0 := by decide
  rw [e0, hhiv, hone, hnv, hlen] at hy1 hy2
  simp only [List.size_toArray]
  simp only [Nat.sub_zero, show ((0#usize : Usize).val) = 0 by decide] at hy1 hy2
  unfold beatmap.dotnet.binary_search_f64
  simp only [hnc, bind_ok, hhi, hy]
  obtain ⟨ylo, yres⟩ := y
  cases yres with
  | some r =>
    simp only at hy2 ⊢
    refine ⟨r, rfl, ?_⟩
    rw [← hy2]; rfl
  | none =>
    simp only at hy1 hy2
    rw [← hy2]
    simp only at hy3 hy4
    have hneg : ∃ z, (-. ylo) = ok z ∧ z.val = -ylo.val := by
      have hne : ylo ≠ IScalar.min IScalarTy.I64 := by
        intro h; rw [h] at hy3
        have : IScalar.min IScalarTy.I64 = -9223372036854775808 := by
          simp [IScalar.min]; simp [I64.min_eq]
        rw [this] at hy3; omega
      obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (IScalar.neg_step ylo hne)
      exact ⟨z, hz, hzv⟩
    obtain ⟨z, hz, hzv⟩ := hneg
    obtain ⟨w, hw, hwv⟩ := dns_i64_sub z 1#i64 (by rw [hone, hzv]; omega) (by rw [hone, hzv]; omega)
    refine ⟨w, ?_, ?_⟩
    · show (do let i2 ← -. ylo; i2 - 1#i64) = ok w
      rw [hz]; simp only [bind_ok]; exact hw
    · rw [hwv, hzv, hone, hy1]; rfl


/-! ## IntroSort pieces (`swap`, `swapIfGreater`, `insertionSort`) -/

theorem dns_toList_set! {T : Type} (a : Array T) (i : Nat) (x : T) : (a.set! i x).toList = a.toList.set i x := by
  simp [Array.set!, Array.setIfInBounds]
  split <;> simp_all [List.set_eq_of_length_le]

theorem beatmap.dotnet.swap_refines {T : Type} [Inhabited T] (cl : core.clone.Clone T) (hcl : ∀ x, cl.clone x = ok x)
    (a : alloc.vec.Vec T) (i j : Usize) (hi : i.val < a.val.length) (hj : j.val < a.val.length) :
    ∃ r, beatmap.dotnet.swap cl a i j = ok r ∧ r.val = (IntroSort.swap a.val.toArray i.val j.val).toList := by
  have hj' : j.val < (alloc.vec.Vec.set a i (a.val[j.val]'hj)).val.length := by simp [vec_set_val']; exact hj
  refine ⟨alloc.vec.Vec.set (alloc.vec.Vec.set a i (a.val[j.val]'hj)) j (a.val[i.val]'hi), ?_, ?_⟩
  · simp [beatmap.dotnet.swap, vec_index_eq _ _ hi, vec_index_eq _ _ hj, hcl, vec_index_mut_eq _ _ hi,
      vec_index_mut_eq _ _ hj', vec_index_mut_usize_ok _ _ hj']
  · simp only [IntroSort.swap, dns_toList_set!, vec_set_val']
    rw [getElem!_pos _ i.val (by simpa using hi), getElem!_pos _ j.val (by simpa using hj)]
    simp

theorem beatmap.dotnet.swap_if_greater_refines {T : Type} [Inhabited T] (cl : core.clone.Clone T)
    (hcl : ∀ x, cl.clone x = ok x) (sc : beatmap.dotnet.SortCmp T) (cmp : T → T → Int)
    (hsc : ∀ x y, ∃ r, sc.cmp3 x y = ok r ∧ r.val = cmp x y)
    (a : alloc.vec.Vec T) (i j : Usize) (hi : i.val < a.val.length) (hj : j.val < a.val.length) :
    ∃ r, beatmap.dotnet.swap_if_greater cl sc a i j = ok r ∧
      r.val = (IntroSort.swapIfGreater cmp a.val.toArray i.val j.val).toList := by
  obtain ⟨c, hc, hcv⟩ := hsc (a.val[i.val]'hi) (a.val[j.val]'hj)
  obtain ⟨r, hr, hrv⟩ := beatmap.dotnet.swap_refines cl hcl a i j hi hj
  unfold beatmap.dotnet.swap_if_greater IntroSort.swapIfGreater
  simp only [vec_index_eq _ _ hi, vec_index_eq _ _ hj, bind_ok, hc]
  rw [getElem!_pos _ i.val (by simpa using hi), getElem!_pos _ j.val (by simpa using hj)]
  simp only [List.getElem_toArray]
  by_cases hg : c > 0#i32
  · have : cmp (a.val[i.val]'hi) (a.val[j.val]'hj) > 0 := by
      rw [← hcv]; have := hg; simpa using this
    simp only [hg, if_true, this]; exact ⟨r, hr, hrv⟩
  · have : ¬ cmp (a.val[i.val]'hi) (a.val[j.val]'hj) > 0 := by
      rw [← hcv]; have := hg; simpa using this
    simp only [hg, if_false, this]; exact ⟨a, rfl, by simp⟩


/-- inner step of `IntroSort.insertionSort` (state: array, j, go; `t` = the element being inserted) -/
def dnsIsIn {α : Type} [Inhabited α] (cmp : α → α → Int) (lo : Nat) (t : α) (s : Array α × Int × Bool) :
    Array α × Int × Bool :=
  if s.2.2 = true then
    if (decide (s.2.1 ≥ 0) && decide (cmp t s.1[lo + s.2.1.toNat]! < 0)) = true then
      (s.1.set! (lo + s.2.1.toNat + 1) s.1[lo + s.2.1.toNat]!, s.2.1 - 1, s.2.2)
    else (s.1, s.2.1, false)
  else (s.1, s.2.1, s.2.2)

theorem dns_toArray_set {α : Type} (l : List α) (i : Nat) (x : α) : (l.set i x).toArray = l.toArray.set! i x := by
  apply Array.ext'; simp [dns_toList_set!]

theorem dns_i64_of_usize (u : Usize) (h : u.val < 2^62) : ∃ j : I64, lift (UScalar.hcast .I64 u) = ok j ∧ j.val = u.val := by
  obtain ⟨j, hj, hjv⟩ := eq_ok_of_spec (UScalar.hcast_inBounds_spec .I64 u (by simp [IScalar.max, I64.max_eq]; omega))
  exact ⟨j, hj, hjv⟩

theorem dns_usize_of_i64 (j : I64) (h0 : 0 ≤ j.val) (h : j.val < 2^31) :
    ∃ u : Usize, lift (IScalar.hcast .Usize j) = ok u ∧ (u.val : Int) = j.val := by
  obtain ⟨u, hu, huv⟩ := eq_ok_of_spec (IScalar.hcast_inBounds_spec .Usize j
    (by have := dns_usize_max; rw [UScalar.max_USize_eq]; constructor <;> omega))
  exact ⟨u, hu, by simpa using huv⟩

theorem dns_usize_add (a b : Usize) (h : a.val + b.val < 2^32) : ∃ z, a + b = ok z ∧ z.val = a.val + b.val := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (Usize.add_spec (x := a) (y := b) (by have := dns_usize_max; omega))
  exact ⟨z, hz, by simpa using hv⟩


theorem dns_ins_inner {T : Type} [Inhabited T] (cl : core.clone.Clone T) (hcl : ∀ x, cl.clone x = ok x)
    (sc : beatmap.dotnet.SortCmp T) (cmp : T → T → Int) (hsc : ∀ x y, ∃ r, sc.cmp3 x y = ok r ∧ r.val = cmp x y)
    (lo i : Usize) (t : T) (N : Nat) (hN : N < 2^31) (hb : lo.val + i.val + 1 < N) :
    ∀ (a : alloc.vec.Vec T) (j : I64) (go : Bool) (k : Usize), a.val.length = N → -1 ≤ j.val → j.val ≤ i.val →
      k.val ≤ i.val + 1 →
      ∃ y, beatmap.dotnet.insertion_sort_loop0_loop0 cl sc a lo i t j go k = ok y ∧
        y.1.val.toArray = (iterR (fun _ s => .yield (dnsIsIn cmp lo.val t s)) k.val (i.val + 1 - k.val)
          (a.val.toArray, j.val, go)).1 ∧
        y.2.val = (iterR (fun _ s => .yield (dnsIsIn cmp lo.val t s)) k.val (i.val + 1 - k.val)
          (a.val.toArray, j.val, go)).2.1 ∧
        y.1.val.length = N ∧ -1 ≤ y.2.val ∧ y.2.val ≤ i.val := by
  intro a j go k ha hj0 hj1 hk
  obtain ⟨y, hl, hy⟩ := loop_fold_gen
    (fun (x : alloc.vec.Vec T × I64 × Bool × Usize) =>
      beatmap.dotnet.insertion_sort_loop0_loop0.body cl sc lo i t x.1 x.2.1 x.2.2.1 x.2.2.2)
    (·.2.2.2) (i.val + 1)
    (fun x => x.1.val.length = N ∧ -1 ≤ x.2.1.val ∧ x.2.1.val ≤ i.val)
    (fun x => (x.1.val.toArray, x.2.1.val, x.2.2.1))
    (fun _ s => dnsIsIn cmp lo.val t s)
    (fun y s => y.1.val.toArray = s.1 ∧ y.2.val = s.2.1 ∧ y.1.val.length = N ∧ -1 ≤ y.2.val ∧ y.2.val ≤ i.val)
    (by
      rintro ⟨a, j, go, k⟩ ⟨ha, hj0, hj1⟩ hk
      simp only at ha hj0 hj1 hk ⊢
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := dns_usize_max; omega)
      obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := dns_usize_max; omega)
      have hkiv : k.val < i1.val := by omega
      have hki : k < i1 := hkiv
      cases go
      · refine ⟨(a, j, false, k1), ?_, hk1v, ?_, ha, hj0, hj1⟩
        · simp [beatmap.dotnet.insertion_sort_loop0_loop0.body, hi1, hki, hkiv, hk1]
        · simp [dnsIsIn]
      · by_cases hjn : 0 ≤ j.val
        · obtain ⟨u, hu, huv⟩ := dns_usize_of_i64 j hjn (by omega)
          obtain ⟨p, hp, hpv⟩ := dns_usize_add lo u (by omega)
          have hpl : p.val < a.val.length := by omega
          obtain ⟨c, hc, hcv⟩ := hsc t (a.val[p.val]'hpl)
          have hge : j ≥ 0#i64 := by show (0#i64 : I64).val ≤ j.val; simpa using hjn
          have hjt : j.val.toNat = u.val := by omega
          have hget : a.val.toArray[lo.val + j.val.toNat]! = a.val[p.val]'hpl := by
            rw [getElem!_pos _ _ (by simp; omega)]; simp; congr 1; omega
          by_cases hcn : c < 0#i32
          · obtain ⟨p1, hp1, hp1v⟩ := usize_add_one p (by have := dns_usize_max; omega)
            have hp1l : p1.val < a.val.length := by omega
            obtain ⟨j2, hj2, hj2v⟩ := i64_sub_one j (by omega) (by omega)
            refine ⟨(alloc.vec.Vec.set a p1 (a.val[p.val]'hpl), j2, true, k1), ?_, hk1v, ?_, ?_, ?_, ?_⟩
            · have hcn' : c.val < 0 := by simpa using hcn
              simp [beatmap.dotnet.insertion_sort_loop0_loop0.body, hi1, hki, hkiv, hk1, hge, hu, hp, vec_index_eq _ _ hpl,
                hc, hcn, hcn', hcl, vec_index_mut_eq _ _ hp1l, hp1, hj2, vec_index_usize_ok _ _ hpl,
                vec_index_mut_usize_ok _ _ hp1l]
            · have hcv' : cmp t (a.val[p.val]'hpl) < 0 := by rw [← hcv]; simpa using hcn
              have e1 : lo.val + j.val.toNat + 1 = p1.val := by omega
              simp only [dnsIsIn, if_true, hget, hjn, decide_true, hcv', Bool.and_self, e1]
              rw [vec_set_val', dns_toArray_set]; simp [hj2v]
            · simp [vec_set_val', ha]
            · rw [hj2v]; omega
            · rw [hj2v]; omega
          · refine ⟨(a, j, false, k1), ?_, hk1v, ?_, ha, hj0, hj1⟩
            · have hcn' : ¬ c.val < 0 := by simpa using hcn
              simp [beatmap.dotnet.insertion_sort_loop0_loop0.body, hi1, hki, hkiv, hk1, hge, hu, hp, vec_index_eq _ _ hpl,
                hc, hcn, hcn', vec_index_usize_ok _ _ hpl]
            · have hcv' : ¬ cmp t (a.val[p.val]'hpl) < 0 := by rw [← hcv]; simpa using hcn
              simp [dnsIsIn, hget, hjn, hcv']
        · have hge : ¬ j ≥ 0#i64 := by show ¬ (0#i64 : I64).val ≤ j.val; simpa using hjn
          refine ⟨(a, j, false, k1), ?_, hk1v, ?_, ha, hj0, hj1⟩
          · have hjn' : ¬ 0 ≤ j.val := hjn
            simp [beatmap.dotnet.insertion_sort_loop0_loop0.body, hi1, hki, hkiv, hk1, hge, hjn']
          · simp [dnsIsIn, hjn])
    (by
      rintro ⟨a, j, go, k⟩ ⟨ha, hj0, hj1⟩ hk
      simp only at ha hj0 hj1 hk ⊢
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := dns_usize_max; omega)
      have hkiv : ¬ k.val < i1.val := by omega
      have hki : ¬ k < i1 := hkiv
      exact ⟨(a, j), by simp [beatmap.dotnet.insertion_sort_loop0_loop0.body, hi1, hki, hkiv], rfl, rfl, ha, hj0, hj1⟩)
    (a, j, go, k) ⟨ha, hj0, hj1⟩ hk
  obtain ⟨h1, h2, h3, h4, h5⟩ := hy
  exact ⟨y, by unfold beatmap.dotnet.insertion_sort_loop0_loop0; exact hl, h1, h2, h3, h4, h5⟩


def dnsIsOut {α : Type} [Inhabited α] (cmp : α → α → Int) (lo : Nat) (a : Array α) (i : Nat) : Array α :=
  let t := a[lo + i + 1]!
  let s := iterR (fun _ s => .yield (dnsIsIn cmp lo t s)) 0 (i + 1) (a, (i : Int), true)
  s.1.set! (lo + (s.2.1 + 1).toNat) t

theorem dns_iterR_ext {S : Type} (F G : Nat → S → ForInStep S) (h : ∀ j s, F j s = G j s) (j n : Nat) (s : S) :
    iterR F j n s = iterR G j n s := by
  have : F = G := by funext j s; exact h j s
  rw [this]

theorem dns_ins_spec {α : Type} [Inhabited α] (cmp : α → α → Int) (a : Array α) (lo len : Nat) :
    IntroSort.insertionSort cmp a lo len = iterR (fun i a => .yield (dnsIsOut cmp lo a i)) 0 (len - 1) a := by
  unfold IntroSort.insertionSort
  simp only [Id.run, forIn_range_iterR, Nat.sub_zero, id_bind_eq]
  show iterR _ 0 (len - 1) a = _
  rw [dns_iterR_ext _ (fun i a => .yield (dnsIsOut cmp lo a i)) ?h]
  intro i s
  simp only [dnsIsOut]
  show ForInStep.yield ((iterR _ 0 (i + 1) (s, (i : Int), true)).1.set! _ _) = _
  rw [dns_iterR_ext _ (fun _ s' => .yield (dnsIsIn cmp lo s[lo + i + 1]! s')) ?h2]
  intro _ s'
  simp only [dnsIsIn]
  split <;> (try split) <;> rfl

/-- `InsertionSort(keys[lo..lo+len))` (in-bounds range; sizes below 2^31) -/
theorem beatmap.dotnet.insertion_sort_refines {T : Type} [Inhabited T] (cl : core.clone.Clone T)
    (hcl : ∀ x, cl.clone x = ok x) (sc : beatmap.dotnet.SortCmp T) (cmp : T → T → Int)
    (hsc : ∀ x y, ∃ r, sc.cmp3 x y = ok r ∧ r.val = cmp x y)
    (a : alloc.vec.Vec T) (lo len : Usize) (hb : lo.val + len.val ≤ a.val.length) (hN : a.val.length < 2^31) :
    ∃ r, beatmap.dotnet.insertion_sort cl sc a lo len = ok r ∧
      r.val.toArray = IntroSort.insertionSort cmp a.val.toArray lo.val len.val ∧ r.val.length = a.val.length := by
  obtain ⟨n1, hn1, hn1v⟩ := beatmap.dotnet.nat_sub_refines len 1#usize
  have hone : (1#usize : Usize).val = 1 := by decide
  rw [hone] at hn1v
  obtain ⟨y, hl, hy⟩ := loop_fold_gen
    (fun (x : alloc.vec.Vec T × Usize) => beatmap.dotnet.insertion_sort_loop0.body cl sc lo len x.1 x.2)
    (·.2) (len.val - 1) (fun x => x.1.val.length = a.val.length) (fun x => x.1.val.toArray)
    (fun i s => dnsIsOut cmp lo.val s i) (fun y s => y.val.toArray = s ∧ y.val.length = a.val.length)
    (by
      rintro ⟨v, i⟩ hv hi
      simp only at hv hi ⊢
      obtain ⟨p, hp, hpv⟩ := dns_usize_add lo i (by omega)
      obtain ⟨p1, hp1, hp1v⟩ := usize_add_one p (by have := dns_usize_max; omega)
      have hp1l : p1.val < v.val.length := by omega
      obtain ⟨j, hj, hjv⟩ := dns_i64_of_usize i (by omega)
      obtain ⟨y, hy, hy1, hy2, hy3, hy4, hy5⟩ := dns_ins_inner cl hcl sc cmp hsc lo i (v.val[p1.val]'hp1l)
        v.val.length (by omega) (by omega) v j true 0#usize rfl (by omega) (by omega) (by simp)
      obtain ⟨j1, hj1, hj1v⟩ := i64_add_one y.2 (by omega) (by omega)
      obtain ⟨u, hu, huv⟩ := dns_usize_of_i64 j1 (by omega) (by omega)
      obtain ⟨q, hq, hqv⟩ := dns_usize_add lo u (by omega)
      have hql : q.val < y.1.val.length := by omega
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := dns_usize_max; omega)
      have hiv : i.val < n1.val := by omega
      refine ⟨(alloc.vec.Vec.set y.1 q (v.val[p1.val]'hp1l), i1), ?_, hi1v, ?_, ?_⟩
      · obtain ⟨y1, y2⟩ := y
        simp only at hy hql ⊢
        simp [beatmap.dotnet.insertion_sort_loop0.body, hn1, hiv, show i < n1 from hiv, hp, hp1,
          vec_index_eq _ _ hp1l, hcl, hj, hy, hj1, hu, hq, vec_index_mut_eq _ _ hql, hi1,
          vec_index_usize_ok _ _ hp1l, vec_index_mut_usize_ok _ _ hql]
      · simp only [dnsIsOut]
        have hget : v.val.toArray[lo.val + i.val + 1]! = v.val[p1.val]'hp1l := by
          rw [getElem!_pos _ _ (by simp; omega)]; simp; congr 1; omega
        simp only [show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero, hjv] at hy1 hy2
        rw [hget, ← hy1, ← hy2]
        rw [vec_set_val', dns_toArray_set]
        congr 1; omega
      · simp [vec_set_val', hy3, hv])
    (by
      rintro ⟨v, i⟩ hv hi
      simp only at hv hi ⊢
      have hiv : ¬ i.val < n1.val := by omega
      exact ⟨v, by simp [beatmap.dotnet.insertion_sort_loop0.body, hn1, hiv, show ¬ i < n1 from hiv], rfl, hv⟩)
    (a, 0#usize) rfl (by simp)
  obtain ⟨h1, h2⟩ := hy
  refine ⟨y, by unfold beatmap.dotnet.insertion_sort beatmap.dotnet.insertion_sort_loop0; exact hl, ?_, h2⟩
  rw [h1, dns_ins_spec]; rfl


theorem dns_usize_div2 (x : Usize) : ∃ z, x / 2#usize = ok z ∧ z.val = x.val / 2 := by
  obtain ⟨z, hz, hv⟩ := UScalar.div_spec x (y := 2#usize) (by simp)
  exact ⟨z, hz, by simpa using hv⟩
theorem dns_usize_mul2 (x : Usize) (h : 2 * x.val < 2^32) : ∃ z, 2#usize * x = ok z ∧ z.val = 2 * x.val := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (UScalar.mul_spec (x := 2#usize) (y := x)
    (by have := dns_usize_max; rw [UScalar.max_USize_eq]; simp; omega))
  exact ⟨z, hz, by simpa using hv⟩
theorem dns_usize_sub1 (x : Usize) (h : 1 ≤ x.val) : ∃ z, x - 1#usize = ok z ∧ z.val = x.val - 1 := by
  obtain ⟨z, hz, hv, -⟩ := eq_ok_of_spec (UScalar.sub_spec (x := x) (y := 1#usize) (by simpa using h))
  exact ⟨z, hz, by simpa using hv⟩

/-- the loop step of `IntroSort.downHeap` (`d` = the sifted element) -/
def dnsDh {α : Type} [Inhabited α] (cmp : α → α → Int) (lo n : Nat) (d : α) (s : Array α × Nat × Bool) :
    Array α × Nat × Bool :=
  if (s.2.2 && decide (s.2.1 ≤ n / 2)) = true then
    let c := if (decide (2 * s.2.1 < n) && decide (cmp s.1[lo + 2 * s.2.1 - 1]! s.1[lo + 2 * s.2.1]! < 0)) = true
      then 2 * s.2.1 + 1 else 2 * s.2.1
    if (!decide (cmp d s.1[lo + c - 1]! < 0)) = true then (s.1, s.2.1, false)
    else (s.1.set! (lo + s.2.1 - 1) s.1[lo + c - 1]!, c, s.2.2)
  else s

theorem dns_dh_spec {α : Type} [Inhabited α] (cmp : α → α → Int) (a : Array α) (lo i0 n : Nat) :
    IntroSort.downHeap cmp a lo i0 n =
      (let s := iterR (fun _ s => .yield (dnsDh cmp lo n a[lo + i0 - 1]! s)) 0 (n + 1) (a, i0, true)
       s.1.set! (lo + s.2.1 - 1) a[lo + i0 - 1]!) := by
  unfold IntroSort.downHeap
  simp only [Id.run, forIn_range_iterR, Nat.sub_zero, id_bind_eq]
  show (iterR _ 0 (n + 1) (a, i0, true)).1.set! _ _ = _
  rw [dns_iterR_ext _ (fun _ s => .yield (dnsDh cmp lo n a[lo + i0 - 1]! s)) ?h]
  intro _ s
  simp only [dnsDh]
  split
  · split
    · split <;> rfl
    · split <;> rfl
  · rfl


theorem dns_dh_loop {T : Type} [Inhabited T] (cl : core.clone.Clone T) (hcl : ∀ x, cl.clone x = ok x)
    (sc : beatmap.dotnet.SortCmp T) (cmp : T → T → Int) (hsc : ∀ x y, ∃ r, sc.cmp3 x y = ok r ∧ r.val = cmp x y)
    (lo n : Usize) (d : T) (N : Nat) (hN : N < 2^31) (hb : lo.val + n.val ≤ N) :
    ∀ (a : alloc.vec.Vec T) (i : Usize) (go : Bool) (k : Usize), a.val.length = N → 1 ≤ i.val → i.val ≤ n.val →
      k.val ≤ n.val + 1 →
      ∃ y, beatmap.dotnet.down_heap_loop cl sc a lo n d i go k = ok y ∧
        y.1.val.toArray = (iterR (fun _ s => .yield (dnsDh cmp lo.val n.val d s)) k.val (n.val + 1 - k.val)
          (a.val.toArray, i.val, go)).1 ∧
        y.2.val = (iterR (fun _ s => .yield (dnsDh cmp lo.val n.val d s)) k.val (n.val + 1 - k.val)
          (a.val.toArray, i.val, go)).2.1 ∧
        y.1.val.length = N ∧ 1 ≤ y.2.val ∧ y.2.val ≤ n.val := by
  intro a i go k ha hi0 hi1 hk
  obtain ⟨n1, hn1, hn1v⟩ := usize_add_one n (by have := dns_usize_max; omega)
  obtain ⟨y, hl, hy⟩ := loop_fold_gen
    (fun (x : alloc.vec.Vec T × Usize × Bool × Usize) =>
      beatmap.dotnet.down_heap_loop.body cl sc lo n d x.1 x.2.1 x.2.2.1 x.2.2.2)
    (·.2.2.2) (n.val + 1)
    (fun x => x.1.val.length = N ∧ 1 ≤ x.2.1.val ∧ x.2.1.val ≤ n.val)
    (fun x => (x.1.val.toArray, x.2.1.val, x.2.2.1))
    (fun _ s => dnsDh cmp lo.val n.val d s)
    (fun y s => y.1.val.toArray = s.1 ∧ y.2.val = s.2.1 ∧ y.1.val.length = N ∧ 1 ≤ y.2.val ∧ y.2.val ≤ n.val)
    (by
      rintro ⟨a, i, go, k⟩ ⟨ha, hi0, hi1⟩ hk
      simp only at ha hi0 hi1 hk ⊢
      obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := dns_usize_max; omega)
      have hkn : k.val < n1.val := by omega
      obtain ⟨h2, hh2, hh2v⟩ := dns_usize_div2 n
      have hbase : ∀ go', go' = false ∨ ¬ i.val ≤ n.val / 2 →
          beatmap.dotnet.down_heap_loop.body cl sc lo n d a i go' k = ok (.cont (a, i, go', k1)) := by
        intro go' hg
        rcases hg with hg | hg
        · subst hg; simp [beatmap.dotnet.down_heap_loop.body, hn1, hkn, show k < n1 from hkn, hk1]
        · have hg' : ¬ i ≤ h2 := by show ¬ i.val ≤ h2.val; omega
          have hg'' : ¬ i.val ≤ h2.val := by omega
          cases go' <;> simp [beatmap.dotnet.down_heap_loop.body, hn1, hkn, show k < n1 from hkn, hk1, hh2, hg', hg'']
      by_cases hgo : go = true ∧ i.val ≤ n.val / 2
      · obtain ⟨rfl, hle⟩ := hgo
        have hle' : i ≤ h2 := by show i.val ≤ h2.val; omega
        obtain ⟨c0, hc0, hc0v⟩ := dns_usize_mul2 i (by omega)
        have hle'' : i.val ≤ h2.val := by omega
        by_cases hlt : c0.val < n.val
        · obtain ⟨p, hp, hpv⟩ := dns_usize_add lo c0 (by omega)
          obtain ⟨p1, hp1, hp1v⟩ := dns_usize_sub1 p (by omega)
          have hpl : p.val < a.val.length := by omega
          have hp1l : p1.val < a.val.length := by omega
          obtain ⟨cc, hcc, hccv⟩ := hsc (a.val[p1.val]'hp1l) (a.val[p.val]'hpl)
          have hg1 : a.val.toArray[lo.val + 2 * i.val - 1]! = a.val[p1.val]'hp1l := by
            rw [getElem!_pos _ _ (by simp; omega)]; simp; congr 1; omega
          have hg2 : a.val.toArray[lo.val + 2 * i.val]! = a.val[p.val]'hpl := by
            rw [getElem!_pos _ _ (by simp; omega)]; simp; congr 1; omega
          have hlt' : c0 < n := hlt
          have hlt2 : 2 * i.val < n.val := by omega
          by_cases hcn : cc < 0#i32
          · have hcn' : cc.val < 0 := by simpa using hcn
            have hcv : cmp (a.val[p1.val]'hp1l) (a.val[p.val]'hpl) < 0 := by rw [← hccv]; exact hcn'
            obtain ⟨C1, hC1, hC1v⟩ := usize_add_one c0 (by have := dns_usize_max; omega)
            obtain ⟨q, hq, hqv⟩ := dns_usize_add lo C1 (by omega)
            obtain ⟨q1, hq1, hq1v⟩ := dns_usize_sub1 q (by omega)
            have hq1l : q1.val < a.val.length := by omega
            obtain ⟨e, he, hev⟩ := hsc d (a.val[q1.val]'hq1l)
            have hgq : a.val.toArray[lo.val + C1.val - 1]! = a.val[q1.val]'hq1l := by
              rw [getElem!_pos _ _ (by simp; omega)]; simp; congr 1; omega
            by_cases hen : e < 0#i32
            · have hen' : e.val < 0 := by simpa using hen
              obtain ⟨r, hr, hrv⟩ := dns_usize_add lo i (by omega)
              obtain ⟨r1, hr1, hr1v⟩ := dns_usize_sub1 r (by omega)
              have hr1l : r1.val < a.val.length := by omega
              refine ⟨(alloc.vec.Vec.set a r1 (a.val[q1.val]'hq1l), C1, true, k1), ?_, hk1v, ?_, by simp [vec_set_val', ha],
                by dsimp only; omega, by dsimp only; omega⟩
              · simp [beatmap.dotnet.down_heap_loop.body, hn1, hkn, show k < n1 from hkn, hk1, hh2, hle', hle'', hc0,
                  hlt', hlt, hp, hp1, vec_index_eq _ _ hp1l, vec_index_eq _ _ hpl, vec_index_usize_ok _ _ hp1l, vec_index_usize_ok _ _ hpl, hcc, hcn, hcn', hC1, hq, hq1, vec_index_eq _ _ hq1l, vec_index_usize_ok _ _ hq1l, he, hen, hen', hcl, hr, hr1,
                  vec_index_mut_eq _ _ hr1l, vec_index_mut_usize_ok _ _ hr1l]
              · have hev' : cmp d (a.val[q1.val]'hq1l) < 0 := by rw [← hev]; exact hen'
                simp only [dnsDh, hle, decide_true, Bool.and_self, if_true, hlt2, hg1, hg2, hcv, decide_true, show 2 * i.val + 1 = C1.val by omega, hgq, hev', Bool.not_true,
                  Bool.false_eq_true, if_false]
                rw [vec_set_val', dns_toArray_set]; congr 2; omega
            · have hen' : ¬ e.val < 0 := by simpa using hen
              refine ⟨(a, i, false, k1), ?_, hk1v, ?_, ha, hi0, hi1⟩
              · simp [beatmap.dotnet.down_heap_loop.body, hn1, hkn, show k < n1 from hkn, hk1, hh2, hle', hle'', hc0,
                  hlt', hlt, hp, hp1, vec_index_eq _ _ hp1l, vec_index_eq _ _ hpl, vec_index_usize_ok _ _ hp1l, vec_index_usize_ok _ _ hpl, hcc, hcn, hcn', hC1, hq, hq1, vec_index_eq _ _ hq1l, vec_index_usize_ok _ _ hq1l, he, hen, hen']
              · have hev' : ¬ cmp d (a.val[q1.val]'hq1l) < 0 := by rw [← hev]; exact hen'
                simp only [dnsDh, hle, decide_true, Bool.and_self, if_true, hlt2, hg1, hg2, hcv, decide_true, show 2 * i.val + 1 = C1.val by omega, hgq, hev', decide_false, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
                <;> simp only [Bool.false_eq_true, ite_false, ite_true, hgq, hev', decide_false, Bool.not_false]
          · have hcn' : ¬ cc.val < 0 := by simpa using hcn
            have hcv : ¬ cmp (a.val[p1.val]'hp1l) (a.val[p.val]'hpl) < 0 := by rw [← hccv]; exact hcn'
            obtain ⟨C1, hC1e⟩ : ∃ C1, C1 = c0 := ⟨c0, rfl⟩
            subst hC1e
            obtain ⟨q, hq, hqv⟩ := dns_usize_add lo C1 (by omega)
            obtain ⟨q1, hq1, hq1v⟩ := dns_usize_sub1 q (by omega)
            have hq1l : q1.val < a.val.length := by omega
            have hqq : q1 = p1 := UScalar.eq_of_val_eq (by omega)
            subst hqq
            obtain ⟨e, he, hev⟩ := hsc d (a.val[q1.val]'hq1l)
            have hgq : a.val.toArray[lo.val + 2 * i.val - 1]! = a.val[q1.val]'hq1l := by
              rw [getElem!_pos _ _ (by simp; omega)]; simp; congr 1; omega
            by_cases hen : e < 0#i32
            · have hen' : e.val < 0 := by simpa using hen
              obtain ⟨r, hr, hrv⟩ := dns_usize_add lo i (by omega)
              obtain ⟨r1, hr1, hr1v⟩ := dns_usize_sub1 r (by omega)
              have hr1l : r1.val < a.val.length := by omega
              refine ⟨(alloc.vec.Vec.set a r1 (a.val[q1.val]'hq1l), C1, true, k1), ?_, hk1v, ?_, by simp [vec_set_val', ha],
                by dsimp only; omega, by dsimp only; omega⟩
              · simp [beatmap.dotnet.down_heap_loop.body, hn1, hkn, show k < n1 from hkn, hk1, hh2, hle', hle'', hc0,
                  hlt', hlt, hp, hp1, vec_index_eq _ _ hp1l, vec_index_eq _ _ hpl, vec_index_usize_ok _ _ hp1l, vec_index_usize_ok _ _ hpl, hcc, hcn, hcn', hq, hq1, vec_index_eq _ _ hq1l, vec_index_usize_ok _ _ hq1l, he, hen, hen', hcl, hr, hr1,
                  vec_index_mut_eq _ _ hr1l, vec_index_mut_usize_ok _ _ hr1l]
              · have hev' : cmp d (a.val[q1.val]'hq1l) < 0 := by rw [← hev]; exact hen'
                simp only [dnsDh, hle, decide_true, Bool.and_self, if_true, hlt2, hg1, hg2, hcv, decide_false, Bool.and_false, hgq, hev', Bool.not_true,
                  Bool.false_eq_true, if_false]
                rw [show 2 * i.val = C1.val by omega, vec_set_val', dns_toArray_set]; congr 2; omega
            · have hen' : ¬ e.val < 0 := by simpa using hen
              refine ⟨(a, i, false, k1), ?_, hk1v, ?_, ha, hi0, hi1⟩
              · simp [beatmap.dotnet.down_heap_loop.body, hn1, hkn, show k < n1 from hkn, hk1, hh2, hle', hle'', hc0,
                  hlt', hlt, hp, hp1, vec_index_eq _ _ hp1l, vec_index_eq _ _ hpl, vec_index_usize_ok _ _ hp1l, vec_index_usize_ok _ _ hpl, hcc, hcn, hcn', hq, hq1, vec_index_eq _ _ hq1l, vec_index_usize_ok _ _ hq1l, he, hen, hen']
              · have hev' : ¬ cmp d (a.val[q1.val]'hq1l) < 0 := by rw [← hev]; exact hen'
                simp only [dnsDh, hle, decide_true, Bool.and_self, if_true, hlt2, hg1, hg2, hcv, decide_false, Bool.and_false, hgq, hev', decide_false, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
                <;> simp only [Bool.false_eq_true, ite_false, ite_true, hgq, hev', decide_false, Bool.not_false]
        · have hlt' : ¬ c0 < n := hlt
          have hlt2 : ¬ 2 * i.val < n.val := by omega
          obtain ⟨C1, hC1e⟩ : ∃ C1, C1 = c0 := ⟨c0, rfl⟩
          subst hC1e
          obtain ⟨q, hq, hqv⟩ := dns_usize_add lo C1 (by omega)
          obtain ⟨q1, hq1, hq1v⟩ := dns_usize_sub1 q (by omega)
          have hq1l : q1.val < a.val.length := by omega
          obtain ⟨e, he, hev⟩ := hsc d (a.val[q1.val]'hq1l)
          have hgq : a.val.toArray[lo.val + 2 * i.val - 1]! = a.val[q1.val]'hq1l := by
            rw [getElem!_pos _ _ (by simp; omega)]; simp; congr 1; omega
          by_cases hen : e < 0#i32
          · have hen' : e.val < 0 := by simpa using hen
            obtain ⟨r, hr, hrv⟩ := dns_usize_add lo i (by omega)
            obtain ⟨r1, hr1, hr1v⟩ := dns_usize_sub1 r (by omega)
            have hr1l : r1.val < a.val.length := by omega
            refine ⟨(alloc.vec.Vec.set a r1 (a.val[q1.val]'hq1l), C1, true, k1), ?_, hk1v, ?_, by simp [vec_set_val', ha],
              by dsimp only; omega, by dsimp only; omega⟩
            · simp [beatmap.dotnet.down_heap_loop.body, hn1, hkn, show k < n1 from hkn, hk1, hh2, hle', hle'', hc0,
                hlt', hlt, hq, hq1, vec_index_eq _ _ hq1l, vec_index_usize_ok _ _ hq1l, he, hen, hen', hcl, hr, hr1,
                vec_index_mut_eq _ _ hr1l, vec_index_mut_usize_ok _ _ hr1l]
            · have hev' : cmp d (a.val[q1.val]'hq1l) < 0 := by rw [← hev]; exact hen'
              simp only [dnsDh, hle, decide_true, Bool.and_self, if_true, hlt2, decide_false, Bool.false_and, hgq, hev', Bool.not_true,
                Bool.false_eq_true, if_false]
              rw [show 2 * i.val = C1.val by omega, vec_set_val', dns_toArray_set]; congr 2; omega
          · have hen' : ¬ e.val < 0 := by simpa using hen
            refine ⟨(a, i, false, k1), ?_, hk1v, ?_, ha, hi0, hi1⟩
            · simp [beatmap.dotnet.down_heap_loop.body, hn1, hkn, show k < n1 from hkn, hk1, hh2, hle', hle'', hc0,
                hlt', hlt, hq, hq1, vec_index_eq _ _ hq1l, vec_index_usize_ok _ _ hq1l, he, hen, hen']
            · have hev' : ¬ cmp d (a.val[q1.val]'hq1l) < 0 := by rw [← hev]; exact hen'
              simp only [dnsDh, hle, decide_true, Bool.and_self, if_true, hlt2, decide_false, Bool.false_and, hgq, hev', decide_false, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
                <;> simp only [Bool.false_eq_true, ite_false, ite_true, hgq, hev', decide_false, Bool.not_false]
      · have hg : go = false ∨ ¬ i.val ≤ n.val / 2 := by
          cases go <;> simp_all
        refine ⟨(a, i, go, k1), hbase go hg, hk1v, ?_, ha, hi0, hi1⟩
        simp only [dnsDh]
        rcases hg with hg | hg
        · subst hg; simp
        · simp [hg])
    (by
      rintro ⟨a, i, go, k⟩ ⟨ha, hi0, hi1⟩ hk
      simp only at ha hi0 hi1 hk ⊢
      have hkn : ¬ k.val < n1.val := by omega
      exact ⟨(a, i), by simp [beatmap.dotnet.down_heap_loop.body, hn1, hkn, show ¬ k < n1 from hkn], rfl, rfl, ha, hi0, hi1⟩)
    (a, i, go, k) ⟨ha, hi0, hi1⟩ hk
  obtain ⟨h1, h2, h3, h4, h5⟩ := hy
  exact ⟨y, by unfold beatmap.dotnet.down_heap_loop; exact hl, h1, h2, h3, h4, h5⟩

/-- `DownHeap(keys, i, n, lo)` (1 ≤ i ≤ n, in-bounds range, sizes below 2^31) -/
theorem beatmap.dotnet.down_heap_refines {T : Type} [Inhabited T] (cl : core.clone.Clone T)
    (hcl : ∀ x, cl.clone x = ok x) (sc : beatmap.dotnet.SortCmp T) (cmp : T → T → Int)
    (hsc : ∀ x y, ∃ r, sc.cmp3 x y = ok r ∧ r.val = cmp x y)
    (a : alloc.vec.Vec T) (lo i0 n : Usize) (h1 : 1 ≤ i0.val) (h2 : i0.val ≤ n.val)
    (hb : lo.val + n.val ≤ a.val.length) (hN : a.val.length < 2^31) :
    ∃ r, beatmap.dotnet.down_heap cl sc a lo i0 n = ok r ∧
      r.val.toArray = IntroSort.downHeap cmp a.val.toArray lo.val i0.val n.val ∧ r.val.length = a.val.length := by
  obtain ⟨p, hp, hpv⟩ := dns_usize_add lo i0 (by omega)
  obtain ⟨p1, hp1, hp1v⟩ := dns_usize_sub1 p (by omega)
  have hp1l : p1.val < a.val.length := by omega
  obtain ⟨y, hy, hy1, hy2, hy3, hy4, hy5⟩ := dns_dh_loop cl hcl sc cmp hsc lo n (a.val[p1.val]'hp1l) a.val.length hN hb
    a i0 true 0#usize rfl h1 h2 (by simp)
  obtain ⟨q, hq, hqv⟩ := dns_usize_add lo y.2 (by omega)
  obtain ⟨q1, hq1, hq1v⟩ := dns_usize_sub1 q (by omega)
  have hq1l : q1.val < y.1.val.length := by omega
  refine ⟨alloc.vec.Vec.set y.1 q1 (a.val[p1.val]'hp1l), ?_, ?_, by simp [vec_set_val', hy3]⟩
  · obtain ⟨y1, y2⟩ := y
    simp only at hq hq1l ⊢
    simp [beatmap.dotnet.down_heap, hp, hp1, vec_index_eq _ _ hp1l, vec_index_usize_ok _ _ hp1l, hcl, hy, hq, hq1,
      vec_index_mut_eq _ _ hq1l, vec_index_mut_usize_ok _ _ hq1l]
  · have hget : a.val.toArray[lo.val + i0.val - 1]! = a.val[p1.val]'hp1l := by
      rw [getElem!_pos _ _ (by simp; omega)]; simp; congr 1; omega
    rw [dns_dh_spec, hget]; dsimp only
    simp only [show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero] at hy1 hy2
    rw [← hy1, ← hy2, vec_set_val', dns_toArray_set]; congr 1; omega


theorem dns_hs_spec {α : Type} [Inhabited α] (cmp : α → α → Int) (a : Array α) (lo n : Nat) :
    IntroSort.heapSort cmp a lo n =
      (iterR (fun _ (s : Array α × Nat) => .yield (IntroSort.downHeap cmp (IntroSort.swap s.1 lo (lo + s.2 - 1)) lo 1 (s.2 - 1), s.2 - 1))
        0 (n - 1)
        ((iterR (fun _ (s : Array α × Nat) => .yield (IntroSort.downHeap cmp s.1 lo s.2 n, s.2 - 1)) 0 (n / 2) (a, n / 2)).1, n)).1 := by
  unfold IntroSort.heapSort
  simp only [Id.run, forIn_range_iterR, Nat.sub_zero, id_bind_eq]
  rfl

theorem beatmap.dotnet.heap_sort_refines {T : Type} [Inhabited T] (cl : core.clone.Clone T)
    (hcl : ∀ x, cl.clone x = ok x) (sc : beatmap.dotnet.SortCmp T) (cmp : T → T → Int)
    (hsc : ∀ x y, ∃ r, sc.cmp3 x y = ok r ∧ r.val = cmp x y)
    (a : alloc.vec.Vec T) (lo n : Usize) (hb : lo.val + n.val ≤ a.val.length) (hN : a.val.length < 2^31) :
    ∃ r, beatmap.dotnet.heap_sort cl sc a lo n = ok r ∧
      r.val.toArray = IntroSort.heapSort cmp a.val.toArray lo.val n.val ∧ r.val.length = a.val.length := by
  obtain ⟨h2, hh2, hh2v⟩ := dns_usize_div2 n
  obtain ⟨y1, hl1, hy1⟩ := loop_fold_gen
    (fun (x : alloc.vec.Vec T × Usize × Usize) => beatmap.dotnet.heap_sort_loop0.body cl sc lo n x.1 x.2.1 x.2.2)
    (·.2.2) (n.val / 2) (fun x => x.1.val.length = a.val.length ∧ x.2.1.val + x.2.2.val = n.val / 2)
    (fun x => (x.1.val.toArray, x.2.1.val))
    (fun _ s => (IntroSort.downHeap cmp s.1 lo.val s.2 n.val, s.2 - 1))
    (fun y s => y.val.toArray = s.1 ∧ y.val.length = a.val.length)
    (by
      rintro ⟨v, i, k⟩ ⟨hv, hik⟩ hk
      simp only at hv hik hk ⊢
      have hk' : k < h2 := by show k.val < h2.val; omega
      obtain ⟨w, hw, hwv, hwl⟩ := beatmap.dotnet.down_heap_refines cl hcl sc cmp hsc v lo i n (by omega) (by omega)
        (by omega) (by omega)
      obtain ⟨i2, hi2, hi2v⟩ := beatmap.dotnet.nat_sub_refines i 1#usize
      have hone : (1#usize : Usize).val = 1 := by decide
      obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := dns_usize_max; omega)
      refine ⟨(w, i2, k1), ?_, hk1v, ?_, ?_⟩
      · simp only [beatmap.dotnet.heap_sort_loop0.body, hh2, bind_ok, hk', if_true, hw, hi2, hk1]
      · simp only [hwv, hi2v, hone]
      · simp only; rw [hwl, hv]; constructor; rfl; rw [hi2v, hone, hk1v]; omega)
    (by
      rintro ⟨v, i, k⟩ ⟨hv, hik⟩ hk
      simp only at hv hik hk ⊢
      have hk' : ¬ k < h2 := by show ¬ k.val < h2.val; omega
      exact ⟨v, by simp only [beatmap.dotnet.heap_sort_loop0.body, hh2, bind_ok, hk', if_false], rfl, hv⟩)
    (a, h2, 0#usize) ⟨rfl, by simp [hh2v]⟩ (by simp)
  obtain ⟨n1, hn1, hn1v⟩ := beatmap.dotnet.nat_sub_refines n 1#usize
  have hone : (1#usize : Usize).val = 1 := by decide
  rw [hone] at hn1v
  obtain ⟨y2, hl2, hy2⟩ := loop_fold_gen
    (fun (x : alloc.vec.Vec T × Usize × Usize) => beatmap.dotnet.heap_sort_loop1.body cl sc lo n x.1 x.2.1 x.2.2)
    (·.2.2) (n.val - 1) (fun x => x.1.val.length = a.val.length ∧ x.2.1.val + x.2.2.val = n.val)
    (fun x => (x.1.val.toArray, x.2.1.val))
    (fun _ s => (IntroSort.downHeap cmp (IntroSort.swap s.1 lo.val (lo.val + s.2 - 1)) lo.val 1 (s.2 - 1), s.2 - 1))
    (fun y s => y.val.toArray = s.1 ∧ y.val.length = a.val.length)
    (by
      rintro ⟨v, k, k1⟩ ⟨hv, hkk⟩ hk
      simp only at hv hkk hk ⊢
      have hk' : k1 < n1 := by show k1.val < n1.val; omega
      obtain ⟨p, hp, hpv⟩ := dns_usize_add lo k (by omega)
      obtain ⟨p1, hp1, hp1v⟩ := dns_usize_sub1 p (by omega)
      obtain ⟨sw, hsw, hswv⟩ := beatmap.dotnet.swap_refines cl hcl v lo p1 (by omega) (by omega)
      have hswl : sw.val.length = v.val.length := by
        have := congrArg List.length hswv; simp [IntroSort.swap, dns_toList_set!] at this; omega
      obtain ⟨k2, hk2, hk2v⟩ := dns_usize_sub1 k (by omega)
      obtain ⟨w, hw, hwv, hwl⟩ := beatmap.dotnet.down_heap_refines cl hcl sc cmp hsc sw lo 1#usize k2 (by rw [hone])
        (by rw [hone]; omega) (by omega) (by omega)
      obtain ⟨k11, hk11, hk11v⟩ := usize_add_one k1 (by have := dns_usize_max; omega)
      refine ⟨(w, k2, k11), ?_, hk11v, ?_, ?_⟩
      · simp only [beatmap.dotnet.heap_sort_loop1.body, hn1, bind_ok, hk', if_true, hp, hp1, hsw, hk2, hw, hk11]
      · simp only [hwv, hk2v, hone]
        have e1 : (sw.val.toArray) = IntroSort.swap v.val.toArray lo.val (lo.val + k.val - 1) := by
          rw [show lo.val + k.val - 1 = p1.val by omega]; apply Array.ext'; simp [hswv]
        rw [e1]
      · simp only; rw [hwl, hswl, hv]; constructor; rfl; rw [hk2v, hk11v]; omega)
    (by
      rintro ⟨v, k, k1⟩ ⟨hv, hkk⟩ hk
      simp only at hv hkk hk ⊢
      have hk' : ¬ k1 < n1 := by show ¬ k1.val < n1.val; omega
      exact ⟨v, by simp only [beatmap.dotnet.heap_sort_loop1.body, hn1, bind_ok, hk', if_false], rfl, hv⟩)
    (y1, n, 0#usize) ⟨hy1.2, by simp⟩ (by simp)
  refine ⟨y2, ?_, ?_, hy2.2⟩
  · unfold beatmap.dotnet.heap_sort beatmap.dotnet.heap_sort_loop0 beatmap.dotnet.heap_sort_loop1
    simp only [hh2, bind_ok]
    rw [hl1]; simp only [bind_ok]; exact hl2
  · obtain ⟨e2, -⟩ := hy2
    obtain ⟨e1, -⟩ := hy1
    simp only [show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero, hh2v] at e1 e2
    rw [e2, dns_hs_spec, ← e1]


/-! ## stable merge sort (`stableSortBy`) -/

theorem dns_merge_nil_r {α : Type} (key : α → F64) (xs : List α) (f : Nat) :
    stableSortBy.merge key xs [] f = xs := by
  cases f <;> cases xs <;> simp [stableSortBy.merge]

theorem dns_merge_nil_l {α : Type} (key : α → F64) (ys : List α) (f : Nat) :
    stableSortBy.merge key [] ys f = ys := by
  cases f <;> simp [stableSortBy.merge]

theorem dns_merge_cons {α : Type} (key : α → F64) (x y : α) (xs ys : List α) (f : Nat) :
    stableSortBy.merge key (x :: xs) (y :: ys) (f + 1) =
      if compareF64 (key y) (key x) < 0 then y :: stableSortBy.merge key (x :: xs) ys f
      else x :: stableSortBy.merge key xs (y :: ys) f := by
  simp [stableSortBy.merge]

theorem dns_merge_length {α : Type} (key : α → F64) :
    ∀ (f : Nat) (xs ys : List α), (stableSortBy.merge key xs ys f).length = xs.length + ys.length := by
  intro f
  induction f with
  | zero => intro xs ys; simp [stableSortBy.merge]
  | succ f ih =>
    intro xs ys
    cases xs with
    | nil => simp [dns_merge_nil_l]
    | cons x xs =>
      cases ys with
      | nil => simp [dns_merge_nil_r]
      | cons y ys => rw [dns_merge_cons]; split <;> simp [ih] <;> omega

theorem dns_sort_length {α : Type} (key : α → F64) :
    ∀ (f : Nat) (l : List α), (stableSortBy.sort key l f).length = l.length := by
  intro f
  induction f with
  | zero => intro l; simp [stableSortBy.sort]
  | succ f ih =>
    intro l
    simp only [stableSortBy.sort]
    split
    · rfl
    · rw [dns_merge_length, ih, ih]; simp; omega

theorem dns_merge_fuel {α : Type} (key : α → F64) :
    ∀ (f g : Nat) (xs ys : List α), xs.length + ys.length ≤ f → xs.length + ys.length ≤ g →
      stableSortBy.merge key xs ys f = stableSortBy.merge key xs ys g := by
  intro f
  induction f with
  | zero =>
    intro g xs ys hf hg
    have : xs = [] := by apply List.eq_nil_of_length_eq_zero; omega
    have : ys = [] := by apply List.eq_nil_of_length_eq_zero; omega
    subst xs; subst ys; simp [dns_merge_nil_l]
  | succ f ih =>
    intro g xs ys hf hg
    cases xs with
    | nil => simp [dns_merge_nil_l]
    | cons x xs =>
      cases ys with
      | nil => simp [dns_merge_nil_r]
      | cons y ys =>
        obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by simp at hg; omega⟩
        rw [dns_merge_cons, dns_merge_cons]
        simp at hf hg
        split
        · rw [ih g' _ _ (by simp; omega) (by simp; omega)]
        · rw [ih g' _ _ (by simp; omega) (by simp; omega)]

theorem dns_sort_fuel {α : Type} (key : α → F64) :
    ∀ (f g : Nat) (l : List α), l.length + 1 ≤ f → l.length + 1 ≤ g →
      stableSortBy.sort key l f = stableSortBy.sort key l g := by
  intro f
  induction f with
  | zero => intro g l hf; omega
  | succ f ih =>
    intro g l hf hg
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    simp only [stableSortBy.sort]
    split
    · rfl
    · rename_i hl
      have h1 : (l.take (l.length / 2)).length + 1 ≤ f := by simp; omega
      have h2 : (l.drop (l.length / 2)).length + 1 ≤ f := by simp; omega
      rw [ih g' _ h1 (by simp; omega), ih g' _ h2 (by simp; omega)]


def dnsSl {α : Type} (l : List α) (lo hi : Nat) : List α := (l.drop lo).take (hi - lo)

theorem dnsSl_cons {α : Type} (l : List α) (lo hi : Nat) (h : lo < hi) (hl : lo < l.length) :
    dnsSl l lo hi = l[lo] :: dnsSl l (lo + 1) hi := by
  unfold dnsSl
  rw [List.drop_eq_getElem_cons hl, show hi - lo = (hi - (lo + 1)) + 1 by omega, List.take_succ_cons]

theorem dnsSl_nil {α : Type} (l : List α) (lo hi : Nat) (h : hi ≤ lo) : dnsSl l lo hi = [] := by
  unfold dnsSl; rw [show hi - lo = 0 by omega]; simp

theorem dnsSl_length {α : Type} (l : List α) (lo hi : Nat) (h : hi ≤ l.length) : (dnsSl l lo hi).length = hi - lo := by
  unfold dnsSl; simp; omega

theorem dns_merge_runs_loop {T : Type} (cl : core.clone.Clone T) (hcl : ∀ x, cl.clone x = ok x)
    (sk : beatmap.dotnet.SortKey T) (key : T → F64) (hsk : ∀ x, sk.sort_key x = ok (key x))
    (a : alloc.vec.Vec T) (mid hi : Usize) (hm : mid.val ≤ hi.val) (hh : hi.val ≤ a.val.length) (hN : a.val.length < 2^31) :
    ∀ (F : Nat) (out : alloc.vec.Vec T) (i j : Usize), i.val ≤ mid.val → mid.val ≤ j.val → j.val ≤ hi.val →
      F = (mid.val - i.val) + (hi.val - j.val) → out.val.length + F < 2^31 →
      ∃ r, beatmap.dotnet.merge_runs_loop cl sk a mid hi out i j = ok r ∧
        r.val = out.val ++ stableSortBy.merge key (dnsSl a.val i.val mid.val) (dnsSl a.val j.val hi.val) F := by
  intro F
  induction F with
  | zero =>
    intro out i j hi0 hj0 hj1 hF hlen
    have h1 : ¬ i < mid := by show ¬ i.val < mid.val; omega
    have h2 : ¬ j < hi := by show ¬ j.val < hi.val; omega
    refine ⟨out, ?_, ?_⟩
    · unfold beatmap.dotnet.merge_runs_loop; rw [loop_unfold]
      simp [beatmap.dotnet.merge_runs_loop.body, h1, h2]
    · rw [dnsSl_nil _ _ _ (by omega), dnsSl_nil _ _ _ (by omega)]; simp [stableSortBy.merge]
  | succ F ih =>
    intro out i j hi0 hj0 hj1 hF hlen
    have hmax : out.val.length < Usize.max := by have := dns_usize_max; omega
    by_cases hi' : i.val < mid.val
    · have hil : i.val < a.val.length := by omega
      have hil' : i < mid := hi'
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := dns_usize_max; omega)
      by_cases hj' : j.val < hi.val
      · have hjl : j.val < a.val.length := by omega
        have hjl' : j < hi := hj'
        obtain ⟨j1, hj1', hj1v⟩ := usize_add_one j (by have := dns_usize_max; omega)
        obtain ⟨c, hc, hcv⟩ := beatmap.dotnet.compare_f64_refines (key (a.val[j.val]'hjl)) (key (a.val[i.val]'hil))
        rw [dnsSl_cons _ _ _ hi' hil, dnsSl_cons _ _ _ hj' hjl, dns_merge_cons]
        by_cases hcn : c < 0#i32
        · have hcn' : compareF64 (key (a.val[j.val]'hjl)) (key (a.val[i.val]'hil)) < 0 := by rw [← hcv]; simpa using hcn
          obtain ⟨w, hw, hwv⟩ := push_eq out (a.val[j.val]'hjl) hmax
          obtain ⟨r, hr, hrv⟩ := ih w i j1 hi0 (by omega) (by omega) (by omega) (by rw [hwv]; simp; omega)
          refine ⟨r, ?_, ?_⟩
          · unfold beatmap.dotnet.merge_runs_loop; rw [loop_unfold]
            have hb : beatmap.dotnet.merge_runs_loop.body cl sk a mid hi out i j = ok (.cont (w, i, j1)) := by
              simp [beatmap.dotnet.merge_runs_loop.body, hil', hjl', vec_index_eq _ _ hil, vec_index_eq _ _ hjl,
                vec_index_usize_ok _ _ hil, vec_index_usize_ok _ _ hjl, hsk, hc, hcn, hcl, hw, hj1', show c.val < 0 by simpa using hcn]
            simp only [hb, bind_ok]; unfold beatmap.dotnet.merge_runs_loop at hr; exact hr
          · rw [hrv, hwv, if_pos hcn', hj1v, ← dnsSl_cons _ _ _ hi' hil]; simp
        · have hcn' : ¬ compareF64 (key (a.val[j.val]'hjl)) (key (a.val[i.val]'hil)) < 0 := by rw [← hcv]; simpa using hcn
          obtain ⟨w, hw, hwv⟩ := push_eq out (a.val[i.val]'hil) hmax
          obtain ⟨r, hr, hrv⟩ := ih w i1 j (by omega) hj0 hj1 (by omega) (by rw [hwv]; simp; omega)
          refine ⟨r, ?_, ?_⟩
          · unfold beatmap.dotnet.merge_runs_loop; rw [loop_unfold]
            have hb : beatmap.dotnet.merge_runs_loop.body cl sk a mid hi out i j = ok (.cont (w, i1, j)) := by
              simp [beatmap.dotnet.merge_runs_loop.body, hil', hjl', vec_index_eq _ _ hil, vec_index_eq _ _ hjl,
                vec_index_usize_ok _ _ hil, vec_index_usize_ok _ _ hjl, hsk, hc, hcn, hcl, hw, hi1, show ¬ c.val < 0 by simpa using hcn]
            simp only [hb, bind_ok]; unfold beatmap.dotnet.merge_runs_loop at hr; exact hr
          · rw [hrv, hwv, if_neg hcn', hi1v, ← dnsSl_cons _ _ _ hj' hjl]; simp
      · have hjl' : ¬ j < hi := hj'
        obtain ⟨w, hw, hwv⟩ := push_eq out (a.val[i.val]'hil) hmax
        obtain ⟨r, hr, hrv⟩ := ih w i1 j (by omega) hj0 hj1 (by omega) (by rw [hwv]; simp; omega)
        refine ⟨r, ?_, ?_⟩
        · unfold beatmap.dotnet.merge_runs_loop; rw [loop_unfold]
          have hb : beatmap.dotnet.merge_runs_loop.body cl sk a mid hi out i j = ok (.cont (w, i1, j)) := by
            simp [beatmap.dotnet.merge_runs_loop.body, hil', hjl', vec_index_eq _ _ hil, vec_index_usize_ok _ _ hil,
              hcl, hw, hi1]
          simp only [hb, bind_ok]; unfold beatmap.dotnet.merge_runs_loop at hr; exact hr
        · rw [hrv, hwv, dnsSl_cons _ _ _ hi' hil, dnsSl_nil a.val j.val hi.val (by omega), dns_merge_nil_r,
            dns_merge_nil_r, hi1v]; simp
    · have hil' : ¬ i < mid := hi'
      have hj' : j.val < hi.val := by omega
      have hjl : j.val < a.val.length := by omega
      have hjl' : j < hi := hj'
      obtain ⟨j1, hj1', hj1v⟩ := usize_add_one j (by have := dns_usize_max; omega)
      obtain ⟨w, hw, hwv⟩ := push_eq out (a.val[j.val]'hjl) hmax
      obtain ⟨r, hr, hrv⟩ := ih w i j1 hi0 (by omega) (by omega) (by omega) (by rw [hwv]; simp; omega)
      refine ⟨r, ?_, ?_⟩
      · unfold beatmap.dotnet.merge_runs_loop; rw [loop_unfold]
        have hb : beatmap.dotnet.merge_runs_loop.body cl sk a mid hi out i j = ok (.cont (w, i, j1)) := by
          simp [beatmap.dotnet.merge_runs_loop.body, hil', hjl', vec_index_eq _ _ hjl, vec_index_usize_ok _ _ hjl,
            hcl, hw, hj1']
        simp only [hb, bind_ok]; unfold beatmap.dotnet.merge_runs_loop at hr; exact hr
      · rw [hrv, hwv, dnsSl_nil a.val i.val mid.val (by omega), dns_merge_nil_l, dns_merge_nil_l,
          dnsSl_cons _ _ _ hj' hjl, hj1v]; simp


theorem dns_copy_step {α : Type} (a0 out : List α) (lo k : Nat) (hk : k < out.length) (hb : lo + k < a0.length) :
    (a0.take lo ++ out.take k ++ a0.drop (lo + k)).set (lo + k) (out[k]'hk) =
      a0.take lo ++ out.take (k + 1) ++ a0.drop (lo + k + 1) := by
  have h1 : (a0.take lo ++ out.take k).length = lo + k := by simp; omega
  rw [List.set_append_right _ _ (by omega), h1, Nat.sub_self, List.drop_eq_getElem_cons hb]
  simp only [List.set_cons_zero, List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, List.append_assoc]
  simp

theorem dns_msr_copy {T : Type} (cl : core.clone.Clone T) (hcl : ∀ x, cl.clone x = ok x)
    (a0 out : alloc.vec.Vec T) (lo n : Usize) (hn : out.val.length = n.val) (hb : lo.val + n.val ≤ a0.val.length)
    (hN : a0.val.length < 2^31) :
    ∀ (k : Usize) (a : alloc.vec.Vec T), k.val ≤ n.val →
      a.val = a0.val.take lo.val ++ out.val.take k.val ++ a0.val.drop (lo.val + k.val) →
      ∃ r, beatmap.dotnet.merge_sort_range_loop cl a lo n out k = ok r ∧
        r.val = a0.val.take lo.val ++ out.val ++ a0.val.drop (lo.val + n.val) := by
  intro k
  induction hk : n.val - k.val using Nat.strong_induction_on generalizing k with
  | _ m ih =>
    intro a hkn ha
    have hal : a.val.length = a0.val.length := by rw [ha]; simp; omega
    unfold beatmap.dotnet.merge_sort_range_loop
    rw [loop_unfold]
    by_cases hlt : k.val < n.val
    · have hkl : k.val < out.val.length := by omega
      obtain ⟨p, hp, hpv⟩ := dns_usize_add lo k (by omega)
      have hpl : p.val < a.val.length := by omega
      obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := dns_usize_max; omega)
      have hb' : beatmap.dotnet.merge_sort_range_loop.body cl lo n out a k =
          ok (.cont (alloc.vec.Vec.set a p (out.val[k.val]'hkl), k1)) := by
        simp [beatmap.dotnet.merge_sort_range_loop.body, show k < n from hlt, vec_index_eq _ _ hkl,
          vec_index_usize_ok _ _ hkl, hcl, hp, vec_index_mut_eq _ _ hpl, vec_index_mut_usize_ok _ _ hpl, hk1]
      obtain ⟨r, hr, hrv⟩ := ih (n.val - k1.val) (by omega) k1 rfl (alloc.vec.Vec.set a p (out.val[k.val]'hkl)) (by omega)
        (by rw [vec_set_val', ha, hk1v, hpv, dns_copy_step _ _ _ _ hkl (by omega), Nat.add_assoc])
      refine ⟨r, ?_, hrv⟩
      simp only [hb', bind_ok]; unfold beatmap.dotnet.merge_sort_range_loop at hr; exact hr
    · have hlt' : ¬ k < n := hlt
      refine ⟨a, by simp [beatmap.dotnet.merge_sort_range_loop.body, hlt'], ?_⟩
      rw [ha, show k.val = n.val by omega, List.take_of_length_le (l := out.val) (by omega)]


theorem dns_sl_mid {α : Type} (P X Q : List α) :
    ((P ++ X ++ Q).drop P.length).take ((P.length + X.length) - P.length) = X := by
  simp [List.drop_append]
theorem dns_take_pre {α : Type} (P X Q : List α) : (P ++ X ++ Q).take (P.length + X.length) = P ++ X := by
  simp [List.take_append]
theorem dns_drop_suf {α : Type} (P X Q : List α) (k : Nat) :
    (P ++ X ++ Q).drop (P.length + X.length + k) = Q.drop k := by
  rw [List.append_assoc, List.drop_append, List.drop_append]; simp [Nat.add_assoc]

theorem dns_slice_split {α : Type} (l : List α) (lo hi : Nat) (h1 : lo ≤ hi) (h2 : hi ≤ l.length) :
    l = l.take lo ++ dnsSl l lo hi ++ l.drop hi := by
  unfold dnsSl
  rw [List.append_assoc]
  conv_lhs => rw [← List.take_append_drop hi l]
  rw [show hi = lo + (hi - lo) by omega, List.take_add, List.append_assoc]
  congr 3 <;> omega

theorem dns_msr {T : Type} (cl : core.clone.Clone T) (hcl : ∀ x, cl.clone x = ok x)
    (sk : beatmap.dotnet.SortKey T) (key : T → F64) (hsk : ∀ x, sk.sort_key x = ok (key x)) :
    ∀ (m : Nat) (a : alloc.vec.Vec T) (lo hi : Usize), hi.val - lo.val = m → lo.val ≤ hi.val →
      hi.val ≤ a.val.length → a.val.length < 2^31 →
      ∃ r, beatmap.dotnet.merge_sort_range cl sk a lo hi = ok r ∧
        r.val = a.val.take lo.val ++ stableSortBy.sort key (dnsSl a.val lo.val hi.val) (hi.val - lo.val + 1) ++
          a.val.drop hi.val := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro a lo hi hm hlh hha hN
    obtain ⟨n, hn, hnv⟩ := eq_ok_of_spec (UScalar.sub_spec (x := hi) (y := lo) hlh)
    have hnv' : n.val = hi.val - lo.val := hnv.1
    rw [beatmap.dotnet.merge_sort_range]
    by_cases hn1 : n.val > 1
    · have hn1' : n > 1#usize := by show (1#usize : Usize).val < n.val; simpa using hn1
      obtain ⟨h, hh, hhv⟩ := dns_usize_div2 n
      obtain ⟨mid, hmid, hmidv⟩ := dns_usize_add lo h (by omega)
      obtain ⟨a1, ha1, ha1v⟩ := ih (mid.val - lo.val) (by omega) a lo mid rfl (by omega) (by omega) hN
      have hP : (a.val.take lo.val).length = lo.val := by simp; omega
      have hS1 : (stableSortBy.sort key (dnsSl a.val lo.val mid.val) (mid.val - lo.val + 1)).length = mid.val - lo.val := by
        rw [dns_sort_length, dnsSl_length _ _ _ (by omega)]
      have ha1l : a1.val.length = a.val.length := by rw [ha1v]; simp; omega
      obtain ⟨a2, ha2, ha2v⟩ := ih (hi.val - mid.val) (by omega) a1 mid hi rfl (by omega) (by omega) (by omega)
      generalize hS1d : stableSortBy.sort key (dnsSl a.val lo.val mid.val) (mid.val - lo.val + 1) = S1 at ha1v hS1
      have hmid' : mid.val = (a.val.take lo.val).length + S1.length := by rw [hP, hS1]; omega
      have f1 : dnsSl a1.val mid.val hi.val = dnsSl a.val mid.val hi.val := by
        unfold dnsSl; rw [ha1v, hmid', ← Nat.add_zero ((a.val.take lo.val).length + S1.length), dns_drop_suf]
        simp
      have f2 : a1.val.take mid.val = a.val.take lo.val ++ S1 := by rw [ha1v, hmid', dns_take_pre]
      have f3 : a1.val.drop hi.val = a.val.drop hi.val := by
        rw [ha1v, show hi.val = (a.val.take lo.val).length + S1.length + (hi.val - mid.val) by omega, dns_drop_suf]
        rw [List.drop_drop]; congr 1; omega
      rw [f1, f2, f3] at ha2v
      generalize hS2d : stableSortBy.sort key (dnsSl a.val mid.val hi.val) (hi.val - mid.val + 1) = S2 at ha2v
      have hS2 : S2.length = hi.val - mid.val := by rw [← hS2d, dns_sort_length, dnsSl_length _ _ _ hha]
      have ha2l : a2.val.length = a.val.length := by rw [ha2v]; simp; omega
      obtain ⟨out1, hout1, hout1v⟩ := dns_merge_runs_loop cl hcl sk key hsk a2 mid hi (by omega) (by omega) (by omega)
        ((mid.val - lo.val) + (hi.val - mid.val)) (alloc.vec.Vec.with_capacity T n) lo mid (by omega) le_rfl (by omega)
        rfl (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]; omega)
      have f4 : dnsSl a2.val lo.val mid.val = S1 := by
        have e := dns_sl_mid (a.val.take lo.val) S1 (S2 ++ a.val.drop hi.val)
        rw [hP, show lo.val + S1.length - lo.val = mid.val - lo.val by omega] at e
        unfold dnsSl; rw [ha2v]; simp only [List.append_assoc] at e ⊢; exact e
      have f5 : dnsSl a2.val mid.val hi.val = S2 := by
        have e := dns_sl_mid (a.val.take lo.val ++ S1) S2 (a.val.drop hi.val)
        rw [show (a.val.take lo.val ++ S1).length = mid.val by simp; omega,
          show mid.val + S2.length - mid.val = hi.val - mid.val by omega] at e
        unfold dnsSl; rw [ha2v]; exact e
      rw [f4, f5] at hout1v
      have hwc : (alloc.vec.Vec.with_capacity T n).val = [] := by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
      rw [hwc, List.nil_append] at hout1v
      have hol : out1.val.length = n.val := by rw [hout1v, dns_merge_length, hS1, hS2]; omega
      obtain ⟨r, hr, hrv⟩ := dns_msr_copy cl hcl a2 out1 lo n hol (by omega) (by omega) 0#usize a2 (by simp)
        (by simp)
      refine ⟨r, ?_, ?_⟩
      · simp only [hn, bind_ok, hn1', if_true, hh, hmid, ha1, ha2, beatmap.dotnet.merge_runs, hout1, hr]
      · rw [hrv]
        have t1 : a2.val.take lo.val = a.val.take lo.val := by
          rw [ha2v]; simp only [List.append_assoc]; rw [List.take_append_of_le_length (by omega)]; simp
        have t2 : a2.val.drop (lo.val + n.val) = a.val.drop hi.val := by
          rw [ha2v, show lo.val + n.val = (a.val.take lo.val ++ S1).length + S2.length + 0 by rw [List.length_append, hP, hS1, hS2]; omega, dns_drop_suf]
          simp
        rw [t1, t2, hout1v]
        congr 2
        have hL : (dnsSl a.val lo.val hi.val).length = n.val := by rw [dnsSl_length _ _ _ hha]; omega
        rw [show hi.val - lo.val + 1 = n.val + 1 by omega]
        simp only [stableSortBy.sort, hL, show ¬ n.val ≤ 1 by omega, if_false, decide_false]
        have e1 : (dnsSl a.val lo.val hi.val).take (n.val / 2) = dnsSl a.val lo.val mid.val := by
          unfold dnsSl; rw [List.take_take]; congr 1; omega
        have e2 : (dnsSl a.val lo.val hi.val).drop (n.val / 2) = dnsSl a.val mid.val hi.val := by
          unfold dnsSl; rw [List.drop_take, List.drop_drop, show lo.val + n.val / 2 = mid.val by omega, show hi.val - lo.val - n.val / 2 = hi.val - mid.val by omega]
        rw [e1, e2, ← hS1d, ← hS2d]
        have l1 : (dnsSl a.val lo.val mid.val).length = mid.val - lo.val := dnsSl_length _ _ _ (by omega)
        have l2 : (dnsSl a.val mid.val hi.val).length = hi.val - mid.val := dnsSl_length _ _ _ hha
        rw [dns_sort_fuel key (mid.val - lo.val + 1) n.val (dnsSl a.val lo.val mid.val) (by omega) (by omega),
          dns_sort_fuel key (hi.val - mid.val + 1) n.val (dnsSl a.val mid.val hi.val) (by omega) (by omega)]
        exact dns_merge_fuel key _ _ _ _ (by rw [dns_sort_length, dns_sort_length]; omega)
          (by rw [dns_sort_length, dns_sort_length]; omega)
    · have hn1' : ¬ n > 1#usize := by show ¬ (1#usize : Usize).val < n.val; simpa using hn1
      refine ⟨a, by simp only [hn, bind_ok, hn1', if_false], ?_⟩
      have hsl : (dnsSl a.val lo.val hi.val).length ≤ 1 := by rw [dnsSl_length _ _ _ hha]; omega
      simp only [stableSortBy.sort, hsl, decide_true, if_true]
      first | exact dns_slice_split a.val lo.val hi.val hlh hha | exact (dns_slice_split a.val lo.val hi.val hlh hha).symm


/-- merge of two sorted runs; spec `stableSortBy.merge` -/
theorem beatmap.dotnet.merge_runs_refines {T : Type} (cl : core.clone.Clone T) (hcl : ∀ x, cl.clone x = ok x)
    (sk : beatmap.dotnet.SortKey T) (key : T → F64) (hsk : ∀ x, sk.sort_key x = ok (key x))
    (a : alloc.vec.Vec T) (lo mid hi : Usize) (out : alloc.vec.Vec T) (h1 : lo.val ≤ mid.val) (h2 : mid.val ≤ hi.val)
    (hh : hi.val ≤ a.val.length) (hN : a.val.length < 2^31) (ho : out.val.length + (hi.val - lo.val) < 2^31) :
    ∃ r, beatmap.dotnet.merge_runs cl sk a lo mid hi out = ok r ∧
      r.val = out.val ++ stableSortBy.merge key (dnsSl a.val lo.val mid.val) (dnsSl a.val mid.val hi.val)
        (hi.val - lo.val) := by
  obtain ⟨r, hr, hrv⟩ := dns_merge_runs_loop cl hcl sk key hsk a mid hi h2 hh hN ((mid.val - lo.val) + (hi.val - mid.val))
    out lo mid h1 le_rfl h2 rfl (by omega)
  exact ⟨r, hr, by rw [hrv, show mid.val - lo.val + (hi.val - mid.val) = hi.val - lo.val by omega]⟩

/-- top-down merge sort of `a[lo..hi)`; spec `stableSortBy.sort` -/
theorem beatmap.dotnet.merge_sort_range_refines {T : Type} (cl : core.clone.Clone T) (hcl : ∀ x, cl.clone x = ok x)
    (sk : beatmap.dotnet.SortKey T) (key : T → F64) (hsk : ∀ x, sk.sort_key x = ok (key x))
    (a : alloc.vec.Vec T) (lo hi : Usize) (h1 : lo.val ≤ hi.val) (hh : hi.val ≤ a.val.length) (hN : a.val.length < 2^31) :
    ∃ r, beatmap.dotnet.merge_sort_range cl sk a lo hi = ok r ∧
      r.val = a.val.take lo.val ++ stableSortBy.sort key (dnsSl a.val lo.val hi.val) (hi.val - lo.val + 1) ++
        a.val.drop hi.val :=
  dns_msr cl hcl sk key hsk _ a lo hi rfl h1 hh hN

/-- LINQ `OrderBy` (stable); spec `stableSortBy` -/
theorem beatmap.dotnet.stable_sort_by_refines {T : Type} (cl : core.clone.Clone T) (hcl : ∀ x, cl.clone x = ok x)
    (sk : beatmap.dotnet.SortKey T) (key : T → F64) (hsk : ∀ x, sk.sort_key x = ok (key x))
    (a : alloc.vec.Vec T) (hN : a.val.length < 2^31) :
    ∃ r, beatmap.dotnet.stable_sort_by cl sk a = ok r ∧ r.val.toArray = stableSortBy key a.val.toArray := by
  obtain ⟨r, hr, hrv⟩ := dns_msr cl hcl sk key hsk _ a 0#usize (alloc.vec.Vec.len a) rfl (by simp) (by simp) hN
  refine ⟨r, by unfold beatmap.dotnet.stable_sort_by; exact hr, ?_⟩
  rw [hrv]; unfold stableSortBy dnsSl; simp

end OsuProofs
