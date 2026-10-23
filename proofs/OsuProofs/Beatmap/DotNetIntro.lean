/-
`beatmap::dotnet` introsort (`pick_pivot_and_partition`, `intro_sort`, `intro_sort_iter`, `list_sort`) refines
`IntroSort.*` / `listSort` (mods proof agent). No-panic of the partition's left scan rests on the pivot
being its own sentinel, so these take `hrefl : ∀ x, ¬ cmp x x < 0` (see DECISIONS).
-/
import OsuProofs.Beatmap.DotNetSort
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


def dppL {α : Type} [Inhabited α] (cmp : α → α → Int) (lo : Nat) (a : Array α) (pivot : α) (s : Nat × Bool) : Nat × Bool :=
  if s.2 = true then (if cmp a[lo + s.1]! pivot < 0 then (s.1 + 1, s.2) else (s.1, false)) else (s.1, s.2)

def dppR {α : Type} [Inhabited α] (cmp : α → α → Int) (lo : Nat) (a : Array α) (pivot : α) (s : Nat × Bool) : Nat × Bool :=
  if s.2 = true then (if cmp pivot a[lo + s.1]! < 0 then (s.1 - 1, s.2) else (s.1, false)) else (s.1, s.2)

def dppLs {α : Type} [Inhabited α] (cmp : α → α → Int) (lo len : Nat) (a : Array α) (pivot : α) (l : Nat) : Nat :=
  (iterR (fun _ t => .yield (dppL cmp lo a pivot t)) 0 len (l, true)).1

def dppRs {α : Type} [Inhabited α] (cmp : α → α → Int) (lo len : Nat) (a : Array α) (pivot : α) (r : Nat) : Nat :=
  (iterR (fun _ t => .yield (dppR cmp lo a pivot t)) 0 len (r, true)).1

def dppO {α : Type} [Inhabited α] (cmp : α → α → Int) (lo len : Nat) (pivot : α) (s : Array α × Nat × Nat) :
    Array α × Nat × Nat :=
  if s.2.1 < s.2.2 then
    if dppLs cmp lo len s.1 pivot (s.2.1 + 1) < dppRs cmp lo len s.1 pivot (s.2.2 - 1) then
      (IntroSort.swap s.1 (lo + dppLs cmp lo len s.1 pivot (s.2.1 + 1)) (lo + dppRs cmp lo len s.1 pivot (s.2.2 - 1)),
        dppLs cmp lo len s.1 pivot (s.2.1 + 1), dppRs cmp lo len s.1 pivot (s.2.2 - 1))
    else (s.1, dppLs cmp lo len s.1 pivot (s.2.1 + 1), dppRs cmp lo len s.1 pivot (s.2.2 - 1))
  else s

def dppA {α : Type} [Inhabited α] (cmp : α → α → Int) (a : Array α) (lo len : Nat) : Array α :=
  IntroSort.swapIfGreater cmp (IntroSort.swapIfGreater cmp (IntroSort.swapIfGreater cmp a lo (lo + (len - 1) / 2))
    lo (lo + (len - 1))) (lo + (len - 1) / 2) (lo + (len - 1))

theorem dpp_spec {α : Type} [Inhabited α] (cmp : α → α → Int) (a : Array α) (lo len : Nat) :
    IntroSort.pickPivotAndPartition cmp a lo len =
      (let pv := (dppA cmp a lo len)[lo + (len - 1) / 2]!
       let s := iterR (fun _ s => .yield (dppO cmp lo len pv s)) 0 (len + 1)
         (IntroSort.swap (dppA cmp a lo len) (lo + (len - 1) / 2) (lo + (len - 1) - 1), 0, len - 1 - 1)
       if (s.2.1 != len - 1 - 1) = true then (IntroSort.swap s.1 (lo + s.2.1) (lo + (len - 1) - 1), s.2.1)
       else (s.1, s.2.1)) := by
  unfold IntroSort.pickPivotAndPartition
  simp only [Id.run, forIn_range_iterR, Nat.sub_zero, id_bind_eq]
  rw [dns_iterR_ext _ (fun _ s => .yield (dppO cmp lo len (dppA cmp a lo len)[lo + (len - 1) / 2]! s)) ?h]
  · rfl
  intro j s
  rw [show IntroSort.swapIfGreater cmp (IntroSort.swapIfGreater cmp (IntroSort.swapIfGreater cmp a lo (lo + (len - 1) / 2))
    lo (lo + (len - 1))) (lo + (len - 1) / 2) (lo + (len - 1)) = dppA cmp a lo len from rfl]
  have eL : ∀ (arr : Array α) (pv : α) l, (iterR (fun _ (t : Nat × Bool) =>
      ((if t.2 = true then (if cmp arr[lo + t.1]! pv < 0 then pure (ForInStep.yield (t.1 + 1, t.2))
        else pure (ForInStep.yield (t.1, false))) else pure (ForInStep.yield (t.1, t.2))) : Id (ForInStep (Nat × Bool)))) 0 len (l, true)).1 =
      dppLs cmp lo len arr pv l := by
    intro arr pv l; unfold dppLs; congr 1; apply dns_iterR_ext; intro _ t; simp only [dppL]; split <;> (try split) <;> rfl
  have eR : ∀ (arr : Array α) (pv : α) r, (iterR (fun _ (t : Nat × Bool) =>
      ((if t.2 = true then (if cmp pv arr[lo + t.1]! < 0 then pure (ForInStep.yield (t.1 - 1, t.2))
        else pure (ForInStep.yield (t.1, false))) else pure (ForInStep.yield (t.1, t.2))) : Id (ForInStep (Nat × Bool)))) 0 len (r, true)).1 =
      dppRs cmp lo len arr pv r := by
    intro arr pv r; unfold dppRs; congr 1; apply dns_iterR_ext; intro _ t; simp only [dppR]; split <;> (try split) <;> rfl
  simp only [eL, eR, dppO]
  split_ifs <;> rfl



theorem dpp_scanL {T : Type} [Inhabited T] (sc : beatmap.dotnet.SortCmp T) (cmp : T → T → Int)
    (hsc : ∀ x y, ∃ r, sc.cmp3 x y = ok r ∧ r.val = cmp x y) (hrefl : ∀ x, ¬ cmp x x < 0)
    (a : alloc.vec.Vec T) (lo len : Usize) (pivot : T) (hb : lo.val + len.val ≤ a.val.length) (h2 : 2 ≤ len.val)
    (hN : a.val.length < 2^31) (hpv : a.val[lo.val + len.val - 2]'(by omega) = pivot) :
    ∀ (left : Usize) (go : Bool) (k2 : Usize), left.val ≤ len.val - 2 → k2.val ≤ len.val →
      ∃ y, beatmap.dotnet.pick_pivot_and_partition_loop0_loop0 sc a lo len pivot left go k2 = ok y ∧
        y.val = (iterR (fun _ t => .yield (dppL cmp lo.val a.val.toArray pivot t)) k2.val (len.val - k2.val)
          (left.val, go)).1 ∧ y.val ≤ len.val - 2 := by
  intro left go k2 hl hk
  obtain ⟨y, hy, hq⟩ := loop_fold_gen
    (fun (x : Usize × Bool × Usize) =>
      beatmap.dotnet.pick_pivot_and_partition_loop0_loop0.body sc a lo len pivot x.1 x.2.1 x.2.2)
    (·.2.2) len.val
    (fun x => x.1.val ≤ len.val - 2)
    (fun x => (x.1.val, x.2.1))
    (fun _ s => dppL cmp lo.val a.val.toArray pivot s)
    (fun y s => y.val = s.1 ∧ y.val ≤ len.val - 2)
    (by
      rintro ⟨l, g, k⟩ hI hk
      simp only at hI hk ⊢
      obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := dns_usize_max; omega)
      have hkl : k < len := hk
      cases g
      · refine ⟨(l, false, k1), ?_, hk1v, ?_, hI⟩
        · simp [beatmap.dotnet.pick_pivot_and_partition_loop0_loop0.body, hkl, hk1, uncurry_apply_pair]
        · simp [dppL]
      · obtain ⟨p, hp, hpv'⟩ := dns_usize_add lo l (by omega)
        have hpl : p.val < a.val.length := by omega
        obtain ⟨c, hc, hcv⟩ := hsc (a.val[p.val]'hpl) pivot
        have hget : a.val.toArray[lo.val + l.val]! = a.val[p.val]'hpl := by
          rw [getElem!_pos _ _ (by simp; omega)]; simp; congr 1; omega
        by_cases hcn : c < 0#i32
        all_goals have hcn' : (c.val < 0) ↔ (c < 0#i32) := by simp
        · have hcv' : cmp (a.val[p.val]'hpl) pivot < 0 := by rw [← hcv]; simpa using hcn
          have hlt : l.val < len.val - 2 := by
            by_contra hne
            have he : p.val = lo.val + len.val - 2 := by omega
            have : a.val[p.val]'hpl = pivot := by rw [← hpv]; congr 1
            rw [this] at hcv'; exact hrefl _ hcv'
          obtain ⟨l1, hl1, hl1v⟩ := usize_add_one l (by have := dns_usize_max; omega)
          refine ⟨(l1, true, k1), ?_, hk1v, ?_, by simp only; omega⟩
          · simp [beatmap.dotnet.pick_pivot_and_partition_loop0_loop0.body, hkl, hk1, uncurry_apply_pair, hp,
              vec_index_eq _ _ hpl, vec_index_usize_ok _ _ hpl, hc, hcn, hcn', hl1]
          · simp only [dppL, if_true, hget, hcv', hl1v]
        · have hcv' : ¬ cmp (a.val[p.val]'hpl) pivot < 0 := by rw [← hcv]; simpa using hcn
          refine ⟨(l, false, k1), ?_, hk1v, ?_, hI⟩
          · simp [beatmap.dotnet.pick_pivot_and_partition_loop0_loop0.body, hkl, hk1, uncurry_apply_pair, hp,
              vec_index_eq _ _ hpl, vec_index_usize_ok _ _ hpl, hc, hcn, hcn']
          · simp only [dppL, if_true, hget, hcv', if_false])
    (by
      rintro ⟨l, g, k⟩ hI hk
      simp only at hI hk ⊢
      have hkl : ¬ k < len := by show ¬ k.val < len.val; omega
      exact ⟨l, by simp [beatmap.dotnet.pick_pivot_and_partition_loop0_loop0.body, hkl], rfl, hI⟩)
    (left, go, k2) hl hk
  exact ⟨y, by unfold beatmap.dotnet.pick_pivot_and_partition_loop0_loop0; exact hy, hq⟩

theorem dpp_scanR {T : Type} [Inhabited T] (sc : beatmap.dotnet.SortCmp T) (cmp : T → T → Int)
    (hsc : ∀ x y, ∃ r, sc.cmp3 x y = ok r ∧ r.val = cmp x y)
    (a : alloc.vec.Vec T) (lo len : Usize) (pivot : T) (hb : lo.val + len.val ≤ a.val.length)
    (hN : a.val.length < 2^31) (r0 : Nat) (hr0 : r0 < len.val) :
    ∀ (right : Usize) (go : Bool) (k3 : Usize), right.val ≤ r0 → k3.val ≤ len.val →
      ∃ y, beatmap.dotnet.pick_pivot_and_partition_loop0_loop1 sc a lo len pivot right go k3 = ok y ∧
        y.val = (iterR (fun _ t => .yield (dppR cmp lo.val a.val.toArray pivot t)) k3.val (len.val - k3.val)
          (right.val, go)).1 ∧ y.val ≤ r0 := by
  intro right go k3 hr hk
  obtain ⟨y, hy, hq⟩ := loop_fold_gen
    (fun (x : Usize × Bool × Usize) =>
      beatmap.dotnet.pick_pivot_and_partition_loop0_loop1.body sc a lo len pivot x.1 x.2.1 x.2.2)
    (·.2.2) len.val
    (fun x => x.1.val ≤ r0)
    (fun x => (x.1.val, x.2.1))
    (fun _ s => dppR cmp lo.val a.val.toArray pivot s)
    (fun y s => y.val = s.1 ∧ y.val ≤ r0)
    (by
      rintro ⟨l, g, k⟩ hI hk
      simp only at hI hk ⊢
      obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := dns_usize_max; omega)
      have hkl : k < len := hk
      cases g
      · refine ⟨(l, false, k1), ?_, hk1v, ?_, hI⟩
        · simp [beatmap.dotnet.pick_pivot_and_partition_loop0_loop1.body, hkl, hk1, uncurry_apply_pair]
        · simp [dppR]
      · obtain ⟨p, hp, hpv'⟩ := dns_usize_add lo l (by omega)
        have hpl : p.val < a.val.length := by omega
        obtain ⟨c, hc, hcv⟩ := hsc pivot (a.val[p.val]'hpl)
        have hget : a.val.toArray[lo.val + l.val]! = a.val[p.val]'hpl := by
          rw [getElem!_pos _ _ (by simp; omega)]; simp; congr 1; omega
        by_cases hcn : c < 0#i32
        all_goals have hcn' : (c.val < 0) ↔ (c < 0#i32) := by simp
        · have hcv' : cmp pivot (a.val[p.val]'hpl) < 0 := by rw [← hcv]; simpa using hcn
          obtain ⟨l1, hl1, hl1v⟩ := beatmap.dotnet.nat_sub_refines l 1#usize
          refine ⟨(l1, true, k1), ?_, hk1v, ?_, by simp only; rw [hl1v]; simp; omega⟩
          · simp [beatmap.dotnet.pick_pivot_and_partition_loop0_loop1.body, hkl, hk1, uncurry_apply_pair, hp,
              vec_index_eq _ _ hpl, vec_index_usize_ok _ _ hpl, hc, hcn, hcn', hl1]
          · simp only [dppR, if_true, hget, hcv', hl1v]; simp
        · have hcv' : ¬ cmp pivot (a.val[p.val]'hpl) < 0 := by rw [← hcv]; simpa using hcn
          refine ⟨(l, false, k1), ?_, hk1v, ?_, hI⟩
          · simp [beatmap.dotnet.pick_pivot_and_partition_loop0_loop1.body, hkl, hk1, uncurry_apply_pair, hp,
              vec_index_eq _ _ hpl, vec_index_usize_ok _ _ hpl, hc, hcn, hcn']
          · simp only [dppR, if_true, hget, hcv', if_false])
    (by
      rintro ⟨l, g, k⟩ hI hk
      simp only at hI hk ⊢
      have hkl : ¬ k < len := by show ¬ k.val < len.val; omega
      exact ⟨l, by simp [beatmap.dotnet.pick_pivot_and_partition_loop0_loop1.body, hkl], rfl, hI⟩)
    (right, go, k3) hr hk
  exact ⟨y, by unfold beatmap.dotnet.pick_pivot_and_partition_loop0_loop1; exact hy, hq⟩



theorem dpp_swap_size {α : Type} [Inhabited α] (A : Array α) (i j : Nat) : (IntroSort.swap A i j).size = A.size := by
  simp [IntroSort.swap]

theorem dpp_swap_get_j {α : Type} [Inhabited α] (A : Array α) (i j : Nat) (hi : i < A.size) (hj : j < A.size) :
    (IntroSort.swap A i j)[j]! = A[i]! := by
  simp [IntroSort.swap, getElem!_pos, hi, hj, Array.getElem_setIfInBounds]

theorem dpp_swap_get_ne {α : Type} [Inhabited α] (A : Array α) (i j m : Nat) (hi : m ≠ i) (hj : m ≠ j) :
    (IntroSort.swap A i j)[m]! = A[m]! := by
  by_cases hm : m < A.size
  · unfold IntroSort.swap
    simp [getElem!_pos, hm, Array.getElem_setIfInBounds, Ne.symm hi, Ne.symm hj]
  · have h2 : ¬ m < (IntroSort.swap A i j).size := by rw [dpp_swap_size]; exact hm
    rw [getElem!_neg (IntroSort.swap A i j) m h2, getElem!_neg A m hm]



theorem dpp_outer {T : Type} [Inhabited T] (cl : core.clone.Clone T) (hcl : ∀ x, cl.clone x = ok x)
    (sc : beatmap.dotnet.SortCmp T) (cmp : T → T → Int)
    (hsc : ∀ x y, ∃ r, sc.cmp3 x y = ok r ∧ r.val = cmp x y) (hrefl : ∀ x, ¬ cmp x x < 0)
    (lo len : Usize) (pivot : T) (N : Nat) (hb : lo.val + len.val ≤ N) (h3 : 3 ≤ len.val) (hN : N < 2^31) :
    ∀ (a : alloc.vec.Vec T) (left right k : Usize), a.val.length = N → a.val.toArray[lo.val + len.val - 2]! = pivot →
      left.val ≤ len.val - 2 → right.val ≤ len.val - 2 → k.val ≤ len.val + 1 →
      ∃ y, beatmap.dotnet.pick_pivot_and_partition_loop0 cl sc a lo len pivot left right k = ok y ∧
        y.1.val.toArray = (iterR (fun _ s => .yield (dppO cmp lo.val len.val pivot s)) k.val (len.val + 1 - k.val)
          (a.val.toArray, left.val, right.val)).1 ∧
        y.2.val = (iterR (fun _ s => .yield (dppO cmp lo.val len.val pivot s)) k.val (len.val + 1 - k.val)
          (a.val.toArray, left.val, right.val)).2.1 ∧
        y.1.val.length = N ∧ y.2.val ≤ len.val - 2 := by
  intro a left right k ha hs hl hr hk
  obtain ⟨n1, hn1, hn1v⟩ := usize_add_one len (by have := dns_usize_max; omega)
  obtain ⟨y, hy, hq⟩ := loop_fold_gen
    (fun (x : alloc.vec.Vec T × Usize × Usize × Usize) =>
      beatmap.dotnet.pick_pivot_and_partition_loop0.body cl sc lo len pivot x.1 x.2.1 x.2.2.1 x.2.2.2)
    (·.2.2.2) (len.val + 1)
    (fun x => x.1.val.length = N ∧ x.1.val.toArray[lo.val + len.val - 2]! = pivot ∧ x.2.1.val ≤ len.val - 2 ∧
      x.2.2.1.val ≤ len.val - 2)
    (fun x => (x.1.val.toArray, x.2.1.val, x.2.2.1.val))
    (fun _ s => dppO cmp lo.val len.val pivot s)
    (fun y s => y.1.val.toArray = s.1 ∧ y.2.val = s.2.1 ∧ y.1.val.length = N ∧ y.2.val ≤ len.val - 2)
    (by
      rintro ⟨a, l, r, k⟩ ⟨ha, hs, hl, hr⟩ hk
      simp only at ha hs hl hr hk ⊢
      obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := dns_usize_max; omega)
      have hkl : k < n1 := by show k.val < n1.val; omega
      by_cases hlr : l.val < r.val
      · have hlr' : l < r := hlr
        obtain ⟨l1, hl1, hl1v⟩ := usize_add_one l (by have := dns_usize_max; omega)
        have hpv : a.val[lo.val + len.val - 2]'(by omega) = pivot := by
          rw [← hs, getElem!_pos _ _ (by simp; omega)]; simp
        obtain ⟨l2, hl2, hl2e, hl2b⟩ := dpp_scanL sc cmp hsc hrefl a lo len pivot (by omega) (by omega) (by omega) hpv
          l1 true 0#usize (by omega) (by simp)
        obtain ⟨r1, hr1, hr1v⟩ := beatmap.dotnet.nat_sub_refines r 1#usize
        simp only [show ((1#usize : Usize).val) = 1 from rfl] at hr1v
        obtain ⟨r2, hr2, hr2e, hr2b⟩ := dpp_scanR sc cmp hsc a lo len pivot (by omega) (by omega) (r.val - 1) (by omega)
          r1 true 0#usize (by omega) (by simp)
        have eL : l2.val = dppLs cmp lo.val len.val a.val.toArray pivot (l.val + 1) := by
          rw [hl2e, ← hl1v]; simp [dppLs]
        have eR : r2.val = dppRs cmp lo.val len.val a.val.toArray pivot (r.val - 1) := by
          rw [hr2e, hr1v]; simp [dppRs]
        have hO : dppO cmp lo.val len.val pivot (a.val.toArray, l.val, r.val) =
            (if l2.val < r2.val then (IntroSort.swap a.val.toArray (lo.val + l2.val) (lo.val + r2.val), l2.val, r2.val)
             else (a.val.toArray, l2.val, r2.val)) := by
          simp only [dppO, hlr, if_true, ← eL, ← eR]
        by_cases h22 : l2.val < r2.val
        · have h22' : l2 < r2 := h22
          obtain ⟨p, hp, hpv'⟩ := dns_usize_add lo l2 (by omega)
          obtain ⟨q, hq, hqv⟩ := dns_usize_add lo r2 (by omega)
          obtain ⟨w, hw, hwv⟩ := beatmap.dotnet.swap_refines cl hcl a p q (by omega) (by omega)
          refine ⟨(w, l2, r2, k1), ?_, hk1v, ?_, ?_⟩
          · simp only [beatmap.dotnet.pick_pivot_and_partition_loop0.body, hn1, bind_ok, hkl, if_true, hlr', hl1, hl2,
              hr1, hr2, h22', hp, hq, hw, hk1]
          · rw [hO, if_pos h22]; simp [hwv, hpv', hqv]
          · refine ⟨by rw [hwv]; simp [dpp_swap_size, ha], ?_, hl2b, by simp only; omega⟩
            have hne1 : lo.val + len.val - 2 ≠ lo.val + l2.val := by omega
            have hne2 : lo.val + len.val - 2 ≠ lo.val + r2.val := by omega
            simp only [hwv, Array.toArray_toList, hpv', hqv]
            rw [dpp_swap_get_ne _ _ _ _ hne1 hne2]; exact hs
        · have h22' : ¬ l2 < r2 := h22
          refine ⟨(a, l2, r2, k1), ?_, hk1v, ?_, ha, hs, hl2b, by simp only; omega⟩
          · simp only [beatmap.dotnet.pick_pivot_and_partition_loop0.body, hn1, bind_ok, hkl, if_true, hlr', hl1, hl2,
              hr1, hr2, h22', if_false, hk1]
          · rw [hO, if_neg h22]
      · have hlr' : ¬ l < r := hlr
        refine ⟨(a, l, r, k1), ?_, hk1v, ?_, ha, hs, hl, hr⟩
        · simp only [beatmap.dotnet.pick_pivot_and_partition_loop0.body, hn1, bind_ok, hkl, if_true, hlr', if_false, hk1]
        · simp only [dppO, hlr, if_false])
    (by
      rintro ⟨a, l, r, k⟩ ⟨ha, hs, hl, hr⟩ hk
      simp only at ha hs hl hr hk ⊢
      have hkl : ¬ k < n1 := by show ¬ k.val < n1.val; omega
      exact ⟨(a, l), by simp only [beatmap.dotnet.pick_pivot_and_partition_loop0.body, hn1, bind_ok, hkl, if_false],
        rfl, rfl, ha, hl⟩)
    (a, left, right, k) ⟨ha, hs, hl, hr⟩ hk
  obtain ⟨h1, h2, h3, h4⟩ := hq
  exact ⟨y, by unfold beatmap.dotnet.pick_pivot_and_partition_loop0; exact hy, h1, h2, h3, h4⟩



theorem dpp_sig_size {α : Type} [Inhabited α] (cmp : α → α → Int) (A : Array α) (i j : Nat) :
    (IntroSort.swapIfGreater cmp A i j).size = A.size := by
  unfold IntroSort.swapIfGreater; split
  · exact dpp_swap_size _ _ _
  · rfl

/-- `PickPivotAndPartition(keys[lo..lo+len))` (needs `cmp x x ≥ 0`: the pivot is the left scan's sentinel) -/
theorem beatmap.dotnet.pick_pivot_and_partition_refines {T : Type} [Inhabited T] (cl : core.clone.Clone T)
    (hcl : ∀ x, cl.clone x = ok x) (sc : beatmap.dotnet.SortCmp T) (cmp : T → T → Int)
    (hsc : ∀ x y, ∃ r, sc.cmp3 x y = ok r ∧ r.val = cmp x y) (hrefl : ∀ x, ¬ cmp x x < 0)
    (a : alloc.vec.Vec T) (lo len : Usize) (hb : lo.val + len.val ≤ a.val.length) (h3 : 3 ≤ len.val)
    (hN : a.val.length < 2^31) :
    ∃ p r, beatmap.dotnet.pick_pivot_and_partition cl sc a lo len = ok (p, r) ∧
      r.val.toArray = (IntroSort.pickPivotAndPartition cmp a.val.toArray lo.val len.val).1 ∧
      p.val = (IntroSort.pickPivotAndPartition cmp a.val.toArray lo.val len.val).2 ∧
      r.val.length = a.val.length ∧ p.val ≤ len.val - 2 := by
  have e1 : ((1#usize : Usize).val) = 1 := rfl
  obtain ⟨hi, hhi, hhiv⟩ := beatmap.dotnet.nat_sub_refines len 1#usize
  rw [e1] at hhiv
  obtain ⟨mid, hmid, hmidv⟩ := dns_usize_div2 hi
  obtain ⟨i, hi', hiv⟩ := dns_usize_add lo mid (by omega)
  obtain ⟨a1, ha1, ha1v⟩ := beatmap.dotnet.swap_if_greater_refines cl hcl sc cmp hsc a lo i (by omega) (by omega)
  have ha1l : a1.val.length = a.val.length := by
    have := congrArg List.length ha1v; simp [dpp_sig_size] at this; exact this
  obtain ⟨i1, hi1, hi1v⟩ := dns_usize_add lo hi (by omega)
  obtain ⟨a2, ha2, ha2v⟩ := beatmap.dotnet.swap_if_greater_refines cl hcl sc cmp hsc a1 lo i1 (by omega) (by omega)
  have ha2l : a2.val.length = a.val.length := by
    have := congrArg List.length ha2v; simp [dpp_sig_size] at this; omega
  obtain ⟨a3, ha3, ha3v⟩ := beatmap.dotnet.swap_if_greater_refines cl hcl sc cmp hsc a2 i i1 (by omega) (by omega)
  have ha3l : a3.val.length = a.val.length := by
    have := congrArg List.length ha3v; simp [dpp_sig_size] at this; omega
  have hA3 : a3.val.toArray = dppA cmp a.val.toArray lo.val len.val := by
    rw [ha3v, ha2v, ha1v]; simp only [Array.toArray_toList]; simp only [dppA, hiv, hmidv, hhiv, hi1v]
  have hil : i.val < a3.val.length := by omega
  have hpiv : a3.val[i.val]'hil = (dppA cmp a.val.toArray lo.val len.val)[lo.val + (len.val - 1) / 2]! := by
    rw [← hA3, getElem!_pos _ _ (by simp; omega)]; simp [hiv, hmidv, hhiv]
  obtain ⟨i2, hi2, hi2v⟩ := beatmap.dotnet.nat_sub_refines i1 1#usize
  rw [e1] at hi2v
  obtain ⟨a4, ha4, ha4v⟩ := beatmap.dotnet.swap_refines cl hcl a3 i i2 hil (by omega)
  have ha4l : a4.val.length = a.val.length := by
    have := congrArg List.length ha4v; simp [dpp_swap_size] at this; omega
  have hA4 : a4.val.toArray = IntroSort.swap (dppA cmp a.val.toArray lo.val len.val) (lo.val + (len.val - 1) / 2)
      (lo.val + (len.val - 1) - 1) := by
    rw [ha4v, Array.toArray_toList, hA3, hiv, hi2v, hi1v, hmidv, hhiv]
  obtain ⟨rt, hrt, hrtv⟩ := beatmap.dotnet.nat_sub_refines hi 1#usize
  rw [e1] at hrtv
  have hsent : a4.val.toArray[lo.val + len.val - 2]! = (dppA cmp a.val.toArray lo.val len.val)[lo.val + (len.val - 1) / 2]! := by
    rw [hA4, show lo.val + len.val - 2 = lo.val + (len.val - 1) - 1 by omega, dpp_swap_get_j]
    · simp [dppA, dpp_sig_size]; omega
    · simp [dppA, dpp_sig_size]; omega
  obtain ⟨y, hy, hy1, hy2, hy3, hy4⟩ := dpp_outer cl hcl sc cmp hsc hrefl lo len
    ((dppA cmp a.val.toArray lo.val len.val)[lo.val + (len.val - 1) / 2]!) a.val.length hb h3 hN
    a4 0#usize rt 0#usize ha4l hsent (by simp) (by omega) (by simp)
  obtain ⟨a5, left⟩ := y
  simp only at hy hy1 hy2 hy3 hy4
  rw [hA4, hrtv, hhiv] at hy1 hy2
  simp only [show ((0#usize : Usize).val) = 0 from rfl, Nat.sub_zero] at hy1 hy2
  have hpp := dpp_spec cmp a.val.toArray lo.val len.val
  obtain ⟨i3, hi3, hi3v⟩ := beatmap.dotnet.nat_sub_refines hi 1#usize
  rw [e1] at hi3v
  have hbody : ∀ (res : Usize × alloc.vec.Vec T), (do
      let i3 ← beatmap.dotnet.nat_sub hi 1#usize
      if (left != i3) = true then
        do
        let i4 ← lo + left
        let i5 ← lo + hi
        let i6 ← beatmap.dotnet.nat_sub i5 1#usize
        let a6 ← beatmap.dotnet.swap cl a5 i4 i6
        ok (left, a6)
      else ok (left, a5)) = ok res → beatmap.dotnet.pick_pivot_and_partition cl sc a lo len = ok res := by
    intro res h
    unfold beatmap.dotnet.pick_pivot_and_partition
    simp only [hhi, bind_ok, hmid, hi', ha1, hi1, ha2, ha3, vec_index_eq _ _ hil, hpiv, hcl, hi2, ha4, hrt, hy,
      uncurry_apply_pair]
    simpa only [hrt, hi1, hi2, bind_ok] using h
  by_cases hne : left.val = len.val - 1 - 1
  · have hne' : (left != i3) = false := by
      simp only [bne_eq_false_iff_eq]; apply UScalar.eq_of_val_eq; rw [hi3v, hhiv]; exact hne
    refine ⟨left, a5, hbody _ (by simp only [hi3, bind_ok, hne', Bool.false_eq_true, if_false]), ?_, ?_, hy3, hy4⟩
    · rw [hpp]; simp only [hy1, ← hy2, hne]; simp
    · rw [hpp]; simp only [← hy2, hne]; simp
  · have hne' : (left != i3) = true := by
      simp only [bne_iff_ne, ne_eq]; intro h; apply hne; rw [h, hi3v, hhiv]
    obtain ⟨i4, hi4, hi4v⟩ := dns_usize_add lo left (by omega)
    obtain ⟨i6, hi6, hi6v⟩ := beatmap.dotnet.nat_sub_refines i1 1#usize
    rw [e1] at hi6v
    obtain ⟨a6, ha6, ha6v⟩ := beatmap.dotnet.swap_refines cl hcl a5 i4 i6 (by omega) (by omega)
    refine ⟨left, a6, hbody _ (by simp only [hi3, bind_ok, hne', if_true, hi4, hi1, hi6, ha6]), ?_, ?_, ?_, hy4⟩
    · rw [hpp]; simp only [← hy2, hne]; simp only [bne_iff_ne, ne_eq, hne, not_false_eq_true, if_true]
      rw [ha6v, Array.toArray_toList, hy1, hi4v, hi6v, hi1v, hy2, hhiv]
    · rw [hpp]; simp only [← hy2]; simp [hne]
    · rw [ha6v]; simp [dpp_swap_size, hy3]



def disF {α : Type} [Inhabited α] (cmp : α → α → Int) (lo F : Nat) (_ : Nat)
    (s : Option (Array α) × Array α × Nat × Nat) : ForInStep (Option (Array α) × Array α × Nat × Nat) :=
  if s.2.2.1 > 1 then
    if s.2.2.1 ≤ 16 then
      if (s.2.2.1 == 2) = true then
        .done (some (IntroSort.swapIfGreater cmp s.2.1 lo (lo + 1)), s.2.1, s.2.2.1, s.2.2.2)
      else if (s.2.2.1 == 3) = true then
        .done (some (IntroSort.swapIfGreater cmp (IntroSort.swapIfGreater cmp (IntroSort.swapIfGreater cmp s.2.1 lo (lo + 1)) lo
            (lo + 2)) (lo + 1) (lo + 2)),
          IntroSort.swapIfGreater cmp (IntroSort.swapIfGreater cmp s.2.1 lo (lo + 1)) lo (lo + 2), s.2.2.1, s.2.2.2)
      else .done (some (IntroSort.insertionSort cmp s.2.1 lo s.2.2.1), s.2.1, s.2.2.1, s.2.2.2)
    else if (s.2.2.2 == 0) = true then
      .done (some (IntroSort.heapSort cmp s.2.1 lo s.2.2.1), s.2.1, s.2.2.1, s.2.2.2)
    else .yield (none,
      IntroSort.introSort cmp (IntroSort.pickPivotAndPartition cmp s.2.1 lo s.2.2.1).1
        (lo + (IntroSort.pickPivotAndPartition cmp s.2.1 lo s.2.2.1).2 + 1)
        (s.2.2.1 - ((IntroSort.pickPivotAndPartition cmp s.2.1 lo s.2.2.1).2 + 1)) (s.2.2.2 - 1) F,
      (IntroSort.pickPivotAndPartition cmp s.2.1 lo s.2.2.1).2, s.2.2.2 - 1)
  else .yield (none, s.2.1, s.2.2.1, s.2.2.2)

def disRes {α : Type} (s : Option (Array α) × Array α × Nat × Nat) : Array α :=
  match s.1 with | some r => r | none => s.2.1

theorem dis_spec {α : Type} [Inhabited α] (cmp : α → α → Int) (a : Array α) (lo len d F : Nat) :
    IntroSort.introSort cmp a lo len d (F + 1) = disRes (iterR (disF cmp lo F) 0 (len + 1) (none, a, len, d)) := by
  rw [IntroSort.introSort]
  simp only [Id.run, forIn_range_iterR, Nat.sub_zero, id_bind_eq]
  rw [dns_iterR_ext _ (disF cmp lo F) ?h]
  · unfold disRes
    cases iterR (disF cmp lo F) 0 (len + 1) (none, a, len, d) with
    | mk o p => cases o <;> rfl
  intro j s
  simp only [disF]
  split_ifs <;> rfl

theorem dis_small {α : Type} [Inhabited α] (cmp : α → α → Int) (lo F : Nat) (A : Array α) (ps d : Nat) (h : ps ≤ 1) :
    ∀ k j, iterR (disF cmp lo F) j k (none, A, ps, d) = (none, A, ps, d) := by
  intro k
  induction k with
  | zero => intro j; rfl
  | succ k ih =>
    intro j
    have : disF cmp lo F j (none, A, ps, d) = .yield (none, A, ps, d) := by
      simp only [disF]; rw [if_neg (by omega)]
    simp only [iterR, this]; exact ih _



theorem dis_main {T : Type} [Inhabited T] (cl : core.clone.Clone T) (hcl : ∀ x, cl.clone x = ok x)
    (sc : beatmap.dotnet.SortCmp T) (cmp : T → T → Int)
    (hsc : ∀ x y, ∃ r, sc.cmp3 x y = ok r ∧ r.val = cmp x y) (hrefl : ∀ x, ¬ cmp x x < 0)
    (N : Nat) (hN : N < 2^31) :
    ∀ (F : Nat) (a : alloc.vec.Vec T) (lo len d fuel : Usize), fuel.val = F → a.val.length = N → lo.val + len.val ≤ N →
      ∃ r, beatmap.dotnet.intro_sort cl sc a lo len d fuel = ok r ∧
        r.val.toArray = IntroSort.introSort cmp a.val.toArray lo.val len.val d.val F ∧ r.val.length = N := by
  intro F
  induction F with
  | zero =>
    intro a lo len d fuel hf ha hb
    have : fuel = 0#usize := UScalar.eq_of_val_eq (by rw [hf]; rfl)
    subst this
    refine ⟨a, by unfold beatmap.dotnet.intro_sort; simp, by simp [IntroSort.introSort], ha⟩
  | succ F ih =>
    intro a lo len d fuel hf ha hb
    have hf0 : fuel ≠ 0#usize := by intro h; rw [h] at hf; simp at hf
    have iter : ∀ (steps : Nat) (j : Nat) (sV : Usize) (a : alloc.vec.Vec T) (ps depth : Usize), sV.val = steps →
        a.val.length = N → lo.val + ps.val ≤ N →
        ∃ r, beatmap.dotnet.intro_sort_iter cl sc a lo ps depth sV fuel = ok r ∧
          r.val.toArray = disRes (iterR (disF cmp lo.val F) j steps (none, a.val.toArray, ps.val, depth.val)) ∧
          r.val.length = N := by
      intro steps
      induction steps with
      | zero =>
        intro j sV a ps depth hs ha hb
        have : sV = 0#usize := UScalar.eq_of_val_eq (by rw [hs]; rfl)
        subst this
        exact ⟨a, by unfold beatmap.dotnet.intro_sort_iter; simp, by simp [iterR, disRes], ha⟩
      | succ k ihk =>
        intro j sV a ps depth hs ha hb
        have hs0 : sV ≠ 0#usize := by intro h; rw [h] at hs; simp at hs
        simp only [iterR]
        by_cases h1 : ps.val ≤ 1
        · have h1' : ps ≤ 1#usize := by show ps.val ≤ (1#usize : Usize).val; simpa using h1
          refine ⟨a, by unfold beatmap.dotnet.intro_sort_iter; simp [hs0, h1'], ?_, ha⟩
          have : disF cmp lo.val F j (none, a.val.toArray, ps.val, depth.val) = .yield (none, a.val.toArray, ps.val, depth.val) := by
            simp only [disF]; rw [if_neg (by omega)]
          simp only [this, dis_small cmp lo.val F a.val.toArray ps.val depth.val h1, disRes]
        · have h1' : ¬ ps ≤ 1#usize := by show ¬ ps.val ≤ (1#usize : Usize).val; simpa using h1
          have hg1 : ps.val > 1 := by omega
          by_cases h16 : ps.val ≤ 16
          · have h16' : ps ≤ 16#usize := by show ps.val ≤ (16#usize : Usize).val; simpa using h16
            by_cases h2 : ps.val = 2
            · have h2' : ps = 2#usize := UScalar.eq_of_val_eq (by rw [h2]; rfl)
              obtain ⟨i, hi, hiv⟩ := usize_add_one lo (by have := dns_usize_max; omega)
              obtain ⟨r, hr, hrv⟩ := beatmap.dotnet.swap_if_greater_refines cl hcl sc cmp hsc a lo i (by omega) (by omega)
              refine ⟨r, by unfold beatmap.dotnet.intro_sort_iter; simp [hs0, h1', h16', h2', hi, hr], ?_, ?_⟩
              · simp only [disF, if_pos hg1, if_pos h16, h2, beq_self_eq_true, if_true, disRes]
                rw [hrv, hiv]; simp
              · have := congrArg List.length hrv; simp [dpp_sig_size] at this; omega
            · have h2' : ¬ ps = 2#usize := by intro h; apply h2; rw [h]; rfl
              have h2b : (ps.val == 2) = false := by simpa using h2
              by_cases h3 : ps.val = 3
              · have h3' : ps = 3#usize := UScalar.eq_of_val_eq (by rw [h3]; rfl)
                obtain ⟨i, hi, hiv⟩ := usize_add_one lo (by have := dns_usize_max; omega)
                obtain ⟨i1, hi1, hi1v⟩ := dns_usize_add lo 2#usize (by simp; omega)
                simp only [show ((2#usize : Usize).val) = 2 from rfl] at hi1v
                obtain ⟨r1, hr1, hr1v⟩ := beatmap.dotnet.swap_if_greater_refines cl hcl sc cmp hsc a lo i (by omega) (by omega)
                have hr1l : r1.val.length = N := by
                  have := congrArg List.length hr1v; simp [dpp_sig_size] at this; omega
                obtain ⟨r2, hr2, hr2v⟩ := beatmap.dotnet.swap_if_greater_refines cl hcl sc cmp hsc r1 lo i1 (by omega) (by omega)
                have hr2l : r2.val.length = N := by
                  have := congrArg List.length hr2v; simp [dpp_sig_size] at this; omega
                obtain ⟨r3, hr3, hr3v⟩ := beatmap.dotnet.swap_if_greater_refines cl hcl sc cmp hsc r2 i i1 (by omega) (by omega)
                refine ⟨r3, by unfold beatmap.dotnet.intro_sort_iter; simp [hs0, h1', h16', h2', h3', hi, hr1, hi1, hr2, hr3],
                  ?_, ?_⟩
                · simp only [disF, if_pos hg1, if_pos h16, h2b, h3, beq_self_eq_true, if_true, disRes, Bool.false_eq_true,
                    if_false]
                  rw [hr3v, hr2v, hr1v, hiv, hi1v]; simp
                · have := congrArg List.length hr3v; simp [dpp_sig_size] at this; omega
              · have h3' : ¬ ps = 3#usize := by intro h; apply h3; rw [h]; rfl
                have h3b : (ps.val == 3) = false := by simpa using h3
                obtain ⟨r, hr, hrv, hrl⟩ := beatmap.dotnet.insertion_sort_refines cl hcl sc cmp hsc a lo ps (by omega) (by omega)
                refine ⟨r, by unfold beatmap.dotnet.intro_sort_iter; simp [hs0, h1', h16', h2', h3', hr], ?_, by omega⟩
                simp only [disF, if_pos hg1, if_pos h16, h2b, h3b, disRes, Bool.false_eq_true, if_false]
                exact hrv
          · have h16' : ¬ ps ≤ 16#usize := by show ¬ ps.val ≤ (16#usize : Usize).val; simpa using h16
            by_cases hd : depth.val = 0
            · have hd' : depth = 0#usize := UScalar.eq_of_val_eq (by rw [hd]; rfl)
              obtain ⟨r, hr, hrv, hrl⟩ := beatmap.dotnet.heap_sort_refines cl hcl sc cmp hsc a lo ps (by omega) (by omega)
              refine ⟨r, by unfold beatmap.dotnet.intro_sort_iter; simp [hs0, h1', h16', hd', hr], ?_, by omega⟩
              simp only [disF, if_pos hg1, if_neg h16, hd, beq_self_eq_true, if_true, disRes]
              exact hrv
            · have hd' : ¬ depth = 0#usize := by intro h; apply hd; rw [h]; rfl
              have hdb : (depth.val == 0) = false := by simpa using hd
              obtain ⟨p, a1, hpp, ha1v, hpv, ha1l, hpl⟩ := beatmap.dotnet.pick_pivot_and_partition_refines cl hcl sc cmp hsc
                hrefl a lo ps (by omega) (by omega) (by omega)
              obtain ⟨i, hi, hiv⟩ := dns_usize_add lo p (by omega)
              obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := dns_usize_max; omega)
              obtain ⟨i2, hi2, hi2v⟩ := usize_add_one p (by have := dns_usize_max; omega)
              obtain ⟨i3, hi3, hi3v⟩ := beatmap.dotnet.nat_sub_refines ps i2
              obtain ⟨i4, hi4, hi4v⟩ := dns_usize_sub1 depth (by omega)
              obtain ⟨i5, hi5, hi5v⟩ := dns_usize_sub1 fuel (by omega)
              obtain ⟨a2, ha2, ha2v, ha2l⟩ := ih a1 i1 i3 i4 i5 (by omega) (by omega) (by omega)
              obtain ⟨i6, hi6, hi6v⟩ := dns_usize_sub1 sV (by omega)
              obtain ⟨r, hr, hrv, hrl⟩ := ihk (j + 1) i6 a2 p i4 (by omega) ha2l (by omega)
              refine ⟨r, ?_, ?_, hrl⟩
              · unfold beatmap.dotnet.intro_sort_iter
                simp only [hs0, h1', h16', hd', if_false, hpp, bind_ok, uncurry_apply_pair, hi, hi1, hi2, hi3, hi4, hi5,
                  ha2, hi6]
                exact hr
              · simp only [disF, if_pos hg1, if_neg h16, hdb, Bool.false_eq_true, if_false]
                rw [hrv, ha2v, ha1v, hpv, hi1v, hiv, hi3v, hi2v, hi4v, hpv]
    obtain ⟨n1, hn1, hn1v⟩ := usize_add_one len (by have := dns_usize_max; omega)
    obtain ⟨r, hr, hrv, hrl⟩ := iter (len.val + 1) 0 n1 a len d hn1v ha hb
    refine ⟨r, ?_, ?_, hrl⟩
    · unfold beatmap.dotnet.intro_sort; simp only [hf0, if_false, hn1, bind_ok]; exact hr
    · rw [hrv, dis_spec]



/-- `IntroSort(keys[lo..lo+len), depthLimit)` with fuel (needs `cmp x x ≥ 0`, see `pick_pivot_and_partition_refines`) -/
theorem beatmap.dotnet.intro_sort_refines {T : Type} [Inhabited T] (cl : core.clone.Clone T)
    (hcl : ∀ x, cl.clone x = ok x) (sc : beatmap.dotnet.SortCmp T) (cmp : T → T → Int)
    (hsc : ∀ x y, ∃ r, sc.cmp3 x y = ok r ∧ r.val = cmp x y) (hrefl : ∀ x, ¬ cmp x x < 0)
    (a : alloc.vec.Vec T) (lo len d fuel : Usize) (hb : lo.val + len.val ≤ a.val.length) (hN : a.val.length < 2^31) :
    ∃ r, beatmap.dotnet.intro_sort cl sc a lo len d fuel = ok r ∧
      r.val.toArray = IntroSort.introSort cmp a.val.toArray lo.val len.val d.val fuel.val ∧ r.val.length = a.val.length :=
  dis_main cl hcl sc cmp hsc hrefl a.val.length hN fuel.val a lo len d fuel rfl rfl hb

/-- `List<T>.Sort(Comparison<T>)` (introsort; needs `cmp x x ≥ 0`) -/
theorem beatmap.dotnet.list_sort_refines {T : Type} [Inhabited T] (cl : core.clone.Clone T)
    (hcl : ∀ x, cl.clone x = ok x) (sc : beatmap.dotnet.SortCmp T) (cmp : T → T → Int)
    (hsc : ∀ x y, ∃ r, sc.cmp3 x y = ok r ∧ r.val = cmp x y) (hrefl : ∀ x, ¬ cmp x x < 0)
    (a : alloc.vec.Vec T) (hN : a.val.length < 2^31) :
    ∃ r, beatmap.dotnet.list_sort cl sc a = ok r ∧ r.val.toArray = listSort cmp a.val.toArray ∧
      r.val.length = a.val.length := by
  unfold beatmap.dotnet.list_sort listSort
  by_cases h1 : a.val.length > 1
  · have h1' : alloc.vec.Vec.len a > 1#usize := by show (1#usize : Usize).val < (alloc.vec.Vec.len a).val; simpa using h1
    obtain ⟨l, hl, hlv⟩ := beatmap.dotnet.log2_refines (alloc.vec.Vec.len a)
    have hlt : l.val < 31 := by
      rw [hlv]; show Nat.log2 (alloc.vec.Vec.len a).val < 31
      have hne : (alloc.vec.Vec.len a).val ≠ 0 := by
        have : (1#usize : Usize).val < (alloc.vec.Vec.len a).val := h1'
        have e : (1#usize : Usize).val = 1 := rfl
        omega
      rw [Nat.log2_lt hne]; simpa using hN
    obtain ⟨l1, hl1, hl1v⟩ := usize_add_one l (by have := dns_usize_max; omega)
    obtain ⟨l2, hl2, hl2v⟩ := dns_usize_mul2 l1 (by omega)
    obtain ⟨n1, hn1, hn1v⟩ := usize_add_one (alloc.vec.Vec.len a) (by have := dns_usize_max; simp; omega)
    obtain ⟨r, hr, hrv, hrl⟩ := beatmap.dotnet.intro_sort_refines cl hcl sc cmp hsc hrefl a 0#usize (alloc.vec.Vec.len a)
      l2 n1 (by simp) hN
    refine ⟨r, ?_, ?_, hrl⟩
    · simp only [h1', if_true, hl, bind_ok, hl1, hl2, hn1]; exact hr
    · rw [hrv, if_pos (by simpa using h1), hl2v, hl1v, hlv, hn1v]; simp
  · have h1' : ¬ alloc.vec.Vec.len a > 1#usize := by
      show ¬ (1#usize : Usize).val < (alloc.vec.Vec.len a).val; simpa using h1
    refine ⟨a, by simp only [h1', if_false], ?_, rfl⟩
    rw [if_neg (by simpa using h1)]


/-! ## `cmp x x ≥ 0` for `compareF64`; naturality of the introsort spec under an element map -/


theorem dns_unp_lt_irrefl (u : Float.Model.UnpackedFloat) : u.lt u = false := by
  cases u with
  | notANumber => rfl
  | infinity s => cases s <;> rfl
  | zero s => cases s <;> rfl
  | finite s m e hm =>
    cases s <;> simp [Float.Model.UnpackedFloat.lt, Float.Model.UnpackedFloat.compare, Ordering.then]

theorem dns_f64_lt_irrefl (x : Float) : ¬ x < x := by
  intro h; have h' : Float.lt x x = true := h
  unfold Float.lt at h'
  simp only [LT.lt, Float.Model.lt, dns_unp_lt_irrefl] at h'
  simp at h'

theorem dns_cmp_refl (x : F64) : ¬ compareF64 x x < 0 := by
  unfold compareF64
  rw [if_neg (dns_f64_lt_irrefl x), if_neg (dns_f64_lt_irrefl x)]
  split_ifs <;> decide



section dnt
variable {α β : Type} [Inhabited α] [Inhabited β] (g : α → β) (hd : g default = default)

include hd in
theorem dnt_get (A : Array α) (i : Nat) : (A.map g)[i]! = g A[i]! := by
  by_cases h : i < A.size
  · rw [getElem!_pos (A.map g) i (by simpa using h), getElem!_pos A i h]; simp
  · rw [getElem!_neg (A.map g) i (by simpa using h), getElem!_neg A i h, hd]

theorem dnt_set (A : Array α) (i : Nat) (x : α) : (A.map g).set! i (g x) = (A.set! i x).map g := by
  apply Array.ext'; simp [dns_toList_set!, List.map_set]

include hd in
theorem dnt_swap (A : Array α) (i j : Nat) : IntroSort.swap (A.map g) i j = (IntroSort.swap A i j).map g := by
  unfold IntroSort.swap; simp only [dnt_get g hd, dnt_set]

variable (cmp : α → α → Int) (cmp' : β → β → Int) (hc : ∀ x y, cmp' (g x) (g y) = cmp x y)

include hd hc in
theorem dnt_sig (A : Array α) (i j : Nat) :
    IntroSort.swapIfGreater cmp' (A.map g) i j = (IntroSort.swapIfGreater cmp A i j).map g := by
  unfold IntroSort.swapIfGreater; simp only [dnt_get g hd, hc, dnt_swap g hd]; split <;> rfl

include hd hc in
theorem dnt_ins (A : Array α) (lo len : Nat) :
    IntroSort.insertionSort cmp' (A.map g) lo len = (IntroSort.insertionSort cmp A lo len).map g := by
  rw [dns_ins_spec, dns_ins_spec]
  symm
  apply iterR_hom (fun A : Array α => A.map g) (fun i a => dnsIsOut cmp lo a i) (fun i a => dnsIsOut cmp' lo a i)
  intro i a
  simp only [dnsIsOut, dnt_get g hd]
  have := iterR_hom (fun s : Array α × Int × Bool => (s.1.map g, s.2.1, s.2.2)) (fun _ s => dnsIsIn cmp lo a[lo + i + 1]! s)
    (fun _ s => dnsIsIn cmp' lo (g a[lo + i + 1]!) s) (by
      intro _ s
      simp only [dnsIsIn, dnt_get g hd, hc]
      split_ifs <;> simp [dnt_set]) (i + 1) 0 (a, (i : Int), true)
  simp only at this
  rw [← this, dnt_set]

include hd hc in
theorem dnt_dh (A : Array α) (lo i0 n : Nat) :
    IntroSort.downHeap cmp' (A.map g) lo i0 n = (IntroSort.downHeap cmp A lo i0 n).map g := by
  rw [dns_dh_spec, dns_dh_spec]
  simp only [dnt_get g hd]
  have := iterR_hom (fun s : Array α × Nat × Bool => (s.1.map g, s.2.1, s.2.2)) (fun _ s => dnsDh cmp lo n A[lo + i0 - 1]! s)
    (fun _ s => dnsDh cmp' lo n (g A[lo + i0 - 1]!) s) (by
      intro _ s
      simp only [dnsDh, dnt_get g hd, hc]
      split_ifs <;> simp [dnt_set, dnt_get g hd]) (n + 1) 0 (A, i0, true)
  simp only at this
  rw [← this, dnt_set]

include hd hc in
theorem dnt_hs (A : Array α) (lo n : Nat) :
    IntroSort.heapSort cmp' (A.map g) lo n = (IntroSort.heapSort cmp A lo n).map g := by
  rw [dns_hs_spec, dns_hs_spec]
  have h1 := iterR_hom (fun s : Array α × Nat => (s.1.map g, s.2)) (fun _ s => (IntroSort.downHeap cmp s.1 lo s.2 n, s.2 - 1))
    (fun _ s => (IntroSort.downHeap cmp' s.1 lo s.2 n, s.2 - 1)) (by
      intro _ s; simp only [dnt_dh g hd cmp cmp' hc]) (n / 2) 0 (A, n / 2)
  have h2 := iterR_hom (fun s : Array α × Nat => (s.1.map g, s.2))
    (fun _ s => (IntroSort.downHeap cmp (IntroSort.swap s.1 lo (lo + s.2 - 1)) lo 1 (s.2 - 1), s.2 - 1))
    (fun _ s => (IntroSort.downHeap cmp' (IntroSort.swap s.1 lo (lo + s.2 - 1)) lo 1 (s.2 - 1), s.2 - 1)) (by
      intro _ s; simp only [dnt_swap g hd, dnt_dh g hd cmp cmp' hc]) (n - 1) 0
    ((iterR (fun _ (s : Array α × Nat) => .yield (IntroSort.downHeap cmp s.1 lo s.2 n, s.2 - 1)) 0 (n / 2) (A, n / 2)).1, n)
  simp only at h1 h2
  rw [← (congrArg Prod.fst h1)]; exact (congrArg Prod.fst h2).symm

end dnt



section dnt2
variable {α β : Type} [Inhabited α] [Inhabited β] (g : α → β) (hd : g default = default)
  (cmp : α → α → Int) (cmp' : β → β → Int) (hc : ∀ x y, cmp' (g x) (g y) = cmp x y)

include hd hc in
theorem dnt_dppLs (lo len : Nat) (A : Array α) (pv : α) (l : Nat) :
    dppLs cmp' lo len (A.map g) (g pv) l = dppLs cmp lo len A pv l := by
  unfold dppLs
  congr 1; apply dns_iterR_ext; intro _ s; simp only [dppL, dnt_get g hd, hc]

include hd hc in
theorem dnt_dppRs (lo len : Nat) (A : Array α) (pv : α) (r : Nat) :
    dppRs cmp' lo len (A.map g) (g pv) r = dppRs cmp lo len A pv r := by
  unfold dppRs
  congr 1; apply dns_iterR_ext; intro _ s; simp only [dppR, dnt_get g hd, hc]

include hd hc in
theorem dnt_ppp (A : Array α) (lo len : Nat) :
    IntroSort.pickPivotAndPartition cmp' (A.map g) lo len =
      ((IntroSort.pickPivotAndPartition cmp A lo len).1.map g, (IntroSort.pickPivotAndPartition cmp A lo len).2) := by
  rw [dpp_spec, dpp_spec]
  have hA : dppA cmp' (A.map g) lo len = (dppA cmp A lo len).map g := by simp only [dppA, dnt_sig g hd cmp cmp' hc]
  simp only [hA, dnt_get g hd, dnt_swap g hd]
  have := iterR_hom (fun s : Array α × Nat × Nat => (s.1.map g, s.2.1, s.2.2))
    (fun _ s => dppO cmp lo len (dppA cmp A lo len)[lo + (len - 1) / 2]! s)
    (fun _ s => dppO cmp' lo len (g (dppA cmp A lo len)[lo + (len - 1) / 2]!) s) (by
      intro _ s
      simp only [dppO, dnt_dppLs g hd cmp cmp' hc, dnt_dppRs g hd cmp cmp' hc]
      split_ifs <;> simp [dnt_swap g hd]) (len + 1) 0
    (IntroSort.swap (dppA cmp A lo len) (lo + (len - 1) / 2) (lo + (len - 1) - 1), 0, len - 1 - 1)
  simp only at this
  rw [← this]
  dsimp only
  split_ifs <;> simp [dnt_swap g hd]

def dntPhi (s : Option (Array α) × Array α × Nat × Nat) : Option (Array β) × Array β × Nat × Nat :=
  (s.1.map (·.map g), s.2.1.map g, s.2.2.1, s.2.2.2)

include hd hc in
theorem dnt_intro : ∀ (F : Nat) (A : Array α) (lo len d : Nat),
    IntroSort.introSort cmp' (A.map g) lo len d F = (IntroSort.introSort cmp A lo len d F).map g := by
  intro F
  induction F with
  | zero => intro A lo len d; rfl
  | succ F ih =>
    intro A lo len d
    rw [dis_spec, dis_spec]
    have hstep : ∀ j s, disF cmp' lo F j (dntPhi g s) = (match disF cmp lo F j s with
        | .done c => .done (dntPhi g c) | .yield c => .yield (dntPhi g c)) := by
      intro j s
      simp only [disF, dntPhi, dnt_sig g hd cmp cmp' hc, dnt_ins g hd cmp cmp' hc, dnt_hs g hd cmp cmp' hc,
        dnt_ppp g hd cmp cmp' hc, ih]
      split_ifs <;> rfl
    have key : ∀ k j s, iterR (disF cmp' lo F) j k (dntPhi g s) = dntPhi g (iterR (disF cmp lo F) j k s) := by
      intro k
      induction k with
      | zero => intro j s; rfl
      | succ k ihk =>
        intro j s
        simp only [iterR, hstep]
        cases disF cmp lo F j s with
        | done c => rfl
        | yield c => exact ihk _ _
    have := key (len + 1) 0 (none, A, len, d)
    simp only [dntPhi, Option.map_none] at this
    rw [this]
    unfold disRes
    cases (iterR (disF cmp lo F) 0 (len + 1) (none, A, len, d)).1 <;> rfl

include hd hc in
theorem dnt_list (A : Array α) : listSort cmp' (A.map g) = (listSort cmp A).map g := by
  unfold listSort
  simp only [Array.size_map]
  split
  · exact dnt_intro g hd cmp cmp' hc _ _ _ _ _
  · rfl

end dnt2


/-! ## the introsort spec preserves the array size -/

section dsz
variable {α : Type} [Inhabited α] (cmp : α → α → Int)

theorem dsz_set (A : Array α) (i : Nat) (x : α) : (A.set! i x).size = A.size := by simp

theorem dsz_ins (A : Array α) (lo len : Nat) : (IntroSort.insertionSort cmp A lo len).size = A.size := by
  rw [dns_ins_spec]
  apply iterR_inv (fun B : Array α => B.size = A.size) (fun i a => dnsIsOut cmp lo a i) _ _ _ _ rfl
  intro i a ha
  simp only [dnsIsOut, dsz_set]
  have := iterR_inv (fun s : Array α × Int × Bool => s.1.size = A.size) (fun _ s => dnsIsIn cmp lo a[lo + i + 1]! s)
    (by intro _ s hs; simp only [dnsIsIn]; split_ifs <;> simp [hs]) (i + 1) 0 (a, (i : Int), true) ha
  exact this

theorem dsz_dh (A : Array α) (lo i0 n : Nat) : (IntroSort.downHeap cmp A lo i0 n).size = A.size := by
  rw [dns_dh_spec]
  simp only [dsz_set]
  exact iterR_inv (fun s : Array α × Nat × Bool => s.1.size = A.size) (fun _ s => dnsDh cmp lo n A[lo + i0 - 1]! s)
    (by intro _ s hs; simp only [dnsDh]; split_ifs <;> simp [hs]) (n + 1) 0 (A, i0, true) rfl

theorem dsz_hs (A : Array α) (lo n : Nat) : (IntroSort.heapSort cmp A lo n).size = A.size := by
  rw [dns_hs_spec]
  have h1 := iterR_inv (fun s : Array α × Nat => s.1.size = A.size) (fun _ s => (IntroSort.downHeap cmp s.1 lo s.2 n, s.2 - 1))
    (by intro _ s hs; simp only [dsz_dh, hs]) (n / 2) 0 (A, n / 2) rfl
  exact iterR_inv (fun s : Array α × Nat => s.1.size = A.size)
    (fun _ s => (IntroSort.downHeap cmp (IntroSort.swap s.1 lo (lo + s.2 - 1)) lo 1 (s.2 - 1), s.2 - 1))
    (by intro _ s hs; simp only [dsz_dh, dpp_swap_size, hs]) (n - 1) 0 _ h1

theorem dsz_ppp (A : Array α) (lo len : Nat) : (IntroSort.pickPivotAndPartition cmp A lo len).1.size = A.size := by
  rw [dpp_spec]
  have hA : (dppA cmp A lo len).size = A.size := by simp only [dppA, dpp_sig_size]
  have := iterR_inv (fun s : Array α × Nat × Nat => s.1.size = A.size)
    (fun _ s => dppO cmp lo len (dppA cmp A lo len)[lo + (len - 1) / 2]! s)
    (by intro _ s hs; simp only [dppO]; split_ifs <;> simp [dpp_swap_size, hs]) (len + 1) 0
    (IntroSort.swap (dppA cmp A lo len) (lo + (len - 1) / 2) (lo + (len - 1) - 1), 0, len - 1 - 1)
    (by simp only [dpp_swap_size, hA])
  dsimp only
  split <;> simp [dpp_swap_size, this]

theorem dsz_intro : ∀ (F : Nat) (A : Array α) (lo len d : Nat), (IntroSort.introSort cmp A lo len d F).size = A.size := by
  intro F
  induction F with
  | zero => intro A lo len d; rfl
  | succ F ih =>
    intro A lo len d
    rw [dis_spec]
    have key : ∀ k j (s : Option (Array α) × Array α × Nat × Nat), s.2.1.size = A.size →
        (∀ r, s.1 = some r → r.size = A.size) →
        (iterR (disF cmp lo F) j k s).2.1.size = A.size ∧
          ∀ r, (iterR (disF cmp lo F) j k s).1 = some r → r.size = A.size := by
      intro k
      induction k with
      | zero => intro j s h1 h2; exact ⟨h1, h2⟩
      | succ k ihk =>
        intro j s h1 h2
        simp only [iterR]
        unfold disF
        split_ifs
        all_goals first
          | (exact ihk _ _ (by simp only [IntroSort.introSort, ih, dsz_ppp, h1]) (by intro r hr; cases hr))
          | (exact ihk _ _ h1 (by intro r hr; cases hr))
          | (refine ⟨by simp [dpp_sig_size, h1], ?_⟩; intro r hr; cases hr; simp [dpp_sig_size, dsz_ins, dsz_hs, h1])
    obtain ⟨k1, k2⟩ := key (len + 1) 0 (none, A, len, d) rfl (by intro r hr; cases hr)
    unfold disRes
    split
    · rename_i r hr; exact k2 r hr
    · exact k1

theorem dsz_list (A : Array α) : (listSort cmp A).size = A.size := by
  unfold listSort; split
  · exact dsz_intro cmp _ _ _ _ _
  · rfl

end dsz

theorem sort_nested_size (a : Array NestedObject) : (sortNested a).size = a.size := dsz_list _ a


end OsuProofs
