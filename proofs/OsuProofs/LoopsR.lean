/-
Generic lockstep lemmas for index loops (the common shape of the beatmap code):
* spec side: `for j in [lo:hi]` / `for x in list` in `Id` (with `break`/early `return` as
  `ForInStep.done`) is `iterR f lo (hi - lo) s` for the index-dependent body `f`;
* Rust side: an Aeneas `loop` whose state `t` carries the index `idx t`.
`loop_iterR` reduces "the Rust loop refines the spec loop" to two straight-line obligations
on one iteration (`hstep`, `hend`), which `step*`/`simp` can usually discharge.
-/
import OsuProofs.Loops
set_option linter.unusedSimpArgs false
open Aeneas Aeneas.Std Result

namespace OsuProofs

/-- `k` iterations of an index-dependent `Id` loop body starting at index `j`. -/
def iterR {S : Type} (f : Nat → S → ForInStep S) : Nat → Nat → S → S
  | _, 0, s => s
  | j, k+1, s => match f j s with
    | .done c => c
    | .yield c => iterR f (j + 1) k c

theorem forIn_range'_iterR {S : Type} (f : Nat → S → Id (ForInStep S)) :
    ∀ (k j : Nat) (s : S), forIn (m := Id) (List.range' j k) s f = iterR f j k s := by
  intro k
  induction k with
  | zero => intro j s; rfl
  | succ k ih =>
    intro j s
    rw [List.range'_succ, List.forIn_cons]
    simp only [iterR]
    cases f j s with
    | done c => rfl
    | yield c => exact ih (j + 1) c

/-- `for j in [lo:hi] do …` (step 1) in `Id`. -/
theorem forIn_range_iterR {S : Type} (f : Nat → S → Id (ForInStep S)) (lo hi : Nat) (s : S) :
    forIn (m := Id) [lo:hi] s f = iterR f lo (hi - lo) s := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.div_one]
  rw [show hi - lo + 1 - 1 = hi - lo by omega]
  exact forIn_range'_iterR f (hi - lo) lo s

/-- `for x in l do …` in `Id`, as an index loop. -/
theorem forIn_list_iterR {S X : Type} [Inhabited X] (l : List X) (g : X → S → Id (ForInStep S)) (s : S) :
    forIn (m := Id) l s g = iterR (fun j acc => g l[j]! acc) 0 l.length s := by
  suffices h : ∀ (k : Nat) (s : S), forIn (m := Id) (l.drop k) s g = iterR (fun j acc => g l[j]! acc) k (l.length - k) s by
    simpa using h 0 s
  intro k
  induction h : l.length - k generalizing k with
  | zero => intro s; rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | succ m ih =>
    intro s
    have hk : k < l.length := by omega
    rw [List.drop_eq_getElem_cons hk, List.forIn_cons]
    simp only [iterR]
    rw [getElem!_pos l k hk]
    cases g l[k] s with
    | done c => rfl
    | yield c => exact ih (k + 1) (by omega) c

theorem forIn_array_iterR {S X : Type} [Inhabited X] (a : Array X) (g : X → S → Id (ForInStep S)) (s : S) :
    forIn (m := Id) a s g = iterR (fun j acc => g a[j]! acc) 0 a.size s := by
  rw [← Array.forIn_toList, forIn_list_iterR]
  simp only [Array.length_toList]
  congr 1; funext j acc; simp [getElem!_def]

theorem iterR_drop_foldl {S X : Type} [Inhabited X] (l : List X) (f : S → X → S) :
    ∀ k s, (l.drop k).foldl f s = iterR (fun j acc => .yield (f acc l[j]!)) k (l.length - k) s := by
  intro k
  induction h : l.length - k generalizing k with
  | zero => intro s; rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | succ m ih =>
    intro s
    have hk : k < l.length := by omega
    rw [List.drop_eq_getElem_cons hk, List.foldl_cons, ih (k + 1) (by omega)]
    simp only [iterR]; rw [getElem!_pos l k hk]

theorem foldl_iterR {S X : Type} [Inhabited X] (l : List X) (f : S → X → S) (s : S) :
    l.foldl f s = iterR (fun j acc => .yield (f acc l[j]!)) 0 l.length s := by
  simpa using iterR_drop_foldl l f 0 s

theorem map_iterR {X B : Type} [Inhabited X] (l : List X) (h : X → B) :
    l.map h = iterR (fun j acc => .yield (acc ++ [h l[j]!])) 0 l.length [] := by
  rw [← foldl_iterR l (fun acc x => acc ++ [h x])]
  suffices ∀ acc, l.foldl (fun acc x => acc ++ [h x]) acc = acc ++ l.map h by simpa using (this []).symm
  induction l with
  | nil => intro acc; simp
  | cons x t ih => intro acc; simp [ih]

theorem any_iterR {X : Type} [Inhabited X] (l : List X) (p : X → Bool) :
    l.any p = iterR (fun j acc => if p l[j]! then .done true else .yield acc) 0 l.length false := by
  suffices ∀ k, (l.drop k).any p = iterR (fun j acc => if p l[j]! then .done true else .yield acc) k (l.length - k) false by
    simpa using this 0
  intro k
  induction h : l.length - k generalizing k with
  | zero => rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | succ m ih =>
    have hk : k < l.length := by omega
    rw [List.drop_eq_getElem_cons hk, List.any_cons, ih (k + 1) (by omega)]
    simp only [iterR]; rw [getElem!_pos l k hk]
    cases p l[k] <;> rfl

theorem findIdx_iterR {X : Type} [Inhabited X] (l : List X) (p : X → Bool) :
    l.findIdx? p = iterR (fun j acc => if p l[j]! then .done (some j) else .yield acc) 0 l.length none := by
  suffices ∀ k, ((l.drop k).findIdx? p).map (· + k) =
      iterR (fun j acc => if p l[j]! then .done (some j) else .yield acc) k (l.length - k) none by
    simpa using this 0
  intro k
  induction h : l.length - k generalizing k with
  | zero => rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | succ m ih =>
    have hk : k < l.length := by omega
    rw [List.drop_eq_getElem_cons hk, List.findIdx?_cons]
    simp only [iterR]; rw [getElem!_pos l k hk]
    cases hp : p l[k]
    · simp only [Bool.false_eq_true, if_false, ← ih (k + 1) (by omega)]
      cases List.findIdx? p (List.drop (k + 1) l) <;> simp; omega
    · simp

/-- Lockstep: an Aeneas index loop refines `iterR`. A spec `done` may be matched by the Rust loop
either stopping at once or after one more (flag-checking) iteration. -/
theorem loop_iterR {T Y S : Type} (body : T → Result (ControlFlow T Y)) (f : Nat → S → ForInStep S) (n : Nat)
    (idx : T → Nat) (R : T → S → Prop) (Q : Y → S → Prop)
    (hstep : ∀ t s, R t s → idx t < n →
      (∀ s', f (idx t) s = .yield s' → ∃ t', body t = ok (.cont t') ∧ idx t' = idx t + 1 ∧ R t' s') ∧
      (∀ s', f (idx t) s = .done s' → ∃ y, (body t = ok (.done y) ∨
        ∃ t', body t = ok (.cont t') ∧ body t' = ok (.done y)) ∧ Q y s'))
    (hend : ∀ t s, R t s → n ≤ idx t → ∃ y, body t = ok (.done y) ∧ Q y s) :
    ∀ t s, R t s → idx t ≤ n → ∃ y, loop body t = ok y ∧ Q y (iterR f (idx t) (n - idx t) s) := by
  intro t
  induction hk : n - idx t using Nat.strong_induction_on generalizing t with
  | _ k ih =>
    intro s hR hle
    by_cases hlt : idx t < n
    · obtain ⟨hy, hd⟩ := hstep t s hR hlt
      have e : n - idx t = (n - (idx t + 1)) + 1 := by omega
      rw [← hk, e]; simp only [iterR]
      cases hf : f (idx t) s with
      | yield s' =>
        obtain ⟨t', hb, hi, hR'⟩ := hy s' hf
        obtain ⟨y, hl, hq⟩ := ih (n - idx t') (by omega) t' rfl s' hR' (by omega)
        refine ⟨y, by rw [loop_unfold, hb]; simpa using hl, ?_⟩
        rw [hi] at hq; exact hq
      | done s' =>
        obtain ⟨y, hb, hq⟩ := hd s' hf
        refine ⟨y, ?_, hq⟩
        rcases hb with hb | ⟨t', hb, hb'⟩
        · rw [loop_unfold, hb]; simp only [bind_ok]
        · rw [loop_unfold, hb]; simp only [bind_ok]; rw [loop_unfold, hb']; simp only [bind_ok]
    · obtain ⟨y, hb, hq⟩ := hend t s hR (by omega)
      refine ⟨y, by rw [loop_unfold, hb]; simp only [bind_ok], ?_⟩
      rw [← hk, show n - idx t = 0 by omega]; exact hq

/-- Lockstep for `while` loops: an Aeneas loop refines an `Id` `while`/`repeat` loop
(`forIn Lean.Loop.mk s F`) whose yields decrease a measure `μ`. -/
theorem loop_whileR {T Y S : Type} (body : T → Result (ControlFlow T Y)) (F : Unit → S → Id (ForInStep S))
    (μ : S → Nat) (R : T → S → Prop) (Q : Y → S → Prop)
    (hstep : ∀ t s, R t s →
      (∀ s', F () s = .yield s' → μ s' < μ s ∧ ∃ t', body t = ok (.cont t') ∧ R t' s') ∧
      (∀ s', F () s = .done s' → ∃ y, (body t = ok (.done y) ∨
        ∃ t', body t = ok (.cont t') ∧ body t' = ok (.done y)) ∧ Q y s')) :
    ∀ t s, R t s → ∃ y, loop body t = ok y ∧ Q y (forIn (m := Id) Lean.Loop.mk s F) := by
  intro t s
  induction hk : μ s using Nat.strong_induction_on generalizing t s with
  | _ k ih =>
    intro hR
    obtain ⟨hy, hd⟩ := hstep t s hR
    have hu : (forIn (m := Id) Lean.Loop.mk s F) =
        (match F () s with | .done c => c | .yield c => forIn (m := Id) Lean.Loop.mk c F) := by
      show Lean.Loop.forIn _ _ _ = _
      rw [Lean.Loop.forIn_eq_of_monadTail]
      cases F () s <;> rfl
    rw [hu]
    cases hf : F () s with
    | yield s' =>
      obtain ⟨hlt, t', hb, hR'⟩ := hy s' hf
      obtain ⟨y, hl, hq⟩ := ih (μ s') (by omega) t' s' rfl hR'
      exact ⟨y, by rw [loop_unfold, hb]; simpa using hl, hq⟩
    | done s' =>
      obtain ⟨y, hb, hq⟩ := hd s' hf
      refine ⟨y, ?_, hq⟩
      rcases hb with hb | ⟨t', hb, hb'⟩
      · rw [loop_unfold, hb]; simp only [bind_ok]
      · rw [loop_unfold, hb]; simp only [bind_ok]; rw [loop_unfold, hb']; simp only [bind_ok]

/-- Template for "push `g i` for `i in 0..n`" loops (`Vec::push` in an index loop). -/
theorem loop_push_map {X : Type} (body : alloc.vec.Vec X × Usize → Result (ControlFlow (alloc.vec.Vec X × Usize) (alloc.vec.Vec X)))
    (n : Nat) (g : Nat → X)
    (hstep : ∀ ts i, i.val < n → ts.val.length + (n - i.val) ≤ Usize.max →
      ∃ ts' i', body (ts, i) = ok (.cont (ts', i')) ∧ ts'.val = ts.val ++ [g i.val] ∧ i'.val = i.val + 1)
    (hend : ∀ ts i, n ≤ i.val → body (ts, i) = ok (.done ts)) :
    ∀ ts i, i.val ≤ n → ts.val.length + (n - i.val) ≤ Usize.max →
      ∃ r, loop body (ts, i) = ok r ∧ r.val = ts.val ++ (List.range' i.val (n - i.val)).map g := by
  intro ts i
  induction hk : n - i.val using Nat.strong_induction_on generalizing ts i with
  | _ k ih =>
    intro hle hmax
    by_cases hlt : i.val < n
    · obtain ⟨ts', i', hb, hts, hi⟩ := hstep ts i hlt (by omega)
      have hl' : ts'.val.length = ts.val.length + 1 := by simp [hts]
      obtain ⟨r, hl, hr⟩ := ih (n - i'.val) (by omega) ts' i' rfl (by omega) (by omega)
      refine ⟨r, by rw [loop_unfold, hb]; simpa using hl, ?_⟩
      rw [hr, hts, hi, ← hk, show n - i.val = (n - (i.val + 1)) + 1 by omega, List.range'_succ]
      simp
    · refine ⟨ts, by rw [loop_unfold, hend ts i (by omega)]; simp only [bind_ok], ?_⟩
      rw [← hk, show n - i.val = 0 by omega]; simp


theorem take_set_drop {X : Type} (l : List X) (i : Nat) (h : i < l.length) (g : X → X) :
    (l.set i (g l[i])).take (i + 1) ++ ((l.set i (g l[i])).drop (i + 1)).map g = l.take i ++ (l.drop i).map g := by
  rw [List.drop_eq_getElem_cons h]
  simp [List.take_succ, List.drop_set, h, List.getElem?_set, List.take_set]
  rw [List.set_eq_of_length_le (by simp)]
  conv_rhs => rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp

/-- Template for in-place "`v[i] = g(v[i])` for every `i`" loops (`index_mut` + write back), with an
unchanged extra state component `a`. -/
theorem loop_set_map {A X : Type}
    (body : A × alloc.vec.Vec X × Usize → Result (ControlFlow (A × alloc.vec.Vec X × Usize) (A × alloc.vec.Vec X)))
    (g : X → X)
    (hstep : ∀ a v i (h : i.val < v.val.length), ∃ v' i', body (a, v, i) = ok (.cont (a, v', i')) ∧
      v'.val = v.val.set i.val (g v.val[i.val]) ∧ i'.val = i.val + 1)
    (hend : ∀ a v i, v.val.length ≤ i.val → body (a, v, i) = ok (.done (a, v))) :
    ∀ a v i, i.val ≤ v.val.length → ∃ r, loop body (a, v, i) = ok r ∧ r.1 = a ∧
      r.2.val = v.val.take i.val ++ (v.val.drop i.val).map g := by
  intro a v i
  induction hk : v.val.length - i.val using Nat.strong_induction_on generalizing v i with
  | _ k ih =>
    intro hle
    by_cases hlt : i.val < v.val.length
    · obtain ⟨v', i', hb, hv, hi⟩ := hstep a v i hlt
      have hl : v'.val.length = v.val.length := by simp [hv]
      obtain ⟨r, hlp, hr1, hr2⟩ := ih (v'.val.length - i'.val) (by omega) v' i' rfl (by omega)
      refine ⟨r, by rw [loop_unfold, hb]; simpa using hlp, hr1, ?_⟩
      rw [hr2, hv, hi, take_set_drop _ _ hlt]
    · refine ⟨(a, v), by rw [loop_unfold, hend a v i (by omega)]; simp only [bind_ok], rfl, ?_⟩
      simp [List.drop_eq_nil_of_le (show v.val.length ≤ i.val by omega), List.take_of_length_le (show v.val.length ≤ i.val by omega)]


theorem iterR_hom {S T : Type} (φ : S → T) (g : Nat → S → S) (g' : Nat → T → T)
    (h : ∀ k s, φ (g k s) = g' k (φ s)) :
    ∀ n j s, φ (iterR (fun k s => .yield (g k s)) j n s) = iterR (fun k t => .yield (g' k t)) j n (φ s) := by
  intro n
  induction n with
  | zero => intro j s; rfl
  | succ n ih => intro j s; simp only [iterR]; rw [ih, h]

theorem iterR_inv {S : Type} (P : S → Prop) (g : Nat → S → S) (h : ∀ k s, P s → P (g k s)) :
    ∀ n j s, P s → P (iterR (fun k s => .yield (g k s)) j n s) := by
  intro n
  induction n with
  | zero => intro j s hs; exact hs
  | succ n ih => intro j s hs; simp only [iterR]; exact ih _ _ (h _ _ hs)

/-- Template: a Rust loop over `j < len` that replaces the whole vector by a step `F j` (in a
representation `rep`) and keeps its length. -/
theorem loop_vec_fold {X S : Type}
    (body : alloc.vec.Vec X × Usize → Result (ControlFlow (alloc.vec.Vec X × Usize) (alloc.vec.Vec X)))
    (rep : alloc.vec.Vec X → S) (F : Nat → S → S) (n : Nat)
    (hstep : ∀ v j, v.val.length = n → j.val < n → ∃ v' j', body (v, j) = ok (.cont (v', j')) ∧
      rep v' = F j.val (rep v) ∧ v'.val.length = n ∧ j'.val = j.val + 1)
    (hend : ∀ v j, v.val.length = n → n ≤ j.val → body (v, j) = ok (.done v)) :
    ∀ v j, v.val.length = n → j.val ≤ n → ∃ r, loop body (v, j) = ok r ∧
      rep r = iterR (fun k s => .yield (F k s)) j.val (n - j.val) (rep v) := by
  intro v j hv hj
  have := loop_iterR body (fun k s => .yield (F k s)) n (fun t => t.2.val)
    (fun t s => t.1.val.length = n ∧ rep t.1 = s ∧ t.2.val ≤ n) (fun y s => rep y = s)
    (by
      rintro ⟨v, j⟩ s ⟨h1, h2, h3⟩ hk
      simp only at h1 h2 h3 hk ⊢
      obtain ⟨v', j', hb, hr, hl, hj⟩ := hstep v j h1 hk
      constructor
      · intro s' hs'
        cases hs'
        exact ⟨(v', j'), hb, hj, hl, by rw [hr, h2], by simp only; omega⟩
      · intro s' hs'; cases hs')
    (by
      rintro ⟨v, j⟩ s ⟨h1, h2, h3⟩ hk
      exact ⟨v, hend v j h1 hk, h2⟩)
    (v, j) (rep v) ⟨hv, rfl, hj⟩ hj
  exact this


/-- General index fold: a Rust loop whose state `t` carries an index `ix t` that runs up to `n`, an
invariant `Inv`, and a representation `rep t` that each iteration transforms by `G (ix t)`
(spec side: `for j in [lo:n] do s := G j s`, i.e. `iterR (fun k s => .yield (G k s))`). -/
theorem loop_fold_gen {T Y S : Type} (body : T → Result (ControlFlow T Y)) (ix : T → Usize) (n : Nat)
    (Inv : T → Prop) (rep : T → S) (G : Nat → S → S) (out : Y → S → Prop)
    (hstep : ∀ t, Inv t → (ix t).val < n → ∃ t', body t = ok (.cont t') ∧ (ix t').val = (ix t).val + 1 ∧
      rep t' = G (ix t).val (rep t) ∧ Inv t')
    (hend : ∀ t, Inv t → n ≤ (ix t).val → ∃ y, body t = ok (.done y) ∧ out y (rep t)) :
    ∀ t, Inv t → (ix t).val ≤ n → ∃ y, loop body t = ok y ∧
      out y (iterR (fun k s => .yield (G k s)) (ix t).val (n - (ix t).val) (rep t)) := by
  intro t ht hle
  have := loop_iterR body (fun k s => .yield (G k s)) n (fun t => (ix t).val)
    (fun t s => Inv t ∧ rep t = s ∧ (ix t).val ≤ n) out
    (by
      intro t s ⟨h1, h2, h3⟩ hk
      obtain ⟨t', hb, hi, hr, hI⟩ := hstep t h1 hk
      constructor
      · intro s' hs'
        cases hs'
        exact ⟨t', hb, hi, hI, by rw [hr, h2], by omega⟩
      · intro s' hs'; cases hs')
    (by
      intro t s ⟨h1, h2, h3⟩ hk
      obtain ⟨y, hb, hq⟩ := hend t h1 hk
      exact ⟨y, hb, h2 ▸ hq⟩)
    t (rep t) ⟨ht, rfl, hle⟩ hle
  exact this

/-- `j + 1` on `Usize` below the bound, as a simp-usable rewrite target. -/
theorem usize_succ_ok (j : Usize) (h : j.val + 1 ≤ Usize.max) :
    ∃ j1 : Usize, j + 1#usize = ok j1 ∧ j1.val = j.val + 1 := usize_add_one j h

theorem vec_index_mut_usize_ok {α} (v : alloc.vec.Vec α) (i : Usize) (h : i.val < v.val.length) :
    alloc.vec.Vec.index_mut_usize v i = ok (v.val[i.val]'h, alloc.vec.Vec.set v i) := by
  obtain ⟨⟨a, b⟩, hx, hx1, hx2⟩ := eq_ok_of_spec (alloc.vec.Vec.index_mut_usize_spec v i h)
  rw [hx, hx1, hx2]
theorem vec_set_val' {α} (v : alloc.vec.Vec α) (i : Usize) (x : α) : (alloc.vec.Vec.set v i x).val = v.val.set i.val x := by
  simp [alloc.vec.Vec.set]
theorem list_modify_set {α} (l : List α) (i : Nat) (h : i < l.length) (g : α → α) :
    l.modify i g = l.set i (g l[i]) := by
  simp [List.modify_eq_set_getElem?, List.getElem?_eq_getElem h]

/-- the result of an in-bounds `Vec::push` (for `simp`-driven loop steps) -/
noncomputable def vpush {α} (v : alloc.vec.Vec α) (x : α) (h : v.val.length < Usize.max) : alloc.vec.Vec α :=
  (push_eq v x h).choose
theorem vec_push_ok {α} (v : alloc.vec.Vec α) (x : α) (h : v.val.length < Usize.max) :
    alloc.vec.Vec.push v x = ok (vpush v x h) := (push_eq v x h).choose_spec.1
@[simp] theorem vpush_val {α} (v : alloc.vec.Vec α) (x : α) (h : v.val.length < Usize.max) :
    (vpush v x h).val = v.val ++ [x] := (push_eq v x h).choose_spec.2
theorem vec_index_usize_ok {α} (v : alloc.vec.Vec α) (i : Usize) (h : i.val < v.val.length) :
    alloc.vec.Vec.index_usize v i = ok (v.val[i.val]'h) := by
  obtain ⟨x, hx, hx'⟩ := eq_ok_of_spec (alloc.vec.Vec.index_usize_spec v i h)
  rw [hx, hx']
theorem slice_index_ok {α} (v : Slice α) (i : Usize) (h : i.val < v.val.length) :
    Slice.index_usize v i = ok (v.val[i.val]'h) := index_eq v i h
theorem vec_lt_len_iff {α} (i : Usize) (v : alloc.vec.Vec α) : (i < alloc.vec.Vec.len v) ↔ i.val < v.val.length := by
  show i.val < (alloc.vec.Vec.len v).val ↔ _; simp
theorem slice_lt_len_iff {α} (i : Usize) (v : Slice α) : (i < Slice.len v) ↔ i.val < v.val.length := by
  show i.val < (Slice.len v).val ↔ _; simp

theorem iterR_modify_map_aux {α} (g : α → α) :
    ∀ k (l : List α), k ≤ l.length →
      iterR (fun j s => .yield (s.modify j g)) k (l.length - k) l = l.take k ++ (l.drop k).map g := by
  intro k l hk
  induction h : l.length - k generalizing k l with
  | zero => simp [iterR, List.drop_eq_nil_of_le (show l.length ≤ k by omega), List.take_of_length_le (show l.length ≤ k by omega)]
  | succ m ih =>
    simp only [iterR]
    have hk' : k < l.length := by omega
    have hl : (l.modify k g).length = l.length := by simp
    rw [ih (k + 1) (l.modify k g) (by omega) (by omega)]
    rw [list_modify_set l k hk' g]
    exact take_set_drop l k hk' g

/-- an in-place `v[j] = g(v[j])` loop over all indices is `List.map g` -/
theorem iterR_modify_map {α} (g : α → α) (l : List α) :
    iterR (fun j s => .yield (s.modify j g)) 0 (l.length - 0) l = l.map g := by
  simpa using iterR_modify_map_aux g 0 l (by simp)

/-- `loop_fold_gen` with the index increment handed to the step obligation (so that it can be
discharged by `simp [body, hj1, ...]`). -/
theorem loop_fold_gen' {T Y S : Type} (body : T → Result (ControlFlow T Y)) (ix : T → Usize) (n : Nat)
    (hn : n ≤ Usize.max) (Inv : T → Prop) (rep : T → S) (G : Nat → S → S) (out : Y → S → Prop)
    (hstep : ∀ t, Inv t → (ix t).val < n → ∀ j1 : Usize, ix t + 1#usize = ok j1 → j1.val = (ix t).val + 1 →
      ∃ t', body t = ok (.cont t') ∧ ix t' = j1 ∧ rep t' = G (ix t).val (rep t) ∧ Inv t')
    (hend : ∀ t, Inv t → n ≤ (ix t).val → ∃ y, body t = ok (.done y) ∧ out y (rep t)) :
    ∀ t, Inv t → (ix t).val ≤ n → ∃ y, loop body t = ok y ∧
      out y (iterR (fun k s => .yield (G k s)) (ix t).val (n - (ix t).val) (rep t)) :=
  loop_fold_gen body ix n Inv rep G out
    (fun t hI hlt => by
      obtain ⟨j1, hj1, hj1v⟩ := usize_add_one (ix t) (by omega)
      obtain ⟨t', hb, hi, hr, hI'⟩ := hstep t hI hlt j1 hj1 hj1v
      exact ⟨t', hb, by rw [hi, hj1v], hr, hI'⟩) hend

/-- Discharge a `loop_fold_gen'` step: `loop_step [simp lemmas]`. -/
syntax "loop_step" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| loop_step [$ls,*]) => `(tactic|
      (intro t hI hlt j1 hj1 hj1v
       refine ⟨?t', ?hb, ?hi, ?hr, ?hI⟩
       case hb => (simp (disch := first | assumption | omega | simp_all | (simp_all; omega)) [hj1, vec_lt_len_iff, slice_lt_len_iff, hlt, hI, vec_index_usize_ok, slice_index_ok, $ls,*]; try rfl)
       all_goals (try simp [hj1v, $ls,*])
       all_goals (try simp_all [$ls,*])))

/-- Discharge a `loop_fold_gen'` end case. -/
syntax "loop_end" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| loop_end [$ls,*]) => `(tactic|
      (intro t hI hge
       refine ⟨?y, ?hb, ?hq⟩
       case hb => (simp [vec_lt_len_iff, slice_lt_len_iff, Nat.not_lt.mpr hge, hI, $ls,*]; try rfl)
       all_goals (try simp_all [$ls,*])))

end OsuProofs
