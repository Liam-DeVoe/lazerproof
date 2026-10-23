/-
`beatmap::dotnet` string helpers (Rust `&[u32]` scalar-value slices ↦ spec `String` via
`String.ofList (strS s)`): substring, trimming, prefix/equality tests, splitting.
-/
import OsuProofs.Beatmap.ControlPoints
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

theorem sub_str_loop_ok (s : Slice U32) (hi : Usize) (hh : hi.val ≤ s.val.length) :
    ∀ (out : alloc.vec.Vec U32) (i : Usize), i.val ≤ hi.val → out.val.length + (hi.val - i.val) ≤ s.val.length →
      ∃ v, beatmap.dotnet.sub_str_loop s hi out i = ok v ∧ v.val = out.val ++ (s.val.drop i.val).take (hi.val - i.val) := by
  intro out i hi0 hlen
  unfold beatmap.dotnet.sub_str_loop
  refine loop_ok _ (fun (x : alloc.vec.Vec U32 × Usize) => hi.val - x.2.val)
    (fun (x : alloc.vec.Vec U32 × Usize) => x.2.val ≤ hi.val ∧ x.1.val.length + (hi.val - x.2.val) ≤ s.val.length ∧
      x.1.val ++ (s.val.drop x.2.val).take (hi.val - x.2.val) = out.val ++ (s.val.drop i.val).take (hi.val - i.val))
    (fun (v : alloc.vec.Vec U32) => v.val = out.val ++ (s.val.drop i.val).take (hi.val - i.val)) ?_ (out, i)
    ⟨hi0, hlen, rfl⟩
  rintro ⟨o, j⟩ ⟨hj, hol, heq⟩
  dsimp only at hj hol heq ⊢
  by_cases hlt : j.val < hi.val
  · right
    have hlt' : j < hi := hlt
    have hjl : j.val < s.val.length := by omega
    obtain ⟨o1, ho1, ho1v⟩ := push_eq o (s.val[j.val]'hjl) (by have := s.property; have := usize_ge_32; omega)
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := s.property; omega)
    refine ⟨(o1, j1), by simp [beatmap.dotnet.sub_str_loop.body, hlt', index_eq s j hjl, ho1, hj1], ?_, by dsimp only; omega⟩
    refine ⟨by dsimp only; omega, by dsimp only; rw [ho1v]; simp; omega, ?_⟩
    dsimp only
    rw [ho1v, hj1v, ← heq]
    have e : hi.val - j.val = (hi.val - (j.val + 1)) + 1 := by omega
    have e2 : s.val.drop j.val = s.val[j.val] :: s.val.drop (j.val + 1) := List.drop_eq_getElem_cons hjl
    rw [e, e2, List.take_succ_cons]; simp only [List.append_assoc, List.singleton_append]
  · left
    have hlt' : ¬ j < hi := hlt
    refine ⟨o, by simp [beatmap.dotnet.sub_str_loop.body, hlt'], ?_⟩
    rw [← heq]
    have : hi.val - j.val = 0 := by omega
    simp [this]

theorem beatmap.dotnet.sub_str_refines (s : Slice U32) (lo hi : Usize) (hlh : lo.val ≤ hi.val)
    (hh : hi.val ≤ s.val.length) :
    ∃ v, beatmap.dotnet.sub_str s lo hi = ok v ∧ v.val = (s.val.drop lo.val).take (hi.val - lo.val) := by
  obtain ⟨v, hv, hvv⟩ := sub_str_loop_ok s hi hh (alloc.vec.Vec.new U32) lo hlh (by simp; omega)
  exact ⟨v, hv, by simpa using hvv⟩

/-- `char.IsWhiteSpace` on a scalar value. -/
def wsU (u : U32) : Bool := isWhiteSpace (chOf u)

theorem ws_eq (s : Slice U32) (hs : ValidStr s) (i : Nat) (hi : i < s.val.length) :
    beatmap.dotnet.is_white_space (s.val[i]'hi) = ok (wsU (s.val[i]'hi)) :=
  beatmap.dotnet.is_white_space_refines _ (hs _ (List.getElem_mem hi))

theorem trim_loop0 (s : Slice U32) (hs : ValidStr s) :
    ∀ lo : Usize, lo.val ≤ s.val.length → ∃ lo', beatmap.dotnet.trim_bounds_loop0 s lo = ok lo' ∧
      lo.val ≤ lo'.val ∧ lo'.val ≤ s.val.length ∧ s.val.drop lo'.val = (s.val.drop lo.val).dropWhile wsU := by
  intro lo hlo
  unfold beatmap.dotnet.trim_bounds_loop0
  refine loop_ok _ (fun (x : Usize) => s.val.length - x.val)
    (fun (x : Usize) => lo.val ≤ x.val ∧ x.val ≤ s.val.length ∧ (s.val.drop x.val).dropWhile wsU = (s.val.drop lo.val).dropWhile wsU)
    (fun (x : Usize) => lo.val ≤ x.val ∧ x.val ≤ s.val.length ∧ s.val.drop x.val = (s.val.drop lo.val).dropWhile wsU) ?_ lo
    ⟨le_refl _, hlo, rfl⟩
  intro x ⟨h1, h2, h3⟩
  by_cases hlt : x.val < s.val.length
  · have hlt' : x < Slice.len s := by show x.val < (Slice.len s).val; simpa using hlt
    have e2 : s.val.drop x.val = (s.val[x.val]'hlt) :: s.val.drop (x.val + 1) := List.drop_eq_getElem_cons hlt
    by_cases hw : wsU (s.val[x.val]'hlt) = true
    · right
      obtain ⟨x1, hx1, hx1v⟩ := usize_add_one x (by have := s.property; omega)
      refine ⟨x1, by simp [beatmap.dotnet.trim_bounds_loop0.body, hlt', index_eq s x hlt, ws_eq s hs _ hlt, hw, hx1],
        ⟨by omega, by omega, ?_⟩, by omega⟩
      rw [← h3, e2, List.dropWhile_cons_of_pos hw, hx1v]
    · left
      refine ⟨x, by simp [beatmap.dotnet.trim_bounds_loop0.body, hlt', index_eq s x hlt, ws_eq s hs _ hlt, hw],
        ⟨h1, h2, ?_⟩⟩
      rw [← h3, e2, List.dropWhile_cons_of_neg hw]
  · left
    have hlt' : ¬ x < Slice.len s := by show ¬ x.val < (Slice.len s).val; simpa using hlt
    refine ⟨x, by simp [beatmap.dotnet.trim_bounds_loop0.body, hlt'], ⟨h1, h2, ?_⟩⟩
    rw [← h3]
    have : s.val.drop x.val = [] := List.drop_eq_nil_of_le (by omega)
    rw [this]; rfl

/-- `TrimEnd` on a list of scalar values. -/
def rtrimU (l : List U32) : List U32 := (l.reverse.dropWhile wsU).reverse

theorem rtrimU_append (l : List U32) (a : U32) : rtrimU (l ++ [a]) = if wsU a then rtrimU l else l ++ [a] := by
  unfold rtrimU
  split
  · rename_i h; simp [List.dropWhile_cons_of_pos h]
  · rename_i h; simp [List.dropWhile_cons_of_neg h]

def segU (s : Slice U32) (lo hi : Nat) : List U32 := (s.val.drop lo).take (hi - lo)

theorem segU_snoc (s : Slice U32) (lo hi : Nat) (h : lo < hi) (hh : hi ≤ s.val.length) :
    segU s lo hi = segU s lo (hi - 1) ++ [s.val[hi - 1]'(by omega)] := by
  unfold segU
  have e : hi - lo = (hi - 1 - lo) + 1 := by omega
  rw [e, List.take_add_one]
  congr 1
  rw [List.getElem?_drop, List.getElem?_eq_getElem (by omega)]
  simp; congr 1; omega

theorem trim_loop1 (s : Slice U32) (hs : ValidStr s) (lo : Usize) :
    ∀ hi : Usize, lo.val ≤ hi.val → hi.val ≤ s.val.length → ∃ hi', beatmap.dotnet.trim_bounds_loop1 s lo hi = ok hi' ∧
      lo.val ≤ hi'.val ∧ hi'.val ≤ hi.val ∧ segU s lo.val hi'.val = rtrimU (segU s lo.val hi.val) := by
  intro hi h0 hhi
  unfold beatmap.dotnet.trim_bounds_loop1
  refine loop_ok _ (fun (x : Usize) => x.val)
    (fun (x : Usize) => lo.val ≤ x.val ∧ x.val ≤ hi.val ∧ rtrimU (segU s lo.val x.val) = rtrimU (segU s lo.val hi.val))
    (fun (x : Usize) => lo.val ≤ x.val ∧ x.val ≤ hi.val ∧ segU s lo.val x.val = rtrimU (segU s lo.val hi.val)) ?_ hi
    ⟨h0, le_refl _, rfl⟩
  intro x ⟨h1, h2, h3⟩
  by_cases hgt : lo.val < x.val
  · have hgt' : x > lo := hgt
    obtain ⟨x1, hx1, hx1v, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := x) (y := 1#usize) (by simp; omega))
    simp at hx1v
    have hl : x1.val < s.val.length := by omega
    have hsn := segU_snoc s lo.val x.val hgt (by omega)
    by_cases hw : wsU (s.val[x1.val]'hl) = true
    · right
      refine ⟨x1, by simp [beatmap.dotnet.trim_bounds_loop1.body, hgt', hx1, index_eq s x1 hl, ws_eq s hs _ hl, hw],
        ⟨by omega, by omega, ?_⟩, by omega⟩
      rw [← h3, hsn, rtrimU_append, hx1v]
      have : s.val[x.val - 1]'(by omega) = s.val[x1.val]'hl := by simp [hx1v]
      rw [this, if_pos hw]
    · left
      refine ⟨x, by simp [beatmap.dotnet.trim_bounds_loop1.body, hgt', hx1, index_eq s x1 hl, ws_eq s hs _ hl, hw],
        ⟨h1, h2, ?_⟩⟩
      rw [← h3, hsn, rtrimU_append]
      have : s.val[x.val - 1]'(by omega) = s.val[x1.val]'hl := by simp [hx1v]
      rw [this, if_neg hw]
  · left
    have hgt' : ¬ x > lo := hgt
    refine ⟨x, by simp [beatmap.dotnet.trim_bounds_loop1.body, hgt'], ⟨h1, h2, ?_⟩⟩
    rw [← h3]
    have : segU s lo.val x.val = [] := by unfold segU; simp; omega
    rw [this]; rfl

theorem trim_loop2 (s : Slice U32) (hs : ValidStr s) :
    ∀ hi : Usize, hi.val ≤ s.val.length → ∃ hi', beatmap.dotnet.trim_bounds_loop2 s hi = ok hi' ∧
      hi'.val ≤ hi.val ∧ segU s 0 hi'.val = rtrimU (segU s 0 hi.val) := by
  intro hi hhi
  unfold beatmap.dotnet.trim_bounds_loop2
  refine loop_ok _ (fun (x : Usize) => x.val)
    (fun (x : Usize) => x.val ≤ hi.val ∧ rtrimU (segU s 0 x.val) = rtrimU (segU s 0 hi.val))
    (fun (x : Usize) => x.val ≤ hi.val ∧ segU s 0 x.val = rtrimU (segU s 0 hi.val)) ?_ hi
    ⟨le_refl _, rfl⟩
  intro x ⟨h2, h3⟩
  by_cases hgt : 0 < x.val
  · have hgt' : x > 0#usize := by show (0#usize).val < x.val; simpa using hgt
    obtain ⟨x1, hx1, hx1v, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := x) (y := 1#usize) (by simp; omega))
    simp at hx1v
    have hl : x1.val < s.val.length := by omega
    have hsn := segU_snoc s 0 x.val hgt (by omega)
    by_cases hw : wsU (s.val[x1.val]'hl) = true
    · right
      refine ⟨x1, by simp [beatmap.dotnet.trim_bounds_loop2.body, hgt', hx1, index_eq s x1 hl, ws_eq s hs _ hl, hw],
        ⟨by omega, ?_⟩, by omega⟩
      rw [← h3, hsn, rtrimU_append, hx1v]
      have : s.val[x.val - 1]'(by omega) = s.val[x1.val]'hl := by simp [hx1v]
      rw [this, if_pos hw]
    · left
      refine ⟨x, by simp [beatmap.dotnet.trim_bounds_loop2.body, hgt', hx1, index_eq s x1 hl, ws_eq s hs _ hl, hw],
        ⟨h2, ?_⟩⟩
      rw [← h3, hsn, rtrimU_append]
      have : s.val[x.val - 1]'(by omega) = s.val[x1.val]'hl := by simp [hx1v]
      rw [this, if_neg hw]
  · left
    have hgt' : ¬ x > 0#usize := by show ¬ (0#usize).val < x.val; simpa using hgt
    refine ⟨x, by simp [beatmap.dotnet.trim_bounds_loop2.body, hgt'], ⟨h2, ?_⟩⟩
    rw [← h3]
    have : segU s 0 x.val = [] := by unfold segU; simp; omega
    rw [this]; rfl

theorem segU_full (s : Slice U32) (lo : Nat) : segU s lo s.val.length = s.val.drop lo := by
  unfold segU; rw [List.take_of_length_le]; simp

theorem beatmap.dotnet.trim_bounds_refines (s : Slice U32) (hs : ValidStr s) (st en : Bool) :
    ∃ lo hi, beatmap.dotnet.trim_bounds s st en = ok (lo, hi) ∧ lo.val ≤ hi.val ∧ hi.val ≤ s.val.length ∧
      segU s lo.val hi.val = (if en then rtrimU (if st then s.val.dropWhile wsU else s.val)
        else (if st then s.val.dropWhile wsU else s.val)) := by
  unfold beatmap.dotnet.trim_bounds
  have hlen : (Slice.len s).val = s.val.length := by simp
  cases st with
  | true =>
    obtain ⟨lo, hlo, h1, h2, h3⟩ := trim_loop0 s hs 0#usize (by simp)
    have h3' : s.val.drop lo.val = s.val.dropWhile wsU := by simpa using h3
    cases en with
    | true =>
      obtain ⟨hi, hhi, g1, g2, g3⟩ := trim_loop1 s hs lo (Slice.len s) (by rw [hlen]; exact h2) (by rw [hlen])
      refine ⟨lo, hi, by simp [hlo, hhi], g1, by rw [hlen] at g2; exact g2, ?_⟩
      rw [g3, hlen, segU_full, h3']; rfl
    | false =>
      refine ⟨lo, Slice.len s, by simp [hlo], by rw [hlen]; exact h2, by rw [hlen], ?_⟩
      rw [hlen, segU_full, h3']; rfl
  | false =>
    cases en with
    | true =>
      obtain ⟨hi, hhi, g2, g3⟩ := trim_loop2 s hs (Slice.len s) (by rw [hlen])
      refine ⟨0#usize, hi, by simp [hhi], by simp, by rw [hlen] at g2; exact g2, ?_⟩
      have : (0#usize : Usize).val = 0 := by simp
      rw [this, g3, hlen, segU_full]; simp
    | false =>
      refine ⟨0#usize, Slice.len s, by simp, by simp, by rw [hlen], ?_⟩
      have : (0#usize : Usize).val = 0 := by simp
      rw [this, hlen, segU_full]; simp

theorem strS_dropWhile (l : List U32) : (l.map chOf).dropWhile isWhiteSpace = (l.dropWhile wsU).map chOf := by
  rw [List.dropWhile_map]; rfl

theorem strS_rtrim (l : List U32) :
    ((l.map chOf).reverse.dropWhile isWhiteSpace).reverse = (rtrimU l).map chOf := by
  unfold rtrimU
  rw [← List.map_reverse, strS_dropWhile, List.map_reverse]

theorem trim_common (s : Slice U32) (hs : ValidStr s) (st en : Bool)
    (f : Slice U32 → Result (alloc.vec.Vec U32))
    (hf : ∀ s, f s = (do let (lo, hi) ← beatmap.dotnet.trim_bounds s st en; beatmap.dotnet.sub_str s lo hi)) :
    ∃ v, f s = ok v ∧ v.val = (if en then rtrimU (if st then s.val.dropWhile wsU else s.val)
        else (if st then s.val.dropWhile wsU else s.val)) := by
  obtain ⟨lo, hi, hb, h1, h2, h3⟩ := beatmap.dotnet.trim_bounds_refines s hs st en
  obtain ⟨v, hv, hvv⟩ := beatmap.dotnet.sub_str_refines s lo hi h1 h2
  exact ⟨v, by rw [hf, hb]; simp only [bind_ok]; exact hv, by rw [hvv, ← h3]; rfl⟩

theorem beatmap.dotnet.trim_refines (s : Slice U32) (hs : ValidStr s) :
    ∃ v, beatmap.dotnet.trim s = ok v ∧ String.ofList (v.val.map chOf) = trim (String.ofList (strS s)) := by
  obtain ⟨v, hv, hvv⟩ := trim_common s hs true true beatmap.dotnet.trim (fun _ => rfl)
  refine ⟨v, hv, ?_⟩
  simp only [if_true] at hvv
  rw [hvv]
  simp only [trim, trimEnd, trimStart, String.toList_ofList, strS]
  rw [strS_dropWhile, strS_rtrim]

theorem beatmap.dotnet.trim_start_refines (s : Slice U32) (hs : ValidStr s) :
    ∃ v, beatmap.dotnet.trim_start s = ok v ∧ String.ofList (v.val.map chOf) = trimStart (String.ofList (strS s)) := by
  obtain ⟨v, hv, hvv⟩ := trim_common s hs true false beatmap.dotnet.trim_start (fun _ => rfl)
  refine ⟨v, hv, ?_⟩
  simp only [if_true, Bool.false_eq_true, if_false] at hvv
  rw [hvv]
  simp only [trimStart, String.toList_ofList, strS]
  rw [strS_dropWhile]

theorem beatmap.dotnet.trim_end_refines (s : Slice U32) (hs : ValidStr s) :
    ∃ v, beatmap.dotnet.trim_end s = ok v ∧ String.ofList (v.val.map chOf) = trimEnd (String.ofList (strS s)) := by
  obtain ⟨v, hv, hvv⟩ := trim_common s hs false true beatmap.dotnet.trim_end (fun _ => rfl)
  refine ⟨v, hv, ?_⟩
  simp only [if_true, Bool.false_eq_true, if_false] at hvv
  rw [hvv]
  simp only [trimEnd, String.toList_ofList, strS]
  rw [strS_rtrim]

/-! ## equality / prefix tests -/

theorem u32_bne (a b : U32) : (a != b) = !(decide (a.val = b.val)) := by
  have e : a = b ↔ a.val = b.val := ⟨fun h => h ▸ rfl, fun h => UScalar.eq_of_val_eq h⟩
  by_cases h : a.val = b.val <;> simp [bne, e, h]

theorem cast_u8_val (b : U8) : (UScalar.cast .U32 b).val = b.val := by
  rw [UScalar.cast_val_eq]; have := b.hBounds; simp at this ⊢; omega

theorem take_succ_map {α β} (f : α → β) (l : List α) (k : Nat) (h : k < l.length) :
    (l.take (k + 1)).map f = (l.take k).map f ++ [f (l[k]'h)] := by
  simp only [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.map_append, List.map_cons,
    List.map_nil]

/-- `str_eq_loop`: `ok` stays true iff the first `len lit` scalar values agree. -/
theorem str_eq_loop_ok (s : Slice U32) (lit : Slice U8) (hn : lit.val.length ≤ s.val.length) :
    ∀ (i : Usize) (acc : Bool), i.val ≤ lit.val.length →
      acc = decide ((s.val.take i.val).map (·.val) = (lit.val.take i.val).map (·.val)) →
      beatmap.dotnet.str_eq_loop s lit i acc =
        ok (decide ((s.val.take lit.val.length).map (·.val) = lit.val.map (·.val))) := by
  intro i acc hi hacc
  unfold beatmap.dotnet.str_eq_loop
  have := loop_ok (fun (x : Usize × Bool) => beatmap.dotnet.str_eq_loop.body s lit x.1 x.2)
    (fun (x : Usize × Bool) => lit.val.length - x.1.val)
    (fun (x : Usize × Bool) => x.1.val ≤ lit.val.length ∧
      x.2 = decide ((s.val.take x.1.val).map (·.val) = (lit.val.take x.1.val).map (·.val)))
    (fun (r : Bool) => r = decide ((s.val.take lit.val.length).map (·.val) = lit.val.map (·.val)))
    (by
      rintro ⟨k, a⟩ ⟨hk, ha⟩
      dsimp only at hk ha ⊢
      by_cases hlt : k.val < lit.val.length
      · right
        have hlt' : k < Slice.len lit := by show k.val < (Slice.len lit).val; simpa using hlt
        have hks : k.val < s.val.length := by omega
        obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := lit.property; omega)
        refine ⟨(k1, a && decide ((s.val[k.val]'hks).val = (lit.val[k.val]'hlt).val)), ?_, ⟨by dsimp only; omega, ?_⟩,
          by dsimp only; omega⟩
        · simp only [beatmap.dotnet.str_eq_loop.body, hlt', if_true, index_eq s k hks, index_eq lit k hlt, lift,
            bind_ok, u32_bne, cast_u8_val, hk1]
          congr 2
          cases a <;> by_cases hc : (s.val[k.val]'hks).val = (lit.val[k.val]'hlt).val <;> simp [hc]
        · dsimp only
          rw [ha, hk1v, take_succ_map _ _ _ hks, take_succ_map _ _ _ hlt]
          by_cases hall : (s.val.take k.val).map (·.val) = (lit.val.take k.val).map (·.val)
          · simp [hall]
          · have : ¬ ((s.val.take k.val).map (·.val) ++ [(s.val[k.val]'hks).val] =
                (lit.val.take k.val).map (·.val) ++ [(lit.val[k.val]'hlt).val]) := by
              intro h; apply hall
              have := congrArg (List.take k.val) h
              simpa [List.take_append_of_le_length, List.length_map, List.length_take, show k.val ≤ s.val.length by omega,
                show k.val ≤ lit.val.length by omega] using this
            simp [hall, this]
      · left
        have hlt' : ¬ k < Slice.len lit := by show ¬ k.val < (Slice.len lit).val; simpa using hlt
        refine ⟨a, by simp [beatmap.dotnet.str_eq_loop.body, hlt'], ?_⟩
        have : k.val = lit.val.length := by omega
        rw [ha, this, List.take_length])
    (i, acc) ⟨hi, hacc⟩
  obtain ⟨y, hy, rfl⟩ := this
  exact hy

theorem strS_eq_litS_iff (s : Slice U32) (hs : ValidStr s) (lit : Slice U8) :
    strS s = litS lit ↔ s.val.map (·.val) = lit.val.map (·.val) := by
  unfold strS litS
  constructor
  · intro h
    have h1 := congrArg (List.map Char.toNat) h
    simp only [List.map_map] at h1
    have e1 : List.map (Char.toNat ∘ chOf) s.val = List.map (·.val) s.val :=
      List.map_congr_left (fun u hu => by simp [chOf_toNat u (hs u hu)])
    have e2 : List.map (Char.toNat ∘ fun b : U8 => Char.ofNat b.val) lit.val = List.map (·.val) lit.val :=
      List.map_congr_left (fun b _ => by simp [ofNat_toNat_valid _ (byte_valid b)])
    rw [e1, e2] at h1; exact h1
  · intro h
    have e1 : s.val.map chOf = (s.val.map (·.val)).map Char.ofNat := by simp [chOf]
    have e2 : lit.val.map (fun b : U8 => Char.ofNat b.val) = (lit.val.map (·.val)).map Char.ofNat := by simp
    rw [e1, e2, h]

theorem beatmap.dotnet.str_eq_refines (s : Slice U32) (hs : ValidStr s) (lit : Slice U8) :
    beatmap.dotnet.str_eq s lit = ok (decide (strS s = litS lit)) := by
  unfold beatmap.dotnet.str_eq
  dsimp only
  by_cases hl : s.val.length = lit.val.length
  · have hl' : (Slice.len s != Slice.len lit) = false := by
      rw [bne_eq_false_iff_eq]; apply UScalar.eq_of_val_eq; simp [hl]
    rw [hl']; simp only [Bool.false_eq_true, if_false]
    rw [str_eq_loop_ok s lit (by omega) 0#usize true (by simp) (by simp)]
    rw [← hl, List.take_length]
    congr 1; simp only [strS_eq_litS_iff s hs lit]
  · have hl' : (Slice.len s != Slice.len lit) = true := by
      rw [bne_iff_ne, ne_eq]; intro h; apply hl; have := congrArg UScalar.val h; simpa using this
    rw [hl']; simp only [if_true]
    congr 1; symm; simp only [decide_eq_false_iff_not]
    intro h; apply hl; have := congrArg List.length h; simpa [strS, litS] using this

end OsuProofs
