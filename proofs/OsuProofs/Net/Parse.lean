/-
`net::parse` (Rust) refines `OsuModel.Net.Parse` / `doubleParseChars` / `Parsing.*`.
Strings: the Rust `&[u32]` of Unicode scalar values ↦ the spec `List Char` (`strS`); theorems
assume the slice holds valid scalar values (`ValidStr`, true for every decoded `.osu` line).
List-suffix recursion in the spec ↦ a start index in the Rust (`(strS s).drop i`).
-/
import OsuProofs.Beatmap.Vector2
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Net.Parse

namespace OsuProofs
open OsuImpl

def chOf (u : U32) : Char := Char.ofNat u.val
def strS (s : Slice U32) : List Char := s.val.map chOf
def ValidStr (s : Slice U32) : Prop := ∀ u ∈ s.val, u.val.isValidChar

theorem chOf_toNat (u : U32) (h : u.val.isValidChar) : (chOf u).toNat = u.val := by
  simp [chOf, Char.ofNat, h, Char.ofNatAux]

theorem ofNat_toNat_valid (n : Nat) (h : n.isValidChar) : (Char.ofNat n).toNat = n := by
  simp [Char.ofNat, h, Char.ofNatAux]

theorem strS_length (s : Slice U32) : (strS s).length = s.val.length := by simp [strS]

theorem ValidStr.get {s : Slice U32} (h : ValidStr s) (i : Nat) (hi : i < s.val.length) :
    (s.val[i]'hi).val.isValidChar := h _ (List.getElem_mem hi)

theorem u32_eq_val (a b : U32) : a = b ↔ a.val = b.val :=
  ⟨fun h => h ▸ rfl, fun h => UScalar.eq_of_val_eq h⟩

theorem net.parse.is_white_refines (c : U32) (h : c.val.isValidChar) :
    net.parse.is_white c = ok (isWhite (chOf c)) := by
  have e := chOf_toNat c h
  unfold net.parse.is_white isWhite
  by_cases h1 : c.val = 32 <;> by_cases h2 : 9 ≤ c.val <;> by_cases h3 : c.val ≤ 13 <;>
    simp [e, h1, h2, h3, u32_eq_val]

theorem net.parse.is_unicode_white_space_refines (c : U32) (h : c.val.isValidChar) :
    net.parse.is_unicode_white_space c = ok (isUnicodeWhiteSpace (chOf c)) := by
  have e := chOf_toNat c h
  unfold net.parse.is_unicode_white_space isUnicodeWhiteSpace
  rw [net.parse.is_white_refines c h]
  by_cases hw : isWhite (chOf c) = true
  · simp [hw]
  · simp only [hw]
    by_cases h1 : 8192 ≤ c.val <;> by_cases h2 : c.val ≤ 8202 <;> simp [e, h1, h2, u32_eq_val]
    all_goals (rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]; omega)

theorem net.parse.is_digit_refines (c : U32) (h : c.val.isValidChar) :
    net.parse.is_digit c = ok (isDigit (chOf c)) := by
  have e := chOf_toNat c h
  unfold net.parse.is_digit isDigit
  have l1 : ('0' ≤ chOf c) ↔ 48 ≤ c.val := by
    rw [Char.le_def, UInt32.le_iff_toNat_le]; show '0'.toNat ≤ (chOf c).toNat ↔ _; rw [e]; rfl
  have l2 : (chOf c ≤ '9') ↔ c.val ≤ 57 := by
    rw [Char.le_def, UInt32.le_iff_toNat_le]; show (chOf c).toNat ≤ '9'.toNat ↔ _; rw [e]; rfl
  by_cases h1 : 48 ≤ c.val <;> by_cases h2 : c.val ≤ 57 <;> simp [l1, l2, h1, h2]

theorem toLower_toNat (c : Char) :
    c.toLower.toNat = if 65 ≤ c.toNat ∧ c.toNat ≤ 90 then c.toNat + 32 else c.toNat := by
  unfold Char.toLower
  split
  · rename_i h
    simp only [Char.toNat] at *
    simp [UInt32.le_iff_toNat_le, UInt32.toNat_add] at h ⊢
    rw [ite_eq_left_iff.mpr (fun h' => absurd h h')]; omega
  · rename_i h
    simp only [Char.toNat] at *
    simp [UInt32.le_iff_toNat_le] at h ⊢
    intro h1; exact h h1

theorem toUpper_toNat (c : Char) :
    c.toUpper.toNat = if 97 ≤ c.toNat ∧ c.toNat ≤ 122 then c.toNat - 32 else c.toNat := by
  unfold Char.toUpper
  split
  · rename_i h
    simp only [Char.toNat] at *
    simp [UInt32.le_iff_toNat_le, UInt32.toNat_add] at h ⊢
    rw [ite_eq_left_iff.mpr (fun h' => absurd h h')]; omega
  · rename_i h
    simp only [Char.toNat] at *
    simp [UInt32.le_iff_toNat_le] at h ⊢
    intro h1 h2; exact absurd (h h1) (by omega)

/-- Helper (spec: ASCII `Char.toLower`): value form. -/
theorem net.parse.ascii_lower_refines (c : U32) :
    ∃ r, net.parse.ascii_lower c = ok r ∧ r.val = (if 65 ≤ c.val ∧ c.val ≤ 90 then c.val + 32 else c.val) := by
  unfold net.parse.ascii_lower
  by_cases h1 : 65 ≤ c.val <;> by_cases h2 : c.val ≤ 90
  · obtain ⟨r, hr, hv⟩ := eq_ok_of_spec (U32.add_spec (x := c) (y := 32#u32) (by simp [U32.max_eq]; omega))
    exact ⟨r, by simp [h1, h2, hr], by simp [h1, h2] at hv ⊢; omega⟩
  all_goals exact ⟨c, by simp [h1, h2], by simp [h1, h2]⟩

/-- Helper (spec: ASCII `Char.toUpper`): value form. -/
theorem net.parse.ascii_upper_refines (c : U32) :
    ∃ r, net.parse.ascii_upper c = ok r ∧ r.val = (if 97 ≤ c.val ∧ c.val ≤ 122 then c.val - 32 else c.val) := by
  unfold net.parse.ascii_upper
  by_cases h1 : 97 ≤ c.val <;> by_cases h2 : c.val ≤ 122
  · obtain ⟨r, hr, hv, _⟩ := eq_ok_of_spec (U32.sub_spec (x := c) (y := 32#u32) (by simp; omega))
    exact ⟨r, by simp [h1, h2, hr], by simp [h1, h2] at hv ⊢; omega⟩
  all_goals exact ⟨c, by simp [h1, h2], by simp [h1, h2]⟩

theorem strS_drop (s : Slice U32) (j : Nat) (h : j < s.val.length) :
    (strS s).drop j = chOf (s.val[j]'h) :: (strS s).drop (j + 1) := by
  simp [strS, List.drop_eq_getElem_cons (by simpa using h : j < (s.val.map chOf).length)]

theorem slice_len_lt (s : Slice U32) : s.val.length ≤ Usize.max := Slice.length_ineq s

theorem net.parse.skip_white_refines (s : Slice U32) (hs : ValidStr s) (i : Usize) :
    ∃ j, net.parse.skip_white s i = ok j ∧ i.val ≤ j.val ∧ (i.val ≤ s.val.length → j.val ≤ s.val.length) ∧
      (strS s).drop j.val = dropWhile isWhite ((strS s).drop i.val) := by
  let T := dropWhile isWhite ((strS s).drop i.val)
  unfold net.parse.skip_white net.parse.skip_white_loop
  apply loop_ok _ (fun j => s.val.length - j.val)
    (fun j => i.val ≤ j.val ∧ (i.val ≤ s.val.length → j.val ≤ s.val.length) ∧ dropWhile isWhite ((strS s).drop j.val) = T)
  · rintro j ⟨hij, hjl, hT⟩
    have hl := slice_len_lt s
    by_cases hlt : j < Slice.len s
    · have hlt' : j.val < s.val.length := by simpa using hlt
      have hc := hs.get j.val hlt'
      rw [strS_drop s j.val hlt'] at hT
      by_cases hw : isWhite (chOf (s.val[j.val]'hlt')) = true
      · right
        obtain ⟨j1, hj1, hv⟩ := usize_add_one j (by omega)
        refine ⟨j1, by simp [net.parse.skip_white_loop.body, hlt, index_eq s j hlt',
          net.parse.is_white_refines _ hc, hw, hj1], ⟨by omega, by omega, ?_⟩, by omega⟩
        rw [hv]; simpa [dropWhile, hw] using hT
      · left
        refine ⟨j, by simp [net.parse.skip_white_loop.body, hlt, index_eq s j hlt',
          net.parse.is_white_refines _ hc, hw], hij, hjl, ?_⟩
        rw [strS_drop s j.val hlt']; simpa [dropWhile, hw] using hT
    · left
      have : s.val.length ≤ j.val := by have : ¬ j.val < s.val.length := by simpa using hlt
                                        omega
      refine ⟨j, by simp [net.parse.skip_white_loop.body, hlt], hij, hjl, ?_⟩
      have e : (strS s).drop j.val = [] := List.drop_eq_nil_of_le (by simp [strS_length]; omega)
      rw [e] at hT ⊢; simpa [dropWhile] using hT
  · exact ⟨le_refl _, id, rfl⟩

theorem net.parse.all_nul_refines (s : Slice U32) (hs : ValidStr s) (i : Usize) :
    net.parse.all_nul s i = ok (allNul ((strS s).drop i.val)) := by
  let T := allNul ((strS s).drop i.val)
  unfold net.parse.all_nul net.parse.all_nul_loop
  obtain ⟨y, hy, rfl⟩ := loop_ok (fun (x : Usize × Bool) => net.parse.all_nul_loop.body s x.1 x.2)
    (fun x => s.val.length - x.1.val) (fun x => (x.2 && allNul ((strS s).drop x.1.val)) = T) (fun y => y = T)
    (by
      rintro ⟨j, okf⟩ hT
      dsimp only at hT ⊢
      have hl := slice_len_lt s
      by_cases hlt : j < Slice.len s
      · right
        have hlt' : j.val < s.val.length := by simpa using hlt
        have hc := chOf_toNat _ (hs.get j.val hlt')
        rw [strS_drop s j.val hlt'] at hT
        obtain ⟨j1, hj1, hv⟩ := usize_add_one j (by omega)
        by_cases hz : (s.val[j.val]'hlt').val = 0
        · refine ⟨(j1, okf), by simp [net.parse.all_nul_loop.body, hlt, index_eq s j hlt', hj1, u32_eq_val, hz],
            ?_, by dsimp only; omega⟩
          dsimp only; rw [hv]; simpa [allNul, hc, hz] using hT
        · refine ⟨(j1, false), by simp [net.parse.all_nul_loop.body, hlt, index_eq s j hlt', hj1, u32_eq_val, hz],
            ?_, by dsimp only; omega⟩
          have hz' : ((s.val[j.val]'hlt').val == 0) = false := by simpa using hz
          dsimp only; simp [allNul, hc, hz'] at hT; exact hT.symm
      · left
        have : s.val.length ≤ j.val := by
          have : ¬ j.val < s.val.length := by simpa using hlt
          omega
        refine ⟨okf, by simp [net.parse.all_nul_loop.body, hlt], ?_⟩
        have e : (strS s).drop j.val = [] := List.drop_eq_nil_of_le (by simp [strS_length]; omega)
        rw [e] at hT; simpa [allNul] using hT) (i, true) (by simp [T])
  exact hy

def litS (lit : Slice U8) : List Char := lit.val.map (fun b => Char.ofNat b.val)

theorem eqIgnoreCase_eq (l1 l2 : List Char) : eqIgnoreCase l1 l2 =
    (decide (l1.length = l2.length) && (List.zipWith (fun a b => a.toLower == b.toLower) l1 l2).all id) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp [eqIgnoreCase]
  | cons a t ih => cases l2 <;> simp [eqIgnoreCase, ih, Bool.and_left_comm]

theorem lower_eq_iff (a b : Char) : (a.toLower == b.toLower) = decide ((if 65 ≤ a.toNat ∧ a.toNat ≤ 90 then a.toNat + 32 else a.toNat) =
    (if 65 ≤ b.toNat ∧ b.toNat ≤ 90 then b.toNat + 32 else b.toNat)) := by
  rw [← toLower_toNat, ← toLower_toNat]
  by_cases h : a.toLower = b.toLower
  · simp [h]
  · have h2 : a.toLower.toNat ≠ b.toLower.toNat := fun h' => h (Char.ext (UInt32.toNat_inj.mp h'))
    simp [h, h2]

theorem ascii_lower_val_eq (u : U32) (h : u.val.isValidChar) :
    (if 65 ≤ u.val ∧ u.val ≤ 90 then u.val + 32 else u.val) =
    (if 65 ≤ (chOf u).toNat ∧ (chOf u).toNat ≤ 90 then (chOf u).toNat + 32 else (chOf u).toNat) := by
  rw [chOf_toNat u h]

theorem byte_valid (b : U8) : (b.val).isValidChar := by
  have := b.hBounds; left; simp at this ⊢; omega

theorem net.parse.eq_ignore_case_refines (s : Slice U32) (hs : ValidStr s) (lo hi : Usize)
    (hlh : lo.val ≤ hi.val) (hhi : hi.val ≤ s.val.length) (lit : Slice U8) :
    net.parse.eq_ignore_case s lo hi lit =
      ok (eqIgnoreCase (((strS s).drop lo.val).take (hi.val - lo.val)) (litS lit)) := by
  let A := ((strS s).drop lo.val).take (hi.val - lo.val)
  let B := litS lit
  have hA : A.length = hi.val - lo.val := by simp [A, strS_length]; omega
  have hB : B.length = lit.val.length := by simp [B, litS]
  unfold net.parse.eq_ignore_case
  have hnlt : ¬ hi < lo := by intro h; have : hi.val < lo.val := h; omega
  obtain ⟨d, hd, hdv, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := hi) (y := lo) hlh)
  simp only [hnlt, ite_false, hd, bind_ok]
  rw [eqIgnoreCase_eq]
  change _ = ok (decide (A.length = B.length) && (List.zipWith (fun a b : Char => a.toLower == b.toLower) A B).all id)
  have hdl : (d = Slice.len lit) ↔ d.val = lit.val.length := by
    constructor
    · intro h; rw [h]; simp
    · intro h; apply UScalar.eq_of_val_eq; simp [h]
  by_cases hn : d.val = lit.val.length
  · have hne : (d != Slice.len lit) = false := by simp [hdl.mpr hn]
    simp only [hne, Bool.false_eq_true, ite_false]
    have hlen : A.length = B.length := by rw [hA, hB, ← hdv, hn]
    simp only [hlen, decide_true, Bool.true_and]
    let Z := List.zipWith (fun a b : Char => a.toLower == b.toLower) A B
    have hZ : Z.length = lit.val.length := by simp [Z, hlen, hB]
    unfold net.parse.eq_ignore_case_loop
    obtain ⟨y, hy, rfl⟩ := loop_ok (fun (x : Usize × Bool) => net.parse.eq_ignore_case_loop.body s lo lit x.1 x.2)
      (fun x => lit.val.length - x.1.val) (fun x => x.1.val ≤ lit.val.length ∧ x.2 = (Z.take x.1.val).all id)
      (fun y => y = Z.all id)
      (by
        rintro ⟨i, okf⟩ ⟨hi, hok⟩
        dsimp only at hi hok ⊢
        have hl := Slice.length_ineq lit
        by_cases hlt : i < Slice.len lit
        · right
          have hlt' : i.val < lit.val.length := by simpa using hlt
          have hsl := Slice.length_ineq s
          have hsi : lo.val + i.val < s.val.length := by omega
          obtain ⟨i2, hi2, hi2v⟩ := eq_ok_of_spec (Usize.add_spec (x := lo) (y := i) (by omega))
          have hi2l : i2.val < s.val.length := by omega
          obtain ⟨l1, hl1, hl1v⟩ := net.parse.ascii_lower_refines (s.val[i2.val]'hi2l)
          obtain ⟨l2, hl2, hl2v⟩ := net.parse.ascii_lower_refines (UScalar.cast .U32 (lit.val[i.val]'hlt'))
          obtain ⟨i8, hi8, hi8v⟩ := usize_add_one i (by omega)
          refine ⟨(i8, if l1 != l2 then false else okf), by
            simp [net.parse.eq_ignore_case_loop.body, hlt, hi2, index_eq s i2 hi2l, hl1, index_eq lit i hlt', lift,
              hl2, hi8], ⟨by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
          dsimp only
          have hzi : i.val < Z.length := by omega
          rw [hi8v, List.take_add_one, List.all_append, ← hok, List.getElem?_eq_getElem hzi]
          have hc1 := hs.get i2.val hi2l
          have hb := byte_valid (lit.val[i.val]'hlt')
          have hAi : A[i.val]'(by omega) = chOf (s.val[i2.val]'hi2l) := by
            simp [A, strS, hi2v]
          have hBi : B[i.val]'(by omega) = Char.ofNat (lit.val[i.val]'hlt').val := by simp [B, litS]
          simp only [Z, List.getElem_zipWith, hAi, hBi, Option.toList_some, List.all_cons, List.all_nil,
            Bool.and_true, id, lower_eq_iff]
          rw [chOf_toNat _ hc1, ofNat_toNat_valid _ hb]
          have hcast : (UScalar.cast .U32 (lit.val[i.val]'hlt')).val = (lit.val[i.val]'hlt').val := by simp
          rw [hcast] at hl2v
          by_cases he : l1.val = l2.val
          · have : (l1 != l2) = false := by simp [u32_eq_val, he]
            simp [this, ← hl1v, ← hl2v, he]
          · have : (l1 != l2) = true := by simp [u32_eq_val, he]
            simp [this, ← hl1v, ← hl2v, he]
        · left
          have : i.val = lit.val.length := by
            have : ¬ i.val < lit.val.length := by simpa using hlt
            omega
          refine ⟨okf, by simp [net.parse.eq_ignore_case_loop.body, hlt], ?_⟩
          rw [hok, this, ← hZ, List.take_length]) (0#usize, true) (by simp)
    exact hy
  · have hne : (d != Slice.len lit) = true := by simp [hdl]; exact hn
    simp only [hne, ite_true]
    have hlen : ¬ A.length = B.length := by rw [hA, hB, ← hdv]; exact hn
    simp only [hlen, decide_false, Bool.false_and]

end OsuProofs
