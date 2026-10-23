/-
`beatmap::dotnet` string helpers used by the decoder (Rust `&[u32]` ↦ spec `String` via `strS`):
`split`, `split_key_val`, `starts_with`, `ends_with`, `is_null_or_white_space`, `enum_try_parse`.
`String.splitOn` (legacy, byte positions) with a one-character separator is characterised on
`String.ofList l` as `List.splitOn` (`splitOn_char`), via position lemmas adapted from Batteries
(`BStr`, not in our olean set).
-/
import OsuProofs.Beatmap.Text
import OsuProofs.Beatmap.Names
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.deprecated false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

namespace BStr
open String
/-! Lemmas about the legacy `String` position API on `String.ofList l`, adapted from
Batteries `Batteries/Data/String/Lemmas.lean` (Apache 2.0, Bulhwi Cha, Mario Carneiro; Batteries'
String lemmas are not in our filtered olean set). -/
theorem add_utf8Size_pos : 0 < i + Char.utf8Size c :=
  Nat.add_pos_right _ (Char.utf8Size_pos c)

theorem ne_add_utf8Size_add_self : i ≠ n + Char.utf8Size c + i :=
  Nat.ne_of_lt (Nat.lt_add_of_pos_left add_utf8Size_pos)

theorem ne_self_add_add_utf8Size : i ≠ i + (n + Char.utf8Size c) :=
  Nat.ne_of_lt (Nat.lt_add_of_pos_right add_utf8Size_pos)

/-- The UTF-8 byte length of a list of characters. (This is intended for specification purposes.) -/
@[expose, inline] def utf8Len : List Char → Nat
  | []    => 0
  | c::cs => utf8Len cs + c.utf8Size

theorem utf8ByteSize_ofList (cs) : utf8ByteSize (String.ofList cs) = utf8Len cs := by
  induction cs with
  | nil => simp [utf8Len]
  | cons c cs ih =>
    rw [utf8Len, ← ih, ← List.singleton_append, String.ofList_append,
      utf8ByteSize_append, Nat.add_comm]
    congr
    rw [← size_toByteArray, String.toByteArray_ofList, List.utf8Encode_singleton,
      List.size_toByteArray, length_utf8EncodeChar]

@[simp] theorem utf8Len_nil : utf8Len [] = 0 := rfl

@[simp] theorem utf8Len_cons (c cs) : utf8Len (c :: cs) = utf8Len cs + c.utf8Size := rfl

@[simp] theorem utf8Len_append (cs₁ cs₂) : utf8Len (cs₁ ++ cs₂) = utf8Len cs₁ + utf8Len cs₂ := by
  induction cs₁ <;> simp [*, Nat.add_right_comm]

theorem utf8Len_reverseAux (cs₁ cs₂) :
    utf8Len (cs₁.reverseAux cs₂) = utf8Len cs₁ + utf8Len cs₂ := by
  induction cs₁ generalizing cs₂ <;> simp_all [← Nat.add_assoc, Nat.add_right_comm]

@[simp] theorem utf8Len_reverse (cs) : utf8Len cs.reverse = utf8Len cs := utf8Len_reverseAux ..

@[simp] theorem utf8Len_eq_zero : utf8Len l = 0 ↔ l = [] := by
  cases l <;> simp [Nat.ne_zero_iff_zero_lt.mpr (Char.utf8Size_pos _)]

section
open List
theorem utf8Len_le_of_sublist : ∀ {cs₁ cs₂}, cs₁ <+ cs₂ → utf8Len cs₁ ≤ utf8Len cs₂
  | _, _, .slnil => Nat.le_refl _
  | _, _, .cons _ h => Nat.le_trans (utf8Len_le_of_sublist h) (Nat.le_add_right ..)
  | _, _, .cons_cons _ h => Nat.add_le_add_right (utf8Len_le_of_sublist h) _

theorem utf8Len_le_of_infix (h : cs₁ <:+: cs₂) : utf8Len cs₁ ≤ utf8Len cs₂ :=
  utf8Len_le_of_sublist h.sublist

theorem utf8Len_le_of_suffix (h : cs₁ <:+ cs₂) : utf8Len cs₁ ≤ utf8Len cs₂ :=
  utf8Len_le_of_sublist h.sublist

theorem utf8Len_le_of_prefix (h : cs₁ <+: cs₂) : utf8Len cs₁ ≤ utf8Len cs₂ :=
  utf8Len_le_of_sublist h.sublist
end

@[simp] theorem rawEndPos_ofList (cs : List Char) : rawEndPos (ofList cs ) = ⟨utf8Len cs⟩ := by
  apply Pos.Raw.ext
  simp [String.rawEndPos, utf8ByteSize_ofList]

@[simp]
theorem utf8Len_toList (s : String) : utf8Len s.toList = s.utf8ByteSize := by
  rw [← utf8ByteSize_ofList, ofList_toList]
namespace Pos.Raw
theorem lt_addChar (p : Pos.Raw) (c : Char) : p < p + c :=
  Nat.lt_add_of_pos_right (Char.utf8Size_pos _)

theorem zero_ne_addChar {i : Pos.Raw} {c : Char} : 0 ≠ i + c := by
  intro h; have := congrArg Pos.Raw.byteIdx h; simp at this; have := Char.utf8Size_pos c; omega

end Pos.Raw
/--
Induction along the valid positions in a list of characters.
(This definition is intended only for specification purposes.)
-/
def utf8InductionOn {motive : List Char → Pos.Raw → Sort u}
    (s : List Char) (i p : Pos.Raw)
    (nil : ∀ i, motive [] i)
    (eq  : ∀ c cs, motive (c :: cs) p)
    (ind : ∀ (c : Char) cs i, i ≠ p → motive cs (i + c) → motive (c :: cs) i) :
    motive s i :=
  match s with
  | [] => nil i
  | c::cs =>
    if h : i = p then
      h ▸ eq c cs
    else ind c cs i h (utf8InductionOn cs (i + c) p nil eq ind)

theorem utf8GetAux_add_right_cancel (s : List Char) (i p n : Nat) :
    Pos.Raw.utf8GetAux s ⟨i + n⟩ ⟨p + n⟩ = Pos.Raw.utf8GetAux s ⟨i⟩ ⟨p⟩ := by
  apply utf8InductionOn s ⟨i⟩ ⟨p⟩ (motive := fun s i =>
    Pos.Raw.utf8GetAux s ⟨i.byteIdx + n⟩ ⟨p + n⟩ = Pos.Raw.utf8GetAux s i ⟨p⟩) <;>
  simp only [Pos.Raw.utf8GetAux, Char.reduceDefault, implies_true, ↓reduceIte, ne_eq,
    Pos.Raw.byteIdx_add_char]
  intro c cs ⟨i⟩ h ih
  simp only [Pos.Raw.ext_iff, Pos.Raw.add_char_eq] at h ⊢
  simp only [Nat.add_right_cancel_iff, h, ↓reduceIte]
  rw [Nat.add_right_comm]
  exact ih

theorem utf8GetAux_addChar_right_cancel (s : List Char) (i p : Pos.Raw) (c : Char) :
    Pos.Raw.utf8GetAux s (i + c) (p + c) = Pos.Raw.utf8GetAux s i p :=
  utf8GetAux_add_right_cancel ..

theorem utf8GetAux_of_valid (cs cs' : List Char) {i p : Nat} (hp : i + utf8Len cs = p) :
    Pos.Raw.utf8GetAux (cs ++ cs') ⟨i⟩ ⟨p⟩ = cs'.headD default := by
  match cs, cs' with
  | [], [] => rfl
  | [], c::cs' => simp [← hp, Pos.Raw.utf8GetAux]
  | c::cs, cs' =>
    simp only [List.cons_append, Pos.Raw.utf8GetAux, Char.reduceDefault]
    rw [ite_eq_right]
    case hnc => simp only [← hp, utf8Len_cons, Pos.Raw.ext_iff]; exact ne_self_add_add_utf8Size
    refine utf8GetAux_of_valid cs cs' ?_
    simpa [Nat.add_assoc, Nat.add_comm] using hp

theorem get_of_valid (cs cs' : List Char) :
    Pos.Raw.get (ofList (cs ++ cs')) ⟨utf8Len cs⟩ = cs'.headD default := by
  rw [Pos.Raw.get, String.toList_ofList]
  exact utf8GetAux_of_valid _ _ (Nat.zero_add _)

theorem get_cons_addChar (c : Char) (cs : List Char) (i : Pos.Raw) :
    (i + c).get (ofList (c :: cs)) = i.get (ofList cs) := by
  simp [Pos.Raw.get, Pos.Raw.utf8GetAux, Pos.Raw.zero_ne_addChar, utf8GetAux_addChar_right_cancel]
theorem next_of_valid' (cs cs' : List Char) :
    Pos.Raw.next (ofList (cs ++ cs')) ⟨utf8Len cs⟩ =
      ⟨utf8Len cs + (cs'.headD default).utf8Size⟩ := by
  simp only [Pos.Raw.next, get_of_valid]; rfl

theorem next_of_valid (cs : List Char) (c : Char) (cs' : List Char) :
    Pos.Raw.next (ofList (cs ++ c :: cs')) ⟨utf8Len cs⟩ =
      ⟨utf8Len cs + c.utf8Size⟩ := next_of_valid' ..

@[simp] theorem atEnd_iff (s : String) (p : Pos.Raw) : p.atEnd s ↔ s.rawEndPos ≤ p :=
  decide_eq_true_iff
theorem extract_go₂_add_right_cancel (s : List Char) (i e n : Nat) :
    String.Pos.Raw.extract.go₂ s ⟨i + n⟩ ⟨e + n⟩ = String.Pos.Raw.extract.go₂ s ⟨i⟩ ⟨e⟩ := by
  apply utf8InductionOn s ⟨i⟩ ⟨e⟩ (motive := fun s i =>
    String.Pos.Raw.extract.go₂ s ⟨i.byteIdx + n⟩ ⟨e + n⟩ = String.Pos.Raw.extract.go₂ s i ⟨e⟩)
    <;> simp only [ne_eq, String.Pos.Raw.extract.go₂, Pos.Raw.byteIdx_add_char, implies_true, ↓reduceIte]
  intro c cs ⟨i⟩ h ih
  simp only [Pos.Raw.ext_iff, Pos.Raw.add_char_eq] at h ⊢
  simp only [Nat.add_right_cancel_iff, h, ↓reduceIte, List.cons.injEq, true_and]
  rw [Nat.add_right_comm]
  exact ih

theorem extract_go₂_append_left : ∀ (s t : List Char) (i e : Nat),
    e = utf8Len s + i → String.Pos.Raw.extract.go₂ (s ++ t) ⟨i⟩ ⟨e⟩ = s
| [], t, i, _, rfl => by cases t <;> simp [String.Pos.Raw.extract.go₂]
| c :: cs, t, i, _, rfl => by
  simp only [List.cons_append, utf8Len_cons, String.Pos.Raw.extract.go₂, Pos.Raw.ext_iff, ne_add_utf8Size_add_self,
    ↓reduceIte, Pos.Raw.add_char_eq, List.cons.injEq, true_and]
  apply extract_go₂_append_left; rw [Nat.add_right_comm, Nat.add_assoc]

theorem extract_go₁_add_right_cancel (s : List Char) (i b e n : Nat) :
    String.Pos.Raw.extract.go₁ s ⟨i + n⟩ ⟨b + n⟩ ⟨e + n⟩ = String.Pos.Raw.extract.go₁ s ⟨i⟩ ⟨b⟩ ⟨e⟩ := by
  apply utf8InductionOn s ⟨i⟩ ⟨b⟩ (motive := fun s i =>
    String.Pos.Raw.extract.go₁ s ⟨i.byteIdx + n⟩ ⟨b + n⟩ ⟨e + n⟩ = String.Pos.Raw.extract.go₁ s i ⟨b⟩ ⟨e⟩)
    <;> simp only [ne_eq, String.Pos.Raw.extract.go₁, Pos.Raw.byteIdx_add_char, implies_true, ↓reduceIte]
  · intro c cs
    apply extract_go₂_add_right_cancel
  · intro c cs ⟨i⟩ h ih
    simp only [Pos.Raw.ext_iff, Pos.Raw.add_char_eq] at h ih ⊢
    simp only [Nat.add_right_cancel_iff, h, ↓reduceIte]
    rw [Nat.add_right_comm]
    exact ih

theorem extract_go₁_cons_addChar (c : Char) (cs : List Char) (b e : Pos.Raw) :
    String.Pos.Raw.extract.go₁ (c :: cs) 0 (b + c) (e + c) = String.Pos.Raw.extract.go₁ cs 0 b e := by
  simp only [String.Pos.Raw.extract.go₁, Pos.Raw.ext_iff, Pos.Raw.byteIdx_zero, Pos.Raw.byteIdx_add_char,
    Nat.ne_of_lt add_utf8Size_pos, ↓reduceIte]
  apply extract_go₁_add_right_cancel

theorem extract_go₁_append_right : ∀ (s t : List Char) (i b : Nat) (e : Pos.Raw),
    b = utf8Len s + i → String.Pos.Raw.extract.go₁ (s ++ t) ⟨i⟩ ⟨b⟩ e = String.Pos.Raw.extract.go₂ t ⟨b⟩ e
| [], t, i, _, e, rfl => by cases t <;> simp [String.Pos.Raw.extract.go₁, String.Pos.Raw.extract.go₂]
| c :: cs, t, i, _, e, rfl => by
  simp only [String.Pos.Raw.extract.go₁, utf8Len_cons, Pos.Raw.ext_iff, ne_add_utf8Size_add_self, ↓reduceIte,
    List.cons_append, Pos.Raw.add_char_eq]
  apply extract_go₁_append_right; rw [Nat.add_right_comm, Nat.add_assoc]

theorem extract_go₁_zero_utf8Len (s : List Char) : String.Pos.Raw.extract.go₁ s 0 0 ⟨utf8Len s⟩ = s :=
  (extract_go₁_append_right [] s 0 0 ⟨utf8Len s⟩ rfl).trans <| by
    simpa using extract_go₂_append_left s [] 0 (utf8Len s) rfl

theorem extract_of_valid (l m r : List Char) :
    Pos.Raw.extract (ofList (l ++ m ++ r)) ⟨utf8Len l⟩ ⟨utf8Len l + utf8Len m⟩ = ofList m := by
  simp only [Pos.Raw.extract]
  split
  · next h => rw [utf8Len_eq_zero.1 <| Nat.le_zero.1 <| Nat.add_le_add_iff_left.1 h, ofList_nil]
  · congr
    rw [List.append_assoc, String.toList_ofList,
      extract_go₁_append_right _ _ _ _ _ (by rfl)]
    apply extract_go₂_append_left; apply Nat.add_comm

end BStr

namespace BStr
open String

theorem toString_ofList (c : Char) : c.toString = String.ofList [c] := by
  apply String.ext; simp
theorem sep_get (c : Char) : Pos.Raw.get c.toString 0 = c := by
  have := get_of_valid [] [c]; rw [toString_ofList]; simpa using this
theorem sep_next (c : Char) : Pos.Raw.next c.toString 0 = ⟨c.utf8Size⟩ := by
  have := next_of_valid [] c []; rw [toString_ofList]; simpa using this
theorem sep_end (c : Char) : rawEndPos c.toString = ⟨c.utf8Size⟩ := by
  rw [toString_ofList, rawEndPos_ofList]; simp [utf8Len]

theorem splitOnAux_single (c : Char) : ∀ (r l m : List Char) (acc : List String),
    String.splitOnAux (ofList (l ++ m ++ r)) c.toString ⟨utf8Len l⟩ ⟨utf8Len l + utf8Len m⟩ 0 acc =
      acc.reverse ++ (List.splitOnPPrepend (· == c) r m.reverse).map ofList := by
  intro r
  induction r with
  | nil =>
    intro l m acc
    rw [String.splitOnAux]
    simp only [List.append_nil, atEnd_iff, rawEndPos_ofList, utf8Len_append]
    have := extract_of_valid l m []
    simp at this
    simp [this]
  | cons x r ih =>
    intro l m acc
    rw [String.splitOnAux]
    have hne : ¬ (rawEndPos (ofList (l ++ m ++ x :: r)) ≤ ⟨utf8Len l + utf8Len m⟩) := by
      rw [rawEndPos_ofList]; simp only [utf8Len_append, utf8Len_cons, Pos.Raw.le_iff]
      have := Char.utf8Size_pos x; omega
    have hget : Pos.Raw.get (ofList (l ++ m ++ x :: r)) ⟨utf8Len l + utf8Len m⟩ = x := by
      have := get_of_valid (l ++ m) (x :: r); simpa using this
    have hnext : Pos.Raw.next (ofList (l ++ m ++ x :: r)) ⟨utf8Len l + utf8Len m⟩ = ⟨utf8Len l + utf8Len m + x.utf8Size⟩ := by
      have := next_of_valid (l ++ m) x r; simpa using this
    have hsepend : (Pos.Raw.next c.toString 0).atEnd c.toString = true := by
      rw [sep_next]; unfold Pos.Raw.atEnd; rw [toString_ofList]; dsimp only; rw [utf8ByteSize_ofList]; simp [utf8Len]
    simp only [atEnd_iff, hne, decide_false, Bool.false_eq_true, if_false, hget, sep_get, hsepend, if_true]
    by_cases hx : x = c
    · subst hx
      simp only [beq_self_eq_true, if_true, hnext, sep_next]
      have hu : (⟨utf8Len l + utf8Len m + x.utf8Size⟩ : Pos.Raw).unoffsetBy ⟨x.utf8Size⟩ = ⟨utf8Len l + utf8Len m⟩ := by
        simp [Pos.Raw.unoffsetBy]
      rw [hu, show (⟨utf8Len l + utf8Len m⟩ : Pos.Raw) = ⟨utf8Len l + utf8Len m⟩ from rfl]
      rw [extract_of_valid l m (x :: r)]
      have := ih (l ++ m ++ [x]) [] (ofList m :: acc)
      simp only [List.append_nil, utf8Len_append, utf8Len_cons, utf8Len_nil, Nat.add_zero, Nat.zero_add,
        List.append_assoc, List.singleton_append, List.cons_append, List.nil_append, Nat.add_assoc] at this ⊢
      rw [this, List.splitOnPPrepend_cons_eq_if]
      simp
    · have hx' : (x == c) = false := by simpa using hx
      simp only [hx', Bool.false_eq_true, if_false]
      have hu : (⟨utf8Len l + utf8Len m⟩ : Pos.Raw).unoffsetBy 0 = ⟨utf8Len l + utf8Len m⟩ := by
        simp [Pos.Raw.unoffsetBy]
      rw [hu, hnext]
      have := ih l (m ++ [x]) acc
      simp only [List.append_nil, utf8Len_append, utf8Len_cons, utf8Len_nil, Nat.add_zero, Nat.zero_add,
        List.append_assoc, List.singleton_append, List.cons_append, List.nil_append, Nat.add_assoc] at this ⊢
      rw [this, List.splitOnPPrepend_cons_eq_if]
      simp [hx]
end BStr

theorem splitOn_char (l : List Char) (c : Char) :
    (String.ofList l).splitOn c.toString = (l.splitOn c).map String.ofList := by
  unfold String.splitOn
  have hne : (c.toString == "") = false := by
    rw [BStr.toString_ofList]; simp
  rw [hne]; simp only [Bool.false_eq_true, if_false]
  have := BStr.splitOnAux_single c l [] [] []
  simp only [List.nil_append, List.append_nil, BStr.utf8Len_nil, Nat.add_zero, List.reverse_nil] at this
  rw [List.splitOn_eq_splitOnP]; exact this

theorem chOf_beq_valid (x c : U32) (hx : x.val.isValidChar) (hc : c.val.isValidChar) :
    (chOf x == chOf c) = decide (x = c) := by
  by_cases h : x = c
  · simp [h]
  · have : chOf x ≠ chOf c := by
      intro e; apply h; apply UScalar.eq_of_val_eq
      have := congrArg Char.toNat e; rwa [chOf_toNat x hx, chOf_toNat c hc] at this
    simp [h, this]

abbrev SPX := alloc.vec.Vec (alloc.vec.Vec U32) × alloc.vec.Vec U32 × Usize

theorem beatmap.dotnet.split_refines (s : Slice U32) (hs : ValidStr s) (c : U32) (hc : c.val.isValidChar)
    (hn : s.val.length < Usize.max) :
    ∃ v, beatmap.dotnet.split s c = ok v ∧ (v.val.map strV).toArray = split (String.ofList (strS s)) (chOf c) ∧
      ∀ l ∈ v.val, ValidL l.val := by
  have hmax : s.val.length ≤ Usize.max := s.property
  let p := fun (x : Char) => x == chOf c
  obtain ⟨y, hy, hq⟩ := loop_ok
    (fun (x : SPX) => beatmap.dotnet.split_loop.body s c x.1 x.2.1 x.2.2)
    (fun x => s.val.length - x.2.2.val)
    (fun (x : SPX) => x.2.2.val ≤ s.val.length ∧ x.1.val.length + x.2.1.val.length ≤ x.2.2.val ∧
      (∀ l ∈ x.1.val, ValidL l.val) ∧ ValidL x.2.1.val ∧
      x.1.val.map (fun v => v.val.map chOf) ++ List.splitOnPPrepend p ((strS s).drop x.2.2.val) (x.2.1.val.map chOf).reverse
        = (strS s).splitOnP p)
    (fun (y : alloc.vec.Vec (alloc.vec.Vec U32) × alloc.vec.Vec U32) => y.1.val.length + y.2.val.length ≤ s.val.length ∧
      (∀ l ∈ y.1.val, ValidL l.val) ∧ ValidL y.2.val ∧
      y.1.val.map (fun v => v.val.map chOf) ++ [y.2.val.map chOf] = (strS s).splitOnP p)
    (by
      rintro ⟨out, cur, i⟩ ⟨hi, hl, hvo, hvc, heq⟩
      dsimp only at hi hl hvo hvc heq ⊢
      by_cases hlt : i.val < s.val.length
      · right
        have hlt' : i < Slice.len s := by show i.val < (Slice.len s).val; simpa using hlt
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
        have hx := hs _ (List.getElem_mem hlt)
        have hd : (strS s).drop i.val = chOf (s.val[i.val]'hlt) :: (strS s).drop (i.val + 1) := by
          unfold strS; rw [List.drop_eq_getElem_cons (by simpa using hlt)]; simp
        by_cases he : s.val[i.val]'hlt = c
        · obtain ⟨o1, ho1, ho1v⟩ := push_eq out cur (by omega)
          refine ⟨(o1, alloc.vec.Vec.new U32, i1), by simp [beatmap.dotnet.split_loop.body, hlt', index_eq s i hlt, he, ho1, hi1],
            ⟨by dsimp only; omega, by dsimp only; rw [ho1v]; simp [alloc.vec.Vec.new]; omega, ?_, by simp [ValidL, alloc.vec.Vec.new], ?_⟩,
            by dsimp only; omega⟩
          · intro l hl; rw [ho1v] at hl; simp at hl; rcases hl with hl | hl
            · exact hvo l hl
            · rw [hl]; exact hvc
          · dsimp only; rw [← heq, hd, hi1v, List.splitOnPPrepend_cons_eq_if, ho1v]
            simp [p, he, alloc.vec.Vec.new]
        · obtain ⟨c1, hc1, hc1v⟩ := push_eq cur (s.val[i.val]'hlt) (by omega)
          refine ⟨(out, c1, i1), by simp [beatmap.dotnet.split_loop.body, hlt', index_eq s i hlt, he, hc1, hi1],
            ⟨by dsimp only; omega, by dsimp only; rw [hc1v]; simp; omega, hvo, ?_, ?_⟩, by dsimp only; omega⟩
          · intro u hu; rw [hc1v] at hu; simp at hu; rcases hu with hu | hu
            · exact hvc u hu
            · rw [hu]; exact hx
          · dsimp only; rw [← heq, hd, hi1v, List.splitOnPPrepend_cons_eq_if, hc1v]
            have : (chOf (s.val[i.val]'hlt) == chOf c) = false := by rw [chOf_beq_valid _ _ hx hc]; simp [he]
            simp [p, this]
      · left
        have hlt' : ¬ i < Slice.len s := by show ¬ i.val < (Slice.len s).val; simpa using hlt
        refine ⟨(out, cur), by simp [beatmap.dotnet.split_loop.body, hlt'], by dsimp only; omega, hvo, hvc, ?_⟩
        rw [← heq]
        have : (strS s).drop i.val = [] := List.drop_eq_nil_of_le (by simp [strS]; omega)
        rw [this]; simp)
    (alloc.vec.Vec.new _, alloc.vec.Vec.new U32, 0#usize)
    ⟨by simp, by simp [alloc.vec.Vec.new], by simp [alloc.vec.Vec.new], by simp [ValidL, alloc.vec.Vec.new],
      by simp [alloc.vec.Vec.new]⟩
  obtain ⟨o, cu⟩ := y
  obtain ⟨hl, hvo, hvc, heq⟩ := hq
  dsimp only at hl hvo hvc heq
  obtain ⟨w, hw, hwv⟩ := push_eq o cu (by omega)
  refine ⟨w, ?_, ?_, ?_⟩
  · unfold beatmap.dotnet.split beatmap.dotnet.split_loop
    simp only [hy, bind_ok]; exact hw
  · unfold split
    rw [splitOn_char, List.splitOn_eq_splitOnP, ← heq, hwv]
    simp [strV, Function.comp_def]
  · intro l hl; rw [hwv] at hl; simp at hl; rcases hl with hl | hl
    · exact hvo l hl
    · rw [hl]; exact hvc

/-- valid scalar values: `Char.ofNat` round-trips -/
theorem map_toNat_strS (l : List U32) (h : ∀ u ∈ l, u.val.isValidChar) :
    (l.map chOf).map Char.toNat = l.map (·.val) := by
  simp only [List.map_map]; exact List.map_congr_left (fun u hu => by simp [chOf_toNat u (h u hu)])
theorem map_toNat_litS (l : List U8) :
    (l.map (fun b : U8 => Char.ofNat b.val)).map Char.toNat = l.map (·.val) := by
  simp only [List.map_map]; exact List.map_congr_left (fun b _ => by simp [ofNat_toNat_valid _ (byte_valid b)])

theorem chars_eq_iff (a : List U32) (ha : ∀ u ∈ a, u.val.isValidChar) (b : List U8) :
    a.map chOf = b.map (fun x : U8 => Char.ofNat x.val) ↔ a.map (·.val) = b.map (·.val) := by
  constructor
  · intro h; have := congrArg (List.map Char.toNat) h; rwa [map_toNat_strS a ha, map_toNat_litS] at this
  · intro h
    have e1 : a.map chOf = (a.map (·.val)).map Char.ofNat := by simp [chOf]
    have e2 : b.map (fun x : U8 => Char.ofNat x.val) = (b.map (·.val)).map Char.ofNat := by simp
    rw [e1, e2, h]

theorem cmp_loop_inv (s : Slice U32) (lit : Slice U8) (off k : Nat) (hk : k < lit.val.length)
    (hs : off + k < s.val.length) (a : Bool)
    (ha : a = decide (((s.val.drop off).take k).map (·.val) = (lit.val.take k).map (·.val))) :
    (a && decide ((s.val[off + k]'hs).val = (lit.val[k]'hk).val)) =
      decide (((s.val.drop off).take (k+1)).map (·.val) = (lit.val.take (k+1)).map (·.val)) := by
  have hs' : k < (s.val.drop off).length := by simp; omega
  have hget : (s.val.drop off)[k]'hs' = s.val[off + k]'hs := by simp
  rw [take_succ_map _ _ _ hs', take_succ_map _ _ _ hk, hget, ha]
  by_cases h1 : ((s.val.drop off).take k).map (·.val) = (lit.val.take k).map (·.val)
  · rw [h1]; by_cases h2 : (s.val[off + k]'hs).val = (lit.val[k]'hk).val <;> simp [h2]
  · have : ¬ (((s.val.drop off).take k).map (·.val) ++ [(s.val[off + k]'hs).val] =
        (lit.val.take k).map (·.val) ++ [(lit.val[k]'hk).val]) := by
      intro h; exact h1 (List.append_inj' h rfl).1
    simp only [h1, this, decide_false, Bool.false_and]

theorem starts_with_loop_ok (s : Slice U32) (lit : Slice U8) (hn : lit.val.length ≤ s.val.length) :
    ∀ (i : Usize) (acc : Bool), i.val ≤ lit.val.length →
      acc = decide (((s.val.drop 0).take i.val).map (·.val) = (lit.val.take i.val).map (·.val)) →
      beatmap.dotnet.starts_with_loop s lit i acc =
        ok (decide (((s.val.drop 0).take lit.val.length).map (·.val) = lit.val.map (·.val))) := by
  intro i acc hi hacc
  unfold beatmap.dotnet.starts_with_loop
  have := loop_ok (fun (x : Usize × Bool) => beatmap.dotnet.starts_with_loop.body s lit x.1 x.2)
    (fun (x : Usize × Bool) => lit.val.length - x.1.val)
    (fun (x : Usize × Bool) => x.1.val ≤ lit.val.length ∧
      x.2 = decide (((s.val.drop 0).take x.1.val).map (·.val) = (lit.val.take x.1.val).map (·.val)))
    (fun (r : Bool) => r = decide (((s.val.drop 0).take lit.val.length).map (·.val) = lit.val.map (·.val)))
    (by
      rintro ⟨k, a⟩ ⟨hk, ha⟩
      dsimp only at hk ha ⊢
      by_cases hlt : k.val < lit.val.length
      · right
        have hlt' : k < Slice.len lit := by show k.val < (Slice.len lit).val; simpa using hlt
        have hks : 0 + k.val < s.val.length := by omega
        obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := lit.property; omega)
        refine ⟨(k1, a && decide ((s.val[0 + k.val]'hks).val = (lit.val[k.val]'hlt).val)), ?_, ⟨by dsimp only; omega, ?_⟩,
          by dsimp only; omega⟩
        · simp only [beatmap.dotnet.starts_with_loop.body, hlt', if_true, index_eq s k (by omega), index_eq lit k hlt, lift,
            bind_ok, u32_bne, cast_u8_val, hk1]
          congr 2
          cases a <;> by_cases hc : (s.val[k.val]'(by omega)).val = (lit.val[k.val]'hlt).val <;> simp [hc]
        · dsimp only; rw [hk1v]; exact cmp_loop_inv s lit 0 k.val hlt hks a ha
      · left
        have hlt' : ¬ k < Slice.len lit := by show ¬ k.val < (Slice.len lit).val; simpa using hlt
        refine ⟨a, by simp [beatmap.dotnet.starts_with_loop.body, hlt'], ?_⟩
        have : k.val = lit.val.length := by omega
        rw [ha, this, List.take_length])
    (i, acc) ⟨hi, hacc⟩
  obtain ⟨y, hy, rfl⟩ := this
  exact hy

theorem ends_with_loop_ok (s : Slice U32) (lit : Slice U8) (off : Usize) (hn : off.val + lit.val.length ≤ s.val.length) :
    ∀ (i : Usize) (acc : Bool), i.val ≤ lit.val.length →
      acc = decide (((s.val.drop off.val).take i.val).map (·.val) = (lit.val.take i.val).map (·.val)) →
      beatmap.dotnet.ends_with_loop s lit off i acc =
        ok (decide (((s.val.drop off.val).take lit.val.length).map (·.val) = lit.val.map (·.val))) := by
  intro i acc hi hacc
  unfold beatmap.dotnet.ends_with_loop
  have := loop_ok (fun (x : Usize × Bool) => beatmap.dotnet.ends_with_loop.body s lit off x.1 x.2)
    (fun (x : Usize × Bool) => lit.val.length - x.1.val)
    (fun (x : Usize × Bool) => x.1.val ≤ lit.val.length ∧
      x.2 = decide (((s.val.drop off.val).take x.1.val).map (·.val) = (lit.val.take x.1.val).map (·.val)))
    (fun (r : Bool) => r = decide (((s.val.drop off.val).take lit.val.length).map (·.val) = lit.val.map (·.val)))
    (by
      rintro ⟨k, a⟩ ⟨hk, ha⟩
      dsimp only at hk ha ⊢
      by_cases hlt : k.val < lit.val.length
      · right
        have hlt' : k < Slice.len lit := by show k.val < (Slice.len lit).val; simpa using hlt
        have hks : off.val + k.val < s.val.length := by omega
        obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := lit.property; omega)
        obtain ⟨o, ho, hov⟩ := usize_add_k off k (by have := s.property; omega)
        refine ⟨(k1, a && decide ((s.val[off.val + k.val]'hks).val = (lit.val[k.val]'hlt).val)), ?_, ⟨by dsimp only; omega, ?_⟩,
          by dsimp only; omega⟩
        · have e : s.val[o.val]'(by omega) = s.val[off.val + k.val]'hks := by simp [hov]
          simp only [beatmap.dotnet.ends_with_loop.body, hlt', if_true, ho, index_eq s o (by omega), e, index_eq lit k hlt, lift,
            bind_ok, u32_bne, cast_u8_val, hk1]
          congr 2
          cases a <;> by_cases hc : (s.val[off.val + k.val]'hks).val = (lit.val[k.val]'hlt).val <;> simp [hc]
        · dsimp only; rw [hk1v]; exact cmp_loop_inv s lit off.val k.val hlt hks a ha
      · left
        have hlt' : ¬ k < Slice.len lit := by show ¬ k.val < (Slice.len lit).val; simpa using hlt
        refine ⟨a, by simp [beatmap.dotnet.ends_with_loop.body, hlt'], ?_⟩
        have : k.val = lit.val.length := by omega
        rw [ha, this, List.take_length])
    (i, acc) ⟨hi, hacc⟩
  obtain ⟨y, hy, rfl⟩ := this
  exact hy

theorem prefix_chars_iff (s : Slice U32) (hs : ValidStr s) (lit : Slice U8) (hn : lit.val.length ≤ s.val.length) :
    litS lit <+: strS s ↔ (s.val.take lit.val.length).map (·.val) = lit.val.map (·.val) := by
  rw [List.prefix_iff_eq_take]
  have : (strS s).take (litS lit).length = (s.val.take lit.val.length).map chOf := by simp [strS, litS, List.map_take]
  rw [this, eq_comm]; exact chars_eq_iff _ (fun u hu => hs u (List.mem_of_mem_take hu)) lit.val

theorem suffix_chars_iff (s : Slice U32) (hs : ValidStr s) (lit : Slice U8) (hn : lit.val.length ≤ s.val.length) :
    litS lit <:+ strS s ↔ (s.val.drop (s.val.length - lit.val.length)).map (·.val) = lit.val.map (·.val) := by
  rw [List.suffix_iff_eq_drop]
  have : (strS s).drop ((strS s).length - (litS lit).length) = (s.val.drop (s.val.length - lit.val.length)).map chOf := by
    simp [strS, litS, List.map_drop]
  rw [this, eq_comm]; exact chars_eq_iff _ (fun u hu => hs u (List.mem_of_mem_drop hu)) lit.val

theorem beatmap.dotnet.starts_with_refines (s : Slice U32) (hs : ValidStr s) (lit : Slice U8) :
    beatmap.dotnet.starts_with s lit = ok ((String.ofList (strS s)).startsWith (String.ofList (litS lit))) := by
  unfold beatmap.dotnet.starts_with
  have hspec : (String.ofList (strS s)).startsWith (String.ofList (litS lit)) = decide (litS lit <+: strS s) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff]; unfold String.startsWith
    rw [String.Slice.startsWith_string_iff, String.copy_toSlice, String.toList_ofList, String.toList_ofList]
  rw [hspec]
  by_cases hl : s.val.length < lit.val.length
  · have hl' : Slice.len s < Slice.len lit := by show (Slice.len s).val < (Slice.len lit).val; simpa using hl
    simp only [hl', if_true]
    congr 1; symm; simp only [decide_eq_false_iff_not]
    intro h; have := h.length_le; simp [strS, litS] at this; omega
  · have hl' : ¬ Slice.len s < Slice.len lit := by show ¬ (Slice.len s).val < (Slice.len lit).val; simpa using hl
    simp only [hl', if_false]
    rw [starts_with_loop_ok s lit (by omega) 0#usize true (by simp) (by simp)]
    congr 1; simp only [List.drop_zero, prefix_chars_iff s hs lit (by omega)]

theorem beatmap.dotnet.ends_with_refines (s : Slice U32) (hs : ValidStr s) (lit : Slice U8) :
    beatmap.dotnet.ends_with s lit = ok ((String.ofList (strS s)).endsWith (String.ofList (litS lit))) := by
  unfold beatmap.dotnet.ends_with
  have hspec : (String.ofList (strS s)).endsWith (String.ofList (litS lit)) = decide (litS lit <:+ strS s) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff]; unfold String.endsWith
    rw [String.Slice.endsWith_string_iff, String.copy_toSlice, String.toList_ofList, String.toList_ofList]
  rw [hspec]
  by_cases hl : s.val.length < lit.val.length
  · have hl' : Slice.len s < Slice.len lit := by show (Slice.len s).val < (Slice.len lit).val; simpa using hl
    simp only [hl', if_true]
    congr 1; symm; simp only [decide_eq_false_iff_not]
    intro h; have := h.length_le; simp [strS, litS] at this; omega
  · have hl' : ¬ Slice.len s < Slice.len lit := by show ¬ (Slice.len s).val < (Slice.len lit).val; simpa using hl
    simp only [hl', if_false]
    obtain ⟨off, hoff, hoffv, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := Slice.len s) (y := Slice.len lit) (by simp; omega))
    simp at hoffv
    simp only [hoff, bind_ok]
    rw [ends_with_loop_ok s lit off (by omega) 0#usize true (by simp) (by simp)]
    congr 1; apply decide_eq_decide.mpr
    rw [suffix_chars_iff s hs lit (by omega), hoffv, List.take_of_length_le (by simp; omega)]

theorem ds_deref_val (v : alloc.vec.Vec U32) : (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref]

theorem validStr_of (v : alloc.vec.Vec U32) (h : ValidL v.val) : ValidStr (alloc.vec.Vec.deref v) := by
  intro u hu; rw [ds_deref_val] at hu; exact h u hu

theorem skv_loop_ok (line : Slice U32) (sep : U32) :
    ∃ i f, beatmap.dotnet.split_key_val_loop line sep 0#usize false = ok (i, f) ∧ i.val ≤ line.val.length ∧
      (∀ j, j < i.val → line.val[j]? ≠ some sep) ∧
      (f = true → ∃ h : i.val < line.val.length, line.val[i.val]'h = sep) ∧ (f = false → i.val = line.val.length) := by
  unfold beatmap.dotnet.split_key_val_loop
  obtain ⟨y, hy, hq⟩ := loop_ok (fun (x : Usize × Bool) => beatmap.dotnet.split_key_val_loop.body line sep x.1 x.2)
    (fun x => line.val.length - x.1.val + (if x.2 then 0 else 1))
    (fun x => x.1.val ≤ line.val.length ∧ (∀ j, j < x.1.val → line.val[j]? ≠ some sep) ∧
      (x.2 = true → ∃ h : x.1.val < line.val.length, line.val[x.1.val]'h = sep))
    (fun y => y.1.val ≤ line.val.length ∧ (∀ j, j < y.1.val → line.val[j]? ≠ some sep) ∧
      (y.2 = true → ∃ h : y.1.val < line.val.length, line.val[y.1.val]'h = sep) ∧ (y.2 = false → y.1.val = line.val.length))
    (by
      rintro ⟨i, f⟩ ⟨hi, hne, hf⟩
      dsimp only at hi hne hf ⊢
      cases f with
      | true => left; exact ⟨(i, true), by simp [beatmap.dotnet.split_key_val_loop.body], hi, hne, hf, by simp⟩
      | false =>
        by_cases hlt : i.val < line.val.length
        · right
          have hlt' : i < Slice.len line := by show i.val < (Slice.len line).val; simpa using hlt
          by_cases he : line.val[i.val]'hlt = sep
          · exact ⟨(i, true), by simp [beatmap.dotnet.split_key_val_loop.body, hlt', index_eq line i hlt, he],
              ⟨hi, hne, fun _ => ⟨hlt, he⟩⟩, by simp⟩
          · obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := line.property; omega)
            refine ⟨(i1, false), by simp [beatmap.dotnet.split_key_val_loop.body, hlt', index_eq line i hlt, he, hi1],
              ⟨by dsimp only; omega, ?_, by simp⟩, by dsimp only; omega⟩
            intro j hj; dsimp only at hj
            by_cases hji : j = i.val
            · subst hji; rw [List.getElem?_eq_getElem hlt]; simpa using he
            · exact hne j (by omega)
        · left
          have hlt' : ¬ i < Slice.len line := by show ¬ i.val < (Slice.len line).val; simpa using hlt
          exact ⟨(i, false), by simp [beatmap.dotnet.split_key_val_loop.body, hlt'], hi, hne, by simp, fun _ => by dsimp only; omega⟩)
    (0#usize, false) ⟨by simp, by simp, by simp⟩
  obtain ⟨i, f⟩ := y
  exact ⟨i, f, hy, hq⟩

theorem not_mem_chars (l : List U32) (hl : ∀ u ∈ l, u.val.isValidChar) (c : U32) (hc : c.val.isValidChar)
    (h : ∀ j, j < l.length → l[j]? ≠ some c) : chOf c ∉ l.map chOf := by
  intro hm
  obtain ⟨u, hu, he⟩ := List.mem_map.mp hm
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
  have : l[j] = c := by
    apply UScalar.eq_of_val_eq
    have := congrArg Char.toNat he
    rwa [chOf_toNat _ (hl _ hu), chOf_toNat c hc] at this
  exact h j hj (by rw [List.getElem?_eq_getElem hj, this])

theorem mem_dropWhile_sub {α} (p : α → Bool) (l : List α) (u : α) (h : u ∈ l.dropWhile p) : u ∈ l :=
  (List.dropWhile_suffix p).subset h
theorem mem_rtrimU_sub (l : List U32) (u : U32) (h : u ∈ rtrimU l) : u ∈ l := by
  unfold rtrimU at h; rw [List.mem_reverse] at h; exact List.mem_reverse.mp (mem_dropWhile_sub _ _ _ h)

theorem trim_valid (s : Slice U32) (hs : ValidStr s) :
    ∃ v, beatmap.dotnet.trim s = ok v ∧ String.ofList (v.val.map chOf) = trim (String.ofList (strS s)) ∧ ValidL v.val := by
  obtain ⟨v, hv, hvv⟩ := beatmap.dotnet.trim_refines s hs
  obtain ⟨v', hv', hvv'⟩ := trim_common s hs true true beatmap.dotnet.trim (fun _ => rfl)
  have e : v' = v := by rw [hv] at hv'; simpa using hv'.symm
  subst e
  refine ⟨v', hv, hvv, fun u hu => hs u ?_⟩
  simp only [if_true] at hvv'; rw [hvv'] at hu
  exact mem_dropWhile_sub _ _ _ (mem_rtrimU_sub _ _ hu)

theorem beatmap.dotnet.split_key_val_refines (line : Slice U32) (hs : ValidStr line) (sep : U32)
    (hsep : sep.val.isValidChar) :
    ∃ k v, beatmap.dotnet.split_key_val line sep = ok (k, v) ∧
      (strV k, strV v) = splitKeyVal (String.ofList (strS line)) (chOf sep) ∧ ValidL k.val ∧ ValidL v.val := by
  have hmax : line.val.length ≤ Usize.max := line.property
  obtain ⟨i, f, hl, hi, hne, hf, hnf⟩ := skv_loop_ok line sep
  unfold beatmap.dotnet.split_key_val splitKeyVal
  simp only [hl, bind_ok]
  rw [splitOn_char]
  cases f with
  | false =>
    have hi' := hnf rfl
    obtain ⟨t, ht, htv, htval⟩ := trim_valid line hs
    have hnm : chOf sep ∉ strS line := not_mem_chars line.val hs sep hsep (by rw [← hi']; exact hne)
    rw [List.splitOn_eq_singleton hnm]
    refine ⟨t, alloc.vec.Vec.new U32, by simp [ht], ?_, htval, by simp [ValidL, alloc.vec.Vec.new]⟩
    simp [strV, htv, alloc.vec.Vec.new]
  | true =>
    obtain ⟨hlt, heq⟩ := hf rfl
    obtain ⟨k, hk, hkv⟩ := beatmap.dotnet.sub_str_refines line 0#usize i (by simp) hi
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
    obtain ⟨v, hv, hvv⟩ := beatmap.dotnet.sub_str_refines line i1 (Slice.len line) (by simp; omega) (by simp)
    have hkv' : k.val = line.val.take i.val := by simpa using hkv
    have hvv' : v.val = line.val.drop (i.val + 1) := by
      rw [hvv, hi1v]; simp
    have hkV : ValidL k.val := fun u hu => hs u (by rw [hkv'] at hu; exact List.mem_of_mem_take hu)
    have hvV : ValidL v.val := fun u hu => hs u (by rw [hvv'] at hu; exact List.mem_of_mem_drop hu)
    obtain ⟨t1, ht1, ht1v, ht1V⟩ := trim_valid (alloc.vec.Vec.deref k) (validStr_of k hkV)
    obtain ⟨t2, ht2, ht2v, ht2V⟩ := trim_valid (alloc.vec.Vec.deref v) (validStr_of v hvV)
    refine ⟨t1, t2, by simp [hk, hi1, hv, ht1, ht2], ?_, ht1V, ht2V⟩
    have hsplit : strS line = (line.val.take i.val).map chOf ++ chOf sep :: (line.val.drop (i.val + 1)).map chOf := by
      unfold strS
      conv => lhs; rw [← List.take_append_drop i.val line.val, List.drop_eq_getElem_cons hlt]
      simp [heq]
    have hnm : chOf sep ∉ (line.val.take i.val).map chOf :=
      not_mem_chars _ (fun u hu => hs u (List.mem_of_mem_take hu)) sep hsep
        (fun j hj => by
          simp at hj
          rw [List.getElem?_take, if_pos hj.1]; exact hne j hj.1)
    rw [hsplit, List.splitOn_append_cons_self_of_not_mem hnm]
    obtain ⟨r0, rs, hrs⟩ := List.exists_cons_of_ne_nil (List.splitOn_ne_nil (chOf sep) ((line.val.drop (i.val + 1)).map chOf))
    have hb := List.intercalate_splitOn (xs := (line.val.drop (i.val + 1)).map chOf) (chOf sep)
    rw [hrs] at hb ⊢
    simp only [List.map_cons]
    have hint : (chOf sep).toString.intercalate (String.ofList r0 :: rs.map String.ofList) =
        String.ofList ((line.val.drop (i.val + 1)).map chOf) := by
      apply String.ext
      rw [String.toList_intercalate, BStr.toString_ofList]
      simp only [String.toList_ofList, List.map_cons, List.map_map, Function.comp_def, String.toList_ofList, List.map_id']
      exact hb
    rw [hint]
    simp only [strV, ht1v, ht2v, strS, ds_deref_val, hkv', hvv']

theorem beatmap.dotnet.is_null_or_white_space_refines (s : Slice U32) (hs : ValidStr s) :
    beatmap.dotnet.is_null_or_white_space s = ok (isNullOrWhiteSpace (String.ofList (strS s))) := by
  have hspec : isNullOrWhiteSpace (String.ofList (strS s)) = s.val.all wsU := by
    simp [isNullOrWhiteSpace, strS, List.all_map, wsU, Function.comp_def]; rfl
  rw [hspec]
  unfold beatmap.dotnet.is_null_or_white_space beatmap.dotnet.is_null_or_white_space_loop
  obtain ⟨y, hy, hq⟩ := loop_ok (fun (x : Usize × Bool) => beatmap.dotnet.is_null_or_white_space_loop.body s x.1 x.2)
    (fun x => s.val.length - x.1.val)
    (fun x => x.1.val ≤ s.val.length ∧ x.2 = (s.val.take x.1.val).all wsU)
    (fun y => y = s.val.all wsU)
    (by
      rintro ⟨i, a⟩ ⟨hi, ha⟩
      dsimp only at hi ha ⊢
      by_cases hlt : i.val < s.val.length
      · right
        have hlt' : i < Slice.len s := by show i.val < (Slice.len s).val; simpa using hlt
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := s.property; omega)
        refine ⟨(i1, a && wsU (s.val[i.val]'hlt)), ?_, ⟨by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
        · simp only [beatmap.dotnet.is_null_or_white_space_loop.body, hlt', if_true, index_eq s i hlt, ws_eq s hs _ hlt, bind_ok, hi1]
          cases a <;> cases wsU (s.val[i.val]'hlt) <;> simp
        · dsimp only; rw [hi1v, ha, List.take_add_one, List.getElem?_eq_getElem hlt, List.all_append]; simp
      · left
        have hlt' : ¬ i < Slice.len s := by show ¬ i.val < (Slice.len s).val; simpa using hlt
        refine ⟨a, by simp [beatmap.dotnet.is_null_or_white_space_loop.body, hlt'], ?_⟩
        rw [ha, List.take_of_length_le (by omega)])
    (0#usize, true) ⟨by simp, by simp⟩
  rw [hy, hq]

set_option maxRecDepth 20000 in
theorem enumTable_val (t k : Nat) (hk : k < (enumTable t).length) : ((enumTable t)[k]'hk).2 = Int32.ofNat k := by
  match t with
  | 0 => revert k; decide
  | 1 => revert k; decide
  | 2 => revert k; decide
  | 3 => revert k; decide
  | 4 => revert k; decide
  | 5 => revert k; decide
  | n + 6 => rw [enumTable_ge (n + 6) (by omega)] at hk; simp at hk

theorem enumTable_len (t : Nat) : (enumTable t).length ≤ 12 := by
  match t with
  | 0 | 1 | 2 | 3 | 4 | 5 => decide
  | n + 6 => rw [enumTable_ge (n + 6) (by omega)]; simp

theorem i32S_hcast (k : Usize) (hk : k.val < 100) : i32S (UScalar.hcast .I32 k) = Int32.ofNat k.val := by
  apply Int32.toInt_inj.mp
  rw [i32S_toInt]; simp

theorem etp_inner (t : U32) (p : alloc.vec.Vec U32) (hp : ValidL p.val) :
    ∃ r, beatmap.dotnet.enum_try_parse_loop0_loop0 t p none 0#usize = ok r ∧
      r.map i32S = ((enumTable t.val).find? (fun q => q.1 == String.ofList (strS (alloc.vec.Vec.deref p)))).map (·.2) := by
  have hs := validStr_of p hp
  let L := enumTable t.val
  let str := String.ofList (strS (alloc.vec.Vec.deref p))
  obtain ⟨tl, htl, htlv0⟩ := beatmap.names.table_len_refines t
  have hL : L.length ≤ 12 := enumTable_len t.val
  have htlv : tl.val = L.length := htlv0
  have hname : ∀ (k : Usize), beatmap.names.table_name_is t k (alloc.vec.Vec.deref p) =
      ok (decide (∃ h : k.val < L.length, (L[k.val]'h).1 = str)) := by
    intro k
    rw [beatmap.names.table_name_is_refines t k _ hs]
    congr 1; apply decide_eq_decide.mpr
    constructor
    · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩
      rw [List.getD_eq_getElem _ _ h1] at h2
      apply String.ext; rw [String.toList_ofList]; exact h2.symm
    · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩
      rw [List.getD_eq_getElem _ _ h1, h2]; simp [str]
  unfold beatmap.dotnet.enum_try_parse_loop0_loop0
  have hnone : ∀ (k : Nat), (∀ j (hj : j < L.length), j < k → (L[j]'hj).1 ≠ str) → L.length ≤ k →
      L.find? (fun q => q.1 == str) = none := by
    intro k h hk; rw [List.find?_eq_none]; intro q hq
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    simpa using h j hj (by omega)
  obtain ⟨y, hy, hq⟩ := loop_ok (fun (x : Option I32 × Usize) => beatmap.dotnet.enum_try_parse_loop0_loop0.body t p x.1 x.2)
    (fun x => L.length + 1 - x.2.val)
    (fun x => x.2.val ≤ L.length ∧ (∀ j (hj : j < L.length), j < x.2.val → (L[j]'hj).1 ≠ str ∨
        ∃ k0 : Usize, k0.val ≤ j ∧ x.1 = some (UScalar.hcast .I32 k0)) ∧
      (∀ v, x.1 = some v → ∃ k0 : Usize, ∃ h : k0.val < L.length, v = UScalar.hcast .I32 k0 ∧ (L[k0.val]'h).1 = str ∧
        ∀ j (hj : j < L.length), j < k0.val → (L[j]'hj).1 ≠ str))
    (fun r => r.map i32S = (L.find? (fun q => q.1 == str)).map (·.2))
    (by
      rintro ⟨f, k⟩ ⟨hk, hpre, hf⟩
      dsimp only at hk hpre hf ⊢
      cases f with
      | some v =>
        left
        refine ⟨some v, by simp [beatmap.dotnet.enum_try_parse_loop0_loop0.body], ?_⟩
        obtain ⟨k0, hk0, rfl, he, hb⟩ := hf v rfl
        have : L.find? (fun q => q.1 == str) = some (L[k0.val]'hk0) := by
          rw [List.find?_eq_some_iff_getElem]
          refine ⟨by simp [he], k0.val, hk0, rfl, fun j hj => by simpa using hb j (by omega) hj⟩
        rw [this]; simp [enumTable_val, L, i32S_hcast k0 (by omega)]
      | none =>
        by_cases hlt : k.val < L.length
        · right
          have hlt' : k < tl := by show k.val < tl.val; rw [htlv]; exact hlt
          have hlt'' : k.val < tl.val := by rw [htlv]; exact hlt
          obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := usize_ge_32; omega)
          by_cases hm : (L[k.val]'hlt).1 = str
          · refine ⟨(some (UScalar.hcast .I32 k), k1), ?_, ⟨by dsimp only; omega, ?_, ?_⟩, by dsimp only; omega⟩
            · have : decide (∃ h : k.val < L.length, (L[k.val]'h).1 = str) = true := by simp [hlt, hm]
              simp [beatmap.dotnet.enum_try_parse_loop0_loop0.body, htl, hlt', hlt'', hname, this, lift, hk1]
            · intro j hj hjk; dsimp only at hjk
              by_cases hjk' : j < k.val
              · rcases hpre j hj hjk' with h | ⟨_, _, h⟩
                · exact Or.inl h
                · simp at h
              · exact Or.inr ⟨k, by omega, rfl⟩
            · intro v hv; simp at hv; subst hv
              refine ⟨k, hlt, rfl, hm, fun j hj hjk => ?_⟩
              rcases hpre j hj hjk with h | ⟨_, _, h⟩
              · exact h
              · simp at h
          · refine ⟨(none, k1), ?_, ⟨by dsimp only; omega, ?_, by simp⟩, by dsimp only; omega⟩
            · have : decide (∃ h : k.val < L.length, (L[k.val]'h).1 = str) = false := by simp [hlt, hm]
              simp [beatmap.dotnet.enum_try_parse_loop0_loop0.body, htl, hlt', hlt'', hname, this, hk1]
            · intro j hj hjk; dsimp only at hjk
              by_cases hjk' : j < k.val
              · exact hpre j hj hjk'
              · have : j = k.val := by omega
                subst this; exact Or.inl hm
        · left
          have hlt' : ¬ k < tl := by show ¬ k.val < tl.val; rw [htlv]; exact hlt
          have hlt'' : ¬ k.val < tl.val := by rw [htlv]; exact hlt
          refine ⟨none, by simp [beatmap.dotnet.enum_try_parse_loop0_loop0.body, htl, hlt', hlt''], ?_⟩
          rw [hnone k.val (fun j hj hjk => by rcases hpre j hj hjk with h | ⟨_, _, h⟩; exact h; simp at h) (by omega)]
          rfl)
    ((none : Option I32), 0#usize) ⟨by simp, by simp, by simp⟩
  exact ⟨y, hy, hq⟩

def etpF (names : List (String × Int32)) (acc : Option Int32) (p : String) : Option Int32 :=
  match acc with
  | none => none
  | some v =>
    match names.find? (fun q => q.1 == trim p) with
    | some (_, x) => some (v ||| x)
    | none => none

theorem etp_outer (t : U32) (parts : alloc.vec.Vec (alloc.vec.Vec U32)) (hp : ∀ l ∈ parts.val, ValidL l.val) :
    ∃ r, beatmap.dotnet.enum_try_parse_loop0 t parts (some 0#i32) 0#usize = ok r ∧
      r.map i32S = (parts.val.map strV).foldl (etpF (enumTable t.val)) (some 0) := by
  unfold beatmap.dotnet.enum_try_parse_loop0
  obtain ⟨y, hy, hq⟩ := loop_ok (fun (x : Option I32 × Usize) => beatmap.dotnet.enum_try_parse_loop0.body t parts x.1 x.2)
    (fun x => parts.val.length - x.2.val)
    (fun x => x.2.val ≤ parts.val.length ∧ x.1.map i32S = ((parts.val.map strV).take x.2.val).foldl (etpF (enumTable t.val)) (some 0))
    (fun r => r.map i32S = (parts.val.map strV).foldl (etpF (enumTable t.val)) (some 0))
    (by
      rintro ⟨acc, i⟩ ⟨hi, ha⟩
      dsimp only at hi ha ⊢
      by_cases hlt : i.val < parts.val.length
      · right
        have hlt' : i < alloc.vec.Vec.len parts := by show i.val < (alloc.vec.Vec.len parts).val; simpa using hlt
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := parts.property; omega)
        have htake : ((parts.val.map strV).take (i.val + 1)) = (parts.val.map strV).take i.val ++ [strV (parts.val[i.val]'hlt)] := by
          rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hlt)]; simp
        cases acc with
        | none =>
          refine ⟨(none, i1), by simp [beatmap.dotnet.enum_try_parse_loop0.body, hlt', hi1], ⟨by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
          dsimp only; rw [hi1v, htake, List.foldl_append, ← ha]; rfl
        | some v =>
          have hv := hp _ (List.getElem_mem hlt)
          obtain ⟨pt, hpt, hptv, hptV⟩ := trim_valid (alloc.vec.Vec.deref (parts.val[i.val]'hlt)) (validStr_of _ hv)
          obtain ⟨fd, hfd, hfdv⟩ := etp_inner t pt hptV
          have hstr : String.ofList (strS (alloc.vec.Vec.deref pt)) = trim (strV (parts.val[i.val]'hlt)) := by
            simp only [strS, ds_deref_val, strV] at hptv ⊢; exact hptv
          rw [hstr] at hfdv
          cases fd with
          | none =>
            refine ⟨(none, i1), by simp [beatmap.dotnet.enum_try_parse_loop0.body, hlt', vec_index_eq' parts i hlt, hpt, hfd, hi1],
              ⟨by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
            dsimp only; rw [hi1v, htake, List.foldl_append, ← ha]
            simp only [List.foldl_cons, List.foldl_nil, Option.map_some, etpF]
            cases h : (enumTable t.val).find? (fun q => q.1 == trim (strV (parts.val[i.val]'hlt))) with
            | none => rfl
            | some q => rw [h] at hfdv; simp at hfdv
          | some x =>
            refine ⟨(some (v ||| x), i1), by simp [beatmap.dotnet.enum_try_parse_loop0.body, hlt', vec_index_eq' parts i hlt, hpt, hfd, lift, hi1],
              ⟨by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
            dsimp only; rw [hi1v, htake, List.foldl_append, ← ha]
            simp only [List.foldl_cons, List.foldl_nil, Option.map_some, etpF]
            cases h : (enumTable t.val).find? (fun q => q.1 == trim (strV (parts.val[i.val]'hlt))) with
            | none => rw [h] at hfdv; simp at hfdv
            | some q =>
              obtain ⟨n, y⟩ := q
              rw [h] at hfdv; simp at hfdv
              rw [← hfdv]; unfold i32S; simp
      · left
        have hlt' : ¬ i < alloc.vec.Vec.len parts := by show ¬ i.val < (alloc.vec.Vec.len parts).val; simpa using hlt
        refine ⟨acc, by simp [beatmap.dotnet.enum_try_parse_loop0.body, hlt'], ?_⟩
        rw [ha, List.take_of_length_le (by simp; omega)])
    (some 0#i32, 0#usize) ⟨by simp, by simp; rfl⟩
  exact ⟨y, hy, hq⟩

theorem trim_start_valid (s : Slice U32) (hs : ValidStr s) :
    ∃ v, beatmap.dotnet.trim_start s = ok v ∧ String.ofList (v.val.map chOf) = trimStart (String.ofList (strS s)) ∧
      ValidL v.val ∧ v.val.length ≤ s.val.length := by
  obtain ⟨v, hv, hvv⟩ := beatmap.dotnet.trim_start_refines s hs
  obtain ⟨v', hv', hvv'⟩ := trim_common s hs true false beatmap.dotnet.trim_start (fun _ => rfl)
  have e : v' = v := by rw [hv] at hv'; simpa using hv'.symm
  subst e
  simp only [if_true, Bool.false_eq_true, if_false] at hvv'
  refine ⟨v', hv, hvv, fun u hu => hs u ?_, ?_⟩
  · rw [hvv'] at hu; exact mem_dropWhile_sub _ _ _ hu
  · rw [hvv']; exact (List.dropWhile_suffix _).length_le

theorem comma_eq : "," = (chOf 44#u32).toString := by decide

theorem beatmap.dotnet.enum_try_parse_refines (names : U32) (s : Slice U32) (hs : ValidStr s)
    (hn : s.val.length < Usize.max) :
    ∃ r, beatmap.dotnet.enum_try_parse names s = ok r ∧
      r.map i32S = enumTryParse (enumTable names.val) (String.ofList (strS s)) := by
  obtain ⟨tv, htv, htvv, htvV, htvl⟩ := trim_start_valid s hs
  unfold beatmap.dotnet.enum_try_parse enumTryParse
  rw [← htvv]
  simp only [htv, bind_ok, String.toList_ofList]
  have hsd : strS (alloc.vec.Vec.deref tv) = tv.val.map chOf := by simp [strS, ds_deref_val]
  have hP : ∃ r, (do
        let r ← net.parse.int_parse (alloc.vec.Vec.deref tv)
        match r with
        | core.result.Result.Ok v => ok (some v)
        | core.result.Result.Err _ => ok none) = ok r ∧
      r.map i32S = (match OsuModel.Net.intParse (String.ofList (tv.val.map chOf)) with
        | Except.ok v => some v
        | Except.error _ => none) := by
    rw [net.parse.int_parse_refines _ (validStr_of tv htvV), bind_ok, OsuModel.Net.intParse, String.toList_ofList, hsd]
    cases OsuModel.Net.intParseChars (tv.val.map chOf) with
    | ok v => exact ⟨some (i32I v), rfl, by simp⟩
    | error e => exact ⟨none, rfl, rfl⟩
  cases htl : tv.val with
  | nil =>
    have : alloc.vec.Vec.len tv = 0#usize := by apply UScalar.eq_of_val_eq; simp [htl]
    exact ⟨none, by simp [this], rfl⟩
  | cons t0 rest =>
    have hlen : ¬ alloc.vec.Vec.len tv = 0#usize := by
      intro h; have := congrArg UScalar.val h; simp [htl] at this
    have h0 : (0#usize : Usize).val < tv.val.length := by simp [htl]
    have ht0 : tv.val[(0#usize : Usize).val]'h0 = t0 := by simp [htl]
    have hv0 : t0.val.isValidChar := htvV t0 (by simp [htl])
    rw [htl] at hP; simp only [List.map_cons] at hP
    simp only [hlen, if_false, vec_index_eq' tv 0#usize h0, ht0, bind_ok, net.parse.is_digit_refines t0 hv0,
      List.map_cons]
    by_cases kd : OsuModel.Net.Parse.isDigit (chOf t0) = true
    · simp only [kd, if_true, Bool.true_or]; exact hP
    · have kd' : OsuModel.Net.Parse.isDigit (chOf t0) = false := by simpa using kd
      by_cases kp : t0 = 43#u32
      · have : (chOf t0 == '+') = true := by rw [kp]; decide
        simp only [kd', if_pos kp, Bool.false_eq_true, if_false, this, Bool.false_or, Bool.true_or, if_true]; exact hP
      · by_cases km : t0 = 45#u32
        · have : (chOf t0 == '-') = true := by rw [km]; decide
          have hp' : (chOf t0 == '+') = false := by
            rw [chOf_beq_lit _ _ (by decide)]; simp; intro h; exact kp (UScalar.eq_of_val_eq (by simpa using h))
          simp only [kd', if_neg kp, if_pos km, Bool.false_eq_true, if_false, this, hp', Bool.false_or, Bool.or_true, if_true]; exact hP
        · have hp' : (chOf t0 == '+') = false := by
            rw [chOf_beq_lit _ _ (by decide)]; simp; intro h; exact kp (UScalar.eq_of_val_eq (by simpa using h))
          have hm' : (chOf t0 == '-') = false := by
            rw [chOf_beq_lit _ _ (by decide)]; simp; intro h; exact km (UScalar.eq_of_val_eq (by simpa using h))
          simp only [kd', if_neg kp, if_neg km, Bool.false_eq_true, if_false, hp', hm', Bool.false_or]
          obtain ⟨parts, hparts, hpv, hpV⟩ := beatmap.dotnet.split_refines (alloc.vec.Vec.deref tv) (validStr_of tv htvV)
            44#u32 (by decide) (by simp [ds_deref_val]; omega)
          obtain ⟨r, hr, hrv⟩ := etp_outer names parts hpV
          refine ⟨r, by simp [hparts, hr], ?_⟩
          rw [hrv]
          have hl : parts.val.map strV = (String.ofList (List.map chOf (t0 :: rest))).splitOn "," := by
            have := congrArg Array.toList hpv
            simp only [split, hsd, htl, ← comma_eq] at this
            simpa using this
          rw [hl]; rfl

end OsuProofs
