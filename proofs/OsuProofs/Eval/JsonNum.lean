/-
`eval::mods_json` number helpers of `toSetting` (json agent, D46): `is_nat`, `nat_sat`, `starts_minus`,
`has_frac_or_exp`, `int_of_text`, `in_range`, `long_of`.

Lean 4.35 String API bridges (proved here from core lemmas): `String.isNat` (`String.Slice.isNat`, a `for` loop with
early `return`) = `js_isNatAux false` on the character list; `String.toNat!` / `(t.drop 1).toNat!` = `js_toNatL`
(fold over the characters, `_` skipped; `panic!` default 0); `String.any` = `List.any`; `startsWith "-"` = head is
`'-'`. Rust `nat_sat` saturates at 2^64 (`NAT_CAP`): its result is `min (toNat! …) 2^64` (`js_fold_sat`), which is
enough for the 64-bit range tests of `toSetting`.
-/
import OsuProofs.Eval.JsonValue
import OsuProofs.Beatmap.DecoderStr
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
def js_isNatAux (last : Bool) : List Char → Bool
  | [] => last
  | c :: cs => if c = '_' then (if !last then false else js_isNatAux false cs)
      else if c.isDigit then js_isNatAux true cs else false

def js_isNatBody : Char → Option Bool × Bool → Id (ForInStep (Option Bool × Bool)) := fun c __s =>
  if c = '_' then
    if (!__s.2) = true then pure (ForInStep.done (some false, __s.2)) else pure (ForInStep.yield (none, false))
  else if c.isDigit = true then pure (ForInStep.yield (none, true)) else pure (ForInStep.done (some false, __s.2))

def js_isNatSt (b : Bool) : List Char → Option Bool × Bool
  | [] => (none, b)
  | c :: cs => if c = '_' then (if !b then (some false, b) else js_isNatSt false cs)
      else if c.isDigit then js_isNatSt true cs else (some false, b)

theorem js_isNat_forIn (L : List Char) (b : Bool) :
    forIn (m := Id) L ((none : Option Bool), b) js_isNatBody = js_isNatSt b L := by
  induction L generalizing b with
  | nil => rfl
  | cons c cs ih =>
    rw [List.forIn_cons]
    by_cases h1 : c = '_'
    · cases b
      · have : js_isNatBody c (none, false) = pure (ForInStep.done (some false, false)) := by simp [js_isNatBody, h1]
        rw [this]; simp [js_isNatSt, h1]; rfl
      · have : js_isNatBody c (none, true) = pure (ForInStep.yield (none, false)) := by simp [js_isNatBody, h1]
        rw [this]; simp only [pure_bind, js_isNatSt, h1]; exact ih false
    · by_cases h2 : c.isDigit = true
      · have : js_isNatBody c (none, b) = pure (ForInStep.yield (none, true)) := by simp [js_isNatBody, h1, h2]
        rw [this]; simp only [pure_bind, js_isNatSt, h1, h2]; exact ih true
      · have : js_isNatBody c (none, b) = pure (ForInStep.done (some false, b)) := by simp [js_isNatBody, h1, h2]
        rw [this]; simp [js_isNatSt, h1, h2]; rfl

theorem js_isNatSt_some (b : Bool) (L : List Char) (r : Bool) (h : (js_isNatSt b L).1 = some r) :
    r = false ∧ js_isNatAux b L = false := by
  induction L generalizing b with
  | nil => simp [js_isNatSt] at h
  | cons c cs ih =>
    by_cases h1 : c = '_'
    · cases b
      · simp [js_isNatSt, h1] at h; simp [js_isNatAux, h1, h]
      · simp only [js_isNatSt, h1, js_isNatAux] at h ⊢; simpa using ih false h
    · by_cases h2 : c.isDigit = true
      · simp only [js_isNatSt, h1, h2, js_isNatAux] at h ⊢; simpa using ih true h
      · simp [js_isNatSt, h1, h2] at h; simp [js_isNatAux, h1, h2, h]

theorem js_isNatSt_none (b : Bool) (L : List Char) (h : (js_isNatSt b L).1 = none) :
    js_isNatAux b L = (js_isNatSt b L).2 := by
  induction L generalizing b with
  | nil => rfl
  | cons c cs ih =>
    by_cases h1 : c = '_'
    · cases b
      · simp [js_isNatSt, h1] at h
      · simp only [js_isNatSt, h1, js_isNatAux] at h ⊢; simpa using ih false h
    · by_cases h2 : c.isDigit = true
      · simp only [js_isNatSt, h1, h2, js_isNatAux] at h ⊢; simpa using ih true h
      · simp [js_isNatSt, h1, h2] at h

theorem js_isNat_eq (L : List Char) : (String.ofList L).isNat = js_isNatAux false L := by
  simp only [String.isNat, String.Slice.isNat, String.Slice.forIn_eq_forIn_toList, String.copy_toSlice, String.toList_ofList]
  rw [show (forIn (m := Id) L ((none : Option Bool), false) fun c (__s : Option Bool × Bool) =>
        if c = '_' then
          if (!__s.2) = true then pure (ForInStep.done (some false, __s.2)) else pure (ForInStep.yield (none, false))
        else if c.isDigit = true then pure (ForInStep.yield (none, true)) else pure (ForInStep.done (some false, __s.2)))
      = js_isNatSt false L from js_isNat_forIn L false]
  rcases h : js_isNatSt false L with ⟨o, d⟩
  cases o with
  | some r => have := js_isNatSt_some false L r (by rw [h]); rw [this.2, this.1]; rfl
  | none => have := js_isNatSt_none false L (by rw [h]); rw [this, h]; rfl
end OsuProofs

namespace OsuProofs
open OsuImpl
/-- the characters `s[lo..hi]` -/
def js_sub (s : Slice U32) (lo hi : Nat) : List Char := ((strS s).drop lo).take (hi - lo)

theorem js_sub_cons (s : Slice U32) (i hi : Nat) (h : i < hi) (hl : hi ≤ s.val.length) :
    js_sub s i hi = chOf (s.val[i]'(by first | omega | (dsimp only; omega))) :: js_sub s (i+1) hi := by
  unfold js_sub
  rw [strS_drop s i (by first | omega | (dsimp only; omega)), show hi - i = (hi - (i+1)) + 1 by first | omega | (dsimp only; omega), List.take_succ_cons]

theorem js_sub_nil (s : Slice U32) (i hi : Nat) (h : hi ≤ i) : js_sub s i hi = [] := by
  unfold js_sub; rw [show hi - i = 0 by first | omega | (dsimp only; omega)]; simp

theorem eval.mods_json.is_nat_refines (s : Slice U32) (hs : ValidStr s) (lo hi : Usize) (hlh : lo.val ≤ hi.val)
    (hl : hi.val ≤ s.val.length) :
    eval.mods_json.is_nat s lo hi = ok (String.ofList (js_sub s lo.val hi.val)).isNat := by
  rw [js_isNat_eq]
  have hmax := slice_len_lt s
  have H := loop_ok (fun (x : Bool × Bool × Usize) => eval.mods_json.is_nat_loop.body s hi x.1 x.2.1 x.2.2)
    (fun x => hi.val - x.2.2.val)
    (fun x => lo.val ≤ x.2.2.val ∧ x.2.2.val ≤ hi.val ∧
      (x.2.1 = true → js_isNatAux false (js_sub s lo.val hi.val) = js_isNatAux x.1 (js_sub s x.2.2.val hi.val)) ∧
      (x.2.1 = false → js_isNatAux false (js_sub s lo.val hi.val) = false))
    (fun y => (if y.2 then y.1 else false) = js_isNatAux false (js_sub s lo.val hi.val)) ?_ (false, true, lo)
    ⟨le_refl _, hlh, fun _ => rfl, fun h => by simp at h⟩
  · obtain ⟨y, hy, hq⟩ := H
    unfold eval.mods_json.is_nat eval.mods_json.is_nat_loop
    rw [show (fun (x : Bool × Bool × Usize) => match x with
        | (last_was_digit1, ok_1, i1) => eval.mods_json.is_nat_loop.body s hi last_was_digit1 ok_1 i1) =
        (fun (x : Bool × Bool × Usize) => eval.mods_json.is_nat_loop.body s hi x.1 x.2.1 x.2.2) from rfl, hy]
    obtain ⟨a, b⟩ := y
    cases b <;> simp at hq ⊢ <;> exact hq
  · rintro ⟨last, ok_, i⟩ ⟨h1, h2, h3, h4⟩
    simp only at h1 h2 h3 h4 ⊢
    cases ok_ with
    | false => left; exact ⟨(last, false), by simp [eval.mods_json.is_nat_loop.body], by simp [h4 rfl]⟩
    | true =>
      have h3 := h3 rfl
      by_cases hlt : i.val < hi.val
      · right
        have hil : i.val < s.val.length := by first | omega | (dsimp only; omega)
        have hlt' : i < hi := hlt
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by first | omega | (dsimp only; omega))
        rw [js_sub_cons s i.val hi.val hlt hl] at h3
        generalize hc : s.val[i.val]'hil = c at h3
        have hcv : c.val.isValidChar := hc ▸ hs.get i.val hil
        by_cases h95 : c.val = 95
        · have hch : chOf c = '_' := (chOf_eq_lit c '_' (by decide)).mpr h95
          cases last with
          | false =>
            refine ⟨(false, false, i1), ?_, ⟨by first | omega | (dsimp only; omega), by first | omega | (dsimp only; omega), fun h => by simp at h, fun _ => ?_⟩, by first | omega | (dsimp only; omega)⟩
            · simp [eval.mods_json.is_nat_loop.body, hlt', slice_index_ok s i hil, hc, UScalar.eq_equiv, h95, hi1]
            · rw [h3]; simp [js_isNatAux, hch]
          | true =>
            refine ⟨(false, true, i1), ?_, ⟨by first | omega | (dsimp only; omega), by first | omega | (dsimp only; omega), fun _ => ?_, fun h => by simp at h⟩, by first | omega | (dsimp only; omega)⟩
            · simp [eval.mods_json.is_nat_loop.body, hlt', slice_index_ok s i hil, hc, UScalar.eq_equiv, h95, hi1]
            · rw [h3, hi1v]; simp [js_isNatAux, hch]
        · have hch : chOf c ≠ '_' := fun hh => h95 ((chOf_eq_lit c '_' (by decide)).mp hh)
          have hne : ¬ c = 95#u32 := fun hh => h95 (by rw [hh]; rfl)
          by_cases hd : (chOf c).isDigit = true
          · refine ⟨(true, true, i1), ?_, ⟨by first | omega | (dsimp only; omega), by first | omega | (dsimp only; omega), fun _ => ?_, fun h => by simp at h⟩, by first | omega | (dsimp only; omega)⟩
            · simp [eval.mods_json.is_nat_loop.body, hlt', slice_index_ok s i hil, hc, hne, hi1,
                eval.mods_json.is_digit_refines c hcv, hd]
            · rw [h3, hi1v]; simp [js_isNatAux, hch, hd]
          · refine ⟨(last, false, i1), ?_, ⟨by first | omega | (dsimp only; omega), by first | omega | (dsimp only; omega), fun h => by simp at h, fun _ => ?_⟩, by first | omega | (dsimp only; omega)⟩
            · simp [eval.mods_json.is_nat_loop.body, hlt', slice_index_ok s i hil, hc, hne, hi1,
                eval.mods_json.is_digit_refines c hcv, hd]
            · rw [h3]; simp [js_isNatAux, hch, hd]
      · left
        have hlt' : ¬ i < hi := hlt
        refine ⟨(last, true), by simp [eval.mods_json.is_nat_loop.body, hlt'], ?_⟩
        simp only [if_true]; rw [h3, js_sub_nil s i.val hi.val (by first | omega | (dsimp only; omega))]; rfl
end OsuProofs

namespace OsuProofs
open OsuImpl
/-- `String.toNat!`'s fold step -/
def js_toNatF (n : Nat) (c : Char) : Nat := if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)
/-- `String.toNat!` on the characters `L` (the `panic!` default is `0`) -/
def js_toNatL (L : List Char) : Nat := if js_isNatAux false L then L.foldl js_toNatF 0 else 0

theorem js_toNat_str (L : List Char) : (String.ofList L).toNat! = js_toNatL L := by
  simp only [String.toNat!, String.Slice.toNat!, String.Slice.foldl_eq_foldl_toList, String.copy_toSlice,
    String.toList_ofList, String.isNat_toSlice, js_isNat_eq, js_toNatL]
  split <;> rfl

theorem js_toNat_drop1 (L : List Char) : ((String.ofList L).drop 1).toNat! = js_toNatL (L.drop 1) := by
  simp only [String.Slice.toNat!, String.Slice.foldl_eq_foldl_toList, String.toList_copy_drop, String.toList_ofList]
  rw [← String.Slice.isNat_copy, ← String.ofList_toList (s := ((String.ofList L).drop 1).copy), js_isNat_eq,
    String.toList_copy_drop, String.toList_ofList, js_toNatL]
  split <;> rfl

theorem js_isNatAux_mem (b : Bool) (L : List Char) (h : js_isNatAux b L = true) : ∀ c ∈ L, c = '_' ∨ c.isDigit = true := by
  induction L generalizing b with
  | nil => simp
  | cons c cs ih =>
    intro x hx
    by_cases h1 : c = '_'
    · have h' : js_isNatAux false cs = true := by
        cases b <;> simp [js_isNatAux, h1] at h; exact h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl h1
      · exact ih false h' x hx
    · by_cases h2 : c.isDigit = true
      · have h' : js_isNatAux true cs = true := by simpa [js_isNatAux, h1, h2] using h
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inr h2
        · exact ih true h' x hx
      · simp [js_isNatAux, h1, h2] at h

theorem js_toNatF_ge (n : Nat) (c : Char) : n ≤ js_toNatF n c := by
  unfold js_toNatF; split <;> omega

theorem js_fold_sat (C : Nat) : ∀ (R : List Char) (x : Nat),
    min (R.foldl js_toNatF (min x C)) C = min (R.foldl js_toNatF x) C := by
  intro R
  induction R with
  | nil => intro x; simp
  | cons c R ih =>
    intro x
    simp only [List.foldl_cons]
    have key : min (js_toNatF (min x C) c) C = min (js_toNatF x c) C := by
      by_cases hx : x ≤ C
      · rw [show min x C = x from Nat.min_eq_left hx]
      · rw [show min x C = C from Nat.min_eq_right (by omega)]
        have a1 := js_toNatF_ge C c; have a2 := js_toNatF_ge x c; omega
    rw [← ih (js_toNatF (min x C) c), key, ih]
end OsuProofs

namespace OsuProofs
open OsuImpl
theorem js_cap_val : eval.mods_json.NAT_CAP.val = 2^64 := by
  unfold eval.mods_json.NAT_CAP; rfl

theorem eval.mods_json.nat_sat_refines (s : Slice U32) (hs : ValidStr s) (lo hi : Usize) (hlh : lo.val ≤ hi.val)
    (hl : hi.val ≤ s.val.length) :
    ∃ r, eval.mods_json.nat_sat s lo hi = ok r ∧
      r.val = min ((String.ofList (js_sub s lo.val hi.val)).toNat!) (2^64) := by
  rw [js_toNat_str]
  have hmax := slice_len_lt s
  unfold eval.mods_json.nat_sat
  rw [eval.mods_json.is_nat_refines s hs lo hi hlh hl, js_isNat_eq, bind_ok]
  by_cases hN : js_isNatAux false (js_sub s lo.val hi.val) = true
  · simp only [hN, if_true]
    have hmem := js_isNatAux_mem false _ hN
    have H := loop_ok (fun (x : U128 × Usize) => eval.mods_json.nat_sat_loop.body s hi x.1 x.2)
      (fun x => hi.val - x.2.val)
      (fun x => lo.val ≤ x.2.val ∧ x.2.val ≤ hi.val ∧ x.1.val ≤ 2^64 ∧
        (∀ c ∈ js_sub s x.2.val hi.val, c = '_' ∨ c.isDigit = true) ∧
        min ((js_sub s x.2.val hi.val).foldl js_toNatF x.1.val) (2^64) =
          min ((js_sub s lo.val hi.val).foldl js_toNatF 0) (2^64))
      (fun y => y.val = min ((js_sub s lo.val hi.val).foldl js_toNatF 0) (2^64)) ?_ (0#u128, lo)
      ⟨le_refl _, hlh, by simp, hmem, by simp⟩
    · obtain ⟨y, hy, hq⟩ := H
      refine ⟨y, ?_, by rw [hq, js_toNatL, if_pos hN]⟩
      unfold eval.mods_json.nat_sat_loop
      rw [show (fun (x : U128 × Usize) => match x with
          | (v1, i1) => eval.mods_json.nat_sat_loop.body s hi v1 i1) =
          (fun (x : U128 × Usize) => eval.mods_json.nat_sat_loop.body s hi x.1 x.2) from rfl, hy]
    · rintro ⟨v, i⟩ ⟨h1, h2, h3, hm, h4⟩
      simp only at h1 h2 h3 hm h4 ⊢
      by_cases hlt : i.val < hi.val
      · right
        have hil : i.val < s.val.length := by first | omega | (dsimp only; omega)
        have hlt' : i < hi := hlt
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by first | omega | (dsimp only; omega))
        rw [js_sub_cons s i.val hi.val hlt hl] at h4 hm
        generalize hc : s.val[i.val]'hil = c at h4 hm
        have hcv : c.val.isValidChar := hc ▸ hs.get i.val hil
        simp only [List.foldl_cons] at h4
        have hm' : ∀ x ∈ js_sub s (i.val+1) hi.val, x = '_' ∨ x.isDigit = true := fun x hx => hm x (List.mem_cons_of_mem _ hx)
        by_cases h95 : c.val = 95
        · have hch : chOf c = '_' := (chOf_eq_lit c '_' (by decide)).mpr h95
          refine ⟨(v, i1), ?_, ⟨by first | omega | (dsimp only; omega), by first | omega | (dsimp only; omega), h3, by rw [hi1v]; exact hm', ?_⟩, by simp; omega⟩
          · simp [eval.mods_json.nat_sat_loop.body, hlt', slice_index_ok s i hil, hc, h95, hi1]
          · rw [hi1v, ← h4]; simp [js_toNatF, hch]
        · have hch : chOf c ≠ '_' := fun hh => h95 ((chOf_eq_lit c '_' (by decide)).mp hh)
          have hd : (chOf c).isDigit = true := (hm _ List.mem_cons_self).resolve_left hch
          rw [ev_isDigit_chOf c hcv] at hd
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
          have hU : U128.max = 2^128 - 1 := by simp [U128.max, U128.numBits]
          obtain ⟨m, hm1, hm1v⟩ := eq_ok_of_spec (U128.mul_spec (x := v) (y := 10#u128) (by simp [hU]; omega))
          obtain ⟨d, hd1, hd1v⟩ := ev_u32_sub c 48#u32 (by simp; omega)
          have hcast : (UScalar.cast .U128 d).val = d.val := by
            rw [UScalar.cast_val_eq]; simp; have := d.hBounds; simp at this; omega
          obtain ⟨w, hw, hwv⟩ := eq_ok_of_spec (U128.add_spec (x := m) (y := UScalar.cast .U128 d) (by simp [hm1v, hcast, hd1v, hU]; omega))
          have hwv' : w.val = v.val * 10 + (c.val - 48) := by simp [hwv, hm1v, hcast, hd1v]
          have hne : (c != 95#u32) = true := by
            simp only [bne_iff_ne, ne_eq]; intro hh; exact h95 (by rw [hh]; rfl)
          have hF : js_toNatF v.val (chOf c) = w.val := by
            unfold js_toNatF; rw [if_neg hch, chOf_toNat c hcv, hwv']; rfl
          rw [hF] at h4
          have hcap := js_cap_val
          have hbody : eval.mods_json.nat_sat_loop.body s hi v i =
              ok (.cont (if w > eval.mods_json.NAT_CAP then eval.mods_json.NAT_CAP else w, i1)) := by
            simp only [eval.mods_json.nat_sat_loop.body, hlt', if_true, slice_index_ok s i hil, hc, hne, bind_ok,
              hm1, hd1, lift, hw, hi1]
            split <;> simp only [bind_ok]
          by_cases hgt : w.val > 2^64
          · have hgt' : w > eval.mods_json.NAT_CAP := by show eval.mods_json.NAT_CAP.val < w.val; omega
            refine ⟨(eval.mods_json.NAT_CAP, i1), by rw [hbody, if_pos hgt'], ⟨by dsimp only; omega, by dsimp only; omega, by simp [hcap],
              by rw [hi1v]; exact hm', ?_⟩, by simp; omega⟩
            simp only
            rw [hi1v, ← h4, hcap, ← js_fold_sat (2^64) _ w.val, show min w.val (2^64) = 2^64 by omega]
          · have hgt' : ¬ w > eval.mods_json.NAT_CAP := by show ¬ eval.mods_json.NAT_CAP.val < w.val; omega
            refine ⟨(w, i1), by rw [hbody, if_neg hgt'], ⟨by dsimp only; omega, by dsimp only; omega, by simp; omega,
              by rw [hi1v]; exact hm', ?_⟩, by simp; omega⟩
            simp only
            rw [hi1v, ← h4]
      · left
        have hlt' : ¬ i < hi := hlt
        refine ⟨v, by simp [eval.mods_json.nat_sat_loop.body, hlt'], ?_⟩
        rw [← h4, js_sub_nil s i.val hi.val (by first | omega | (dsimp only; omega))]; simp; omega
  · refine ⟨0#u128, by simp [hN], ?_⟩
    simp [js_toNatL, hN]
end OsuProofs

namespace OsuProofs
open OsuImpl
theorem js_startsWith_minus (L : List Char) :
    (String.ofList L).startsWith "-" = decide (L.head? = some '-') := by
  have : (String.ofList L).startsWith "-" = decide (['-'] <+: L) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff]; unfold String.startsWith
    rw [String.Slice.startsWith_string_iff, String.copy_toSlice, String.toList_ofList]; simp only [String.toList_ofList]
  rw [this]; cases L with
  | nil => simp
  | cons c cs => simp [List.cons_prefix_cons, eq_comm]

theorem eval.mods_json.starts_minus_refines (t : Slice U32) :
    eval.mods_json.starts_minus t = ok ((String.ofList (strS t)).startsWith "-") := by
  rw [js_startsWith_minus]
  unfold eval.mods_json.starts_minus
  by_cases h : 0 < t.val.length
  · have h' : Slice.len t > 0#usize := by show (0#usize).val < (Slice.len t).val; simpa using h
    rw [if_pos h', slice_index_ok t 0#usize h, bind_ok]
    generalize hx : t.val[0#usize.val]'h = x
    have hh : (strS t).head? = some (chOf x) := by
      rw [← hx]; simp [strS, List.head?_eq_getElem?, List.getElem?_eq_getElem h]
    rw [hh]; congr 1
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, Option.some.injEq, chOf_eq_lit x '-' (by decide)]
    constructor <;> intro hh
    · rw [hh]; rfl
    · exact UScalar.eq_of_val_eq (by rw [hh]; rfl)
  · have h' : ¬ Slice.len t > 0#usize := by show ¬ (0#usize).val < (Slice.len t).val; simpa using h
    rw [if_neg h']
    have : t.val = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [strS, this]
end OsuProofs

namespace OsuProofs
open OsuImpl
theorem js_any_str (L : List Char) (p : Char → Bool) : (String.ofList L).any p = L.any p := by
  simp [String.any, String.contains_bool_eq]

theorem js_fracP_chOf (c : U32) :
    (chOf c == '.' || chOf c == 'e' || chOf c == 'E') = (decide (c.val = 46) || decide (c.val = 101) || decide (c.val = 69)) := by
  have e1 := chOf_eq_lit c '.' (by decide)
  have e2 := chOf_eq_lit c 'e' (by decide)
  have e3 := chOf_eq_lit c 'E' (by decide)
  by_cases a1 : c.val = 46 <;> by_cases a2 : c.val = 101 <;> by_cases a3 : c.val = 69 <;>
    simp_all <;> omega

theorem eval.mods_json.has_frac_or_exp_refines (t : Slice U32) :
    eval.mods_json.has_frac_or_exp t = ok ((String.ofList (strS t)).any (fun c => c == '.' || c == 'e' || c == 'E')) := by
  rw [js_any_str]
  have hmax := slice_len_lt t
  have H := loop_ok (fun (x : Bool × Usize) => eval.mods_json.has_frac_or_exp_loop.body t x.1 x.2)
    (fun x => t.val.length - x.2.val)
    (fun x => x.2.val ≤ t.val.length ∧ (x.1 || ((strS t).drop x.2.val).any (fun c => c == '.' || c == 'e' || c == 'E')) =
      (strS t).any (fun c => c == '.' || c == 'e' || c == 'E'))
    (fun y => y = (strS t).any (fun c => c == '.' || c == 'e' || c == 'E')) ?_ (false, 0#usize) ⟨by simp, by simp⟩
  · obtain ⟨y, hy, hq⟩ := H
    unfold eval.mods_json.has_frac_or_exp eval.mods_json.has_frac_or_exp_loop
    rw [show (fun (x : Bool × Usize) => match x with
        | (r1, i1) => eval.mods_json.has_frac_or_exp_loop.body t r1 i1) =
        (fun (x : Bool × Usize) => eval.mods_json.has_frac_or_exp_loop.body t x.1 x.2) from rfl, hy, hq]
  · rintro ⟨r, i⟩ ⟨h1, h2⟩
    simp only at h1 h2 ⊢
    by_cases hlt : i.val < t.val.length
    · right
      have hlt' : i < Slice.len t := (slice_lt_len_iff i t).mpr hlt
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
      rw [strS_drop t i.val hlt] at h2
      generalize hc : t.val[i.val]'hlt = c at h2
      simp only [List.any_cons, js_fracP_chOf] at h2
      refine ⟨(r || (decide (c.val = 46) || decide (c.val = 101) || decide (c.val = 69)), i1), ?_,
        ⟨by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
      · simp only [eval.mods_json.has_frac_or_exp_loop.body, hlt', if_true, slice_index_ok t i hlt, hc, bind_ok, hi1]
        by_cases a1 : c.val = 46
        · have : c = 46#u32 := UScalar.eq_of_val_eq a1
          simp [this]
        by_cases a2 : c.val = 101
        · have : c = 101#u32 := UScalar.eq_of_val_eq a2
          simp [this]
        by_cases a3 : c.val = 69
        · have : c = 69#u32 := UScalar.eq_of_val_eq a3
          simp [this]
        have b1 : ¬ c = 46#u32 := fun hh => a1 (by rw [hh]; rfl)
        have b2 : ¬ c = 101#u32 := fun hh => a2 (by rw [hh]; rfl)
        have b3 : ¬ c = 69#u32 := fun hh => a3 (by rw [hh]; rfl)
        simp [b1, b2, b3, a1, a2, a3]
      · dsimp only; rw [hi1v, ← h2]; simp only [Bool.or_assoc]
    · left
      have hlt' : ¬ i < Slice.len t := by rw [slice_lt_len_iff]; exact hlt
      refine ⟨r, by simp [eval.mods_json.has_frac_or_exp_loop.body, hlt'], ?_⟩
      rw [← h2, List.drop_eq_nil_of_le (by simp [strS_length]; omega)]; simp
end OsuProofs

namespace OsuProofs
open OsuImpl
theorem js_sub_all (s : Slice U32) (lo : Nat) : js_sub s lo s.val.length = (strS s).drop lo := by
  unfold js_sub; apply List.take_of_length_le; simp [strS_length]

theorem eval.mods_json.int_of_text_refines (t : Slice U32) (hs : ValidStr t) :
    ∃ neg m, eval.mods_json.int_of_text t = ok (neg, m) ∧ neg = (String.ofList (strS t)).startsWith "-" ∧
      m.val = min (if neg then ((String.ofList (strS t)).drop 1).toNat! else (String.ofList (strS t)).toNat!) (2^64) := by
  unfold eval.mods_json.int_of_text
  rw [eval.mods_json.starts_minus_refines, bind_ok]
  have hl : (Slice.len t).val = t.val.length := by simp
  by_cases hneg : (String.ofList (strS t)).startsWith "-" = true
  · have h1 : 1 ≤ t.val.length := by
      rw [js_startsWith_minus] at hneg
      cases ht : t.val with
      | nil => simp [strS, ht] at hneg
      | cons _ _ => simp
    obtain ⟨m, hm, hmv⟩ := eval.mods_json.nat_sat_refines t hs 1#usize (Slice.len t) (by simp; omega) (by simp)
    refine ⟨true, m, by simp [hneg, hm], hneg.symm, ?_⟩
    rw [hmv, if_pos rfl, js_toNat_str, js_toNat_drop1, hl, js_sub_all]; rfl
  · obtain ⟨m, hm, hmv⟩ := eval.mods_json.nat_sat_refines t hs 0#usize (Slice.len t) (by simp) (by simp)
    refine ⟨false, m, by simp [hneg, hm], by simpa using hneg, ?_⟩
    rw [hmv, if_neg (by simp), hl, js_sub_all]; rfl

/-- the spec's `-9223372036854775808 ≤ n && n ≤ 9223372036854775807`-style range test, `n = ±m` -/
theorem eval.mods_json.in_range_refines (neg : Bool) (m lo hi : U128) :
    eval.mods_json.in_range neg m lo hi =
      ok (decide (-(lo.val : Int) ≤ (if neg then -(m.val : Int) else m.val)) &&
          decide ((if neg then -(m.val : Int) else m.val) ≤ hi.val)) := by
  unfold eval.mods_json.in_range
  cases neg <;> simp [UScalar.le_equiv] <;> omega

theorem js_lo_mag : eval.mods_json.I64_LO_MAG.val = 2^63 := by unfold eval.mods_json.I64_LO_MAG; rfl
theorem js_hi : eval.mods_json.I64_HI.val = 2^63 - 1 := by unfold eval.mods_json.I64_HI; rfl

theorem eval.mods_json.long_of_refines (neg : Bool) (m : U128)
    (h : -(2^63 : Int) ≤ (if neg then -(m.val : Int) else m.val) ∧ (if neg then -(m.val : Int) else m.val) ≤ 2^63 - 1) :
    ∃ x, eval.mods_json.long_of neg m = ok x ∧ x.val = (if neg then -(m.val : Int) else m.val) := by
  unfold eval.mods_json.long_of
  have hc : m.val < 2^63 → (UScalar.hcast .I64 m).val = (m.val : Int) := by
    intro hm; rw [UScalar.hcast_val_eq]; simp; rw [Int.bmod_eq_of_le] <;> omega
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact ⟨_, rfl, hc (by omega)⟩
  | true =>
    simp only [↓reduceIte] at h ⊢
    by_cases he : m = eval.mods_json.I64_LO_MAG
    · refine ⟨core.num.I64.MIN, by simp [he], ?_⟩
      rw [he, js_lo_mag]; rfl
    · have hlt : m.val < 2^63 := by
        have : m.val ≠ 2^63 := fun hh => he (UScalar.eq_of_val_eq (by rw [hh, js_lo_mag]))
        omega
      have hmin : UScalar.hcast .I64 m ≠ IScalar.min .I64 := by
        intro hh; have h2 := hc hlt; rw [hh] at h2; simp [I64.min, I64.numBits] at h2
      obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (HNeg.hNeg.step (UScalar.hcast .I64 m) hmin)
      refine ⟨z, ?_, by rw [hzv, hc hlt]⟩
      simp only [he, if_false, lift, bind_ok]; exact hz
end OsuProofs
