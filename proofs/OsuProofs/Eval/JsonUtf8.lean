/-
The `utf8` fact of the end-to-end assumptions (`ev_utf8Fact`, Eval/E2EBase.lean), proved (json agent):
Lean's `String.fromUTF8? raw = some s` implies that the model's lazer-style decoder `decodeUtf8 raw 0`
(Beatmap/Text.lean, U+FFFD maximal-subpart replacement) returns exactly `s.toList`, and that `raw` does not start
with `00 00 FE` (0xFE never occurs in UTF-8). Route: `raw = s.toList.utf8Encode` (core); per character the
encoding bytes (`js_enc1..4`, from core's `utf8EncodeChar_eq_*`) make `u8dec` return `(c, c.utf8Size)`
(`js_u8dec1..4`: Nat bit arithmetic; surrogates/overlongs excluded by `Char.valid`); `js_loop` walks the
`decodeUtf8_eq` iteration (`iterId utf8G`) character by character.
-/
import OsuProofs.Beatmap.Text
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result

namespace OsuProofs
theorem js_or_hi (x p k : Nat) (h : x < 2^k) : (x ||| p * 2^k) = p * 2^k + x := by
  rw [Nat.lor_comm, Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt h]
theorem js_and_lo (x p k : Nat) (h : x < 2^k) : (p * 2^k + x) &&& (2^k - 1) = x := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt h]
theorem js_cont_ok : ∀ r, r < 64 → (r + 128) &&& 192 = 128 := by decide

theorem js_enc_size (c : Char) :
    (c.utf8Size = 1 ∧ c.toNat < 128) ∨ (c.utf8Size = 2 ∧ 128 ≤ c.toNat ∧ c.toNat < 2048) ∨
    (c.utf8Size = 3 ∧ 2048 ≤ c.toNat ∧ c.toNat < 65536) ∨ (c.utf8Size = 4 ∧ 65536 ≤ c.toNat) := by
  unfold Char.utf8Size
  simp only [UInt32.le_iff_toNat_le, Char.toNat] 
  split_ifs <;> simp_all <;> omega

theorem js_byte_gen (x p w : Nat) (hw : w ≤ 8) : ((x % 256) &&& (2^w - 1)) ||| (p * 2^w) = p * 2^w + x % 2^w := by
  rw [Nat.and_two_pow_sub_one_eq_mod, js_or_hi _ _ _ (Nat.mod_lt _ (by positivity))]
  congr 1
  have : 2^w ∣ 256 := by
    have : (256 : Nat) = 2^w * 2^(8-w) := by rw [← Nat.pow_add, Nat.add_sub_cancel' hw]
    rw [this]; exact Dvd.intro _ rfl
  exact Nat.mod_mod_of_dvd x this
theorem js_b5 (x : Nat) : (x % 256 &&& 31 ||| 192) = x % 32 + 192 := by
  have := js_byte_gen x 6 5 (by omega); simp at this; omega
theorem js_b6 (x : Nat) : (x % 256 &&& 63 ||| 128) = x % 64 + 128 := by
  have := js_byte_gen x 2 6 (by omega); simp at this; omega
theorem js_b4 (x : Nat) : (x % 256 &&& 15 ||| 224) = x % 16 + 224 := by
  have := js_byte_gen x 14 4 (by omega); simp at this; omega
theorem js_b3 (x : Nat) : (x % 256 &&& 7 ||| 240) = x % 8 + 240 := by
  have := js_byte_gen x 30 3 (by omega); simp at this; omega

theorem js_enc2 (c : Char) (h : c.utf8Size = 2) :
    (String.utf8EncodeChar c).map UInt8.toNat = [c.toNat / 64 % 32 + 192, c.toNat % 64 + 128] := by
  rw [String.utf8EncodeChar_eq_cons_cons h]
  simp only [List.map_cons, List.map_nil, UInt8.toNat_or, UInt8.toNat_and, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight,
    UInt8.reduceToNat, Nat.shiftRight_eq_div_pow, UInt32.reduceToNat, Nat.reduceMod, Nat.reducePow, js_b5, js_b6]
  rfl

theorem js_enc1 (c : Char) (h : c.utf8Size = 1) (hc : c.toNat < 128) :
    (String.utf8EncodeChar c).map UInt8.toNat = [c.toNat] := by
  rw [String.utf8EncodeChar_eq_singleton h]
  simp only [List.map_cons, List.map_nil, UInt32.toNat_toUInt8]
  congr 1; show c.toNat % 2^8 = c.toNat; omega

theorem js_enc3 (c : Char) (h : c.utf8Size = 3) :
    (String.utf8EncodeChar c).map UInt8.toNat = [c.toNat / 4096 % 16 + 224, c.toNat / 64 % 64 + 128, c.toNat % 64 + 128] := by
  rw [String.utf8EncodeChar_eq_cons_cons_cons h]
  simp only [List.map_cons, List.map_nil, UInt8.toNat_or, UInt8.toNat_and, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight,
    UInt8.reduceToNat, Nat.shiftRight_eq_div_pow, UInt32.reduceToNat, Nat.reduceMod, Nat.reducePow, js_b4, js_b6]
  rfl

theorem js_enc4 (c : Char) (h : c.utf8Size = 4) :
    (String.utf8EncodeChar c).map UInt8.toNat =
      [c.toNat / 262144 % 8 + 240, c.toNat / 4096 % 64 + 128, c.toNat / 64 % 64 + 128, c.toNat % 64 + 128] := by
  rw [String.utf8EncodeChar_eq_cons_cons_cons_cons h]
  simp only [List.map_cons, List.map_nil, UInt8.toNat_or, UInt8.toNat_and, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight,
    UInt8.reduceToNat, Nat.shiftRight_eq_div_pow, UInt32.reduceToNat, Nat.reduceMod, Nat.reducePow, js_b3, js_b6]
  rfl
end OsuProofs

namespace OsuProofs
theorem js_andlo' (x p k : Nat) (h : x < 2^k) (m : Nat) (hm : m = 2^k - 1) : (x + p * 2^k) &&& m = x := by
  subst hm; rw [Nat.add_comm]; exact js_and_lo x p k h

theorem js_u8dec2 (B : Nat → Nat) (n i c : Nat) (hc1 : 128 ≤ c) (hc2 : c < 2048) (hn : i + 2 ≤ n)
    (h0 : B i = c / 64 % 32 + 192) (h1 : B (i+1) = c % 64 + 128) : u8dec B n i = (c, 2) := by
  unfold u8dec
  rw [h0, h1]
  have e0 : (c / 64 % 32 + 192) &&& 31 = c / 64 % 32 := js_andlo' _ 6 5 (by omega) _ rfl
  have e1 : (c % 64 + 128) &&& 63 = c % 64 := js_andlo' _ 2 6 (by omega) _ rfl
  have e2 : (c % 64 + 128) &&& 192 = 128 := js_cont_ok _ (by omega)
  rw [e0, e1, e2, Nat.shiftLeft_eq, Nat.lor_comm, js_or_hi _ _ _ (by omega : c % 64 < 2^6)]
  simp only [show ¬ (c / 64 % 32 + 192 < 128) by omega, show ¬ (c / 64 % 32 + 192 < 194) by omega,
    show c / 64 % 32 + 192 < 224 by omega, show i + 1 < n by omega, if_true, if_false, and_self]
  congr 1; omega

theorem js_u8dec1 (B : Nat → Nat) (n i c : Nat) (hc : c < 128) (h0 : B i = c) : u8dec B n i = (c, 1) := by
  unfold u8dec; rw [h0]; simp [hc]

theorem js_u8dec3 (B : Nat → Nat) (n i c : Nat) (hc1 : 2048 ≤ c) (hc2 : c < 65536) (hs : c < 0xd800 ∨ 0xdfff < c)
    (hn : i + 3 ≤ n) (h0 : B i = c / 4096 % 16 + 224) (h1 : B (i+1) = c / 64 % 64 + 128) (h2 : B (i+2) = c % 64 + 128) :
    u8dec B n i = (c, 3) := by
  unfold u8dec
  rw [h0, h1, h2]
  have e0 : (c / 4096 % 16 + 224) &&& 15 = c / 4096 % 16 := js_andlo' _ 14 4 (by omega) _ rfl
  have e1 : (c / 64 % 64 + 128) &&& 63 = c / 64 % 64 := js_andlo' _ 2 6 (by omega) _ rfl
  have e2 : (c % 64 + 128) &&& 63 = c % 64 := js_andlo' _ 2 6 (by omega) _ rfl
  have e3 : (c % 64 + 128) &&& 192 = 128 := js_cont_ok _ (by omega)
  have v1 : (c / 4096 % 16) <<< 12 ||| (c / 64 % 64) <<< 6 = (c / 4096 % 16 * 64 + c / 64 % 64) * 2^6 := by
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.lor_comm, js_or_hi _ _ _ (by omega : c / 64 % 64 * 2^6 < 2^12)]; ring
  have v2 : (c / 64 % 64 + 128) &&& 63 = c / 64 % 64 := e1
  simp only [show ¬ (c / 4096 % 16 + 224 < 128) by omega, show ¬ (c / 4096 % 16 + 224 < 194) by omega,
    show ¬ (c / 4096 % 16 + 224 < 224) by omega, show c / 4096 % 16 + 224 < 240 by omega, if_true, if_false]
  rw [if_pos, if_pos]
  · rw [e0, e2, v2, v1, Nat.lor_comm, js_or_hi _ _ _ (by omega : c % 64 < 2^6)]
    congr 1; omega
  · exact ⟨by omega, e3⟩
  · refine ⟨by omega, ?_, ?_⟩ <;> split <;> omega

theorem js_u8dec4 (B : Nat → Nat) (n i c : Nat) (hc1 : 65536 ≤ c) (hc2 : c < 0x110000)
    (hn : i + 4 ≤ n) (h0 : B i = c / 262144 % 8 + 240) (h1 : B (i+1) = c / 4096 % 64 + 128)
    (h2 : B (i+2) = c / 64 % 64 + 128) (h3 : B (i+3) = c % 64 + 128) :
    u8dec B n i = (c, 4) := by
  unfold u8dec
  rw [h0, h1, h2, h3]
  have e0 : (c / 262144 % 8 + 240) &&& 7 = c / 262144 % 8 := js_andlo' _ 30 3 (by omega) _ rfl
  have e1 : (c / 4096 % 64 + 128) &&& 63 = c / 4096 % 64 := js_andlo' _ 2 6 (by omega) _ rfl
  have e2 : (c / 64 % 64 + 128) &&& 63 = c / 64 % 64 := js_andlo' _ 2 6 (by omega) _ rfl
  have e3 : (c % 64 + 128) &&& 63 = c % 64 := js_andlo' _ 2 6 (by omega) _ rfl
  have e4 : (c / 64 % 64 + 128) &&& 192 = 128 := js_cont_ok _ (by omega)
  have e5 : (c % 64 + 128) &&& 192 = 128 := js_cont_ok _ (by omega)
  have v1 : (c / 262144 % 8) <<< 18 ||| (c / 4096 % 64) <<< 12 = (c / 262144 % 8 * 64 + c / 4096 % 64) * 2^12 := by
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.lor_comm, js_or_hi _ _ _ (by omega : c / 4096 % 64 * 2^12 < 2^18)]; ring
  have v2 : (c / 262144 % 8 * 64 + c / 4096 % 64) * 2^12 ||| (c / 64 % 64) <<< 6 =
      ((c / 262144 % 8 * 64 + c / 4096 % 64) * 64 + c / 64 % 64) * 2^6 := by
    rw [Nat.shiftLeft_eq, Nat.lor_comm, js_or_hi _ _ _ (by omega : c / 64 % 64 * 2^6 < 2^12)]; ring
  simp only [show ¬ (c / 262144 % 8 + 240 < 128) by omega, show ¬ (c / 262144 % 8 + 240 < 194) by omega,
    show ¬ (c / 262144 % 8 + 240 < 224) by omega, show ¬ (c / 262144 % 8 + 240 < 240) by omega,
    show c / 262144 % 8 + 240 < 245 by omega, if_true, if_false]
  rw [if_pos, if_pos, if_pos]
  · rw [e0, e1, e2, e3, v1, v2, Nat.lor_comm, js_or_hi _ _ _ (by omega : c % 64 < 2^6)]
    congr 1; omega
  · exact ⟨by omega, e5⟩
  · exact ⟨by omega, e4⟩
  · refine ⟨by omega, ?_, ?_⟩ <;> split <;> omega
end OsuProofs

namespace OsuProofs
open OsuModel.Beatmap
def js_B (b : ByteArray) (j : Nat) : Nat := (b[j]!).toNat
theorem js_repl : ('�' : Char) = Char.ofNat 65533 := rfl

theorem js_utf8G_lt (b : ByteArray) (out : _root_.Array Char) (i : Nat) (hi : i < b.size) :
    utf8G b (out, i) = .yield (out.push (Char.ofNat (u8dec (js_B b) b.size i).1),
      i + (u8dec (js_B b) b.size i).2) := by
  unfold utf8G u8dec js_B
  dsimp only
  generalize b[i]! = y0
  generalize b[i+1]! = y1
  generalize b[i+2]! = y2
  generalize b[i+3]! = y3
  generalize b.size = n at *
  simp only [hi, if_true, UInt8.lt_iff_toNat_lt, UInt8.le_iff_toNat_le,
    ← UInt8.toNat_inj, beq_iff_eq, UInt8.toNat_and, Bool.and_eq_true, decide_eq_true_eq, UInt8.reduceToNat,
    apply_ite UInt8.toNat, and_assoc, js_repl]
  split_ifs <;> simp_all
end OsuProofs

namespace OsuProofs
open OsuModel.Beatmap
def js_bl (l : List Char) : List UInt8 := l.flatMap String.utf8EncodeChar

theorem js_bl_size (l : List Char) : l.utf8Encode.size = (js_bl l).length := by
  simp [List.utf8Encode, js_bl]

theorem js_bl_get (l : List Char) (k : Nat) (h : k < (js_bl l).length) :
    (l.utf8Encode)[k]! = (js_bl l)[k] := by
  have h' : k < l.utf8Encode.size := by rw [js_bl_size]; exact h
  rw [getElem!_pos (l.utf8Encode) k h']
  show (l.utf8Encode).data[k] = _
  simp only [List.utf8Encode, js_bl]
  simp

theorem js_enc_len (c : Char) : (String.utf8EncodeChar c).length = c.utf8Size := String.length_utf8EncodeChar c

theorem js_bl_split (pre post : List Char) (c : Char) :
    js_bl (pre ++ c :: post) = js_bl pre ++ String.utf8EncodeChar c ++ js_bl post := by
  simp [js_bl, List.flatMap_append]

/-- the bytes of `c` at its offset in the encoding -/
theorem js_B_at (pre post : List Char) (c : Char) (j : Nat) (hj : j < (String.utf8EncodeChar c).length) :
    js_B (pre ++ c :: post).utf8Encode ((js_bl pre).length + j) = ((String.utf8EncodeChar c)[j]).toNat := by
  unfold js_B
  rw [js_bl_get _ _ (by have := js_enc_len c; rw [js_bl_split]; simp; omega)]
  congr 1
  simp only [js_bl_split]
  rw [List.getElem_append]
  split
  · rw [List.getElem_append]; split
    · omega
    · simp
  · rename_i hh; simp only [List.length_append] at hh; omega
end OsuProofs

namespace OsuProofs
open OsuModel.Beatmap
theorem js_char_bounds (c : Char) : c.toNat < 0xd800 ∨ (0xdfff < c.toNat ∧ c.toNat < 0x110000) := by
  have := c.valid
  simp only [UInt32.isValidChar, Nat.isValidChar, Char.toNat] at this ⊢
  omega

theorem js_byte_of (c : Char) (L : List Nat) (e : (String.utf8EncodeChar c).map UInt8.toNat = L) (j : Nat)
    (hj : j < (String.utf8EncodeChar c).length) : ((String.utf8EncodeChar c)[j]).toNat = L.getD j 0 := by
  rw [← e]; simp [List.getElem?_eq_getElem hj]

theorem js_step (pre post : List Char) (c : Char) (out : _root_.Array Char) :
    utf8G (pre ++ c :: post).utf8Encode (out, (js_bl pre).length) =
      .yield (out.push c, (js_bl pre).length + c.utf8Size) := by
  have hsz : (js_bl pre).length + c.utf8Size ≤ (pre ++ c :: post).utf8Encode.size := by
    rw [js_bl_size, js_bl_split]; simp [js_enc_len]
  have hpos : 0 < c.utf8Size := Char.utf8Size_pos c
  rw [js_utf8G_lt _ _ _ (by omega)]
  have hB := js_B_at pre post c
  have hb := js_char_bounds c
  have hD : u8dec (js_B (pre ++ c :: post).utf8Encode) (pre ++ c :: post).utf8Encode.size (js_bl pre).length =
      (c.toNat, c.utf8Size) := by
    rcases js_enc_size c with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · have e := js_enc1 c h1 h2
      have v0 := hB 0 (by rw [js_enc_len]; omega)
      rw [js_byte_of c _ e 0 (by rw [js_enc_len]; omega)] at v0
      simp only [List.getD_cons_succ, List.getD_cons_zero] at v0
      simp only [Nat.add_zero] at v0
      rw [js_u8dec1 _ _ _ _ h2 v0, h1]
    · have e := js_enc2 c h1
      have v0 := hB 0 (by rw [js_enc_len]; omega)
      have v1 := hB 1 (by rw [js_enc_len]; omega)
      rw [js_byte_of c _ e 0 (by rw [js_enc_len]; omega)] at v0
      simp only [List.getD_cons_succ, List.getD_cons_zero] at v0
      rw [js_byte_of c _ e 1 (by rw [js_enc_len]; omega)] at v1
      simp only [List.getD_cons_succ, List.getD_cons_zero] at v1
      simp only [Nat.add_zero] at v0
      rw [js_u8dec2 _ _ _ _ h2 h3 (by omega) v0 v1, h1]
    · have e := js_enc3 c h1
      have v0 := hB 0 (by rw [js_enc_len]; omega)
      have v1 := hB 1 (by rw [js_enc_len]; omega)
      have v2 := hB 2 (by rw [js_enc_len]; omega)
      rw [js_byte_of c _ e 0 (by rw [js_enc_len]; omega)] at v0
      simp only [List.getD_cons_succ, List.getD_cons_zero] at v0
      rw [js_byte_of c _ e 1 (by rw [js_enc_len]; omega)] at v1
      simp only [List.getD_cons_succ, List.getD_cons_zero] at v1
      rw [js_byte_of c _ e 2 (by rw [js_enc_len]; omega)] at v2
      simp only [List.getD_cons_succ, List.getD_cons_zero] at v2
      simp only [Nat.add_zero] at v0
      rw [js_u8dec3 _ _ _ _ h2 h3 (by omega) (by omega) v0 v1 v2, h1]
    · have e := js_enc4 c h1
      have v0 := hB 0 (by rw [js_enc_len]; omega)
      have v1 := hB 1 (by rw [js_enc_len]; omega)
      have v2 := hB 2 (by rw [js_enc_len]; omega)
      have v3 := hB 3 (by rw [js_enc_len]; omega)
      rw [js_byte_of c _ e 0 (by rw [js_enc_len]; omega)] at v0
      simp only [List.getD_cons_succ, List.getD_cons_zero] at v0
      rw [js_byte_of c _ e 1 (by rw [js_enc_len]; omega)] at v1
      simp only [List.getD_cons_succ, List.getD_cons_zero] at v1
      rw [js_byte_of c _ e 2 (by rw [js_enc_len]; omega)] at v2
      simp only [List.getD_cons_succ, List.getD_cons_zero] at v2
      rw [js_byte_of c _ e 3 (by rw [js_enc_len]; omega)] at v3
      simp only [List.getD_cons_succ, List.getD_cons_zero] at v3
      simp only [Nat.add_zero] at v0
      rw [js_u8dec4 _ _ _ _ h2 (by omega) (by omega) v0 v1 v2 v3, h1]
  rw [hD]
  simp [Char.ofNat_toNat]
end OsuProofs

namespace OsuProofs
open OsuModel.Beatmap
theorem js_iterId_fix {β} (g : β → ForInStep β) (s : β) (h : g s = .yield s) : ∀ k, iterId g k s = s := by
  intro k; induction k with
  | zero => rfl
  | succ k ih => simp only [iterId, h]; exact ih

theorem js_bl_len_ge (l : List Char) : l.length ≤ (js_bl l).length := by
  induction l with
  | nil => simp [js_bl]
  | cons c l ih =>
    have := Char.utf8Size_pos c
    simp only [js_bl, List.flatMap_cons, List.length_append, js_enc_len, List.length_cons] at ih ⊢; omega

theorem js_loop (L : List Char) : ∀ (post pre : List Char) (out : _root_.Array Char) (k : Nat), pre ++ post = L →
    out.toList = pre → post.length + 1 ≤ k →
    (iterId (utf8G L.utf8Encode) k (out, (js_bl pre).length)).1.toList = L := by
  intro post
  induction post with
  | nil =>
    intro pre out k hL hout hk
    simp only [List.append_nil] at hL; subst hL
    have hfix : utf8G pre.utf8Encode (out, (js_bl pre).length) = .yield (out, (js_bl pre).length) := by
      simp [utf8G, js_bl_size]
    rw [js_iterId_fix _ _ hfix]; exact hout
  | cons c post ih =>
    intro pre out k hL hout hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    subst hL
    simp only [iterId, js_step]
    have e1 : (js_bl pre).length + c.utf8Size = (js_bl (pre ++ [c])).length := by
      simp [js_bl, js_enc_len]
    rw [e1]
    exact ih (pre ++ [c]) (out.push c) k (by simp) (by simp [hout]) (by simp at hk; omega)

theorem js_enc_ne_fe (c : Char) (x : UInt8) (hx : x ∈ String.utf8EncodeChar c) : x ≠ 0xFE := by
  intro hfe; subst hfe
  have hm : (254 : Nat) ∈ (String.utf8EncodeChar c).map UInt8.toNat := List.mem_map_of_mem hx
  rcases js_enc_size c with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · rw [js_enc1 c h1 h2] at hm; simp at hm; omega
  · rw [js_enc2 c h1] at hm; simp at hm; omega
  · rw [js_enc3 c h1] at hm; simp at hm; omega
  · rw [js_enc4 c h1] at hm; simp at hm; omega

theorem js_bl_ne_fe (l : List Char) (x : UInt8) (hx : x ∈ js_bl l) : x ≠ 0xFE := by
  simp only [js_bl, List.mem_flatMap] at hx
  obtain ⟨c, -, hc⟩ := hx
  exact js_enc_ne_fe c x hc

/-- The `utf8` fact of the eval agent's `EvalAssumptions` (`ev_utf8Fact`, Eval/E2EBase.lean), proved. -/
theorem js_utf8Fact : ∀ (raw : ByteArray) (s : String), String.fromUTF8? raw = some s →
    s.toList = (decodeUtf8 raw 0).toList ∧ ¬ (3 ≤ raw.size ∧ raw[0]! = 0 ∧ raw[1]! = 0 ∧ raw[2]! = 0xFE) := by
  intro raw s h
  have hraw : raw = s.toList.utf8Encode := by
    unfold String.fromUTF8? at h
    split at h
    · simp at h; subst h; simp [String.fromUTF8]
    · simp at h
  subst hraw
  refine ⟨?_, ?_⟩
  · rw [decodeUtf8_eq]
    have := js_loop s.toList s.toList [] (Array.mkEmpty s.toList.utf8Encode.size) (s.toList.utf8Encode.size + 1)
      (by simp) (by simp) (by have := js_bl_len_ge s.toList; rw [js_bl_size]; omega)
    simpa [js_bl] using this.symm
  · rintro ⟨h3, -, -, h2⟩
    rw [js_bl_get _ 2 (by rw [← js_bl_size]; omega)] at h2
    exact js_bl_ne_fe s.toList _ (List.getElem_mem _) h2
end OsuProofs

