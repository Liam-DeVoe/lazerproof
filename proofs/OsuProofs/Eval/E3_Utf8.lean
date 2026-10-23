/-
eval3 slice: the `eval.osr` UTF-8 validator of the D35 patch (`utf8_cont`, `utf8_seq_len`, `utf8_valid`) refines
the spec's well-formedness test. The spec (`OsuModel.Replay.Osr.readCompressedText`) takes the fast path when
Lean core's `String.fromUTF8? raw` succeeds; `String.fromUTF8?` is `if h : raw.IsValidUTF8`, decided by
`ByteArray.validateUTF8` (`validateUTF8_eq_true_iff`), a loop `validateUTF8.go` over `validateUTF8At` (core's
`parseFirstByte` + `verify₁..₄`) stepping by `utf8ByteSize` of the first byte.
Route: `e3_seqN` = the Rust `utf8_seq_len` over Nat byte values; `e3_validAt` (core's `validateUTF8At` = `seqN ≠ 0`,
via `e3_asm2..4`, the Nat values of core's `assemble₂..₄Unchecked`, and single-byte tables proved by `decide +kernel`
over all 256 bytes); `e3_seqS_eq` (`seqS`, the spec step length, = `seqN`); `e3_seq_len_eq` (Rust = `seqN`);
`e3_loop` (Rust loop in lockstep with `validateUTF8.go`, strong induction on `len - i`).
-/
import OsuProofs.Eval.Osr
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open ByteArray.utf8DecodeChar?
theorem e3_cont_nat : ∀ n : Nat, n < 256 → ((n &&& 192 = 128) ↔ (128 ≤ n ∧ n < 192)) := by decide +kernel
theorem e3_and_mod (x n m : Nat) (hm : m = 2^n - 1) : x &&& m = x % 2^n := by
  subst hm; exact Nat.and_two_pow_sub_one_eq_mod x n
theorem e3_or_mul (a b k : Nat) (hb : b < 2^k) : (a * 2^k) ||| b = a * 2^k + b := by
  rw [Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt hb]
theorem e3_or_dvd (A B k : Nat) (hA : 2^k ∣ A) (hB : B < 2^k) : A ||| B = A + B := by
  obtain ⟨q, rfl⟩ := hA; rw [Nat.mul_comm]; exact e3_or_mul q B k hB
theorem e3_asm2 (w x : UInt8) : (assemble₂Unchecked w x).toNat = w.toNat % 32 * 64 + x.toNat % 64 := by
  simp only [assemble₂Unchecked, UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, UInt8.toNat_and,
    UInt8.reduceToNat, UInt32.reduceToNat, Nat.reduceMod]
  rw [e3_and_mod _ 5 31 rfl, e3_and_mod _ 6 63 rfl, Nat.mod_eq_of_lt (a := (w.toNat % 2^5) <<< 6) (by
    rw [Nat.shiftLeft_eq]; have := Nat.mod_lt w.toNat (show 2^5 > 0 by decide); omega)]
  rw [Nat.shiftLeft_eq, e3_or_mul _ _ _ (Nat.mod_lt _ (by decide))]; rfl
theorem e3_asm3 (w x y : UInt8) : (assemble₃Unchecked w x y).toNat = w.toNat % 16 * 4096 + x.toNat % 64 * 64 + y.toNat % 64 := by
  simp only [assemble₃Unchecked, UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, UInt8.toNat_and,
    UInt8.reduceToNat, UInt32.reduceToNat, Nat.reduceMod]
  rw [e3_and_mod w.toNat 4 15 rfl, e3_and_mod x.toNat 6 63 rfl, e3_and_mod y.toNat 6 63 rfl, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have ha := Nat.mod_lt w.toNat (show 2^4 > 0 by decide)
  have hb := Nat.mod_lt x.toNat (show 2^6 > 0 by decide)
  have hc := Nat.mod_lt y.toNat (show 2^6 > 0 by decide)
  generalize w.toNat % 2^4 = a at *
  generalize x.toNat % 2^6 = b at *
  generalize y.toNat % 2^6 = c at *
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [e3_or_dvd (a * 2^12) (b * 2^6) 12 ⟨a, by ring⟩ (by omega),
    e3_or_dvd (a * 2^12 + b * 2^6) c 6 ⟨a * 2^6 + b, by ring⟩ hc]
theorem e3_asm4 (w x y z : UInt8) : (assemble₄Unchecked w x y z).toNat =
    w.toNat % 8 * 262144 + x.toNat % 64 * 4096 + y.toNat % 64 * 64 + z.toNat % 64 := by
  simp only [assemble₄Unchecked, UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, UInt8.toNat_and,
    UInt8.reduceToNat, UInt32.reduceToNat, Nat.reduceMod]
  rw [e3_and_mod w.toNat 3 7 rfl, e3_and_mod x.toNat 6 63 rfl, e3_and_mod y.toNat 6 63 rfl, e3_and_mod z.toNat 6 63 rfl,
    Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have ha := Nat.mod_lt w.toNat (show 2^3 > 0 by decide)
  have hb := Nat.mod_lt x.toNat (show 2^6 > 0 by decide)
  have hc := Nat.mod_lt y.toNat (show 2^6 > 0 by decide)
  have hd := Nat.mod_lt z.toNat (show 2^6 > 0 by decide)
  generalize w.toNat % 2^3 = a at *
  generalize x.toNat % 2^6 = b at *
  generalize y.toNat % 2^6 = c at *
  generalize z.toNat % 2^6 = d at *
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [e3_or_dvd (a * 2^18) (b * 2^12) 18 ⟨a, by ring⟩ (by omega),
    e3_or_dvd (a * 2^18 + b * 2^12) (c * 2^6) 12 ⟨a * 2^6 + b, by ring⟩ (by omega),
    e3_or_dvd (a * 2^18 + b * 2^12 + c * 2^6) d 6 ⟨a * 2^12 + b * 2^6 + c, by ring⟩ hd]
end OsuProofs

namespace OsuProofs
open ByteArray.utf8DecodeChar?

/-- UTF-8 continuation byte (Nat form) -/
def e3_cn (x : Nat) : Bool := 128 ≤ x && x < 192

/-- `utf8_seq_len` over a byte function (Nat form of the Rust) -/
def e3_seqN (B : Nat → Nat) (n i : Nat) : Nat :=
  if B i < 128 then 1
  else if B i < 194 then 0
  else if B i < 224 then (if i + 1 < n ∧ e3_cn (B (i+1)) = true then 2 else 0)
  else if B i < 240 then
    (if i + 2 < n ∧ (if B i = 224 then 160 else 128) ≤ B (i+1) ∧ B (i+1) ≤ (if B i = 237 then 159 else 191) ∧
      e3_cn (B (i+2)) = true then 3 else 0)
  else if B i < 245 then
    (if i + 3 < n ∧ (if B i = 240 then 144 else 128) ≤ B (i+1) ∧ B (i+1) ≤ (if B i = 244 then 143 else 191) ∧
      e3_cn (B (i+2)) = true ∧ e3_cn (B (i+3)) = true then 4 else 0)
  else 0

theorem e3_u8_all (P : UInt8 → Prop) (h : ∀ n, n < 256 → P (UInt8.ofNat n)) : ∀ x, P x := fun x => by
  have := h x.toNat x.toNat_lt; rwa [UInt8.ofNat_toNat] at this

theorem e3_inv_cont : ∀ x : UInt8, isInvalidContinuationByte x = !e3_cn x.toNat :=
  e3_u8_all _ (by decide +kernel)

def e3_fbN : FirstByte → Nat
  | .invalid => 0 | .done => 1 | .oneMore => 2 | .twoMore => 3 | .threeMore => 4

theorem e3_pfb : ∀ w : UInt8, e3_fbN (parseFirstByte w) =
    (if w.toNat < 128 then 1 else if w.toNat < 192 then 0 else if w.toNat < 224 then 2 else if w.toNat < 240 then 3
     else if w.toNat < 248 then 4 else 0) :=
  e3_u8_all _ (by decide +kernel)

theorem e3_ubs : ∀ w : UInt8, (if w &&& 0x80 = 0 then 1 else if w &&& 0xe0 = 0xc0 then 2 else if w &&& 0xf0 = 0xe0 then 3 else 4) =
    (if w.toNat < 128 then 1 else if w.toNat < 224 then 2 else if w.toNat < 240 then 3 else 4) ∨ (128 ≤ w.toNat ∧ w.toNat < 192) :=
  e3_u8_all _ (by decide +kernel)
end OsuProofs

namespace OsuProofs
theorem e3_ite3 (x y z : Bool) (q : Prop) [Decidable q] :
    (if (!x || !y || !z) = true then false else decide q) = decide ((x = true ∧ y = true ∧ z = true) ∧ q) := by
  cases x <;> cases y <;> cases z <;> simp
theorem e3_cn_iff (x : Nat) : e3_cn x = true ↔ 128 ≤ x ∧ x < 192 := by simp [e3_cn]
theorem e3_v4 (a b c d n i : Nat) (ha : 240 ≤ a ∧ a < 248) (hb : b < 256) (hc : c < 256) (hd : d < 256) (h3 : i + 3 < n) :
    (if (!e3_cn b || !e3_cn c || !e3_cn d) = true then false
    else decide (65536 ≤ a % 8 * 262144 + b % 64 * 4096 + c % 64 * 64 + d % 64 ∧
          a % 8 * 262144 + b % 64 * 4096 + c % 64 * 64 + d % 64 ≤ 1114111)) =
    decide ((if a < 128 then 1 else if a < 194 then 0
            else if a < 224 then if i + 1 < n ∧ e3_cn b = true then 2 else 0
            else if a < 240 then
                if i + 2 < n ∧ (if a = 224 then 160 else 128) ≤ b ∧ (b ≤ if a = 237 then 159 else 191) ∧ e3_cn c = true then 3
                else 0
            else if a < 245 then
                if i + 3 < n ∧ (if a = 240 then 144 else 128) ≤ b ∧ (b ≤ if a = 244 then 143 else 191) ∧ e3_cn c = true ∧
                  e3_cn d = true then 4 else 0
            else 0) ≠ 0) := by
  rw [if_neg (show ¬ a < 128 by omega), if_neg (show ¬ a < 194 by omega), if_neg (show ¬ a < 224 by omega), if_neg (show ¬ a < 240 by omega)]
  rw [e3_ite3, decide_eq_decide]
  simp only [e3_cn_iff]
  split_ifs <;> omega

theorem e3_v4n (a b c d n i : Nat) (ha : 240 ≤ a ∧ a < 248) (h3 : ¬ i + 3 < n) :
    false =
    decide ((if a < 128 then 1 else if a < 194 then 0
            else if a < 224 then if i + 1 < n ∧ e3_cn b = true then 2 else 0
            else if a < 240 then
                if i + 2 < n ∧ (if a = 224 then 160 else 128) ≤ b ∧ (b ≤ if a = 237 then 159 else 191) ∧ e3_cn c = true then 3
                else 0
            else if a < 245 then
                if i + 3 < n ∧ (if a = 240 then 144 else 128) ≤ b ∧ (b ≤ if a = 244 then 143 else 191) ∧ e3_cn c = true ∧
                  e3_cn d = true then 4 else 0
            else 0) ≠ 0) := by
  rw [if_neg (show ¬ a < 128 by omega), if_neg (show ¬ a < 194 by omega), if_neg (show ¬ a < 224 by omega), if_neg (show ¬ a < 240 by omega)]
  by_cases h5 : a < 245
  · rw [if_pos h5]; simp [h3]
  · rw [if_neg h5]; simp
end OsuProofs

namespace OsuProofs
open ByteArray.utf8DecodeChar?
theorem e3_validAt (B : ByteArray) (i : Nat) (hi : i < B.size) :
    B.validateUTF8At i = decide (e3_seqN (fun j => B[j]!.toNat) B.size i ≠ 0) := by
  unfold ByteArray.validateUTF8At
  rw [dif_pos hi]
  have hp := e3_pfb B[i]
  have e0 : B[i]! = B[i] := getElem!_pos B i hi
  have l0 := B[i].toNat_lt
  unfold e3_seqN
  dsimp only
  simp only [e0]
  split
  next hh =>
    rw [hh] at hp; simp only [e3_fbN] at hp
    generalize B[i].toNat = a at *
    split_ifs at hp ⊢ <;> first | omega | simp
  next hh =>
    rw [hh] at hp; simp only [e3_fbN] at hp
    generalize B[i].toNat = a at *
    split_ifs at hp ⊢ <;> first | omega | simp [verify₁]
  next hh =>
    rw [hh] at hp; simp only [e3_fbN] at hp
    by_cases h1 : i + 1 < B.size
    · rw [dif_pos h1]
      have e1 : B[i+1]! = B[i+1] := getElem!_pos B (i+1) h1
      have l1 := B[i+1].toNat_lt
      simp only [e1]
      unfold verify₂
      dsimp only; simp only [e3_inv_cont, UInt32.le_iff_toNat_le, e3_asm2, UInt32.reduceToNat]
      generalize B[i].toNat = a at *
      generalize B[i+1].toNat = b at *
      unfold e3_cn
      split_ifs at hp ⊢ <;> simp_all <;> omega
    · rw [dif_neg h1]
      generalize B[i].toNat = a at *
      split_ifs at hp ⊢ <;> simp_all <;> omega
  next hh =>
    rw [hh] at hp; simp only [e3_fbN] at hp
    by_cases h2 : i + 2 < B.size
    · rw [dif_pos h2]
      have e1 : B[i+1]! = B[i+1] := getElem!_pos B (i+1) (by omega)
      have e2 : B[i+2]! = B[i+2] := getElem!_pos B (i+2) h2
      have l1 := B[i+1].toNat_lt
      have l2 := B[i+2].toNat_lt
      simp only [e1, e2]
      unfold verify₃
      dsimp only; simp only [e3_inv_cont, UInt32.le_iff_toNat_le, UInt32.lt_iff_toNat_lt, e3_asm3, UInt32.reduceToNat]
      generalize B[i].toNat = a at *
      generalize B[i+1].toNat = b at *
      generalize B[i+2].toNat = c at *
      unfold e3_cn
      split_ifs at hp ⊢ <;> simp_all <;> omega
    · rw [dif_neg h2]
      generalize B[i].toNat = a at *
      split_ifs at hp ⊢ <;> simp_all <;> omega
  next hh =>
    rw [hh] at hp; simp only [e3_fbN] at hp
    have ha : 240 ≤ B[i].toNat ∧ B[i].toNat < 248 := by
      clear * - hp; generalize B[i].toNat = a at hp ⊢; split_ifs at hp <;> omega
    clear hp
    by_cases h3 : i + 3 < B.size
    · rw [dif_pos h3]
      have e1 : B[i+1]! = B[i+1] := getElem!_pos B (i+1) (by omega)
      have e2 : B[i+2]! = B[i+2] := getElem!_pos B (i+2) (by omega)
      have e3 : B[i+3]! = B[i+3] := getElem!_pos B (i+3) h3
      have l1 := B[i+1].toNat_lt
      have l2 := B[i+2].toNat_lt
      have l3 := B[i+3].toNat_lt
      simp only [e1, e2, e3]
      unfold verify₄
      dsimp only; simp only [e3_inv_cont, UInt32.le_iff_toNat_le, e3_asm4, UInt32.reduceToNat]
      exact e3_v4 _ _ _ _ B.size i ha l1 l2 l3 h3
    · rw [dif_neg h3]
      exact e3_v4n _ _ _ _ B.size i ha h3
end OsuProofs

namespace OsuProofs
open OsuImpl
theorem e3_bget (b : Slice U8) (j : Nat) (h : j < b.val.length) : ((bytesS b)[j]!).toNat = (b.val[j]'h).val := by
  rw [getElem!_pos (bytesS b) j (by rw [bytesS_size]; exact h)]
  simp [bytesS, ByteArray.getElem_eq_getElem_data]
end OsuProofs
namespace OsuProofs
open OsuImpl
theorem e3_cont_eq (x : U8) : eval.osr.utf8_cont x = ok (e3_cn x.val) := by
  unfold eval.osr.utf8_cont
  simp only [lift, bind_ok]
  congr 1
  have h := e3_cont_nat x.val (by scalar_tac)
  have e : (x &&& 192#u8 = 128#u8) ↔ (x.val &&& 192 = 128) := by
    constructor
    · intro hh; have := congrArg UScalar.val hh; simpa using this
    · intro hh; apply UScalar.eq_of_val_eq; simpa using hh
  by_cases hc : x.val &&& 192 = 128
  · have := h.mp hc; simp [e3_cn, e.mpr hc, this.1, this.2]
  · have : ¬ (128 ≤ x.val ∧ x.val < 192) := fun hh => hc (h.mpr hh)
    have hn : ¬ (x &&& 192#u8 = 128#u8) := fun hh => hc (e.mp hh)
    simp only [hn, decide_false, e3_cn]
    by_cases h1 : 128 ≤ x.val <;> simp_all
end OsuProofs

namespace OsuProofs
open OsuImpl
theorem e3_add (a k : Usize) (h : a.val + k.val ≤ Usize.max) : ∃ c : Usize, a + k = ok c ∧ c.val = a.val + k.val := by
  obtain ⟨c, hc, hcv⟩ := eq_ok_of_spec (Usize.add_spec (x := a) (y := k) (by scalar_tac))
  exact ⟨c, hc, by simpa using hcv⟩

theorem e3_seq_len_eq (b : Slice U8) (i : Usize) (hi : i.val < b.val.length) (hb : b.val.length + 4 ≤ Usize.max) :
    ∃ k, eval.osr.utf8_seq_len b i = ok k ∧ k.val = e3_seqN (fun j => (bytesS b)[j]!.toNat) b.val.length i.val := by
  unfold eval.osr.utf8_seq_len
  rw [slice_index_ok b i hi]; simp only [bind_ok, e3_cont_eq]
  have e0 := e3_bget b i.val hi
  generalize hc0 : b.val[i.val]'hi = c0 at e0 ⊢
  unfold e3_seqN
  dsimp only
  simp only [e0]
  have l0 : c0.val < 256 := by scalar_tac
  by_cases h1 : c0.val < 128
  · rw [if_pos (show c0 < 128#u8 by scalar_tac), if_pos h1]; exact ⟨_, rfl, rfl⟩
  rw [if_neg (show ¬ c0 < 128#u8 by scalar_tac), if_neg h1]
  by_cases h2 : c0.val < 194
  · rw [if_pos (show c0 < 194#u8 by scalar_tac), if_pos h2]; exact ⟨_, rfl, rfl⟩
  rw [if_neg (show ¬ c0 < 194#u8 by scalar_tac), if_neg h2]
  by_cases h3 : c0.val < 224
  · rw [if_pos (show c0 < 224#u8 by scalar_tac), if_pos h3]
    obtain ⟨u1, hu1, hu1v⟩ := e3_add i 1#usize (by scalar_tac)
    rw [hu1]; simp only [bind_ok]
    by_cases hl : i.val + 1 < b.val.length
    · rw [if_pos ((slice_lt_len_iff _ _).mpr (by simp at hu1v; omega)), slice_index_ok b u1 (by simp at hu1v; omega)]
      simp only [bind_ok]
      have e1 := e3_bget b (i.val + 1) hl
      simp only [e1]
      have : (b.val[u1.val]'(by simp at hu1v; omega)) = b.val[i.val + 1] := by simp at hu1v; simp [hu1v]
      rw [this]
      by_cases hc : e3_cn (b.val[i.val + 1]).val = true
      · rw [if_pos hc, if_pos ⟨hl, hc⟩]; exact ⟨_, rfl, rfl⟩
      · rw [if_neg hc, if_neg (fun hh => hc hh.2)]; exact ⟨_, rfl, rfl⟩
    · rw [if_neg (fun hh => hl (by rw [slice_lt_len_iff] at hh; simp at hu1v; omega)), if_neg (fun hh => hl hh.1)]
      exact ⟨_, rfl, rfl⟩
  rw [if_neg (show ¬ c0 < 224#u8 by scalar_tac), if_neg h3]
  have ok_ite : ∀ (p : Prop) [Decidable p] (x y : U8), (if p then ok x else ok y : Result U8) = ok (if p then x else y) := by
    intro p _ x y; split <;> rfl
  have le_ite : ∀ (p : Prop) [Decidable p] (x y z : U8), ((if p then x else y) ≤ z) ↔ ((if p then x.val else y.val) ≤ z.val) := by
    intro p _ x y z; split <;> exact UScalar.le_equiv _ _
  have ite_le : ∀ (p : Prop) [Decidable p] (x y z : U8), (z ≤ (if p then x else y)) ↔ (z.val ≤ (if p then x.val else y.val)) := by
    intro p _ x y z; split <;> exact UScalar.le_equiv _ _
  have q224 : (c0 = 224#u8) ↔ c0.val = 224 := ⟨fun h => by rw [h]; rfl, fun h => by apply UScalar.eq_of_val_eq; simpa using h⟩
  have q237 : (c0 = 237#u8) ↔ c0.val = 237 := ⟨fun h => by rw [h]; rfl, fun h => by apply UScalar.eq_of_val_eq; simpa using h⟩
  have q240 : (c0 = 240#u8) ↔ c0.val = 240 := ⟨fun h => by rw [h]; rfl, fun h => by apply UScalar.eq_of_val_eq; simpa using h⟩
  have q244 : (c0 = 244#u8) ↔ c0.val = 244 := ⟨fun h => by rw [h]; rfl, fun h => by apply UScalar.eq_of_val_eq; simpa using h⟩
  by_cases h4 : c0.val < 240
  · rw [if_pos (show c0 < 240#u8 by scalar_tac), if_pos h4]
    simp only [ok_ite, bind_ok]
    obtain ⟨u2, hu2, hu2v⟩ := e3_add i 2#usize (by scalar_tac)
    rw [hu2]; simp only [bind_ok]
    by_cases hl : i.val + 2 < b.val.length
    · rw [if_pos ((slice_lt_len_iff _ _).mpr (by simp at hu2v; omega))]
      obtain ⟨u1, hu1, hu1v⟩ := e3_add i 1#usize (by scalar_tac)
      rw [hu1]; simp only [bind_ok]
      rw [slice_index_ok b u1 (by simp at hu1v; omega), slice_index_ok b u2 (by simp at hu2v; omega)]
      simp only [bind_ok]
      have e1 := e3_bget b (i.val + 1) (by omega)
      have e2 := e3_bget b (i.val + 2) hl
      simp only [e1, e2]
      have : (b.val[u1.val]'(by simp at hu1v; omega)) = b.val[i.val + 1] := by simp at hu1v; simp [hu1v]
      rw [this]
      have : (b.val[u2.val]'(by simp at hu2v; omega)) = b.val[i.val + 2] := by simp at hu2v; simp [hu2v]
      rw [this]
      simp only [le_ite, ite_le, q224, q237]
      split_ifs <;> refine ⟨_, rfl, ?_⟩ <;> simp_all <;> omega
    · rw [if_neg (fun hh => hl (by rw [slice_lt_len_iff] at hh; simp at hu2v; omega)), if_neg (fun hh => hl hh.1)]
      exact ⟨_, rfl, rfl⟩
  rw [if_neg (show ¬ c0 < 240#u8 by scalar_tac), if_neg h4]
  by_cases h5 : c0.val < 245
  · rw [if_pos (show c0 < 245#u8 by scalar_tac), if_pos h5]
    simp only [ok_ite, bind_ok]
    obtain ⟨u3, hu3, hu3v⟩ := e3_add i 3#usize (by scalar_tac)
    rw [hu3]; simp only [bind_ok]
    by_cases hl : i.val + 3 < b.val.length
    · rw [if_pos ((slice_lt_len_iff _ _).mpr (by simp at hu3v; omega))]
      obtain ⟨u1, hu1, hu1v⟩ := e3_add i 1#usize (by scalar_tac)
      obtain ⟨u2, hu2, hu2v⟩ := e3_add i 2#usize (by scalar_tac)
      rw [hu1]; simp only [bind_ok]
      rw [slice_index_ok b u1 (by simp at hu1v; omega)]
      simp only [bind_ok, hu2, slice_index_ok b u2 (by simp at hu2v; omega), slice_index_ok b u3 (by simp at hu3v; omega)]
      have e1 := e3_bget b (i.val + 1) (by omega)
      have e2 := e3_bget b (i.val + 2) (by omega)
      have e3 := e3_bget b (i.val + 3) hl
      simp only [e1, e2, e3]
      have : (b.val[u1.val]'(by simp at hu1v; omega)) = b.val[i.val + 1] := by simp at hu1v; simp [hu1v]
      rw [this]
      have : (b.val[u2.val]'(by simp at hu2v; omega)) = b.val[i.val + 2] := by simp at hu2v; simp [hu2v]
      rw [this]
      have : (b.val[u3.val]'(by simp at hu3v; omega)) = b.val[i.val + 3] := by simp at hu3v; simp [hu3v]
      rw [this]
      simp only [le_ite, ite_le, q240, q244]
      split_ifs <;> refine ⟨_, rfl, ?_⟩ <;> simp_all <;> omega
    · rw [if_neg (fun hh => hl (by rw [slice_lt_len_iff] at hh; simp at hu3v; omega)), if_neg (fun hh => hl hh.1)]
      exact ⟨_, rfl, rfl⟩
  rw [if_neg (show ¬ c0 < 245#u8 by scalar_tac), if_neg h5]
  exact ⟨_, rfl, rfl⟩
end OsuProofs

namespace OsuProofs
open OsuImpl

/-- One step of the spec's `ByteArray.validateUTF8.go` at `i`: the length of the well-formed sequence at `i`
(`validateUTF8At` + `utf8ByteSize` of the first byte), 0 when ill-formed. -/
def e3_seqS (B : ByteArray) (i : Nat) : Nat :=
  if h : B.validateUTF8At i = true then
    (B[i]'(ByteArray.lt_size_of_validateUTF8At h)).utf8ByteSize (ByteArray.isUTF8FirstByte_of_validateUTF8At h)
  else 0

theorem e3_seqS_eq (B : ByteArray) (i : Nat) (hi : i < B.size) :
    e3_seqS B i = e3_seqN (fun j => B[j]!.toNat) B.size i := by
  have hv := e3_validAt B i hi
  unfold e3_seqS
  split
  · rename_i h
    rw [hv] at h
    have hne : e3_seqN (fun j => B[j]!.toNat) B.size i ≠ 0 := by simpa using h
    have hu := e3_ubs B[i]
    unfold UInt8.utf8ByteSize
    have e0 : B[i]! = B[i] := getElem!_pos B i hi
    revert hne
    unfold e3_seqN
    dsimp only
    simp only [e0]
    generalize B[i].toNat = a at hu ⊢
    intro hne
    rcases hu with hu | hu
    · rw [hu]; split_ifs at hne ⊢ <;> omega
    · split_ifs at hne <;> omega
  · rename_i h
    rw [hv] at h
    simp at h; exact h.symm
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem e3_seqN_le (B : Nat → Nat) (n i : Nat) (hi : i < n) : i + e3_seqN B n i ≤ n := by
  unfold e3_seqN; split_ifs <;> omega

theorem e3_seq_len_S (b : Slice U8) (i : Usize) (hi : i.val < b.val.length) (hb : b.val.length + 4 ≤ Usize.max) :
    ∃ k, eval.osr.utf8_seq_len b i = ok k ∧ k.val = e3_seqS (bytesS b) i.val ∧ i.val + k.val ≤ b.val.length := by
  obtain ⟨k, hk, hkv⟩ := e3_seq_len_eq b i hi hb
  refine ⟨k, hk, ?_, by rw [hkv]; exact e3_seqN_le _ _ _ hi⟩
  rw [hkv, e3_seqS_eq _ _ (by rw [bytesS_size]; exact hi), bytesS_size]

theorem e3_go_congr (B : ByteArray) (j j' : Nat) (h : j ≤ B.size) (h' : j' ≤ B.size) (e : j = j') :
    ByteArray.validateUTF8.go B j h = ByteArray.validateUTF8.go B j' h' := by subst e; rfl

theorem e3_loop_false (b : Slice U8) (n i : Usize) :
    eval.osr.utf8_valid_loop b n i false = ok false := by
  unfold eval.osr.utf8_valid_loop
  rw [loop_unfold]; simp [eval.osr.utf8_valid_loop.body]

theorem e3_loop (b : Slice U8) (hb : b.val.length + 4 ≤ Usize.max) :
    ∀ (i : Usize) (hi : i.val ≤ (bytesS b).size),
      eval.osr.utf8_valid_loop b (Slice.len b) i true = ok (ByteArray.validateUTF8.go (bytesS b) i.val hi) := by
  intro i
  induction hk : b.val.length - i.val using Nat.strong_induction_on generalizing i with
  | _ m ih =>
    intro hi
    have hsz := bytesS_size b
    unfold eval.osr.utf8_valid_loop
    rw [loop_unfold]
    rw [ByteArray.validateUTF8.go]
    by_cases hlt : i.val < b.val.length
    · rw [dif_pos (by omega)]
      obtain ⟨k, hk', hkv, hkb⟩ := e3_seq_len_S b i hlt hb
      simp only [eval.osr.utf8_valid_loop.body, if_true, (show i < Slice.len b by rw [slice_lt_len_iff]; exact hlt), hk', bind_ok]
      unfold e3_seqS at hkv
      have hl0 := e3_loop_false b (Slice.len b) i
      unfold eval.osr.utf8_valid_loop at hl0
      by_cases hk0 : k = 0#usize
      · simp only [hk0, if_true, bind_ok]
        simp only [eval.osr.utf8_valid_loop.body] at hl0
        rw [hl0]
        split
        · rfl
        · rename_i ht
          rw [dif_pos ht, hk0] at hkv
          have hpos := UInt8.utf8ByteSize_pos _ (ByteArray.isUTF8FirstByte_of_validateUTF8At ht)
          simp at hkv; omega
      · simp only [hk0, if_false]
        split
        · rename_i hf
          rw [dif_neg (by rw [hf]; simp)] at hkv
          exact absurd (show k = 0#usize by scalar_tac) hk0
        · rename_i ht
          rw [dif_pos ht] at hkv
          have hpos := UInt8.utf8ByteSize_pos _ (ByteArray.isUTF8FirstByte_of_validateUTF8At ht)
          obtain ⟨i1, hi1, hi1v⟩ := e3_add i k (by scalar_tac)
          rw [hi1]; simp only [bind_ok]
          have ih' := ih (b.val.length - i1.val) (by omega) i1 rfl (by omega)
          unfold eval.osr.utf8_valid_loop at ih'
          simp only [eval.osr.utf8_valid_loop.body] at ih'
          rw [ih']
          congr 1
          exact e3_go_congr _ _ _ _ _ (by omega)
    · rw [dif_neg (by omega)]
      simp [eval.osr.utf8_valid_loop.body, (show ¬ i < Slice.len b by rw [slice_lt_len_iff]; exact hlt)]
end OsuProofs

namespace OsuProofs
open OsuImpl

/-- `utf8_cont` is core's continuation-byte test (`¬ isInvalidContinuationByte`, used by `validateUTF8At`). -/
theorem eval.osr.utf8_cont_refines (x : U8) :
    eval.osr.utf8_cont x = ok (!ByteArray.utf8DecodeChar?.isInvalidContinuationByte (UInt8.ofBitVec x.bv)) := by
  rw [e3_cont_eq, e3_inv_cont]
  simp [UInt8.toNat_ofBitVec]

/-- `utf8_seq_len b i` is one step of the spec's `String.fromUTF8?` validation (`ByteArray.validateUTF8.go`):
the byte length of the well-formed sequence at `i` (`validateUTF8At`, then `utf8ByteSize` of the first byte),
or 0 when it is ill-formed. -/
theorem eval.osr.utf8_seq_len_refines (b : Slice U8) (i : Usize) (hi : i.val < b.val.length)
    (hb : b.val.length + 4 ≤ Usize.max) :
    ∃ k, eval.osr.utf8_seq_len b i = ok k ∧ k.val = e3_seqS (bytesS b) i.val := by
  obtain ⟨k, hk, hkv, -⟩ := e3_seq_len_S b i hi hb
  exact ⟨k, hk, hkv⟩

/-- `utf8_valid b` decides whether the spec's `String.fromUTF8?` accepts the bytes (the fast path of
`readCompressedText`). -/
theorem eval.osr.utf8_valid_refines (b : Slice U8) (hb : b.val.length + 4 ≤ Usize.max) :
    eval.osr.utf8_valid b = ok (String.fromUTF8? (bytesS b)).isSome := by
  unfold eval.osr.utf8_valid
  rw [e3_loop b hb 0#usize (by simp)]
  congr 1
  have e : ByteArray.validateUTF8.go (bytesS b) (0#usize : Usize).val (by simp) = (bytesS b).validateUTF8 := by
    unfold ByteArray.validateUTF8; rfl
  rw [e]
  unfold String.fromUTF8?
  by_cases h : (bytesS b).IsValidUTF8
  · rw [dif_pos h]; simpa using h
  · rw [dif_neg h]; simpa using h
end OsuProofs

