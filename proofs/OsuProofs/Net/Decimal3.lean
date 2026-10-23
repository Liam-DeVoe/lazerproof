/-
`net::decimal` part 3: the 192-bit helpers (`U192 { hi : u64, lo : u128 }` ↦ `hi * 2^128 + lo`),
`ScaleResult`, `decimal * decimal`, `decimal / decimal`, `GetBits`.
-/
import OsuProofs.Net.Decimal2
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

def u192S (x : net.decimal.U192) : Nat := x.hi.val * 2^128 + x.lo.val

theorem u64_bounds (x : U64) : x.val < 2^64 := by have := x.hBounds; simpa using this

/-- Helper: `x = 0` on the 192-bit value. -/
theorem net.decimal.u192_is_zero_refines (x : net.decimal.U192) :
    net.decimal.u192_is_zero x = ok (u192S x == 0) := by
  have h1 := u128_bounds x.lo
  unfold net.decimal.u192_is_zero u192S
  by_cases hh : x.hi.val = 0
  · have : x.hi = 0#u64 := UScalar.eq_of_val_eq (by simp [hh])
    by_cases hl : x.lo.val = 0
    · have : x.lo = 0#u128 := UScalar.eq_of_val_eq (by simp [hl])
      simp [*]
    · have : ¬ x.lo = 0#u128 := fun e => hl (by rw [e]; rfl)
      simp [*]
  · have : ¬ x.hi = 0#u64 := fun e => hh (by rw [e]; rfl)
    simp [this]
    intro h; exact absurd h hh

theorem net.decimal.u192_ge_two96_refines (x : net.decimal.U192) :
    net.decimal.u192_ge_two96 x = ok (decide (u192S x ≥ 2^96)) := by
  have h1 := u128_bounds x.lo
  unfold net.decimal.u192_ge_two96 u192S
  by_cases hh : x.hi.val = 0
  · have : x.hi = 0#u64 := UScalar.eq_of_val_eq (by simp [hh])
    simp [this, TWO96_eq, hh]
    exact Iff.rfl
  · have : ¬ x.hi = 0#u64 := fun e => hh (by rw [e]; rfl)
    have : (x.hi != 0#u64) = true := by simpa using this
    simp only [this, ite_true]
    have p128 : (2:Nat)^128 = 340282366920938463463374607431768211456 := rfl
    have p96 : (2:Nat)^96 = 79228162514264337593543950336 := rfl
    have hge : x.hi.val * 2^128 + x.lo.val ≥ 2^96 := by rw [p128, p96]; omega
    simp only [hge, decide_true]

theorem log_hi_lo (h l : Nat) (hh : h ≠ 0) (hl : l < 2^128) :
    Nat.log 2 (h * 2^128 + l) = Nat.log 2 h + 128 := by
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · have := Nat.pow_log_le_self 2 hh
    rw [Nat.pow_add]; exact Nat.le_trans (Nat.mul_le_mul_right _ this) (Nat.le_add_right _ _)
  · have := Nat.lt_pow_succ_log_self (by decide : 1 < 2) h
    rw [show Nat.log 2 h + 128 + 1 = (Nat.log 2 h).succ + 128 by omega, Nat.pow_add]
    have : (h + 1) * 2^128 ≤ 2 ^ (Nat.log 2 h).succ * 2^128 := Nat.mul_le_mul_right _ this
    rw [Nat.add_mul, Nat.one_mul] at this
    omega

theorem log2_lt_iff (n k : Nat) (hn : n ≠ 0) : n.log2 < k ↔ n < 2^k := by
  rw [Nat.log2_lt hn]

/-- Helper: bit length `Nat.log2 x + 1` (0 for 0). -/
theorem net.decimal.u192_bitlen_refines (x : net.decimal.U192) :
    ∃ b, net.decimal.u192_bitlen x = ok b ∧ b.val = (if u192S x = 0 then 0 else (u192S x).log2 + 1) := by
  have h1 := u128_bounds x.lo
  have h2 := u64_bounds x.hi
  unfold net.decimal.u192_bitlen u192S
  simp only [Nat.log2_eq_log_two]
  by_cases hh : x.hi.val = 0
  · have : x.hi = 0#u64 := UScalar.eq_of_val_eq (by simp [hh])
    have hb : (x.hi != 0#u64) = false := by simp [this]
    simp only [hb, Bool.false_eq_true, ite_false, lift, bind_ok, hh, zero_mul, zero_add]
    have hlz : (core.num.U128.leading_zeros x.lo).val = (if x.lo.val = 0 then 128 else 128 - Nat.log 2 x.lo.val - 1) := by
      simp only [core.num.U128.leading_zeros, UScalar.val, BitVec.leadingZeros]
      by_cases hz : x.lo.bv = 0
      · rw [if_pos hz]; simp [hz]
      · have hz' : x.lo.bv.toNat ≠ 0 := by intro h; apply hz; exact BitVec.eq_of_toNat_eq (by simpa using h)
        rw [if_neg hz, if_neg hz']; simp; omega
    have hlog : x.lo.val ≠ 0 → Nat.log 2 x.lo.val < 128 := by
      intro hv; exact (Nat.log_lt_iff_lt_pow (by decide) hv).mpr (by simpa using h1)
    by_cases hz : x.lo.val = 0
    · have : core.num.U128.leading_zeros x.lo = 128#u32 := UScalar.eq_of_val_eq (by rw [hlz]; simp [hz])
      exact ⟨0#u32, by simp only [this]; rfl, by simp [hz]⟩
    · obtain ⟨r, hr, hrv, _⟩ := eq_ok_of_spec (U32.sub_spec (x := 128#u32) (y := core.num.U128.leading_zeros x.lo)
        (by rw [hlz]; simp [hz]; omega))
      refine ⟨r, hr, ?_⟩
      rw [hrv, hlz]; simp [hz]; have := hlog hz; omega
  · have : ¬ x.hi = 0#u64 := fun e => hh (by rw [e]; rfl)
    have hb : (x.hi != 0#u64) = true := by simpa using this
    simp only [hb, ite_true, lift, bind_ok]
    have hlz : (core.num.U64.leading_zeros x.hi).val = 64 - Nat.log 2 x.hi.val - 1 := by
      simp only [core.num.U64.leading_zeros, UScalar.val, BitVec.leadingZeros]
      have hz : ¬ x.hi.bv = 0 := by intro h; apply hh; simp [UScalar.val, h]
      have hz' : x.hi.bv.toNat ≠ 0 := hh
      rw [if_neg hz]; simp; omega
    have hlog : Nat.log 2 x.hi.val < 64 := (Nat.log_lt_iff_lt_pow (by decide) hh).mpr (by simpa using h2)
    obtain ⟨i1, hi1, hi1v, _⟩ := eq_ok_of_spec (U32.sub_spec (x := 64#u32) (y := core.num.U64.leading_zeros x.hi)
      (by rw [hlz]; simp; omega))
    obtain ⟨r, hr, hrv⟩ := eq_ok_of_spec (U32.add_spec (x := 128#u32) (y := i1)
      (by rw [hi1v, hlz]; simp [U32.max_eq]; omega))
    refine ⟨r, by simp [hi1, hr], ?_⟩
    have hne : x.hi.val * 2^128 + x.lo.val ≠ 0 := by
      intro h0; apply hh
      have := (Nat.eq_zero_of_add_eq_zero h0).1
      rcases Nat.mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (by positivity)
    rw [if_neg hne, log_hi_lo _ _ hh h1, hrv, hi1v, hlz]; simp; omega

theorem p128_eq : (2:Nat)^128 = 340282366920938463463374607431768211456 := rfl
theorem p64_eq : (2:Nat)^64 = 18446744073709551616 := rfl

/-- Helper: `x + 1` on 192 bits (guard: no overflow of the 192-bit value). -/
theorem net.decimal.u192_add_one_refines (x : net.decimal.U192) (hx : x.hi.val < 2^64 - 1) :
    ∃ y, net.decimal.u192_add_one x = ok y ∧ u192S y = u192S x + 1 := by
  have h1 := u128_bounds x.lo
  have hov := core.num.U128.overflowing_add_eq x.lo 1#u128
  unfold net.decimal.u192_add_one
  generalize hz : core.num.U128.overflowing_add x.lo 1#u128 = z at hov
  obtain ⟨lo, c⟩ := z
  simp only [lift, bind_ok]
  have hmx : UScalar.max .U128 = 340282366920938463463374607431768211455 := by
    simp [U128.max_eq]
  have hsz : UScalar.size .U128 = 340282366920938463463374607431768211456 := by
    simp [U128.size_eq]
  by_cases hc : x.lo.val + (1#u128 : U128).val > UScalar.max .U128
  · rw [if_pos hc] at hov
    obtain ⟨hlo, hcv⟩ := hov
    subst hcv
    obtain ⟨h1', hh1, hh1v⟩ := eq_ok_of_spec (U64.add_spec (x := x.hi) (y := 1#u64) (by simp [U64.max_eq]; omega))
    refine ⟨⟨h1', lo⟩, by simp [hh1], ?_⟩
    simp [u192S, hh1v]
    rw [hmx] at hc; rw [hsz] at hlo
    simp at hc hlo
    rw [p128_eq] at *; omega
  · rw [if_neg hc] at hov
    obtain ⟨hlo, hcv⟩ := hov
    subst hcv
    obtain ⟨h1', hh1, hh1v⟩ := eq_ok_of_spec (U64.add_spec (x := x.hi) (y := 0#u64) (by simp [U64.max_eq]; omega))
    refine ⟨⟨h1', lo⟩, by simp [hh1], ?_⟩
    simp [u192S, hh1v, hlo]; omega

theorem u128_shl64 (x : U128) : ∃ z, x <<< 64#i32 = ok z ∧ z.val = (x.val * 2^64) % 2^128 := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (UScalar.ShiftLeft_IScalar_spec x (y := 64#i32) (2^128) (by simp) (by simp)
    (by simp [U128.size_eq]))
  exact ⟨z, hz, by simpa [Nat.shiftLeft_eq] using hv.1⟩

/-- Helper: exact product of two values `< 2^96`. -/
theorem net.decimal.mul_u96_refines (a b : U128) (ha : a.val < 2^96) (hb : b.val < 2^96) :
    ∃ y, net.decimal.mul_u96 a b = ok y ∧ u192S y = a.val * b.val := by
  have p96 : (2:Nat)^96 = 79228162514264337593543950336 := rfl
  have hal := u128_and_mask64 a
  have hbl := u128_and_mask64 b
  obtain ⟨ah, hah, hahv⟩ := u128_shr64 a
  obtain ⟨bh, hbh, hbhv⟩ := u128_shr64 b
  generalize hA : (a &&& 18446744073709551615#u128) = al at hal
  generalize hB : (b &&& 18446744073709551615#u128) = bl at hbl
  have ha1 : al.val < 2^64 := by rw [hal]; exact Nat.mod_lt _ (by decide)
  have hb1 : bl.val < 2^64 := by rw [hbl]; exact Nat.mod_lt _ (by decide)
  have ha2 : ah.val < 2^32 := by rw [hahv]; rw [p96] at ha; rw [p64_eq]; omega
  have hb2 : bh.val < 2^32 := by rw [hbhv]; rw [p96] at hb; rw [p64_eq]; omega
  have hae : a.val = ah.val * 2^64 + al.val := by rw [hahv, hal]; exact (Nat.div_add_mod' _ _).symm
  have hbe : b.val = bh.val * 2^64 + bl.val := by rw [hbhv, hbl]; exact (Nat.div_add_mod' _ _).symm
  have hmax : U128.max = 2^128 - 1 := by simp [U128.max_eq]
  have m1 : al.val * bl.val < 2^128 := by
    calc al.val * bl.val < 2^64 * 2^64 := Nat.mul_lt_mul'' ha1 hb1
      _ = 2^128 := by norm_num
  obtain ⟨ll, hll, hllv⟩ := eq_ok_of_spec (U128.mul_spec (x := al) (y := bl) (by rw [hmax]; omega))
  have m2 : al.val * bh.val < 2^96 := by
    calc al.val * bh.val < 2^64 * 2^32 := Nat.mul_lt_mul'' ha1 hb2
      _ = 2^96 := by norm_num
  have m3 : ah.val * bl.val < 2^96 := by
    calc ah.val * bl.val < 2^32 * 2^64 := Nat.mul_lt_mul'' ha2 hb1
      _ = 2^96 := by norm_num
  have m4 : ah.val * bh.val < 2^64 := by
    calc ah.val * bh.val < 2^32 * 2^32 := Nat.mul_lt_mul'' ha2 hb2
      _ = 2^64 := by norm_num
  rw [p96] at m2 m3; rw [p64_eq] at m4
  obtain ⟨i0, hi0, hi0v⟩ := eq_ok_of_spec (U128.mul_spec (x := al) (y := bh) (by rw [hmax]; omega))
  obtain ⟨i1, hi1, hi1v⟩ := eq_ok_of_spec (U128.mul_spec (x := ah) (y := bl) (by rw [hmax]; omega))
  obtain ⟨mid, hmid, hmidv⟩ := eq_ok_of_spec (U128.add_spec (x := i0) (y := i1) (by rw [hmax, hi0v, hi1v]; omega))
  obtain ⟨hh, hhh, hhhv⟩ := eq_ok_of_spec (U128.mul_spec (x := ah) (y := bh) (by rw [hmax]; omega))
  have hml := u128_and_mask64 mid
  generalize hM : (mid &&& 18446744073709551615#u128) = i2 at hml
  obtain ⟨mlo, hmlo, hmlov⟩ := u128_shl64 i2
  have hi2l : i2.val < 2^64 := by rw [hml]; exact Nat.mod_lt _ (by decide)
  have hmlov' : mlo.val = i2.val * 2^64 := by
    rw [hmlov]; apply Nat.mod_eq_of_lt; rw [p64_eq] at hi2l ⊢; rw [p128_eq]; omega
  obtain ⟨mhi, hmhi, hmhiv⟩ := u128_shr64 mid
  have hov := core.num.U128.overflowing_add_eq ll mlo
  generalize hz : core.num.U128.overflowing_add ll mlo = z at hov
  obtain ⟨lo, c⟩ := z
  have hmx : UScalar.max .U128 = 340282366920938463463374607431768211455 := by simp [U128.max_eq]
  have hsz : UScalar.size .U128 = 340282366920938463463374607431768211456 := by simp [U128.size_eq]
  have hmide : mid.val = mhi.val * 2^64 + i2.val := by rw [hmhiv, hml]; exact (Nat.div_add_mod' _ _).symm
  have key : a.val * b.val = hh.val * 2^128 + mid.val * 2^64 + ll.val := by
    rw [hae, hbe, hhhv, hmidv, hi0v, hi1v, hllv]; ring
  simp only [p64_eq, p128_eq] at key hmide hmlov' hi2l
  have hab : a.val * b.val < 2^192 := by
    calc a.val * b.val < 2^96 * 2^96 := Nat.mul_lt_mul'' (by rw [p96]; exact ha) (by rw [p96]; exact hb)
      _ = 2^192 := by norm_num
  simp only [show (2:Nat)^192 = 6277101735386680763835789423207666416102355444464034512896 from rfl] at hab
  unfold net.decimal.mul_u96
  simp only [lift, bind_ok, hA, hah, hB, hbh, hll, hi0, hi1, hmid, hhh, hM, hmlo, hmhi, hz]
  obtain ⟨i3, hi3, hi3v⟩ := eq_ok_of_spec (U128.add_spec (x := hh) (y := mhi) (by rw [hmax, hhhv]; omega))
  by_cases hc : ll.val + mlo.val > UScalar.max .U128
  · rw [if_pos hc] at hov
    obtain ⟨hlo, hcv⟩ := hov
    subst hcv
    dsimp only at hlo
    obtain ⟨hi, hhi, hhiv⟩ := eq_ok_of_spec (U128.add_spec (x := i3) (y := 1#u128) (by rw [hmax, hi3v, hhhv]; simp; omega))
    refine ⟨⟨UScalar.cast .U64 hi, lo⟩, by simp [hi3, hhi], ?_⟩
    rw [hmx] at hc; rw [hsz] at hlo
    simp only [u192S, UScalar.cast_val_eq]
    have hhi' : hi.val < 2^64 := by rw [hhiv, hi3v]; simp; omega
    rw [Nat.mod_eq_of_lt (by simpa using hhi')]
    rw [hhiv, hi3v]; simp; omega
  · rw [if_neg hc] at hov
    obtain ⟨hlo, hcv⟩ := hov
    subst hcv
    dsimp only at hlo
    obtain ⟨hi, hhi, hhiv⟩ := eq_ok_of_spec (U128.add_spec (x := i3) (y := 0#u128) (by rw [hmax, hi3v, hhhv]; simp; omega))
    refine ⟨⟨UScalar.cast .U64 hi, lo⟩, by simp [hi3, hhi], ?_⟩
    rw [hmx] at hc
    simp only [u192S, UScalar.cast_val_eq]
    have hhi' : hi.val < 2^64 := by rw [hhiv, hi3v]; simp; omega
    rw [Nat.mod_eq_of_lt (by simpa using hhi')]
    rw [hhiv, hi3v]; simp; omega

def u32S (x : U32) : UInt32 := ⟨x.bv⟩

theorem u32S_eq_ofNat (x : U32) (n : Nat) (h : x.val = n % 2^32) : u32S x = UInt32.ofNat n := by
  apply UInt32.toNat_inj.mp
  show x.bv.toNat = _
  simpa using h

theorem net.decimal.get_bits_refines (d : net.decimal.NetDecimal) :
    ∃ a b c f, net.decimal.get_bits d = ok (a, b, c, f) ∧
      (u32S a, u32S b, u32S c, u32S f) = NetDecimal.getBits (decS d) := by
  have hm := u128_bounds d.mant
  obtain ⟨sh, hsh, hshv⟩ := eq_ok_of_spec (UScalar.ShiftLeft_IScalar_spec d.scale (y := 16#i32) (2^32) (by simp) (by simp)
    (by simp [U32.size_eq]))
  have hshv' : sh.val = (d.scale.val <<< 16) % 2^32 := by simpa using hshv.1
  obtain ⟨m32, hm32, hm32v⟩ := eq_ok_of_spec (UScalar.ShiftRight_IScalar_spec d.mant (y := 32#i32) (by simp) (by simp))
  obtain ⟨m64, hm64, hm64v⟩ := eq_ok_of_spec (UScalar.ShiftRight_IScalar_spec d.mant (y := 64#i32) (by simp) (by simp))
  have hm32v' : m32.val = d.mant.val >>> 32 := by simpa using hm32v.1
  have hm64v' : m64.val = d.mant.val >>> 64 := by simpa using hm64v.1
  have mask32 : ∀ x : U128, (x &&& 4294967295#u128).val = x.val % 2^32 := by
    intro x; simp only [UScalar.val, UScalar.bv_and]; rw [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod x.bv.toNat 32
  let sg : U32 := if d.neg then 2147483648#u32 else 0#u32
  refine ⟨UScalar.cast .U32 (d.mant &&& 4294967295#u128), UScalar.cast .U32 (m32 &&& 4294967295#u128),
    UScalar.cast .U32 (m64 &&& 4294967295#u128), sh ||| sg, ?_, ?_⟩
  · simp only [net.decimal.get_bits, hsh, bind_ok, lift, hm32, hm64, sg]
    split <;> simp
  · simp only [NetDecimal.getBits, decS, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply u32S_eq_ofNat; rw [UScalar.cast_val_eq, mask32]; simp
    · apply u32S_eq_ofNat; rw [UScalar.cast_val_eq, mask32, hm32v']; simp
    · apply u32S_eq_ofNat; rw [UScalar.cast_val_eq, mask32, hm64v']; simp
    · apply u32S_eq_ofNat
      simp only [UScalar.val, UScalar.bv_or]; rw [BitVec.toNat_or]
      rw [← UScalar.val, hshv', Nat.or_mod_two_pow]
      congr 1
      by_cases hn : d.neg = true <;> simp [sg, hn]

theorem net.decimal.of_bits_refines (lo mid hi flags : U32) :
    ∃ d, net.decimal.of_bits lo mid hi flags = ok d ∧
      decS d = NetDecimal.ofBits (u32S lo) (u32S mid) (u32S hi) (u32S flags) := by
  have hb := fun (x : U32) => (show x.val < 2^32 by have := x.hBounds; simpa using this)
  obtain ⟨f31, hf31, hf31v⟩ := eq_ok_of_spec (UScalar.ShiftRight_IScalar_spec flags (y := 31#i32) (by simp) (by simp))
  obtain ⟨f16, hf16, hf16v⟩ := eq_ok_of_spec (UScalar.ShiftRight_IScalar_spec flags (y := 16#i32) (by simp) (by simp))
  obtain ⟨m1, hm1, hm1v⟩ := eq_ok_of_spec (UScalar.ShiftLeft_IScalar_spec (UScalar.cast .U128 mid) (y := 32#i32) (2^128)
    (by simp) (by simp) (by simp [U128.size_eq]))
  obtain ⟨h1, hh1, hh1v⟩ := eq_ok_of_spec (UScalar.ShiftLeft_IScalar_spec (UScalar.cast .U128 hi) (y := 64#i32) (2^128)
    (by simp) (by simp) (by simp [U128.size_eq]))
  refine ⟨⟨f31 = 1#u32, (UScalar.cast .U128 lo ||| m1) ||| h1, f16 &&& 255#u32⟩,
    by simp [net.decimal.of_bits, hf31, hf16, hm1, hh1, lift], ?_⟩
  simp only [decS, NetDecimal.ofBits, NetDecimal.mk.injEq]
  have hu : ∀ x : U32, (u32S x).toNat = x.val := fun x => rfl
  have h31 : f31.val = flags.val >>> 31 := by simpa using hf31v.1
  have h16 : f16.val = flags.val >>> 16 := by simpa using hf16v.1
  refine ⟨?_, ?_, ?_⟩
  · rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, beq_iff_eq, uscalar_eq_val, h31, ← UInt32.toNat_inj, UInt32.toNat_shiftRight, hu]
    simp
  · have c1 : (UScalar.cast .U128 lo).val = lo.val := by rw [UScalar.cast_val_eq]; simp; have := hb lo; omega
    have c2 : m1.val = mid.val <<< 32 := by
      have := hm1v.1; simp at this; rw [this]
      have := hb mid; apply Nat.mod_eq_of_lt; rw [Nat.shiftLeft_eq]; omega
    have c3 : h1.val = hi.val <<< 64 := by
      have := hh1v.1; simp at this; rw [this]
      have := hb hi; apply Nat.mod_eq_of_lt; rw [Nat.shiftLeft_eq]; omega
    simp only [UScalar.val, UScalar.bv_or, BitVec.toNat_or] at c1 c2 c3 ⊢
    rw [c1, c2, c3]; rfl
  · simp only [UScalar.val, UScalar.bv_and, BitVec.toNat_and]
    rw [← UScalar.val, h16]
    simp [UInt32.toNat_and, UInt32.toNat_shiftRight, hu]

end OsuProofs
