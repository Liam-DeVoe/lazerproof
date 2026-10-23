/-
Facts about Lean's IEEE float model (`Float.Model`, `Float32.Model`) used by the refinement
proofs, mainly NaN propagation: the trusted primitives `to_bits`/`is_negative` are partial (fail on
NaN), so proofs must show their arguments are not NaN. No Aeneas import (fast to check).
-/
import OsuModel.Net
set_option linter.unusedSimpArgs false
open Float.Model (UnpackedFloat Format)
open Float.Model.UnpackedFloat

namespace OsuProofs.FloatFacts

/-! ## Unpacked level -/

theorem roundWithAccuracy_isNaN (spec s m e a) : (roundWithAccuracy spec s m e a).isNaN = false := by
  unfold roundWithAccuracy; dsimp only; split <;> rfl

theorem round_isNaN (spec s m e) : (UnpackedFloat.round spec s m e).isNaN = false := by
  unfold UnpackedFloat.round; exact roundWithAccuracy_isNaN ..

theorem normalize_isNaN (spec m e s) : (UnpackedFloat.normalize spec m e s).isNaN = false := by
  unfold UnpackedFloat.normalize; split <;> first | rfl | exact round_isNaN ..

theorem unpack_isNaN {spec : Format} (b : BitVec spec.numBits) :
    (unpack spec b).isNaN = (unpackExponent b == -1#_ && unpackMantissa b != 0#_) := by
  unfold unpack; dsimp only
  split
  · split <;> simp_all [isNaN]
  · split
    · split <;> simp_all [isNaN]
    · simp_all [isNaN]

theorem unpack_pack_isNaN (spec : Format) (f : UnpackedFloat) : (unpack spec (pack spec f)).isNaN = f.isNaN := by
  rw [unpack_isNaN]
  have hm := spec.hm
  have he := spec.he
  fun_cases pack with
  | case1 =>
    simp [packedNaN, isNaN]
    intro h
    have h2 := congrArg BitVec.toNat h
    simp [BitVec.toNat_shiftLeft] at h2
    obtain ⟨k, hk⟩ : ∃ k, spec.mantissaBitsWithoutImplicit = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hm).symm⟩
    rw [hk] at h2
    simp [Nat.shiftLeft_eq, Nat.pow_succ] at h2
    have hp : 0 < 2 ^ k := Nat.two_pow_pos k
    rw [Nat.mod_eq_of_lt (by omega)] at h2
    omega
  | case2 s => simp [packedInfinity, isNaN]
  | case3 s =>
    simp [packedZero, isNaN]
  | case4 s m e hm biasedExponent h => simp [packedInfinity, isNaN]
  | case5 s m e hm actualMantissaBits biasedExponent h₁ h₂ =>
    suffices biasedExponent % 2 ^ spec.exponentBits ≠ 2 ^ spec.exponentBits - 1 by
      simp [BitVec.neg_one_eq_allOnes, ← BitVec.toNat_inj, this, isNaN]
    suffices biasedExponent < 2 ^ spec.exponentBits - 1 by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    omega
  | case6 s m e hm actualMantissaBits biasedExponent h₁ h₂ =>
    simp [isNaN]; omega



theorem add_isNaN (spec : Format) (x y : UnpackedFloat) (hx : x.isNaN = false) (hy : y.isNaN = false)
    (hi : y.isInf = false) : (add spec x y).isNaN = false := by
  cases x <;> cases y <;> simp [isNaN, isInf] at hx hy hi <;> simp only [add] <;>
    first | rfl | exact normalize_isNaN .. | (split <;> rfl)

theorem sub_isNaN (spec : Format) (x y : UnpackedFloat) (hx : x.isNaN = false) (hy : y.isNaN = false)
    (hi : y.isInf = false) : (sub spec x y).isNaN = false := by
  cases x <;> cases y <;> simp [isNaN, isInf] at hx hy hi <;> simp only [sub] <;>
    first | rfl | exact normalize_isNaN .. | (split <;> rfl)

theorem mul_isNaN (spec : Format) (x y : UnpackedFloat) (hx : x.isNaN = false) (hy : y.isNaN = false)
    (hix : x.isInf = false) (hi : y.isInf = false) : (mul spec x y).isNaN = false := by
  cases x <;> cases y <;> simp [isNaN, isInf] at hx hy hix hi <;> simp only [mul] <;>
    first | rfl | exact roundWithAccuracy_isNaN ..

/-! ## Float level -/
theorem f64_isNaN_def (a : Float) : a.isNaN = (unpack Format.binary64 a.toBits.toBitVec).isNaN := rfl

theorem f64_isNaN_add (a b : Float) (ha : a.isNaN = false) (hb : b.isNaN = false) (hi : b.isInf = false) :
    (a + b).isNaN = false := by
  have := add_isNaN Format.binary64 a.toModel.unpack b.toModel.unpack ha hb hi
  show (unpack Format.binary64 (UInt64.ofBitVec (pack Format.binary64 _)).toBitVec).isNaN = false
  rw [UInt64.toBitVec_ofBitVec, unpack_pack_isNaN]; exact this

theorem f64_isNaN_sub (a b : Float) (ha : a.isNaN = false) (hb : b.isNaN = false) (hi : b.isInf = false) :
    (a - b).isNaN = false := by
  have := sub_isNaN Format.binary64 a.toModel.unpack b.toModel.unpack ha hb hi
  show (unpack Format.binary64 (UInt64.ofBitVec (pack Format.binary64 _)).toBitVec).isNaN = false
  rw [UInt64.toBitVec_ofBitVec, unpack_pack_isNaN]; exact this

theorem f64_isNaN_mul (a b : Float) (ha : a.isNaN = false) (hb : b.isNaN = false)
    (hia : a.isInf = false) (hi : b.isInf = false) : (a * b).isNaN = false := by
  have := mul_isNaN Format.binary64 a.toModel.unpack b.toModel.unpack ha hb hia hi
  show (unpack Format.binary64 (UInt64.ofBitVec (pack Format.binary64 _)).toBitVec).isNaN = false
  rw [UInt64.toBitVec_ofBitVec, unpack_pack_isNaN]; exact this

theorem f32_isNaN_add (a b : Float32) (ha : a.isNaN = false) (hb : b.isNaN = false) (hi : b.isInf = false) :
    (a + b).isNaN = false := by
  have := add_isNaN Format.binary32 a.toModel.unpack b.toModel.unpack ha hb hi
  show (unpack Format.binary32 (UInt32.ofBitVec (pack Format.binary32 _)).toBitVec).isNaN = false
  rw [UInt32.toBitVec_ofBitVec, unpack_pack_isNaN]; exact this

theorem f32_isNaN_sub (a b : Float32) (ha : a.isNaN = false) (hb : b.isNaN = false) (hi : b.isInf = false) :
    (a - b).isNaN = false := by
  have := sub_isNaN Format.binary32 a.toModel.unpack b.toModel.unpack ha hb hi
  show (unpack Format.binary32 (UInt32.ofBitVec (pack Format.binary32 _)).toBitVec).isNaN = false
  rw [UInt32.toBitVec_ofBitVec, unpack_pack_isNaN]; exact this

theorem f32_isNaN_mul (a b : Float32) (ha : a.isNaN = false) (hb : b.isNaN = false)
    (hia : a.isInf = false) (hi : b.isInf = false) : (a * b).isNaN = false := by
  have := mul_isNaN Format.binary32 a.toModel.unpack b.toModel.unpack ha hb hia hi
  show (unpack Format.binary32 (UInt32.ofBitVec (pack Format.binary32 _)).toBitVec).isNaN = false
  rw [UInt32.toBitVec_ofBitVec, unpack_pack_isNaN]; exact this

/-! ## NaN is unique (the model canonicalises NaN) -/
theorem f32_isNaN_eq (x : Float32) (h : x.isNaN = true) : x = Float32.nan := by
  have h' : (unpack Format.binary32 x.toModel.toBits.toBitVec).isNaN = true := h
  rw [unpack_isNaN] at h'
  simp at h'
  have hb := x.toModel.valid.eq_packedNaN h'.1 h'.2
  rcases x with ⟨⟨bits, valid⟩⟩
  show Float32.ofModel ⟨bits, valid⟩ = Float32.ofModel ⟨_, _⟩
  congr 2
  apply UInt32.toBitVec_inj.mp
  simp [Float32.Model.nan, Float32.Model.pack]; exact hb

theorem f64_isNaN_eq (x : Float) (h : x.isNaN = true) : x = Float.nan := by
  have h' : (unpack Format.binary64 x.toModel.toBits.toBitVec).isNaN = true := h
  rw [unpack_isNaN] at h'
  simp at h'
  have hb := x.toModel.valid.eq_packedNaN h'.1 h'.2
  rcases x with ⟨⟨bits, valid⟩⟩
  show Float.ofModel ⟨bits, valid⟩ = Float.ofModel ⟨_, _⟩
  congr 2
  apply UInt64.toBitVec_inj.mp
  simp [Float.Model.nan, Float.Model.pack]; exact hb

/-! ## Infinity from the bits -/
theorem bv64_and_abs (b : BitVec 64) : (b &&& 0x7FFFFFFFFFFFFFFF#64).toNat = b.toNat % 2^63 := by
  rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod b.toNat 63
theorem unpack64_isInf (b : BitVec 64) :
    (unpack Format.binary64 b).isInf = ((b &&& 0x7FFFFFFFFFFFFFFF#64) == 0x7FF0000000000000#64) := by
  have h1 := bv64_and_abs b
  have hlt := b.isLt
  unfold unpack
  simp only [unpackExponent, unpackMantissa]
  by_cases he : BitVec.extractLsb' 52 11 b = -1#11 <;> by_cases hm : BitVec.extractLsb' 0 52 b = 0#52 <;>
    by_cases h0 : BitVec.extractLsb' 52 11 b = 0#11 <;> simp only [he, hm, h0, ↓reduceIte, ↓reduceDIte, isInf] <;>
    simp [← BitVec.toNat_inj, h1, Nat.shiftRight_eq_div_pow] at *
  all_goals omega
theorem bv32_and_abs (b : BitVec 32) : (b &&& 0x7FFFFFFF#32).toNat = b.toNat % 2^31 := by
  rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod b.toNat 31
theorem unpack32_isInf (b : BitVec 32) :
    (unpack Format.binary32 b).isInf = ((b &&& 0x7FFFFFFF#32) == 0x7F800000#32) := by
  have h1 := bv32_and_abs b
  have hlt := b.isLt
  unfold unpack
  simp only [unpackExponent, unpackMantissa]
  by_cases he : BitVec.extractLsb' 23 8 b = -1#8 <;> by_cases hm : BitVec.extractLsb' 0 23 b = 0#23 <;>
    by_cases h0 : BitVec.extractLsb' 23 8 b = 0#8 <;> simp only [he, hm, h0, ↓reduceIte, ↓reduceDIte, isInf] <;>
    simp [← BitVec.toNat_inj, h1, Nat.shiftRight_eq_div_pow] at *
  all_goals omega

theorem f64_isInf_bits (x : Float) :
    x.isInf = ((x.toBits.toBitVec &&& 0x7FFFFFFFFFFFFFFF#64) == 0x7FF0000000000000#64) :=
  unpack64_isInf x.toBits.toBitVec
theorem f32_isInf_bits (x : Float32) :
    x.isInf = ((x.toBits.toBitVec &&& 0x7FFFFFFF#32) == 0x7F800000#32) :=
  unpack32_isInf x.toBits.toBitVec

theorem unp_nan_not_lt (y : UnpackedFloat) : UnpackedFloat.lt .notANumber y = false := by
  simp [UnpackedFloat.lt, UnpackedFloat.compare]
theorem unp_inf_not_lt (y : UnpackedFloat) : UnpackedFloat.lt (.infinity .positive) y = false := by
  cases y <;> try (rename_i s; cases s)
  all_goals simp [UnpackedFloat.lt, UnpackedFloat.compare]

theorem f64_unpack_nan : Float.nan.toModel.unpack = .notANumber := by rfl
theorem f64_unpack_inf : Float.inf.toModel.unpack = .infinity .positive := by rfl
theorem f32_unpack_nan : Float32.nan.toModel.unpack = .notANumber := by rfl
theorem f32_unpack_inf : Float32.inf.toModel.unpack = .infinity .positive := by rfl
theorem f64_nan_not_lt (c : Float) : ¬ (Float.nan < c) := by
  have := unp_nan_not_lt c.toModel.unpack
  rw [← f64_unpack_nan] at this
  intro h; have h' : Float.lt Float.nan c = true := h
  simp [Float.lt, LT.lt, Float.Model.lt, this] at h'
theorem f64_inf_not_lt (c : Float) : ¬ (Float.inf < c) := by
  have := unp_inf_not_lt c.toModel.unpack
  rw [← f64_unpack_inf] at this
  intro h; have h' : Float.lt Float.inf c = true := h
  simp [Float.lt, LT.lt, Float.Model.lt, this] at h'
/-- `|x| < c` excludes NaN and ±∞ (the bitwise `Math.Abs` of the spec). -/
theorem f64_abs_lt (x c : Float) (h : OsuModel.Net.F64.abs x < c) : x.isNaN = false ∧ x.isInf = false := by
  constructor
  · cases hn : x.isNaN
    · rfl
    · exfalso; have := f64_isNaN_eq x hn; subst this
      have e : OsuModel.Net.F64.abs Float.nan = Float.nan := by decide
      rw [e] at h; exact f64_nan_not_lt c h
  · cases hi : x.isInf
    · rfl
    · exfalso
      rw [f64_isInf_bits] at hi
      have hb : x.toBits &&& 0x7FFFFFFFFFFFFFFF = 0x7FF0000000000000 := by
        apply UInt64.toBitVec_inj.mp; simpa using hi
      have e : OsuModel.Net.F64.abs x = Float.inf := by
        unfold OsuModel.Net.F64.abs; rw [hb]; decide
      rw [e] at h; exact f64_inf_not_lt c h
theorem f32_nan_not_lt (c : Float32) : ¬ (Float32.nan < c) := by
  have := unp_nan_not_lt c.toModel.unpack
  rw [← f32_unpack_nan] at this
  intro h; have h' : Float32.lt Float32.nan c = true := h
  simp [Float32.lt, LT.lt, Float32.Model.lt, this] at h'
theorem f32_inf_not_lt (c : Float32) : ¬ (Float32.inf < c) := by
  have := unp_inf_not_lt c.toModel.unpack
  rw [← f32_unpack_inf] at this
  intro h; have h' : Float32.lt Float32.inf c = true := h
  simp [Float32.lt, LT.lt, Float32.Model.lt, this] at h'
/-- `|x| < c` excludes NaN and ±∞ (the bitwise `Math.Abs` of the spec). -/
theorem f32_abs_lt (x c : Float32) (h : OsuModel.Net.F32.abs x < c) : x.isNaN = false ∧ x.isInf = false := by
  constructor
  · cases hn : x.isNaN
    · rfl
    · exfalso; have := f32_isNaN_eq x hn; subst this
      have e : OsuModel.Net.F32.abs Float32.nan = Float32.nan := by decide
      rw [e] at h; exact f32_nan_not_lt c h
  · cases hi : x.isInf
    · rfl
    · exfalso
      rw [f32_isInf_bits] at hi
      have hb : x.toBits &&& 0x7FFFFFFF = 0x7F800000 := by
        apply UInt32.toBitVec_inj.mp; simpa using hi
      have e : OsuModel.Net.F32.abs x = Float32.inf := by
        unfold OsuModel.Net.F32.abs; rw [hb]; decide
      rw [e] at h; exact f32_inf_not_lt c h

/-! ## Sign bit masks -/
theorem nat_and_two_pow (n k : Nat) : n &&& 2^k = if n.testBit k then 2^k else 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_two_pow]
  split <;> rename_i h <;> by_cases hik : k = i <;> simp_all [Nat.zero_testBit]

theorem u64_and_sign (x : UInt64) : x &&& 0x8000000000000000 = 0 ∨ x &&& 0x8000000000000000 = 0x8000000000000000 := by
  have h := nat_and_two_pow x.toNat 63
  cases hb : x.toNat.testBit 63 <;> simp [hb] at h
  · left; apply UInt64.toNat_inj.mp; simpa using h
  · right; apply UInt64.toNat_inj.mp; simpa using h

theorem u32_and_sign (x : UInt32) : x &&& 0x80000000 = 0 ∨ x &&& 0x80000000 = 0x80000000 := by
  have h := nat_and_two_pow x.toNat 31
  cases hb : x.toNat.testBit 31 <;> simp [hb] at h
  · left; apply UInt32.toNat_inj.mp; simpa using h
  · right; apply UInt32.toNat_inj.mp; simpa using h

end OsuProofs.FloatFacts
