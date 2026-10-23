/-
`net::mathops` (Rust) refines `OsuModel.Net.MathOps` (.NET `Math.Round/Max/Min/Clamp/Sign`).
-/
import OsuProofs.Net.Basic
import OsuProofs.Loops
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

def mrS : net.mathops.MidpointRounding → MidpointRounding
  | .ToEven => .toEven | .AwayFromZero => .awayFromZero | .ToZero => .toZero
  | .ToNegativeInfinity => .toNegativeInfinity | .ToPositiveInfinity => .toPositiveInfinity

/-! ## `pow10_u64` (helper: `10^k` for the digit-rounding power) -/

/-- Helper (no spec def): `10^k` for `k ≤ 19`. -/
theorem net.mathops.pow10_u64_refines (k : U32) (hk : k.val ≤ 19) :
    ∃ y, net.mathops.pow10_u64 k = ok y ∧ y.val = 10 ^ k.val := by
  unfold net.mathops.pow10_u64 net.mathops.pow10_u64_loop
  apply loop_ok _ (fun x => k.val - x.2.val) (fun x => x.2.val ≤ k.val ∧ x.1.val = 10 ^ x.2.val)
  · rintro ⟨r, i⟩ ⟨hi, hr⟩
    dsimp only at hi hr ⊢
    simp only [net.mathops.pow10_u64_loop.body]
    by_cases hlt : i < k
    · right
      have hlt' : i.val < k.val := hlt
      have hpow : 10 ^ i.val * 10 ≤ 10 ^ 19 := by
        rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega)
      obtain ⟨r1, hr1, hv⟩ := eq_ok_of_spec (U64.mul_spec (x := r) (y := 10#u64)
        (by simp [hr, U64.max_eq]; omega))
      obtain ⟨i1, hi1, hiv⟩ := eq_ok_of_spec (U32.add_spec (x := i) (y := 1#u32)
        (by simp [U32.max_eq]; omega))
      refine ⟨(r1, i1), by simp [hlt, hr1, hi1], ?_, ?_⟩
      · simp at hv hiv; simp [hv, hiv, hr, Nat.pow_succ]; omega
      · simp at hiv; simp [hiv]; omega
    · left
      have : i.val = k.val := by have : ¬ i.val < k.val := hlt; omega
      exact ⟨r, by simp [hlt], by rw [hr, this]⟩
  · simp


/-! ## constants -/
@[simp] theorem mathops_F64_INTEGER_BOUNDARY : net.mathops.F64_INTEGER_BOUNDARY = ok F64.integerBoundary := by
  simp [net.mathops.F64_INTEGER_BOUNDARY, F64.integerBoundary, F64.ofBitsN]
@[simp] theorem mathops_F64_JUST_BELOW_HALF : net.mathops.F64_JUST_BELOW_HALF = ok F64.justBelowHalf := by
  simp [net.mathops.F64_JUST_BELOW_HALF, F64.justBelowHalf, F64.ofBitsN]

theorem f64_boundary_temp (a : F64) : (F64.copySign F64.integerBoundary a).isNaN = false ∧
    (F64.copySign F64.integerBoundary a).isInf = false := by
  unfold F64.copySign
  rcases FloatFacts.u64_and_sign a.toBits with h | h <;> rw [h] <;> decide

theorem net.mathops.f64_round_refines (a : F64) : net.mathops.f64_round a = ok (F64.round a) := by
  cases hn : a.isNaN
  · have ⟨t1, t2⟩ := f64_boundary_temp a
    have hb : F64.integerBoundary.isNaN = false := by decide
    have h2 := FloatFacts.f64_isNaN_add a _ hn t1 t2
    have h3 := FloatFacts.f64_isNaN_sub _ _ h2 t1 t2
    simp [net.mathops.f64_round, F64.round, hn, net.basic.f64_copy_sign_refines _ _ hb hn,
      net.basic.f64_copy_sign_refines _ _ h3 hn]
  · have := FloatFacts.f64_isNaN_eq a hn; subst this
    simp [net.mathops.f64_round, hn]; decide


theorem f64_jbh_nonnan : F64.justBelowHalf.isNaN = false := by decide

/-- Guarded for `AwayFromZero` (it copies the sign of `x`, read through `to_bits`). -/
theorem net.mathops.f64_round_mode_refines (x : F64) (mode : net.mathops.MidpointRounding)
    (hx : mode = .AwayFromZero → x.isNaN = false) :
    net.mathops.f64_round_mode x mode = ok (F64.roundMode x (mrS mode)) := by
  cases mode <;> simp [net.mathops.f64_round_mode, F64.roundMode, mrS, net.mathops.f64_round_refines]
  · rw [net.basic.f64_copy_sign_refines _ _ f64_jbh_nonnan (hx rfl)]; simp

@[simp] theorem mathops_F64_1E16 : net.mathops.F64_1E16 = ok (F64.ofInt 10000000000000000) := by
  simp [net.mathops.F64_1E16]; decide

theorem net.mathops.f64_round_digits_mode_refines (value : F64) (digits : I64)
    (mode : net.mathops.MidpointRounding) :
    net.mathops.f64_round_digits_mode value digits mode =
      ok (exceptI id (F64.roundDigitsMode value digits.val (mrS mode))) := by
  unfold net.mathops.f64_round_digits_mode F64.roundDigitsMode
  by_cases h0 : digits.val < 0
  · have : digits < 0#i64 := by simpa using h0
    simp [this, h0, exceptI, exnI]
  by_cases h15 : digits.val > 15
  · have : digits > 15#i64 := by simpa using h15
    simp [this, h0, h15, exceptI, exnI]
  have a0 : ¬ digits < 0#i64 := by simpa using h0
  have a15 : ¬ digits > 15#i64 := by simpa using h15
  simp only [a0, a15, h0, h15, ite_false, decide_false, Bool.or_false]
  by_cases hlt : F64.abs value < F64.ofInt 10000000000000000
  · obtain ⟨hn, hi⟩ := FloatFacts.f64_abs_lt _ _ hlt
    have hc : (IScalar.hcast .U32 digits).val = digits.val.toNat := by
      rw [IScalar.hcast_val_eq]; simp; omega
    obtain ⟨p, hp, hpv⟩ := net.mathops.pow10_u64_refines (IScalar.hcast .U32 digits) (by omega)
    have hpow : F64.ofInt (p.val : Int) = F64.ofInt (10 ^ digits.val.toNat) := by
      rw [hpv, hc]; simp
    have key : ∀ k, k < 16 → (F64.ofInt (10 ^ k)).isNaN = false ∧ (F64.ofInt (10 ^ k)).isInf = false := by
      decide
    obtain ⟨hpn, hpi⟩ := key digits.val.toNat (by omega)
    have hm := FloatFacts.f64_isNaN_mul value _ hn hpn hi hpi
    simp [hlt, lift, hp, float.F64.from_u64, hpow, net.mathops.f64_round_mode_refines _ _ (fun _ => hm), exceptI]
  · simp [hlt, exceptI]

theorem net.mathops.f64_round_digits_refines (value : F64) (digits : I64) :
    net.mathops.f64_round_digits value digits =
      ok (exceptI id (F64.roundDigits value digits.val)) := by
  simp [net.mathops.f64_round_digits, F64.roundDigits, net.mathops.f64_round_digits_mode_refines, mrS]

theorem net.mathops.f64_sign_refines (value : F64) :
    net.mathops.f64_sign value = ok (exceptI i32I (F64.sign value)) := by
  have z : net.mathops.F64_ZERO = ok (0 : F64) := by simp [net.mathops.F64_ZERO]; decide
  unfold net.mathops.f64_sign F64.sign
  by_cases h1 : value < 0 <;> by_cases h2 : 0 < value <;> by_cases h3 : (value == 0) = true <;>
    simp [z, h1, h2, h3, exceptI, exnI] <;> rfl

theorem net.mathops.f64_clamp_refines (v lo hi : F64) :
    net.mathops.f64_clamp v lo hi = ok (exceptI id (F64.clamp v lo hi)) := by
  unfold net.mathops.f64_clamp F64.clamp
  by_cases h1 : hi < lo <;> by_cases h2 : v < lo <;> by_cases h3 : hi < v <;>
    simp [h1, h2, h3, exceptI, exnI]

/-! ## binary32 -/
@[simp] theorem mathops_F32_INTEGER_BOUNDARY : net.mathops.F32_INTEGER_BOUNDARY = ok F32.integerBoundary := by
  simp [net.mathops.F32_INTEGER_BOUNDARY, F32.integerBoundary, F32.ofBitsN]
@[simp] theorem mathops_F32_JUST_BELOW_HALF : net.mathops.F32_JUST_BELOW_HALF = ok F32.justBelowHalf := by
  simp [net.mathops.F32_JUST_BELOW_HALF, F32.justBelowHalf, F32.ofBitsN]

theorem f32_boundary_temp (a : F32) : (F32.copySign F32.integerBoundary a).isNaN = false ∧
    (F32.copySign F32.integerBoundary a).isInf = false := by
  unfold F32.copySign
  rcases FloatFacts.u32_and_sign a.toBits with h | h <;> rw [h] <;> decide

theorem net.mathops.f32_round_refines (a : F32) : net.mathops.f32_round a = ok (F32.round a) := by
  cases hn : a.isNaN
  · have ⟨t1, t2⟩ := f32_boundary_temp a
    have hb : F32.integerBoundary.isNaN = false := by decide
    have h2 := FloatFacts.f32_isNaN_add a _ hn t1 t2
    have h3 := FloatFacts.f32_isNaN_sub _ _ h2 t1 t2
    simp [net.mathops.f32_round, F32.round, hn, net.basic.f32_copy_sign_refines _ _ hb hn,
      net.basic.f32_copy_sign_refines _ _ h3 hn]
  · have := FloatFacts.f32_isNaN_eq a hn; subst this
    simp [net.mathops.f32_round, hn]; decide


theorem f32_jbh_nonnan : F32.justBelowHalf.isNaN = false := by decide

/-- Guarded for `AwayFromZero` (it copies the sign of `x`, read through `to_bits`). -/
theorem net.mathops.f32_round_mode_refines (x : F32) (mode : net.mathops.MidpointRounding)
    (hx : mode = .AwayFromZero → x.isNaN = false) :
    net.mathops.f32_round_mode x mode = ok (F32.roundMode x (mrS mode)) := by
  cases mode <;> simp [net.mathops.f32_round_mode, F32.roundMode, mrS, net.mathops.f32_round_refines]
  · rw [net.basic.f32_copy_sign_refines _ _ f32_jbh_nonnan (hx rfl)]; simp

@[simp] theorem mathops_F32_1E8 : net.mathops.F32_1E8 = ok (F32.ofInt 100000000) := by
  simp [net.mathops.F32_1E8]; decide

theorem net.mathops.f32_round_digits_mode_refines (value : F32) (digits : I64)
    (mode : net.mathops.MidpointRounding) :
    net.mathops.f32_round_digits_mode value digits mode =
      ok (exceptI id (F32.roundDigitsMode value digits.val (mrS mode))) := by
  unfold net.mathops.f32_round_digits_mode F32.roundDigitsMode
  by_cases h0 : digits.val < 0
  · have : digits < 0#i64 := by simpa using h0
    simp [this, h0, exceptI, exnI]
  by_cases h15 : digits.val > 6
  · have : digits > 6#i64 := by simpa using h15
    simp [this, h0, h15, exceptI, exnI]
  have a0 : ¬ digits < 0#i64 := by simpa using h0
  have a15 : ¬ digits > 6#i64 := by simpa using h15
  simp only [a0, a15, h0, h15, ite_false, decide_false, Bool.or_false]
  by_cases hlt : F32.abs value < F32.ofInt 100000000
  · obtain ⟨hn, hi⟩ := FloatFacts.f32_abs_lt _ _ hlt
    have hc : (IScalar.hcast .U32 digits).val = digits.val.toNat := by
      rw [IScalar.hcast_val_eq]; simp; omega
    obtain ⟨p, hp, hpv⟩ := net.mathops.pow10_u64_refines (IScalar.hcast .U32 digits) (by omega)
    have hpow : F32.ofInt (p.val : Int) = F32.ofInt (10 ^ digits.val.toNat) := by
      rw [hpv, hc]; simp
    have key : ∀ k, k < 7 → (F32.ofInt (10 ^ k)).isNaN = false ∧ (F32.ofInt (10 ^ k)).isInf = false := by
      decide
    obtain ⟨hpn, hpi⟩ := key digits.val.toNat (by omega)
    have hm := FloatFacts.f32_isNaN_mul value _ hn hpn hi hpi
    simp [hlt, lift, hp, float.F32.from_u64, hpow, net.mathops.f32_round_mode_refines _ _ (fun _ => hm), exceptI]
  · simp [hlt, exceptI]

theorem net.mathops.f32_round_digits_refines (value : F32) (digits : I64) :
    net.mathops.f32_round_digits value digits =
      ok (exceptI id (F32.roundDigits value digits.val)) := by
  simp [net.mathops.f32_round_digits, F32.roundDigits, net.mathops.f32_round_digits_mode_refines, mrS]

theorem net.mathops.f32_sign_refines (value : F32) :
    net.mathops.f32_sign value = ok (exceptI i32I (F32.sign value)) := by
  have z : net.mathops.F32_ZERO = ok (0 : F32) := by simp [net.mathops.F32_ZERO]; decide
  unfold net.mathops.f32_sign F32.sign
  by_cases h1 : value < 0 <;> by_cases h2 : 0 < value <;> by_cases h3 : (value == 0) = true <;>
    simp [z, h1, h2, h3, exceptI, exnI] <;> rfl

theorem net.mathops.f32_clamp_refines (v lo hi : F32) :
    net.mathops.f32_clamp v lo hi = ok (exceptI id (F32.clamp v lo hi)) := by
  unfold net.mathops.f32_clamp F32.clamp
  by_cases h1 : hi < lo <;> by_cases h2 : v < lo <;> by_cases h3 : hi < v <;>
    simp [h1, h2, h3, exceptI, exnI]


theorem beq_not_nan_left32 {a b : Float32} (h : (a == b) = true) : a.isNaN = false := by
  revert h
  simp only [BEq.beq, Float32.beq, Float32.isNaN, Float32.Model.beq, Float32.Model.isNaN,
    Float.Model.UnpackedFloat.beq]
  generalize a.toModel.unpack = x
  generalize b.toModel.unpack = y
  cases x <;> cases y <;> simp [Float.Model.UnpackedFloat.compare, Float.Model.UnpackedFloat.isNaN] <;> rfl

theorem beq_not_nan_right32 {a b : Float32} (h : (a == b) = true) : b.isNaN = false := by
  revert h
  simp only [BEq.beq, Float32.beq, Float32.isNaN, Float32.Model.beq, Float32.Model.isNaN,
    Float.Model.UnpackedFloat.beq]
  generalize a.toModel.unpack = x
  generalize b.toModel.unpack = y
  cases x <;> cases y <;> simp [Float.Model.UnpackedFloat.compare, Float.Model.UnpackedFloat.isNaN] <;> rfl

theorem net.mathops.f32_max_refines (a b : F32) : net.mathops.f32_max a b = ok (F32.max a b) := by
  unfold net.mathops.f32_max F32.max
  by_cases h : (a == b) = true
  · have := beq_not_nan_right32 h
    simp [h, f32_is_negative_eq b this]
  · simp only [Bool.not_eq_true] at h
    simp [h]
    split <;> simp_all

theorem net.mathops.f32_min_refines (a b : F32) : net.mathops.f32_min a b = ok (F32.min a b) := by
  unfold net.mathops.f32_min F32.min
  by_cases h : (a == b) = true
  · have := beq_not_nan_left32 h
    simp [h, f32_is_negative_eq a this]
  · simp only [Bool.not_eq_true] at h
    simp [h]
    split <;> simp_all

end OsuProofs
