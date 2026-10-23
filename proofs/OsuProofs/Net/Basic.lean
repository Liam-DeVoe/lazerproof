/-
`net::basic` (Rust) refines `OsuModel.Net.F64/F32` bit helpers (`copySign`, `isInf`).
`copy_sign` reads raw bits (`to_bits` is partial on NaN), so its theorem is guarded by non-NaN
arguments; `is_inf` checks NaN first and is unconditional.
-/
import OsuProofs.Repr
import OsuProofs.Spec.FloatFacts
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

/-- Guarded: both arguments non-NaN (Rust copies the real NaN sign bit; the model has one NaN). -/
theorem net.basic.f64_copy_sign_refines (x y : F64) (hx : x.isNaN = false) (hy : y.isNaN = false) :
    net.basic.f64_copy_sign x y = ok (F64.copySign x y) := by
  simp [net.basic.f64_copy_sign, f64_to_bits_eq x hx, f64_to_bits_eq y hy, F64.copySign, lift, u64_ofNat_val]

theorem net.basic.f64_is_inf_refines (x : F64) : net.basic.f64_is_inf x = ok x.isInf := by
  cases h : x.isNaN
  · simp [net.basic.f64_is_inf, h, f64_to_bits_eq x h, lift, FloatFacts.f64_isInf_bits, UScalar.eq_equiv_bv_eq]
    rfl
  · have := FloatFacts.f64_isNaN_eq x h; subst this
    simp [net.basic.f64_is_inf, h]; decide

/-- Guarded: both arguments non-NaN (Rust copies the real NaN sign bit; the model has one NaN). -/
theorem net.basic.f32_copy_sign_refines (x y : F32) (hx : x.isNaN = false) (hy : y.isNaN = false) :
    net.basic.f32_copy_sign x y = ok (F32.copySign x y) := by
  simp [net.basic.f32_copy_sign, f32_to_bits_eq x hx, f32_to_bits_eq y hy, F32.copySign, lift, u32_ofNat_val]

theorem net.basic.f32_is_inf_refines (x : F32) : net.basic.f32_is_inf x = ok x.isInf := by
  cases h : x.isNaN
  · simp [net.basic.f32_is_inf, h, f32_to_bits_eq x h, lift, FloatFacts.f32_isInf_bits, UScalar.eq_equiv_bv_eq]
    rfl
  · have := FloatFacts.f32_isNaN_eq x h; subst this
    simp [net.basic.f32_is_inf, h]; decide

end OsuProofs
