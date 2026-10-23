/-
`sim::netx` (Rust: .NET numeric helpers of the Sim port) refines `OsuModel.Net` (`F64.copySign/round/sign`,
`F32.max/min/clamp/sign`, `Bindable.equalsD`, the `F64.clamp` / `F32.clamp` "or keep" idiom). Same proofs as the
`net::mathops` copies (OsuProofs/Net/MathOps.lean). `copy_sign` reads raw bits (`to_bits` is partial on NaN),
so it is guarded by non-NaN arguments.
-/
import OsuProofs.Sim.Abs
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

@[simp] theorem netx_F64_INTEGER_BOUNDARY : sim.netx.F64_INTEGER_BOUNDARY = ok F64.integerBoundary := by
  simp [sim.netx.F64_INTEGER_BOUNDARY, F64.integerBoundary, F64.ofBitsN]
@[simp] theorem netx_F64_ZERO : sim.netx.F64_ZERO = ok (0 : F64) := by
  simp [sim.netx.F64_ZERO]; decide
@[simp] theorem netx_F32_ZERO : sim.netx.F32_ZERO = ok (0 : F32) := by
  simp [sim.netx.F32_ZERO]; decide
@[simp] theorem netx_F64_NAN : sim.netx.F64_NAN = ok F64.nan := by
  simp [sim.netx.F64_NAN]; decide
@[simp] theorem netx_F64_POS_INF : sim.netx.F64_POS_INF = ok F64.posInf := by
  simp [sim.netx.F64_POS_INF]; decide
@[simp] theorem netx_F64_NEG_INF : sim.netx.F64_NEG_INF = ok F64.negInf := by
  simp [sim.netx.F64_NEG_INF]; decide
@[simp] theorem netx_F32_POS_INF : sim.netx.F32_POS_INF = ok F32.posInf := by
  simp [sim.netx.F32_POS_INF]; decide
@[simp] theorem netx_F32_NEG_INF : sim.netx.F32_NEG_INF = ok F32.negInf := by
  simp [sim.netx.F32_NEG_INF]; decide

theorem sim.netx.f64_copy_sign_refines (x y : F64) (hx : x.isNaN = false) (hy : y.isNaN = false) :
    sim.netx.f64_copy_sign x y = ok (F64.copySign x y) := by
  simp [sim.netx.f64_copy_sign, f64_to_bits_eq x hx, f64_to_bits_eq y hy, F64.copySign, lift, u64_ofNat_val,
    sim.netx.F64_MAG, sim.netx.F64_SIGN]

theorem sim.netx.f64_round_refines (a : F64) : sim.netx.f64_round a = ok (F64.round a) := by
  simp [sim.netx.f64_round, net.mathops.f64_round_refines]

/-- `Math.Sign(double)`; `none` = the spec's `ArithmeticException` (NaN). -/
def simOptEx {α β} (f : α → β) : Except NetExn α → Option β
  | .ok a => some (f a)
  | .error _ => none

theorem sim.netx.f64_sign_refines (value : F64) :
    sim.netx.f64_sign value = ok (simOptEx i32I (F64.sign value)) := by
  unfold sim.netx.f64_sign F64.sign
  by_cases h1 : value < 0 <;> by_cases h2 : 0 < value <;> by_cases h3 : (value == 0) = true <;>
    simp [h1, h2, h3, simOptEx] <;> rfl

theorem sim.netx.f32_sign_refines (value : F32) :
    sim.netx.f32_sign value = ok (simOptEx i32I (F32.sign value)) := by
  unfold sim.netx.f32_sign F32.sign
  by_cases h1 : value < 0 <;> by_cases h2 : 0 < value <;> by_cases h3 : (value == 0) = true <;>
    simp [h1, h2, h3, simOptEx] <;> rfl

theorem sim.netx.f32_max_refines (a b : F32) : sim.netx.f32_max a b = ok (F32.max a b) := by
  unfold sim.netx.f32_max F32.max
  by_cases h : (a == b) = true
  · have := beq_not_nan_right32 h
    simp [h, f32_is_negative_eq b this]
  · simp only [Bool.not_eq_true] at h
    simp [h]
    split <;> simp_all

theorem sim.netx.f32_min_refines (a b : F32) : sim.netx.f32_min a b = ok (F32.min a b) := by
  unfold sim.netx.f32_min F32.min
  by_cases h : (a == b) = true
  · have := beq_not_nan_left32 h
    simp [h, f32_is_negative_eq a this]
  · simp only [Bool.not_eq_true] at h
    simp [h]
    split <;> simp_all

theorem sim.netx.f32_clamp_refines (v lo hi : F32) :
    sim.netx.f32_clamp v lo hi = ok (simOptEx id (F32.clamp v lo hi)) := by
  unfold sim.netx.f32_clamp F32.clamp
  by_cases h1 : hi < lo <;> by_cases h2 : v < lo <;> by_cases h3 : hi < v <;>
    simp [h1, h2, h3, simOptEx]

theorem net.clamp_refines (v lo hi : F64) :
    net.clamp v lo hi = ok (simOptEx id (F64.clamp v lo hi)) := by
  unfold net.clamp F64.clamp
  by_cases h1 : hi < lo <;> by_cases h2 : v < lo <;> by_cases h3 : hi < v <;>
    simp [h1, h2, h3, simOptEx]

theorem sim.netx.equals_d_refines (a b : F64) :
    sim.netx.equals_d a b = ok (Framework.Bindable.equalsD a b) := by
  unfold sim.netx.equals_d Framework.Bindable.equalsD
  by_cases h : (a == b) = true <;> simp [h]

/-- The spec idiom `match F64.clamp x lo hi with | .ok v => v | .error _ => x`. -/
def simClampOrD (x lo hi : F64) : F64 := match F64.clamp x lo hi with | .ok v => v | .error _ => x
def simClampOrF (x lo hi : F32) : F32 := match F32.clamp x lo hi with | .ok v => v | .error _ => x

theorem sim.netx.f64_clamp_or_refines (x lo hi : F64) :
    sim.netx.f64_clamp_or x lo hi = ok (simClampOrD x lo hi) := by
  unfold sim.netx.f64_clamp_or simClampOrD
  rw [net.clamp_refines]
  cases F64.clamp x lo hi <;> simp [simOptEx]
theorem sim.netx.f32_clamp_or_refines (x lo hi : F32) :
    sim.netx.f32_clamp_or x lo hi = ok (simClampOrF x lo hi) := by
  unfold sim.netx.f32_clamp_or simClampOrF
  rw [sim.netx.f32_clamp_refines]
  cases F32.clamp x lo hi <;> simp [simOptEx]

/-! `crate::net::max/min` (`Math.Max/Min(double, double)`, net root module; used by the sim) -/
theorem net.max_refines (a b : F64) : net.max a b = ok (F64.max a b) := by
  unfold net.max F64.max
  by_cases h : (a == b) = true
  · have := beq_not_nan_right h
    simp [h, f64_is_negative_eq b this]
  · simp only [Bool.not_eq_true] at h
    simp [h]
    split <;> simp_all
theorem net.min_refines (a b : F64) : net.min a b = ok (F64.min a b) := by
  unfold net.min F64.min
  by_cases h : (a == b) = true
  · have := beq_not_nan_left h
    simp [h, f64_is_negative_eq a this]
  · simp only [Bool.not_eq_true] at h
    simp [h]
    split <;> simp_all

end OsuProofs
