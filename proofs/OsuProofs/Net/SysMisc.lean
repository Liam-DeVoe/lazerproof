/-
`net::sysmisc` and `net::libm` (Rust) refine `OsuModel.Net.SysMisc` (degree/radian conversions,
`Enumerable.Average`) and `OsuModel.Net.F64.logBase` (`Math.Log(a, newBase)`).
-/
import OsuProofs.Net.MathOps
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

theorem net.sysmisc.f32_degrees_to_radians_refines (d : F32) :
    net.sysmisc.f32_degrees_to_radians d = ok (SysMisc.F32.degreesToRadians d) := by
  simp [net.sysmisc.f32_degrees_to_radians, net.sysmisc.F32_PI, net.sysmisc.F32_180,
    SysMisc.F32.degreesToRadians, SysMisc.f32Pi, SysMisc.f32_180]
theorem net.sysmisc.f32_radians_to_degrees_refines (d : F32) :
    net.sysmisc.f32_radians_to_degrees d = ok (SysMisc.F32.radiansToDegrees d) := by
  simp [net.sysmisc.f32_radians_to_degrees, net.sysmisc.F32_PI, net.sysmisc.F32_180,
    SysMisc.F32.radiansToDegrees, SysMisc.f32Pi, SysMisc.f32_180]
theorem net.sysmisc.f64_degrees_to_radians_refines (d : F64) :
    net.sysmisc.f64_degrees_to_radians d = ok (SysMisc.F64.degreesToRadians d) := by
  simp [net.sysmisc.f64_degrees_to_radians, net.sysmisc.F64_PI, net.sysmisc.F64_180,
    SysMisc.F64.degreesToRadians, SysMisc.f64Pi, SysMisc.f64_180]
theorem net.sysmisc.f64_radians_to_degrees_refines (d : F64) :
    net.sysmisc.f64_radians_to_degrees d = ok (SysMisc.F64.radiansToDegrees d) := by
  simp [net.sysmisc.f64_radians_to_degrees, net.sysmisc.F64_PI, net.sysmisc.F64_180,
    SysMisc.F64.radiansToDegrees, SysMisc.f64Pi, SysMisc.f64_180]

theorem average_loop (xs : Slice F64) : ∀ (x : F64 × Usize), x.2.val ≤ xs.val.length →
    net.sysmisc.average_f64_loop xs x.1 x.2 = ok ((xs.val.drop x.2.val).foldl (· + ·) x.1) := by
  intro x hx
  unfold net.sysmisc.average_f64_loop
  exact loop_eq (fun (p : F64 × Usize) => net.sysmisc.average_f64_loop.body xs p.1 p.2) (fun x => xs.val.length - x.2.val) (fun x => x.2.val ≤ xs.val.length)
    (fun x => (xs.val.drop x.2.val).foldl (· + ·) x.1)
    (by
      rintro ⟨acc, i⟩ hi
      dsimp only at hi ⊢
      by_cases hlt : i < Slice.len xs
      · right
        have hlt' : i.val < xs.val.length := by simpa using hlt
        have hn := Slice.length_ineq xs
        obtain ⟨i1, hi1, hv⟩ := usize_add_one i (by omega)
        refine ⟨(acc + xs.val[i.val], i1), ?_, ?_, ?_, ?_⟩
        · simp [net.sysmisc.average_f64_loop.body, hlt, index_eq xs i hlt', hi1]
        · simp; omega
        · simp; omega
        · dsimp only; rw [hv, List.drop_eq_getElem_cons hlt' (l := xs.val), List.foldl_cons]
      · left
        have : i.val = xs.val.length := by
          have : ¬ i.val < xs.val.length := by simpa using hlt
          omega
        simp [net.sysmisc.average_f64_loop.body, hlt, this]) x hx

theorem net.sysmisc.average_f64_refines (xs : Slice F64) :
    net.sysmisc.average_f64 xs = ok (exceptI id (SysMisc.averageF64 xs.val)) := by
  unfold net.sysmisc.average_f64 SysMisc.averageF64
  by_cases h : xs.val.length = 0
  · have : Slice.len xs = 0#usize := by scalar_tac
    have h' : xs.val = [] := List.eq_nil_of_length_eq_zero h
    simp [this, h', exceptI, exnI]
  · have : ¬ Slice.len xs = 0#usize := by scalar_tac
    have z0 : Float.ofBits 0 = (0 : F64) := by decide
    have hl := average_loop xs (0, 0#usize) (by simp)
    simp at hl
    have hc : (UScalar.cast .U64 (Slice.len xs)).val = xs.val.length := by
      rw [UScalar.cast_val_eq]; simp
      have h1 := Slice.length_ineq xs
      rcases Usize.bounds_eq with h2 | h2 <;> rw [h2] at h1 <;> simp [U32.max_eq, U64.max_eq] at h1 <;> omega
    have hne : xs.val.isEmpty = false := by simpa using h
    simp [this, hl, lift, float.F64.from_u64, hc, hne, exceptI, z0]

theorem net.libm.f64_log_base_refines (a nb : F64) :
    net.libm.f64_log_base a nb = ok (F64.logBase a nb) := by
  have one : net.libm.ONE = ok (1 : F64) := by simp [net.libm.ONE]; decide
  have zero : net.libm.ZERO = ok (0 : F64) := by simp [net.libm.ZERO]; decide
  have nan : net.basic.F64_NAN = ok F64.nan := by simp [net.basic.F64_NAN]; decide
  have inf : net.basic.F64_POS_INF = ok F64.posInf := by simp [net.basic.F64_POS_INF]; decide
  unfold net.libm.f64_log_base F64.logBase
  by_cases h1 : a.isNaN = true <;> by_cases h2 : nb.isNaN = true <;> by_cases h3 : (nb == 1) = true <;>
    by_cases h4 : (a == 1) = true <;> by_cases h5 : (nb == 0) = true <;> by_cases h6 : (nb == F64.posInf) = true <;>
    simp [one, zero, nan, inf, h1, h2, h3, h4, h5, h6, F64.log]

end OsuProofs
