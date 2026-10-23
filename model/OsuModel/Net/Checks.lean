import OsuModel.Net.Parse
import OsuModel.Net.Libm

/-!
# Kernel-checked facts about the primitives

Everything here is checked with `decide +kernel` (pure kernel evaluation, no `native_decide`),
which also demonstrates that the definitions are kernel-computable.
-/

namespace OsuModel.Net
open F64 F32

/-! ### basic arithmetic (Lean core model) -/
example : ((0.1 : F64) + 0.2).toBits = 0x3FD3333333333334 := by decide +kernel
example : ((0.1 : F32) + 0.2).toBits = 0x3E99999A := by decide +kernel

/-! ### conversions -/
-- (float)0.1 = 0.1f
example : (0.1 : F64).toF32.toBits = 0x3DCCCCCD := by decide +kernel
-- (double)0.1f is exact
example : (0.1 : F32).toF64.toBits = 0x3FB99999A0000000 := by decide +kernel
-- overflow / subnormal / tie-to-even cases of (float)double
example : (F64.ofBitsN 0x47EFFFFFF0000000).toF32.toBits = 0x7F800000 := by decide +kernel -- MAX+½ulp → ∞
example : (F64.ofBitsN 0x47EFFFFFE0000000).toF32.toBits = 0x7F7FFFFF := by decide +kernel
example : (F64.ofBitsN 0x3690000000000000).toF32.toBits = 0x00000000 := by decide +kernel -- 2^-150 → 0 (tie, even)
example : (F64.ofBitsN 0x3690000000000001).toF32.toBits = 0x00000001 := by decide +kernel
example : (F64.ofBitsN 0x3FF0000010000000).toF32.toBits = 0x3F800000 := by decide +kernel -- tie → even
example : (F64.ofBitsN 0x3FF0000030000000).toF32.toBits = 0x3F800002 := by decide +kernel -- tie → even (up)
-- saturating casts
example : F64.toInt32 F64.nan = 0 := by decide +kernel
example : F64.toInt32 (F64.ofInt (10^10)) = 2147483647 := by decide +kernel
example : F64.toInt32 (-(F64.ofInt (10^10))) = -2147483648 := by decide +kernel
example : F64.toInt32 (-1.5) = -1 := by decide +kernel
example : F64.toUInt32 (-1.0) = 0 := by decide +kernel
example : F64.toInt64 (F64.ofInt (2^63)) = 9223372036854775807 := by decide +kernel
-- (float)ulong is a single rounding
example : (F32.ofUInt64 0x8000008000000001).toBits = 0x5F000001 := by decide +kernel
example : (F64.ofInt64 9007199254740993).toBits = 0x4340000000000000 := by decide +kernel

/-! ### rounding -/
example : (F64.round 0.5).toBits = 0 := by decide +kernel
example : (F64.round 1.5).toBits = (2.0 : F64).toBits := by decide +kernel
example : (F64.round 2.5).toBits = (2.0 : F64).toBits := by decide +kernel
example : (F64.round (-0.5)).toBits = 0x8000000000000000 := by decide +kernel
example : (F64.roundMode 2.5 .awayFromZero).toBits = (3.0 : F64).toBits := by decide +kernel
example : (F64.roundMode (-0.4) .awayFromZero).toBits = 0x8000000000000000 := by decide +kernel
example : (F64.roundMode 0.49999999999999994 .awayFromZero).toBits = 0 := by decide +kernel
example : (F64.floor (-0.5)).toBits = (-1.0 : F64).toBits := by decide +kernel
example : (F64.ceiling (-0.5)).toBits = 0x8000000000000000 := by decide +kernel
example : (F64.truncate (-2.7)).toBits = (-2.0 : F64).toBits := by decide +kernel
example : (F32.round 2.5).toBits = (2.0 : F32).toBits := by decide +kernel
-- Math.Round(2.675, 2) = 2.68 in .NET (because 2.675 * 100 rounds to 267.5), not 2.67
example : (F64.roundDigits 2.675 2).map Float.toBits = .ok (2.68 : F64).toBits := by decide +kernel
example : (F64.roundDigits 0.125 2).map Float.toBits = .ok (0.12 : F64).toBits := by decide +kernel

/-! ### sqrt (correctly rounded, via integer square root) -/
example : (F64.sqrt 2).toBits = 0x3FF6A09E667F3BCD := by decide +kernel
example : (F64.sqrt 4).toBits = (2.0 : F64).toBits := by decide +kernel
example : (F64.sqrt (F64.ofBitsN 1)).toBits = 0x1E60000000000000 := by decide +kernel -- √(2^-1074) = 2^-537
example : (F64.sqrt (-0.0)).toBits = 0x8000000000000000 := by decide +kernel
example : (F64.sqrt (-1)).isNaN = true := by decide +kernel
example : (F32.sqrt 2).toBits = 0x3FB504F3 := by decide +kernel
-- agrees with Lean's own model sqrt on a sample (Float.sqrt itself does not kernel-reduce:
-- core `Nat.sqrt` is defined by well-founded recursion)
example : isqrt (2^200 + 12345) = 2^100 := by decide +kernel
example : isqrt (2^200 - 1) = 2^100 - 1 := by decide +kernel

/-! ### Max / Min (.NET IEEE 754:2019 semantics) -/
example : (F64.max 0.0 (-0.0)).toBits = 0 := by decide +kernel
example : (F64.max (-0.0) 0.0).toBits = 0 := by decide +kernel
example : (F64.min 0.0 (-0.0)).toBits = 0x8000000000000000 := by decide +kernel
example : (F64.max 1 F64.nan).isNaN = true := by decide +kernel
example : (F64.min F64.nan 1).isNaN = true := by decide +kernel
example : (F64.clamp 5 2 1).map Float.toBits = .error .argument := by decide +kernel
example : (F64.sign F64.nan) = .error .arithmetic := by decide +kernel
example : (F64.sign (-0.0)) = .ok 0 := by decide +kernel

/-! ### parsing (on explicit char lists) -/
example : (doubleParseChars ['0', '.', '1']).map Float.toBits = .ok 0x3FB999999999999A := by decide +kernel
example : (doubleParseChars ['1', ',', ',', '0']).map Float.toBits = .ok (10.0 : F64).toBits := by decide +kernel
example : (doubleParseChars [',', '1']).map Float.toBits = .error .format := by decide +kernel
example : (doubleParseChars ['-', '0']).map Float.toBits = .ok 0x8000000000000000 := by decide +kernel
example : (doubleParseChars ['1', 'e', '4', '0', '0']).map Float.toBits = .ok 0x7FF0000000000000 := by decide +kernel
example : (doubleParseChars [' ', '1', ' ', '\x00']).map Float.toBits = .ok (1.0 : F64).toBits := by decide +kernel
example : (doubleParseChars ['1', '\x00', ' ']).map Float.toBits = .error .format := by decide +kernel
example : (doubleParseChars ['n', 'A', 'n']).map Float.isNaN = .ok true := by decide +kernel
-- smallest subnormal and the halfway point below it
example : (doubleParseChars "4.9406564584124654e-324".toList).map Float.toBits = .ok 1 := by decide +kernel
example : (doubleParseChars "2.4703282292062327e-324".toList).map Float.toBits = .ok 0 := by decide +kernel
example : (doubleParseChars "2.4703282292062328e-324".toList).map Float.toBits = .ok 1 := by decide +kernel
-- float.Parse rounds directly to binary32 (no double rounding)
example : (floatParseChars "1.00000005960464477539062500001".toList).map Float32.toBits = .ok 0x3F800001 := by decide +kernel
example : (intParseChars "2147483648".toList) = .error .overflow := by decide +kernel
example : (intParseChars " -2147483648 ".toList) = .ok (-2147483648) := by decide +kernel
example : (intParseChars "1.0".toList) = .error .format := by decide +kernel

/-! ### small lemmas -/

/-- `Math.Round` on exact halves `n + ½` (n = 0..63) rounds to the even neighbour. -/
theorem round_half_even_small :
    ∀ n : Fin 64, (F64.round (F64.ofInt n.val + 0.5)).toBits =
      (F64.ofInt (if n.val % 2 == 0 then n.val else n.val + 1)).toBits := by decide +kernel

/-- `(double)(float)x` round-trips for every `float` with a small exponent field sample. -/
theorem f32_f64_roundtrip_sample :
    ∀ i : Fin 256, let x := F32.ofBitsN (i.val * 0x01000000 + 0x123457)
      x.toF64.toF32.toBits = x.toBits ∨ x.isNaN := by decide +kernel

end OsuModel.Net
