import OsuModel.Net.Convert

/-!
# `System.Math` / `System.MathF` (non-transcendental part) — all kernel-computable

Each definition follows the .NET 10.0.13 source (`src/libraries/System.Private.CoreLib/src/System/Math.cs`,
`MathF.cs`) literally where the source is managed code, and IEEE semantics where the method is a
JIT intrinsic lowered to a single instruction (on x64 with SSE4.1):

| .NET                      | x64 lowering              | here                                  |
|---------------------------|---------------------------|---------------------------------------|
| `Math.Sqrt`, `MathF.Sqrt` | `sqrtsd` / `sqrtss`       | `sqrtBits` (integer square root)      |
| `Math.Floor/Ceiling/Truncate` (+MathF) | `roundsd/roundss` imm 9/10/11 | `roundIntBits`         |
| `Math.Round(double)`      | `roundsd` imm 4 (managed fallback: `CopySign((a + 2^52) - 2^52, a)`) | managed formula |
| `Math.Abs`                | `andpd` sign mask         | bit mask                              |
| `Math.Max/Min(double)`    | managed IEEE-754:2019 maximum/minimum (or `vfixupimm`/`vrange` sequences with identical results) | managed source |
| `Math.Round(x, AwayFromZero)` | managed `Truncate(x + CopySign(0.49999999999999994, x))` | managed source |
| `Math.Round(x, digits[, mode])` | managed: `Round(x * 10^d, mode) / 10^d` if `|x| < 1e16` | managed source |
| `Math.Clamp`, `Math.Sign` | managed                   | managed source (exceptions as `Except`) |
-/

namespace OsuModel.Net

/-- `System.MidpointRounding`. -/
inductive MidpointRounding where
  | toEven | awayFromZero | toZero | toNegativeInfinity | toPositiveInfinity
deriving Repr, DecidableEq, Inhabited

namespace F64
/-- `Math.Abs(double)`: clear the sign bit. -/
def abs (x : F64) : F64 := Float.ofBits (x.toBits &&& 0x7FFFFFFFFFFFFFFF)
/-- `Math.Floor(double)`. -/
def floor (x : F64) : F64 := ofBitsN (roundIntBits Fmt.f64 .floor x.bitsN)
/-- `Math.Ceiling(double)`. -/
def ceiling (x : F64) : F64 := ofBitsN (roundIntBits Fmt.f64 .ceil x.bitsN)
/-- `Math.Truncate(double)`. -/
def truncate (x : F64) : F64 := ofBitsN (roundIntBits Fmt.f64 .trunc x.bitsN)
/-- `Math.Sqrt(double)` — correctly rounded. -/
def sqrt (x : F64) : F64 := ofBitsN (sqrtBits Fmt.f64 x.bitsN)

/-- 2^52 -/
def integerBoundary : F64 := ofBitsN 0x4330000000000000
/-- `BitDecrement(0.5)` = 0.49999999999999994 -/
def justBelowHalf : F64 := ofBitsN 0x3FDFFFFFFFFFFFFF

/-- `Math.Round(double)` — round half to even (managed source; the `roundsd` intrinsic agrees). -/
def round (a : F64) : F64 :=
  if integerBoundary ≤ abs a then a
  else
    let temp := copySign integerBoundary a
    copySign ((a + temp) - temp) a

/-- `Math.Round(double, MidpointRounding)`. -/
def roundMode (x : F64) : MidpointRounding → F64
  | .awayFromZero => truncate (x + copySign justBelowHalf x)
  | .toEven => round x
  | .toZero => truncate x
  | .toNegativeInfinity => floor x
  | .toPositiveInfinity => ceiling x

/-- `Math.Round(double, int digits, MidpointRounding)`; `digits ∉ [0,15]` throws. -/
def roundDigitsMode (value : F64) (digits : Int) (mode : MidpointRounding) : Except NetExn F64 :=
  if digits < 0 || digits > 15 then .error .argumentOutOfRange
  else if abs value < ofInt (10 ^ 16) then
    let power10 := ofInt (10 ^ digits.toNat)
    .ok (roundMode (value * power10) mode / power10)
  else .ok value

/-- `Math.Round(double, int digits)` (ToEven). -/
def roundDigits (value : F64) (digits : Int) : Except NetExn F64 :=
  roundDigitsMode value digits .toEven

/-- `Math.Max(double, double)` — IEEE 754:2019 `maximum` (NaN-propagating, `+0 > -0`). -/
def max (val1 val2 : F64) : F64 :=
  if !(val1 == val2) then
    (if !val1.isNaN then (if val2 < val1 then val1 else val2) else val1)
  else if val2.isNegative then val1 else val2

/-- `Math.Min(double, double)` — IEEE 754:2019 `minimum`. -/
def min (val1 val2 : F64) : F64 :=
  if !(val1 == val2) then
    (if !val1.isNaN then (if val1 < val2 then val1 else val2) else val1)
  else if val1.isNegative then val1 else val2

/-- `Math.Clamp(double value, double min, double max)`; throws `ArgumentException` if `min > max`.
Note: a NaN `value` is returned as is; NaN bounds never throw. -/
def clamp (value lo hi : F64) : Except NetExn F64 :=
  if hi < lo then .error .argument
  else if value < lo then .ok lo
  else if hi < value then .ok hi
  else .ok value

/-- `Math.Sign(double)`; throws `ArithmeticException` on NaN. -/
def sign (value : F64) : Except NetExn Int32 :=
  if value < 0 then .ok (-1)
  else if 0 < value then .ok 1
  else if value == 0 then .ok 0
  else .error .arithmetic
end F64

namespace F32
/-- `MathF.Abs` / `Math.Abs(float)`. -/
def abs (x : F32) : F32 := Float32.ofBits (x.toBits &&& 0x7FFFFFFF)
def floor (x : F32) : F32 := ofBitsN (roundIntBits Fmt.f32 .floor x.bitsN)
def ceiling (x : F32) : F32 := ofBitsN (roundIntBits Fmt.f32 .ceil x.bitsN)
def truncate (x : F32) : F32 := ofBitsN (roundIntBits Fmt.f32 .trunc x.bitsN)
/-- `MathF.Sqrt` — correctly rounded (`sqrtss`). -/
def sqrt (x : F32) : F32 := ofBitsN (sqrtBits Fmt.f32 x.bitsN)

/-- 2^23 -/
def integerBoundary : F32 := ofBitsN 0x4B000000
/-- 0.49999997f -/
def justBelowHalf : F32 := ofBitsN 0x3EFFFFFF

/-- `MathF.Round(float)` — half to even. -/
def round (a : F32) : F32 :=
  if integerBoundary ≤ abs a then a
  else
    let temp := copySign integerBoundary a
    copySign ((a + temp) - temp) a

/-- `MathF.Round(float, MidpointRounding)`. -/
def roundMode (x : F32) : MidpointRounding → F32
  | .awayFromZero => truncate (x + copySign justBelowHalf x)
  | .toEven => round x
  | .toZero => truncate x
  | .toNegativeInfinity => floor x
  | .toPositiveInfinity => ceiling x

/-- `MathF.Round(float, int digits, MidpointRounding)`; digits ∈ [0,6], limit 1e8f. -/
def roundDigitsMode (x : F32) (digits : Int) (mode : MidpointRounding) : Except NetExn F32 :=
  if digits < 0 || digits > 6 then .error .argumentOutOfRange
  else if abs x < ofInt (10 ^ 8) then
    let power10 := ofInt (10 ^ digits.toNat)
    .ok (roundMode (x * power10) mode / power10)
  else .ok x

def roundDigits (x : F32) (digits : Int) : Except NetExn F32 := roundDigitsMode x digits .toEven

/-- `MathF.Max` / `Math.Max(float, float)`. -/
def max (val1 val2 : F32) : F32 :=
  if !(val1 == val2) then
    (if !val1.isNaN then (if val2 < val1 then val1 else val2) else val1)
  else if val2.isNegative then val1 else val2

/-- `MathF.Min` / `Math.Min(float, float)`. -/
def min (val1 val2 : F32) : F32 :=
  if !(val1 == val2) then
    (if !val1.isNaN then (if val1 < val2 then val1 else val2) else val1)
  else if val1.isNegative then val1 else val2

/-- `Math.Clamp(float, float, float)`. -/
def clamp (value lo hi : F32) : Except NetExn F32 :=
  if hi < lo then .error .argument
  else if value < lo then .ok lo
  else if hi < value then .ok hi
  else .ok value

/-- `Math.Sign(float)` / `MathF.Sign`. -/
def sign (value : F32) : Except NetExn Int32 :=
  if value < 0 then .ok (-1)
  else if 0 < value then .ok 1
  else if value == 0 then .ok 0
  else .error .arithmetic
end F32

end OsuModel.Net
