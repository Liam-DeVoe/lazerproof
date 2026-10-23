import OsuModel.Net.Fmt

/-!
# .NET `double` / `float` as Lean `Float` / `Float32`

Lean 4.35's `Float`/`Float32` are logically `Float.Model`/`Float32.Model` (IEEE binary64/binary32
bit patterns with one canonical NaN). `+ - * /`, comparisons, `ofBits`/`toBits`, `ofScientific`,
`neg` reduce in the kernel; when compiled they are the C operators on `double`/`float`, which on
x86-64 are SSE2 instructions — exactly the instructions RyuJIT emits for C# `+ - * /` and
comparisons. So these are used directly.

C# operator ↔ Lean:
* `a + b`, `a - b`, `a * b`, `a / b` ↔ `a + b` etc. on `F64`/`F32` (no FMA contraction in either).
* `a < b`, `a <= b`, `a > b`, `a >= b`, `a == b` ↔ `a < b`, `a ≤ b`, `b < a`, `b ≤ a`, `a == b`
  (IEEE: any comparison with NaN is false; `+0 == -0`). C# `a != b` ↔ `!(a == b)`.
* unary `-a` ↔ `-a` (sign flip, also of NaN — invisible in the model).

NaN: the logical model has a single NaN. .NET produces `0xFFF8000000000000` for `0/0`, `double.NaN`,
etc. The model must never observe NaN sign/payload (lazer does not: it only tests `IsNaN`).
`double.IsNegative`/`BitConverter.DoubleToInt64Bits` on a NaN are the only ways to observe it.
-/

namespace OsuModel.Net

deriving instance DecidableEq for Except

/-- .NET `System.Double`. -/
abbrev F64 := Float
/-- .NET `System.Single`. -/
abbrev F32 := Float32

/-- Exceptions that the modelled .NET primitives can throw. -/
inductive NetExn where
  | format            -- System.FormatException
  | overflow          -- System.OverflowException
  | argument          -- System.ArgumentException (e.g. Math.Clamp with min > max)
  | argumentOutOfRange
  | arithmetic        -- System.ArithmeticException (Math.Sign(NaN))
deriving Repr, DecidableEq, Inhabited

namespace F64
/-- Raw bits as a `Nat` (`BitConverter.DoubleToUInt64Bits`, NaN canonical in the logic). -/
@[inline] def bitsN (x : F64) : Nat := x.toBits.toNat
@[inline] def ofBitsN (n : Nat) : F64 := Float.ofBits (UInt64.ofNat n)
@[inline] def dec (x : F64) : Dec := decode Fmt.f64 x.bitsN
/-- `double.NaN`. -/
def nan : F64 := Float.nan
def posInf : F64 := Float.inf
def negInf : F64 := -Float.inf
@[inline] def isNaN (x : F64) : Bool := Float.isNaN x
/-- `double.IsNegative` (sign bit). Not meaningful on NaN in the model. -/
@[inline] def isNegative (x : F64) : Bool := x.toBits >>> 63 == 1
/-- `Math.CopySign` / `double.CopySign` (bitwise). -/
@[inline] def copySign (x y : F64) : F64 :=
  Float.ofBits ((x.toBits &&& 0x7FFFFFFFFFFFFFFF) ||| (y.toBits &&& 0x8000000000000000))
/-- Bit-pattern equality (what `decide`/`=` sees); NaN = NaN. -/
@[inline] def bitEq (x y : F64) : Bool := x.toBits == y.toBits
end F64

namespace F32
@[inline] def bitsN (x : F32) : Nat := x.toBits.toNat
@[inline] def ofBitsN (n : Nat) : F32 := Float32.ofBits (UInt32.ofNat n)
@[inline] def dec (x : F32) : Dec := decode Fmt.f32 x.bitsN
def nan : F32 := Float32.nan
def posInf : F32 := Float32.inf
def negInf : F32 := -Float32.inf
@[inline] def isNaN (x : F32) : Bool := Float32.isNaN x
@[inline] def isNegative (x : F32) : Bool := x.toBits >>> 31 == 1
@[inline] def copySign (x y : F32) : F32 :=
  Float32.ofBits ((x.toBits &&& 0x7FFFFFFF) ||| (y.toBits &&& 0x80000000))
@[inline] def bitEq (x y : F32) : Bool := x.toBits == y.toBits
end F32

end OsuModel.Net
