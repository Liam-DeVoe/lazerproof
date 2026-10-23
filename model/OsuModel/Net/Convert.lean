import OsuModel.Net.Basic

/-!
# Conversions (C# casts) — all kernel-computable

* `(float)double`  — `cvtsd2ss`, round-to-nearest-even, overflow → ±∞, NaN → NaN.
* `(double)float`  — `cvtss2sd`, exact.
* `(double)int/long/uint/ulong`, `(float)int/long/uint/ulong` — single correct rounding
  (verified on .NET 10 x64, including `(float)ulong`, which is *not* double-rounded).
* `(int)x`, `(long)x`, `(uint)x`, `(ulong)x` for `x : double/float` — **saturating** (since .NET 9 on
  x64): truncate toward zero, clamp to the target range, NaN → 0. Verified on this machine.

Lean's own `Float.toFloat32`/`Float32.toFloat` are opaque (not kernel-reducible), so we
implement the conversions on bit patterns via `OsuModel.Net.convertBits`.
-/

namespace OsuModel.Net

namespace F64
/-- C# `(float)x`. -/
def toF32 (x : F64) : F32 := F32.ofBitsN (convertBits Fmt.f64 Fmt.f32 x.bitsN)

/-- Exact/correctly-rounded conversion of a mathematical integer. -/
def ofInt (n : Int) : F64 := ofBitsN (encInt Fmt.f64 (decide (n < 0)) n.natAbs)
/-- C# `(double)i` for `int`. -/
def ofInt32 (n : Int32) : F64 := ofInt n.toInt
/-- C# `(double)l` for `long`. -/
def ofInt64 (n : Int64) : F64 := ofInt n.toInt
/-- C# `(double)u` for `uint`. -/
def ofUInt32 (n : UInt32) : F64 := ofInt n.toNat
/-- C# `(double)u` for `ulong`. -/
def ofUInt64 (n : UInt64) : F64 := ofInt n.toNat

/-- C# `(int)x` (saturating). -/
def toInt32 (x : F64) : Int32 := Int32.ofInt (satConv Fmt.f64 (-2^31) (2^31 - 1) x.bitsN)
/-- C# `(long)x` (saturating). -/
def toInt64 (x : F64) : Int64 := Int64.ofInt (satConv Fmt.f64 (-2^63) (2^63 - 1) x.bitsN)
/-- C# `(uint)x` (saturating). -/
def toUInt32 (x : F64) : UInt32 := UInt32.ofNat (satConv Fmt.f64 0 (2^32 - 1) x.bitsN).toNat
/-- C# `(ulong)x` (saturating). -/
def toUInt64 (x : F64) : UInt64 := UInt64.ofNat (satConv Fmt.f64 0 (2^64 - 1) x.bitsN).toNat
end F64

namespace F32
/-- C# `(double)x` for `float x` (exact). -/
def toF64 (x : F32) : F64 := F64.ofBitsN (convertBits Fmt.f32 Fmt.f64 x.bitsN)

def ofInt (n : Int) : F32 := ofBitsN (encInt Fmt.f32 (decide (n < 0)) n.natAbs)
/-- C# `(float)i` for `int` (rounds above 2^24). -/
def ofInt32 (n : Int32) : F32 := ofInt n.toInt
def ofInt64 (n : Int64) : F32 := ofInt n.toInt
def ofUInt32 (n : UInt32) : F32 := ofInt n.toNat
def ofUInt64 (n : UInt64) : F32 := ofInt n.toNat

def toInt32 (x : F32) : Int32 := Int32.ofInt (satConv Fmt.f32 (-2^31) (2^31 - 1) x.bitsN)
def toInt64 (x : F32) : Int64 := Int64.ofInt (satConv Fmt.f32 (-2^63) (2^63 - 1) x.bitsN)
def toUInt32 (x : F32) : UInt32 := UInt32.ofNat (satConv Fmt.f32 0 (2^32 - 1) x.bitsN).toNat
def toUInt64 (x : F32) : UInt64 := UInt64.ofNat (satConv Fmt.f32 0 (2^64 - 1) x.bitsN).toNat
end F32

end OsuModel.Net
