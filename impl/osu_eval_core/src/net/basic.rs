//! Port of `OsuModel/Net/Basic.lean`: exceptions, NaN/inf constants, `CopySign`, bit equality.
use crate::float::{F32, F64};

/// Spec `OsuModel.Net.NetExn`: exceptions the modelled .NET primitives can throw.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum NetExn {
    /// System.FormatException
    Format,
    /// System.OverflowException
    Overflow,
    /// System.ArgumentException
    Argument,
    /// System.ArgumentOutOfRangeException
    ArgumentOutOfRange,
    /// System.ArithmeticException (also DivideByZero)
    Arithmetic,
}

/// `double.NaN` (spec `F64.nan`; the model has one NaN)
pub const F64_NAN: F64 = F64::from_bits(0x7FF8_0000_0000_0000);
/// spec `F64.posInf`
pub const F64_POS_INF: F64 = F64::from_bits(0x7FF0_0000_0000_0000);
/// spec `F64.negInf`
pub const F64_NEG_INF: F64 = F64::from_bits(0xFFF0_0000_0000_0000);
pub const F32_NAN: F32 = F32::from_bits(0x7FC0_0000);
pub const F32_POS_INF: F32 = F32::from_bits(0x7F80_0000);
pub const F32_NEG_INF: F32 = F32::from_bits(0xFF80_0000);

/// `Math.CopySign(x, y)` (bitwise); spec `OsuModel.Net.F64.copySign`
pub fn f64_copy_sign(x: F64, y: F64) -> F64 {
    F64::from_bits((x.to_bits() & 0x7FFF_FFFF_FFFF_FFFF) | (y.to_bits() & 0x8000_0000_0000_0000))
}

/// spec `OsuModel.Net.F32.copySign`
pub fn f32_copy_sign(x: F32, y: F32) -> F32 {
    F32::from_bits((x.to_bits() & 0x7FFF_FFFF) | (y.to_bits() & 0x8000_0000))
}

/// spec `F64.isInf` (Lean core `Float.isInf`)
pub fn f64_is_inf(x: F64) -> bool {
    // NaN first (`isInf` is false on NaN): `to_bits` is identified with the
    // spec only on non-NaN values (proofs/OsuProofs/Generated/FunsExternal.lean)
    !x.is_nan() && (x.to_bits() & 0x7FFF_FFFF_FFFF_FFFF) == 0x7FF0_0000_0000_0000
}

/// spec `F32.isInf`
pub fn f32_is_inf(x: F32) -> bool {
    // NaN first (`isInf` is false on NaN): `to_bits` is identified with the
    // spec only on non-NaN values (proofs/OsuProofs/Generated/FunsExternal.lean)
    !x.is_nan() && (x.to_bits() & 0x7FFF_FFFF) == 0x7F80_0000
}
