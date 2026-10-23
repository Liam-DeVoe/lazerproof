//! .NET numeric helpers needed by the Sim port that are not (yet) in `crate::net`
//! (written over the `float` primitives; translated, not trusted).
//! Spec: `OsuModel/Net/MathOps.lean`, `OsuModel/Net/Basic.lean`, `OsuModel/Net/Framework.lean`.
//! NOTE: when the Net port (`crate::net`) provides these, switch the call sites and delete this file.
use crate::float::{F32, F64};

pub const F64_SIGN: u64 = 0x8000_0000_0000_0000;
pub const F64_MAG: u64 = 0x7FFF_FFFF_FFFF_FFFF;
/// 2^52 (`F64.integerBoundary`)
pub const F64_INTEGER_BOUNDARY: F64 = F64::from_bits(0x4330_0000_0000_0000);
pub const F64_POS_INF: F64 = F64::from_bits(0x7FF0_0000_0000_0000);
pub const F64_NEG_INF: F64 = F64::from_bits(0xFFF0_0000_0000_0000);
pub const F64_NAN: F64 = F64::from_bits(0x7FF8_0000_0000_0000);
pub const F64_ZERO: F64 = F64::from_bits(0);
pub const F32_ZERO: F32 = F32::from_bits(0);

/// `F64.copySign` (`Math.CopySign`, bitwise)
pub fn f64_copy_sign(x: F64, y: F64) -> F64 {
    F64::from_bits((x.to_bits() & F64_MAG) | (y.to_bits() & F64_SIGN))
}

/// `F64.round` (`Math.Round(double)`, half to even): the Net port's (it handles NaN before `to_bits`, which the
/// refinement proofs need; same value)
pub fn f64_round(a: F64) -> F64 {
    crate::net::mathops::f64_round(a)
}

/// `F64.sign` (`Math.Sign(double)`; `None` = ArithmeticException on NaN)
pub fn f64_sign(value: F64) -> Option<i32> {
    if value.lt(F64_ZERO) {
        Some(-1)
    } else if F64_ZERO.lt(value) {
        Some(1)
    } else if value.eq(F64_ZERO) {
        Some(0)
    } else {
        None
    }
}

/// `F32.max` (`MathF.Max`)
pub fn f32_max(val1: F32, val2: F32) -> F32 {
    if !val1.eq(val2) {
        if !val1.is_nan() {
            if val2.lt(val1) { val1 } else { val2 }
        } else {
            val1
        }
    } else if val2.is_negative() {
        val1
    } else {
        val2
    }
}

/// `F32.min` (`MathF.Min`)
pub fn f32_min(val1: F32, val2: F32) -> F32 {
    if !val1.eq(val2) {
        if !val1.is_nan() {
            if val1.lt(val2) { val1 } else { val2 }
        } else {
            val1
        }
    } else if val1.is_negative() {
        val1
    } else {
        val2
    }
}

/// `F32.clamp` (`Math.Clamp(float, float, float)`; `None` = ArgumentException)
pub fn f32_clamp(value: F32, lo: F32, hi: F32) -> Option<F32> {
    if hi.lt(lo) {
        None
    } else if value.lt(lo) {
        Some(lo)
    } else if hi.lt(value) {
        Some(hi)
    } else {
        Some(value)
    }
}

/// `F32.sign` (`MathF.Sign`; `None` on NaN)
pub fn f32_sign(value: F32) -> Option<i32> {
    if value.lt(F32_ZERO) {
        Some(-1)
    } else if F32_ZERO.lt(value) {
        Some(1)
    } else if value.eq(F32_ZERO) {
        Some(0)
    } else {
        None
    }
}

/// `Framework.Bindable.equalsD` (`double.Equals`: `==` or both NaN)
pub fn equals_d(a: F64, b: F64) -> bool {
    a.eq(b) || (a.is_nan() && b.is_nan())
}

/// `match F64.clamp x lo hi with | .ok v => v | .error _ => x` (the recurring spec idiom)
pub fn f64_clamp_or(x: F64, lo: F64, hi: F64) -> F64 {
    match crate::net::clamp(x, lo, hi) {
        Some(v) => v,
        None => x,
    }
}

/// same idiom for `F32.clamp`
pub fn f32_clamp_or(x: F32, lo: F32, hi: F32) -> F32 {
    match f32_clamp(x, lo, hi) {
        Some(v) => v,
        None => x,
    }
}

pub const F32_POS_INF: F32 = F32::from_bits(0x7F80_0000);
pub const F32_NEG_INF: F32 = F32::from_bits(0xFF80_0000);
