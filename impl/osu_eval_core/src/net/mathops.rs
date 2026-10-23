//! Port of `OsuModel/Net/MathOps.lean` (the managed parts of `System.Math`/`MathF`).
//! `Abs/Floor/Ceiling/Truncate/Sqrt` are trusted primitives (`crate::float`); `F64` max/min/clamp
//! live in `crate::net` (POC, proven).
use super::basic::{f32_copy_sign, f64_copy_sign, NetExn};
use crate::float::{F32, F64};

/// spec `OsuModel.Net.MidpointRounding`
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum MidpointRounding {
    ToEven,
    AwayFromZero,
    ToZero,
    ToNegativeInfinity,
    ToPositiveInfinity,
}

/// 2^52; spec `F64.integerBoundary`
pub const F64_INTEGER_BOUNDARY: F64 = F64::from_bits(0x4330_0000_0000_0000);
/// 0.49999999999999994; spec `F64.justBelowHalf`
pub const F64_JUST_BELOW_HALF: F64 = F64::from_bits(0x3FDF_FFFF_FFFF_FFFF);
/// 2^23; spec `F32.integerBoundary`
pub const F32_INTEGER_BOUNDARY: F32 = F32::from_bits(0x4B00_0000);
/// 0.49999997f; spec `F32.justBelowHalf`
pub const F32_JUST_BELOW_HALF: F32 = F32::from_bits(0x3EFF_FFFF);
const F64_ZERO: F64 = F64::from_bits(0);
const F32_ZERO: F32 = F32::from_bits(0);
/// 1e16
const F64_1E16: F64 = F64::from_bits(0x4341_C379_37E0_8000);
/// 1e8f
const F32_1E8: F32 = F32::from_bits(0x4CBE_BC20);

/// `10^k` for `k <= 19` (helper for `ofInt (10 ^ k)`)
pub fn pow10_u64(k: u32) -> u64 {
    let mut r: u64 = 1;
    let mut i: u32 = 0;
    while i < k {
        r = r * 10;
        i = i + 1;
    }
    r
}

/// `Math.Round(double)`, half to even; spec `OsuModel.Net.F64.round`
pub fn f64_round(a: F64) -> F64 {
    // NaN first (same model value: the spec result is NaN too): `to_bits` is identified with the
    // spec only on non-NaN values (proofs/OsuProofs/Generated/FunsExternal.lean)
    if a.is_nan() {
        a
    } else if F64_INTEGER_BOUNDARY.le(a.abs()) {
        a
    } else {
        let temp = f64_copy_sign(F64_INTEGER_BOUNDARY, a);
        f64_copy_sign(a.add(temp).sub(temp), a)
    }
}

/// `Math.Round(double, MidpointRounding)`; spec `OsuModel.Net.F64.roundMode`
pub fn f64_round_mode(x: F64, mode: MidpointRounding) -> F64 {
    match mode {
        MidpointRounding::AwayFromZero => x.add(f64_copy_sign(F64_JUST_BELOW_HALF, x)).trunc(),
        MidpointRounding::ToEven => f64_round(x),
        MidpointRounding::ToZero => x.trunc(),
        MidpointRounding::ToNegativeInfinity => x.floor(),
        MidpointRounding::ToPositiveInfinity => x.ceil(),
    }
}

/// `Math.Round(double, int digits, MidpointRounding)`; spec `OsuModel.Net.F64.roundDigitsMode`
pub fn f64_round_digits_mode(value: F64, digits: i64, mode: MidpointRounding) -> Result<F64, NetExn> {
    if digits < 0 || digits > 15 {
        Err(NetExn::ArgumentOutOfRange)
    } else if value.abs().lt(F64_1E16) {
        let power10 = F64::from_u64(pow10_u64(digits as u32));
        Ok(f64_round_mode(value.mul(power10), mode).div(power10))
    } else {
        Ok(value)
    }
}

/// `Math.Round(double, int digits)`; spec `OsuModel.Net.F64.roundDigits`
pub fn f64_round_digits(value: F64, digits: i64) -> Result<F64, NetExn> {
    f64_round_digits_mode(value, digits, MidpointRounding::ToEven)
}

/// `Math.Sign(double)`; spec `OsuModel.Net.F64.sign`
pub fn f64_sign(value: F64) -> Result<i32, NetExn> {
    if value.lt(F64_ZERO) {
        Ok(-1)
    } else if F64_ZERO.lt(value) {
        Ok(1)
    } else if value.eq(F64_ZERO) {
        Ok(0)
    } else {
        Err(NetExn::Arithmetic)
    }
}

/// `MathF.Round(float)`; spec `OsuModel.Net.F32.round`
pub fn f32_round(a: F32) -> F32 {
    // NaN first (same model value: the spec result is NaN too): `to_bits` is identified with the
    // spec only on non-NaN values (proofs/OsuProofs/Generated/FunsExternal.lean)
    if a.is_nan() {
        a
    } else if F32_INTEGER_BOUNDARY.le(a.abs()) {
        a
    } else {
        let temp = f32_copy_sign(F32_INTEGER_BOUNDARY, a);
        f32_copy_sign(a.add(temp).sub(temp), a)
    }
}

/// `MathF.Round(float, MidpointRounding)`; spec `OsuModel.Net.F32.roundMode`
pub fn f32_round_mode(x: F32, mode: MidpointRounding) -> F32 {
    match mode {
        MidpointRounding::AwayFromZero => x.add(f32_copy_sign(F32_JUST_BELOW_HALF, x)).trunc(),
        MidpointRounding::ToEven => f32_round(x),
        MidpointRounding::ToZero => x.trunc(),
        MidpointRounding::ToNegativeInfinity => x.floor(),
        MidpointRounding::ToPositiveInfinity => x.ceil(),
    }
}

/// `MathF.Round(float, int digits, MidpointRounding)`; spec `OsuModel.Net.F32.roundDigitsMode`
pub fn f32_round_digits_mode(x: F32, digits: i64, mode: MidpointRounding) -> Result<F32, NetExn> {
    if digits < 0 || digits > 6 {
        Err(NetExn::ArgumentOutOfRange)
    } else if x.abs().lt(F32_1E8) {
        let power10 = F32::from_u64(pow10_u64(digits as u32));
        Ok(f32_round_mode(x.mul(power10), mode).div(power10))
    } else {
        Ok(x)
    }
}

/// spec `OsuModel.Net.F32.roundDigits`
pub fn f32_round_digits(x: F32, digits: i64) -> Result<F32, NetExn> {
    f32_round_digits_mode(x, digits, MidpointRounding::ToEven)
}

/// `MathF.Max`; spec `OsuModel.Net.F32.max`
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

/// `MathF.Min`; spec `OsuModel.Net.F32.min`
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

/// `Math.Clamp(float, float, float)`; spec `OsuModel.Net.F32.clamp`
pub fn f32_clamp(value: F32, lo: F32, hi: F32) -> Result<F32, NetExn> {
    if hi.lt(lo) {
        Err(NetExn::Argument)
    } else if value.lt(lo) {
        Ok(lo)
    } else if hi.lt(value) {
        Ok(hi)
    } else {
        Ok(value)
    }
}

/// `Math.Clamp(double, double, double)` with the exception kind; spec `OsuModel.Net.F64.clamp`
/// (`crate::net::clamp` is the POC `Option` version).
pub fn f64_clamp(value: F64, lo: F64, hi: F64) -> Result<F64, NetExn> {
    if hi.lt(lo) {
        Err(NetExn::Argument)
    } else if value.lt(lo) {
        Ok(lo)
    } else if hi.lt(value) {
        Ok(hi)
    } else {
        Ok(value)
    }
}

/// `MathF.Sign`; spec `OsuModel.Net.F32.sign`
pub fn f32_sign(value: F32) -> Result<i32, NetExn> {
    if value.lt(F32_ZERO) {
        Ok(-1)
    } else if F32_ZERO.lt(value) {
        Ok(1)
    } else if value.eq(F32_ZERO) {
        Ok(0)
    } else {
        Err(NetExn::Arithmetic)
    }
}
