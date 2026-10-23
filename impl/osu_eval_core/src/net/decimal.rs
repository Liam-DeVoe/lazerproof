//! Port of `OsuModel/Net/Decimal.lean`: the `System.Decimal` subset used by osu-framework
//! (`VarDecFromR8/R4`, `VarR8FromDec`, `VarDecDiv`, `VarDecMul`, `ScaleResult`,
//! `SearchScale`, `OverflowUnscale`, `Unscale`, `InternalRound`, `CreateTruncating`).
//!
//! The spec's exact `Nat` arithmetic is done in `u128` where every intermediate provably fits
//! (mantissas < 2^96, scale factors <= 10^9), and in the 192-bit `U192` for the product of two
//! 96-bit mantissas (`mul`/`scaleResult`).
use super::basic::NetExn;
use super::mathops::f64_round;
use crate::float::{F32, F64};

/// spec `OsuModel.Net.NetDecimal` (sign bit, mantissa < 2^96, scale <= 28)
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct NetDecimal {
    pub neg: bool,
    pub mant: u128,
    pub scale: u32,
}

/// 2^96
pub const TWO96: u128 = 1u128 << 96;
pub const ZERO: NetDecimal = NetDecimal { neg: false, mant: 0, scale: 0 };
/// `decimal.MaxValue`
pub const MAX_VALUE: NetDecimal = NetDecimal { neg: false, mant: TWO96 - 1, scale: 0 };
/// `decimal.MinValue`
pub const MIN_VALUE: NetDecimal = NetDecimal { neg: true, mant: TWO96 - 1, scale: 0 };

/// `10^k` as `u128` (`k <= 38`)
pub fn pow10(k: u32) -> u128 {
    let mut r: u128 = 1;
    let mut i = 0;
    while i < k {
        r = r * 10;
        i = i + 1;
    }
    r
}

/// `decimal.GetBits`: `[lo, mid, hi, flags]`; spec `NetDecimal.getBits`
pub fn get_bits(d: NetDecimal) -> (u32, u32, u32, u32) {
    let flags: u32 = (d.scale << 16) | (if d.neg { 0x8000_0000 } else { 0 });
    ((d.mant & 0xFFFF_FFFF) as u32, ((d.mant >> 32) & 0xFFFF_FFFF) as u32, ((d.mant >> 64) & 0xFFFF_FFFF) as u32, flags)
}

/// `new decimal(int[] bits)`; spec `NetDecimal.ofBits`
pub fn of_bits(lo: u32, mid: u32, hi: u32, flags: u32) -> NetDecimal {
    NetDecimal {
        neg: (flags >> 31) == 1,
        mant: (lo as u128) | ((mid as u128) << 32) | ((hi as u128) << 64),
        scale: (flags >> 16) & 0xFF,
    }
}

/// `d > 0m`; spec `NetDecimal.isPositive`
pub fn is_positive(d: NetDecimal) -> bool {
    !d.neg && d.mant != 0
}

/// `DoublePowers10[k]` = the double literal `1e{k}`; spec `NetDecimal.doublePowers10`
pub fn double_powers10(k: u32) -> F64 {
    match k {
        0 => F64::from_bits(0x3FF0000000000000),
        1 => F64::from_bits(0x4024000000000000),
        2 => F64::from_bits(0x4059000000000000),
        3 => F64::from_bits(0x408F400000000000),
        4 => F64::from_bits(0x40C3880000000000),
        5 => F64::from_bits(0x40F86A0000000000),
        6 => F64::from_bits(0x412E848000000000),
        7 => F64::from_bits(0x416312D000000000),
        8 => F64::from_bits(0x4197D78400000000),
        9 => F64::from_bits(0x41CDCD6500000000),
        10 => F64::from_bits(0x4202A05F20000000),
        11 => F64::from_bits(0x42374876E8000000),
        12 => F64::from_bits(0x426D1A94A2000000),
        13 => F64::from_bits(0x42A2309CE5400000),
        14 => F64::from_bits(0x42D6BCC41E900000),
        15 => F64::from_bits(0x430C6BF526340000),
        16 => F64::from_bits(0x4341C37937E08000),
        17 => F64::from_bits(0x4376345785D8A000),
        18 => F64::from_bits(0x43ABC16D674EC800),
        19 => F64::from_bits(0x43E158E460913D00),
        20 => F64::from_bits(0x4415AF1D78B58C40),
        21 => F64::from_bits(0x444B1AE4D6E2EF50),
        22 => F64::from_bits(0x4480F0CF064DD592),
        23 => F64::from_bits(0x44B52D02C7E14AF6),
        24 => F64::from_bits(0x44EA784379D99DB4),
        25 => F64::from_bits(0x45208B2A2C280291),
        26 => F64::from_bits(0x4554ADF4B7320335),
        27 => F64::from_bits(0x4589D971E4FE8402),
        28 => F64::from_bits(0x45C027E72F1F1281),
        _ => F64::from_bits(0x7FF8_0000_0000_0000),
    }
}

/// 2^64 as a double; spec `NetDecimal.ds2to64`
pub const DS2TO64: F64 = F64::from_bits(0x43F0_0000_0000_0000);

/// `VarR8FromDec` = `(double)d`; spec `NetDecimal.toF64`
pub fn to_f64(d: NetDecimal) -> F64 {
    let lo = (d.mant & 0xFFFF_FFFF_FFFF_FFFF) as u64;
    let hi = (d.mant >> 64) as u64;
    let num = F64::from_u64(lo).add(F64::from_u64(hi).mul(DS2TO64)).div(double_powers10(d.scale));
    if d.neg { num.neg() } else { num }
}

/// `VarR4FromDec` = `(float)(double)d`; spec `NetDecimal.toF32`
pub fn to_f32(d: NetDecimal) -> F32 {
    to_f64(d).to_f32()
}

/// C# `>>` on int (floor division by 2^k); spec `NetDecimal.sar`
pub fn sar(x: i64, k: u32) -> i64 {
    x >> k
}

/// spec `NetDecimal.finishFromR` (`steps` = the greedy stripping powers, largest first)
pub fn finish_from_r(neg: bool, mant: u128, power: i64, max_strip: u32, steps: &[u32]) -> Result<NetDecimal, NetExn> {
    if power < 0 {
        let v = mant * pow10((-power) as u32);
        if v >= TWO96 { Err(NetExn::Overflow) } else { Ok(NetDecimal { neg, mant: v, scale: 0 }) }
    } else {
        let mut m = mant;
        let mut p = power as u32;
        let mut lim = if p < max_strip { p } else { max_strip };
        let mut i = 0;
        while i < steps.len() {
            let k = steps[i];
            if lim >= k && m % pow10(k) == 0 {
                m = m / pow10(k);
                p = p - k;
                lim = lim - k;
            }
            i = i + 1;
        }
        Ok(NetDecimal { neg, mant: m, scale: p })
    }
}

const P1E15: F64 = F64::from_bits(0x430C_6BF5_2634_0000);
const P1E14: F64 = F64::from_bits(0x42D6_BCC4_1E90_0000);
const P1E7: F64 = F64::from_bits(0x4163_12D0_0000_0000);
const P1E6: F64 = F64::from_bits(0x412E_8480_0000_0000);
const F64TEN: F64 = F64::from_bits(0x4024_0000_0000_0000);
const F64_ZERO: F64 = F64::from_bits(0);
const F32_ZERO: F32 = F32::from_bits(0);
const STEPS_R8: [u32; 4] = [8, 4, 2, 1];
const STEPS_R4: [u32; 3] = [4, 2, 1];

/// `VarDecFromR8` = `(decimal)double`; spec `NetDecimal.ofF64`
pub fn of_f64(input: F64) -> Result<NetDecimal, NetExn> {
    // NaN first (same model value: the spec throws Overflow for NaN: exponent 0x7FF): `to_bits` is identified with the
    // spec only on non-NaN values (proofs/OsuProofs/Generated/FunsExternal.lean)
    if input.is_nan() {
        return Err(NetExn::Overflow);
    }
    let e: i64 = ((input.to_bits() >> 52) & 0x7FF) as i64;
    let num = e - 1022;
    if num < -94 {
        Ok(ZERO)
    } else if num > 96 {
        Err(NetExn::Overflow)
    } else {
        let neg = input.lt(F64_ZERO);
        let dbl0 = if neg { input.neg() } else { input };
        let power0: i64 = 14 - sar(num * 19728, 16);
        let mut dbl = dbl0;
        let mut power = power0;
        if power0 >= 0 {
            power = if power0 > 28 { 28 } else { power0 };
            dbl = dbl0.mul(double_powers10(power as u32));
        } else if power0 != -1 || P1E15.le(dbl0) {
            dbl = dbl0.div(double_powers10((-power0) as u32));
        } else {
            power = 0;
        }
        if dbl.lt(P1E14) && power < 28 {
            dbl = dbl.mul(F64TEN);
            power = power + 1;
        }
        let r = f64_round(dbl).to_i64_sat();
        let mant: u128 = if r < 0 { 0 } else { r as u128 };
        if mant == 0 { Ok(ZERO) } else { finish_from_r(neg, mant, power, 14, &STEPS_R8) }
    }
}

/// `VarDecFromR4` = `(decimal)float`; spec `NetDecimal.ofF32`
pub fn of_f32(input: F32) -> Result<NetDecimal, NetExn> {
    // NaN first (same model value: the spec throws Overflow for NaN: exponent 0xFF): `to_bits` is identified with the
    // spec only on non-NaN values (proofs/OsuProofs/Generated/FunsExternal.lean)
    if input.is_nan() {
        return Err(NetExn::Overflow);
    }
    let e: i64 = ((input.to_bits() >> 23) & 0xFF) as i64;
    let num = e - 126;
    if num < -94 {
        Ok(ZERO)
    } else if num > 96 {
        Err(NetExn::Overflow)
    } else {
        let neg = input.lt(F32_ZERO);
        let dbl0 = (if neg { input.neg() } else { input }).to_f64();
        let power0: i64 = 6 - sar(num * 19728, 16);
        let mut dbl = dbl0;
        let mut power = power0;
        if power0 >= 0 {
            power = if power0 > 28 { 28 } else { power0 };
            dbl = dbl0.mul(double_powers10(power as u32));
        } else if power0 != -1 || P1E7.le(dbl0) {
            dbl = dbl0.div(double_powers10((-power0) as u32));
        } else {
            power = 0;
        }
        if dbl.lt(P1E6) && power < 28 {
            dbl = dbl.mul(F64TEN);
            power = power + 1;
        }
        let r = f64_round(dbl).to_i32_sat();
        let mant: u128 = if r < 0 { 0 } else { r as u128 };
        if mant == 0 { Ok(ZERO) } else { finish_from_r(neg, mant, power, 6, &STEPS_R4) }
    }
}

/// 7.922816251426434E+28 = 2^96; spec `NetDecimal.f64DecMax`
pub const F64_DEC_MAX: F64 = F64::from_bits(0x45F0_0000_0000_0000);
/// 7.9228163E+28f; spec `NetDecimal.f32DecMax`
pub const F32_DEC_MAX: F32 = F32::from_bits(0x6F80_0000);

/// `decimal.CreateTruncating(double)`; spec `NetDecimal.createTruncatingF64`
pub fn create_truncating_f64(x: F64) -> Result<NetDecimal, NetExn> {
    if F64_DEC_MAX.le(x) {
        Ok(MAX_VALUE)
    } else if x.le(F64_DEC_MAX.neg()) {
        Ok(MIN_VALUE)
    } else if x.is_nan() {
        Ok(NetDecimal { neg: false, mant: 0, scale: 1 })
    } else {
        of_f64(x)
    }
}

/// `decimal.CreateTruncating(float)`; spec `NetDecimal.createTruncatingF32`
pub fn create_truncating_f32(x: F32) -> Result<NetDecimal, NetExn> {
    if F32_DEC_MAX.le(x) {
        Ok(MAX_VALUE)
    } else if x.le(F32_DEC_MAX.neg()) {
        Ok(MIN_VALUE)
    } else if x.is_nan() {
        Ok(NetDecimal { neg: false, mant: 0, scale: 1 })
    } else {
        of_f32(x)
    }
}

/// A 192-bit unsigned integer (`hi * 2^128 + lo`, `hi < 2^64`): the spec's `Nat` for products
/// of two 96-bit mantissas.
#[derive(Clone, Copy)]
pub struct U192 {
    pub hi: u64,
    pub lo: u128,
}

/// exact product of two values `< 2^96`
pub fn mul_u96(a: u128, b: u128) -> U192 {
    let a_lo = a & 0xFFFF_FFFF_FFFF_FFFF;
    let a_hi = a >> 64; // < 2^32
    let b_lo = b & 0xFFFF_FFFF_FFFF_FFFF;
    let b_hi = b >> 64;
    let ll = a_lo * b_lo; // < 2^128
    let mid = a_lo * b_hi + a_hi * b_lo; // each < 2^96, sum < 2^97
    let hh = a_hi * b_hi; // < 2^64
    // value = hh * 2^128 + mid * 2^64 + ll
    let mid_lo = (mid & 0xFFFF_FFFF_FFFF_FFFF) << 64;
    let mid_hi = mid >> 64;
    let (lo, carry) = ll.overflowing_add(mid_lo);
    let hi = hh + mid_hi + (if carry { 1 } else { 0 });
    U192 { hi: hi as u64, lo }
}

pub fn u192_is_zero(x: U192) -> bool {
    x.hi == 0 && x.lo == 0
}

/// `x >= 2^96`
pub fn u192_ge_two96(x: U192) -> bool {
    x.hi != 0 || x.lo >= TWO96
}

/// `Nat.log2 x + 1` (bit length; 0 for 0)
pub fn u192_bitlen(x: U192) -> u32 {
    if x.hi != 0 {
        128 + (64 - x.hi.leading_zeros())
    } else {
        128 - x.lo.leading_zeros()
    }
}

/// `(x / d, x % d)` for `0 < d < 2^32`
pub fn u192_divmod_small(x: U192, d: u64) -> (U192, u64) {
    let dd = d as u128;
    let q_hi = (x.hi as u128) / dd;
    let r1 = (x.hi as u128) % dd; // < 2^32
    let top = (r1 << 64) | (x.lo >> 64); // < 2^96
    let q_mid = top / dd; // < 2^64
    let r2 = top % dd;
    let bot = (r2 << 64) | (x.lo & 0xFFFF_FFFF_FFFF_FFFF);
    let q_low = bot / dd;
    let r3 = bot % dd;
    // q = q_hi * 2^128 + q_mid * 2^64 + q_low (q_low < 2^96 but < 2^64 * d ... combine with carry)
    let (lo, carry) = (q_mid << 64).overflowing_add(q_low);
    (U192 { hi: (q_hi as u64) + (if carry { 1 } else { 0 }), lo }, r3 as u64)
}

/// `x + 1`
pub fn u192_add_one(x: U192) -> U192 {
    let (lo, carry) = x.lo.overflowing_add(1);
    U192 { hi: x.hi + (if carry { 1 } else { 0 }), lo }
}

/// `ScaleResult`; spec `NetDecimal.scaleResult`
pub fn scale_result(p: U192, scale: u32) -> Result<(u128, u32), NetExn> {
    let bitlen = u192_bitlen(p) as i64;
    let mut num: i64 = 0;
    let mut bad = false;
    if u192_ge_two96(p) {
        num = sar((bitlen - 97) * 77, 8) + 1;
        if num > scale as i64 {
            bad = true;
        }
    }
    if bad {
        Err(NetExn::Overflow)
    } else {
        if num < (scale as i64) - 28 {
            num = (scale as i64) - 28;
        }
        if num == 0 {
            Ok((p.lo, scale))
        } else {
            scale_result_loop(p, (scale as i64) - num, num)
        }
    }
}

/// The `for _ in [0:120]` loop of `scaleResult` (state: q, sc, num, sticky, rem, pow).
pub fn scale_result_loop(p: U192, sc0: i64, num0: i64) -> Result<(u128, u32), NetExn> {
    let mut q = p;
    let mut sc = sc0;
    let mut num = num0;
    let mut sticky = false;
    let mut rem: u64 = 0;
    let mut res: Option<Result<(u128, u32), NetExn>> = None;
    let mut it = 0;
    while res.is_none() && it < 120 {
        it = it + 1;
        sticky = sticky || rem != 0;
        let chunk: u32 = if num >= 9 { 9 } else if num < 0 { 0 } else { num as u32 };
        let pw = pow10(chunk) as u64;
        let (q2, r2) = u192_divmod_small(q, pw);
        rem = r2;
        q = q2;
        num = num - 9;
        if num > 0 {
            // continue
        } else if u192_ge_two96(q) {
            if sc == 0 {
                res = Some(Err(NetExn::Overflow));
            } else {
                num = 1;
                sc = sc - 1;
            }
        } else {
            let half = pw / 2;
            if half <= rem && (half < rem || (q.lo & 1) == 1 || sticky) {
                q = u192_add_one(q);
                if u192_ge_two96(q) {
                    if sc == 0 {
                        res = Some(Err(NetExn::Overflow));
                    } else {
                        sticky = false;
                        rem = 0;
                        num = 1;
                        sc = sc - 1;
                    }
                } else {
                    res = Some(Ok((q.lo, sc as u32)));
                }
            } else {
                res = Some(Ok((q.lo, sc as u32)));
            }
        }
    }
    match res {
        Some(r) => r,
        None => Ok((q.lo, sc as u32)),
    }
}

/// `decimal * decimal` (`VarDecMul`); spec `NetDecimal.mul`
pub fn mul(d1: NetDecimal, d2: NetDecimal) -> Result<NetDecimal, NetExn> {
    let scale = d1.scale + d2.scale;
    let neg = d1.neg != d2.neg;
    if d1.mant < (1u128 << 32) && d2.mant < (1u128 << 32) {
        let mut p = d1.mant * d2.mant;
        let mut s = scale;
        if s > 28 {
            if s > 47 {
                return Ok(ZERO);
            }
            let pw = pow10(s - 28);
            let q = p / pw;
            let item = p % pw;
            let half = pw / 2;
            p = if item >= half && (item > half || q % 2 == 1) { q + 1 } else { q };
            s = 28;
        }
        Ok(NetDecimal { neg, mant: p, scale: s })
    } else {
        let p = mul_u96(d1.mant, d2.mant);
        if u192_is_zero(p) {
            Ok(ZERO)
        } else if u192_ge_two96(p) || scale > 28 {
            let (q, s) = tri!(scale_result(p, scale));
            Ok(NetDecimal { neg, mant: q, scale: s })
        } else {
            Ok(NetDecimal { neg, mant: p.lo, scale })
        }
    }
}

/// `PowerOvflValues[i]` = `floor((2^96 - 1) / 10^(i+1))` as (hi, midlo); spec `NetDecimal.powerOvfl`
pub fn power_ovfl(i: u32) -> (u128, u128) {
    let v = (TWO96 - 1) / pow10(i + 1);
    (v >> 64, v & 0xFFFF_FFFF_FFFF_FFFF)
}

/// spec `searchScale.check`
fn search_check(num: u32, scale: i64) -> Result<u32, NetExn> {
    if (num as i64) + scale < 0 { Err(NetExn::Overflow) } else { Ok(num) }
}

/// `SearchScale(quotient, scale)`; spec `NetDecimal.searchScale`
pub fn search_scale(q: u128, scale: i64) -> Result<u32, NetExn> {
    let u = q >> 64;
    let low = q & 0xFFFF_FFFF_FFFF_FFFF;
    if u > 429496729 {
        search_check(0, scale)
    } else {
        let num0: u32 = if u > 42949 {
            if u > 4294967 {
                if u > 42949672 { 1 } else { 2 }
            } else if u > 429496 {
                3
            } else {
                4
            }
        } else if u > 429 {
            if u > 4294 { 5 } else { 6 }
        } else if u > 42 {
            7
        } else {
            8
        };
        let (hi, ml) = power_ovfl(num0 - 1);
        let band = if u == hi && low > ml { num0 - 1 } else { num0 };
        if scale > 19 {
            let num = (28 - scale) as u32;
            let (h2, _) = power_ovfl(num - 1);
            if u < h2 { search_check(num, scale) } else { search_check(band, scale) }
        } else if u < 4 || (u == 4 && low <= 5441186219426131129) {
            Ok(9)
        } else {
            search_check(band, scale)
        }
    }
}

/// `OverflowUnscale`; spec `NetDecimal.overflowUnscale`
pub fn overflow_unscale(q: u128, scale0: i64, sticky: bool) -> Result<(u128, i64), NetExn> {
    let scale = scale0 - 1;
    if scale < 0 {
        Err(NetExn::Overflow)
    } else {
        let r = q % 10;
        let q2 = q / 10;
        Ok((if r > 5 || (r == 5 && (sticky || q2 % 2 == 1)) { q2 + 1 } else { q2 }, scale))
    }
}

/// `Unscale`; spec `NetDecimal.unscale`
pub fn unscale(q0: u128, scale0: i64) -> (u128, i64) {
    let mut q = q0;
    let mut s = scale0;
    let mut i = 0;
    while i < 4 {
        if q % 100000000 == 0 && s >= 8 {
            q = q / 100000000;
            s = s - 8;
        }
        i = i + 1;
    }
    if q % 10000 == 0 && s >= 4 {
        q = q / 10000;
        s = s - 4;
    }
    if q % 100 == 0 && s >= 2 {
        q = q / 100;
        s = s - 2;
    }
    if q % 10 == 0 && s >= 1 {
        q = q / 10;
        s = s - 1;
    }
    (q, s)
}

/// State of the division loop of `VarDecDiv`.
#[derive(Clone, Copy)]
pub struct DivState {
    pub scale: i64,
    pub flag: bool,
    pub q: u128,
    pub r: u128,
    pub round_it: bool,
    pub done: bool,
}

/// One iteration of the `for _ in [0:40]` loop of `div` (`done` = break).
pub fn div_step(st: DivState, den: u128) -> Result<DivState, NetExn> {
    let mut s = st;
    let p: u32;
    if s.r == 0 {
        if s.scale >= 0 {
            s.done = true;
            return Ok(s);
        }
        let m = -s.scale;
        p = if m < 9 { m as u32 } else { 9 };
    } else {
        s.flag = true;
        if s.scale == 28 {
            s.round_it = true;
            s.done = true;
            return Ok(s);
        }
        p = tri!(search_scale(s.q, s.scale));
        if p == 0 {
            s.round_it = true;
            s.done = true;
            return Ok(s);
        }
    }
    s.scale = s.scale + (p as i64);
    let pw = pow10(p);
    if s.q * pw >= TWO96 {
        return Err(NetExn::Overflow);
    }
    let rr = s.r * pw;
    s.q = s.q * pw + rr / den;
    s.r = rr % den;
    if s.q >= TWO96 {
        let (q2, s2) = tri!(overflow_unscale(s.q, s.scale, s.r != 0));
        s.q = q2;
        s.scale = s2;
        s.done = true;
    }
    Ok(s)
}

/// `decimal / decimal` (`VarDecDiv`); spec `NetDecimal.div`
pub fn div(d1: NetDecimal, d2: NetDecimal) -> Result<NetDecimal, NetExn> {
    let den = d2.mant;
    if den == 0 {
        return Err(NetExn::Arithmetic);
    }
    let mut st = DivState {
        scale: (d1.scale as i64) - (d2.scale as i64),
        flag: false,
        q: d1.mant / den,
        r: d1.mant % den,
        round_it: false,
        done: false,
    };
    let mut it = 0;
    let mut err: Option<NetExn> = None;
    while !st.done && err.is_none() && it < 40 {
        match div_step(st, den) {
            Ok(s2) => st = s2,
            Err(e) => err = Some(e),
        }
        it = it + 1;
    }
    match err {
        Some(e) => Err(e),
        None => div_finish(d1, d2, st, den),
    }
}

/// The rounding / unscaling tail of `div`.
pub fn div_finish(d1: NetDecimal, d2: NetDecimal, st: DivState, den: u128) -> Result<NetDecimal, NetExn> {
    let mut q = st.q;
    let mut scale = st.scale;
    if st.round_it {
        if 2 * st.r > den || (2 * st.r == den && q % 2 == 1) {
            q = q + 1;
            if q >= TWO96 {
                let (q2, s2) = tri!(overflow_unscale(q, scale, true));
                q = q2;
                scale = s2;
            }
        }
    }
    if st.flag {
        let (q2, s2) = unscale(q, scale);
        q = q2;
        scale = s2;
    }
    Ok(NetDecimal { neg: d1.neg != d2.neg, mant: q, scale: if scale < 0 { 0 } else { scale as u32 } })
}

/// `Math.Round(decimal)` (half-even, scale 0, keeps the sign bit); spec `NetDecimal.round`
pub fn round(d: NetDecimal) -> NetDecimal {
    if d.scale == 0 {
        d
    } else {
        let pw = pow10(d.scale);
        let q = d.mant / pw;
        let r = d.mant % pw;
        let q2 = if 2 * r > pw || (2 * r == pw && q % 2 == 1) { q + 1 } else { q };
        NetDecimal { neg: d.neg, mant: q2, scale: 0 }
    }
}
