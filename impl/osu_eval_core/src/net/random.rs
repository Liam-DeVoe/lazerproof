//! Port of `OsuModel/Net/Random.lean`: `System.Random(int seed)` (`CompatSeedImpl` +
//! `CompatPrng`, Knuth's subtractive generator). All arithmetic is C# `unchecked` int (wrapping).
use super::basic::NetExn;
use crate::float::{F32, F64};

/// `int.MaxValue` (`MBIG`)
pub const MBIG: i32 = 2147483647;
/// `MSEED`
pub const MSEED: i32 = 161803398;

/// spec `NetRandom.State` (`_seedArray[56]`, `_inext`, `_inextp`)
#[derive(Clone, Copy)]
pub struct State {
    pub a: [i32; 56],
    pub inext: usize,
    pub inextp: usize,
}

/// spec `NetRandom.initLoop1 54 a mj 1 0` (first loop of `Initialize`)
pub fn init_loop1(a0: [i32; 56], mj0: i32) -> [i32; 56] {
    let mut a = a0;
    let mut mj = mj0;
    let mut mk: i32 = 1;
    let mut ii: usize = 0;
    let mut n: usize = 0;
    while n < 54 {
        ii = if ii + 21 >= 55 { ii + 21 - 55 } else { ii + 21 };
        a[ii] = mk;
        mk = mj.wrapping_sub(mk);
        if mk < 0 {
            mk = mk.wrapping_add(MBIG);
        }
        mj = a[ii];
        n = n + 1;
    }
    a
}

/// spec `NetRandom.initLoop2Inner 55 a 1`
pub fn init_loop2_inner(a0: [i32; 56]) -> [i32; 56] {
    let mut a = a0;
    let mut k: usize = 1;
    while k < 56 {
        let n = if k + 30 >= 55 { k + 30 - 55 } else { k + 30 };
        let mut v = a[k].wrapping_sub(a[1 + n]);
        if v < 0 {
            v = v.wrapping_add(MBIG);
        }
        a[k] = v;
        k = k + 1;
    }
    a
}

/// spec `NetRandom.initLoop2 4`
pub fn init_loop2(a0: [i32; 56]) -> [i32; 56] {
    let mut a = a0;
    let mut j = 0;
    while j < 4 {
        a = init_loop2_inner(a);
        j = j + 1;
    }
    a
}

/// `new Random(seed)`; spec `NetRandom.create`
pub fn create(seed: i32) -> State {
    let sub: i32 = if seed == -2147483648 { 2147483647 } else if seed < 0 { -seed } else { seed };
    let mj = MSEED.wrapping_sub(sub);
    let mut a = [0i32; 56];
    a[55] = mj;
    let a = init_loop1(a, mj);
    let a = init_loop2(a);
    State { a, inext: 0, inextp: 21 }
}

/// `CompatPrng.InternalSample()`; spec `NetRandom.internalSample`
pub fn internal_sample(st: State) -> (i32, State) {
    let inext = if st.inext + 1 >= 56 { 1 } else { st.inext + 1 };
    let inextp = if st.inextp + 1 >= 56 { 1 } else { st.inextp + 1 };
    let mut num = st.a[inext].wrapping_sub(st.a[inextp]);
    if num == MBIG {
        num = num - 1;
    }
    if num < 0 {
        num = num.wrapping_add(MBIG);
    }
    let mut a = st.a;
    a[inext] = num;
    (num, State { a, inext, inextp })
}

/// `1.0 / int.MaxValue` (bits `0x3E00000000200000`); spec `NetRandom.invMBIG`
pub const INV_MBIG: F64 = F64::from_bits(0x3E00_0000_0020_0000);

/// `CompatPrng.Sample()` = `NextDouble()`; spec `NetRandom.sample`
pub fn sample(st: State) -> (F64, State) {
    let (n, st2) = internal_sample(st);
    (F64::from_i64(n as i64).mul(INV_MBIG), st2)
}

/// `Random.NextDouble()`; spec `NetRandom.nextDouble`
pub fn next_double(st: State) -> (F64, State) {
    sample(st)
}

/// `Random.Next()`; spec `NetRandom.next`
pub fn next(st: State) -> (i32, State) {
    internal_sample(st)
}

/// `Random.Next(maxValue)`; spec `NetRandom.nextMax`
pub fn next_max(st: State, max_value: i32) -> Result<(i32, State), NetExn> {
    if max_value < 0 {
        Err(NetExn::ArgumentOutOfRange)
    } else {
        let (s, st2) = sample(st);
        Ok((s.mul(F64::from_i64(max_value as i64)).to_i32_sat(), st2))
    }
}

const C2147483646: F64 = F64::from_bits(0x41DF_FFFF_FF80_0000);
const C4294967293: F64 = F64::from_bits(0x41EF_FFFF_FFA0_0000);

/// `CompatPrng.GetSampleForLargeRange()`; spec `NetRandom.sampleForLargeRange`
pub fn sample_for_large_range(st: State) -> (F64, State) {
    let (n0, st1) = internal_sample(st);
    let (m, st2) = internal_sample(st1);
    let n: i64 = if m % 2 == 0 { -(n0 as i64) } else { n0 as i64 };
    (F64::from_i64(n).add(C2147483646).div(C4294967293), st2)
}

/// `Random.Next(minValue, maxValue)`; spec `NetRandom.nextRange`
pub fn next_range(st: State, min_value: i32, max_value: i32) -> Result<(i32, State), NetExn> {
    if max_value < min_value {
        Err(NetExn::ArgumentOutOfRange)
    } else {
        let range: i64 = (max_value as i64) - (min_value as i64);
        if range > 2147483647 {
            let (s, st2) = sample_for_large_range(st);
            let l = s.mul(F64::from_i64(range)).to_i64_sat().wrapping_add(min_value as i64);
            Ok((l as i32, st2))
        } else {
            let (s, st2) = sample(st);
            let v = (s.mul(F64::from_i64(range)).to_i32_sat() as i64) + (min_value as i64);
            Ok((v as i32, st2))
        }
    }
}

const F32_ONE: F32 = F32::from_bits(0x3F80_0000);

/// `Random.NextSingle()` with `fuel` retries; spec `NetRandom.nextSingle`
pub fn next_single(fuel: u64, st0: State) -> Option<(F32, State)> {
    let mut st = st0;
    let mut k: u64 = 0;
    let mut res: Option<(F32, State)> = None;
    while res.is_none() && k < fuel {
        let (s, st2) = sample(st);
        st = st2;
        let f = s.to_f32();
        if f.lt(F32_ONE) {
            res = Some((f, st));
        }
        k = k + 1;
    }
    res
}
