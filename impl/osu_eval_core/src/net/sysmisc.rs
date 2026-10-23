//! Port of `OsuModel/Net/SysMisc.lean`: `float/double.DegreesToRadians/RadiansToDegrees`,
//! `Enumerable.Average`.
use super::basic::NetExn;
use crate::float::{F32, F64};

/// `float.Pi`
pub const F32_PI: F32 = F32::from_bits(0x4049_0FDB);
pub const F32_180: F32 = F32::from_bits(0x4334_0000);
/// `Math.PI`
pub const F64_PI: F64 = F64::from_bits(0x4009_21FB_5444_2D18);
pub const F64_180: F64 = F64::from_bits(0x4066_8000_0000_0000);

/// spec `SysMisc.F32.degreesToRadians`
pub fn f32_degrees_to_radians(d: F32) -> F32 {
    d.mul(F32_PI).div(F32_180)
}
/// spec `SysMisc.F32.radiansToDegrees`
pub fn f32_radians_to_degrees(r: F32) -> F32 {
    r.mul(F32_180).div(F32_PI)
}
/// spec `SysMisc.F64.degreesToRadians`
pub fn f64_degrees_to_radians(d: F64) -> F64 {
    d.mul(F64_PI).div(F64_180)
}
/// spec `SysMisc.F64.radiansToDegrees`
pub fn f64_radians_to_degrees(r: F64) -> F64 {
    r.mul(F64_180).div(F64_PI)
}

/// `Enumerable.Average(IEnumerable<double>)`; spec `SysMisc.averageF64`
pub fn average_f64(xs: &[F64]) -> Result<F64, NetExn> {
    if xs.len() == 0 {
        Err(NetExn::Argument)
    } else {
        let mut acc = F64::from_bits(0);
        let mut i = 0;
        while i < xs.len() {
            acc = acc.add(xs[i]);
            i = i + 1;
        }
        Ok(acc.div(F64::from_u64(xs.len() as u64)))
    }
}
