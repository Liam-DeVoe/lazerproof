//! Port of `OsuModel/Beatmap/Vector2.lean`: `osuTK.Vector2` (float32; the same type as
//! `net::osutk::Vector2`) and `osu.Framework.Utils.Precision`.
use crate::float::{F32, F64};
pub use crate::net::osutk::Vector2 as Vec2;
use crate::net::osutk;

pub const ZERO: Vec2 = osutk::V2_ZERO;

/// `new Vector2(v)`; spec `Vec2.splat`
pub fn splat(v: F32) -> Vec2 {
    Vec2 { x: v, y: v }
}
pub fn add(a: Vec2, b: Vec2) -> Vec2 {
    osutk::v2_add(a, b)
}
pub fn sub(a: Vec2, b: Vec2) -> Vec2 {
    osutk::v2_sub(a, b)
}
pub fn neg(a: Vec2) -> Vec2 {
    osutk::v2_neg(a)
}
pub fn scale(a: Vec2, s: F32) -> Vec2 {
    osutk::v2_scale(a, s)
}
/// `operator /(Vector2, float)`; spec `Vec2.div`
pub fn div(a: Vec2, s: F32) -> Vec2 {
    osutk::v2_div_s(a, s)
}
pub fn eq(a: Vec2, b: Vec2) -> bool {
    osutk::v2_eq(a, b)
}
pub fn length_squared(a: Vec2) -> F32 {
    osutk::v2_length_squared(a)
}
pub fn length(a: Vec2) -> F32 {
    osutk::v2_length(a)
}
pub fn normalized(a: Vec2) -> Vec2 {
    osutk::v2_normalized(a)
}
/// osuTK `Vector2.Distance`; spec `Vec2.distance`
pub fn distance(v1: Vec2, v2: Vec2) -> F32 {
    osutk::v2_distance(v1, v2)
}
/// framework `Vector2Extensions.Distance` (`MathF.Sqrt`); spec `Vec2.distanceFw`
pub fn distance_fw(v1: Vec2, v2: Vec2) -> F32 {
    crate::net::framework::distance(v1, v2)
}
pub fn dot(a: Vec2, b: Vec2) -> F32 {
    osutk::v2_dot(a, b)
}

/// `Precision.FLOAT_EPSILON = 1e-3f`
pub const FLOAT_EPSILON: F32 = F32::from_bits(0x3A83_126F);
/// `Precision.DOUBLE_EPSILON = 1e-7`
pub const DOUBLE_EPSILON: F64 = F64::from_bits(0x3E7A_D7F2_9ABC_AF48);

/// `Precision.AlmostEquals(float, float, FLOAT_EPSILON)`; spec `Precision.almostEqualsF32`
pub fn almost_equals_f32(a: F32, b: F32) -> bool {
    a.sub(b).abs().le(FLOAT_EPSILON)
}
/// `Precision.AlmostEquals(double, double, DOUBLE_EPSILON)`; spec `Precision.almostEqualsF64`
pub fn almost_equals_f64(a: F64, b: F64) -> bool {
    a.sub(b).abs().le(DOUBLE_EPSILON)
}
/// `Precision.DefinitelyBigger(double, double, DOUBLE_EPSILON)`; spec `Precision.definitelyBiggerF64`
pub fn definitely_bigger_f64(a: F64, b: F64) -> bool {
    b.lt(a.sub(DOUBLE_EPSILON))
}
