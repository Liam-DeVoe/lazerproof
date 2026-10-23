//! Port of `OsuModel/Net/OsuTK.lean`: `osuTK.Vector2/Vector3/Matrix3/MathHelper` (binary32,
//! source order). `OsuModel.Beatmap.Vec2` is the same type (`crate::beatmap::vector2`).
use crate::float::{F32, F64};

/// `osuTK.Vector2`; spec `OsuTK.Vector2` (= `OsuModel.Beatmap.Vec2`)
#[derive(Clone, Copy)]
pub struct Vector2 {
    pub x: F32,
    pub y: F32,
}

/// `osuTK.Vector3`
#[derive(Clone, Copy)]
pub struct Vector3 {
    pub x: F32,
    pub y: F32,
    pub z: F32,
}

/// `osuTK.Matrix3` (row-major)
#[derive(Clone, Copy)]
pub struct Matrix3 {
    pub row0: Vector3,
    pub row1: Vector3,
    pub row2: Vector3,
}

pub const F32_ZERO: F32 = F32::from_bits(0);
pub const F32_ONE: F32 = F32::from_bits(0x3F80_0000);

pub const V2_ZERO: Vector2 = Vector2 { x: F32_ZERO, y: F32_ZERO };
pub const V2_ONE: Vector2 = Vector2 { x: F32_ONE, y: F32_ONE };

pub fn v2(x: F32, y: F32) -> Vector2 {
    Vector2 { x, y }
}
/// `operator +`
pub fn v2_add(a: Vector2, b: Vector2) -> Vector2 {
    Vector2 { x: a.x.add(b.x), y: a.y.add(b.y) }
}
/// `operator -`
pub fn v2_sub(a: Vector2, b: Vector2) -> Vector2 {
    Vector2 { x: a.x.sub(b.x), y: a.y.sub(b.y) }
}
/// unary `operator -` (IL `neg`)
pub fn v2_neg(a: Vector2) -> Vector2 {
    Vector2 { x: a.x.neg(), y: a.y.neg() }
}
/// `operator *(Vector2, float)` / `*(float, Vector2)`
pub fn v2_scale(a: Vector2, s: F32) -> Vector2 {
    Vector2 { x: a.x.mul(s), y: a.y.mul(s) }
}
/// `operator *(Vector2, Vector2)` (componentwise)
pub fn v2_mul(a: Vector2, b: Vector2) -> Vector2 {
    Vector2 { x: a.x.mul(b.x), y: a.y.mul(b.y) }
}
/// `operator /(Vector2, float)`
pub fn v2_div_s(a: Vector2, s: F32) -> Vector2 {
    Vector2 { x: a.x.div(s), y: a.y.div(s) }
}
/// `Vector2.Divide(Vector2, Vector2)`
pub fn v2_divide(a: Vector2, b: Vector2) -> Vector2 {
    Vector2 { x: a.x.div(b.x), y: a.y.div(b.y) }
}
/// `operator ==` (float `==`)
pub fn v2_eq(a: Vector2, b: Vector2) -> bool {
    a.x.eq(b.x) && a.y.eq(b.y)
}
/// `LengthSquared`
pub fn v2_length_squared(a: Vector2) -> F32 {
    a.x.mul(a.x).add(a.y.mul(a.y))
}
/// `Length => (float)Math.Sqrt(X * X + Y * Y)`; spec `Vector2.length`
pub fn v2_length(a: Vector2) -> F32 {
    a.x.mul(a.x).add(a.y.mul(a.y)).to_f64().sqrt().to_f32()
}
/// `PerpendicularRight`
pub fn v2_perpendicular_right(a: Vector2) -> Vector2 {
    Vector2 { x: a.y, y: a.x.neg() }
}
/// `PerpendicularLeft`
pub fn v2_perpendicular_left(a: Vector2) -> Vector2 {
    Vector2 { x: a.y.neg(), y: a.x }
}
/// `Normalized()`
pub fn v2_normalized(a: Vector2) -> Vector2 {
    let num = F32_ONE.div(v2_length(a));
    Vector2 { x: a.x.mul(num), y: a.y.mul(num) }
}
/// `Vector2.Distance` (`(float)Math.Sqrt`)
pub fn v2_distance(v1: Vector2, v2: Vector2) -> F32 {
    let dx = v2.x.sub(v1.x);
    let dy = v2.y.sub(v1.y);
    dx.mul(dx).add(dy.mul(dy)).to_f64().sqrt().to_f32()
}
/// `Vector2.DistanceSquared`
pub fn v2_distance_squared(v1: Vector2, v2: Vector2) -> F32 {
    let dx = v2.x.sub(v1.x);
    let dy = v2.y.sub(v1.y);
    dx.mul(dx).add(dy.mul(dy))
}
/// `Vector2.Dot`
pub fn v2_dot(a: Vector2, b: Vector2) -> F32 {
    a.x.mul(b.x).add(a.y.mul(b.y))
}
/// `Vector2.PerpDot`
pub fn v2_perp_dot(a: Vector2, b: Vector2) -> F32 {
    a.x.mul(b.y).sub(a.y.mul(b.x))
}
/// `Vector2.Lerp`
pub fn v2_lerp(a: Vector2, b: Vector2, blend: F32) -> Vector2 {
    Vector2 { x: blend.mul(b.x.sub(a.x)).add(a.x), y: blend.mul(b.y.sub(a.y)).add(a.y) }
}
fn clamp_c(x: F32, l: F32, h: F32) -> F32 {
    if x.lt(l) { l } else if h.lt(x) { h } else { x }
}
/// `Vector2.Clamp(vec, min, max)`
pub fn v2_clamp(v: Vector2, lo: Vector2, hi: Vector2) -> Vector2 {
    Vector2 { x: clamp_c(v.x, lo.x, hi.x), y: clamp_c(v.y, lo.y, hi.y) }
}
/// `Vector2.ComponentMin`
pub fn v2_component_min(a: Vector2, b: Vector2) -> Vector2 {
    Vector2 { x: if a.x.lt(b.x) { a.x } else { b.x }, y: if a.y.lt(b.y) { a.y } else { b.y } }
}
/// `Vector2.ComponentMax`
pub fn v2_component_max(a: Vector2, b: Vector2) -> Vector2 {
    Vector2 { x: if b.x.lt(a.x) { a.x } else { b.x }, y: if b.y.lt(a.y) { a.y } else { b.y } }
}

pub fn v3_add(a: Vector3, b: Vector3) -> Vector3 {
    Vector3 { x: a.x.add(b.x), y: a.y.add(b.y), z: a.z.add(b.z) }
}
pub fn v3_sub(a: Vector3, b: Vector3) -> Vector3 {
    Vector3 { x: a.x.sub(b.x), y: a.y.sub(b.y), z: a.z.sub(b.z) }
}
pub fn v3_scale(a: Vector3, s: F32) -> Vector3 {
    Vector3 { x: a.x.mul(s), y: a.y.mul(s), z: a.z.mul(s) }
}

pub const M3_IDENTITY: Matrix3 = Matrix3 {
    row0: Vector3 { x: F32_ONE, y: F32_ZERO, z: F32_ZERO },
    row1: Vector3 { x: F32_ZERO, y: F32_ONE, z: F32_ZERO },
    row2: Vector3 { x: F32_ZERO, y: F32_ZERO, z: F32_ONE },
};

fn m3_row(a: Vector3, r: Matrix3) -> Vector3 {
    Vector3 {
        x: a.x.mul(r.row0.x).add(a.y.mul(r.row1.x)).add(a.z.mul(r.row2.x)),
        y: a.x.mul(r.row0.y).add(a.y.mul(r.row1.y)).add(a.z.mul(r.row2.y)),
        z: a.x.mul(r.row0.z).add(a.y.mul(r.row1.z)).add(a.z.mul(r.row2.z)),
    }
}
/// `Matrix3.Mult(left, right)`; spec `Matrix3.mult`
pub fn m3_mult(l: Matrix3, r: Matrix3) -> Matrix3 {
    Matrix3 { row0: m3_row(l.row0, r), row1: m3_row(l.row1, r), row2: m3_row(l.row2, r) }
}

/// `MathHelper.Pi`
pub const PI_F: F32 = F32::from_bits(0x4049_0FDB);
pub const TWO_PI_F: F32 = F32::from_bits(0x40C9_0FDB);
pub const PI_OVER2_F: F32 = F32::from_bits(0x3FC9_0FDB);
pub const PI_OVER4_F: F32 = F32::from_bits(0x3F49_0FDB);
pub const DEG_TO_RAD_F: F32 = F32::from_bits(0x3C8E_FA35);
pub const RAD_TO_DEG_F: F32 = F32::from_bits(0x4265_2EE0);
pub const DEG_TO_RAD_D: F64 = F64::from_bits(0x3F91_DF46_A252_9D39);
pub const RAD_TO_DEG_D: F64 = F64::from_bits(0x404C_A5DC_1A63_C1F8);
const HALF_F: F32 = F32::from_bits(0x3F00_0000);
const THREE_HALVES_F: F32 = F32::from_bits(0x3FC0_0000);

/// `MathHelper.InverseSqrtFast(float)`; spec `MathHelper.inverseSqrtFast`
pub fn inverse_sqrt_fast(x: F32) -> F32 {
    // NaN first (same model value: the spec result is NaN too): `to_bits` is identified with the
    // spec only on non-NaN values (proofs/OsuProofs/Generated/FunsExternal.lean)
    if x.is_nan() {
        return x;
    }
    let xh = HALF_F.mul(x);
    let i: i32 = (0x5f375a86i32).wrapping_sub((x.to_bits() as i32) >> 1);
    let y = F32::from_bits(i as u32);
    y.mul(THREE_HALVES_F.sub(xh.mul(y).mul(y)))
}
/// `Vector2.LengthFast`
pub fn length_fast(a: Vector2) -> F32 {
    F32_ONE.div(inverse_sqrt_fast(a.x.mul(a.x).add(a.y.mul(a.y))))
}
/// `Vector2.NormalizeFast`
pub fn normalize_fast(a: Vector2) -> Vector2 {
    let num = inverse_sqrt_fast(a.x.mul(a.x).add(a.y.mul(a.y)));
    Vector2 { x: a.x.mul(num), y: a.y.mul(num) }
}
pub fn degrees_to_radians_f(d: F32) -> F32 {
    d.mul(DEG_TO_RAD_F)
}
pub fn radians_to_degrees_f(r: F32) -> F32 {
    r.mul(RAD_TO_DEG_F)
}
pub fn degrees_to_radians_d(d: F64) -> F64 {
    d.mul(DEG_TO_RAD_D)
}
pub fn radians_to_degrees_d(r: F64) -> F64 {
    r.mul(RAD_TO_DEG_D)
}
