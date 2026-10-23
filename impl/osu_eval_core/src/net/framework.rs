//! Port of `OsuModel/Net/Framework.lean` (osu-framework 2026.921.1): `Precision`,
//! `DefaultEasingFunction`, `Interpolation`, `Vector2Extensions`, `MatrixExtensions`,
//! `DrawInfo.ApplyTransform`, and the `BindableNumber<T>` setter state machine.
use super::basic::NetExn;
use super::decimal;
use super::mathops::{f32_max, f32_min, f64_round};
use super::osutk::{
    m3_mult, v2_add, v2_divide, v2_eq, v2_neg, v2_scale, v2_sub, v3_add, v3_scale, v3_sub, Matrix3, Vector2, Vector3,
    V2_ONE, V2_ZERO,
};
use super::sysmisc::f32_degrees_to_radians;
use super::{max as f64_max, min as f64_min};
use crate::float::{F32, F64};

// ---------------------------------------------------------------------------------- Precision

/// `FLOAT_EPSILON = 1e-3f`
pub const FLOAT_EPSILON: F32 = F32::from_bits(0x3A83_126F);
/// `DOUBLE_EPSILON = 1e-7`
pub const DOUBLE_EPSILON: F64 = F64::from_bits(0x3E7A_D7F2_9ABC_AF48);

/// `Precision.DefinitelyBigger(float)`; spec `Precision.definitelyBiggerF`
pub fn definitely_bigger_f(a: F32, b: F32, e: F32) -> bool {
    b.lt(a.sub(e))
}
pub fn definitely_bigger_d(a: F64, b: F64, e: F64) -> bool {
    b.lt(a.sub(e))
}
/// `Precision.AlmostBigger`
pub fn almost_bigger_f(a: F32, b: F32, e: F32) -> bool {
    b.sub(e).lt(a)
}
pub fn almost_bigger_d(a: F64, b: F64, e: F64) -> bool {
    b.sub(e).lt(a)
}
/// `Precision.AlmostEquals`
pub fn almost_equals_f(a: F32, b: F32, e: F32) -> bool {
    a.sub(b).abs().le(e)
}
pub fn almost_equals_d(a: F64, b: F64, e: F64) -> bool {
    a.sub(b).abs().le(e)
}
pub fn almost_equals_v(a: Vector2, b: Vector2, e: F32) -> bool {
    almost_equals_f(a.x, b.x, e) && almost_equals_f(a.y, b.y, e)
}

// ---------------------------------------------------------------------------------- Easing

/// `osu.Framework.Graphics.Easing` (enum order = numeric value); spec `Framework.Easing`
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Easing {
    None,
    Out,
    In,
    InQuad,
    OutQuad,
    InOutQuad,
    InCubic,
    OutCubic,
    InOutCubic,
    InQuart,
    OutQuart,
    InOutQuart,
    InQuint,
    OutQuint,
    InOutQuint,
    InSine,
    OutSine,
    InOutSine,
    InExpo,
    OutExpo,
    InOutExpo,
    InCirc,
    OutCirc,
    InOutCirc,
    InElastic,
    OutElastic,
    OutElasticHalf,
    OutElasticQuarter,
    InOutElastic,
    InBack,
    OutBack,
    InOutBack,
    InBounce,
    OutBounce,
    InOutBounce,
    OutPow10,
}

/// numeric value -> enum (out of range = `None`); spec `Easing.ofIndex`
pub fn easing_of_index(n: u64) -> Easing {
    match n {
        1 => Easing::Out,
        2 => Easing::In,
        3 => Easing::InQuad,
        4 => Easing::OutQuad,
        5 => Easing::InOutQuad,
        6 => Easing::InCubic,
        7 => Easing::OutCubic,
        8 => Easing::InOutCubic,
        9 => Easing::InQuart,
        10 => Easing::OutQuart,
        11 => Easing::InOutQuart,
        12 => Easing::InQuint,
        13 => Easing::OutQuint,
        14 => Easing::InOutQuint,
        15 => Easing::InSine,
        16 => Easing::OutSine,
        17 => Easing::InOutSine,
        18 => Easing::InExpo,
        19 => Easing::OutExpo,
        20 => Easing::InOutExpo,
        21 => Easing::InCirc,
        22 => Easing::OutCirc,
        23 => Easing::InOutCirc,
        24 => Easing::InElastic,
        25 => Easing::OutElastic,
        26 => Easing::OutElasticHalf,
        27 => Easing::OutElasticQuarter,
        28 => Easing::InOutElastic,
        29 => Easing::InBack,
        30 => Easing::OutBack,
        31 => Easing::InOutBack,
        32 => Easing::InBounce,
        33 => Easing::OutBounce,
        34 => Easing::InOutBounce,
        35 => Easing::OutPow10,
        _ => Easing::None,
    }
}

/// `EasingConst.pi`
pub const PI: F64 = F64::from_bits(0x4009_21FB_5444_2D18);
const K1: F64 = F64::from_bits(0x3FF0_0000_0000_0000) /* 1 */;
const K2: F64 = F64::from_bits(0x4000_0000_0000_0000) /* 2 */;
const K4: F64 = F64::from_bits(0x4010_0000_0000_0000) /* 4 */;
const K8: F64 = F64::from_bits(0x4020_0000_0000_0000) /* 8 */;
const K10: F64 = F64::from_bits(0x4024_0000_0000_0000) /* 10 */;
const K16: F64 = F64::from_bits(0x4030_0000_0000_0000) /* 16 */;
const K20: F64 = F64::from_bits(0x4034_0000_0000_0000) /* 20 */;
const K11: F64 = F64::from_bits(0x4026_0000_0000_0000) /* 11 */;
const K0_3: F64 = F64::from_bits(0x3FD3_3333_3333_3333) /* 0.3 */;
const K1_5: F64 = F64::from_bits(0x3FF8_0000_0000_0000) /* 1.5 */;
const K1_525: F64 = F64::from_bits(0x3FF8_6666_6666_6666) /* 1.525 */;
const K2_5: F64 = F64::from_bits(0x4004_0000_0000_0000) /* 2.5 */;
const K2_25: F64 = F64::from_bits(0x4002_0000_0000_0000) /* 2.25 */;
const K2_625: F64 = F64::from_bits(0x4005_0000_0000_0000) /* 2.625 */;
const K2_75: F64 = F64::from_bits(0x4006_0000_0000_0000) /* 2.75 */;
const BACK_CONST: F64 = F64::from_bits(0x3FFB_39AB_F338_7161) /* 1.70158 */;
const C7_5625: F64 = F64::from_bits(0x401E_4000_0000_0000) /* 7.5625 */;
const C0_75: F64 = F64::from_bits(0x3FE8_0000_0000_0000) /* 0.75 */;
const C0_9375: F64 = F64::from_bits(0x3FEE_0000_0000_0000) /* 0.9375 */;
const C0_984375: F64 = F64::from_bits(0x3FEF_8000_0000_0000) /* 0.984375 */;
const HALF: F64 = F64::from_bits(0x3FE0_0000_0000_0000) /* 0.5 */;
const QUARTER: F64 = F64::from_bits(0x3FD0_0000_0000_0000) /* 0.25 */;

/// `elastic_const = 2 * pi / 0.3`
pub fn elastic_const() -> F64 {
    K2.mul(PI).div(K0_3)
}
/// `elastic_const2 = 0.3 / 4`
pub fn elastic_const2() -> F64 {
    K0_3.div(K4)
}
pub fn back_const2() -> F64 {
    BACK_CONST.mul(K1_525)
}
pub fn back_const_p1() -> F64 {
    BACK_CONST.add(K1)
}
pub fn back_const2_p1() -> F64 {
    back_const2().add(K1)
}
pub fn bounce_const() -> F64 {
    K1.div(K2_75)
}
pub fn b2() -> F64 {
    K2.mul(bounce_const())
}
pub fn b25() -> F64 {
    K2_5.mul(bounce_const())
}
pub fn b15() -> F64 {
    K1_5.mul(bounce_const())
}
pub fn b225() -> F64 {
    K2_25.mul(bounce_const())
}
pub fn b2625() -> F64 {
    K2_625.mul(bounce_const())
}
pub fn one_m_ec2() -> F64 {
    K1.sub(elastic_const2())
}
pub fn ec2_15() -> F64 {
    elastic_const2().mul(K1_5)
}
pub fn one_m_ec2_15() -> F64 {
    K1.sub(ec2_15())
}
/// `static readonly expo_offset = Math.Pow(2, -10)`
pub fn expo_offset() -> F64 {
    K2.pow(K10.neg())
}
pub fn elastic_offset_full() -> F64 {
    K2.pow(K11.neg())
}
pub fn elastic_offset_half() -> F64 {
    K2.pow(K10.neg()).mul(HALF.sub(elastic_const2()).mul(elastic_const()).sin())
}
pub fn elastic_offset_quarter() -> F64 {
    K2.pow(K10.neg()).mul(QUARTER.sub(elastic_const2()).mul(elastic_const()).sin())
}
pub fn in_out_elastic_offset() -> F64 {
    K2.pow(K10.neg()).mul(K1.sub(elastic_const2().mul(K1_5)).mul(elastic_const()).div(K1_5).sin())
}

/// `DefaultEasingFunction.OutBounce` branch; spec `Framework.outBounce`
pub fn out_bounce(time: F64) -> F64 {
    if time.lt(bounce_const()) {
        C7_5625.mul(time).mul(time)
    } else if time.lt(b2()) {
        let t = time.sub(b15());
        C7_5625.mul(t).mul(t).add(C0_75)
    } else if time.lt(b25()) {
        let t = time.sub(b225());
        C7_5625.mul(t).mul(t).add(C0_9375)
    } else {
        let t = time.sub(b2625());
        C7_5625.mul(t).mul(t).add(C0_984375)
    }
}

/// `DefaultEasingFunction.ApplyEasing(time)`; spec `Framework.applyEasing`
pub fn apply_easing(e: Easing, time: F64) -> F64 {
    match e {
        Easing::None => time,
        Easing::In | Easing::InQuad => time.mul(time),
        Easing::Out | Easing::OutQuad => time.mul(K2.sub(time)),
        Easing::InOutQuad => {
            if time.lt(HALF) {
                time.mul(time).mul(K2)
            } else {
                let t = time.sub(K1);
                t.mul(t).mul(K2.neg()).add(K1)
            }
        }
        Easing::InCubic => time.mul(time).mul(time),
        Easing::OutCubic => {
            let t = time.sub(K1);
            t.mul(t).mul(t).add(K1)
        }
        Easing::InOutCubic => {
            if time.lt(HALF) {
                time.mul(time).mul(time).mul(K4)
            } else {
                let t = time.sub(K1);
                t.mul(t).mul(t).mul(K4).add(K1)
            }
        }
        Easing::InQuart => time.mul(time).mul(time).mul(time),
        Easing::OutQuart => {
            let t = time.sub(K1);
            K1.sub(t.mul(t).mul(t).mul(t))
        }
        Easing::InOutQuart => {
            if time.lt(HALF) {
                time.mul(time).mul(time).mul(time).mul(K8)
            } else {
                let t = time.sub(K1);
                t.mul(t).mul(t).mul(t).mul(K8.neg()).add(K1)
            }
        }
        Easing::InQuint => time.mul(time).mul(time).mul(time).mul(time),
        Easing::OutQuint => {
            let t = time.sub(K1);
            t.mul(t).mul(t).mul(t).mul(t).add(K1)
        }
        Easing::InOutQuint => {
            if time.lt(HALF) {
                time.mul(time).mul(time).mul(time).mul(time).mul(K16)
            } else {
                let t = time.sub(K1);
                t.mul(t).mul(t).mul(t).mul(t).mul(K16).add(K1)
            }
        }
        Easing::InSine => K1.sub(time.mul(PI).mul(HALF).cos()),
        Easing::OutSine => time.mul(PI).mul(HALF).sin(),
        Easing::InOutSine => HALF.sub(HALF.mul(PI.mul(time).cos())),
        Easing::InExpo => K2.pow(K10.mul(time.sub(K1))).add(expo_offset().mul(time.sub(K1))),
        Easing::OutExpo => K2.pow(K10.neg().mul(time)).neg().add(K1).add(expo_offset().mul(time)),
        Easing::InOutExpo => {
            if time.lt(HALF) {
                HALF.mul(K2.pow(K20.mul(time).sub(K10)).add(expo_offset().mul(K2.mul(time).sub(K1))))
            } else {
                K1.sub(HALF.mul(
                    K2.pow(K20.neg().mul(time).add(K10)).add(expo_offset().mul(K2.neg().mul(time).add(K1))),
                ))
            }
        }
        Easing::InCirc => K1.sub(K1.sub(time.mul(time)).sqrt()),
        Easing::OutCirc => {
            let t = time.sub(K1);
            K1.sub(t.mul(t)).sqrt()
        }
        Easing::InOutCirc => {
            let t = time.mul(K2);
            if t.lt(K1) {
                HALF.sub(HALF.mul(K1.sub(t.mul(t)).sqrt()))
            } else {
                let t2 = t.sub(K2);
                HALF.mul(K1.sub(t2.mul(t2)).sqrt()).add(HALF)
            }
        }
        Easing::InElastic => K2
            .pow(K10.neg().add(K10.mul(time)))
            .neg()
            .mul(one_m_ec2().sub(time).mul(elastic_const()).sin())
            .add(elastic_offset_full().mul(K1.sub(time))),
        Easing::OutElastic => K2
            .pow(K10.neg().mul(time))
            .mul(time.sub(elastic_const2()).mul(elastic_const()).sin())
            .add(K1)
            .sub(elastic_offset_full().mul(time)),
        Easing::OutElasticHalf => K2
            .pow(K10.neg().mul(time))
            .mul(HALF.mul(time).sub(elastic_const2()).mul(elastic_const()).sin())
            .add(K1)
            .sub(elastic_offset_half().mul(time)),
        Easing::OutElasticQuarter => K2
            .pow(K10.neg().mul(time))
            .mul(QUARTER.mul(time).sub(elastic_const2()).mul(elastic_const()).sin())
            .add(K1)
            .sub(elastic_offset_quarter().mul(time)),
        Easing::InOutElastic => {
            let t = time.mul(K2);
            if t.lt(K1) {
                HALF.neg().mul(
                    K2.pow(K10.neg().add(K10.mul(t)))
                        .mul(one_m_ec2_15().sub(t).mul(elastic_const()).div(K1_5).sin())
                        .sub(in_out_elastic_offset().mul(K1.sub(t))),
                )
            } else {
                let t2 = t.sub(K1);
                HALF.mul(
                    K2.pow(K10.neg().mul(t2))
                        .mul(t2.sub(ec2_15()).mul(elastic_const()).div(K1_5).sin())
                        .sub(in_out_elastic_offset().mul(t2)),
                )
                .add(K1)
            }
        }
        Easing::InBack => time.mul(time).mul(back_const_p1().mul(time).sub(BACK_CONST)),
        Easing::OutBack => {
            let t = time.sub(K1);
            t.mul(t).mul(back_const_p1().mul(t).add(BACK_CONST)).add(K1)
        }
        Easing::InOutBack => {
            let t = time.mul(K2);
            if t.lt(K1) {
                HALF.mul(t).mul(t).mul(back_const2_p1().mul(t).sub(back_const2()))
            } else {
                let t2 = t.sub(K2);
                HALF.mul(t2.mul(t2).mul(back_const2_p1().mul(t2).add(back_const2())).add(K2))
            }
        }
        Easing::InBounce => {
            let t = K1.sub(time);
            if t.lt(bounce_const()) {
                K1.sub(C7_5625.mul(t).mul(t))
            } else if t.lt(b2()) {
                let t2 = t.sub(b15());
                K1.sub(C7_5625.mul(t2).mul(t2).add(C0_75))
            } else if t.lt(b25()) {
                let t2 = t.sub(b225());
                K1.sub(C7_5625.mul(t2).mul(t2).add(C0_9375))
            } else {
                let t2 = t.sub(b2625());
                K1.sub(C7_5625.mul(t2).mul(t2).add(C0_984375))
            }
        }
        Easing::OutBounce => out_bounce(time),
        Easing::InOutBounce => {
            if time.lt(HALF) {
                HALF.sub(HALF.mul(out_bounce(K1.sub(time.mul(K2)))))
            } else {
                out_bounce(time.sub(HALF).mul(K2)).mul(HALF).add(HALF)
            }
        }
        Easing::OutPow10 => {
            let t = time.sub(K1);
            t.mul(t.pow(K10)).add(K1)
        }
    }
}

// ---------------------------------------------------------------------------------- Interpolation

/// `Interpolation.Lerp`; spec `Interpolation.lerp`
pub fn lerp(start: F64, fin: F64, amount: F64) -> F64 {
    start.add(fin.sub(start).mul(amount))
}
/// `Interpolation.Damp`; spec `Interpolation.damp`
pub fn damp(start: F64, fin: F64, base: F64, exponent: F64) -> Result<F64, NetExn> {
    if base.lt(F64::from_bits(0)) || K1.lt(base) {
        Err(NetExn::ArgumentOutOfRange)
    } else {
        Ok(lerp(start, fin, K1.sub(base.pow(exponent))))
    }
}
/// `Interpolation.DampContinuously`; spec `Interpolation.dampContinuously`
pub fn damp_continuously(current: F64, target: F64, half_time: F64, elapsed: F64) -> F64 {
    lerp(current, target, K1.sub(HALF.pow(elapsed.div(half_time))))
}
/// `Interpolation.ValueAt(double ...)`; spec `Interpolation.valueAtD`
pub fn value_at_d(time: F64, val1: F64, val2: F64, start_time: F64, end_time: F64, e: Easing) -> F64 {
    if val1.eq(val2) {
        val1
    } else {
        let current = time.sub(start_time);
        let duration = end_time.sub(start_time);
        if current.eq(F64::from_bits(0)) {
            val1
        } else if duration.eq(F64::from_bits(0)) {
            val2
        } else {
            let t = apply_easing(e, current.div(duration));
            val1.add(t.mul(val2.sub(val1)))
        }
    }
}
/// `ValueAt(float ...)`; spec `Interpolation.valueAtF`
pub fn value_at_f(time: F64, val1: F32, val2: F32, start_time: F64, end_time: F64, e: Easing) -> F32 {
    value_at_d(time, val1.to_f64(), val2.to_f64(), start_time, end_time, e).to_f32()
}
/// `ValueAt(int ...)`; spec `Interpolation.valueAtI`
pub fn value_at_i(time: F64, val1: i32, val2: i32, start_time: F64, end_time: F64, e: Easing) -> i32 {
    f64_round(value_at_d(time, F64::from_i64(val1 as i64), F64::from_i64(val2 as i64), start_time, end_time, e)).to_i32_sat()
}
/// `ValueAt(Vector2 ...)`; spec `Interpolation.valueAtV`
pub fn value_at_v(time: F64, val1: Vector2, val2: Vector2, start_time: F64, end_time: F64, e: Easing) -> Vector2 {
    let current = time.sub(start_time).to_f32();
    let duration = end_time.sub(start_time).to_f32();
    let z = F32::from_bits(0);
    if duration.eq(z) || current.eq(z) {
        val1
    } else {
        let t = apply_easing(e, current.div(duration).to_f64()).to_f32();
        v2_add(val1, v2_scale(v2_sub(val2, val1), t))
    }
}

// ---------------------------------------------------------------------------------- Vector2Extensions

/// `Vector2Extensions.Transform(pos, mat)`; spec `Vector2Extensions.transform`
pub fn transform(p: Vector2, m: Matrix3) -> Vector2 {
    Vector2 {
        x: m.row0.x.mul(p.x).add(m.row1.x.mul(p.y)).add(m.row2.x),
        y: m.row0.y.mul(p.x).add(m.row1.y.mul(p.y)).add(m.row2.y),
    }
}
/// `Vector2Extensions.Distance` (`MathF.Sqrt`); spec `Vector2Extensions.distance`
pub fn distance(v1: Vector2, v2: Vector2) -> F32 {
    let dx = v2.x.sub(v1.x);
    let dy = v2.y.sub(v1.y);
    dx.mul(dx).add(dy.mul(dy)).sqrt()
}
pub fn distance_squared(v1: Vector2, v2: Vector2) -> F32 {
    let dx = v2.x.sub(v1.x);
    let dy = v2.y.sub(v1.y);
    dx.mul(dx).add(dy.mul(dy))
}

// ---------------------------------------------------------------------------------- MatrixExtensions

/// spec `MatrixExtensions.translateFromLeft`
pub fn translate_from_left(m: Matrix3, v: Vector2) -> Matrix3 {
    Matrix3 { row0: m.row0, row1: m.row1, row2: v3_add(m.row2, v3_add(v3_scale(m.row0, v.x), v3_scale(m.row1, v.y))) }
}
fn tfr_row(a: Vector3, v: Vector2) -> Vector3 {
    Vector3 { x: a.x.add(a.z.mul(v.x)), y: a.y.add(a.z.mul(v.y)), z: a.z }
}
/// spec `MatrixExtensions.translateFromRight`
pub fn translate_from_right(m: Matrix3, v: Vector2) -> Matrix3 {
    Matrix3 { row0: tfr_row(m.row0, v), row1: tfr_row(m.row1, v), row2: tfr_row(m.row2, v) }
}
/// spec `MatrixExtensions.rotateFromLeft`
pub fn rotate_from_left(m: Matrix3, radians: F32) -> Matrix3 {
    let c = radians.cos();
    let s = radians.sin();
    Matrix3 {
        row0: v3_add(v3_scale(m.row0, c), v3_scale(m.row1, s)),
        row1: v3_sub(v3_scale(m.row1, c), v3_scale(m.row0, s)),
        row2: m.row2,
    }
}
fn rfr_row(a: Vector3, c: F32, s: F32) -> Vector3 {
    Vector3 { x: a.x.mul(c).sub(a.y.mul(s)), y: a.y.mul(c).add(a.x.mul(s)), z: a.z }
}
/// spec `MatrixExtensions.rotateFromRight`
pub fn rotate_from_right(m: Matrix3, radians: F32) -> Matrix3 {
    let c = radians.cos();
    let s = radians.sin();
    Matrix3 { row0: rfr_row(m.row0, c, s), row1: rfr_row(m.row1, c, s), row2: rfr_row(m.row2, c, s) }
}
/// spec `MatrixExtensions.scaleFromLeft`
pub fn scale_from_left(m: Matrix3, v: Vector2) -> Matrix3 {
    Matrix3 { row0: v3_scale(m.row0, v.x), row1: v3_scale(m.row1, v.y), row2: m.row2 }
}
fn sfr_row(a: Vector3, v: Vector2) -> Vector3 {
    Vector3 { x: a.x.mul(v.x), y: a.y.mul(v.y), z: a.z }
}
/// spec `MatrixExtensions.scaleFromRight`
pub fn scale_from_right(m: Matrix3, v: Vector2) -> Matrix3 {
    Matrix3 { row0: sfr_row(m.row0, v), row1: sfr_row(m.row1, v), row2: sfr_row(m.row2, v) }
}
/// spec `MatrixExtensions.shearFromLeft`
pub fn shear_from_left(m: Matrix3, v: Vector2) -> Matrix3 {
    Matrix3 {
        row0: v3_add(v3_add(m.row0, v3_scale(m.row1, v.y)), v3_scale(v3_scale(m.row0, v.x), v.y)),
        row1: v3_add(m.row1, v3_scale(m.row0, v.x)),
        row2: m.row2,
    }
}
fn shfr_row(a: Vector3, v: Vector2, xy: F32) -> Vector3 {
    Vector3 { x: a.x.add(a.y.mul(v.x)), y: a.y.add(a.x.mul(v.y).add(a.y.mul(xy))), z: a.z }
}
/// spec `MatrixExtensions.shearFromRight`
pub fn shear_from_right(m: Matrix3, v: Vector2) -> Matrix3 {
    let xy = v.x.mul(v.y);
    Matrix3 { row0: shfr_row(m.row0, v, xy), row1: shfr_row(m.row1, v, xy), row2: shfr_row(m.row2, v, xy) }
}

/// unused but kept for parity with osuTK `Matrix3.Mult` users
pub fn mult(l: Matrix3, r: Matrix3) -> Matrix3 {
    m3_mult(l, r)
}

// ---------------------------------------------------------------------------------- DrawInfo

/// spec `Framework.DrawInfo`
#[derive(Clone, Copy)]
pub struct DrawInfo {
    pub matrix: Matrix3,
    pub matrix_inverse: Matrix3,
}

/// spec `DrawInfo.clampScaleComp`
pub fn clamp_scale_comp(s: F32) -> F32 {
    if s.abs().lt(FLOAT_EPSILON) {
        let one = F32::from_bits(0x3F80_0000);
        let sg = if s.eq(F32::from_bits(0)) { one } else if s.lt(F32::from_bits(0)) { one.neg() } else { one };
        sg.mul(FLOAT_EPSILON)
    } else {
        s
    }
}

/// `DrawInfo.ApplyTransform`; spec `DrawInfo.applyTransform`
pub fn apply_transform(di: DrawInfo, translation: Vector2, scale: Vector2, rotation: F32, shear: Vector2, origin: Vector2) -> DrawInfo {
    let mut m = di.matrix;
    let mut mi = di.matrix_inverse;
    if !v2_eq(translation, V2_ZERO) {
        m = translate_from_left(m, translation);
        mi = translate_from_right(mi, v2_neg(translation));
    }
    if !rotation.eq(F32::from_bits(0)) {
        let radians = f32_degrees_to_radians(rotation);
        m = rotate_from_left(m, radians);
        mi = rotate_from_right(mi, radians.neg());
    }
    if !v2_eq(shear, V2_ZERO) {
        m = shear_from_left(m, v2_neg(shear));
        mi = shear_from_right(mi, shear);
    }
    if !v2_eq(scale, V2_ONE) {
        let s = Vector2 { x: clamp_scale_comp(scale.x), y: clamp_scale_comp(scale.y) };
        m = scale_from_left(m, s);
        mi = scale_from_right(mi, v2_divide(V2_ONE, s));
    }
    if !v2_eq(origin, V2_ZERO) {
        m = translate_from_left(m, v2_neg(origin));
        mi = translate_from_right(mi, origin);
    }
    DrawInfo { matrix: m, matrix_inverse: mi }
}

// ---------------------------------------------------------------------------------- Bindable

/// `double.Clamp` (IEEE min/max); spec `Bindable.clampD`
pub fn clamp_d(v: F64, lo: F64, hi: F64) -> Result<F64, NetExn> {
    if hi.lt(lo) { Err(NetExn::Argument) } else { Ok(f64_min(f64_max(v, lo), hi)) }
}
/// spec `Bindable.clampF`
pub fn clamp_f(v: F32, lo: F32, hi: F32) -> Result<F32, NetExn> {
    if hi.lt(lo) { Err(NetExn::Argument) } else { Ok(f32_min(f32_max(v, lo), hi)) }
}
/// `double.Equals`; spec `Bindable.equalsD`
pub fn equals_d(a: F64, b: F64) -> bool {
    a.eq(b) || (a.is_nan() && b.is_nan())
}
/// spec `Bindable.equalsF`
pub fn equals_f(a: F32, b: F32) -> bool {
    a.eq(b) || (a.is_nan() && b.is_nan())
}

/// `BindableNumber` decimal snapping; spec `Bindable.snapD`
pub fn snap_d(lo: F64, hi: F64, p: F64, v: F64) -> Result<F64, NetExn> {
    let dp = tri!(decimal::create_truncating_f64(p));
    if decimal::is_positive(dp) {
        let c = tri!(clamp_d(v, lo, hi));
        let a = tri!(decimal::create_truncating_f64(c));
        let q = tri!(decimal::div(a, dp));
        let r = tri!(decimal::mul(decimal::round(q), dp));
        Ok(decimal::to_f64(r))
    } else {
        Ok(v)
    }
}
/// spec `Bindable.snapF`
pub fn snap_f(lo: F32, hi: F32, p: F32, v: F32) -> Result<F32, NetExn> {
    let dp = tri!(decimal::create_truncating_f32(p));
    if decimal::is_positive(dp) {
        let c = tri!(clamp_f(v, lo, hi));
        let a = tri!(decimal::create_truncating_f32(c));
        let q = tri!(decimal::div(a, dp));
        let r = tri!(decimal::mul(decimal::round(q), dp));
        Ok(decimal::to_f32(r))
    } else {
        Ok(v)
    }
}
/// spec `Bindable.setDouble`
pub fn set_double(lo: F64, hi: F64, p: F64, v: F64) -> Result<F64, NetExn> {
    let s = tri!(snap_d(lo, hi, p, v));
    clamp_d(s, lo, hi)
}
/// spec `Bindable.setFloat`
pub fn set_float(lo: F32, hi: F32, p: F32, v: F32) -> Result<F32, NetExn> {
    let s = tri!(snap_f(lo, hi, p, v));
    clamp_f(s, lo, hi)
}

/// `BindableDouble` state; spec `Bindable.BD`
#[derive(Clone, Copy)]
pub struct BD {
    pub value: F64,
    pub min_v: F64,
    pub max_v: F64,
    pub prec: F64,
}

/// spec `BD.store`
pub fn bd_store(s: BD, v: F64) -> BD {
    if equals_d(s.value, v) { s } else { BD { value: v, min_v: s.min_v, max_v: s.max_v, prec: s.prec } }
}
/// spec `BD.rcSet`
pub fn bd_rc_set(s: BD, v: F64) -> Result<BD, NetExn> {
    let c = tri!(clamp_d(v, s.min_v, s.max_v));
    Ok(bd_store(s, c))
}
/// spec `BD.setValue`
pub fn bd_set_value(s: BD, v: F64) -> Result<BD, NetExn> {
    let x = tri!(snap_d(s.min_v, s.max_v, s.prec, v));
    bd_rc_set(s, x)
}
pub const DBL_MAX: F64 = F64::from_bits(0x7FEF_FFFF_FFFF_FFFF);
pub const DBL_EPS: F64 = F64::from_bits(1);
/// `new BindableDouble(d)`; spec `BD.create`
pub fn bd_create(d: F64) -> Result<BD, NetExn> {
    let s = BD { value: d, min_v: DBL_MAX.neg(), max_v: DBL_MAX, prec: DBL_EPS };
    let s1 = tri!(bd_rc_set(s, d));
    bd_set_value(s1, s1.value)
}
/// spec `BD.setMin`
pub fn bd_set_min(s: BD, m: F64) -> Result<BD, NetExn> {
    if equals_d(m, s.min_v) { Ok(s) } else { bd_rc_set(BD { value: s.value, min_v: m, max_v: s.max_v, prec: s.prec }, s.value) }
}
/// spec `BD.setMax`
pub fn bd_set_max(s: BD, m: F64) -> Result<BD, NetExn> {
    if equals_d(m, s.max_v) { Ok(s) } else { bd_rc_set(BD { value: s.value, min_v: s.min_v, max_v: m, prec: s.prec }, s.value) }
}
/// spec `BD.setPrecision`
pub fn bd_set_precision(s: BD, p: F64) -> Result<BD, NetExn> {
    if p.eq(s.prec) {
        Ok(s)
    } else if p.le(F64::from_bits(0)) {
        Err(NetExn::ArgumentOutOfRange)
    } else {
        bd_set_value(BD { value: s.value, min_v: s.min_v, max_v: s.max_v, prec: p }, s.value)
    }
}
/// `new BindableDouble(d) { MinValue, MaxValue, Precision }`; spec `BD.init`
pub fn bd_init(d: F64, lo: F64, hi: F64, p: F64) -> Result<BD, NetExn> {
    let s = tri!(bd_create(d));
    let s = tri!(bd_set_min(s, lo));
    let s = tri!(bd_set_max(s, hi));
    bd_set_precision(s, p)
}

/// `BindableFloat` state; spec `Bindable.BF`
#[derive(Clone, Copy)]
pub struct BF {
    pub value: F32,
    pub min_v: F32,
    pub max_v: F32,
    pub prec: F32,
}
pub fn bf_store(s: BF, v: F32) -> BF {
    if equals_f(s.value, v) { s } else { BF { value: v, min_v: s.min_v, max_v: s.max_v, prec: s.prec } }
}
pub fn bf_rc_set(s: BF, v: F32) -> Result<BF, NetExn> {
    let c = tri!(clamp_f(v, s.min_v, s.max_v));
    Ok(bf_store(s, c))
}
pub fn bf_set_value(s: BF, v: F32) -> Result<BF, NetExn> {
    let x = tri!(snap_f(s.min_v, s.max_v, s.prec, v));
    bf_rc_set(s, x)
}
pub const FLT_MAX: F32 = F32::from_bits(0x7F7F_FFFF);
pub const FLT_EPS: F32 = F32::from_bits(1);
pub fn bf_create(d: F32) -> Result<BF, NetExn> {
    let s = BF { value: d, min_v: FLT_MAX.neg(), max_v: FLT_MAX, prec: FLT_EPS };
    let s1 = tri!(bf_rc_set(s, d));
    bf_set_value(s1, s1.value)
}
pub fn bf_set_min(s: BF, m: F32) -> Result<BF, NetExn> {
    if equals_f(m, s.min_v) { Ok(s) } else { bf_rc_set(BF { value: s.value, min_v: m, max_v: s.max_v, prec: s.prec }, s.value) }
}
pub fn bf_set_max(s: BF, m: F32) -> Result<BF, NetExn> {
    if equals_f(m, s.max_v) { Ok(s) } else { bf_rc_set(BF { value: s.value, min_v: s.min_v, max_v: m, prec: s.prec }, s.value) }
}
pub fn bf_set_precision(s: BF, p: F32) -> Result<BF, NetExn> {
    if p.eq(s.prec) {
        Ok(s)
    } else if p.le(F32::from_bits(0)) {
        Err(NetExn::ArgumentOutOfRange)
    } else {
        bf_set_value(BF { value: s.value, min_v: s.min_v, max_v: s.max_v, prec: p }, s.value)
    }
}
pub fn bf_init(d: F32, lo: F32, hi: F32, p: F32) -> Result<BF, NetExn> {
    let s = tri!(bf_create(d));
    let s = tri!(bf_set_min(s, lo));
    let s = tri!(bf_set_max(s, hi));
    bf_set_precision(s, p)
}
