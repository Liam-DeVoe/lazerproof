//! Sim basics: float32 vectors / 3x3 matrices (osuTK), `HitResult`, small .NET helpers.
//! Spec: `model/OsuModel/Sim/Basic.lean` (namespace `OsuModel.Sim`). Same op order as the spec.
use crate::float::{F32, F64};
use crate::sim::netx;

/// `Vec2` (`osuTK.Vector2`, float32)
#[derive(Clone, Copy)]
pub struct Vec2 {
    pub x: F32,
    pub y: F32,
}

pub const F32_0: F32 = F32::from_bits(0x0000_0000);
pub const F32_1: F32 = F32::from_bits(0x3F80_0000);
pub const F32_2: F32 = F32::from_bits(0x4000_0000);
/// `Vec2.zero`
pub const VEC2_ZERO: Vec2 = Vec2 { x: F32_0, y: F32_0 };
pub const VEC2_ONE: Vec2 = Vec2 { x: F32_1, y: F32_1 };

impl Vec2 {
    /// `Vec2.add`
    #[inline]
    pub fn add(self, b: Vec2) -> Vec2 {
        Vec2 { x: self.x.add(b.x), y: self.y.add(b.y) }
    }
    /// `Vec2.sub`
    #[inline]
    pub fn sub(self, b: Vec2) -> Vec2 {
        Vec2 { x: self.x.sub(b.x), y: self.y.sub(b.y) }
    }
    /// `Vec2.neg`
    #[inline]
    pub fn neg(self) -> Vec2 {
        Vec2 { x: self.x.neg(), y: self.y.neg() }
    }
    /// `Vec2.scale` (`Vector2 * float`)
    #[inline]
    pub fn scale(self, s: F32) -> Vec2 {
        Vec2 { x: self.x.mul(s), y: self.y.mul(s) }
    }
    /// `Vec2.mul` (componentwise)
    #[inline]
    pub fn mul(self, b: Vec2) -> Vec2 {
        Vec2 { x: self.x.mul(b.x), y: self.y.mul(b.y) }
    }
    /// `Vec2.cdiv` (`Vector2.Divide`, componentwise)
    #[inline]
    pub fn cdiv(self, b: Vec2) -> Vec2 {
        Vec2 { x: self.x.div(b.x), y: self.y.div(b.y) }
    }
    /// `Vec2.eq` (float `==` per component)
    #[inline]
    pub fn eq(self, b: Vec2) -> bool {
        self.x.eq(b.x) && self.y.eq(b.y)
    }
    /// `Vec2.lengthSquared`
    #[inline]
    pub fn length_squared(self) -> F32 {
        self.x.mul(self.x).add(self.y.mul(self.y))
    }
}

/// `Mat3` (`osuTK.Matrix3`, row-major)
#[derive(Clone, Copy)]
pub struct Mat3 {
    pub m11: F32,
    pub m12: F32,
    pub m13: F32,
    pub m21: F32,
    pub m22: F32,
    pub m23: F32,
    pub m31: F32,
    pub m32: F32,
    pub m33: F32,
}

pub const MAT3_IDENTITY: Mat3 = Mat3 {
    m11: F32_1, m12: F32_0, m13: F32_0, m21: F32_0, m22: F32_1, m23: F32_0, m31: F32_0, m32: F32_0, m33: F32_1,
};

/// `Mat3.translateFromLeft`
pub fn translate_from_left(m: Mat3, v: Vec2) -> Mat3 {
    Mat3 {
        m31: m.m31.add(m.m11.mul(v.x).add(m.m21.mul(v.y))),
        m32: m.m32.add(m.m12.mul(v.x).add(m.m22.mul(v.y))),
        m33: m.m33.add(m.m13.mul(v.x).add(m.m23.mul(v.y))),
        ..m
    }
}

/// `Mat3.translateFromRight`
pub fn translate_from_right(m: Mat3, v: Vec2) -> Mat3 {
    Mat3 {
        m11: m.m11.add(m.m13.mul(v.x)),
        m21: m.m21.add(m.m23.mul(v.x)),
        m31: m.m31.add(m.m33.mul(v.x)),
        m12: m.m12.add(m.m13.mul(v.y)),
        m22: m.m22.add(m.m23.mul(v.y)),
        m32: m.m32.add(m.m33.mul(v.y)),
        ..m
    }
}

/// `Mat3.scaleFromLeft`
pub fn scale_from_left(m: Mat3, v: Vec2) -> Mat3 {
    Mat3 {
        m11: m.m11.mul(v.x),
        m12: m.m12.mul(v.x),
        m13: m.m13.mul(v.x),
        m21: m.m21.mul(v.y),
        m22: m.m22.mul(v.y),
        m23: m.m23.mul(v.y),
        ..m
    }
}

/// `Mat3.scaleFromRight`
pub fn scale_from_right(m: Mat3, v: Vec2) -> Mat3 {
    Mat3 {
        m11: m.m11.mul(v.x),
        m21: m.m21.mul(v.x),
        m31: m.m31.mul(v.x),
        m12: m.m12.mul(v.y),
        m22: m.m22.mul(v.y),
        m32: m.m32.mul(v.y),
        ..m
    }
}

/// `Mat3.transform` (`Vector2Extensions.Transform`)
#[inline]
pub fn mat3_transform(m: &Mat3, p: Vec2) -> Vec2 {
    Vec2 {
        x: m.m11.mul(p.x).add(m.m21.mul(p.y)).add(m.m31),
        y: m.m12.mul(p.x).add(m.m22.mul(p.y)).add(m.m32),
    }
}

/// `DrawInfo`
#[derive(Clone, Copy)]
pub struct DrawInfo {
    pub matrix: Mat3,
    pub inverse: Mat3,
}

pub const DRAWINFO_DEFAULT: DrawInfo = DrawInfo { matrix: MAT3_ZERO, inverse: MAT3_ZERO };
/// Lean's `default : Mat3` (all fields `default : Float32` = 0)
pub const MAT3_ZERO: Mat3 = Mat3 {
    m11: F32_0, m12: F32_0, m13: F32_0, m21: F32_0, m22: F32_0, m23: F32_0, m31: F32_0, m32: F32_0, m33: F32_0,
};

/// `Precision.FLOAT_EPSILON = 1e-3f`
pub const FLOAT_EPSILON: F32 = F32::from_bits(0x3A83_126F);

/// the `fix` of `DrawInfo.applyTransform` (zero-scale clamping)
pub fn fix_scale(s: F32) -> F32 {
    if s.abs().lt(FLOAT_EPSILON) {
        if s.eq(F32_0) {
            FLOAT_EPSILON
        } else if s.lt(F32_0) {
            FLOAT_EPSILON.neg()
        } else {
            FLOAT_EPSILON
        }
    } else {
        s
    }
}

/// `DrawInfo.applyTransform` (rotation 0, shear 0)
pub fn apply_transform(di: &DrawInfo, translation: Vec2, scale: Vec2, origin: Vec2) -> DrawInfo {
    let mut m = di.matrix;
    let mut mi = di.inverse;
    if !translation.eq(VEC2_ZERO) {
        m = translate_from_left(m, translation);
        mi = translate_from_right(mi, translation.neg());
    }
    if !scale.eq(VEC2_ONE) {
        let s = Vec2 { x: fix_scale(scale.x), y: fix_scale(scale.y) };
        m = scale_from_left(m, s);
        mi = scale_from_right(mi, Vec2 { x: F32_1.div(s.x), y: F32_1.div(s.y) });
    }
    if !origin.eq(VEC2_ZERO) {
        m = translate_from_left(m, origin.neg());
        mi = translate_from_right(mi, origin);
    }
    DrawInfo { matrix: m, inverse: mi }
}

/// `DrawInfo.toScreen`
#[inline]
pub fn to_screen(di: &DrawInfo, p: Vec2) -> Vec2 {
    mat3_transform(&di.matrix, p)
}

/// `DrawInfo.toLocal`
#[inline]
pub fn to_local(di: &DrawInfo, p: Vec2) -> Vec2 {
    mat3_transform(&di.inverse, p)
}

/// `HitResult` (declaration order; `to_nat` gives the C# enum value)
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum HitResult {
    None,
    Miss,
    Meh,
    Ok_,
    Good,
    Great,
    Perfect,
    SmallTickMiss,
    SmallTickHit,
    LargeTickMiss,
    LargeTickHit,
    SmallBonus,
    LargeBonus,
    IgnoreMiss,
    IgnoreHit,
    ComboBreak,
    SliderTailHit,
    LegacyComboIncrease,
}

/// number of `HitResult` values (statistics arrays are indexed by `index`)
pub const HIT_RESULT_COUNT: usize = 18;

/// The ordinal (position in `HitResult.all`); statistics are stored by ordinal instead of the
/// spec's 100-entry `toNat` array (a bijection on the used indices).
pub fn hr_index(r: HitResult) -> usize {
    match r {
        HitResult::None => 0,
        HitResult::Miss => 1,
        HitResult::Meh => 2,
        HitResult::Ok_ => 3,
        HitResult::Good => 4,
        HitResult::Great => 5,
        HitResult::Perfect => 6,
        HitResult::SmallTickMiss => 7,
        HitResult::SmallTickHit => 8,
        HitResult::LargeTickMiss => 9,
        HitResult::LargeTickHit => 10,
        HitResult::SmallBonus => 11,
        HitResult::LargeBonus => 12,
        HitResult::IgnoreMiss => 13,
        HitResult::IgnoreHit => 14,
        HitResult::ComboBreak => 15,
        HitResult::SliderTailHit => 16,
        HitResult::LegacyComboIncrease => 17,
    }
}

/// `HitResult.toNat` (C# enum value)
pub fn hr_to_nat(r: HitResult) -> u32 {
    match r {
        HitResult::LegacyComboIncrease => 99,
        _ => hr_index(r) as u32,
    }
}

/// `HitResult.affectsCombo`
pub fn affects_combo(r: HitResult) -> bool {
    match r {
        HitResult::Miss
        | HitResult::Meh
        | HitResult::Ok_
        | HitResult::Good
        | HitResult::Great
        | HitResult::Perfect
        | HitResult::LargeTickHit
        | HitResult::LargeTickMiss
        | HitResult::LegacyComboIncrease
        | HitResult::ComboBreak
        | HitResult::SliderTailHit => true,
        _ => false,
    }
}

/// `HitResult.isHit`
pub fn is_hit(r: HitResult) -> bool {
    match r {
        HitResult::None
        | HitResult::IgnoreMiss
        | HitResult::Miss
        | HitResult::SmallTickMiss
        | HitResult::LargeTickMiss
        | HitResult::ComboBreak => false,
        _ => true,
    }
}

/// `HitResult.increasesCombo`
pub fn increases_combo(r: HitResult) -> bool {
    affects_combo(r) && is_hit(r)
}

/// `HitResult.breaksCombo`
pub fn breaks_combo(r: HitResult) -> bool {
    affects_combo(r) && !is_hit(r)
}

/// `HitResult.isBonus`
pub fn is_bonus(r: HitResult) -> bool {
    match r {
        HitResult::SmallBonus | HitResult::LargeBonus => true,
        _ => false,
    }
}

/// `HitResult.isTick`
pub fn is_tick(r: HitResult) -> bool {
    match r {
        HitResult::LargeTickHit
        | HitResult::LargeTickMiss
        | HitResult::SmallTickHit
        | HitResult::SmallTickMiss
        | HitResult::SliderTailHit => true,
        _ => false,
    }
}

/// `HitResult.isScorable`
pub fn is_scorable(r: HitResult) -> bool {
    match r {
        HitResult::LegacyComboIncrease | HitResult::ComboBreak | HitResult::SliderTailHit => true,
        _ => {
            let n = hr_to_nat(r);
            1 <= n && n < 13
        }
    }
}

/// `HitResult.affectsAccuracy`
pub fn affects_accuracy(r: HitResult) -> bool {
    match r {
        HitResult::LegacyComboIncrease | HitResult::ComboBreak => false,
        _ => is_scorable(r) && !is_bonus(r),
    }
}

/// `1e-7` (default `acceptableDifference` of `almostEqualsD`)
pub const ALMOST_EQUALS_EPS: F64 = F64::from_bits(0x3E7A_D7F2_9ABC_AF48);

/// `almostEqualsD` (`Precision.AlmostEquals(double, double, 1e-7)`)
pub fn almost_equals_d(a: F64, b: F64) -> bool {
    a.sub(b).abs().le(ALMOST_EQUALS_EPS)
}

/// `fmod1` (C# `x % 1`)
pub fn fmod1(x: F64) -> F64 {
    if x.abs().lt(netx::F64_INTEGER_BOUNDARY) {
        let r = x.sub(x.trunc());
        if r.eq(netx::F64_ZERO) { netx::f64_copy_sign(netx::F64_ZERO, x) } else { r }
    } else if x.is_nan() || x.abs().eq(netx::F64_POS_INF) {
        netx::F64_NAN
    } else {
        netx::f64_copy_sign(netx::F64_ZERO, x)
    }
}

// ---- M7 (Lean commit 7cffd29): rotation ----

/// `rotL` (`MatrixExtensions.RotateFromLeft`, cosf/sinf)
pub fn rot_l(m: Mat3, rad: F32) -> Mat3 {
    let c = rad.cos();
    let s = rad.sin();
    Mat3 {
        m11: m.m11.mul(c).add(m.m21.mul(s)),
        m12: m.m12.mul(c).add(m.m22.mul(s)),
        m13: m.m13.mul(c).add(m.m23.mul(s)),
        m21: m.m21.mul(c).sub(m.m11.mul(s)),
        m22: m.m22.mul(c).sub(m.m12.mul(s)),
        m23: m.m23.mul(c).sub(m.m13.mul(s)),
        ..m
    }
}

/// `rotR` (`MatrixExtensions.RotateFromRight`)
pub fn rot_r(m: Mat3, rad: F32) -> Mat3 {
    let c = rad.cos();
    let s = rad.sin();
    Mat3 {
        m11: m.m11.mul(c).sub(m.m12.mul(s)),
        m12: m.m12.mul(c).add(m.m11.mul(s)),
        m21: m.m21.mul(c).sub(m.m22.mul(s)),
        m22: m.m22.mul(c).add(m.m21.mul(s)),
        m31: m.m31.mul(c).sub(m.m32.mul(s)),
        m32: m.m32.mul(c).add(m.m31.mul(s)),
        ..m
    }
}

/// `DrawInfo.applyTransformR` (with rotation)
pub fn apply_transform_r(di: &DrawInfo, translation: Vec2, scale: Vec2, rotation: F32, origin: Vec2) -> DrawInfo {
    if rotation.eq(F32_0) {
        apply_transform(di, translation, scale, origin)
    } else {
        let mut m = di.matrix;
        let mut mi = di.inverse;
        if !translation.eq(VEC2_ZERO) {
            m = translate_from_left(m, translation);
            mi = translate_from_right(mi, translation.neg());
        }
        let rad = crate::net::sysmisc::f32_degrees_to_radians(rotation);
        m = rot_l(m, rad);
        mi = rot_r(mi, rad.neg());
        if !scale.eq(VEC2_ONE) {
            let s = Vec2 { x: fix_scale(scale.x), y: fix_scale(scale.y) };
            m = scale_from_left(m, s);
            mi = scale_from_right(mi, Vec2 { x: F32_1.div(s.x), y: F32_1.div(s.y) });
        }
        if !origin.eq(VEC2_ZERO) {
            m = translate_from_left(m, origin.neg());
            mi = translate_from_right(mi, origin);
        }
        DrawInfo { matrix: m, inverse: mi }
    }
}
