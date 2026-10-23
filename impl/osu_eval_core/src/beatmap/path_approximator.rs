//! Port of `OsuModel/Beatmap/PathApproximator.lean` (osu-framework `PathApproximator` and
//! `CircularArcProperties`; float32 geometry, double arc angles with glibc atan2/cos/sin/acos).
use super::dotnet::nat_sub;
use super::vector2::{self as v, almost_equals_f32, Vec2};
use crate::float::{F32, F64};
use alloc::vec::Vec;

/// `BEZIER_TOLERANCE = 0.25f`
pub const BEZIER_TOLERANCE: F32 = F32::from_bits(0x3E80_0000);
/// `catmull_detail = 50`
pub const CATMULL_DETAIL: usize = 50;
/// `circular_arc_tolerance = 0.1f`
pub const CIRCULAR_ARC_TOLERANCE: F32 = F32::from_bits(0x3DCC_CCCD);
const K0_25: F32 = F32::from_bits(0x3E80_0000);
const K0_5: F32 = F32::from_bits(0x3F00_0000);
const K1: F32 = F32::from_bits(0x3F80_0000);
const K2: F32 = F32::from_bits(0x4000_0000);
const K3: F32 = F32::from_bits(0x4040_0000);
const K4: F32 = F32::from_bits(0x4080_0000);
const K5: F32 = F32::from_bits(0x40A0_0000);
const F32_ZERO: F32 = F32::from_bits(0);

/// `BEZIER_TOLERANCE * BEZIER_TOLERANCE * 4`; spec `kFlat`
pub fn k_flat() -> F32 {
    BEZIER_TOLERANCE.mul(BEZIER_TOLERANCE).mul(K4)
}
/// `(float)catmull_detail`; spec `kCatmullDetail`
pub fn k_catmull_detail() -> F32 {
    F32::from_i64(CATMULL_DETAIL as i64)
}

fn replicate_zero(n: usize) -> Vec<Vec2> {
    let mut out: Vec<Vec2> = Vec::with_capacity(n);
    let mut i = 0;
    while i < n {
        out.push(v::ZERO);
        i = i + 1;
    }
    out
}

fn extract(a: &[Vec2], lo: usize, hi: usize) -> Vec<Vec2> {
    let mut out: Vec<Vec2> = Vec::new();
    let mut i = lo;
    while i < hi && i < a.len() {
        out.push(a[i]);
        i = i + 1;
    }
    out
}

/// `bSplineToBezierInternal(controlPoints, ref degree)`; spec `bSplineToBezierInternal`
pub fn b_spline_to_bezier_internal(control_points: &[Vec2], degree0: usize) -> (Vec<Vec<Vec2>>, usize) {
    let pc = nat_sub(control_points.len(), 1);
    let degree = if degree0 < pc { degree0 } else { pc };
    let point_count = pc;
    let mut points: Vec<Vec2> = extract(control_points, 0, control_points.len());
    if degree == point_count {
        let mut r: Vec<Vec<Vec2>> = Vec::new();
        r.push(points);
        return (r, degree);
    }
    let mut result: Vec<Vec<Vec2>> = Vec::new();
    let mut i = 0;
    while i < nat_sub(point_count, degree) {
        let mut sub_bezier = replicate_zero(degree + 1);
        sub_bezier[0] = points[i];
        let mut j = 0;
        while j < nat_sub(degree, 1) {
            sub_bezier[j + 1] = points[i + 1];
            let mut k = 1;
            while k < nat_sub(degree, j) {
                let lim = nat_sub(nat_sub(point_count, degree), i);
                let l = if k < lim { k } else { lim };
                let lf = F32::from_i64(l as i64);
                points[i + k] = v::div(v::add(v::scale(points[i + k], lf), points[i + k + 1]), F32::from_i64((l + 1) as i64));
                k = k + 1;
            }
            j = j + 1;
        }
        sub_bezier[degree] = points[i + 1];
        result.push(sub_bezier);
        i = i + 1;
    }
    result.push(extract(&points, nat_sub(point_count, degree), points.len()));
    (result, degree)
}

/// `bezierIsFlatEnough`; spec `bezierIsFlatEnough`
pub fn bezier_is_flat_enough(cp: &[Vec2]) -> bool {
    let kf = k_flat();
    let mut i = 1;
    let mut flat = true;
    while flat && i < nat_sub(cp.len(), 1) {
        let d = v::add(v::sub(cp[i - 1], v::scale(cp[i], K2)), cp[i + 1]);
        if kf.lt(v::length_squared(d)) {
            flat = false;
        }
        i = i + 1;
    }
    flat
}

/// `bezierSubdivide(controlPoints, l, r, subdivisionBuffer, count)`: returns `(l, r)`; spec `bezierSubdivide`
pub fn bezier_subdivide(cp: &[Vec2], count: usize) -> (Vec<Vec2>, Vec<Vec2>) {
    let mut midpoints = extract(cp, 0, count);
    let mut l = replicate_zero(count);
    let mut r = replicate_zero(count);
    let mut i = 0;
    while i < count {
        l[i] = midpoints[0];
        r[count - i - 1] = midpoints[count - i - 1];
        let mut j = 0;
        while j < count - i - 1 {
            midpoints[j] = v::div(v::add(midpoints[j], midpoints[j + 1]), K2);
            j = j + 1;
        }
        i = i + 1;
    }
    (l, r)
}

/// `bezierApproximate(controlPoints, output, ..., count)`: appends to `output`; spec `bezierApproximate`
pub fn bezier_approximate(cp: &[Vec2], output: &mut Vec<Vec2>, count: usize) {
    let (l0, r) = bezier_subdivide(cp, count);
    let mut l = l0;
    let mut z = 0;
    while z < nat_sub(count, 1) {
        l.push(v::ZERO);
        z = z + 1;
    }
    let mut i = 0;
    while i < nat_sub(count, 1) {
        l[count + i] = r[i + 1];
        i = i + 1;
    }
    output.push(cp[0]);
    let mut k = 1;
    while k < nat_sub(count, 1) {
        let index = 2 * k;
        let p = v::scale(v::add(v::add(l[index - 1], v::scale(l[index], K2)), l[index + 1]), K0_25);
        output.push(p);
        k = k + 1;
    }
}

/// `BSplineToPiecewiseLinear(controlPoints, degree)`; spec `bSplineToPiecewiseLinear`
pub fn b_spline_to_piecewise_linear(control_points: &[Vec2], degree0: usize) -> (Vec<Vec2>, bool) {
    if control_points.len() < 2 {
        let mut out: Vec<Vec2> = Vec::new();
        if control_points.len() == 1 {
            out.push(control_points[0]);
        }
        return (out, false);
    }
    let pc = control_points.len() - 1;
    let degree1 = if degree0 < pc { degree0 } else { pc };
    let point_count = pc;
    let (segs, degree) = b_spline_to_bezier_internal(control_points, degree1);
    // stack: top = last element (segments reversed)
    let mut to_flatten: Vec<Vec<Vec2>> = Vec::with_capacity(segs.len());
    let mut s = segs.len();
    while s > 0 {
        s = s - 1;
        to_flatten.push(segs[s].clone());
    }
    let mut output: Vec<Vec2> = Vec::new();
    let mut fuel: u64 = 0;
    while to_flatten.len() > 0 && fuel < 100000000 {
        let parent = match to_flatten.pop() {
            Some(p) => p,
            None => Vec::new(),
        };
        if bezier_is_flat_enough(&parent) {
            bezier_approximate(&parent, &mut output, degree + 1);
        } else {
            let (left_child, right_child) = bezier_subdivide(&parent, degree + 1);
            to_flatten.push(right_child);
            to_flatten.push(extract(&left_child, 0, degree + 1));
        }
        fuel = fuel + 1;
    }
    output.push(control_points[point_count]);
    // `true`: the subdivision fuel ran out (spec flag, D72)
    let fuel_out = to_flatten.len() != 0;
    (output, fuel_out)
}

/// `BezierToPiecewiseLinear` = `BSplineToPiecewiseLinear(cp, max(1, n - 1))`; spec `bezierToPiecewiseLinear`
/// (the fuel flag is dropped, as in the spec: only the unreachable invalid-arc branch of
/// `circular_arc_to_piecewise_linear` calls it)
pub fn bezier_to_piecewise_linear(control_points: &[Vec2]) -> Vec<Vec2> {
    let d = nat_sub(control_points.len(), 1);
    let (out, _fuel_out) = b_spline_to_piecewise_linear(control_points, if 1 < d { d } else { 1 });
    out
}

fn catmull_coord(v1: F32, v2: F32, v3: F32, v4: F32, t: F32, t2: F32, t3: F32) -> F32 {
    let a = K2.mul(v2);
    let b = v1.neg().add(v3).mul(t);
    let c = K2.mul(v1).sub(K5.mul(v2)).add(K4.mul(v3)).sub(v4).mul(t2);
    let d = v1.neg().add(K3.mul(v2)).sub(K3.mul(v3)).add(v4).mul(t3);
    K0_5.mul(a.add(b).add(c).add(d))
}

/// `catmullFindPoint`; spec `catmullFindPoint`
pub fn catmull_find_point(v1: Vec2, v2: Vec2, v3: Vec2, v4: Vec2, t: F32) -> Vec2 {
    let t2 = t.mul(t);
    let t3 = t.mul(t2);
    Vec2 { x: catmull_coord(v1.x, v2.x, v3.x, v4.x, t, t2, t3), y: catmull_coord(v1.y, v2.y, v3.y, v4.y, t, t2, t3) }
}

/// `CatmullToPiecewiseLinear`; spec `catmullToPiecewiseLinear`
pub fn catmull_to_piecewise_linear(cp: &[Vec2]) -> Vec<Vec2> {
    let mut result: Vec<Vec2> = Vec::new();
    let kd = k_catmull_detail();
    let n = cp.len();
    let mut i = 0;
    while i < nat_sub(n, 1) {
        let v1 = if i > 0 { cp[i - 1] } else { cp[i] };
        let v2 = cp[i];
        let v3 = if i < n - 1 { cp[i + 1] } else { v::sub(v::add(v2, v2), v1) };
        let v4 = if i + 2 < n { cp[i + 2] } else { v::sub(v::add(v3, v3), v2) };
        let mut c = 0;
        while c < CATMULL_DETAIL {
            result.push(catmull_find_point(v1, v2, v3, v4, F32::from_i64(c as i64).div(kd)));
            result.push(catmull_find_point(v1, v2, v3, v4, F32::from_i64((c + 1) as i64).div(kd)));
            c = c + 1;
        }
        i = i + 1;
    }
    result
}

/// `LinearToPiecewiseLinear`; spec `linearToPiecewiseLinear`
pub fn linear_to_piecewise_linear(cp: &[Vec2]) -> Vec<Vec2> {
    extract(cp, 0, cp.len())
}

/// `Math.PI`
pub const PI: F64 = F64::from_bits(0x4009_21FB_5444_2D18);
const D1: F64 = F64::from_bits(0x3FF0_0000_0000_0000);
const D2: F64 = F64::from_bits(0x4000_0000_0000_0000);
const D0: F64 = F64::from_bits(0);

/// `CircularArcProperties`; spec `CircularArcProperties`
#[derive(Clone, Copy)]
pub struct CircularArcProperties {
    pub is_valid: bool,
    pub theta_start: F64,
    pub theta_range: F64,
    pub direction: F64,
    pub radius: F32,
    pub centre: Vec2,
}

pub const ARC_INVALID: CircularArcProperties =
    CircularArcProperties { is_valid: false, theta_start: D0, theta_range: D0, direction: D0, radius: F32_ZERO, centre: v::ZERO };

/// `new CircularArcProperties(controlPoints)`; spec `circularArcProperties`
pub fn circular_arc_properties(cp: &[Vec2]) -> CircularArcProperties {
    let a = cp[0];
    let b = cp[1];
    let c = cp[2];
    if almost_equals_f32(F32_ZERO, b.y.sub(a.y).mul(c.x.sub(a.x)).sub(b.x.sub(a.x).mul(c.y.sub(a.y)))) {
        return ARC_INVALID;
    }
    let bc = v::sub(b, c);
    let ca = v::sub(c, a);
    let ab = v::sub(a, b);
    let d = K2.mul(a.x.mul(bc.y).add(b.x.mul(ca.y)).add(c.x.mul(ab.y)));
    let a_sq = v::length_squared(a);
    let b_sq = v::length_squared(b);
    let c_sq = v::length_squared(c);
    let cb = v::sub(c, b);
    let ac = v::sub(a, c);
    let ba = v::sub(b, a);
    let centre = v::div(
        Vec2 {
            x: a_sq.mul(bc.y).add(b_sq.mul(ca.y)).add(c_sq.mul(ab.y)),
            y: a_sq.mul(cb.x).add(b_sq.mul(ac.x)).add(c_sq.mul(ba.x)),
        },
        d,
    );
    let d_a = v::sub(a, centre);
    let d_c = v::sub(c, centre);
    let radius = v::length(d_a);
    let theta_start = d_a.y.to_f64().atan2(d_a.x.to_f64());
    let mut theta_end = d_c.y.to_f64().atan2(d_c.x.to_f64());
    let mut k = 0;
    while k < 4 {
        if theta_end.lt(theta_start) {
            theta_end = theta_end.add(PI.mul(D2));
        }
        k = k + 1;
    }
    let mut direction = D1;
    let mut theta_range = theta_end.sub(theta_start);
    let ortho0 = v::sub(c, a);
    let ortho_a_to_c = Vec2 { x: ortho0.y, y: ortho0.x.neg() };
    if v::dot(ortho_a_to_c, v::sub(b, a)).lt(F32_ZERO) {
        direction = direction.neg();
        theta_range = PI.mul(D2).sub(theta_range);
    }
    CircularArcProperties { is_valid: true, theta_start, theta_range, direction, radius, centre }
}

/// number of arc points; spec `arcPointCount`
pub fn arc_point_count(pr: &CircularArcProperties) -> i32 {
    if K2.mul(pr.radius).le(CIRCULAR_ARC_TOLERANCE) {
        2
    } else {
        let inner = K1.sub(CIRCULAR_ARC_TOLERANCE.div(pr.radius));
        let n = pr.theta_range.div(D2.mul(inner.to_f64().acos())).ceil().to_i32_sat();
        if n < 2 { 2 } else { n }
    }
}

/// `CircularArcToPiecewiseLinear`; spec `circularArcToPiecewiseLinear`
pub fn circular_arc_to_piecewise_linear(cp: &[Vec2]) -> Vec<Vec2> {
    let pr = circular_arc_properties(cp);
    if !pr.is_valid {
        return bezier_to_piecewise_linear(cp);
    }
    let amount_points = arc_point_count(&pr);
    let mut output: Vec<Vec2> = Vec::new();
    let n: usize = if amount_points < 0 { 0 } else { amount_points as usize };
    let mut i = 0;
    while i < n {
        let fract = F64::from_i64(i as i64).div(F64::from_i64((amount_points as i64) - 1));
        let theta = pr.theta_start.add(pr.direction.mul(fract).mul(pr.theta_range));
        let o = v::scale(Vec2 { x: theta.cos().to_f32(), y: theta.sin().to_f32() }, pr.radius);
        output.push(v::add(pr.centre, o));
        i = i + 1;
    }
    output
}
