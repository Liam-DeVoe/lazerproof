//! Port of `OsuModel/Beatmap/SliderPath.lean` (`osu.Game.Rulesets.Objects.SliderPath`): the
//! cache contents (`calculatedPath`, `cumulativeLength`, `calculatedLength`) computed eagerly.
use super::dotnet::{binary_search_f64, nat_sub};
use super::path_approximator as pa;
use super::types::{PathControlPoint, PathType};
use super::vector2::{self as v, almost_equals_f64, Vec2};
use crate::float::F64;
use alloc::vec::Vec;

/// The persistent part of a `SliderPath`; spec `SliderPathSpec`
#[derive(Clone)]
pub struct SliderPathSpec {
    pub control_points: Vec<PathControlPoint>,
    pub expected_distance: Option<F64>,
    pub optimise_catmull: bool,
}

/// The cached state after `ensureValid()`; spec `SliderPath`
#[derive(Clone)]
pub struct SliderPath {
    pub spec: SliderPathSpec,
    pub calculated_path: Vec<Vec2>,
    pub cumulative_length: Vec<F64>,
    pub calculated_length: F64,
    /// spec `fuelOut`: a B-spline subdivision of this (or an earlier) path of the slider ran out of fuel (D72)
    pub fuel_out: bool,
}

const D0: F64 = F64::from_bits(0);
const D1: F64 = F64::from_bits(0x3FF0_0000_0000_0000);
const D6: F64 = F64::from_bits(0x4018_0000_0000_0000);

/// The Catmull "6px" optimisation; returns (path, optimisedLength increase); spec `optimiseCatmullPath`
pub fn optimise_catmull_path(sub_path: &[Vec2]) -> (Vec<Vec2>, F64) {
    let mut optimised_path: Vec<Vec2> = Vec::new();
    let mut optimised_length = D0;
    let mut last_start: Option<Vec2> = None;
    let mut length_removed_since_start = D0;
    let mut i = 0;
    while i < sub_path.len() {
        match last_start {
            None => {
                optimised_path.push(sub_path[i]);
                last_start = Some(sub_path[i]);
            }
            Some(ls) => {
                let dist_from_start = v::distance(ls, sub_path[i]).to_f64();
                length_removed_since_start = length_removed_since_start.add(v::distance(sub_path[i - 1], sub_path[i]).to_f64());
                if D6.lt(dist_from_start) || (i + 1) % 100 == 0 || i == sub_path.len() - 1 {
                    optimised_path.push(sub_path[i]);
                    optimised_length = optimised_length.add(length_removed_since_start.sub(dist_from_start));
                    last_start = None;
                    length_removed_since_start = D0;
                }
            }
        }
        i = i + 1;
    }
    (optimised_path, optimised_length)
}

fn sub_bspline(sub: &[Vec2], degree: Option<i32>) -> (Vec<Vec2>, F64, bool) {
    let d: usize = match degree {
        Some(d) => {
            if d < 0 { 0 } else { d as usize }
        }
        None => sub.len(),
    };
    let (p, fo) = pa::b_spline_to_piecewise_linear(sub, d);
    (p, D0, fo)
}

/// `calculateSubPath(subControlPoints, type)`; spec `SliderPath.calculateSubPath`
pub fn calculate_sub_path(sub: &[Vec2], ptype: PathType, optimise_catmull: bool) -> (Vec<Vec2>, F64, bool) {
    match ptype {
        PathType::Linear => (pa::linear_to_piecewise_linear(sub), D0, false),
        PathType::PerfectCurve => {
            if sub.len() != 3 {
                sub_bspline(sub, None)
            } else {
                let pr = pa::circular_arc_properties(sub);
                if !pr.is_valid {
                    sub_bspline(sub, None)
                } else {
                    let sub_points = pa::arc_point_count(&pr);
                    if sub_points >= 1000 {
                        sub_bspline(sub, None)
                    } else {
                        let sub_path = pa::circular_arc_to_piecewise_linear(sub);
                        if sub_path.len() == 0 { sub_bspline(sub, None) } else { (sub_path, D0, false) }
                    }
                }
            }
        }
        PathType::Catmull => {
            let sub_path = pa::catmull_to_piecewise_linear(sub);
            if !optimise_catmull {
                (sub_path, D0, false)
            } else {
                let (p, ol) = optimise_catmull_path(&sub_path);
                (p, ol, false)
            }
        }
        PathType::BSpline(d) => sub_bspline(sub, d),
    }
}

/// One segment `cps[start..=i]` of `calculatePath()`: returns `path` with its sub-path appended and
/// the `optimisedLength` contribution (loop body of spec `SliderPath.calculatePath`); `None` for 0/1-vertex
/// segments, for which the spec adds nothing (D27: not `+ 0`, so the refinement needs no `x + 0 = x` float fact);
/// the last component is the sub-path's B-spline fuel flag (`false` for 0/1-vertex segments).
pub fn calculate_path_segment(spec: &SliderPathSpec, start: usize, i: usize, path0: Vec<Vec2>) -> (Vec<Vec2>, Option<F64>, bool) {
    let mut path = path0;
    let mut segment_vertices: Vec<Vec2> = Vec::new();
    let mut k = start;
    while k < i + 1 {
        segment_vertices.push(spec.control_points[k].position);
        k = k + 1;
    }
    let segment_type = match spec.control_points[start].ptype {
        Some(t) => t,
        None => PathType::Linear,
    };
    if segment_vertices.len() == 1 {
        path.push(segment_vertices[0]);
        (path, None, false)
    } else if segment_vertices.len() > 1 {
        let (sub_path, ol, fo) = calculate_sub_path(&segment_vertices, segment_type, spec.optimise_catmull);
        let skip_first = path.len() > 0 && sub_path.len() > 0 && v::eq(path[path.len() - 1], sub_path[0]);
        let mut j = if skip_first { 1 } else { 0 };
        while j < sub_path.len() {
            path.push(sub_path[j]);
            j = j + 1;
        }
        (path, Some(ol), fo)
    } else {
        (path, None, false)
    }
}

/// first `i >= from` that ends a segment in `calculatePath()` (`Type != null` or the last
/// control point), `n` if none
pub fn next_segment_end(spec: &SliderPathSpec, from: usize) -> usize {
    let n = spec.control_points.len();
    let mut i = from;
    let mut found = false;
    while !found && i < n {
        if spec.control_points[i].ptype.is_none() && i < n - 1 {
            i = i + 1;
        } else {
            found = true;
        }
    }
    i
}

/// `calculatePath()`: the piecewise-linear path, `optimisedLength` and the B-spline fuel flag; spec
/// `SliderPath.calculatePath` (the spec's `for i` loop with `continue` on non-segment-ends is iterated over the
/// segment ends)
pub fn calculate_path(spec: &SliderPathSpec) -> (Vec<Vec2>, F64, bool) {
    let n = spec.control_points.len();
    let mut path: Vec<Vec2> = Vec::new();
    let mut optimised_length = D0;
    let mut fuel_out = false;
    if n == 0 {
        return (path, optimised_length, fuel_out);
    }
    let mut start = 0;
    let mut i = next_segment_end(spec, 0);
    while i < n {
        let (p2, ol, fo) = calculate_path_segment(spec, start, i, path);
        path = p2;
        fuel_out = fuel_out || fo;
        // the spec adds `ol` only for segments with > 1 vertex (`None` otherwise; D27)
        match ol {
            Some(x) => optimised_length = optimised_length.add(x),
            None => {}
        }
        start = i;
        i = next_segment_end(spec, i + 1);
    }
    (path, optimised_length, fuel_out)
}

/// `calculateLength()` given the output of `calculatePath`; spec `SliderPath.calculateLength`
pub fn calculate_length(spec: SliderPathSpec, path0: Vec<Vec2>, optimised_length: F64) -> SliderPath {
    let mut path = path0;
    let mut calculated_length = optimised_length;
    let mut cumulative_length: Vec<F64> = Vec::with_capacity(path.len());
    cumulative_length.push(D0);
    let mut i = 0;
    while i < nat_sub(path.len(), 1) {
        let diff = v::sub(path[i + 1], path[i]);
        calculated_length = calculated_length.add(v::length(diff).to_f64());
        cumulative_length.push(calculated_length);
        i = i + 1;
    }
    match spec.expected_distance {
        None => SliderPath { spec, calculated_path: path, cumulative_length, calculated_length, fuel_out: false },
        Some(expected_distance) => {
            if calculated_length.eq(expected_distance) {
                return SliderPath { spec, calculated_path: path, cumulative_length, calculated_length, fuel_out: false };
            }
            let n = path.len();
            if n >= 2 && v::eq(path[n - 1], path[n - 2]) && calculated_length.lt(expected_distance) {
                cumulative_length.push(calculated_length);
                return SliderPath { spec, calculated_path: path, cumulative_length, calculated_length, fuel_out: false };
            }
            cumulative_length.pop();
            let mut path_end_index: i64 = (path.len() as i64) - 1;
            if expected_distance.lt(calculated_length) {
                let mut k = 0;
                let lim = path.len() + 1;
                while k < lim {
                    let cl = cumulative_length.len();
                    if cl > 0 && expected_distance.le(cumulative_length[cl - 1]) {
                        cumulative_length.pop();
                        path.pop();
                        path_end_index = path_end_index - 1;
                    }
                    k = k + 1;
                }
            }
            if path_end_index <= 0 {
                cumulative_length.push(D0);
                return SliderPath { spec, calculated_path: path, cumulative_length, calculated_length, fuel_out: false };
            }
            let e = path_end_index as usize;
            let dir = v::normalized(v::sub(path[e], path[e - 1]));
            let last = cumulative_length[cumulative_length.len() - 1];
            path[e] = v::add(path[e - 1], v::scale(dir, expected_distance.sub(last).to_f32()));
            cumulative_length.push(expected_distance);
            SliderPath { spec, calculated_path: path, cumulative_length, calculated_length, fuel_out: false }
        }
    }
}

/// `ensureValid()`; spec `SliderPath.compute`
pub fn compute(spec: SliderPathSpec) -> SliderPath {
    let (p, ol, fo) = calculate_path(&spec);
    let mut sp = calculate_length(spec, p, ol);
    sp.fuel_out = fo;
    sp
}

/// `new SliderPath(controlPoints, expectedDistance)`; spec `SliderPath.ofControlPoints`
pub fn of_control_points(cps: Vec<PathControlPoint>, expected: Option<F64>, optimise_catmull: bool) -> SliderPath {
    compute(SliderPathSpec { control_points: cps, expected_distance: expected, optimise_catmull })
}

/// `Distance`; spec `SliderPath.distance`
pub fn distance(p: &SliderPath) -> F64 {
    let n = p.cumulative_length.len();
    if n == 0 { D0 } else { p.cumulative_length[n - 1] }
}

/// `CalculatedDistance`; spec `SliderPath.calculatedDistance`
pub fn calculated_distance(p: &SliderPath) -> F64 {
    p.calculated_length
}

/// Lean `a[i]!` on a `F64` array (default `0` out of bounds)
pub fn get_f64(a: &[F64], i: usize) -> F64 {
    if i < a.len() { a[i] } else { D0 }
}

/// `indexOfDistance(d)`; spec `SliderPath.indexOfDistance`
pub fn index_of_distance(p: &SliderPath, d: F64) -> i64 {
    let i = binary_search_f64(&p.cumulative_length, d);
    if i < 0 { -i - 1 } else { i }
}

/// `progressToDistance(progress)`; spec `SliderPath.progressToDistance`
pub fn progress_to_distance(p: &SliderPath, progress: F64) -> F64 {
    let c = if progress.lt(D0) { D0 } else if D1.lt(progress) { D1 } else { progress };
    c.mul(distance(p))
}

/// `interpolateVertices(i, d)`; spec `SliderPath.interpolateVertices`
pub fn interpolate_vertices(p: &SliderPath, i: i64, d: F64) -> Vec2 {
    let cp = &p.calculated_path;
    if cp.len() == 0 {
        v::ZERO
    } else if i <= 0 {
        cp[0]
    } else if i >= cp.len() as i64 {
        cp[cp.len() - 1]
    } else {
        let iu = i as usize;
        let p0 = cp[iu - 1];
        let p1 = cp[iu];
        let d0 = get_f64(&p.cumulative_length, iu - 1);
        let d1 = get_f64(&p.cumulative_length, iu);
        if almost_equals_f64(d0, d1) {
            p0
        } else {
            let w = d.sub(d0).div(d1.sub(d0));
            v::add(p0, v::scale(v::sub(p1, p0), w.to_f32()))
        }
    }
}

/// `PositionAt(progress)`; spec `SliderPath.positionAt`
pub fn position_at(p: &SliderPath, progress: F64) -> Vec2 {
    let d = progress_to_distance(p, progress);
    interpolate_vertices(p, index_of_distance(p, d), d)
}
