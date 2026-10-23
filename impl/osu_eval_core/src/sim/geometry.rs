//! Screen-space geometry of the hit tests (float32, bit-exact).
//! Spec: `model/OsuModel/Sim/Geometry.lean`.
use crate::float::{F32, F64};
use crate::sim::basic::*;
use crate::sim::err::SimErr;
use crate::sim::netx::{self, f32_max, f32_min};
use crate::sim::playable::{HObj, SliderData};

/// `ChainNode` (one ancestor of the HitObjectContainer); `is_pac` = `typeName == "OsuPlayfieldAdjustmentContainer"`
#[derive(Clone, Copy)]
pub struct ChainNode {
    pub is_pac: bool,
    pub pos: Vec2,
    pub scale: Vec2,
    pub rot: F32,
    pub origin: Vec2,
}

/// `Env`
#[derive(Clone)]
pub struct Env {
    pub hoc_first: DrawInfo,
    pub hoc: DrawInfo,
    pub argon_path_radius: F32,
    pub hoc_size: Vec2,
    pub chain_first: alloc::vec::Vec<ChainNode>,
    pub chain: alloc::vec::Vec<ChainNode>,
}

/// `composeChain nodes pacRotScale`
pub fn compose_chain(nodes: &[ChainNode], pac_rot_scale: Option<(F32, Vec2)>) -> DrawInfo {
    let mut di = DrawInfo { matrix: MAT3_IDENTITY, inverse: MAT3_IDENTITY };
    let mut i: usize = 0;
    while i < nodes.len() {
        let n = nodes[i];
        let (rot, sc) = match pac_rot_scale {
            Some((r, s)) => {
                if n.is_pac { (r, s) } else { (n.rot, n.scale) }
            }
            None => (n.rot, n.scale),
        };
        di = apply_transform_r(&di, n.pos, sc, rot, n.origin);
        i += 1;
    }
    di
}

/// `objectRadius` (`OsuHitObject.OBJECT_RADIUS`)
pub const OBJECT_RADIUS: F32 = F32::from_bits(0x4280_0000); // 64
pub const F32_128: F32 = F32::from_bits(0x4300_0000);
/// `objectDimensions` = (128, 128)
pub const OBJECT_DIMENSIONS: Vec2 = Vec2 { x: F32_128, y: F32_128 };
pub const F32_0_5: F32 = F32::from_bits(0x3F00_0000);
pub const VEC2_HALF: Vec2 = Vec2 { x: F32_0_5, y: F32_0_5 };

/// `centreOf`
pub fn centre_of(size: Vec2) -> Vec2 {
    Vec2 { x: size.x.div(F32_2), y: size.y.div(F32_2) }
}

/// `childDrawInfo`
pub fn child_draw_info(parent: &DrawInfo, draw_position: Vec2, anchor_position: Vec2, scale: Vec2, origin: Vec2) -> DrawInfo {
    let pos = draw_position.add(anchor_position).add(VEC2_ZERO);
    apply_transform(parent, pos, scale, origin.sub(VEC2_ZERO))
}

/// `receptorFromDho`
pub fn receptor_from_dho(parent: &DrawInfo, dho_pos: Vec2, dho_anchor: Vec2, scale: F32) -> DrawInfo {
    let dho = child_draw_info(parent, dho_pos, dho_anchor, VEC2_ONE, centre_of(OBJECT_DIMENSIONS));
    let sc_size = Vec2 { x: F32_1.mul(OBJECT_DIMENSIONS.x), y: F32_1.mul(OBJECT_DIMENSIONS.y) };
    let sc = child_draw_info(&dho, VEC2_ZERO, VEC2_HALF.mul(OBJECT_DIMENSIONS), Vec2 { x: scale, y: scale }, centre_of(sc_size));
    child_draw_info(&sc, VEC2_ZERO, VEC2_HALF.mul(sc_size), VEC2_ONE, centre_of(OBJECT_DIMENSIONS))
}

/// `circleReceptor`
pub fn circle_receptor(env: &Env, h: &HObj) -> DrawInfo {
    receptor_from_dho(&env.hoc, h.stacked, VEC2_ZERO, h.scale)
}

/// `SliderGeom`
#[derive(Clone, Copy)]
pub struct SliderGeom {
    pub path_radius: F32,
    pub size: Vec2,
    pub origin: Vec2,
    pub draw_info: DrawInfo,
    pub head_receptor: DrawInfo,
}

/// `default : SliderGeom`
pub const SLIDER_GEOM_DEFAULT: SliderGeom = SliderGeom {
    path_radius: F32_0,
    size: VEC2_ZERO,
    origin: VEC2_ZERO,
    draw_info: DRAWINFO_DEFAULT,
    head_receptor: DRAWINFO_DEFAULT,
};

/// Bounds accumulator of `sliderGeom`'s loop.
#[derive(Clone, Copy)]
pub struct Bounds {
    pub min_x: F32,
    pub min_y: F32,
    pub max_x: F32,
    pub max_y: F32,
}

/// the `for v in sd.path` loop of `sliderGeom`
pub fn path_bounds(path: &[Vec2], r: F32) -> Bounds {
    let mut b = Bounds { min_x: F32_0, min_y: F32_0, max_x: F32_0, max_y: F32_0 };
    let mut i: usize = 0;
    while i < path.len() {
        let v = path[i];
        b.min_x = f32_min(b.min_x, v.x.sub(r));
        b.min_y = f32_min(b.min_y, v.y.sub(r));
        b.max_x = f32_max(b.max_x, v.x.add(r));
        b.max_y = f32_max(b.max_y, v.y.add(r));
        i += 1;
    }
    b
}

/// `sliderGeom`
pub fn slider_geom(env: &Env, h: &HObj, sd: &SliderData) -> Result<SliderGeom, SimErr> {
    let r = env.argon_path_radius.mul(h.scale);
    let b = path_bounds(&sd.path, r);
    let n = sd.path.len();
    let size = if n > 0 { Vec2 { x: b.max_x.sub(b.min_x), y: b.max_y.sub(b.min_y) } } else { VEC2_ZERO };
    let tl = if n > 0 { Vec2 { x: b.min_x, y: b.min_y } } else { VEC2_ZERO };
    // `SliderBody.PathOffset => path.PositionInBoundingBox(path.Vertices[0])` throws on an empty path
    if n == 0 {
        return Err(SimErr::EmptyPath);
    }
    let v0 = sd.path[0];
    let origin = v0.sub(tl);
    let di = child_draw_info(&env.hoc, h.stacked, VEC2_ZERO, VEC2_ONE, origin);
    let hc_size = Vec2 { x: F32_1.mul(size.x), y: F32_1.mul(size.y) };
    let hc = child_draw_info(&di, VEC2_ZERO, VEC2_ZERO.mul(size), VEC2_ONE, VEC2_ZERO);
    let rel_anchor = origin.cdiv(size);
    let head = receptor_from_dho(&hc, VEC2_ZERO, rel_anchor.mul(hc_size), h.scale);
    Ok(SliderGeom { path_radius: r, size, origin, draw_info: di, head_receptor: head })
}

// ---- M7: geometry with transformable DHO state ----

/// `Placement`
#[derive(Clone, Copy)]
pub struct Placement {
    pub pos: Vec2,
    pub scale: Vec2,
    pub rot: F32,
}

/// `childDrawInfoR`
pub fn child_draw_info_r(parent: &DrawInfo, draw_position: Vec2, anchor_position: Vec2, scale: Vec2, rot: F32, origin: Vec2) -> DrawInfo {
    let pos = draw_position.add(anchor_position).add(VEC2_ZERO);
    apply_transform_r(parent, pos, scale, rot, origin.sub(VEC2_ZERO))
}

/// `receptorFromPlacement`
pub fn receptor_from_placement(parent: &DrawInfo, pl: Placement, dho_anchor: Vec2, scale: F32) -> DrawInfo {
    let dho = child_draw_info_r(parent, pl.pos, dho_anchor, pl.scale, pl.rot, centre_of(OBJECT_DIMENSIONS));
    let sc_size = Vec2 { x: F32_1.mul(OBJECT_DIMENSIONS.x), y: F32_1.mul(OBJECT_DIMENSIONS.y) };
    let sc = child_draw_info(&dho, VEC2_ZERO, VEC2_HALF.mul(OBJECT_DIMENSIONS), Vec2 { x: scale, y: scale }, centre_of(sc_size));
    child_draw_info(&sc, VEC2_ZERO, VEC2_HALF.mul(sc_size), VEC2_ONE, centre_of(OBJECT_DIMENSIONS))
}

/// `bodyRefresh`: (Size, PathOffset)
pub fn body_refresh(sd: &SliderData, r: F32) -> Result<(Vec2, Vec2), SimErr> {
    let b = path_bounds(&sd.path, r);
    let n = sd.path.len();
    let size = if n > 0 { Vec2 { x: b.max_x.sub(b.min_x), y: b.max_y.sub(b.min_y) } } else { VEC2_ZERO };
    let tl = if n > 0 { Vec2 { x: b.min_x, y: b.min_y } } else { VEC2_ZERO };
    if n == 0 {
        return Err(SimErr::EmptyPath);
    }
    let v0 = sd.path[0];
    Ok((size, v0.sub(tl)))
}

/// `sliderGeomP`
pub fn slider_geom_p(hoc: &DrawInfo, argon_path_radius: F32, h: &HObj, pl: Placement, size: Vec2, origin: Vec2, rel_anchor: Vec2, head_pl: Placement) -> SliderGeom {
    let di = child_draw_info_r(hoc, pl.pos, VEC2_ZERO, pl.scale, pl.rot, origin);
    let hc_size = Vec2 { x: F32_1.mul(size.x), y: F32_1.mul(size.y) };
    let hc = child_draw_info(&di, VEC2_ZERO, VEC2_ZERO.mul(size), VEC2_ONE, VEC2_ZERO);
    let head = receptor_from_placement(&hc, head_pl, rel_anchor.mul(hc_size), h.scale);
    SliderGeom { path_radius: argon_path_radius.mul(h.scale), size, origin, draw_info: di, head_receptor: head }
}

/// `receptorCornerExponent`
pub const RECEPTOR_CORNER_EXPONENT: F32 = F32_2;
pub const F32_0_8: F32 = F32::from_bits(0x3F4C_CCCD);
pub const F32_0_2: F32 = F32::from_bits(0x3E4C_CCCD);

/// `receptorEffectiveCornerRadius`
pub fn receptor_effective_corner_radius() -> F32 {
    OBJECT_RADIUS.mul(F32_0_8).mul(RECEPTOR_CORNER_EXPONENT).div(F32_2).add(F32_0_2.mul(OBJECT_RADIUS))
}

/// `receptorCornerRadiusPow` (computed once per run, stored in `Ctx.corner_pow`)
pub fn receptor_corner_radius_pow() -> F64 {
    receptor_effective_corner_radius().to_f64().pow(RECEPTOR_CORNER_EXPONENT.to_f64())
}

/// `receptorContains`; `corner_pow` = `receptorCornerRadiusPow`
pub fn receptor_contains(di: &DrawInfo, screen: Vec2, corner_pow: F64) -> bool {
    let corner_exponent = RECEPTOR_CORNER_EXPONENT;
    let c_r = receptor_effective_corner_radius();
    if c_r.eq(F32_0) {
        let l = to_local(di, screen);
        F32_0.le(l.x) && l.x.le(F32_128) && F32_0.le(l.y) && l.y.le(F32_128)
    } else {
        let l = to_local(di, screen);
        let rx = F32_0.sub(c_r.neg());
        let ry = F32_0.sub(c_r.neg());
        let rw = F32_128.add(c_r.neg().add(c_r.neg()));
        let rh = F32_128.add(c_r.neg().add(c_r.neg()));
        let right = rx.add(rw);
        let bottom = ry.add(rh);
        let dist_x = f32_max(F32_0, f32_max(l.x.sub(right), rx.sub(l.x)));
        let dist_y = f32_max(F32_0, f32_max(l.y.sub(bottom), ry.sub(l.y)));
        let lhs = dist_x.pow(corner_exponent).add(dist_y.pow(corner_exponent));
        lhs.to_f64().le(corner_pow)
    }
}

/// `SpinnerGeom`
#[derive(Clone, Copy)]
pub struct SpinnerGeom {
    pub aspect: DrawInfo,
    pub tracker_size: Vec2,
}

pub const SPINNER_GEOM_DEFAULT: SpinnerGeom = SpinnerGeom { aspect: DRAWINFO_DEFAULT, tracker_size: VEC2_ZERO };

/// `spinnerGeomP`
pub fn spinner_geom_p(hoc: &DrawInfo, hoc_size: Vec2, pl: Placement) -> SpinnerGeom {
    let conv = Vec2 { x: hoc_size.x.div(F32_1), y: hoc_size.y.div(F32_1) };
    let s_size = Vec2 { x: F32_1.mul(conv.x), y: F32_1.mul(conv.y) };
    let sp = child_draw_info_r(hoc, pl.pos, VEC2_ZERO, pl.scale, pl.rot, centre_of(s_size));
    let s_conv = Vec2 { x: s_size.x.div(F32_1), y: s_size.y.div(F32_1) };
    let a_h = F32_1.mul(s_conv.y);
    let a_size = Vec2 { x: a_h, y: a_h };
    let aspect = child_draw_info(&sp, VEC2_ZERO, VEC2_HALF.mul(s_size), VEC2_ONE, centre_of(a_size));
    let a_conv = Vec2 { x: a_size.x.div(F32_1), y: a_size.y.div(F32_1) };
    SpinnerGeom { aspect, tracker_size: Vec2 { x: F32_1.mul(a_conv.x), y: F32_1.mul(a_conv.y) } }
}

/// `spinnerGeom`
pub fn spinner_geom(env: &Env, h: &HObj) -> SpinnerGeom {
    spinner_geom_p(&env.hoc, env.hoc_size, Placement { pos: h.pos, scale: VEC2_ONE, rot: F32_0 })
}

pub const F32_180: F32 = F32::from_bits(0x4334_0000);
/// `float.Pi`
pub const F32_PI: F32 = F32::from_bits(0x4049_0FDB);

/// `radiansToDegrees`
pub fn radians_to_degrees(x: F32) -> F32 {
    x.mul(F32_180).div(F32_PI)
}

/// `compareD` (`double.CompareTo`)
pub fn compare_d(a: F64, b: F64) -> i32 {
    if a.lt(b) {
        -1
    } else if b.lt(a) {
        1
    } else if a.eq(b) {
        0
    } else if a.is_nan() {
        if b.is_nan() { 0 } else { -1 }
    } else {
        1
    }
}

/// `binarySearchD` (`List<double>.BinarySearch`); returns the index or the complement of the insertion point.
pub fn binary_search_d(a: &[F64], v: F64) -> i64 {
    let mut lo: i64 = 0;
    let mut hi: i64 = a.len() as i64 - 1;
    let mut fuel: u64 = a.len() as u64 + 2;
    while lo <= hi && fuel > 0 {
        fuel -= 1;
        let i = lo + (hi - lo) / 2;
        let c = compare_d(a[i as usize], v);
        if c == 0 {
            return i;
        }
        if c < 0 {
            lo = i + 1;
        } else {
            hi = i - 1;
        }
    }
    -lo - 1
}

/// `SliderData.distance`
pub fn distance(sd: &SliderData) -> F64 {
    let n = sd.cum_len.len();
    if n > 0 { sd.cum_len[n - 1] } else { netx::F64_ZERO }
}

pub const F64_0: F64 = F64::from_bits(0);
pub const F64_1: F64 = F64::from_bits(0x3FF0_0000_0000_0000);

/// `SliderData.positionAt`
pub fn position_at(sd: &SliderData, progress: F64) -> Result<Vec2, SimErr> {
    // `Math.Clamp(progress, 0, 1)`: literal bounds, never throws
    let clamped = if progress.lt(F64_0) { F64_0 } else if F64_1.lt(progress) { F64_1 } else { progress };
    let d = clamped.mul(distance(sd));
    let i0 = binary_search_d(&sd.cum_len, d);
    let i = if i0 < 0 { -i0 - 1 } else { i0 };
    let n = sd.path.len();
    if n == 0 {
        Ok(VEC2_ZERO)
    } else if i <= 0 {
        Ok(sd.path[0])
    } else if i >= n as i64 {
        Ok(sd.path[n - 1])
    } else {
        let k = (i - 1) as usize;
        let p0 = sd.path[k];
        let p1 = sd.path[k + 1];
        // `cumulativeLength[i-1]`, `cumulativeLength[i]`: lazer keeps one length per path vertex
        let m = sd.cum_len.len();
        if k >= m {
            return Err(SimErr::CumLen(k));
        }
        if k + 1 >= m {
            return Err(SimErr::CumLen(k + 1));
        }
        let d0 = sd.cum_len[k];
        let d1 = sd.cum_len[k + 1];
        if almost_equals_d(d0, d1) {
            Ok(p0)
        } else {
            let w = d.sub(d0).div(d1.sub(d0));
            Ok(p0.add(p1.sub(p0).scale(w.to_f32())))
        }
    }
}

/// `SliderData.spanAt`
pub fn span_at(sd: &SliderData, progress: F64) -> i32 {
    progress.mul(F64::from_u64(sd.span_count)).to_i32_sat()
}

/// `SliderData.progressAt`
pub fn progress_at(sd: &SliderData, progress: F64) -> F64 {
    let p = fmod1(progress.mul(F64::from_u64(sd.span_count)));
    // spec: `Int.emod (spanAt progress) 2 == 1`, i.e. the span index is odd (also when negative)
    if span_at(sd, progress) % 2 != 0 { F64_1.sub(p) } else { p }
}

/// `SliderData.curvePositionAt`
pub fn curve_position_at(sd: &SliderData, progress: F64) -> Result<Vec2, SimErr> {
    position_at(sd, progress_at(sd, progress))
}

/// `f32_2_4` (`DrawableSliderBall.FOLLOW_AREA`)
pub const F32_2_4: F32 = F32::from_bits(0x4019_999A);

/// `followRadius`
pub fn follow_radius(h: &HObj, expanded: bool) -> F32 {
    let r = h.radius.to_f32();
    if expanded { r.mul(F32_2_4) } else { r }
}

/// `mouseInSlider`
pub fn mouse_in_slider(g: &SliderGeom, screen: Vec2) -> Vec2 {
    to_local(&g.draw_info, screen).sub(g.origin)
}

/// `isMouseInFollowArea`
pub fn is_mouse_in_follow_area(h: &HObj, sd: &SliderData, g: &SliderGeom, mouse: Option<Vec2>, t: F64, expanded: bool) -> Result<bool, SimErr> {
    match mouse {
        None => Ok(false),
        Some(pos) => {
            let radius = follow_radius(h, expanded);
            let fp0 = t.sub(h.start).div(sd.duration);
            // `Math.Clamp(…, 0, 1)`: literal bounds, never throws
            let follow_progress = if fp0.lt(F64_0) { F64_0 } else if F64_1.lt(fp0) { F64_1 } else { fp0 };
            let follow = curve_position_at(sd, follow_progress)?;
            let m = mouse_in_slider(g, pos);
            Ok(m.sub(follow).length_squared().le(radius.mul(radius)))
        }
    }
}
