//! Port of `OsuModel/Beatmap/ModRandom.lean`: Random (`OsuModRandom`) and the repositioning
//! utilities (`OsuHitObjectGenerationUtils`). RNG: `System.Random((int)Seed)`, `NextDouble`.
use super::control_points::{timing_point_at, ControlPointInfo};
use super::dotnet::fmod_f64;
use super::dotnet::fmod_f32;
use super::errors::*;
use super::hit_object_parser::{lift_net, DecodeError};
use super::mods::{modify_slider, set_position, PointMap};
use super::objects::{end_position, is_circle, is_slider, is_spinner, radius, ObjectKind, OsuHitObject};
use super::playable::PlayableBeatmap;
use super::slider_path::{self, SliderPath, SliderPathSpec};
use super::vector2::{self as v, almost_equals_f32, Vec2};
use crate::float::{F32, F64};
use crate::net::basic::F32_POS_INF;
use crate::net::mathops::{f32_clamp, f32_max, f32_min};
use crate::net::osutk::inverse_sqrt_fast;
use crate::net::random::{self, State};
use alloc::vec::Vec;

const F0: F32 = F32::from_bits(0);
const F1: F32 = F32::from_bits(0x3F80_0000) /* 1f */;
const F2: F32 = F32::from_bits(0x4000_0000) /* 2f */;
/// `OsuPlayfield.BASE_SIZE`
pub const BASE_SIZE: Vec2 = Vec2 { x: F32::from_bits(0x4400_0000) /* 512f */, y: F32::from_bits(0x43C0_0000) /* 384f */ };
/// `BASE_SIZE / 2`
pub const CENTRE: Vec2 = Vec2 { x: F32::from_bits(0x4380_0000) /* 256f */, y: F32::from_bits(0x4340_0000) /* 192f */ };
/// `playfield_edge_ratio = 0.375f`
pub const EDGE_RATIO: F32 = F32::from_bits(0x3EC0_0000) /* 0.375f */;
/// `MathF.PI`
pub const PI: F32 = F32::from_bits(0x4049_0FDB);

pub fn border_x() -> F32 {
    F32::from_bits(0x4400_0000) /* 512f */.mul(EDGE_RATIO)
}
pub fn border_y() -> F32 {
    F32::from_bits(0x43C0_0000) /* 384f */.mul(EDGE_RATIO)
}
/// `2 * MathF.PI`; spec `Reposition.TWO_PI`
pub fn two_pi() -> F32 {
    F2.mul(PI)
}

/// `MathF.Atan2(y, x)`
pub fn atan2f(y: F32, x: F32) -> F32 {
    y.atan2(x)
}

/// `RotateVectorTowardsVector`; spec `Reposition.rotateVectorTowardsVector`
pub fn rotate_vector_towards_vector(initial: Vec2, destination: Vec2, rotation_ratio: F32) -> Vec2 {
    let initial_angle = atan2f(initial.y, initial.x);
    let dest_angle = atan2f(destination.y, destination.x);
    let mut diff = dest_angle.sub(initial_angle);
    let tp = two_pi();
    let mut k = 0;
    while k < 4 {
        if diff.lt(PI.neg()) {
            diff = diff.add(tp);
        }
        k = k + 1;
    }
    k = 0;
    while k < 4 {
        if PI.lt(diff) {
            diff = diff.sub(tp);
        }
        k = k + 1;
    }
    let final_angle = initial_angle.add(rotation_ratio.mul(diff));
    Vec2 { x: v::length(initial).mul(final_angle.cos()), y: v::length(initial).mul(final_angle.sin()) }
}

/// `RotateAwayFromEdge(prevObjectPos, posRelativeToPrev, rotationRatio)`; spec `Reposition.rotateAwayFromEdge`
pub fn rotate_away_from_edge(prev: Vec2, rel: Vec2, rotation_ratio: F32) -> Vec2 {
    let bx = border_x();
    let by = border_y();
    let r0 = F0;
    let r1 = if prev.x.lt(CENTRE.x) {
        f32_max(bx.sub(prev.x).div(bx), r0)
    } else {
        f32_max(prev.x.sub(BASE_SIZE.x.sub(bx)).div(bx), r0)
    };
    let r2 = if prev.y.lt(CENTRE.y) {
        f32_max(by.sub(prev.y).div(by), r1)
    } else {
        f32_max(prev.y.sub(BASE_SIZE.y.sub(by)).div(by), r1)
    };
    rotate_vector_towards_vector(rel, v::sub(CENTRE, prev), f32_min(F1, r2.mul(rotation_ratio)))
}

/// `rotateVector(vector, rotation)`; spec `Reposition.rotateVector`
pub fn rotate_vector(vv: Vec2, rotation: F32) -> Vec2 {
    let angle = atan2f(vv.y, vv.x).add(rotation);
    let length = v::length(vv);
    Vec2 { x: length.mul(angle.cos()), y: length.mul(angle.sin()) }
}

/// the default (empty) `SliderPath` (Lean `default`)
pub fn empty_path() -> SliderPath {
    SliderPath {
        spec: SliderPathSpec { control_points: Vec::new(), expected_distance: None, optimise_catmull: false },
        calculated_path: Vec::new(),
        cumulative_length: Vec::new(),
        calculated_length: F64::from_bits(0),
        fuel_out: false,
    }
}

/// spec `Reposition.sliderPath` (borrowing; `None` = the spec's `default`)
pub fn slider_path_of(h: &OsuHitObject) -> Option<&SliderPath> {
    match &h.kind {
        ObjectKind::Slider(s) => Some(&s.path),
        _ => None,
    }
}

const D1: F64 = F64::from_bits(0x3FF0_0000_0000_0000);

/// `getSliderRotation(slider)`; spec `Reposition.sliderRotation`
pub fn slider_rotation(h: &OsuHitObject) -> F32 {
    let e = match &h.kind {
        ObjectKind::Slider(s) => slider_path::position_at(&s.path, D1),
        _ => slider_path::position_at(&empty_path(), D1),
    };
    atan2f(e.y, e.x)
}

/// `getAngleDifference(a1, a2)`; spec `Reposition.angleDifference`
pub fn angle_difference(a1: F32, a2: F32) -> F32 {
    let tp = two_pi();
    let diff = fmod_f32(a1.sub(a2).abs(), tp);
    f32_min(diff, tp.sub(diff))
}

/// `RotateSlider(slider, rotation)`; spec `Reposition.rotateSlider`
pub fn rotate_slider(h: &mut OsuHitObject, rotation: F32) {
    modify_slider(PointMap::Rotate(rotation), h);
}

/// `FlipSliderInPlaceHorizontally(slider)`; spec `Reposition.flipSliderInPlaceHorizontally`
pub fn flip_slider_in_place_horizontally(h: &mut OsuHitObject) {
    modify_slider(PointMap::NegX, h);
}

/// `RectangleF`; spec `Reposition.RectF`
#[derive(Clone, Copy)]
pub struct RectF {
    pub x: F32,
    pub y: F32,
    pub w: F32,
    pub h: F32,
}
pub fn rect_right(r: RectF) -> F32 {
    r.x.add(r.w)
}
pub fn rect_bottom(r: RectF) -> F32 {
    r.y.add(r.h)
}

/// `CalculatePossibleMovementBounds(slider)`; spec `Reposition.possibleMovementBounds`
pub fn possible_movement_bounds(h: &OsuHitObject) -> RectF {
    let mut min_x = F32_POS_INF;
    let mut max_x = F32_POS_INF.neg();
    let mut min_y = F32_POS_INF;
    let mut max_y = F32_POS_INF.neg();
    match slider_path_of(h) {
        Some(p) => {
            let mut i = 0;
            while i < p.calculated_path.len() {
                let q = p.calculated_path[i];
                min_x = f32_min(min_x, q.x);
                max_x = f32_max(max_x, q.x);
                min_y = f32_min(min_y, q.y);
                max_y = f32_max(max_y, q.y);
                i = i + 1;
            }
        }
        None => {}
    }
    let rad = radius(h).to_f32();
    min_x = min_x.sub(rad);
    min_y = min_y.sub(rad);
    max_x = max_x.add(rad);
    max_y = max_y.add(rad);
    let left = min_x.neg();
    let right = BASE_SIZE.x.sub(max_x);
    let top = min_y.neg();
    let bottom = BASE_SIZE.y.sub(max_y);
    RectF { x: left, y: top, w: right.sub(left), h: bottom.sub(top) }
}

/// `clampToPlayfieldWithPadding(position, padding)`; spec `Reposition.clampWithPadding`
pub fn clamp_with_padding(p: Vec2, padding: F32) -> Result<Vec2, DecodeError> {
    let x = tri!(lift_net(W_MATH_CLAMP, f32_clamp(p.x, padding, BASE_SIZE.x.sub(padding))));
    let y = tri!(lift_net(W_MATH_CLAMP, f32_clamp(p.y, padding, BASE_SIZE.y.sub(padding))));
    Ok(Vec2 { x, y })
}

const D50: F64 = F64::from_bits(0x4049_0000_0000_0000);

/// `calculateCentreOfMass(slider)`; spec `Reposition.centreOfMass`
pub fn centre_of_mass(h: &OsuHitObject) -> Vec2 {
    match &h.kind {
        ObjectKind::Slider(s) => centre_of_mass_path(&s.path),
        _ => centre_of_mass_path(&empty_path()),
    }
}

/// `calculateCentreOfMass` on the slider's path
pub fn centre_of_mass_path(path: &SliderPath) -> Vec2 {
    let sample_step = D50;
    if slider_path::distance(path).le(sample_step) {
        let e = slider_path::position_at(path, D1);
        return Vec2 { x: e.x.div(F2), y: e.y.div(F2) };
    }
    let mut count: u64 = 0;
    let mut sum = v::ZERO;
    let path_distance = slider_path::distance(path);
    let mut i = F64::from_bits(0);
    let mut fuel: u64 = 0;
    while i.lt(path_distance) && fuel < 100000000 {
        sum = v::add(sum, slider_path::position_at(path, i.div(path_distance)));
        count = count + 1;
        i = i.add(sample_step);
        fuel = fuel + 1;
    }
    let c = F32::from_u64(count);
    Vec2 { x: sum.x.div(c), y: sum.y.div(c) }
}

/// `ObjectPositionInfo`; spec `Reposition.PositionInfo`
#[derive(Clone, Copy)]
pub struct PositionInfo {
    pub relative_angle: F32,
    pub distance_from_previous: F32,
    pub rotation: F32,
}

/// `GeneratePositionInfos(hitObjects)`; spec `Reposition.generatePositionInfos`
pub fn generate_position_infos(hos: &[OsuHitObject]) -> Vec<PositionInfo> {
    let mut out: Vec<PositionInfo> = Vec::with_capacity(hos.len());
    let mut previous_position = CENTRE;
    let mut previous_angle = F0;
    let mut i = 0;
    while i < hos.len() {
        let h = &hos[i];
        let rel = v::sub(h.position, previous_position);
        let mut absolute_angle = atan2f(rel.y, rel.x);
        let mut info = PositionInfo { relative_angle: absolute_angle.sub(previous_angle), distance_from_previous: v::length(rel), rotation: F0 };
        if is_slider(h) {
            let absolute_rotation = slider_rotation(h);
            info.rotation = absolute_rotation.sub(absolute_angle);
            absolute_angle = absolute_rotation;
        }
        out.push(info);
        previous_position = end_position(h);
        previous_angle = absolute_angle;
        i = i + 1;
    }
    out
}

/// `WorkingObject`; spec `Reposition.Working`
#[derive(Clone, Copy)]
pub struct Working {
    pub rotation_original: F32,
    pub position_modified: Vec2,
    pub end_position_modified: Vec2,
}

const F_HALF: F32 = F32::from_bits(0x3F00_0000) /* 0.5f */;

/// `computeModifiedPosition(current, previous, beforePrevious)`: may rotate `hos[i]` (a slider)
/// and returns its `PositionModified`; spec `Reposition.computeModifiedPosition`
pub fn compute_modified_position(hos: &mut Vec<OsuHitObject>, ws: &[Working], infos: &[PositionInfo], i: usize, prev: Option<usize>, before_prev: Option<usize>) -> Vec2 {
    let mut previous_absolute_angle = F0;
    match prev {
        Some(p) => {
            if is_slider(&hos[p]) {
                previous_absolute_angle = slider_rotation(&hos[p]);
            } else {
                let earliest = match before_prev {
                    Some(b) => end_position(&hos[b]),
                    None => CENTRE,
                };
                let rel = v::sub(hos[p].position, earliest);
                previous_absolute_angle = atan2f(rel.y, rel.x);
            }
        }
        None => {}
    }
    let info = infos[i];
    let absolute_angle = previous_absolute_angle.add(info.relative_angle);
    let pos_rel0 = Vec2 { x: info.distance_from_previous.mul(absolute_angle.cos()), y: info.distance_from_previous.mul(absolute_angle.sin()) };
    let last_end = match prev {
        Some(p) => ws[p].end_position_modified,
        None => CENTRE,
    };
    let pos_rel = rotate_away_from_edge(last_end, pos_rel0, F_HALF);
    let position_modified = v::add(last_end, pos_rel);
    if !is_slider(&hos[i]) {
        return position_modified;
    }
    let absolute_angle2 = atan2f(pos_rel.y, pos_rel.x);
    let com_original = centre_of_mass(&hos[i]);
    let com_modified0 = rotate_vector(com_original, info.rotation.add(absolute_angle2).sub(slider_rotation(&hos[i])));
    let com_modified = rotate_away_from_edge(position_modified, com_modified0, F_HALF);
    let relative_rotation = atan2f(com_modified.y, com_modified.x).sub(atan2f(com_original.y, com_original.x));
    if !almost_equals_f32(relative_rotation, F0) {
        rotate_slider(&mut hos[i], relative_rotation);
    }
    position_modified
}

/// `clampSliderToPlayfield(workingObject)`: returns the new working object and the shift;
/// spec `Reposition.clampSliderToPlayfield`
pub fn clamp_slider_to_playfield(h: &mut OsuHitObject, w: Working) -> Result<(Working, Vec2), DecodeError> {
    let mut bounds = possible_movement_bounds(h);
    if bounds.w.lt(F0) || bounds.h.lt(F0) {
        let current_rotation = slider_rotation(h);
        let diff1 = angle_difference(w.rotation_original, current_rotation);
        let diff2 = angle_difference(w.rotation_original.add(PI), current_rotation);
        if diff1.lt(diff2) {
            let r = w.rotation_original.sub(slider_rotation(h));
            rotate_slider(h, r);
        } else {
            let r = w.rotation_original.add(PI).sub(slider_rotation(h));
            rotate_slider(h, r);
        }
        bounds = possible_movement_bounds(h);
    }
    let previous_position = w.position_modified;
    let new_x = if bounds.w.lt(F0) {
        tri!(lift_net(W_MATH_CLAMP, f32_clamp(bounds.x, F0, BASE_SIZE.x)))
    } else {
        tri!(lift_net(W_MATH_CLAMP, f32_clamp(previous_position.x, bounds.x, rect_right(bounds))))
    };
    let new_y = if bounds.h.lt(F0) {
        tri!(lift_net(W_MATH_CLAMP, f32_clamp(bounds.y, F0, BASE_SIZE.y)))
    } else {
        tri!(lift_net(W_MATH_CLAMP, f32_clamp(previous_position.y, bounds.y, rect_bottom(bounds))))
    };
    let p = Vec2 { x: new_x, y: new_y };
    set_position(h, p);
    let w2 = Working { rotation_original: w.rotation_original, position_modified: p, end_position_modified: end_position(h) };
    Ok((w2, v::sub(p, previous_position)))
}

/// `applyDecreasingShift` over the (up to 10) preceding hit circles of `i`
pub fn apply_decreasing_shift(hos: &mut Vec<OsuHitObject>, i: usize, shift: Vec2) -> Result<(), DecodeError> {
    let mut to_be_shifted: Vec<usize> = Vec::new();
    let mut k = 1;
    let mut go = true;
    while go && k < 11 {
        if k > i {
            go = false;
        } else if !is_circle(&hos[i - k]) {
            go = false;
        } else {
            to_be_shifted.push(i - k);
            k = k + 1;
        }
    }
    let count = to_be_shifted.len();
    let mut idx = 0;
    let mut err: Option<DecodeError> = None;
    while err.is_none() && idx < count {
        let j = to_be_shifted[idx];
        let f = F32::from_u64((count - idx) as u64).div(F32::from_u64((count + 1) as u64));
        let position = v::add(hos[j].position, Vec2 { x: shift.x.mul(f), y: shift.y.mul(f) });
        let r = clamp_with_padding(position, radius(&hos[j]).to_f32());
        let mut p = v::ZERO;
        match r {
            Ok(q) => p = q,
            Err(e) => err = Some(e),
        }
        if err.is_none() {
            set_position(&mut hos[j], p);
        }
        idx = idx + 1;
    }
    match err {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

/// One iteration of `RepositionHitObjects` for a non-spinner `i`.
pub fn reposition_one(hos: &mut Vec<OsuHitObject>, ws: &mut Vec<Working>, infos: &[PositionInfo], i: usize, previous: Option<usize>) -> Result<(), DecodeError> {
    let pm = compute_modified_position(hos, ws, infos, i, previous, if i > 1 { Some(i - 2) } else { None });
    ws[i].position_modified = pm;
    let mut shift = v::ZERO;
    if is_circle(&hos[i]) {
        let w = ws[i];
        let previous_position = w.position_modified;
        let p = tri!(clamp_with_padding(w.position_modified, radius(&hos[i]).to_f32()));
        ws[i] = Working { rotation_original: w.rotation_original, position_modified: p, end_position_modified: p };
        set_position(&mut hos[i], p);
        shift = v::sub(p, previous_position);
    } else if is_slider(&hos[i]) {
        let (w2, s) = tri!(clamp_slider_to_playfield(&mut hos[i], ws[i]));
        ws[i] = w2;
        shift = s;
    }
    if !v::eq(shift, v::ZERO) {
        tri!(apply_decreasing_shift(hos, i, shift));
    }
    Ok(())
}

/// `RepositionHitObjects(objectPositionInfos)`; spec `Reposition.repositionHitObjects`
pub fn reposition_hit_objects(hos: &mut Vec<OsuHitObject>, infos: &[PositionInfo]) -> Result<(), DecodeError> {
    let mut ws: Vec<Working> = Vec::with_capacity(hos.len());
    let mut k = 0;
    while k < hos.len() {
        let h = &hos[k];
        ws.push(Working {
            rotation_original: if is_slider(h) { slider_rotation(h) } else { F0 },
            position_modified: h.position,
            end_position_modified: end_position(h),
        });
        k = k + 1;
    }
    let mut previous: Option<usize> = None;
    let mut err: Option<DecodeError> = None;
    let mut i = 0;
    while err.is_none() && i < hos.len() {
        if is_spinner(&hos[i]) {
            previous = Some(i);
        } else {
            let r = reposition_one(hos, &mut ws, infos, i, previous);
            match r {
                Ok(_) => {}
                Err(e) => err = Some(e),
            }
            previous = Some(i);
        }
        i = i + 1;
    }
    match err {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

// ----------------------------------------------------------------- RandomMod

const D2: F64 = F64::from_bits(0x4000_0000_0000_0000);

/// `IsHitObjectOnBeat(beatmap, hitObject, downbeatsOnly)`; spec `RandomMod.isOnBeat`
pub fn is_on_beat(cpi: &ControlPointInfo, h: &OsuHitObject, downbeats_only: bool) -> bool {
    let tp = timing_point_at(cpi, h.start_time);
    let time_since = h.start_time.sub(tp.time);
    let beat_length = if downbeats_only { tp.beat_length.mul(F64::from_i64(tp.time_signature as i64)) } else { tp.beat_length };
    fmod_f64(time_since.add(D1).abs(), beat_length).lt(D2)
}

/// `OsuPlayfield.BASE_SIZE.LengthFast`; spec `RandomMod.playfieldDiagonal`
pub fn playfield_diagonal() -> F32 {
    F1.div(inverse_sqrt_fast(F32::from_bits(0x4400_0000) /* 512f */.mul(F32::from_bits(0x4400_0000) /* 512f */).add(F32::from_bits(0x43C0_0000) /* 384f */.mul(F32::from_bits(0x43C0_0000) /* 384f */))))
}

pub fn six_tenths_f() -> F64 {
    F32::from_bits(0x3F19_999A) /* 0.6f */.to_f64()
}
pub fn four_tenths_f() -> F64 {
    F32::from_bits(0x3ECC_CCCD) /* 0.4f */.to_f64()
}

/// `Math.PI`
const DPI: F64 = F64::from_bits(0x4009_21FB_5444_2D18);

/// `RandomGaussian(rng, 0, stdDev)`; spec `RandomMod.randomGaussian`
pub fn random_gaussian(std_dev: F32, rng: State) -> (F32, State) {
    let (a, r1) = random::next_double(rng);
    let x1 = D1.sub(a);
    let (b, r2) = random::next_double(r1);
    let x2 = D1.sub(b);
    let std_normal = F64::from_bits(0xC000_0000_0000_0000) /* -2 */.mul(x1.log()).sqrt().mul(D2.mul(DPI).mul(x2).sin());
    (F0.add(std_dev.mul(std_normal.to_f32())), r2)
}

/// `getRandomOffset(stdDev)`; spec `RandomMod.randomOffset`
pub fn random_offset(sharpness: F32, std_dev: F32, rng: State) -> (F32, State) {
    let mult = F32::from_bits(0x3FC0_0000) /* 1.5f */.mul(F32::from_bits(0x4120_0000) /* 10f */).sub(sharpness).div(F32::from_bits(0x3FC0_0000) /* 1.5f */.mul(F32::from_bits(0x4120_0000) /* 10f */).sub(F32::from_bits(0x40E0_0000) /* 7f */));
    random_gaussian(std_dev.mul(mult), rng)
}

/// `getRelativeTargetAngle(targetDistance, offset, flowDirection)`; spec `RandomMod.relativeTargetAngle`
pub fn relative_target_angle(sharpness: F32, target_distance0: F32, offset: F32, flow: bool) -> F32 {
    let angle_sharpness = sharpness.div(F32::from_bits(0x4120_0000) /* 10f */);
    let angle_wideness = F1.sub(angle_sharpness);
    let custom_offset_x = angle_sharpness.mul(F32::from_bits(0x42C8_0000) /* 100f */).sub(F32::from_bits(0x428C_0000) /* 70f */);
    let custom_offset_y = angle_wideness.mul(F32::from_bits(0x3E80_0000) /* 0.25f */).sub(F32::from_bits(0x3D99_999A) /* 0.075f */);
    let target_distance = target_distance0.add(custom_offset_x);
    let inner = target_distance.sub(F32::from_bits(0x439B_0000) /* 310f */).add(custom_offset_x);
    let angle0 = F64::from_bits(0x4001_47AE_147A_E148) /* 2.16 */.div(D1.add(F64::from_bits(0x4069_0000_0000_0000) /* 200 */.mul(F64::from_bits(0x3FA2_6E97_8D4F_DF3B) /* 0.036 */.mul(inner.to_f64()).exp()))).add(F64::from_bits(0x3FE0_0000_0000_0000) /* 0.5 */).to_f32();
    let angle = angle0.add(offset.add(custom_offset_y));
    let relative_angle = PI.sub(angle);
    if flow { relative_angle.neg() } else { relative_angle }
}

/// `shouldStartNewSection`'s / `shouldApplyFlowChange`'s "combo started" condition
fn combo_started(hos: &[OsuHitObject], i: usize) -> bool {
    hos[if i >= 2 { i - 2 } else { 0 }].index_in_current_combo > 1 && hos[i - 1].new_combo
}

/// `OsuModRandom.ApplyToBeatmap`; spec `RandomMod.apply`
pub fn apply(seed: i32, sharpness: F32, pb: &mut PlayableBeatmap) -> Result<(), DecodeError> {
    let mut rng = random::create(seed);
    let mut infos = generate_position_infos(&pb.hit_objects);
    let mut section_offset = F0;
    let mut flow = false;
    let six = six_tenths_f();
    let four = four_tenths_f();
    let mut i = 0;
    while i < infos.len() {
        let new_section = if i == 0 {
            true
        } else {
            let started = combo_started(&pb.hit_objects, i);
            let downbeat = is_on_beat(&pb.control_points, &pb.hit_objects[i - 1], true);
            let on_beat = is_on_beat(&pb.control_points, &pb.hit_objects[i - 1], false);
            let mut r = false;
            if started {
                let (d, s) = random::next_double(rng);
                rng = s;
                r = d.lt(six);
            }
            if !r {
                r = downbeat;
            }
            if !r && on_beat {
                let (d, s) = random::next_double(rng);
                rng = s;
                r = d.lt(four);
            }
            r
        };
        if new_section {
            let (o, s) = random_offset(sharpness, F32::from_bits(0x3A51_B717) /* 0.0008f */, rng);
            rng = s;
            section_offset = o;
            flow = !flow;
        }
        if is_slider(&pb.hit_objects[i]) {
            let (d, s) = random::next_double(rng);
            rng = s;
            if d.lt(F64::from_bits(0x3FE0_0000_0000_0000) /* 0.5 */) {
                flip_slider_in_place_horizontally(&mut pb.hit_objects[i]);
            }
        }
        if i == 0 {
            let (d1, s1) = random::next_double(rng);
            let (d2, s2) = random::next_double(s1);
            rng = s2;
            infos[0].distance_from_previous = d1.mul(F32::from_bits(0x43C0_0000) /* 384f */.to_f64()).div(D2).to_f32();
            infos[0].relative_angle = d2.mul(D2).mul(DPI).sub(DPI).to_f32();
        } else {
            let mut flow_change_offset = F0;
            let (one_time, s) = random_offset(sharpness, F32::from_bits(0x3B03_126F) /* 0.002f */, rng);
            rng = s;
            let started = combo_started(&pb.hit_objects, i);
            let mut apply_change = false;
            if started {
                let (d, s2) = random::next_double(rng);
                rng = s2;
                apply_change = d.lt(six);
            }
            if apply_change {
                let (o, s3) = random_offset(sharpness, F32::from_bits(0x3B03_126F) /* 0.002f */, rng);
                rng = s3;
                flow_change_offset = o;
                flow = !flow;
            }
            let dist = infos[i].distance_from_previous;
            let total_offset = section_offset.add(one_time).mul(dist).add(flow_change_offset.mul(playfield_diagonal().sub(dist)));
            infos[i].relative_angle = relative_target_angle(sharpness, dist, total_offset, flow);
        }
        i = i + 1;
    }
    reposition_hit_objects(&mut pb.hit_objects, &infos)
}
