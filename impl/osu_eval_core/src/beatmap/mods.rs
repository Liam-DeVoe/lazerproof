//! Port of `OsuModel/Beatmap/Mods.lean`: beatmap-pipeline effects of the osu! mods and the hook
//! dispatch (`ModConfig.hooks` / `ModConfig.allHooks`, whose `Mod` record of closures becomes the
//! `apply_*` functions below, consulted by `playable::get_playable_beatmap` in the spec's order).
use super::dotnet::{binary_search_f64, compare_f64, stable_sort_by, str_eq};
use super::errors::*;
use super::hit_object_parser::DecodeError;
use super::mod_random;
use super::names::*;
use super::mod_settings::{get_bool, get_float, get_int, get_opt_float, get_opt_int, ModConfig};
use super::mod_target_practice;
use super::objects::{end_time, is_slider, is_spinner, HitWindows, NestedKind, ObjectKind, OsuHitObject, SliderData};
use super::playable::{update_nested_positions, ModState, ObjRef, PlayableBeatmap};
use super::slider_path;
use super::types::{Difficulty, PathControlPoint};
use super::vector2::{self as v, Vec2};
use crate::float::{F32, F64};
use crate::net::mathops::f32_min;
use alloc::vec::Vec;

/// `OsuPlayfield.BASE_SIZE`
pub const BASE_W: F32 = F32::from_bits(0x4400_0000);
pub const BASE_H: F32 = F32::from_bits(0x43C0_0000);

/// `PathControlPoint.Position` setter (no-op when `==`); spec `Mods.setControlPointPos`
pub fn set_control_point_pos(old: Vec2, new: Vec2) -> Vec2 {
    if v::eq(new, old) { old } else { new }
}

/// `new PathControlPoint(position, type)`; spec `Mods.newControlPointPos`
pub fn new_control_point_pos(p: Vec2) -> Vec2 {
    set_control_point_pos(v::ZERO, p)
}

/// The control-point maps used with `modifySlider` (spec: the closure argument `f`).
#[derive(Clone, Copy)]
pub enum PointMap {
    /// `p => (-p.x, p.y)`
    NegX,
    /// `p => (p.x, -p.y)`
    NegY,
    /// `p => rotateVector(p, rotation)`
    Rotate(F32),
}

pub fn apply_point_map(f: PointMap, p: Vec2) -> Vec2 {
    match f {
        PointMap::NegX => Vec2 { x: p.x.neg(), y: p.y },
        PointMap::NegY => Vec2 { x: p.x, y: p.y.neg() },
        PointMap::Rotate(r) => mod_random::rotate_vector(p, r),
    }
}

/// `modifySlider(slider, f)`; spec `Mods.modifySlider`
pub fn modify_slider(f: PointMap, h: &mut OsuHitObject) {
    let changed = match &mut h.kind {
        ObjectKind::Slider(s) => {
            let old = &s.path.spec.control_points;
            let mut cps: Vec<PathControlPoint> = Vec::with_capacity(old.len());
            let mut i = 0;
            while i < old.len() {
                let c = new_control_point_pos(old[i].position);
                let p1 = set_control_point_pos(c, apply_point_map(f, c));
                cps.push(PathControlPoint { position: new_control_point_pos(p1), ptype: old[i].ptype });
                i = i + 1;
            }
            let ed = s.path.spec.expected_distance;
            let old_fuel_out = s.path.fuel_out;
            s.path = slider_path::of_control_points(cps, ed, true);
            // the old path's fuel flag is kept (spec `modifySlider`, D72)
            s.path.fuel_out = s.path.fuel_out || old_fuel_out;
            true
        }
        _ => false,
    };
    if changed {
        update_nested_positions(h);
    }
}

/// `OsuHitObject.Position` setter; spec `Mods.setPosition`
pub fn set_position(h: &mut OsuHitObject, p: Vec2) {
    h.position = p;
    update_nested_positions(h);
}

/// `ReflectHorizontallyAlongPlayfield`; spec `Mods.reflectHorizontally`
pub fn reflect_horizontally(h: &mut OsuHitObject) {
    let p = Vec2 { x: BASE_W.sub(h.position.x), y: h.position.y };
    set_position(h, p);
    modify_slider(PointMap::NegX, h);
}

/// `ReflectVerticallyAlongPlayfield`; spec `Mods.reflectVertically`
pub fn reflect_vertically(h: &mut OsuHitObject) {
    let p = Vec2 { x: h.position.x, y: BASE_H.sub(h.position.y) };
    set_position(h, p);
    modify_slider(PointMap::NegY, h);
}

const F_HALF: F32 = F32::from_bits(0x3F00_0000);
/// `ModHardRock.ADJUST_RATIO = 1.4f`
pub const HR_RATIO: F32 = F32::from_bits(0x3FB3_3333);
/// `1.3f`
pub const HR_CS_RATIO: F32 = F32::from_bits(0x3FA6_6666);
const F10: F32 = F32::from_bits(0x4120_0000);

/// `ModEasy` + `OsuModEasy.ApplyToDifficulty`; spec `Mods.easyDifficulty`
pub fn easy_difficulty(d: Difficulty) -> Difficulty {
    let mut r = d;
    r.circle_size = d.circle_size.mul(F_HALF);
    r.approach_rate = d.approach_rate.mul(F_HALF);
    r.drain_rate = d.drain_rate.mul(F_HALF);
    r.overall_difficulty = d.overall_difficulty.mul(F_HALF);
    r
}

/// `ModHardRock` + `OsuModHardRock.ApplyToDifficulty`; spec `Mods.hardRockDifficulty`
pub fn hard_rock_difficulty(d: Difficulty) -> Difficulty {
    let mut r = d;
    r.drain_rate = f32_min(d.drain_rate.mul(HR_RATIO), F10);
    r.overall_difficulty = f32_min(d.overall_difficulty.mul(HR_RATIO), F10);
    r.circle_size = f32_min(d.circle_size.mul(HR_CS_RATIO), F10);
    r.approach_rate = f32_min(d.approach_rate.mul(HR_RATIO), F10);
    r
}

/// `OsuModDifficultyAdjust.ApplySettings`; spec `Mods.difficultyAdjust`
pub fn difficulty_adjust(m: &ModConfig, d: Difficulty) -> Difficulty {
    let mut r = d;
    match get_opt_float(m, K_DRAIN_RATE) {
        Some(x) => r.drain_rate = x,
        None => {}
    }
    match get_opt_float(m, K_OVERALL_DIFFICULTY) {
        Some(x) => r.overall_difficulty = x,
        None => {}
    }
    match get_opt_float(m, K_CIRCLE_SIZE) {
        Some(x) => r.circle_size = x,
        None => {}
    }
    match get_opt_float(m, K_APPROACH_RATE) {
        Some(x) => r.approach_rate = x,
        None => {}
    }
    r
}

/// `new StrictTrackingSlider(original)`; spec `Mods.strictTrackingSlider`
pub fn strict_tracking_slider(h: &OsuHitObject) -> OsuHitObject {
    match &h.kind {
        ObjectKind::Slider(s) => {
            let sd = SliderData {
                path: slider_path::compute(s.path.spec.clone()),
                repeat_count: s.repeat_count,
                velocity: F64::from_bits(0),
                tick_distance: F64::from_bits(0),
                tick_distance_multiplier: s.tick_distance_multiplier,
                slider_velocity_multiplier: s.slider_velocity_multiplier,
                generate_ticks: true,
                classic_slider_behaviour: false,
                strict_tracking: true,
            };
            let mut o = super::objects::object_default(ObjectKind::Slider(sd), h.start_time, h.position);
            o.new_combo = h.new_combo;
            o.combo_offset = h.combo_offset;
            o
        }
        _ => h.clone(),
    }
}

/// `OsuModStrictTracking.ApplyToBeatmap`; spec `Mods.strictTracking`
pub fn strict_tracking(pb: &mut PlayableBeatmap) {
    let mut i = 0;
    while i < pb.hit_objects.len() {
        if is_slider(&pb.hit_objects[i]) {
            pb.hit_objects[i] = strict_tracking_slider(&pb.hit_objects[i]);
        }
        i = i + 1;
    }
}

/// `OsuModClassic.ApplyToHitObject`; spec `Mods.classicHitObject`
pub fn classic_hit_object(val: bool, h: &mut OsuHitObject) {
    let is_s = match &mut h.kind {
        ObjectKind::Slider(s) => {
            s.classic_slider_behaviour = val;
            true
        }
        _ => false,
    };
    if is_s {
        let mut i = 0;
        while i < h.nested.len() {
            match h.nested[i].kind {
                NestedKind::Head | NestedKind::Tail => h.nested[i].classic_slider_behaviour = val,
                _ => {}
            }
            i = i + 1;
        }
    }
}

/// `OsuModMirror.ApplyToHitObject`; spec `Mods.mirror`
pub fn mirror(reflection: i32, h: &mut OsuHitObject) {
    if reflection == 0 {
        reflect_horizontally(h);
    } else if reflection == 1 {
        reflect_vertically(h);
    } else if reflection == 2 {
        reflect_horizontally(h);
        reflect_vertically(h);
    }
}

/// `getFirstAdjustableObjectRecursive`; spec `Mods.firstAdjustableObject`
pub fn first_adjustable_object(pb: &PlayableBeatmap, skip_spinners: bool) -> Option<ObjRef> {
    let mut res: Option<ObjRef> = None;
    let mut i = 0;
    while res.is_none() && i < pb.hit_objects.len() {
        if !(skip_spinners && is_spinner(&pb.hit_objects[i])) {
            res = Some(ObjRef { index: i, nested: None, epoch: pb.epoch });
        } else {
            res = first_adjustable_nested(pb, i, skip_spinners);
        }
        i = i + 1;
    }
    res
}

/// the nested-object part of `getFirstAdjustableObjectRecursive` for object `i`
pub fn first_adjustable_nested(pb: &PlayableBeatmap, i: usize, skip_spinners: bool) -> Option<ObjRef> {
    let n = pb.hit_objects[i].nested.len();
    let mut res: Option<ObjRef> = None;
    let mut j = 0;
    while res.is_none() && j < n {
        let k = pb.hit_objects[i].nested[j].kind;
        let is_spin_tick = k == NestedKind::SpinnerTick || k == NestedKind::SpinnerBonusTick;
        if !(skip_spinners && is_spin_tick) {
            res = Some(ObjRef { index: i, nested: Some(j), epoch: pb.epoch });
        }
        j = j + 1;
    }
    res
}

/// spec `Mods.recordFirstObject`
pub fn record_first_object(skip_spinners: bool, idx: usize, pb: &mut PlayableBeatmap) {
    let r = first_adjustable_object(pb, skip_spinners);
    pb.mod_states.push((idx, ModState::FirstObject(r)));
}

/// `FADE_IN_DURATION_MULTIPLIER = 0.4`
pub const FADE_IN_DURATION_MULTIPLIER: F64 = F64::from_bits(0x3FD9_9999_9999_999A);

/// `OsuModHidden.applyFadeInAdjustment`; spec `Mods.hiddenFadeIn`
pub fn hidden_fade_in(h: &mut OsuHitObject) {
    if !is_slider(h) {
        h.time_fade_in = h.time_preempt.mul(FADE_IN_DURATION_MULTIPLIER);
    }
    let mut i = 0;
    while i < h.nested.len() {
        h.nested[i].time_fade_in = h.nested[i].time_preempt.mul(FADE_IN_DURATION_MULTIPLIER);
        i = i + 1;
    }
}

/// `OsuModFreezeFrame.ApplyToBeatmap`; spec `Mods.freezeFrame`
pub fn freeze_frame(pb: &mut PlayableBeatmap) {
    let mut last_nc = F64::from_bits(0);
    let mut i = 0;
    while i < pb.hit_objects.len() {
        let h = &mut pb.hit_objects[i];
        if h.new_combo {
            last_nc = h.start_time;
        }
        if !is_spinner(h) {
            h.time_preempt = h.time_preempt.add(h.start_time.sub(last_nc));
        }
        let mut repeat_count: usize = 0;
        let mut j = 0;
        while j < h.nested.len() {
            let n = &mut h.nested[j];
            match n.kind {
                NestedKind::Tick => {}
                NestedKind::Repeat => {
                    if repeat_count > 2 {
                    } else {
                        n.time_preempt = n.time_preempt.add(n.start_time.sub(last_nc));
                        repeat_count = repeat_count + 1;
                    }
                }
                _ => {
                    n.time_preempt = n.time_preempt.add(n.start_time.sub(last_nc));
                }
            }
            j = j + 1;
        }
        i = i + 1;
    }
}

/// `Enumerable.Max` over doubles (NaN smallest, first of ties); spec `Mods.linqMaxF64`
pub fn linq_max_f64(xs: &[F64]) -> F64 {
    let mut i = 0;
    let mut val = xs[0];
    while val.is_nan() && i + 1 < xs.len() {
        i = i + 1;
        val = xs[i];
    }
    let mut j = i + 1;
    while j < xs.len() {
        if val.lt(xs[j]) {
            val = xs[j];
        }
        j = j + 1;
    }
    val
}

/// `GetLastObjectTime()`; spec `Mods.lastObjectTime`
pub fn last_object_time(pb: &PlayableBeatmap) -> F64 {
    let mut ts: Vec<F64> = Vec::with_capacity(pb.hit_objects.len());
    let mut i = 0;
    while i < pb.hit_objects.len() {
        ts.push(end_time(&pb.hit_objects[i]));
        i = i + 1;
    }
    linq_max_f64(&ts)
}

/// `FINAL_RATE_PROGRESS = 0.75f`
pub const FINAL_RATE_PROGRESS: F32 = F32::from_bits(0x3F40_0000);

/// `ModTimeRamp.ApplyToBeatmap`; spec `Mods.timeRamp`
pub fn time_ramp(idx: usize, pb: &mut PlayableBeatmap) {
    let n = pb.hit_objects.len();
    let first = if n > 0 { pb.hit_objects[0].start_time } else { F64::from_bits(0) };
    let last_end = if n > 0 { last_object_time(pb) } else { F64::from_bits(0) };
    let fin = first.add(FINAL_RATE_PROGRESS.to_f64().mul(last_end.sub(first)));
    pb.mod_states.push((idx, ModState::TimeRamp(first, fin)));
}

/// `ModAdaptiveSpeed.ApplyToBeatmap`; spec `Mods.adaptiveSpeed`
pub fn adaptive_speed(idx: usize, pb: &mut PlayableBeatmap) {
    let mut objs: Vec<(ObjRef, F64)> = Vec::new();
    let mut i = 0;
    while i < pb.hit_objects.len() {
        let h = &pb.hit_objects[i];
        let has_windows = match h.hit_windows {
            Some(HitWindows::Empty) => false,
            _ => true,
        };
        if has_windows {
            objs.push((ObjRef { index: i, nested: None, epoch: pb.epoch }, end_time(h)));
        }
        let mut j = 0;
        while j < h.nested.len() {
            let has_w = match h.nested[j].hit_windows {
                HitWindows::Empty => false,
                _ => true,
            };
            if has_w {
                objs.push((ObjRef { index: i, nested: Some(j), epoch: pb.epoch }, h.nested[j].start_time));
            }
            j = j + 1;
        }
        i = i + 1;
    }
    let mut sorted: Vec<F64> = Vec::with_capacity(objs.len());
    let mut k = 0;
    while k < objs.len() {
        sorted.push(objs[k].1);
        k = k + 1;
    }
    stable_sort_by(&mut sorted);
    let mut end_times: Vec<F64> = Vec::new();
    let mut m = 0;
    while m < sorted.len() {
        let t = sorted[m];
        if end_times.len() == 0 || compare_f64(end_times[end_times.len() - 1], t) != 0 {
            end_times.push(t);
        }
        m = m + 1;
    }
    let mut entries: Vec<(ObjRef, F64)> = Vec::new();
    let mut q = 0;
    while q < objs.len() {
        let (r, t) = objs[q];
        let b = binary_search_f64(&end_times, t);
        let index = (if b < 0 { -b - 1 } else { b }) - 1;
        if index >= 0 {
            entries.push((r, end_times[index as usize]));
        }
        q = q + 1;
    }
    pb.mod_states.push((idx, ModState::PrecedingEndTimes(entries)));
}

// ----------------------------------------------------------------- hook dispatch (`allHooks`)

fn acr_is(m: &ModConfig, lit: &[u8]) -> bool {
    m.known && str_eq(&m.acronym, lit)
}

/// `IApplicableAfterBeatmapConversion` (ST)
pub fn apply_after_conversion(m: &ModConfig, pb: &mut PlayableBeatmap) {
    if acr_is(m, b"ST") {
        strict_tracking(pb);
    }
}

/// `IApplicableToDifficulty` (EZ, HR, DA, TP)
pub fn apply_to_difficulty(m: &ModConfig, d: Difficulty) -> Difficulty {
    if acr_is(m, b"EZ") {
        easy_difficulty(d)
    } else if acr_is(m, b"HR") {
        hard_rock_difficulty(d)
    } else if acr_is(m, b"DA") {
        difficulty_adjust(m, d)
    } else if acr_is(m, b"TP") {
        let mut r = d;
        r.approach_rate = d.approach_rate.mul(F_HALF);
        r
    } else {
        d
    }
}

/// whether the mod implements `IApplicableToHitObject` (HR, MR, CL)
pub fn has_apply_to_hit_object(m: &ModConfig) -> bool {
    acr_is(m, b"HR") || acr_is(m, b"MR") || acr_is(m, b"CL")
}

/// `IApplicableToHitObject.ApplyToHitObject` (HR, MR, CL)
pub fn apply_to_hit_object(m: &ModConfig, h: &mut OsuHitObject) {
    if acr_is(m, b"HR") {
        reflect_vertically(h);
    } else if acr_is(m, b"MR") {
        mirror(get_int(m, K_REFLECTION), h);
    } else if acr_is(m, b"CL") {
        classic_hit_object(get_bool(m, K_NO_SLIDER_HEAD_ACCURACY), h);
    }
}

/// `IApplicableToBeatmap.ApplyToBeatmap` with the mod index
pub fn apply_to_beatmap(m: &ModConfig, i: usize, pb: &mut PlayableBeatmap) -> Result<(), DecodeError> {
    if acr_is(m, b"HD") {
        record_first_object(true, i, pb);
        let mut k = 0;
        while k < pb.hit_objects.len() {
            hidden_fade_in(&mut pb.hit_objects[k]);
            k = k + 1;
        }
    } else if acr_is(m, b"TC") {
        record_first_object(true, i, pb);
    } else if acr_is(m, b"GR") || acr_is(m, b"DF") || acr_is(m, b"SI") || acr_is(m, b"TR") || acr_is(m, b"WG") || acr_is(m, b"DP") {
        record_first_object(false, i, pb);
    } else if acr_is(m, b"FR") {
        freeze_frame(pb);
    } else if acr_is(m, b"WU") || acr_is(m, b"WD") {
        time_ramp(i, pb);
    } else if acr_is(m, b"AS") {
        adaptive_speed(i, pb);
    } else if acr_is(m, b"RD") {
        match get_opt_int(m, K_SEED) {
            Some(s) => return mod_random::apply(s, get_float(m, K_ANGLE_SHARPNESS), pb),
            None => return Err(DecodeError::Msg(M_RANDOM_WITHOUT_A_SEED_IS_NOT_REPRODUCIBL)),
        }
    } else if acr_is(m, b"TP") {
        match get_opt_int(m, K_SEED) {
            Some(s) => return mod_target_practice::apply(s, i, pb),
            None => return Err(DecodeError::Msg(M_TARGET_PRACTICE_WITHOUT_A_SEED_IS_NOT_RE)),
        }
    }
    Ok(())
}
