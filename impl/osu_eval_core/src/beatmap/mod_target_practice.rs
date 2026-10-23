//! Port of `OsuModel/Beatmap/ModTargetPractice.lean`: Target Practice beatmap generation.
use super::control_points::{binary_search_idx, timing_point_at, ControlPointInfo};
use super::dotnet::stable_sort_by;
use super::errors::*;
use super::hit_object_parser::DecodeError;
use super::mod_random::{atan2f, rotate_away_from_edge, two_pi, BASE_SIZE, CENTRE, PI};
use super::mods::{last_object_time, record_first_object};
use super::objects::{apply_defaults, duration, end_time, is_slider, object_default, radius, span_count, ObjectKind, OsuHitObject};
use super::playable::{ModState, PlayableBeatmap};
use super::types::BreakPeriod;
use super::vector2::{self as v, Vec2};
use crate::float::{F32, F64};
use crate::net::mathops::{f32_min, f64_round};
use crate::net::random::{self, State};
use alloc::vec::Vec;

/// `timing_precision = 1`
pub const TIMING_PRECISION: F64 = F64::from_bits(0x3FF0_0000_0000_0000);

/// `Precision.AlmostBigger(a, b, 1)`; spec `TargetPractice.almostBigger`
pub fn almost_bigger(a: F64, b: F64) -> bool {
    b.sub(TIMING_PRECISION).lt(a)
}
/// `Precision.DefinitelyBigger(a, b, 1)`; spec `TargetPractice.definitelyBigger`
pub fn definitely_bigger(a: F64, b: F64) -> bool {
    b.lt(a.sub(TIMING_PRECISION))
}

/// index of `TimingPointAt(time)` (`None` = DEFAULT); spec `TargetPractice.timingPointIndexAt`
pub fn timing_point_index_at(cpi: &ControlPointInfo, time: F64) -> Option<usize> {
    match binary_search_idx(&cpi.timing_points, time) {
        Some(i) => Some(i),
        None => {
            if cpi.timing_points.len() > 0 { Some(0) } else { None }
        }
    }
}

/// `isInsideBreakPeriod`; spec `TargetPractice.insideBreak`
pub fn inside_break(orig: &[OsuHitObject], breaks: &[BreakPeriod], time: F64) -> bool {
    let mut any = false;
    let mut k = 0;
    while !any && k < breaks.len() {
        let b = breaks[k];
        let mut first_after: Option<usize> = None;
        let mut j = 0;
        while first_after.is_none() && j < orig.len() {
            if almost_bigger(orig[j].start_time, b.end_time) {
                first_after = Some(j);
            }
            j = j + 1;
        }
        let ok2 = match first_after {
            None => true,
            Some(o) => definitely_bigger(orig[o].start_time, time),
        };
        if almost_bigger(time, b.start_time) && ok2 {
            any = true;
        }
        k = k + 1;
    }
    any
}

const D2: F64 = F64::from_bits(0x4000_0000_0000_0000);

/// `generateBeats(beatmap, originalHitObjects)`; spec `TargetPractice.generateBeats`
pub fn generate_beats(pb: &PlayableBeatmap, orig: &[OsuHitObject]) -> Vec<F64> {
    let cpi = &pb.control_points;
    let start_time = pb.hit_objects[0].start_time;
    let end_t = last_object_time(pb);
    let mut beats: Vec<F64> = Vec::new();
    let mut ti = 0;
    while ti < cpi.timing_points.len() {
        let tp = cpi.timing_points[ti];
        if !definitely_bigger(tp.time, end_t) {
            let mut i: i32 = 0;
            let mut cur = tp.time;
            let mut fuel: u64 = 0;
            let mut go = true;
            while go && fuel < 1000000000 {
                let same = match timing_point_index_at(cpi, cur) {
                    Some(x) => x == ti,
                    None => false,
                };
                if definitely_bigger(cur, end_t) || !same {
                    go = false;
                } else {
                    beats.push(cur.floor());
                    i = i.wrapping_add(1);
                    cur = tp.time.add(F64::from_i64(i as i64).mul(tp.beat_length));
                    fuel = fuel + 1;
                }
            }
        }
        ti = ti + 1;
    }
    let mut b1: Vec<F64> = Vec::new();
    let mut k = 0;
    while k < beats.len() {
        if almost_bigger(beats[k], start_time) {
            b1.push(beats[k]);
        }
        k = k + 1;
    }
    let mut b2: Vec<F64> = Vec::new();
    k = 0;
    while k < b1.len() {
        if !inside_break(orig, &pb.breaks, b1[k]) {
            b2.push(b1[k]);
        }
        k = k + 1;
    }
    if b2.len() < 2 {
        return b2;
    }
    // backwards removal of beats too close to the next kept one (kept in reverse order)
    let mut kept_rev: Vec<F64> = Vec::new();
    kept_rev.push(b2[b2.len() - 1]);
    let mut m = 0;
    while m < b2.len() - 1 {
        let i = b2.len() - 2 - m;
        let beat = b2[i];
        let next = kept_rev[kept_rev.len() - 1];
        if definitely_bigger(next.sub(beat), timing_point_at(cpi, beat).beat_length.div(D2)) {
            kept_rev.push(beat);
        }
        m = m + 1;
    }
    let mut out: Vec<F64> = Vec::with_capacity(kept_rev.len());
    let mut r = kept_rev.len();
    while r > 0 {
        r = r - 1;
        out.push(kept_rev[r]);
    }
    out
}

/// `fixComboInfo(hitObjects, originalHitObjects)`; spec `TargetPractice.fixComboInfo`
pub fn fix_combo_info(hos: &mut Vec<OsuHitObject>, orig: &[OsuHitObject]) {
    let mut i = 0;
    while i < hos.len() {
        let mut closest: Option<usize> = None;
        let mut j = orig.len();
        while closest.is_none() && j > 0 {
            j = j - 1;
            if almost_bigger(hos[i].start_time, orig[j].start_time) {
                closest = Some(j);
            }
        }
        hos[i].combo_index = match closest {
            Some(c) => orig[c].combo_index,
            None => 0,
        };
        i = i + 1;
    }
    let mut keys: Vec<i32> = Vec::new();
    i = 0;
    while i < hos.len() {
        let ci = hos[i].combo_index;
        let mut seen = false;
        let mut k = 0;
        while k < keys.len() {
            if keys[k] == ci {
                seen = true;
            }
            k = k + 1;
        }
        if !seen {
            keys.push(ci);
        }
        i = i + 1;
    }
    // `idxs` are computed on the mapped (not yet renumbered) combo indices
    let mapped: Vec<i32> = {
        let mut m: Vec<i32> = Vec::with_capacity(hos.len());
        let mut q = 0;
        while q < hos.len() {
            m.push(hos[q].combo_index);
            q = q + 1;
        }
        m
    };
    let mut g: i32 = 0;
    let mut ki = 0;
    while ki < keys.len() {
        renumber_combo(hos, &mapped, keys[ki], g);
        g = g.wrapping_add(1);
        ki = ki + 1;
    }
}

fn set_combo(h: &mut OsuHitObject, g: i32, jj: i32) {
    h.combo_index = g;
    h.index_in_current_combo = jj;
}

/// first `k >= from` with `mapped[k] == key` (`mapped.len()` if none)
pub fn next_match(mapped: &[i32], key: i32, from: usize) -> usize {
    let mut k = from;
    let mut found = false;
    while !found && k < mapped.len() {
        if mapped[k] == key {
            found = true;
        } else {
            k = k + 1;
        }
    }
    k
}

/// one `GroupBy` group of `fixComboInfo`: objects whose (mapped) combo index is `key` get combo
/// `g`, consecutive `IndexInCurrentCombo`, `NewCombo` on the first, `LastInCombo` on the last.
pub fn renumber_combo(hos: &mut Vec<OsuHitObject>, mapped: &[i32], key: i32, g: i32) {
    let first = next_match(mapped, key, 0);
    let mut jj: i32 = 0;
    let mut last: usize = 0;
    let mut k = first;
    while k < mapped.len() {
        set_combo(&mut hos[k], g, jj);
        jj = jj.wrapping_add(1);
        last = k;
        k = next_match(mapped, key, k + 1);
    }
    if first < mapped.len() {
        hos[first].new_combo = true;
    }
    hos[last].last_in_combo = true;
}

const D1: F64 = F64::from_bits(0x3FF0_0000_0000_0000);

/// `nodeIndexFromTime(curve, timeSinceStart)`; spec `TargetPractice.nodeIndexFromTime`
pub fn node_index_from_time(h: &OsuHitObject, time_since_start: F64) -> i32 {
    let sc: i32 = match &h.kind {
        ObjectKind::Slider(s) => span_count(s),
        _ => 1,
    };
    let span_duration = duration(h).div(F64::from_i64(sc as i64));
    let node_index = time_since_start.div(span_duration);
    if node_index.sub(f64_round(node_index)).abs().le(D1) { f64_round(node_index).to_i32_sat() } else { -1 }
}

fn sample_pred(o: &OsuHitObject, t: F64) -> bool {
    if t.sub(o.start_time).abs().le(TIMING_PRECISION) {
        true
    } else if !is_slider(o) {
        false
    } else if !almost_bigger(t, o.start_time) || !almost_bigger(end_time(o), t) {
        false
    } else {
        node_index_from_time(o, t.sub(o.start_time)) != -1
    }
}

/// `addHitSamples` lookups (which can throw); spec `TargetPractice.checkHitSamples`
pub fn check_hit_samples(orig: &[OsuHitObject], beats: &[F64]) -> Result<(), DecodeError> {
    let mut bi = 0;
    while bi < beats.len() {
        let t = beats[bi];
        let mut found: Option<usize> = None;
        let mut j = 0;
        while found.is_none() && j < orig.len() {
            if sample_pred(&orig[j], t) {
                found = Some(j);
            }
            j = j + 1;
        }
        match found {
            Some(oi) => {
                let o = &orig[oi];
                match &o.kind {
                    ObjectKind::Slider(s) => {
                        let i = node_index_from_time(o, t.sub(o.start_time));
                        if i < 0 || i > s.repeat_count.wrapping_add(1) {
                            return Err(DecodeError::Msg(M_ARGUMENTOUTOFRANGEEXCEPTION_NODESAMPLES));
                        }
                    }
                    _ => {}
                }
            }
            None => {
                let mut preceding: i64 = -1;
                let mut k = orig.len();
                let mut done = false;
                while !done && k > 0 {
                    k = k - 1;
                    if orig[k].start_time.lt(t) {
                        preceding = k as i64;
                        done = true;
                    }
                }
                if preceding != (orig.len() as i64) - 1 && preceding == -1 {
                    return Err(DecodeError::Msg(M_ARGUMENTOUTOFRANGEEXCEPTION_GETCLOSESTHI));
                }
            }
        }
        bi = bi + 1;
    }
    Ok(())
}

pub const MAX_BASE_DISTANCE: F32 = F32::from_bits(0x43A6_8000) /* 333f */;
pub const DISTANCE_CAP: F32 = F32::from_bits(0x43BE_0000) /* 380f */;
pub const EDGE_ROTATION_MULTIPLIER: F32 = F32::from_bits(0x3F40_0000) /* 0.75f */;
pub const OVERLAP_CHECK_COUNT: usize = 5;

/// `clampToPlayfield(obj)`; spec `TargetPractice.clampToPlayfield`
pub fn clamp_to_playfield(p: Vec2, rad: F32) -> Vec2 {
    let y = if p.y.lt(rad) { rad } else if BASE_SIZE.y.sub(rad).lt(p.y) { BASE_SIZE.y.sub(rad) } else { p.y };
    let x = if p.x.lt(rad) { rad } else if BASE_SIZE.x.sub(rad).lt(p.x) { BASE_SIZE.x.sub(rad) } else { p.x };
    Vec2 { x, y }
}

/// `mapRange`; spec `TargetPractice.mapRange`
pub fn map_range(value: F32, from_low: F32, from_high: F32, to_low: F32, to_high: F32) -> F32 {
    value.sub(from_low).mul(to_high.sub(to_low)).div(from_high.sub(from_low)).add(to_low)
}

/// `rng.NextSingle()` as lazer computes it here (`(float)(NextDouble() * 1f)`)
fn next_single(r: State) -> (F32, State) {
    let (d, r2) = random::next_double(r);
    (d.mul(F32::from_bits(0x3F80_0000) /* 1f */.to_f64()).to_f32(), r2)
}

/// `randomizeCirclePos(hitObjects, rng)`; spec `TargetPractice.randomizeCirclePos`
pub fn randomize_circle_pos(hos: &mut Vec<OsuHitObject>, rng0: State) {
    if hos.len() == 0 {
        return;
    }
    let tp = two_pi();
    let mut rng = rng0;
    let (ns0, r0) = next_single(rng);
    rng = r0;
    let mut direction = tp.mul(ns0);
    let max_combo_index = hos[hos.len() - 1].combo_index;
    let d2 = D2;
    let mut i = 0;
    while i < hos.len() {
        let last_pos = if i == 0 { CENTRE } else { hos[i - 1].position };
        let obj_radius = radius(&hos[i]);
        let rad = obj_radius.to_f32();
        let mut distance = if max_combo_index == 0 {
            rad
        } else {
            map_range(F32::from_i64(hos[i].combo_index as i64), F32::from_bits(0), F32::from_i64(max_combo_index as i64), rad, MAX_BASE_DISTANCE)
        };
        if hos[i].new_combo {
            distance = distance.mul(F32::from_bits(0x3FC0_0000) /* 1.5f */);
        }
        if hos[i].kiai {
            distance = distance.mul(F32::from_bits(0x3F99_999A) /* 1.2f */);
        }
        distance = f32_min(DISTANCE_CAP, distance);
        let lo = if i >= OVERLAP_CHECK_COUNT { i - OVERLAP_CHECK_COUNT } else { 0 };
        let mut preceding: Vec<Vec2> = Vec::new();
        let mut q = lo;
        while q < i {
            preceding.push(hos[q].position);
            q = q + 1;
        }
        let mut try_count: u64 = 0;
        let mut pos = hos[i].position;
        let mut fuel = 0;
        let mut go = true;
        while go && fuel < 100000 {
            if try_count > 0 {
                let (ns, r) = next_single(rng);
                rng = r;
                direction = tp.mul(ns);
            }
            let rel0 = Vec2 { x: distance.mul(direction.cos()), y: distance.mul(direction.sin()) };
            let rel = rotate_away_from_edge(last_pos, rel0, EDGE_ROTATION_MULTIPLIER);
            direction = atan2f(rel.y, rel.x);
            pos = clamp_to_playfield(v::add(last_pos, rel), rad);
            try_count = try_count + 1;
            if try_count % 10 == 0 {
                distance = distance.mul(F32::from_bits(0x3F66_6666) /* 0.9f */);
            }
            let mut overlap = false;
            let mut z = 0;
            while z < preceding.len() {
                if v::distance(preceding[z], pos).to_f64().lt(obj_radius.mul(d2)) {
                    overlap = true;
                }
                z = z + 1;
            }
            if !(obj_radius.mul(d2).le(distance.to_f64()) && overlap) {
                go = false;
            }
            fuel = fuel + 1;
        }
        hos[i].position = pos;
        if hos[i].last_in_combo {
            let (ns, r) = next_single(rng);
            rng = r;
            direction = tp.mul(ns);
        } else {
            let (ns, r) = next_single(rng);
            rng = r;
            direction = direction.add(distance.div(DISTANCE_CAP).mul(ns.mul(tp).sub(PI)));
        }
        i = i + 1;
    }
}

/// `OsuModTargetPractice.ApplyToBeatmap` (+ `FirstObject`); spec `TargetPractice.apply`
pub fn apply(seed: i32, idx: usize, pb: &mut PlayableBeatmap) -> Result<(), DecodeError> {
    let rng = random::create(seed);
    if pb.hit_objects.len() == 0 {
        pb.mod_states.push((idx, ModState::FirstObject(None)));
        return Ok(());
    }
    let mut orig = pb.hit_objects.clone();
    stable_sort_by(&mut orig);
    let beats = generate_beats(pb, &orig);
    let mut hos: Vec<OsuHitObject> = Vec::with_capacity(beats.len());
    let mut k = 0;
    let mut err: Option<DecodeError> = None;
    while err.is_none() && k < beats.len() {
        let mut c = object_default(ObjectKind::Circle, F64::from_bits(0), v::ZERO);
        let r = apply_defaults(&pb.control_points, &pb.difficulty, &mut c);
        match r {
            Ok(_) => {
                c.start_time = beats[k];
                hos.push(c);
            }
            Err(e) => err = Some(e),
        }
        k = k + 1;
    }
    if let Some(e) = err {
        return Err(e);
    }
    tri!(check_hit_samples(&orig, &beats));
    fix_combo_info(&mut hos, &orig);
    randomize_circle_pos(&mut hos, rng);
    pb.hit_objects = hos;
    pb.epoch = pb.epoch + 1;
    record_first_object(false, idx, pb);
    Ok(())
}
