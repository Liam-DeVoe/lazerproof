//! `OsuAutoGenerator` (used by Autopilot). Spec: `model/OsuModel/Sim/AutoGen.lean` at Lean commit `e0e8215`
//! (namespace `OsuModel.Sim.AutoGen`, plus `RateMod.apply`). The spec's
//! `M := ReaderT (List RateMod) (StateT G (Except String))` becomes `(mods: &[RateMod], g: &mut G) -> Result<_, SimErr>`.
//! Action lists are references into `G.heap` (`List<OsuAction>` aliasing).
use crate::beatmap::dotnet::insert_at;
use crate::float::{F32, F64};
use crate::net;
use crate::net::framework::{value_at_v, Easing};
use crate::net::osutk::{v2, v2_add, v2_length, v2_normalized, v2_scale, v2_sub, Vector2};
use crate::replay::frames::{act_contains, act_eq, act_push, Action, ActList, ACTLIST_EMPTY};
use crate::sim::geometry::{compare_d, curve_position_at};
use crate::net::basic::NetExn;
use crate::net::mathops::{f64_clamp, f64_round_digits};
use crate::sim::err::SimErr;
use crate::sim::mods::RateMod;
use crate::sim::playable::{Kind, Playable, SliderData, TopObj, HObj};
use alloc::vec::Vec;

pub const F64_0: F64 = F64::from_bits(0);
pub const F64_1: F64 = F64::from_bits(0x3FF0_0000_0000_0000);
pub const F32_0: F32 = F32::from_bits(0);
pub const F32_1: F32 = F32::from_bits(0x3F80_0000);

/// `RateMod.apply`
pub fn rate_mod_apply(m: RateMod, time: F64, rate: F64) -> Result<F64, NetExn> {
    match m {
        RateMod::Speed(s) => Ok(rate.mul(s)),
        RateMod::TimeRamp(i, f, b, ft) => {
            let amount = time.sub(b).div(net::max(F64_1, ft.sub(b)));
            let ramp = i.add(f.sub(i).mul(f64_clamp(amount, F64_0, F64_1)?));
            Ok(rate.mul(f64_round_digits(ramp, 2)?))
        }
        RateMod::Adaptive(i) => Ok(rate.mul(i)),
    }
}

/// `liftN`
pub fn lift_n(e: Result<F64, NetExn>) -> Result<F64, SimErr> {
    match e {
        Ok(v) => Ok(v),
        Err(x) => Err(SimErr::Net(x)),
    }
}

/// `AFrame`
#[derive(Clone, Copy)]
pub struct AFrame {
    pub time: F64,
    pub pos: Vector2,
    pub actions: usize,
    pub key_up: bool,
}

/// `spinnerCentre = (512f / 2, 384f / 2)`
pub fn spinner_centre() -> Vector2 {
    v2(F32::from_bits(0x4400_0000).div(F32::from_bits(0x4000_0000)), F32::from_bits(0x43C0_0000).div(F32::from_bits(0x4000_0000)))
}
/// `spinRadius = 50`
pub const SPIN_RADIUS: F32 = F32::from_bits(0x4248_0000);
/// `radsPerMillisecond`
pub const RADS_PER_MILLISECOND: F32 = F32::from_bits(0x3D4C_CCCE);
/// `keyUpDelay = 50`
pub const KEY_UP_DELAY: F64 = F64::from_bits(0x4049_0000_0000_0000);
/// `minSeparationForAlternating = 266`
pub const MIN_SEPARATION_FOR_ALTERNATING: F64 = F64::from_bits(0x4070_A000_0000_0000);
/// `1000.0 / 60`
pub const SIXTY_FRAME: F64 = F64::from_bits(0x4030_AAAA_AAAA_AAAB);

/// `G`
#[derive(Clone)]
pub struct G {
    pub frames: Vec<AFrame>,
    pub button_index: u64,
    pub heap: Vec<ActList>,
}

/// `applyModsToTimeDelta`
pub fn apply_mods_to_time_delta(mods: &[RateMod], start: F64, end_t: F64) -> Result<F64, SimErr> {
    let mut d = end_t.sub(start);
    let mut i: usize = 0;
    while i < mods.len() {
        let r = lift_n(rate_mod_apply(mods[i], start, F64_1))?;
        d = d.div(r);
        i += 1;
    }
    Ok(d)
}

/// `applyModsToRate`
pub fn apply_mods_to_rate(mods: &[RateMod], time: F64, rate: F64) -> Result<F64, SimErr> {
    let mut r = rate;
    let mut i: usize = 0;
    while i < mods.len() {
        r = lift_n(rate_mod_apply(mods[i], time, r))?;
        i += 1;
    }
    Ok(r)
}

/// `getFrameDelay`
pub fn get_frame_delay(mods: &[RateMod], time: F64) -> Result<F64, SimErr> {
    apply_mods_to_rate(mods, time, SIXTY_FRAME)
}

/// `findInsertionIndex`
pub fn find_insertion_index(fs: &[AFrame], t: F64) -> usize {
    let mut lo: i64 = 0;
    let mut hi: i64 = fs.len() as i64 - 1;
    let mut found: Option<i64> = None;
    let mut fuel: u64 = fs.len() as u64 + 2;
    while lo <= hi && fuel > 0 && found.is_none() {
        fuel -= 1;
        let i = lo + (hi - lo) / 2;
        let c = compare_d(fs[i as usize].time, t);
        if c == 0 {
            found = Some(i);
        } else if c < 0 {
            lo = i + 1;
        } else {
            hi = i - 1;
        }
    }
    match found {
        None => lo as usize,
        Some(i) => {
            let mut idx = i as usize;
            while idx < fs.len() && t.eq(fs[idx].time) {
                idx += 1;
            }
            idx
        }
    }
}

/// `addFrame`
pub fn add_frame(g: &mut G, f: AFrame) {
    let k = find_insertion_index(&g.frames, f.time);
    insert_at(&mut g.frames, k, f);
}

/// `lastFrame` (`frames.back!`)
pub fn last_frame(g: &G) -> AFrame {
    g.frames[g.frames.len() - 1]
}

/// `newList`
pub fn new_list(g: &mut G, xs: ActList) -> usize {
    let r = g.heap.len();
    g.heap.push(xs);
    r
}

/// `[a]`
pub fn single(a: Action) -> ActList {
    act_push(ACTLIST_EMPTY, a)
}

/// `circlePosition`
pub fn circle_position(t: F64, radius: F64) -> Vector2 {
    v2(t.cos().mul(radius).to_f32(), t.sin().mul(radius).to_f32())
}

/// `calcSpinnerStart`: (position, direction)
pub fn calc_spinner_start(prev_pos: Vector2) -> (Vector2, F32) {
    let centre = spinner_centre();
    let off = v2_sub(centre, prev_pos);
    let dist_from_centre = v2_length(off);
    let dist_to_tangent_point = dist_from_centre.mul(dist_from_centre).sub(SPIN_RADIUS.mul(SPIN_RADIUS)).sqrt();
    if SPIN_RADIUS.lt(dist_from_centre) {
        let angle = SPIN_RADIUS.div(dist_from_centre).asin();
        let dir = if F32_0.lt(angle) { F32_1.neg() } else { F32_1 };
        let x = off.x.mul(angle.cos()).sub(off.y.mul(angle.sin()));
        let y = x.mul(angle.sin()).add(off.y.mul(angle.cos()));
        let o = v2_normalized(v2(x, y));
        let o2 = v2_scale(o, dist_to_tangent_point);
        (v2_add(prev_pos, o2), dir)
    } else if F32_0.lt(v2_length(off)) {
        (v2_sub(centre, v2_scale(off, SPIN_RADIUS.div(v2_length(off)))), F32_1)
    } else {
        (v2_add(centre, v2(F32_0, SPIN_RADIUS.neg())), F32_1)
    }
}

/// `ofVec`
pub fn of_vec(p: crate::sim::basic::Vec2) -> Vector2 {
    v2(p.x, p.y)
}

/// `moveToHitObject`
pub fn move_to_hit_object(mods: &[RateMod], g: &mut G, h: &HObj, target: Vector2, easing: Easing) -> Result<(), SimErr> {
    let mut lf = last_frame(g);
    let reaction = apply_mods_to_rate(mods, h.start.sub(h.preempt), F64::from_bits(0x4059_0000_0000_0000))?; // 100
    let wait_time = h.start.sub(net::max(F64_0, h.preempt.sub(reaction)));
    let mut has_waited = false;
    if lf.time.lt(wait_time) {
        lf = AFrame { time: wait_time, pos: lf.pos, actions: lf.actions, key_up: false };
        has_waited = true;
        add_frame(g, lf);
    }
    let time_difference = apply_mods_to_time_delta(mods, lf.time, h.start)?;
    let n = g.frames.len();
    let last_last: Option<AFrame> = if n >= 2 { Some(g.frames[n - 2]) } else { None };
    if F64_0.le(time_difference) {
        match last_last {
            Some(ll) => {
                if lf.key_up && !has_waited {
                    let np = value_at_v(lf.time, lf.pos, target, ll.time, h.start, easing);
                    lf.pos = np;
                    let m = g.frames.len();
                    g.frames[m - 1] = lf;
                }
            }
            None => {}
        }
        let d0 = get_frame_delay(mods, lf.time)?;
        let (fuel, time) = move_frames(mods, g, h, lf, target, easing, lf.time.add(d0))?;
        if fuel == 0 && time.lt(h.start) {
            return Err(SimErr::AutogenFuel(0));
        }
    }
    if F64_0.le(time_difference) && time_difference.lt(MIN_SEPARATION_FOR_ALTERNATING) {
        g.button_index += 1;
    } else {
        g.button_index = 0;
    }
    Ok(())
}

/// the interpolated-frame loop of `moveToHitObject` (from the last frame `lf` towards `target`, first frame at
/// `time0`); returns the remaining fuel and the final time. (Every loop that can reject is the first statement of its
/// own function: Aeneas rejects early returns from a loop nested in a branch.)
pub fn move_frames(mods: &[RateMod], g: &mut G, h: &HObj, lf: AFrame, target: Vector2, easing: Easing, time0: F64) -> Result<(u32, F64), SimErr> {
    let mut fuel: u32 = 10000000;
    let mut time = time0;
    while time.lt(h.start) && fuel > 0 {
        fuel -= 1;
        time = move_frame_step(mods, g, h, lf, lf.pos, target, easing, time)?;
    }
    Ok((fuel, time))
}

/// one iteration of `move_frames`: adds the frame at `time`, returns the next time
pub fn move_frame_step(mods: &[RateMod], g: &mut G, h: &HObj, lf: AFrame, last_position: Vector2, target: Vector2, easing: Easing, time: F64) -> Result<F64, SimErr> {
    let cur = value_at_v(time, last_position, target, lf.time, h.start, easing);
    add_frame(g, AFrame { time: F64::from_i64(time.to_i32_sat() as i64), pos: cur, actions: lf.actions, key_up: false });
    let dt = get_frame_delay(mods, time)?;
    Ok(time.add(dt))
}

/// the frame-list surgery of `addClickFrames` (when the previous frame holds keys)
pub fn click_frames_fixup(g: &mut G, index: usize, prev_ref: usize, start_ref: usize, end_time: F64, action0: Action) -> Action {
    let mut action = action0;
    if act_contains(&g.heap[prev_ref], action) {
        action = if action == Action::Left { Action::Right } else { Action::Left };
        g.heap[start_ref] = single(action);
    }
    let end_index = find_insertion_index(&g.frames, end_time);
    let size = g.frames.len();
    if index + 1 < size {
        let cnt = if end_index > index + 1 { end_index - (index + 1) } else { 0 };
        let mut fs: Vec<AFrame> = Vec::new();
        let mut k: usize = 0;
        while k < size {
            if k < index + 1 || k >= index + 1 + cnt {
                fs.push(g.frames[k]);
            }
            k += 1;
        }
        g.frames = fs;
    }
    let fsize = g.frames.len();
    let mut j = index + 1;
    while j < fsize {
        let f = g.frames[j];
        if j < fsize - 1 || act_eq(&g.heap[f.actions], &g.heap[prev_ref]) {
            g.heap[f.actions] = single(action);
        }
        j += 1;
    }
    action
}

/// one iteration of the spinner loop of `addClickFrames`: adds the frame at `next_frame`; returns (angle, next frame time)
pub fn spinner_frame_step(mods: &[RateMod], g: &mut G, angle0: F32, previous_frame: F64, next_frame: F64, spinner_direction: F32, action: Action) -> Result<(F32, F64), SimErr> {
    let centre = spinner_centre();
    let t = apply_mods_to_time_delta(mods, previous_frame, next_frame)?.mul(spinner_direction.to_f64());
    let angle = angle0.add(t.to_f32().mul(RADS_PER_MILLISECOND));
    let pos = v2_add(centre, circle_position(angle.to_f64(), SPIN_RADIUS.to_f64()));
    let r = new_list(g, single(action));
    add_frame(g, AFrame { time: F64::from_i64(next_frame.to_i32_sat() as i64), pos, actions: r, key_up: false });
    let dt = get_frame_delay(mods, next_frame)?;
    Ok((angle, next_frame.add(dt)))
}

/// the frame loop of the spinner branch of `addClickFrames`; returns (fuel left, angle, previous frame, next frame)
pub fn spinner_frames(mods: &[RateMod], g: &mut G, angle0: F32, prev0: F64, next0: F64, end_t: F64, spinner_direction: F32, action: Action) -> Result<(u32, F32, F64, F64), SimErr> {
    let mut fuel: u32 = 10000000;
    let mut angle = angle0;
    let mut previous_frame = prev0;
    let mut next_frame = next0;
    while next_frame.lt(end_t) && fuel > 0 {
        fuel -= 1;
        let (a2, n2) = spinner_frame_step(mods, g, angle, previous_frame, next_frame, spinner_direction, action)?;
        angle = a2;
        previous_frame = next_frame;
        next_frame = n2;
    }
    Ok((fuel, angle, previous_frame, next_frame))
}

/// the spinner branch of `addClickFrames`; returns the end position
pub fn spinner_click_frames(mods: &[RateMod], g: &mut G, h: &HObj, start_position: Vector2, spinner_direction: F32, action: Action) -> Result<Vector2, SimErr> {
    let centre = spinner_centre();
    let difference = v2_sub(start_position, centre);
    let radius = v2_length(difference);
    let mut angle = if radius.eq(F32_0) { F32_0 } else { difference.y.atan2(difference.x) };
    let end_t = h.end_time;
    let d0 = get_frame_delay(mods, h.start)?;
    let (fuel, a1, previous_frame, next_frame) =
        spinner_frames(mods, g, angle, h.start, h.start.add(d0), end_t, spinner_direction, action)?;
    angle = a1;
    if fuel == 0 && next_frame.lt(end_t) {
        return Err(SimErr::AutogenFuel(1));
    }
    let t = apply_mods_to_time_delta(mods, previous_frame, end_t)?.mul(spinner_direction.to_f64());
    angle = angle.add(t.to_f32().mul(RADS_PER_MILLISECOND));
    let end_position = v2_add(centre, circle_position(angle.to_f64(), SPIN_RADIUS.to_f64()));
    let r = new_list(g, single(action));
    add_frame(g, AFrame { time: end_t, pos: end_position, actions: r, key_up: false });
    Ok(end_position)
}

/// one iteration of the slider loop of `addClickFrames`: adds the frame at `start + j`; returns the next `j`
pub fn slider_frame_step(mods: &[RateMod], g: &mut G, h: &HObj, sd: &SliderData, j: F64, action: Action) -> Result<F64, SimErr> {
    // `StackedPositionAt(t) = StackedPosition + CurvePositionAt(t)`
    let cp = curve_position_at(sd, j.div(sd.duration))?;
    let pos = v2_add(of_vec(h.stacked), of_vec(cp));
    let r = new_list(g, single(action));
    add_frame(g, AFrame { time: h.start.add(j), pos, actions: r, key_up: false });
    let dt = get_frame_delay(mods, h.start.add(j))?;
    Ok(j.add(dt))
}

/// the frame loop of the slider branch of `addClickFrames`; returns (fuel left, final `j`)
pub fn slider_frames(mods: &[RateMod], g: &mut G, h: &HObj, sd: &SliderData, j0: F64, action: Action) -> Result<(u32, F64), SimErr> {
    let mut fuel: u32 = 10000000;
    let mut j = j0;
    while j.lt(sd.duration) && fuel > 0 {
        fuel -= 1;
        j = slider_frame_step(mods, g, h, sd, j, action)?;
    }
    Ok((fuel, j))
}

/// the slider branch of `addClickFrames`
pub fn slider_click_frames(mods: &[RateMod], g: &mut G, o: &TopObj, stacked_end: Vector2, action: Action) -> Result<(), SimErr> {
    let h = &o.h;
    let sd = match &o.slider {
        Some(s) => s,
        None => {
            return Err(SimErr::NoSliderData);
        }
    };
    let j0 = get_frame_delay(mods, h.start)?;
    let (fuel, j) = slider_frames(mods, g, h, sd, j0, action)?;
    if fuel == 0 && j.lt(sd.duration) {
        return Err(SimErr::AutogenFuel(2));
    }
    let r = new_list(g, single(action));
    add_frame(g, AFrame { time: h.end_time, pos: stacked_end, actions: r, key_up: false });
    Ok(())
}

/// `addClickFrames`
pub fn add_click_frames(mods: &[RateMod], g: &mut G, o: &TopObj, start_position: Vector2, spinner_direction: F32, stacked_end: Vector2) -> Result<(), SimErr> {
    let h = &o.h;
    let mut action = if g.button_index % 2 == 0 { Action::Left } else { Action::Right };
    let start_ref = new_list(g, single(action));
    let start_frame = AFrame { time: h.start, pos: start_position, actions: start_ref, key_up: false };
    let h_end_time = h.end_time.add(KEY_UP_DELAY);
    let end_delay = if h.kind == Kind::Spinner { F64_1 } else { F64_0 };
    let end_ref = new_list(g, ACTLIST_EMPTY);
    let mut end_frame = AFrame { time: h_end_time.add(end_delay), pos: stacked_end, actions: end_ref, key_up: true };
    let ins = find_insertion_index(&g.frames, start_frame.time);
    if ins >= 1 {
        let index = ins - 1;
        let prev_ref = g.frames[index].actions;
        if g.heap[prev_ref].len != 0 {
            action = click_frames_fixup(g, index, prev_ref, start_ref, end_frame.time, action);
        }
    }
    add_frame(g, start_frame);
    if h.kind == Kind::Spinner {
        end_frame.pos = spinner_click_frames(mods, g, h, start_position, spinner_direction, action)?;
    } else if h.kind == Kind::Slider {
        slider_click_frames(mods, g, o, stacked_end, action)?;
    }
    if last_frame(g).time.le(end_frame.time) {
        add_frame(g, end_frame);
    }
    Ok(())
}

/// `StackedEndPosition` of `addHitObjectReplay`
pub fn stacked_end(o: &TopObj) -> Vector2 {
    if o.h.kind == Kind::Slider {
        let mut j: usize = 0;
        let mut found: Option<Vector2> = None;
        while j < o.nested.len() && found.is_none() {
            if o.nested[j].kind == Kind::Tail {
                found = Some(of_vec(o.nested[j].stacked));
            }
            j += 1;
        }
        match found {
            Some(p) => p,
            None => of_vec(o.h.stacked),
        }
    } else {
        of_vec(o.h.stacked)
    }
}

/// `addHitObjectReplay`
pub fn add_hit_object_replay(mods: &[RateMod], g: &mut G, o: &TopObj) -> Result<(), SimErr> {
    let h = &o.h;
    let se = stacked_end(o);
    let mut start_position = of_vec(h.stacked);
    let mut easing = Easing::Out;
    let mut spinner_direction = F32_1.neg();
    let mut skip = false;
    if h.kind == Kind::Spinner {
        match o.spinner {
            None => {
                skip = true;
            }
            Some(sp) => {
                if sp.spins_required == 0 {
                    skip = true;
                } else {
                    let lp = last_frame(g).pos;
                    let (sp2, dir) = calc_spinner_start(lp);
                    start_position = sp2;
                    spinner_direction = dir;
                    if SPIN_RADIUS.lt(v2_length(v2_sub(spinner_centre(), lp))) {
                        easing = Easing::In;
                    }
                }
            }
        }
    }
    if !skip {
        if g.frames.len() > 0 {
            move_to_hit_object(mods, g, h, start_position, easing)?;
        }
        add_click_frames(mods, g, o, start_position, spinner_direction, se)?;
    }
    Ok(())
}

/// `generate`
pub fn generate(pb: &Playable, mods: &[RateMod]) -> Result<Vec<AFrame>, SimErr> {
    if pb.objects.len() == 0 {
        Ok(Vec::new())
    } else {
        let mut g = G { frames: Vec::new(), button_index: 0, heap: Vec::new() };
        let r = new_list(&mut g, ACTLIST_EMPTY);
        let t0 = pb.objects[0].h.start.sub(F64::from_bits(0x4097_7000_0000_0000)); // 1500
        add_frame(&mut g, AFrame { time: t0, pos: v2(F32::from_bits(0x4380_0000), F32::from_bits(0x43FA_0000)), actions: r, key_up: false });
        generate_objects(pb, mods, &mut g)?;
        Ok(g.frames)
    }
}

/// the `for o in pb.objects do addHitObjectReplay o` loop of `generate`
pub fn generate_objects(pb: &Playable, mods: &[RateMod], g: &mut G) -> Result<(), SimErr> {
    let mut i: usize = 0;
    while i < pb.objects.len() {
        add_hit_object_replay(mods, g, &pb.objects[i])?;
        i += 1;
    }
    Ok(())
}
