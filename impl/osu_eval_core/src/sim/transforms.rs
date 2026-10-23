//! osu-framework transform system (M7). Spec: `model/OsuModel/Sim/Transforms.lean` at Lean commit `7cffd29`
//! (`Member`, `Tr`, `Tracker`, `TObj`, `trackerUpdate`, `updateTransforms`, `addTransform`, `clearState`,
//! `TransformSequence` helpers, `latestEnd`). Functional updates `TObj → TObj` become `&mut TObj`.
use crate::float::{F32, F64};
use crate::net;
use crate::net::framework::{value_at_f, value_at_v, Easing};
use crate::net::osutk::{v2, Vector2};
use crate::sim::basic::{Vec2, VEC2_ZERO};
use crate::sim::geometry::compare_d;
use alloc::vec::Vec;

/// `Member`
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Member {
    Position,
    Scale,
    Rotation,
    Alpha,
}

/// `Member.isScalar`
pub fn member_is_scalar(m: Member) -> bool {
    match m {
        Member::Rotation | Member::Alpha => true,
        Member::Position | Member::Scale => false,
    }
}

/// `Tr`
#[derive(Clone, Copy)]
pub struct Tr {
    pub id: u64,
    pub member: Member,
    pub start: F64,
    pub end_t: F64,
    pub sv: Vec2,
    pub ev: Vec2,
    pub easing: Easing,
    pub offset: Option<Vec2>,
    pub applied: bool,
    pub applied_to_end: bool,
    pub has_start: bool,
}

/// `Tracker`
#[derive(Clone)]
pub struct Tracker {
    pub member: Member,
    pub ts: Vec<Tr>,
    pub counter: u64,
    pub last_applied: usize,
}

/// `TObj`
#[derive(Clone)]
pub struct TObj {
    pub pos: Vec2,
    pub scale: Vec2,
    pub rot: F32,
    pub alpha: F32,
    pub trackers: Vec<Tracker>,
    pub last_update: F64,
    pub delay: F64,
}

const F32_0: F32 = F32::from_bits(0);
const F32_1: F32 = F32::from_bits(0x3F80_0000);
const F64_0: F64 = F64::from_bits(0);

/// `{} : TObj` with the given alpha
pub fn tobj_new(alpha: F32) -> TObj {
    TObj {
        pos: VEC2_ZERO,
        scale: Vec2 { x: F32_1, y: F32_1 },
        rot: F32_0,
        alpha,
        trackers: Vec::new(),
        last_update: F64_0,
        delay: F64_0,
    }
}

/// `TObj.get`
pub fn tobj_get(o: &TObj, m: Member) -> Vec2 {
    match m {
        Member::Position => o.pos,
        Member::Scale => o.scale,
        Member::Rotation => Vec2 { x: o.rot, y: F32_0 },
        Member::Alpha => Vec2 { x: o.alpha, y: F32_0 },
    }
}

/// `TObj.set` (property setters: no-op if equal under float `==`)
pub fn tobj_set(o: &mut TObj, m: Member, v: Vec2) {
    match m {
        Member::Position => {
            if !o.pos.eq(v) {
                o.pos = v;
            }
        }
        Member::Scale => {
            if !o.scale.eq(v) {
                o.scale = v;
            }
        }
        Member::Rotation => {
            if !o.rot.eq(v.x) {
                o.rot = v.x;
            }
        }
        Member::Alpha => {
            if !o.alpha.eq(v.x) {
                o.alpha = v.x;
            }
        }
    }
}

/// `toTK`
pub fn to_tk(v: Vec2) -> Vector2 {
    v2(v.x, v.y)
}
/// `ofTK`
pub fn of_tk(v: Vector2) -> Vec2 {
    Vec2 { x: v.x, y: v.y }
}

/// `Tr.valueAt`
pub fn tr_value_at(t: &Tr, time: F64) -> Vec2 {
    if time.lt(t.start) {
        t.sv
    } else if t.end_t.le(time) {
        t.ev
    } else if member_is_scalar(t.member) {
        Vec2 { x: value_at_f(time, t.sv.x, t.ev.x, t.start, t.end_t, t.easing), y: F32_0 }
    } else {
        of_tk(value_at_v(time, to_tk(t.sv), to_tk(t.ev), t.start, t.end_t, t.easing))
    }
}

/// `applyTr`: writes the member, returns the transform with `applied`
pub fn apply_tr(o: &mut TObj, t: Tr, time: F64) -> Tr {
    tobj_set(o, t.member, tr_value_at(&t, time));
    Tr { applied: true, ..t }
}

/// `readStart`
pub fn read_start(o: &TObj, t: Tr) -> Tr {
    let cur = tobj_get(o, t.member);
    match t.offset {
        Some(off) => Tr { sv: cur, ev: cur.add(off), has_start: true, ..t },
        None => Tr { sv: cur, has_start: true, ..t },
    }
}

/// the rewind pass of `trackerUpdate`
pub fn tracker_rewind(o: &mut TObj, ts: &mut Vec<Tr>, time: F64) {
    let n = ts.len();
    let mut reverted = false;
    let mut k: usize = 0;
    while k < n {
        let i = n - 1 - k;
        let t = ts[i];
        if t.applied {
            if t.start.le(time) {
                if !reverted {
                    ts[i] = Tr { applied_to_end: false, ..t };
                    reverted = true;
                }
            } else {
                let t2 = apply_tr(o, t, time);
                ts[i] = Tr { applied: false, applied_to_end: false, ..t2 };
            }
        }
        k += 1;
    }
}

/// the catch-up of earlier transforms in `trackerUpdate` (`for j in [last:i]`)
pub fn tracker_catch_up(o: &mut TObj, ts: &mut Vec<Tr>, last: usize, i: usize, at: F64) {
    let mut j = last;
    while j < i {
        let u = ts[j];
        let mut u2 = u;
        if !u.applied_to_end {
            u2 = apply_tr(o, u, at);
        }
        ts[j] = Tr { applied_to_end: true, ..u2 };
        j += 1;
    }
}

/// `trackerUpdate`
pub fn tracker_update(o: &mut TObj, tk: Tracker, time: F64, rewinding: bool) -> Tracker {
    let mut ts = tk.ts;
    let mut last = tk.last_applied;
    if rewinding {
        last = 0;
        tracker_rewind(o, &mut ts, time);
    }
    let mut i = last;
    let mut fuel = ts.len() + 1;
    let mut stop = false;
    while i < ts.len() && fuel > 0 && !stop {
        fuel -= 1;
        let mut t = ts[i];
        if time.lt(t.start) {
            stop = true;
        } else {
            if !t.applied {
                tracker_catch_up(o, &mut ts, last, i, t.start);
            }
            if !t.has_start {
                t = read_start(o, t);
            }
            if !t.applied_to_end {
                let end_reached = t.end_t.le(time);
                let tt = apply_tr(o, t, time);
                t = Tr { applied_to_end: end_reached, ..tt };
            }
            ts[i] = t;
            if t.applied_to_end {
                last = i + 1;
            }
            i += 1;
        }
    }
    Tracker { member: tk.member, ts, counter: tk.counter, last_applied: last }
}

/// `updateTransforms`
pub fn update_transforms(o: &mut TObj, time: F64, force: bool) {
    let rewinding = time.lt(o.last_update) || force;
    o.last_update = time;
    let mut k: usize = 0;
    while k < o.trackers.len() {
        let tk = o.trackers[k].clone();
        let tk2 = tracker_update(o, tk, time, rewinding);
        o.trackers[k] = tk2;
        k += 1;
    }
}

/// `trLess` (`(StartTime, TransformID)` order)
pub fn tr_less(a: &Tr, b: &Tr) -> bool {
    let c = compare_d(a.start, b.start);
    c < 0 || (c == 0 && a.id < b.id)
}

/// index of the tracker of member `m`
pub fn tracker_index(o: &TObj, m: Member) -> Option<usize> {
    let mut k: usize = 0;
    let mut r: Option<usize> = None;
    while k < o.trackers.len() && r.is_none() {
        if o.trackers[k].member == m {
            r = Some(k);
        }
        k += 1;
    }
    r
}

/// the insertion point of `addTransform` (first element `t` sorts before)
pub fn insertion_point(ts: &[Tr], t: &Tr) -> usize {
    let mut j: usize = 0;
    let mut r: Option<usize> = None;
    while j < ts.len() && r.is_none() {
        if tr_less(t, &ts[j]) {
            r = Some(j);
        }
        j += 1;
    }
    match r {
        Some(x) => x,
        None => ts.len(),
    }
}

/// `addTransform`
pub fn add_transform(o: &mut TObj, t0: Tr, now: F64) {
    let k = match tracker_index(o, t0.member) {
        Some(k) => k,
        None => {
            o.trackers.push(Tracker { member: t0.member, ts: Vec::new(), counter: 0, last_applied: 0 });
            o.trackers.len() - 1
        }
    };
    let counter = o.trackers[k].counter;
    let t = Tr { id: counter + 1, ..t0 };
    let ins = insertion_point(&o.trackers[k].ts, &t);
    let mut ts: Vec<Tr> = Vec::new();
    let mut j: usize = 0;
    while j < ins {
        ts.push(o.trackers[k].ts[j]);
        j += 1;
    }
    ts.push(t);
    o.trackers[k] = Tracker { member: t0.member, ts, counter: counter + 1, last_applied: 0 };
    if t.start.lt(now) || t.end_t.le(now) {
        update_transforms(o, now, t.start.le(now));
    }
}

/// `clearTransformsAfter`
pub fn clear_transforms_after(o: &mut TObj, time: F64) {
    let mut k: usize = 0;
    while k < o.trackers.len() {
        let mut ts: Vec<Tr> = Vec::new();
        let mut j: usize = 0;
        while j < o.trackers[k].ts.len() {
            let t = o.trackers[k].ts[j];
            if t.start.lt(time) {
                ts.push(t);
            }
            j += 1;
        }
        o.trackers[k].ts = ts;
        o.trackers[k].last_applied = 0;
        k += 1;
    }
}

/// `dblMinValue`
pub const DBL_MIN_VALUE: F64 = F64::from_bits(0xFFEF_FFFF_FFFF_FFFF);

/// `clearState`
pub fn clear_state(o: &mut TObj) {
    update_transforms(o, DBL_MIN_VALUE, false);
    clear_transforms_after(o, DBL_MIN_VALUE);
}

/// `startTime`
pub fn start_time(o: &TObj, now: F64) -> F64 {
    now.add(o.delay)
}

/// `absSeq`
pub fn abs_seq(o: &mut TObj, now: F64, t: F64) {
    o.delay = t.sub(now);
}

/// `Seq`
#[derive(Clone, Copy)]
pub struct Seq {
    pub current_time: F64,
    pub last_end_time: F64,
    pub has_last: bool,
}

/// `transformTo`
pub fn transform_to(o: &mut TObj, now: F64, m: Member, v: Vec2, dur: F64, e: Easing, offset: Option<Vec2>) -> Seq {
    let st = start_time(o, now);
    let t = Tr {
        id: 0,
        member: m,
        start: st,
        end_t: st.add(dur),
        sv: VEC2_ZERO,
        ev: v,
        easing: e,
        offset,
        applied: false,
        applied_to_end: false,
        has_start: false,
    };
    let seq = Seq { current_time: st, last_end_time: t.end_t, has_last: true };
    add_transform(o, t, now);
    seq
}

/// `Seq.append`
pub fn seq_append(s: Seq, o: &mut TObj, now: F64, m: Member, v: Vec2, dur: F64, e: Easing, offset: Option<Vec2>) -> Seq {
    let saved = o.delay;
    abs_seq(o, now, s.current_time);
    let child = transform_to(o, now, m, v, dur, e, offset);
    let end_t = child.last_end_time;
    o.delay = saved;
    Seq {
        current_time: s.current_time,
        last_end_time: if !s.has_last || s.last_end_time.lt(end_t) { end_t } else { s.last_end_time },
        has_last: true,
    }
}

/// `Seq.then_`
pub fn seq_then(s: Seq) -> Seq {
    Seq { current_time: net::max(s.current_time, s.last_end_time), ..s }
}

/// `delaySeq`
pub fn delay_seq(o: &TObj, now: F64, d: F64) -> Seq {
    let st = start_time(o, now);
    Seq { current_time: st.add(d), last_end_time: st, has_last: false }
}

/// `vs`
pub fn vs(x: F32) -> Vec2 {
    Vec2 { x, y: F32_0 }
}

/// `fadeInFromZero`
pub fn fade_in_from_zero(o: &mut TObj, now: F64, dur: F64, e: Easing) {
    let s = transform_to(o, now, Member::Alpha, vs(F32_0), F64_0, Easing::None, None);
    seq_append(s, o, now, Member::Alpha, vs(F32_1), dur, e, None);
}

/// `latestEnd`
pub fn latest_end(o: &TObj, now: F64) -> F64 {
    let mut m = start_time(o, now);
    let mut k: usize = 0;
    while k < o.trackers.len() {
        let mut j: usize = 0;
        while j < o.trackers[k].ts.len() {
            let e = o.trackers[k].ts[j].end_t;
            if m.lt(e) {
                m = e.add(F64::from_bits(0x3FF0_0000_0000_0000));
            }
            j += 1;
        }
        k += 1;
    }
    m
}
