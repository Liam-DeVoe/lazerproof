//! Step schedule: reference sequences + FrameStabilityContainer stepping (DECISIONS D9).
//! Spec: `model/OsuModel/Sim/Schedule.lean` (total since `e0e8215`: `references`, `simulateSteps` and `steps` return
//! `Except String`). `crate::schedule::simulate_steps` is the proof-POC copy of the pre-G17 `simulateSteps` (proven
//! against `proofs/OsuProofs/Spec/Schedule.lean`, docs/proof-poc.md); the simulation uses `simulate_steps` here.
use crate::float::F64;
use crate::net;
use crate::replay::frames::Frame;
pub use crate::schedule::Step;
use crate::schedule::{frame_time, SimState, CATCHUP_THRESHOLD, FUEL, K0, NEG_INF, SIXTY_FRAME_TIME};
use crate::sim::err::SimErr;
use crate::sim::netx::{F64_NEG_INF, F64_ZERO};
use crate::sim::playable::Playable;
use alloc::vec::Vec;

/// `ScheduleKind`
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ScheduleKind {
    Catchup,
    Perframe,
    Dense1ms,
}

pub const F64_2000: F64 = F64::from_bits(0x409F_4000_0000_0000);
pub const F64_1000: F64 = F64::from_bits(0x408F_4000_0000_0000);
pub const F64_ONE: F64 = F64::from_bits(0x3FF0_0000_0000_0000);

/// `gameplayStartTime`
pub fn gameplay_start_time(pb: &Playable) -> F64 {
    if pb.objects.len() > 0 {
        let o = &pb.objects[0];
        o.h.start.sub(net::max(F64_2000, o.h.preempt))
    } else {
        F64_ZERO
    }
}

/// `referenceStart`
pub fn reference_start(pb: &Playable) -> F64 {
    let t = net::min(F64_ZERO, gameplay_start_time(pb));
    if pb.objects.len() > 0 {
        let o = &pb.objects[0];
        if F64_ZERO.lt(pb.audio_lead_in) { net::min(t, o.h.start.sub(pb.audio_lead_in)) } else { t }
    } else {
        t
    }
}

/// `referenceEnd`
pub fn reference_end(pb: &Playable) -> F64 {
    let mut m = F64_NEG_INF;
    let mut i: usize = 0;
    while i < pb.objects.len() {
        m = max_end_time(m, &pb.objects[i]);
        i += 1;
    }
    m.add(F64_1000)
}

/// the body of `referenceEnd`'s outer loop: `Math.Max` over the object's and its nested objects' end times
pub fn max_end_time(m0: F64, o: &crate::sim::playable::TopObj) -> F64 {
    let mut m = net::max(m0, o.h.end_time);
    let mut j: usize = 0;
    while j < o.nested.len() {
        m = net::max(m, o.nested[j].end_time);
        j += 1;
    }
    m
}

/// the `.perframe` branch of `references`
pub fn references_perframe(r0: F64, end_t: F64, frame_times: &[F64]) -> Vec<F64> {
    let mut l: Vec<F64> = Vec::new();
    l.push(r0);
    let mut last = r0;
    let mut i: usize = 0;
    while i < frame_times.len() {
        let f = frame_times[i];
        if last.lt(f) {
            l.push(f);
            last = f;
        }
        i += 1;
    }
    if last.lt(end_t) {
        l.push(end_t);
    }
    l
}

/// the `.dense1ms` branch of `references`
pub fn references_dense1ms(r0: F64, end_t: F64) -> Result<Vec<F64>, SimErr> {
    let mut l: Vec<F64> = Vec::new();
    l.push(r0);
    let mut cur = r0;
    let mut fuel: u32 = 100_000_000;
    while cur.lt(end_t) && fuel > 0 {
        fuel -= 1;
        cur = cur.floor().add(F64_ONE);
        l.push(cur);
    }
    if cur.lt(end_t) {
        return Err(SimErr::DenseFuel);
    }
    Ok(l)
}

/// `references`
pub fn references(kind: ScheduleKind, r0: F64, end_t: F64, frame_times: &[F64]) -> Result<Vec<F64>, SimErr> {
    match kind {
        ScheduleKind::Catchup => {
            let mut l: Vec<F64> = Vec::new();
            l.push(r0);
            l.push(net::max(r0, end_t));
            Ok(l)
        }
        ScheduleKind::Perframe => Ok(references_perframe(r0, end_t, frame_times)),
        ScheduleKind::Dense1ms => references_dense1ms(r0, end_t),
    }
}

/// One frame-stable step towards reference `r` (the body of `simulateSteps`' inner `while`); rejects where
/// `Math.Clamp(time, frames[idx].Time, frames[idx+1].Time)` throws (out-of-order frame times).
pub fn fsc_step(st: SimState, r: F64, frames: &[F64], gst: F64) -> Result<SimState, SimErr> {
    let mut first = st.first;
    let manual = st.manual;
    let mut idx = st.idx;
    let mut handler_time = st.handler_time;
    let mut proposed = r;
    // (the spec's `manual := proposed` assignments here are dead: `manual` is overwritten below)
    if first {
        first = false;
    } else if manual.lt(gst) {
        proposed = net::min(gst, proposed);
    } else if CATCHUP_THRESHOLD.lt(manual.sub(proposed).abs()) {
        proposed = if manual.lt(proposed) {
            net::min(proposed, manual.add(SIXTY_FRAME_TIME))
        } else {
            net::max(proposed, manual.sub(SIXTY_FRAME_TIME))
        };
    }
    if frames.len() == 0 {
        handler_time = proposed;
    } else {
        let fs = frame_time(frames, idx);
        let fe = frame_time(frames, idx + 1);
        if fe.le(proposed) {
            proposed = fe;
            idx += 1;
        } else if proposed.lt(fs) && handler_time.eq(fs) {
            idx -= 1;
        }
        let fs2 = frame_time(frames, idx);
        let fe2 = frame_time(frames, idx + 1);
        handler_time = match crate::net::mathops::f64_clamp(proposed, fs2, fe2) {
            Ok(v) => v,
            Err(e) => return Err(SimErr::ClampFrames(e, idx)),
        };
    }
    Ok(SimState { first, manual: handler_time, idx, handler_time })
}

/// the inner loop of `simulateSteps` for one reference: steps until the FSC reaches `r`
pub fn simulate_ref(steps: &mut Vec<Step>, st0: SimState, r: F64, frames: &[F64], gst: F64) -> Result<SimState, SimErr> {
    let mut st = st0;
    let mut fuel: u32 = FUEL;
    let mut reached = false;
    while fuel > 0 && !reached {
        fuel -= 1;
        st = fsc_step(st, r, frames, gst)?;
        steps.push(Step { time: st.manual, frame_index: st.idx });
        if st.handler_time.eq(r) {
            reached = true;
        }
    }
    // the spec checks `fuel == 0` after the loop (also when the last iteration reached `r`)
    if fuel == 0 {
        return Err(SimErr::StepFuel);
    }
    Ok(st)
}

/// `simulateSteps` (`StepSimulator.Simulate`): each reference is held until the FSC reaches it.
pub fn simulate_steps(refs: &[F64], frames: &[F64], gst: F64) -> Result<Vec<Step>, SimErr> {
    let mut steps: Vec<Step> = Vec::new();
    let mut st = SimState { first: true, manual: K0, idx: -1, handler_time: NEG_INF };
    let mut ri: usize = 0;
    while ri < refs.len() {
        st = simulate_ref(&mut steps, st, refs[ri], frames, gst)?;
        ri += 1;
    }
    Ok(steps)
}

/// `frames.map (·.time)`
pub fn frame_times(frames: &[Frame]) -> Vec<F64> {
    let mut v: Vec<F64> = Vec::new();
    let mut i: usize = 0;
    while i < frames.len() {
        v.push(frames[i].time);
        i += 1;
    }
    v
}

/// `steps`
pub fn steps(kind: ScheduleKind, pb: &Playable, frames: &[Frame]) -> Result<Vec<Step>, SimErr> {
    let ft = frame_times(frames);
    let refs = references(kind, reference_start(pb), reference_end(pb), &ft)?;
    simulate_steps(&refs, &ft, gameplay_start_time(pb))
}
