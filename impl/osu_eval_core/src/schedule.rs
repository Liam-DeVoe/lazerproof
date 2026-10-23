//! FrameStabilityContainer step schedule (DECISIONS D9).
//! Spec: `OsuModel.Sim.simulateSteps` (Sim/Schedule.lean).
use crate::float::F64;
use crate::net;
use alloc::vec::Vec;

pub const K0: F64 = F64::from_bits(0);
pub const POS_INF: F64 = F64::from_bits(0x7FF0_0000_0000_0000);
pub const NEG_INF: F64 = F64::from_bits(0xFFF0_0000_0000_0000);
/// `1000.0 / 60`
pub const SIXTY_FRAME_TIME: F64 = F64::from_bits(0x4030_AAAA_AAAA_AAAB);
/// `sixty_frame_time * 1.2f`
pub const CATCHUP_THRESHOLD: F64 = F64::from_bits(0x4034_0000_0D55_5556);
/// per-reference iteration bound of the spec (`fuel`)
pub const FUEL: u32 = 100_000_000;

#[derive(Clone, Copy)]
pub struct Step {
    pub time: F64,
    pub frame_index: i64,
}

/// Frame time at handler index `i` (-∞ before the first frame, +∞ after the last).
pub fn frame_time(frames: &[F64], i: i64) -> F64 {
    if i < 0 {
        NEG_INF
    } else {
        let u = i as usize;
        if u >= frames.len() { POS_INF } else { frames[u] }
    }
}

/// Mutable state of the FSC + replay handler between steps.
#[derive(Clone, Copy)]
pub struct SimState {
    pub first: bool,
    pub manual: F64,
    pub idx: i64,
    pub handler_time: F64,
}

/// One frame-stable step towards reference `r` (the body of the spec's inner `while`).
/// Returns the new state; the step to record is `(st.manual, st.idx)`.
pub fn fsc_step(st: SimState, r: F64, frames: &[F64], gst: F64) -> SimState {
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
        let fs = frame_time(frames, idx);
        let fe = frame_time(frames, idx + 1);
        handler_time = match net::clamp(proposed, fs, fe) {
            Some(v) => v,
            None => proposed,
        };
    }
    SimState { first, manual: handler_time, idx, handler_time }
}

/// `StepSimulator.Simulate`: each reference is held until the FSC reaches it.
pub fn simulate_steps(refs: &[F64], frames: &[F64], gst: F64) -> Vec<Step> {
    let mut steps: Vec<Step> = Vec::new();
    let mut st = SimState { first: true, manual: K0, idx: -1, handler_time: NEG_INF };
    let mut ri: usize = 0;
    while ri < refs.len() {
        let r = refs[ri];
        let mut fuel: u32 = FUEL;
        while fuel > 0 {
            fuel -= 1;
            st = fsc_step(st, r, frames, gst);
            steps.push(Step { time: st.manual, frame_index: st.idx });
            if st.handler_time.eq(r) {
                break;
            }
        }
        ri += 1;
    }
    steps
}
