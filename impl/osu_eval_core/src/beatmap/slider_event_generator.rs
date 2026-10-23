//! Port of `OsuModel/Beatmap/SliderEventGenerator.lean` (`SliderEventGenerator.Generate`).
use super::errors::*;
use super::hit_object_parser::{lift_net, DecodeError};
use crate::float::F64;
use crate::net::mathops::f64_clamp;
use crate::net::min as f64_min;
use crate::net::max as f64_max;
use alloc::vec::Vec;

/// `SliderEventType`; spec `SliderEventType`
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SliderEventType {
    Tick,
    LegacyLastTick,
    Head,
    Repeat,
    Tail,
}

/// `SliderEventDescriptor`; spec `SliderEventDescriptor`
#[derive(Clone, Copy)]
pub struct SliderEventDescriptor {
    pub etype: SliderEventType,
    pub time: F64,
    pub span_index: i32,
    pub span_start_time: F64,
    pub path_progress: F64,
}

/// `TAIL_LENIENCY = -36`
pub const TAIL_LENIENCY: F64 = F64::from_bits(0xC042_0000_0000_0000);
const D0: F64 = F64::from_bits(0);
const D1: F64 = F64::from_bits(0x3FF0_0000_0000_0000);
const D2: F64 = F64::from_bits(0x4000_0000_0000_0000);
const D10: F64 = F64::from_bits(0x4024_0000_0000_0000);
const MAX_LENGTH: F64 = F64::from_bits(0x40F8_6A00_0000_0000); // 100000

/// `generateTicks(...)` (one span, increasing distance); spec `SliderEventGenerator.generateTicks`
pub fn generate_ticks(span_index: i32, span_start_time: F64, span_duration: F64, reversed: bool, length: F64, tick_distance: F64, min_distance_from_end: F64) -> Vec<SliderEventDescriptor> {
    let mut out: Vec<SliderEventDescriptor> = Vec::new();
    let mut d = tick_distance;
    let mut fuel: u64 = 0;
    let mut go = true;
    while go && fuel < 10000000 {
        if !d.le(length) {
            go = false;
        } else if length.sub(min_distance_from_end).le(d) {
            go = false;
        } else {
            let path_progress = d.div(length);
            let time_progress = if reversed { D1.sub(path_progress) } else { path_progress };
            out.push(SliderEventDescriptor {
                etype: SliderEventType::Tick,
                span_index,
                span_start_time,
                time: span_start_time.add(time_progress.mul(span_duration)),
                path_progress,
            });
            d = d.add(tick_distance);
            fuel = fuel + 1;
        }
    }
    out
}

/// `Generate(startTime, spanDuration, velocity, tickDistance, totalDistance, spanCount)`; spec
/// `SliderEventGenerator.generate`
pub fn generate(start_time: F64, span_duration: F64, velocity: F64, tick_distance0: F64, total_distance: F64, span_count: i32) -> Result<Vec<SliderEventDescriptor>, DecodeError> {
    let length = f64_min(MAX_LENGTH, total_distance);
    let tick_distance = tri!(lift_net(W_MATH_CLAMP_TICKDISTANCE_0_LENGTH, f64_clamp(tick_distance0, D0, length)));
    let min_distance_from_end = velocity.mul(D10);
    let mut out: Vec<SliderEventDescriptor> = Vec::new();
    out.push(SliderEventDescriptor { etype: SliderEventType::Head, span_index: 0, span_start_time: start_time, time: start_time, path_progress: D0 });
    let n: i32 = if span_count < 0 { 0 } else { span_count };
    let mut span: i32 = 0;
    while span < n {
        let span_start_time = start_time.add(F64::from_i64(span as i64).mul(span_duration));
        let reversed = span % 2 == 1;
        if !tick_distance.eq(D0) {
            let ticks = generate_ticks(span, span_start_time, span_duration, reversed, length, tick_distance, min_distance_from_end);
            if reversed {
                let mut k = ticks.len();
                while k > 0 {
                    k = k - 1;
                    out.push(ticks[k]);
                }
            } else {
                let mut k = 0;
                while k < ticks.len() {
                    out.push(ticks[k]);
                    k = k + 1;
                }
            }
        }
        if span < span_count.wrapping_sub(1) {
            out.push(SliderEventDescriptor {
                etype: SliderEventType::Repeat,
                span_index: span,
                span_start_time: start_time.add(F64::from_i64(span as i64).mul(span_duration)),
                time: span_start_time.add(span_duration),
                path_progress: F64::from_i64((span.wrapping_add(1) % 2) as i64),
            });
        }
        span = span + 1;
    }
    let total_duration = F64::from_i64(span_count as i64).mul(span_duration);
    let final_span_index = span_count.wrapping_sub(1);
    let final_span_start_time = start_time.add(F64::from_i64(final_span_index as i64).mul(span_duration));
    let legacy_last_tick_time =
        f64_max(start_time.add(total_duration.div(D2)), final_span_start_time.add(span_duration).add(TAIL_LENIENCY));
    let mut legacy_last_tick_progress = legacy_last_tick_time.sub(final_span_start_time).div(span_duration);
    if span_count % 2 == 0 {
        legacy_last_tick_progress = D1.sub(legacy_last_tick_progress);
    }
    out.push(SliderEventDescriptor {
        etype: SliderEventType::LegacyLastTick,
        span_index: final_span_index,
        span_start_time: final_span_start_time,
        time: legacy_last_tick_time,
        path_progress: legacy_last_tick_progress,
    });
    out.push(SliderEventDescriptor {
        etype: SliderEventType::Tail,
        span_index: final_span_index,
        span_start_time: start_time.add(F64::from_i64(span_count.wrapping_sub(1) as i64).mul(span_duration)),
        time: start_time.add(total_duration),
        path_progress: F64::from_i64((span_count % 2) as i64),
    });
    Ok(out)
}
