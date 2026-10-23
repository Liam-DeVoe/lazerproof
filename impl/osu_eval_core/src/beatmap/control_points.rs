//! Port of `OsuModel/Beatmap/ControlPoints.lean`: timing/difficulty/effect control points,
//! bindable clamping, redundancy, `TimingPointAt`/`DifficultyPointAt`/`EffectPointAt`, `DeepClone`.
use super::dotnet::{compare_f64, insert_at};
use crate::float::F64;
use alloc::vec::Vec;

/// `TimingControlPoint`; spec `TimingPoint`
#[derive(Clone, Copy)]
pub struct TimingPoint {
    pub time: F64,
    pub beat_length: F64,
    /// `TimeSignature.Numerator`
    pub time_signature: i32,
}

const K6: F64 = F64::from_bits(0x4018_0000_0000_0000);
const K60000: F64 = F64::from_bits(0x40ED_4C00_0000_0000);
const K0_1: F64 = F64::from_bits(0x3FB9_9999_9999_999A);
const K10: F64 = F64::from_bits(0x4024_0000_0000_0000);
const K0_01: F64 = F64::from_bits(0x3F84_7AE1_47AE_147B);
const K1: F64 = F64::from_bits(0x3FF0_0000_0000_0000);
const K1000: F64 = F64::from_bits(0x408F_4000_0000_0000);
const K0: F64 = F64::from_bits(0);

/// `BeatLengthBindable` assignment (clamp to [6, 60000]); spec `clampBeatLength`
pub fn clamp_beat_length(v: F64) -> F64 {
    if v.lt(K6) { K6 } else if K60000.lt(v) { K60000 } else { v }
}

/// `TimingControlPoint.DEFAULT`; spec `TimingPoint.default`
pub const TIMING_DEFAULT: TimingPoint = TimingPoint { time: K0, beat_length: K1000, time_signature: 4 };

/// `DifficultyControlPoint`; spec `DifficultyPoint`
#[derive(Clone, Copy)]
pub struct DifficultyPoint {
    pub time: F64,
    pub slider_velocity: F64,
    pub generate_ticks: bool,
}

/// `SliderVelocityBindable` assignment (clamp to [0.1, 10]); spec `clampSV`
pub fn clamp_sv(v: F64) -> F64 {
    if v.lt(K0_1) { K0_1 } else if K10.lt(v) { K10 } else { v }
}

/// spec `DifficultyPoint.default`
pub const DIFFICULTY_DEFAULT: DifficultyPoint = DifficultyPoint { time: K0, slider_velocity: K1, generate_ticks: true };

/// spec `DifficultyPoint.isRedundant`
pub fn difficulty_is_redundant(p: DifficultyPoint, e: DifficultyPoint) -> bool {
    p.generate_ticks == e.generate_ticks && p.slider_velocity.eq(e.slider_velocity)
}

/// `EffectControlPoint`; spec `EffectPoint`
#[derive(Clone, Copy)]
pub struct EffectPoint {
    pub time: F64,
    pub kiai: bool,
    pub scroll_speed: F64,
}

/// `ScrollSpeedBindable` assignment (clamp to [0.01, 10]); spec `clampScrollSpeed`
pub fn clamp_scroll_speed(v: F64) -> F64 {
    if v.lt(K0_01) { K0_01 } else if K10.lt(v) { K10 } else { v }
}

/// spec `EffectPoint.default`
pub const EFFECT_DEFAULT: EffectPoint = EffectPoint { time: K0, kiai: false, scroll_speed: K1 };

/// spec `EffectPoint.isRedundant`
pub fn effect_is_redundant(p: EffectPoint, e: EffectPoint) -> bool {
    p.kiai == e.kiai && p.scroll_speed.eq(e.scroll_speed)
}

/// Access to a control point's time (spec: the `timeOf`/`setTime` arguments).
pub trait HasTime {
    fn time_of(&self) -> F64;
    fn with_time(&self, t: F64) -> Self;
}
impl HasTime for TimingPoint {
    fn time_of(&self) -> F64 {
        self.time
    }
    fn with_time(&self, t: F64) -> TimingPoint {
        TimingPoint { time: t, beat_length: self.beat_length, time_signature: self.time_signature }
    }
}
impl HasTime for DifficultyPoint {
    fn time_of(&self) -> F64 {
        self.time
    }
    fn with_time(&self, t: F64) -> DifficultyPoint {
        DifficultyPoint { time: t, slider_velocity: self.slider_velocity, generate_ticks: self.generate_ticks }
    }
}
impl HasTime for EffectPoint {
    fn time_of(&self) -> F64 {
        self.time
    }
    fn with_time(&self, t: F64) -> EffectPoint {
        EffectPoint { time: t, kiai: self.kiai, scroll_speed: self.scroll_speed }
    }
}

/// `ControlPointInfo.BinarySearch(list, time, Rightmost)` + adjustment: index of the last point
/// with `Time <= time`; spec `binarySearchIdx`
pub fn binary_search_idx<T: HasTime>(list: &[T], time: F64) -> Option<usize> {
    let n = list.len();
    if n == 0 {
        None
    } else if time.lt(list[0].time_of()) {
        None
    } else if list[n - 1].time_of().lt(time) {
        Some(n - 1)
    } else {
        let mut l: i64 = 0;
        let mut r: i64 = (n as i64) - 1;
        let mut eq = false;
        let mut k = 0;
        while k < n + 1 {
            if l <= r {
                let pivot = l + (r - l) / 2;
                let pt = list[pivot as usize].time_of();
                if pt.lt(time) {
                    l = pivot + 1;
                } else if time.lt(pt) {
                    r = pivot - 1;
                } else {
                    eq = true;
                    l = pivot + 1;
                }
            }
            k = k + 1;
        }
        let index0: i64 = if eq { l - 1 } else { -l - 1 };
        let index = if index0 < 0 { -index0 - 1 - 1 } else { index0 };
        if index >= 0 { Some(index as usize) } else { None }
    }
}

/// The typed lists of a `LegacyControlPointInfo`; spec `ControlPointInfo`
#[derive(Clone)]
pub struct ControlPointInfo {
    pub timing_points: Vec<TimingPoint>,
    pub difficulty_points: Vec<DifficultyPoint>,
    pub effect_points: Vec<EffectPoint>,
}

pub fn cpi_empty() -> ControlPointInfo {
    ControlPointInfo { timing_points: Vec::new(), difficulty_points: Vec::new(), effect_points: Vec::new() }
}

/// `TimingPointAt(time)`; spec `ControlPointInfo.timingPointAt`
pub fn timing_point_at(c: &ControlPointInfo, time: F64) -> TimingPoint {
    match binary_search_idx(&c.timing_points, time) {
        Some(i) => c.timing_points[i],
        None => {
            if c.timing_points.len() > 0 { c.timing_points[0] } else { TIMING_DEFAULT }
        }
    }
}

/// `DifficultyPointAt(time)`; spec `ControlPointInfo.difficultyPointAt`
pub fn difficulty_point_at(c: &ControlPointInfo, time: F64) -> DifficultyPoint {
    match binary_search_idx(&c.difficulty_points, time) {
        Some(i) => c.difficulty_points[i],
        None => DIFFICULTY_DEFAULT,
    }
}

/// `EffectPointAt(time)`; spec `ControlPointInfo.effectPointAt`
pub fn effect_point_at(c: &ControlPointInfo, time: F64) -> EffectPoint {
    match binary_search_idx(&c.effect_points, time) {
        Some(i) => c.effect_points[i],
        None => EFFECT_DEFAULT,
    }
}

/// Insert into a time-sorted list, replacing a point at the same time (which keeps the group's
/// time); spec `insertSorted`
pub fn insert_sorted<T: HasTime + Clone>(list: &mut Vec<T>, p: T) {
    let t = p.time_of();
    let mut same: Option<usize> = None;
    let mut i = 0;
    while same.is_none() && i < list.len() {
        if compare_f64(list[i].time_of(), t) == 0 {
            same = Some(i);
        }
        i = i + 1;
    }
    match same {
        Some(j) => {
            let gt = list[j].time_of();
            list[j] = p.with_time(gt);
        }
        None => {
            let mut k = 0;
            let mut found = false;
            while !found && k < list.len() {
                if compare_f64(t, list[k].time_of()) < 0 {
                    found = true;
                } else {
                    k = k + 1;
                }
            }
            insert_at(list, k, p);
        }
    }
}

/// `ControlPointInfo.Add(time, TimingControlPoint)`; spec `ControlPointInfo.addTiming`
pub fn add_timing(c: &mut ControlPointInfo, p: TimingPoint) {
    insert_sorted(&mut c.timing_points, p);
}

/// `ControlPointInfo.Add(time, DifficultyControlPoint)` (dropped if redundant); spec `addDifficulty`
pub fn add_difficulty(c: &mut ControlPointInfo, p: DifficultyPoint) {
    if !difficulty_is_redundant(p, difficulty_point_at(c, p.time)) {
        insert_sorted(&mut c.difficulty_points, p);
    }
}

/// `ControlPointInfo.Add(time, EffectControlPoint)` (dropped if redundant); spec `addEffect`
pub fn add_effect(c: &mut ControlPointInfo, p: EffectPoint) {
    if !effect_is_redundant(p, effect_point_at(c, p.time)) {
        insert_sorted(&mut c.effect_points, p);
    }
}

/// `ControlPointInfo.DeepClone()` (re-adds every point, re-checking redundancy); spec `deepClone`
pub fn deep_clone(c: &ControlPointInfo) -> ControlPointInfo {
    let mut r = cpi_empty();
    let mut i = 0;
    while i < c.timing_points.len() {
        add_timing(&mut r, c.timing_points[i]);
        i = i + 1;
    }
    let mut j = 0;
    while j < c.difficulty_points.len() {
        add_difficulty(&mut r, c.difficulty_points[j]);
        j = j + 1;
    }
    let mut k = 0;
    while k < c.effect_points.len() {
        add_effect(&mut r, c.effect_points[k]);
        k = k + 1;
    }
    r
}
