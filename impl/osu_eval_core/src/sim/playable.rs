//! The playable beatmap as consumed by the simulation (the Sim's input interface).
//! Spec: `model/OsuModel/Sim/Playable.lean`. The JSON loader (`Load.*`) is not translated: it lives in
//! the `simtest_rs` shell (`impl/simtest_rs/src/load.rs`).
use crate::float::F64;
use crate::sim::basic::{HitResult, Vec2, VEC2_ZERO};
use alloc::vec::Vec;

/// `Kind`
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    Circle,
    Slider,
    Spinner,
    Head,
    Tick,
    Repeat,
    Tail,
    SpinnerTick,
    SpinnerBonusTick,
}

/// `Kind.isCircleLike`
pub fn is_circle_like(k: Kind) -> bool {
    match k {
        Kind::Circle | Kind::Head => true,
        _ => false,
    }
}

/// `HitWindows` (OsuHitWindows: Great/Ok/Meh/Miss)
#[derive(Clone, Copy)]
pub struct HitWindows {
    pub great: F64,
    pub ok_: F64,
    pub meh: F64,
    pub miss: F64,
}

/// `HitWindows.resultFor`
pub fn result_for(hw: &HitWindows, time_offset: F64) -> HitResult {
    let o = time_offset.abs();
    if o.le(hw.great) {
        HitResult::Great
    } else if o.le(hw.ok_) {
        HitResult::Ok_
    } else if o.le(hw.meh) {
        HitResult::Meh
    } else if o.le(hw.miss) {
        HitResult::Miss
    } else {
        HitResult::None
    }
}

/// `HitWindows.canBeHit`
pub fn can_be_hit(hw: &HitWindows, time_offset: F64) -> bool {
    time_offset.le(hw.meh)
}

/// `HObj`. `type_id` indexes `Playable.type_names` (the spec's `typeName : String`; `0` = the
/// kind's default class name, see `TYPE_DEFAULT`).
#[derive(Clone, Copy)]
pub struct HObj {
    pub kind: Kind,
    pub type_id: u32,
    pub start: F64,
    pub end_time: F64,
    pub pos: Vec2,
    pub stacked: Vec2,
    pub stack_height: i64,
    pub scale: crate::float::F32,
    pub radius: F64,
    pub preempt: F64,
    /// `TimeFadeIn` (M7)
    pub fade_in: F64,
    pub max_judgement_offset: F64,
    pub hit_windows: Option<HitWindows>,
    pub max_result: HitResult,
    pub min_result: HitResult,
    pub new_combo: bool,
    pub combo_index: u64,
    pub index_in_combo: u64,
    pub last_in_combo: bool,
    pub span_index: u64,
    pub span_start: F64,
    pub path_progress: F64,
    pub repeat_index: u64,
    /// `typeName == "StrictTrackingSliderTailCircle"` (the only type-name test of the simulation)
    pub strict_tail: bool,
}

/// `type_id` meaning "the kind's default type name" (spec `typeName := ""`)
pub const TYPE_DEFAULT: u32 = 0;

/// `SliderData`
#[derive(Clone)]
pub struct SliderData {
    pub span_count: u64,
    pub duration: F64,
    pub span_duration: F64,
    pub velocity: F64,
    pub path_distance: F64,
    pub classic: bool,
    pub path: Vec<Vec2>,
    pub cum_len: Vec<F64>,
}

/// `default : SliderData`
pub fn slider_data_default() -> SliderData {
    SliderData {
        span_count: 0,
        duration: F64::from_bits(0),
        span_duration: F64::from_bits(0),
        velocity: F64::from_bits(0),
        path_distance: F64::from_bits(0),
        classic: false,
        path: Vec::new(),
        cum_len: Vec::new(),
    }
}

/// `SpinnerData`
#[derive(Clone, Copy)]
pub struct SpinnerData {
    pub duration: F64,
    pub spins_required: i64,
    pub max_bonus_spins: i64,
}

/// `TopObj`
#[derive(Clone)]
pub struct TopObj {
    pub h: HObj,
    pub slider: Option<SliderData>,
    pub spinner: Option<SpinnerData>,
    pub nested: Vec<HObj>,
}

/// `Difficulty`
#[derive(Clone, Copy)]
pub struct Difficulty {
    pub cs: crate::float::F32,
    pub hp: crate::float::F32,
    pub od: crate::float::F32,
    pub ar: crate::float::F32,
}

/// A break period `(start, end)`
#[derive(Clone, Copy)]
pub struct Period {
    pub start: F64,
    pub end: F64,
}

/// `Playable`
#[derive(Clone)]
pub struct Playable {
    pub beatmap_version: i64,
    pub audio_lead_in: F64,
    pub difficulty: Difficulty,
    pub base_difficulty: Difficulty,
    pub slider_multiplier: F64,
    pub slider_tick_rate: F64,
    pub breaks: Vec<Period>,
    pub objects: Vec<TopObj>,
}

/// `default : HObj` fields that the loader leaves at their defaults
pub fn hobj_default() -> HObj {
    HObj {
        kind: Kind::Circle,
        type_id: TYPE_DEFAULT,
        start: F64::from_bits(0),
        end_time: F64::from_bits(0),
        pos: VEC2_ZERO,
        stacked: VEC2_ZERO,
        stack_height: 0,
        scale: crate::float::F32::from_bits(0),
        radius: F64::from_bits(0),
        preempt: F64::from_bits(0),
        fade_in: F64::from_bits(0),
        max_judgement_offset: F64::from_bits(0),
        hit_windows: None,
        max_result: HitResult::None,
        min_result: HitResult::None,
        new_combo: false,
        combo_index: 0,
        index_in_combo: 0,
        last_in_combo: false,
        span_index: 0,
        span_start: F64::from_bits(0),
        path_progress: F64::from_bits(0),
        repeat_index: 0,
        strict_tail: false,
    }
}
