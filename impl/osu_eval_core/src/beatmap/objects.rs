//! Port of `OsuModel/Beatmap/Objects.lean`: osu! hit objects (stored state + derived getters)
//! and `ApplyDefaults`.
use super::control_points::{effect_point_at, timing_point_at, ControlPointInfo, TimingPoint};
use super::dotnet::{fmod1, list_sort, compare_f64, SortCmp, SortKey};
use super::hit_object_parser::DecodeError;
use super::slider_event_generator::{generate, SliderEventType};
use super::slider_path::{self, SliderPath};
use super::types::Difficulty;
use super::vector2::{self as v, Vec2};
use crate::float::{F32, F64};
use crate::net::min as f64_min;
use alloc::vec::Vec;

const D0: F64 = F64::from_bits(0);
const D1: F64 = F64::from_bits(0x3FF0_0000_0000_0000);
const D2: F64 = F64::from_bits(0x4000_0000_0000_0000);
const D5: F64 = F64::from_bits(0x4014_0000_0000_0000);

/// `DifficultyRange(d) = (d - 5) / 5`; spec `difficultyRange1`
pub fn difficulty_range1(d: F64) -> F64 {
    d.sub(D5).div(D5)
}

/// `DifficultyRange(difficulty, min, mid, max)`; spec `difficultyRange`
pub fn difficulty_range(d: F64, min: F64, mid: F64, max: F64) -> F64 {
    if D5.lt(d) {
        mid.add(max.sub(mid).mul(difficulty_range1(d)))
    } else if d.lt(D5) {
        mid.add(mid.sub(min).mul(difficulty_range1(d)))
    } else {
        mid
    }
}

const F32_ONE: F32 = F32::from_bits(0x3F80_0000);
const F32_0_7: F32 = F32::from_bits(0x3F33_3333);
const F32_2: F32 = F32::from_bits(0x4000_0000);
const F32_FUDGE: F32 = F32::from_bits(0x3F80_0D6F); // 1.00041f

/// `CalculateScaleFromCircleSize(circleSize, applyFudge)`; spec `calculateScaleFromCircleSize`
pub fn calculate_scale_from_circle_size(cs: F32, apply_fudge: bool) -> F32 {
    let inner = F32_ONE.to_f64().sub(F32_0_7.to_f64().mul(difficulty_range1(cs.to_f64())));
    inner.to_f32().div(F32_2).mul(if apply_fudge { F32_FUDGE } else { F32_ONE })
}

/// `HitWindows.Empty` or `OsuHitWindows`; spec `HitWindows`
#[derive(Clone, Copy)]
pub enum HitWindows {
    Empty,
    Osu { great: F64, ok_: F64, meh: F64 },
}

/// `OsuHitWindows.MISS_WINDOW`
pub const MISS_WINDOW: F64 = F64::from_bits(0x4079_0000_0000_0000);
const D_HALF: F64 = F64::from_bits(0x3FE0_0000_0000_0000);

/// `OsuHitWindows.SetDifficulty(od)`; spec `osuHitWindows`
pub fn osu_hit_windows(od: F64) -> HitWindows {
    HitWindows::Osu {
        great: difficulty_range(od, F64::from_bits(0x4054_0000_0000_0000), F64::from_bits(0x4049_0000_0000_0000), F64::from_bits(0x4034_0000_0000_0000)).floor().sub(D_HALF),
        ok_: difficulty_range(od, F64::from_bits(0x4061_8000_0000_0000), F64::from_bits(0x4059_0000_0000_0000), F64::from_bits(0x404E_0000_0000_0000)).floor().sub(D_HALF),
        meh: difficulty_range(od, F64::from_bits(0x4069_0000_0000_0000), F64::from_bits(0x4062_C000_0000_0000), F64::from_bits(0x4059_0000_0000_0000)).floor().sub(D_HALF),
    }
}

/// `HitWindows.WindowFor(HitResult.Miss)`; spec `HitWindows.missWindow`
pub fn miss_window(h: HitWindows) -> F64 {
    match h {
        HitWindows::Empty => D0,
        HitWindows::Osu { .. } => MISS_WINDOW,
    }
}

/// Kinds of nested objects; spec `NestedKind`
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum NestedKind {
    Head,
    Tick,
    Repeat,
    Tail,
    SpinnerTick,
    SpinnerBonusTick,
}

/// A nested `OsuHitObject`; spec `NestedObject`
#[derive(Clone, Copy)]
pub struct NestedObject {
    pub kind: NestedKind,
    pub start_time: F64,
    pub position: Vec2,
    pub stack_height: i32,
    pub scale: F32,
    pub time_preempt: F64,
    pub time_fade_in: F64,
    pub hit_windows: HitWindows,
    pub path_progress: F64,
    pub span_index: i32,
    pub span_start_time: F64,
    pub repeat_index: i32,
    pub spinner_duration: F64,
    pub classic_slider_behaviour: bool,
    pub kiai: bool,
    pub strict_tracking_tail: bool,
}

const D600: F64 = F64::from_bits(0x4082_C000_0000_0000);
const D400: F64 = F64::from_bits(0x4079_0000_0000_0000);

/// a `NestedObject` with the spec's field defaults
pub fn nested_default(kind: NestedKind, start_time: F64) -> NestedObject {
    NestedObject {
        kind,
        start_time,
        position: v::ZERO,
        stack_height: 0,
        scale: F32_ONE,
        time_preempt: D600,
        time_fade_in: D400,
        hit_windows: HitWindows::Empty,
        path_progress: D0,
        span_index: 0,
        span_start_time: D0,
        repeat_index: 0,
        spinner_duration: D0,
        classic_slider_behaviour: false,
        kiai: false,
        strict_tracking_tail: false,
    }
}

/// Slider-specific state; spec `SliderData`
#[derive(Clone)]
pub struct SliderData {
    pub path: SliderPath,
    pub repeat_count: i32,
    pub velocity: F64,
    pub tick_distance: F64,
    pub tick_distance_multiplier: F64,
    pub slider_velocity_multiplier: F64,
    pub generate_ticks: bool,
    pub classic_slider_behaviour: bool,
    pub strict_tracking: bool,
}

/// Spinner-specific state; spec `SpinnerData`
#[derive(Clone, Copy)]
pub struct SpinnerData {
    pub duration: F64,
    pub spins_required: i32,
    pub maximum_bonus_spins: i32,
}

/// spec `ObjectKind`
#[derive(Clone)]
pub enum ObjectKind {
    Circle,
    Slider(SliderData),
    Spinner(SpinnerData),
}

/// A top-level `OsuHitObject`; spec `OsuHitObject`
#[derive(Clone)]
pub struct OsuHitObject {
    pub kind: ObjectKind,
    pub start_time: F64,
    pub position: Vec2,
    pub stack_height: i32,
    pub scale: F32,
    pub time_preempt: F64,
    pub time_fade_in: F64,
    pub new_combo: bool,
    pub combo_offset: i32,
    pub combo_index: i32,
    pub combo_index_with_offsets: i32,
    pub index_in_current_combo: i32,
    pub last_in_combo: bool,
    pub kiai: bool,
    pub hit_windows: Option<HitWindows>,
    pub nested: Vec<NestedObject>,
}

/// an `OsuHitObject` with the spec's field defaults
pub fn object_default(kind: ObjectKind, start_time: F64, position: Vec2) -> OsuHitObject {
    OsuHitObject {
        kind,
        start_time,
        position,
        stack_height: 0,
        scale: F32_ONE,
        time_preempt: D600,
        time_fade_in: D400,
        new_combo: false,
        combo_offset: 0,
        combo_index: 0,
        combo_index_with_offsets: 0,
        index_in_current_combo: 0,
        last_in_combo: false,
        kiai: false,
        hit_windows: None,
        nested: Vec::new(),
    }
}

/// `OBJECT_RADIUS = 64f`
pub const OBJECT_RADIUS: F32 = F32::from_bits(0x4280_0000);
/// `BASE_SCORING_DISTANCE = 100f`
pub const BASE_SCORING_DISTANCE: F32 = F32::from_bits(0x42C8_0000);

/// `SpanCount() => RepeatCount + 1`; spec `SliderData.spanCount`
pub fn span_count(s: &SliderData) -> i32 {
    s.repeat_count.wrapping_add(1)
}

/// `ProgressAt(progress)`; spec `SliderData.progressAt`
pub fn progress_at(s: &SliderData, progress: F64) -> F64 {
    let sc = F64::from_i64(span_count(s) as i64);
    let p = fmod1(progress.mul(sc));
    let span_at = progress.mul(sc).to_i32_sat();
    if span_at % 2 == 1 { D1.sub(p) } else { p }
}

/// `CurvePositionAt(progress)`; spec `SliderData.curvePositionAt`
pub fn curve_position_at(s: &SliderData, progress: F64) -> Vec2 {
    slider_path::position_at(&s.path, progress_at(s, progress))
}

/// `GetEndTime()`; spec `OsuHitObject.endTime`
pub fn end_time(h: &OsuHitObject) -> F64 {
    match &h.kind {
        ObjectKind::Slider(s) => h.start_time.add(F64::from_i64(span_count(s) as i64).mul(slider_path::distance(&s.path)).div(s.velocity)),
        ObjectKind::Spinner(s) => h.start_time.add(s.duration),
        ObjectKind::Circle => h.start_time,
    }
}

/// `Duration`; spec `OsuHitObject.duration`
pub fn duration(h: &OsuHitObject) -> F64 {
    match &h.kind {
        ObjectKind::Spinner(s) => s.duration,
        _ => end_time(h).sub(h.start_time),
    }
}

/// `SpanDuration`; spec `OsuHitObject.spanDuration`
pub fn span_duration(h: &OsuHitObject) -> F64 {
    match &h.kind {
        ObjectKind::Slider(s) => duration(h).div(F64::from_i64(span_count(s) as i64)),
        _ => duration(h),
    }
}

/// `EndPosition`; spec `OsuHitObject.endPosition`
pub fn end_position(h: &OsuHitObject) -> Vec2 {
    match &h.kind {
        ObjectKind::Slider(s) => v::add(h.position, curve_position_at(s, D1)),
        _ => h.position,
    }
}

const F32_M6_4: F32 = F32::from_bits(0xC0CC_CCCD);

/// `StackOffset` (zero for spinners); spec `OsuHitObject.stackOffset`
pub fn stack_offset(h: &OsuHitObject) -> Vec2 {
    match &h.kind {
        ObjectKind::Spinner(_) => v::ZERO,
        _ => v::splat(F32::from_i64(h.stack_height as i64).mul(h.scale).mul(F32_M6_4)),
    }
}
pub fn stacked_position(h: &OsuHitObject) -> Vec2 {
    v::add(h.position, stack_offset(h))
}
pub fn stacked_end_position(h: &OsuHitObject) -> Vec2 {
    v::add(end_position(h), stack_offset(h))
}
/// `Radius`; spec `OsuHitObject.radius`
pub fn radius(h: &OsuHitObject) -> F64 {
    OBJECT_RADIUS.mul(h.scale).to_f64()
}
pub fn is_spinner(h: &OsuHitObject) -> bool {
    match &h.kind {
        ObjectKind::Spinner(_) => true,
        _ => false,
    }
}
pub fn is_slider(h: &OsuHitObject) -> bool {
    match &h.kind {
        ObjectKind::Slider(_) => true,
        _ => false,
    }
}
pub fn is_circle(h: &OsuHitObject) -> bool {
    match &h.kind {
        ObjectKind::Circle => true,
        _ => false,
    }
}

/// `MaximumJudgementOffset`; spec `OsuHitObject.maximumJudgementOffset`
pub fn maximum_judgement_offset(h: &OsuHitObject) -> F64 {
    match h.hit_windows {
        Some(w) => miss_window(w),
        None => D0,
    }
}

/// `StackHeight` setter (propagates to nested objects); spec `OsuHitObject.setStackHeight`
pub fn set_stack_height(h: &mut OsuHitObject, val: i32) {
    h.stack_height = val;
    let mut i = 0;
    while i < h.nested.len() {
        h.nested[i].stack_height = val;
        i = i + 1;
    }
}

/// spec `NestedObject.stackOffset`
pub fn nested_stack_offset(n: &NestedObject) -> Vec2 {
    v::splat(F32::from_i64(n.stack_height as i64).mul(n.scale).mul(F32_M6_4))
}
pub fn nested_stacked_position(n: &NestedObject) -> Vec2 {
    v::add(n.position, nested_stack_offset(n))
}
pub fn nested_radius(n: &NestedObject) -> F64 {
    OBJECT_RADIUS.mul(n.scale).to_f64()
}
/// spec `NestedObject.maximumJudgementOffset`
pub fn nested_maximum_judgement_offset(n: &NestedObject) -> F64 {
    match n.kind {
        NestedKind::SpinnerTick | NestedKind::SpinnerBonusTick => n.spinner_duration,
        _ => miss_window(n.hit_windows),
    }
}

// ------------------------------------------------------------------------------ ApplyDefaults

const D1800: F64 = F64::from_bits(0x409C_2000_0000_0000);
const D1200: F64 = F64::from_bits(0x4092_C000_0000_0000);
const D450: F64 = F64::from_bits(0x407C_2000_0000_0000);

/// `TimePreempt = (int)DifficultyRange(AR, 1800, 1200, 450)`; spec `timePreemptFor`
pub fn time_preempt_for(ar: F32) -> F64 {
    F64::from_i64(difficulty_range(ar.to_f64(), D1800, D1200, D450).to_i32_sat() as i64)
}

/// `TimeFadeIn = 400 * Math.Min(1, TimePreempt / PREEMPT_MIN)`; spec `timeFadeInFor`
pub fn time_fade_in_for(preempt: F64) -> F64 {
    D400.mul(f64_min(D1, preempt.div(D450)))
}

/// spec `CommonDefaults`
#[derive(Clone, Copy)]
pub struct CommonDefaults {
    pub time_preempt: F64,
    pub time_fade_in: F64,
    pub scale: F32,
}

/// spec `commonDefaults`
pub fn common_defaults(d: &Difficulty) -> CommonDefaults {
    let p = time_preempt_for(d.approach_rate);
    CommonDefaults { time_preempt: p, time_fade_in: time_fade_in_for(p), scale: calculate_scale_from_circle_size(d.circle_size, true) }
}

const D_M100: F64 = F64::from_bits(0xC059_0000_0000_0000);
const D100: F64 = F64::from_bits(0x4059_0000_0000_0000);
const F10: F32 = F32::from_bits(0x4120_0000);
const F1000: F32 = F32::from_bits(0x447A_0000);

/// `GetPrecisionAdjustedBeatLength`; spec `getPrecisionAdjustedBeatLength`
pub fn get_precision_adjusted_beat_length(slider_velocity_multiplier: F64, tp: &TimingPoint) -> F64 {
    let slider_velocity_as_beat_length = D_M100.div(slider_velocity_multiplier);
    let bpm_multiplier = if slider_velocity_as_beat_length.lt(D0) {
        let vv = slider_velocity_as_beat_length.neg().to_f32();
        let c = if vv.lt(F10) { F10 } else if F1000.lt(vv) { F1000 } else { vv };
        c.to_f64().div(D100)
    } else {
        D1
    };
    tp.beat_length.mul(bpm_multiplier)
}

const F_0_66: F32 = F32::from_bits(0x3F28_F5C3);
const D200: F64 = F64::from_bits(0x4069_0000_0000_0000);

/// `ApplyDefaults` of a nested object; spec `applyNestedDefaults`
pub fn apply_nested_defaults(cpi: &ControlPointInfo, d: &Difficulty, slider_start: F64, span_dur: F64, n: &mut NestedObject) {
    let c = common_defaults(d);
    n.time_preempt = c.time_preempt;
    n.time_fade_in = c.time_fade_in;
    n.scale = c.scale;
    n.kiai = effect_point_at(cpi, n.start_time.add(D1)).kiai;
    match n.kind {
        NestedKind::Head => {
            n.hit_windows = osu_hit_windows(d.overall_difficulty.to_f64());
        }
        NestedKind::Repeat | NestedKind::Tail => {
            if n.repeat_index > 0 {
                n.time_fade_in = D0;
                n.time_preempt = span_dur.mul(D2);
            } else {
                n.time_preempt = n.time_preempt.add(n.start_time.sub(slider_start));
            }
        }
        NestedKind::Tick => {
            let offset = if n.span_index > 0 { D200 } else { n.time_preempt.mul(F_0_66.to_f64()) };
            n.time_preempt = n.start_time.sub(n.span_start_time).div(D2).add(offset);
        }
        NestedKind::SpinnerTick | NestedKind::SpinnerBonusTick => {}
    }
}

impl SortCmp for NestedObject {
    fn cmp3(&self, other: &NestedObject) -> i32 {
        compare_f64(self.start_time, other.start_time)
    }
}

impl SortKey for OsuHitObject {
    fn sort_key(&self) -> F64 {
        self.start_time
    }
}

/// `nestedHitObjects.Sort(by StartTime)` (introsort); spec `sortNested`
pub fn sort_nested(ns: &mut Vec<NestedObject>) {
    list_sort(ns);
}

/// `Slider.CreateNestedHitObjects`; spec `sliderNested`
pub fn slider_nested(h: &OsuHitObject, s: &SliderData) -> Result<Vec<NestedObject>, DecodeError> {
    let events = tri!(generate(h.start_time, span_duration(h), s.velocity, s.tick_distance, slider_path::distance(&s.path), span_count(s)));
    let mut out: Vec<NestedObject> = Vec::new();
    let mut i = 0;
    while i < events.len() {
        let e = events[i];
        match e.etype {
            SliderEventType::Tick => {
                let mut n = nested_default(NestedKind::Tick, e.time);
                n.span_index = e.span_index;
                n.span_start_time = e.span_start_time;
                n.position = v::add(h.position, slider_path::position_at(&s.path, e.path_progress));
                n.path_progress = e.path_progress;
                n.stack_height = h.stack_height;
                out.push(n);
            }
            SliderEventType::Head => {
                let mut n = nested_default(NestedKind::Head, e.time);
                n.position = h.position;
                n.stack_height = h.stack_height;
                n.classic_slider_behaviour = s.classic_slider_behaviour;
                out.push(n);
            }
            SliderEventType::Tail => {
                let mut n = nested_default(NestedKind::Tail, e.time);
                n.repeat_index = e.span_index;
                n.position = end_position(h);
                n.stack_height = h.stack_height;
                n.classic_slider_behaviour = s.classic_slider_behaviour;
                n.strict_tracking_tail = s.strict_tracking;
                out.push(n);
            }
            SliderEventType::Repeat => {
                let st = h.start_time.add(F64::from_i64(e.span_index.wrapping_add(1) as i64).mul(span_duration(h)));
                let mut n = nested_default(NestedKind::Repeat, st);
                n.repeat_index = e.span_index;
                n.position = v::add(h.position, slider_path::position_at(&s.path, e.path_progress));
                n.stack_height = h.stack_height;
                n.path_progress = e.path_progress;
                out.push(n);
            }
            SliderEventType::LegacyLastTick => {}
        }
        i = i + 1;
    }
    Ok(out)
}

const D60: F64 = F64::from_bits(0x404E_0000_0000_0000);
const D1000: F64 = F64::from_bits(0x408F_4000_0000_0000);
const DURATION_ERROR: F64 = F64::from_bits(0x3F1A_36E2_EB1C_432D); // 0.0001

/// `Spinner.ApplyDefaultsToSelf`; spec `spinnerDefaults`
pub fn spinner_defaults(d: &Difficulty, s: SpinnerData) -> SpinnerData {
    let od = d.overall_difficulty.to_f64();
    let min_rps = difficulty_range(od, F64::from_bits(0x4056_8000_0000_0000), F64::from_bits(0x4062_C000_0000_0000), F64::from_bits(0x406C_2000_0000_0000)).div(D60);
    let max_rps = difficulty_range(od, F64::from_bits(0x406F_4000_0000_0000), F64::from_bits(0x4077_C000_0000_0000), F64::from_bits(0x407A_E000_0000_0000)).div(D60);
    let seconds_duration = s.duration.div(D1000);
    let spins_required = min_rps.mul(seconds_duration).add(DURATION_ERROR).to_i32_sat();
    let bonus = max_rps.mul(seconds_duration).add(DURATION_ERROR).to_i32_sat().wrapping_sub(spins_required).wrapping_sub(2);
    SpinnerData { duration: s.duration, spins_required, maximum_bonus_spins: if bonus < 0 { 0 } else { bonus } }
}

/// `Spinner.CreateNestedHitObjects`; spec `spinnerNested`
pub fn spinner_nested(h: &OsuHitObject, s: &SpinnerData) -> Vec<NestedObject> {
    let total_spins: i32 = s.maximum_bonus_spins.wrapping_add(s.spins_required).wrapping_add(2);
    let mut out: Vec<NestedObject> = Vec::new();
    let n: i32 = if total_spins < 0 { 0 } else { total_spins };
    let ts = F32::from_i64(total_spins as i64);
    let mut i: i32 = 0;
    while i < n {
        let st = h.start_time.add(F32::from_i64(i.wrapping_add(1) as i64).div(ts).to_f64().mul(s.duration));
        let kind = if i < s.spins_required.wrapping_add(2) { NestedKind::SpinnerTick } else { NestedKind::SpinnerBonusTick };
        let mut nn = nested_default(kind, st);
        nn.spinner_duration = s.duration;
        out.push(nn);
        i = i + 1;
    }
    out
}

/// `HitObject.ApplyDefaults(controlPointInfo, difficulty)`; spec `applyDefaults`
pub fn apply_defaults(cpi: &ControlPointInfo, d: &Difficulty, h: &mut OsuHitObject) -> Result<(), DecodeError> {
    let c = common_defaults(d);
    let hw0 = match h.hit_windows {
        Some(w) => w,
        None => match &h.kind {
            ObjectKind::Circle => osu_hit_windows(d.overall_difficulty.to_f64()),
            _ => HitWindows::Empty,
        },
    };
    let hw = match hw0 {
        HitWindows::Osu { .. } => osu_hit_windows(d.overall_difficulty.to_f64()),
        w => w,
    };
    h.time_preempt = c.time_preempt;
    h.time_fade_in = c.time_fade_in;
    h.scale = c.scale;
    h.hit_windows = Some(hw);
    h.kiai = effect_point_at(cpi, h.start_time.add(D1)).kiai;
    // kind-specific ApplyDefaultsToSelf
    let start = h.start_time;
    match &mut h.kind {
        ObjectKind::Circle => {}
        ObjectKind::Spinner(s) => {
            *s = spinner_defaults(d, *s);
        }
        ObjectKind::Slider(s) => {
            let tp = timing_point_at(cpi, start);
            let velocity = BASE_SCORING_DISTANCE.to_f64().mul(d.slider_multiplier).div(get_precision_adjusted_beat_length(s.slider_velocity_multiplier, &tp));
            let scoring_distance = velocity.mul(tp.beat_length);
            let tick_distance = if s.generate_ticks {
                scoring_distance.div(d.slider_tick_rate).mul(s.tick_distance_multiplier)
            } else {
                F64::from_bits(0x7FF0_0000_0000_0000)
            };
            s.velocity = velocity;
            s.tick_distance = tick_distance;
        }
    }
    // CreateNestedHitObjects
    let mut nested = match &h.kind {
        ObjectKind::Circle => Vec::new(),
        ObjectKind::Spinner(s) => spinner_nested(h, s),
        ObjectKind::Slider(s) => tri!(slider_nested(h, s)),
    };
    sort_nested(&mut nested);
    let sd = span_duration(h);
    let mut i = 0;
    while i < nested.len() {
        apply_nested_defaults(cpi, d, start, sd, &mut nested[i]);
        i = i + 1;
    }
    h.nested = nested;
    Ok(())
}
