//! Port of `OsuModel/Eval/Adapter.lean`: Beatmap model -> simulation input
//! (`OsuModel.Beatmap.PlayableBeatmap` -> `OsuModel.Sim.Playable`), field by field the C# getters the
//! oracle's `--dump-playable` reads (`oracle/Dump.cs:68-215`). The spec's `HObj.typeName : String`
//! is `type_id` (ids below; texts in `text::type_name`, the spec's string literals).
use crate::beatmap::objects::{self as bo, HitWindows as BHitWindows, NestedKind, NestedObject, ObjectKind, OsuHitObject, MISS_WINDOW};
use crate::beatmap::playable::PlayableBeatmap;
use crate::beatmap::slider_path;
use crate::beatmap::types::Difficulty as BDifficulty;
use crate::beatmap::vector2::Vec2 as BVec2;
use crate::sim::basic::{HitResult, Vec2};
use crate::sim::playable::{Difficulty, HObj, HitWindows, Kind, Period, Playable, SliderData, SpinnerData, TopObj};
use alloc::vec::Vec;

/// `typeName` ids of the adapter's type names (0 = `""`, unused here)
pub const T_HIT_CIRCLE: u32 = 1;
pub const T_SLIDER: u32 = 2;
pub const T_STRICT_TRACKING_SLIDER: u32 = 3;
pub const T_SPINNER: u32 = 4;
pub const T_SLIDER_HEAD_CIRCLE: u32 = 5;
pub const T_SLIDER_TICK: u32 = 6;
pub const T_SLIDER_REPEAT: u32 = 7;
pub const T_SLIDER_TAIL_CIRCLE: u32 = 8;
pub const T_STRICT_TRACKING_SLIDER_TAIL_CIRCLE: u32 = 9;
pub const T_SPINNER_TICK: u32 = 10;
pub const T_SPINNER_BONUS_TICK: u32 = 11;

/// spec `vec`
pub fn vec(v: BVec2) -> Vec2 {
    Vec2 { x: v.x, y: v.y }
}

/// spec `windows`
pub fn windows(w: BHitWindows) -> Option<HitWindows> {
    match w {
        BHitWindows::Empty => None,
        BHitWindows::Osu { great, ok_, meh } => Some(HitWindows { great, ok_, meh, miss: MISS_WINDOW }),
    }
}

/// spec `defaultMinResult` (`Judgement.MinResult` default, `osu.Game/Rulesets/Judgements/Judgement.cs:61-84`)
pub fn default_min_result(r: HitResult) -> HitResult {
    match r {
        HitResult::SmallBonus => HitResult::IgnoreMiss,
        HitResult::LargeBonus => HitResult::IgnoreMiss,
        HitResult::IgnoreHit => HitResult::IgnoreMiss,
        HitResult::SmallTickHit => HitResult::SmallTickMiss,
        HitResult::LargeTickHit => HitResult::LargeTickMiss,
        HitResult::SliderTailHit => HitResult::IgnoreMiss,
        _ => HitResult::Miss,
    }
}

/// spec `judgementOf` (`CreateJudgement()` -> (MaxResult, MinResult); source lines in the spec)
pub fn judgement_of(k: Kind, classic: bool, strict_tail: bool) -> (HitResult, HitResult) {
    let mx: HitResult = match k {
        Kind::Circle => HitResult::Great,
        Kind::Spinner => HitResult::Great,
        Kind::Slider => {
            if classic { HitResult::Great } else { HitResult::IgnoreHit }
        }
        Kind::Head => {
            if classic { HitResult::LargeTickHit } else { HitResult::Great }
        }
        Kind::Tick => HitResult::LargeTickHit,
        Kind::Repeat => HitResult::LargeTickHit,
        Kind::Tail => {
            if strict_tail {
                HitResult::SliderTailHit
            } else if classic {
                HitResult::SmallTickHit
            } else {
                HitResult::SliderTailHit
            }
        }
        Kind::SpinnerTick => HitResult::SmallBonus,
        Kind::SpinnerBonusTick => HitResult::LargeBonus,
    };
    let mn = if k == Kind::Tail && strict_tail { HitResult::LargeTickMiss } else { default_min_result(mx) };
    (mx, mn)
}

/// spec `nestedKind`
pub fn nested_kind(k: NestedKind) -> Kind {
    match k {
        NestedKind::Head => Kind::Head,
        NestedKind::Tick => Kind::Tick,
        NestedKind::Repeat => Kind::Repeat,
        NestedKind::Tail => Kind::Tail,
        NestedKind::SpinnerTick => Kind::SpinnerTick,
        NestedKind::SpinnerBonusTick => Kind::SpinnerBonusTick,
    }
}

/// `Kind.typeName` as a `type_id`
pub fn kind_type_id(k: Kind) -> u32 {
    match k {
        Kind::Circle => T_HIT_CIRCLE,
        Kind::Slider => T_SLIDER,
        Kind::Spinner => T_SPINNER,
        Kind::Head => T_SLIDER_HEAD_CIRCLE,
        Kind::Tick => T_SLIDER_TICK,
        Kind::Repeat => T_SLIDER_REPEAT,
        Kind::Tail => T_SLIDER_TAIL_CIRCLE,
        Kind::SpinnerTick => T_SPINNER_TICK,
        Kind::SpinnerBonusTick => T_SPINNER_BONUS_TICK,
    }
}

/// spec `nestedTypeName`
pub fn nested_type_name(n: &NestedObject) -> u32 {
    match n.kind {
        NestedKind::Tail => {
            if n.strict_tracking_tail { T_STRICT_TRACKING_SLIDER_TAIL_CIRCLE } else { T_SLIDER_TAIL_CIRCLE }
        }
        k => kind_type_id(nested_kind(k)),
    }
}

/// `Int32.toNatClampNeg`
pub fn nat_clamp_neg(x: i32) -> u64 {
    if x < 0 { 0 } else { x as u64 }
}

/// spec `adaptNested`
pub fn adapt_nested(h: &OsuHitObject, n: &NestedObject) -> HObj {
    let kind = nested_kind(n.kind);
    let (max_result, min_result) = judgement_of(kind, n.classic_slider_behaviour, n.strict_tracking_tail);
    let type_id = nested_type_name(n);
    HObj {
        kind,
        type_id,
        start: n.start_time,
        end_time: n.start_time,
        pos: vec(n.position),
        stacked: vec(bo::nested_stacked_position(n)),
        stack_height: n.stack_height as i64,
        scale: n.scale,
        radius: bo::nested_radius(n),
        preempt: n.time_preempt,
        fade_in: n.time_fade_in,
        max_judgement_offset: bo::nested_maximum_judgement_offset(n),
        hit_windows: windows(n.hit_windows),
        max_result,
        min_result,
        new_combo: false,
        combo_index: nat_clamp_neg(h.combo_index),
        index_in_combo: nat_clamp_neg(h.index_in_current_combo),
        last_in_combo: false,
        span_index: nat_clamp_neg(n.span_index),
        span_start: n.span_start_time,
        path_progress: n.path_progress,
        repeat_index: nat_clamp_neg(n.repeat_index),
        strict_tail: type_id == T_STRICT_TRACKING_SLIDER_TAIL_CIRCLE,
    }
}

/// part of spec `adaptObject`: `match h.hitWindows with | some w => windows w | none => none`
pub fn top_windows(w: Option<BHitWindows>) -> Option<HitWindows> {
    match w {
        Some(x) => windows(x),
        None => None,
    }
}

/// part of spec `adaptObject`: `h.nested.map (adaptNested h)`
pub fn adapt_nested_all(h: &OsuHitObject) -> Vec<HObj> {
    let mut out: Vec<HObj> = Vec::with_capacity(h.nested.len());
    let mut i = 0;
    while i < h.nested.len() {
        out.push(adapt_nested(h, &h.nested[i]));
        i = i + 1;
    }
    out
}

/// part of spec `adaptObject`: `s.path.calculatedPath.map vec`
pub fn path_vec(p: &[BVec2]) -> Vec<Vec2> {
    let mut out: Vec<Vec2> = Vec::with_capacity(p.len());
    let mut i = 0;
    while i < p.len() {
        out.push(vec(p[i]));
        i = i + 1;
    }
    out
}

/// spec `adaptObject`
pub fn adapt_object(h: &OsuHitObject) -> TopObj {
    let (kind, type_id, classic, slider, spinner): (Kind, u32, bool, Option<SliderData>, Option<SpinnerData>) = match &h.kind {
        ObjectKind::Circle => (Kind::Circle, T_HIT_CIRCLE, false, None, None),
        ObjectKind::Slider(s) => (
            Kind::Slider,
            if s.strict_tracking { T_STRICT_TRACKING_SLIDER } else { T_SLIDER },
            s.classic_slider_behaviour,
            Some(SliderData {
                span_count: nat_clamp_neg(bo::span_count(s)),
                duration: bo::duration(h),
                span_duration: bo::span_duration(h),
                velocity: s.velocity,
                path_distance: slider_path::distance(&s.path),
                classic: s.classic_slider_behaviour,
                path: path_vec(&s.path.calculated_path),
                cum_len: s.path.cumulative_length.clone(),
            }),
            None,
        ),
        ObjectKind::Spinner(s) => (
            Kind::Spinner,
            T_SPINNER,
            false,
            None,
            Some(SpinnerData { duration: s.duration, spins_required: s.spins_required as i64, max_bonus_spins: s.maximum_bonus_spins as i64 }),
        ),
    };
    let (max_result, min_result) = judgement_of(kind, classic, false);
    let ho = HObj {
        kind,
        type_id,
        start: h.start_time,
        end_time: bo::end_time(h),
        pos: vec(h.position),
        stacked: vec(bo::stacked_position(h)),
        stack_height: h.stack_height as i64,
        scale: h.scale,
        radius: bo::radius(h),
        preempt: h.time_preempt,
        fade_in: h.time_fade_in,
        max_judgement_offset: bo::maximum_judgement_offset(h),
        hit_windows: top_windows(h.hit_windows),
        max_result,
        min_result,
        new_combo: h.new_combo,
        combo_index: nat_clamp_neg(h.combo_index),
        index_in_combo: nat_clamp_neg(h.index_in_current_combo),
        last_in_combo: h.last_in_combo,
        span_index: 0,
        span_start: crate::float::F64::from_bits(0),
        path_progress: crate::float::F64::from_bits(0),
        repeat_index: 0,
        strict_tail: false,
    };
    TopObj { h: ho, slider, spinner, nested: adapt_nested_all(h) }
}

/// spec `adaptDifficulty`
pub fn adapt_difficulty(d: &BDifficulty) -> Difficulty {
    Difficulty { cs: d.circle_size, hp: d.drain_rate, od: d.overall_difficulty, ar: d.approach_rate }
}

/// part of spec `toSimPlayable`: `pb.breaks.map fun b => (b.startTime, b.endTime)`
pub fn adapt_breaks(pb: &PlayableBeatmap) -> Vec<Period> {
    let mut out: Vec<Period> = Vec::with_capacity(pb.breaks.len());
    let mut i = 0;
    while i < pb.breaks.len() {
        out.push(Period { start: pb.breaks[i].start_time, end: pb.breaks[i].end_time });
        i = i + 1;
    }
    out
}

/// part of spec `toSimPlayable`: `pb.hitObjects.map adaptObject`
pub fn adapt_objects(pb: &PlayableBeatmap) -> Vec<TopObj> {
    let mut out: Vec<TopObj> = Vec::with_capacity(pb.hit_objects.len());
    let mut i = 0;
    while i < pb.hit_objects.len() {
        out.push(adapt_object(&pb.hit_objects[i]));
        i = i + 1;
    }
    out
}

/// spec `toSimPlayable` (the adapter)
pub fn to_sim_playable(pb: &PlayableBeatmap) -> Playable {
    Playable {
        beatmap_version: pb.format_version as i64,
        audio_lead_in: pb.audio_lead_in,
        difficulty: adapt_difficulty(&pb.difficulty),
        base_difficulty: adapt_difficulty(&pb.base_difficulty),
        slider_multiplier: pb.difficulty.slider_multiplier,
        slider_tick_rate: pb.difficulty.slider_tick_rate,
        breaks: adapt_breaks(pb),
        objects: adapt_objects(pb),
    }
}

/// Texts (not translated; excluded from Charon).
pub mod text {
    /// the spec's type-name string of a `type_id`
    pub fn type_name(t: u32) -> &'static str {
        match t {
            1 => "HitCircle",
            2 => "Slider",
            3 => "StrictTrackingSlider",
            4 => "Spinner",
            5 => "SliderHeadCircle",
            6 => "SliderTick",
            7 => "SliderRepeat",
            8 => "SliderTailCircle",
            9 => "StrictTrackingSliderTailCircle",
            10 => "SpinnerTick",
            11 => "SpinnerBonusTick",
            _ => "",
        }
    }
}
