//! Port of `OsuModel/Beatmap/Types.lean`: data types shared by the decoder and the converter.
use super::control_points::{cpi_empty, ControlPointInfo};
use super::vector2::Vec2;
use crate::float::{F32, F64};
use alloc::vec::Vec;

/// `SplineType` + `PathType.Degree`; spec `PathType` (`BSpline(None)` = `PathType.BEZIER`)
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum PathType {
    Catmull,
    BSpline(Option<i32>),
    Linear,
    PerfectCurve,
}

/// Lean `BEq PathType` (derived: structural)
pub fn path_type_eq(a: PathType, b: PathType) -> bool {
    a == b
}

/// `PathControlPoint`; spec `PathControlPoint` (`type` is `ptype`)
#[derive(Clone, Copy)]
pub struct PathControlPoint {
    pub position: Vec2,
    pub ptype: Option<PathType>,
}

/// `BeatmapDifficulty`; spec `Difficulty`
#[derive(Clone, Copy)]
pub struct Difficulty {
    pub drain_rate: F32,
    pub circle_size: F32,
    pub overall_difficulty: F32,
    pub approach_rate: F32,
    pub slider_multiplier: F64,
    pub slider_tick_rate: F64,
}

/// spec `Difficulty` defaults (5, 5, 5, 5, 1.4, 1)
pub const DIFFICULTY_DEFAULT: Difficulty = Difficulty {
    drain_rate: F32::from_bits(0x40A0_0000),
    circle_size: F32::from_bits(0x40A0_0000),
    overall_difficulty: F32::from_bits(0x40A0_0000),
    approach_rate: F32::from_bits(0x40A0_0000),
    slider_multiplier: F64::from_bits(0x3FF6_6666_6666_6666),
    slider_tick_rate: F64::from_bits(0x3FF0_0000_0000_0000),
};

/// `Convert*` hit object kinds; spec `ConvertKind`
#[derive(Clone)]
pub enum ConvertKind {
    Circle,
    Slider { control_points: Vec<PathControlPoint>, expected_distance: Option<F64>, repeat_count: i32 },
    Spinner(F64),
    Hold(F64),
}

/// spec `ConvertHitObject`
#[derive(Clone)]
pub struct ConvertHitObject {
    pub start_time: F64,
    pub position: Vec2,
    pub new_combo: bool,
    pub combo_offset: i32,
    pub kind: ConvertKind,
    pub generate_ticks: bool,
    pub slider_velocity_multiplier: F64,
}

/// `BreakPeriod`; spec `BreakPeriod`
#[derive(Clone, Copy)]
pub struct BreakPeriod {
    pub start_time: F64,
    pub end_time: F64,
}

/// The decoded `Beatmap`; spec `DecodedBeatmap`
#[derive(Clone)]
pub struct DecodedBeatmap {
    pub format_version: i32,
    pub ruleset_id: i32,
    pub difficulty: Difficulty,
    pub stack_leniency: F32,
    pub audio_lead_in: F64,
    pub control_points: ControlPointInfo,
    pub breaks: Vec<BreakPeriod>,
    pub hit_objects: Vec<ConvertHitObject>,
}

pub fn decoded_empty(format_version: i32) -> DecodedBeatmap {
    DecodedBeatmap {
        format_version,
        ruleset_id: 0,
        difficulty: DIFFICULTY_DEFAULT,
        stack_leniency: F32::from_bits(0x3F33_3333),
        audio_lead_in: F64::from_bits(0),
        control_points: cpi_empty(),
        breaks: Vec::new(),
        hit_objects: Vec::new(),
    }
}
