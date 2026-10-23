//! Port of `OsuModel/Beatmap/Playable.lean`: `OsuBeatmapConverter`, `BeatmapConverter.Convert`,
//! `WorkingBeatmap.GetPlayableBeatmap`. The spec's `Mod` hook record (closures) is the dispatch
//! in `beatmap::mods` (`ModConfig.allHooks`): `apply_after_conversion`, `apply_to_difficulty`,
//! `apply_to_hit_object`, `apply_to_beatmap`, consulted in the same order.
use super::control_points::{clamp_sv, deep_clone, difficulty_point_at, ControlPointInfo};
use super::decoder;
use super::dotnet::stable_sort_by;
use super::errors::M_SLIDER_PATH_FUEL_EXHAUSTED;
use super::hit_object_parser::DecodeError;
use super::mod_settings::ModConfig;
use super::mods;
use super::objects::{apply_defaults, end_position, object_default, NestedKind, ObjectKind, OsuHitObject, SliderData, SpinnerData};
use super::processor::{apply_stacking_all, pre_process};
use super::slider_path::{self, of_control_points};
use super::types::{BreakPeriod, ConvertHitObject, ConvertKind, DecodedBeatmap, Difficulty};
use super::vector2 as v;
use crate::float::{F32, F64};
use alloc::vec::Vec;

/// A reference to a (top-level or nested) hit object; spec `ObjRef`
#[derive(Clone, Copy)]
pub struct ObjRef {
    pub index: usize,
    pub nested: Option<usize>,
    pub epoch: usize,
}

/// Beatmap-derived mod state; spec `ModState`
#[derive(Clone)]
pub enum ModState {
    FirstObject(Option<ObjRef>),
    TimeRamp(F64, F64),
    PrecedingEndTimes(Vec<(ObjRef, F64)>),
}

/// The playable osu! beatmap; spec `PlayableBeatmap`
#[derive(Clone)]
pub struct PlayableBeatmap {
    pub format_version: i32,
    pub difficulty: Difficulty,
    pub base_difficulty: Difficulty,
    pub stack_leniency: F32,
    pub audio_lead_in: F64,
    pub control_points: ControlPointInfo,
    pub breaks: Vec<BreakPeriod>,
    pub hit_objects: Vec<OsuHitObject>,
    pub epoch: usize,
    pub mod_states: Vec<(usize, ModState)>,
}

const D1: F64 = F64::from_bits(0x3FF0_0000_0000_0000);

/// `Slider.updateNestedPositions()`; spec `updateNestedPositions`
pub fn update_nested_positions(h: &mut OsuHitObject) {
    let pos = h.position;
    let endp = end_position(h);
    match &h.kind {
        ObjectKind::Slider(s) => {
            let mut i = 0;
            while i < h.nested.len() {
                match h.nested[i].kind {
                    NestedKind::Head => h.nested[i].position = pos,
                    NestedKind::Tail => h.nested[i].position = endp,
                    NestedKind::Repeat | NestedKind::Tick => {
                        h.nested[i].position = v::add(pos, slider_path::position_at(&s.path, h.nested[i].path_progress));
                    }
                    _ => {}
                }
                i = i + 1;
            }
        }
        _ => {}
    }
}

/// `OsuBeatmapConverter.ConvertHitObject`; spec `convertHitObject`
pub fn convert_hit_object(format_version: i32, cpi: &ControlPointInfo, o: &ConvertHitObject) -> OsuHitObject {
    let kind = match &o.kind {
        ConvertKind::Slider { control_points, expected_distance, repeat_count } => {
            let path = of_control_points(control_points.clone(), *expected_distance, true);
            let tdm = if format_version < 8 {
                F32::from_bits(0x3F80_0000).to_f64().div(difficulty_point_at(cpi, o.start_time).slider_velocity)
            } else {
                D1
            };
            ObjectKind::Slider(SliderData {
                path,
                repeat_count: *repeat_count,
                velocity: F64::from_bits(0),
                tick_distance: F64::from_bits(0),
                tick_distance_multiplier: tdm,
                slider_velocity_multiplier: clamp_sv(o.slider_velocity_multiplier),
                generate_ticks: o.generate_ticks,
                classic_slider_behaviour: false,
                strict_tracking: false,
            })
        }
        ConvertKind::Spinner(duration) | ConvertKind::Hold(duration) => {
            let end_time = o.start_time.add(*duration);
            ObjectKind::Spinner(SpinnerData { duration: end_time.sub(o.start_time), spins_required: 1, maximum_bonus_spins: 1 })
        }
        ConvertKind::Circle => ObjectKind::Circle,
    };
    let mut h = object_default(kind, o.start_time, o.position);
    h.new_combo = o.new_combo;
    h.combo_offset = o.combo_offset;
    h
}

/// `BeatmapConverter<T>.Convert()`; spec `convertBeatmap`
pub fn convert_beatmap(d: &DecodedBeatmap) -> PlayableBeatmap {
    let cpi = deep_clone(&d.control_points);
    let mut hos: Vec<OsuHitObject> = Vec::with_capacity(d.hit_objects.len());
    let mut i = 0;
    while i < d.hit_objects.len() {
        hos.push(convert_hit_object(d.format_version, &cpi, &d.hit_objects[i]));
        i = i + 1;
    }
    stable_sort_by(&mut hos);
    PlayableBeatmap {
        format_version: d.format_version,
        difficulty: d.difficulty,
        base_difficulty: d.difficulty,
        stack_leniency: d.stack_leniency,
        audio_lead_in: d.audio_lead_in,
        control_points: cpi,
        breaks: d.breaks.clone(),
        hit_objects: hos,
        epoch: 0,
        mod_states: Vec::new(),
    }
}

/// `WorkingBeatmap.GetPlayableBeatmap(osu ruleset, mods)`; spec `getPlayableBeatmap`
pub fn get_playable_beatmap(d: &DecodedBeatmap, mods_list: &[ModConfig]) -> Result<PlayableBeatmap, DecodeError> {
    let mut bm = convert_beatmap(d);
    let mut i = 0;
    while i < mods_list.len() {
        mods::apply_after_conversion(&mods_list[i], &mut bm);
        i = i + 1;
    }
    i = 0;
    while i < mods_list.len() {
        bm.difficulty = mods::apply_to_difficulty(&mods_list[i], bm.difficulty);
        i = i + 1;
    }
    pre_process(&mut bm.hit_objects);
    let mut err: Option<DecodeError> = None;
    let mut k = 0;
    while err.is_none() && k < bm.hit_objects.len() {
        match apply_defaults(&bm.control_points, &bm.difficulty, &mut bm.hit_objects[k]) {
            Ok(_) => {}
            Err(e) => err = Some(e),
        }
        k = k + 1;
    }
    if let Some(e) = err {
        return Err(e);
    }
    i = 0;
    while i < mods_list.len() {
        if mods::has_apply_to_hit_object(&mods_list[i]) {
            let mut j = 0;
            while j < bm.hit_objects.len() {
                mods::apply_to_hit_object(&mods_list[i], &mut bm.hit_objects[j]);
                j = j + 1;
            }
        }
        i = i + 1;
    }
    apply_stacking_all(bm.format_version, bm.stack_leniency, &mut bm.hit_objects);
    i = 0;
    while err.is_none() && i < mods_list.len() {
        match mods::apply_to_beatmap(&mods_list[i], i, &mut bm) {
            Ok(_) => {}
            Err(e) => err = Some(e),
        }
        i = i + 1;
    }
    match err {
        Some(e) => Err(e),
        None => {
            // a slider path ran out of B-spline subdivision fuel (spec `pathFuelMsg`, D72)
            if any_path_fuel_out(&bm.hit_objects) {
                return Err(DecodeError::Msg(M_SLIDER_PATH_FUEL_EXHAUSTED));
            }
            Ok(bm)
        }
    }
}

/// spec `hitObjects.any (slider path fuelOut)` (end of `getPlayableBeatmap`)
pub fn any_path_fuel_out(hos: &[OsuHitObject]) -> bool {
    let mut i: usize = 0;
    while i < hos.len() {
        match &hos[i].kind {
            ObjectKind::Slider(s) => {
                if s.path.fuel_out {
                    return true;
                }
            }
            _ => {}
        }
        i = i + 1;
    }
    false
}

/// The full pipeline result; spec `LoadResult`
pub enum LoadResult {
    DecodeError(DecodeError),
    OtherRuleset(i32),
    PlayableError(DecodeError),
    Ok(PlayableBeatmap),
}

/// `.osu` bytes -> playable beatmap; spec `load`
pub fn load(bytes: &[u8], mods_list: &[ModConfig]) -> LoadResult {
    match decoder::decode(bytes) {
        Err(e) => LoadResult::DecodeError(e),
        Ok(d) => {
            if d.ruleset_id != 0 {
                LoadResult::OtherRuleset(d.ruleset_id)
            } else {
                match get_playable_beatmap(&d, mods_list) {
                    Err(e) => LoadResult::PlayableError(e),
                    Ok(pb) => LoadResult::Ok(pb),
                }
            }
        }
    }
}
