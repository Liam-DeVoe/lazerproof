//! Port of `OsuModel/Beatmap/HitObjectParser.lean` (`ConvertHitObjectParser.Parse`).
//! Errors drop the line (`LegacyDecoder.cs:69-77`); the parser state that survives a failed
//! line is modelled as in the spec.
use super::chartable::char_is_letter;
use super::errors::*;
use super::dotnet::{split, sub_str, Str};
use super::slider_path;
use super::types::{ConvertHitObject, ConvertKind, PathControlPoint, PathType};
use super::vector2::{self as v, almost_equals_f32, almost_equals_f64, Vec2};
use crate::float::{F32, F64};
use crate::net::basic::NetExn;
use crate::net::parse::{
    int_parse, parse_double_default, parse_int_default, parsing_parse_double, parsing_parse_float, MAX_COORDINATE_VALUE,
};
use crate::net::max as f64_max;
use alloc::vec::Vec;

/// `LegacyBeatmapEncoder.FIRST_LAZER_VERSION`
pub const FIRST_LAZER_VERSION: i32 = 128;

/// Errors of the decoder / converter; spec `DecodeM = Except String` (message ids: `beatmap::errors`). Only the messages that
/// can reach the dump are reproduced exactly (`render` in `beatmap::dump`); `Net(what, e)` is
/// `liftNet what` (`"{what}: {repr e}"`).
#[derive(Clone, Copy)]
pub enum DecodeError {
    Msg(u32),
    Net(u32, NetExn),
}

/// spec `liftNet`
pub fn lift_net<T>(what: u32, r: Result<T, NetExn>) -> Result<T, DecodeError> {
    match r {
        Ok(a) => Ok(a),
        Err(e) => Err(DecodeError::Net(what, e)),
    }
}

/// `array[i]` (throws); spec `at!`
pub fn at(a: &[Str], i: usize) -> Result<&Str, DecodeError> {
    if i < a.len() { Ok(&a[i]) } else { Err(DecodeError::Msg(M_INDEX_OUT_OF_RANGE)) }
}

/// `s[0]`; spec `char0`
pub fn char0(s: &[u32]) -> Result<u32, DecodeError> {
    if s.len() > 0 { Ok(s[0]) } else { Err(DecodeError::Msg(M_INDEX_0_OUT_OF_RANGE_EMPTY_STRING)) }
}

/// `ConvertHitObjectParser` fields; spec `ParserState`
#[derive(Clone, Copy)]
pub struct ParserState {
    pub offset: F64,
    pub format_version: i32,
    pub first_object: bool,
    /// `lastObject is ConvertSpinner`
    pub last_object_is_spinner: bool,
}

/// `readCustomSampleBanks(str, bankInfo, banksOnly)` (only whether it throws); spec
/// `ConvertHitObjectParser.readCustomSampleBanks`
pub fn read_custom_sample_banks(s: &[u32], banks_only: bool) -> Result<(), DecodeError> {
    if s.len() == 0 {
        return Ok(());
    }
    let sp = split(s, 0x3A);
    let _bank = tri!(lift_net(W_BANK, parse_int_default(tri!(at(&sp, 0)))));
    let _add = tri!(lift_net(W_ADDBANK, parse_int_default(tri!(at(&sp, 1)))));
    if banks_only {
        return Ok(());
    }
    if sp.len() > 2 {
        let _c = tri!(lift_net(W_CUSTOMSAMPLEBANK, parse_int_default(&sp[2])));
    }
    if sp.len() > 3 {
        let _v = tri!(lift_net(W_VOLUME, parse_int_default(&sp[3])));
    }
    Ok(())
}

/// `convertPathType(input)`; spec `ConvertHitObjectParser.convertPathType`
pub fn convert_path_type(input: &[u32]) -> Result<PathType, DecodeError> {
    let c = tri!(char0(input));
    if c == 0x42 {
        if input.len() > 1 {
            match int_parse(&sub_str(input, 1, input.len())) {
                Ok(d) => {
                    if d > 0 { Ok(PathType::BSpline(Some(d))) } else { Ok(PathType::BSpline(None)) }
                }
                Err(_) => Ok(PathType::BSpline(None)),
            }
        } else {
            Ok(PathType::BSpline(None))
        }
    } else if c == 0x4C {
        Ok(PathType::Linear)
    } else if c == 0x50 {
        Ok(PathType::PerfectCurve)
    } else {
        Ok(PathType::Catmull)
    }
}

/// A coordinate (`ParseFloat(s, MAX_COORDINATE_VALUE)`, truncated to int below v128); spec
/// `ConvertHitObjectParser.parseCoord`
pub fn parse_coord(format_version: i32, s: &[u32]) -> Result<F32, DecodeError> {
    let lim = F32::from_i64(MAX_COORDINATE_VALUE as i64);
    let v = tri!(lift_net(W_COORDINATE, parsing_parse_float(s, lim, false)));
    if format_version >= FIRST_LAZER_VERSION { Ok(v) } else { Ok(F32::from_i64(v.to_i32_sat() as i64)) }
}

/// `readPoint(value, startPos)`; spec `ConvertHitObjectParser.readPoint`
pub fn read_point(format_version: i32, value: &[u32], start_pos: Vec2) -> Result<Vec2, DecodeError> {
    let vs = split(value, 0x3A);
    let x = tri!(parse_coord(format_version, tri!(at(&vs, 0))));
    let y = tri!(parse_coord(format_version, tri!(at(&vs, 1))));
    Ok(v::sub(Vec2 { x, y }, start_pos))
}

/// `isLinear(p0, p1, p2)`; spec `ConvertHitObjectParser.isLinear`
pub fn is_linear(p0: Vec2, p1: Vec2, p2: Vec2) -> bool {
    almost_equals_f32(F32::from_bits(0), p1.y.sub(p0.y).mul(p2.x.sub(p0.x)).sub(p1.x.sub(p0.x).mul(p2.y.sub(p0.y))))
}

fn append_range(out: &mut Vec<PathControlPoint>, vs: &[PathControlPoint], lo: usize, hi: usize) {
    let mut i = lo;
    while i < hi && i < vs.len() {
        out.push(vs[i]);
        i = i + 1;
    }
}

/// `convertPoints(type, points, endPoint)` (concatenation of the yielded segments); spec
/// `ConvertHitObjectParser.convertPoints`
pub fn convert_points(format_version: i32, type0: PathType, points: &[Vec2], end_point: Option<Vec2>) -> Result<Vec<PathControlPoint>, DecodeError> {
    let mut vertices: Vec<PathControlPoint> = Vec::with_capacity(points.len());
    let mut i = 0;
    while i < points.len() {
        vertices.push(PathControlPoint { position: points[i], ptype: None });
        i = i + 1;
    }
    let mut ptype = type0;
    if ptype == PathType::PerfectCurve {
        let end_point_length: usize = if end_point.is_some() { 1 } else { 0 };
        if format_version < FIRST_LAZER_VERSION {
            if vertices.len() + end_point_length != 3 {
                ptype = PathType::BSpline(None);
            } else {
                let p2 = match end_point {
                    Some(e) => e,
                    None => points[2],
                };
                if is_linear(points[0], points[1], p2) {
                    ptype = PathType::Linear;
                }
            }
        } else if vertices.len() + end_point_length > 3 {
            ptype = PathType::BSpline(None);
        }
    }
    if vertices.len() == 0 {
        return Err(DecodeError::Msg(M_INDEX_0_OUT_OF_RANGE_NO_VERTICES));
    }
    vertices[0].ptype = Some(ptype);
    let mut out: Vec<PathControlPoint> = Vec::new();
    let mut start_index = 0;
    let mut end_index = 0;
    let n = vertices.len();
    let mut k = 0;
    while k < n {
        end_index = end_index + 1;
        if end_index < n {
            if !v::eq(vertices[end_index].position, vertices[end_index - 1].position) {
                // continue
            } else if ptype == PathType::Catmull && end_index > 1 && format_version < FIRST_LAZER_VERSION {
                // continue
            } else if end_index == n - 1 {
                // continue
            } else {
                vertices[end_index - 1].ptype = Some(ptype);
                append_range(&mut out, &vertices, start_index, end_index);
                start_index = end_index + 1;
            }
        }
        k = k + 1;
    }
    if start_index < end_index {
        append_range(&mut out, &vertices, start_index, end_index);
    }
    Ok(out)
}

fn extract_v(a: &[Vec2], lo: usize, hi: usize) -> Vec<Vec2> {
    let mut out: Vec<Vec2> = Vec::new();
    let mut i = lo;
    while i < hi && i < a.len() {
        out.push(a[i]);
        i = i + 1;
    }
    out
}

/// `convertPathString(pointString, offset)`; spec `ConvertHitObjectParser.convertPathString`
pub fn convert_path_string(format_version: i32, point_string: &[u32], offset: Vec2) -> Result<Vec<PathControlPoint>, DecodeError> {
    let parts = split(point_string, 0x7C);
    let mut points: Vec<Vec2> = Vec::new();
    let mut segments: Vec<(PathType, usize)> = Vec::new();
    let mut err: Option<DecodeError> = None;
    let mut i = 0;
    while err.is_none() && i < parts.len() {
        let s = &parts[i];
        match char0(s) {
            Err(e) => err = Some(e),
            Ok(c) => {
                if char_is_letter(c) {
                    match convert_path_type(s) {
                        Err(e) => err = Some(e),
                        Ok(pt) => {
                            segments.push((pt, points.len()));
                            if points.len() == 0 {
                                points.push(v::ZERO);
                            }
                        }
                    }
                } else {
                    match read_point(format_version, s, offset) {
                        Err(e) => err = Some(e),
                        Ok(p) => points.push(p),
                    }
                }
            }
        }
        i = i + 1;
    }
    if let Some(e) = err {
        return Err(e);
    }
    let mut control_points: Vec<PathControlPoint> = Vec::new();
    let mut j = 0;
    while err.is_none() && j < segments.len() {
        let (ptype, start_index) = segments[j];
        let r = if j < segments.len() - 1 {
            let end_index = segments[j + 1].1;
            let end_point = if end_index < points.len() { points[end_index] } else { v::ZERO };
            convert_points(format_version, ptype, &extract_v(&points, start_index, end_index), Some(end_point))
        } else {
            convert_points(format_version, ptype, &extract_v(&points, start_index, points.len()), None)
        };
        match r {
            Err(e) => err = Some(e),
            Ok(cps) => {
                let mut k = 0;
                while k < cps.len() {
                    control_points.push(cps[k]);
                    k = k + 1;
                }
            }
        }
        j = j + 1;
    }
    match err {
        Some(e) => Err(e),
        None => Ok(control_points),
    }
}

/// `LegacyHitObjectType` flags
pub const CIRCLE: i32 = 1;
pub const SLIDER: i32 = 2;
pub const NEW_COMBO: i32 = 4;
pub const SPINNER: i32 = 8;
pub const COMBO_OFFSET: i32 = 112;
pub const HOLD: i32 = 128;

/// The part of `Parse` before the object is created (failures leave the state unchanged).
pub struct PreParse {
    pub pos: Vec2,
    pub start_time: F64,
    pub combo_offset: i32,
    pub combo: bool,
    pub otype: i32,
    pub split: Vec<Str>,
}

/// spec `ConvertHitObjectParser.parse.pre`
pub fn pre_parse(st: &ParserState, text: &[u32]) -> Result<PreParse, DecodeError> {
    let sp = split(text, 0x2C);
    let x = tri!(parse_coord(st.format_version, tri!(at(&sp, 0))));
    let y = tri!(parse_coord(st.format_version, tri!(at(&sp, 1))));
    let start_time = tri!(lift_net(W_STARTTIME, parse_double_default(tri!(at(&sp, 2))))).add(st.offset);
    let type0 = tri!(lift_net(W_TYPE, parse_int_default(tri!(at(&sp, 3)))));
    let combo_offset = (type0 & COMBO_OFFSET) >> 4;
    let type1 = type0 & !COMBO_OFFSET;
    let combo = (type1 & NEW_COMBO) != 0;
    let otype = type1 & !NEW_COMBO;
    let _sound_type = tri!(lift_net(W_SOUNDTYPE, parse_int_default(tri!(at(&sp, 4)))));
    Ok(PreParse { pos: Vec2 { x, y }, start_time, combo_offset, combo, otype, split: sp })
}

fn new_object(start_time: F64, position: Vec2, new_combo: bool, combo_offset: i32, kind: ConvertKind) -> ConvertHitObject {
    ConvertHitObject {
        start_time,
        position,
        new_combo,
        combo_offset,
        kind,
        generate_ticks: true,
        slider_velocity_multiplier: F64::from_bits(0x3FF0_0000_0000_0000),
    }
}

/// spec `parse.finish`
fn finish(st2: ParserState, r: Result<ConvertHitObject, DecodeError>) -> (ParserState, Result<ConvertHitObject, DecodeError>) {
    match r {
        Ok(o) => {
            let mut s = st2;
            s.first_object = false;
            (s, Ok(o))
        }
        Err(e) => (st2, Err(e)),
    }
}

const D0: F64 = F64::from_bits(0);

/// the slider branch of `Parse` (`r` in the spec)
pub fn parse_slider(st: &ParserState, pre: &PreParse, new_combo: bool) -> Result<ConvertHitObject, DecodeError> {
    // straight sequence of helper calls (one per `if` of the spec), see impl/STYLE.md §5
    let sp = &pre.split;
    let repeat_count = tri!(ps_repeat_count(sp));
    let length = tri!(ps_length(sp));
    tri!(ps_check_banks(sp));
    let nodes: usize = (repeat_count as usize) + 2;
    tri!(ps_node_banks(sp, nodes));
    let control_points = tri!(convert_path_string(st.format_version, tri!(at(sp, 5)), pre.pos));
    let path = slider_path::of_control_points(control_points.clone(), length, false);
    // `path.Distance` runs `calculatePath`: an exhausted B-spline subdivision rejects (spec `pathFuelMsg`, D72)
    if path.fuel_out {
        return Err(DecodeError::Msg(M_SLIDER_PATH_FUEL_EXHAUSTED));
    }
    let rc = if almost_equals_f64(slider_path::distance(&path), D0) { 0 } else { repeat_count };
    Ok(new_object(
        pre.start_time,
        pre.pos,
        new_combo,
        if pre.combo { pre.combo_offset } else { 0 },
        ConvertKind::Slider { control_points, expected_distance: length, repeat_count: rc },
    ))
}

/// part of the slider branch of spec `Parse`: `repeatCount` (parse, `> 9000` check, `max 0 (n-1)`)
pub fn ps_repeat_count(sp: &[Str]) -> Result<i32, DecodeError> {
    let repeat_count0 = tri!(lift_net(W_REPEATCOUNT, parse_int_default(tri!(at(sp, 6)))));
    if repeat_count0 > 9000 {
        Err(DecodeError::Msg(M_REPEAT_COUNT_IS_WAY_TOO_HIGH))
    } else {
        let rc1 = repeat_count0.wrapping_sub(1);
        Ok(if rc1 < 0 { 0 } else { rc1 })
    }
}

/// part of the slider branch of spec `Parse`: `length` (the `split.size > 7` branch)
pub fn ps_length(sp: &[Str]) -> Result<Option<F64>, DecodeError> {
    if sp.len() > 7 {
        let lim = F64::from_i64(MAX_COORDINATE_VALUE as i64);
        let l = f64_max(D0, tri!(lift_net(W_LENGTH, parsing_parse_double(&sp[7], lim, false))));
        Ok(if l.eq(D0) { None } else { Some(l) })
    } else {
        Ok(None)
    }
}

/// part of the slider branch of spec `Parse`: the `split.size > 10` sample-bank check
pub fn ps_check_banks(sp: &[Str]) -> Result<(), DecodeError> {
    if sp.len() > 10 {
        read_custom_sample_banks(&sp[10], true)
    } else {
        Ok(())
    }
}

/// part of the slider branch of spec `Parse`: the per-node sample-bank checks (`split.size > 9`)
pub fn ps_node_banks(sp: &[Str], nodes: usize) -> Result<(), DecodeError> {
    if sp.len() > 9 && sp[9].len() > 0 {
        ps_node_banks_loop(&split(&sp[9], 0x7C), nodes)
    } else {
        Ok(())
    }
}

/// the loop of `ps_node_banks` over `nodes` entries of `sets`
pub fn ps_node_banks_loop(sets: &[Str], nodes: usize) -> Result<(), DecodeError> {
    let mut err: Option<DecodeError> = None;
    let mut i = 0;
    while err.is_none() && i < nodes {
        if i < sets.len() {
            match read_custom_sample_banks(&sets[i], false) {
                Ok(_) => {}
                Err(e) => err = Some(e),
            }
        }
        i = i + 1;
    }
    match err {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

/// the hold branch of `Parse` (end time)
pub fn parse_hold_end(pre: &PreParse) -> Result<F64, DecodeError> {
    let sp = &pre.split;
    let mut end_time = f64_max(pre.start_time, tri!(lift_net(W_HOLD_END, parse_double_default(tri!(at(sp, 2))))));
    if sp.len() > 5 && sp[5].len() != 0 {
        let ss = split(&sp[5], 0x3A);
        end_time = f64_max(pre.start_time, tri!(lift_net(W_HOLD_END, parse_double_default(&ss[0]))));
        // ":".intercalate (ss.drop 1)
        let mut rest: Str = Vec::new();
        let mut k = 1;
        while k < ss.len() {
            if k > 1 {
                rest.push(0x3A);
            }
            let mut m = 0;
            while m < ss[k].len() {
                rest.push(ss[k][m]);
                m = m + 1;
            }
            k = k + 1;
        }
        tri!(read_custom_sample_banks(&rest, false));
    }
    Ok(end_time)
}

/// `Parse(text)`; spec `ConvertHitObjectParser.parse`
pub fn parse(st: ParserState, text: &[u32]) -> (ParserState, Result<ConvertHitObject, DecodeError>) {
    let pre = match pre_parse(&st, text) {
        Err(e) => return (st, Err(e)),
        Ok(p) => p,
    };
    let new_combo_of = st.first_object || st.last_object_is_spinner || pre.combo;
    let sp = &pre.split;
    if (pre.otype & CIRCLE) != 0 {
        let obj = new_object(pre.start_time, pre.pos, new_combo_of, if pre.combo { pre.combo_offset } else { 0 }, ConvertKind::Circle);
        let mut st2 = st;
        st2.last_object_is_spinner = false;
        let r = if sp.len() > 5 {
            match read_custom_sample_banks(&sp[5], false) {
                Ok(_) => Ok(obj),
                Err(e) => Err(e),
            }
        } else {
            Ok(obj)
        };
        finish(st2, r)
    } else if (pre.otype & SLIDER) != 0 {
        match parse_slider(&st, &pre, new_combo_of) {
            Ok(o) => {
                let mut st2 = st;
                st2.last_object_is_spinner = false;
                finish(st2, Ok(o))
            }
            Err(e) => (st, Err(e)),
        }
    } else if (pre.otype & SPINNER) != 0 {
        let end_r = if sp.len() > 5 {
            lift_net(W_SPINNER_END, parse_double_default(&sp[5]))
        } else {
            Err(DecodeError::Msg(M_INDEX_OUT_OF_RANGE))
        };
        match end_r {
            Err(e) => (st, Err(e)),
            Ok(end_t) => {
                let duration = f64_max(D0, end_t.add(st.offset).sub(pre.start_time));
                let centre = Vec2 { x: F32::from_bits(0x4380_0000), y: F32::from_bits(0x4340_0000) };
                let obj = new_object(pre.start_time, centre, pre.combo, 0, ConvertKind::Spinner(duration));
                let mut st2 = st;
                st2.last_object_is_spinner = true;
                let r = if sp.len() > 6 {
                    match read_custom_sample_banks(&sp[6], false) {
                        Ok(_) => Ok(obj),
                        Err(e) => Err(e),
                    }
                } else {
                    Ok(obj)
                };
                finish(st2, r)
            }
        }
    } else if (pre.otype & HOLD) != 0 {
        match parse_hold_end(&pre) {
            Err(e) => (st, Err(e)),
            Ok(end_time) => {
                let obj = new_object(pre.start_time, pre.pos, false, 0, ConvertKind::Hold(end_time.add(st.offset).sub(pre.start_time)));
                let mut st2 = st;
                st2.last_object_is_spinner = false;
                finish(st2, Ok(obj))
            }
        }
    } else {
        (st, Err(DecodeError::Msg(M_UNKNOWN_HIT_OBJECT_TYPE)))
    }
}
