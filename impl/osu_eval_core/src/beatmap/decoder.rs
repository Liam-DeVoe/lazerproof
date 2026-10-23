//! Port of `OsuModel/Beatmap/Decoder.lean` (`LegacyBeatmapDecoder`, `LegacyDecoder`, `Decoder`).
use super::control_points::{
    add_difficulty, add_effect, add_timing, clamp_beat_length, clamp_scroll_speed, clamp_sv, cpi_empty, difficulty_point_at,
    ControlPointInfo, DifficultyPoint, EffectPoint, TimingPoint,
};
use super::dotnet::{
    compare_f64, enum_try_parse, insert_at, is_null_or_white_space, split, split_key_val, stable_sort_by, starts_with,
    ends_with, str_eq, sub_str, trim, trim_end, trim_start, SortKey, Str,
};
use super::errors::*;
use super::hit_object_parser::{char0, lift_net, parse as parse_hit_object, at, DecodeError, ParserState};
use super::names::{T_EVENT_TYPE, T_SECTION};
use super::text::{read_lines, stream_reader_decode};
use super::types::{BreakPeriod, ConvertHitObject, ConvertKind, DecodedBeatmap, Difficulty, DIFFICULTY_DEFAULT};
use crate::float::{F32, F64};
use crate::net::max as f64_max;
use crate::net::parse::{parse_double_default, parse_float_default, parse_int_default, parsing_parse_double, MAX_PARSE_VALUE};
use alloc::vec::Vec;


/// `EARLY_VERSION_TIMING_OFFSET`
pub const EARLY_VERSION_TIMING_OFFSET: i32 = 24;
/// `LegacyDecoder.LATEST_VERSION`
pub const LATEST_VERSION: i32 = 14;
/// `MAX_MANIA_KEY_COUNT`
pub const MAX_MANIA_KEY_COUNT: F32 = F32::from_bits(0x4190_0000);

/// `pendingControlPoints`, split by type, list order kept; spec `Pending`
#[derive(Clone)]
pub struct Pending {
    pub timing: Vec<TimingPoint>,
    pub difficulty: Vec<DifficultyPoint>,
    pub effect: Vec<EffectPoint>,
    pub time: F64,
}

/// Decoder state; spec `DecoderState`
#[derive(Clone)]
pub struct DecoderState {
    pub format_version: i32,
    pub offset: i32,
    pub sect: i32,
    pub ruleset_id: i32,
    pub stack_leniency: F32,
    pub audio_lead_in: F64,
    pub difficulty: Difficulty,
    pub has_approach_rate: bool,
    pub cpi: ControlPointInfo,
    pub pending: Pending,
    pub breaks: Vec<BreakPeriod>,
    pub parser: ParserState,
    pub hit_objects: Vec<ConvertHitObject>,
}

/// `getOffsetTime`; spec `LegacyBeatmapDecoder.offsetTime`
pub fn offset_time(s: &DecoderState, t: F64) -> F64 {
    t.add(F64::from_i64(s.offset as i64))
}

/// `flushPendingPoints()` (last pending point of each type wins); spec `flushPendingPoints`
pub fn flush_pending_points(s: &mut DecoderState) {
    let t = s.pending.time;
    let nt = s.pending.timing.len();
    if nt > 0 {
        let mut p = s.pending.timing[nt - 1];
        p.time = t;
        add_timing(&mut s.cpi, p);
    }
    let nd = s.pending.difficulty.len();
    if nd > 0 {
        let mut p = s.pending.difficulty[nd - 1];
        p.time = t;
        add_difficulty(&mut s.cpi, p);
    }
    let ne = s.pending.effect.len();
    if ne > 0 {
        let mut p = s.pending.effect[ne - 1];
        p.time = t;
        add_effect(&mut s.cpi, p);
    }
    s.pending.timing = Vec::new();
    s.pending.difficulty = Vec::new();
    s.pending.effect = Vec::new();
}

/// `addControlPoint` for one line's points; spec `addLinePoints`
pub fn add_line_points(s: &mut DecoderState, time: F64, timing: Option<TimingPoint>, diff: DifficultyPoint, eff: EffectPoint, timing_change: bool) {
    if !time.eq(s.pending.time) {
        flush_pending_points(s);
    }
    match timing {
        Some(tp) => insert_at(&mut s.pending.timing, 0, tp),
        None => {}
    }
    if timing_change {
        insert_at(&mut s.pending.difficulty, 0, diff);
        insert_at(&mut s.pending.effect, 0, eff);
    } else {
        s.pending.difficulty.push(diff);
        s.pending.effect.push(eff);
    }
    s.pending.time = time;
}

/// `handleGeneral(line)`; spec `handleGeneral`
pub fn handle_general(s: &mut DecoderState, line: &[u32]) -> Result<(), DecodeError> {
    let (key, value) = split_key_val(line, 0x3A);
    if str_eq(&key, b"AudioLeadIn") {
        let v = tri!(lift_net(W_AUDIOLEADIN, parse_int_default(&value)));
        s.audio_lead_in = F64::from_i64(v as i64);
    } else if str_eq(&key, b"StackLeniency") {
        s.stack_leniency = tri!(lift_net(W_STACKLENIENCY, parse_float_default(&value)));
    } else if str_eq(&key, b"Mode") {
        let id = tri!(lift_net(W_MODE, parse_int_default(&value)));
        if 0 <= id && id <= 3 {
            s.ruleset_id = id;
        } else {
            return Err(DecodeError::Msg(M_RULESET_IS_NOT_AVAILABLE_LOCALLY));
        }
    }
    Ok(())
}

/// `handleDifficulty(line)`; spec `handleDifficulty`
pub fn handle_difficulty(s: &mut DecoderState, line: &[u32]) -> Result<(), DecodeError> {
    let (key, value) = split_key_val(line, 0x3A);
    if str_eq(&key, b"HPDrainRate") {
        s.difficulty.drain_rate = tri!(lift_net(W_HPDRAINRATE, parse_float_default(&value)));
    } else if str_eq(&key, b"CircleSize") {
        s.difficulty.circle_size = tri!(lift_net(W_CIRCLESIZE, parse_float_default(&value)));
    } else if str_eq(&key, b"OverallDifficulty") {
        let od = tri!(lift_net(W_OVERALLDIFFICULTY, parse_float_default(&value)));
        s.difficulty.overall_difficulty = od;
        if !s.has_approach_rate {
            s.difficulty.approach_rate = od;
        }
    } else if str_eq(&key, b"ApproachRate") {
        let ar = tri!(lift_net(W_APPROACHRATE, parse_float_default(&value)));
        s.difficulty.approach_rate = ar;
        s.has_approach_rate = true;
    } else if str_eq(&key, b"SliderMultiplier") {
        s.difficulty.slider_multiplier = tri!(lift_net(W_SLIDERMULTIPLIER, parse_double_default(&value)));
    } else if str_eq(&key, b"SliderTickRate") {
        s.difficulty.slider_tick_rate = tri!(lift_net(W_SLIDERTICKRATE, parse_double_default(&value)));
    }
    Ok(())
}

fn break_lt(x: BreakPeriod, y: BreakPeriod) -> bool {
    compare_f64(x.start_time, y.start_time) < 0
        || (compare_f64(x.start_time, y.start_time) == 0 && compare_f64(x.end_time, y.end_time) < 0)
}

/// Insert into the `SortedList<BreakPeriod>`; spec `insertBreak`
pub fn insert_break(bs: &mut Vec<BreakPeriod>, b: BreakPeriod) {
    let mut i = 0;
    let mut found = false;
    while !found && i < bs.len() {
        if break_lt(b, bs[i]) {
            found = true;
        } else {
            i = i + 1;
        }
    }
    insert_at(bs, i, b);
}

/// `handleEvent(line)` (only breaks matter); spec `handleEvent`
pub fn handle_event(s: &mut DecoderState, line: &[u32]) -> Result<(), DecodeError> {
    let sp = split(line, 0x2C);
    match enum_try_parse(T_EVENT_TYPE, &sp[0]) {
        Some(2) => {
            let start = offset_time(s, tri!(lift_net(W_BREAK_START, parse_double_default(tri!(at(&sp, 1))))));
            let end_t = f64_max(start, offset_time(s, tri!(lift_net(W_BREAK_END, parse_double_default(tri!(at(&sp, 2)))))));
            insert_break(&mut s.breaks, BreakPeriod { start_time: start, end_time: end_t });
            Ok(())
        }
        _ => Ok(()),
    }
}

const D0: F64 = F64::from_bits(0);
const D1: F64 = F64::from_bits(0x3FF0_0000_0000_0000);
const D100: F64 = F64::from_bits(0x4059_0000_0000_0000);

/// `handleTimingPoint(line)`; spec `handleTimingPoint`
pub fn handle_timing_point(s: &mut DecoderState, line: &[u32]) -> Result<(), DecodeError> {
    // Written as a straight sequence of helper calls (each `if` of the spec is one helper) so that
    // Charon/Aeneas do not duplicate the continuation into every branch (impl/STYLE.md §5).
    let sp = split(line, 0x2C);
    let time = offset_time(s, tri!(lift_net(W_TIME, parse_double_default(&trim(tri!(at(&sp, 0)))))));
    let beat_length = tri!(lift_net(W_BEATLENGTH, parsing_parse_double(&trim(tri!(at(&sp, 1))), MAX_PARSE_VALUE, true)));
    let speed_multiplier = tp_speed_multiplier(beat_length);
    let time_signature = tri!(tp_time_signature(&sp));
    tri!(tp_check_int(&sp, 3, W_SAMPLESET));
    tri!(tp_check_int(&sp, 4, W_CUSTOMSAMPLEBANK));
    tri!(tp_check_int(&sp, 5, W_SAMPLEVOLUME));
    let timing_change = tri!(tp_timing_change(&sp));
    let kiai = tri!(tp_kiai(&sp));
    let timing = tri!(tp_timing(time, beat_length, time_signature, timing_change));
    let diff = DifficultyPoint { time, slider_velocity: clamp_sv(speed_multiplier), generate_ticks: !beat_length.is_nan() };
    let eff = EffectPoint { time, kiai, scroll_speed: tp_scroll_speed(s.ruleset_id, speed_multiplier) };
    add_line_points(s, time, timing, diff, eff, timing_change);
    Ok(())
}

/// part of spec `handleTimingPoint`: `speedMultiplier`
pub fn tp_speed_multiplier(beat_length: F64) -> F64 {
    if beat_length.lt(D0) { D100.div(beat_length.neg()) } else { D1 }
}

/// part of spec `handleTimingPoint`: `timeSignature` (the `split.size ≥ 3` branch)
pub fn tp_time_signature(sp: &[Str]) -> Result<i32, DecodeError> {
    if sp.len() >= 3 {
        let c = tri!(char0(&sp[2]));
        if c != 0x30 {
            let n = tri!(lift_net(W_TIMESIGNATURE, parse_int_default(&sp[2])));
            if n <= 0 {
                Err(DecodeError::Msg(M_TIMESIGNATURE_NUMERATOR_MUST_BE_POSITIVE))
            } else {
                Ok(n)
            }
        } else {
            Ok(4)
        }
    } else {
        Ok(4)
    }
}

/// part of spec `handleTimingPoint`: `if split.size ≥ k+1 then let _ ← liftNet what (parseInt split[k]!)`
pub fn tp_check_int(sp: &[Str], k: usize, what: u32) -> Result<(), DecodeError> {
    if sp.len() > k {
        match lift_net(what, parse_int_default(&sp[k])) {
            Ok(_) => Ok(()),
            Err(e) => Err(e),
        }
    } else {
        Ok(())
    }
}

/// part of spec `handleTimingPoint`: `timingChange` (the `split.size ≥ 7` branch)
pub fn tp_timing_change(sp: &[Str]) -> Result<bool, DecodeError> {
    if sp.len() >= 7 {
        let c = tri!(char0(&sp[6]));
        Ok(c == 0x31)
    } else {
        Ok(true)
    }
}

/// part of spec `handleTimingPoint`: `kiai` (the `split.size ≥ 8` branch)
pub fn tp_kiai(sp: &[Str]) -> Result<bool, DecodeError> {
    if sp.len() >= 8 {
        let flags = tri!(lift_net(W_EFFECTFLAGS, parse_int_default(&sp[7])));
        Ok((flags & 1) != 0)
    } else {
        Ok(false)
    }
}

/// part of spec `handleTimingPoint`: `timing` (the `if timingChange` branch)
pub fn tp_timing(time: F64, beat_length: F64, time_signature: i32, timing_change: bool) -> Result<Option<TimingPoint>, DecodeError> {
    if timing_change {
        if beat_length.is_nan() {
            Err(DecodeError::Msg(M_BEAT_LENGTH_CANNOT_BE_NAN_IN_A_TIMING_CO))
        } else {
            Ok(Some(TimingPoint { time, beat_length: clamp_beat_length(beat_length), time_signature }))
        }
    } else {
        Ok(None)
    }
}

/// part of spec `handleTimingPoint`: the effect point's `scrollSpeed`
pub fn tp_scroll_speed(ruleset_id: i32, speed_multiplier: F64) -> F64 {
    if ruleset_id == 1 || ruleset_id == 3 { clamp_scroll_speed(speed_multiplier) } else { D1 }
}

/// `handleHitObject(line)` (parser state advances even on failure); spec `handleHitObject`
pub fn handle_hit_object(s: &mut DecoderState, line: &[u32]) {
    let (p, r) = parse_hit_object(s.parser, line);
    s.parser = p;
    match r {
        Ok(o) => s.hit_objects.push(o),
        Err(_) => {}
    }
}

/// `ParseLine` dispatch + `catch` (a failing line leaves the state unchanged); spec `parseLine`
pub fn parse_line(s: &mut DecoderState, line: &[u32]) {
    if s.sect == 7 {
        handle_hit_object(s, line);
    } else if s.sect == 0 || s.sect == 3 || s.sect == 4 || s.sect == 5 {
        // handlers mutate only after all their parses succeeded, except `handleTimingPoint`'s
        // final `add_line_points`, which cannot fail: the state is unchanged on `Err`.
        let r = if s.sect == 0 {
            handle_general(s, line)
        } else if s.sect == 3 {
            handle_difficulty(s, line)
        } else if s.sect == 4 {
            handle_event(s, line)
        } else {
            handle_timing_point(s, line)
        };
        match r {
            Ok(_) => {}
            Err(_) => {}
        }
    }
}

/// `ShouldSkipLine(line)`; spec `shouldSkipLine`
pub fn should_skip_line(line: &[u32]) -> bool {
    is_null_or_white_space(line) || starts_with(&trim_start(line), b"//")
}

/// `StripComments(line)` (cut at the first `//` if its index is > 0); spec `stripComments`
pub fn strip_comments(line: &[u32]) -> Str {
    let mut i = 0;
    let mut found = false;
    while !found && i + 1 < line.len() {
        if line[i] == 0x2F && line[i + 1] == 0x2F {
            found = true;
        } else {
            i = i + 1;
        }
    }
    if found && i > 0 { sub_str(line, 0, i) } else { sub_str(line, 0, line.len()) }
}

/// The line loop of `LegacyDecoder.ParseStreamInto`; spec `parseLines`
pub fn parse_lines(s: &mut DecoderState, lines: &[Str]) {
    let mut k = 0;
    while k < lines.len() {
        let line0 = &lines[k];
        if !should_skip_line(line0) {
            let line1 = if s.sect != 2 { strip_comments(line0) } else { sub_str(line0, 0, line0.len()) };
            let line = trim_end(&line1);
            if starts_with(&line, b"[") && ends_with(&line, b"]") {
                let inner = if line.len() >= 2 { sub_str(&line, 1, line.len() - 1) } else { Vec::new() };
                s.sect = match enum_try_parse(T_SECTION, &inner) {
                    Some(x) => x,
                    None => 0,
                };
            } else {
                parse_line(s, &line);
            }
        }
        k = k + 1;
    }
}

fn clamp32(v: F32, lo: F32, hi: F32) -> F32 {
    if v.lt(lo) { lo } else if hi.lt(v) { hi } else { v }
}
fn clamp64(v: F64, lo: F64, hi: F64) -> F64 {
    if v.lt(lo) { lo } else if hi.lt(v) { hi } else { v }
}

/// `applyDifficultyRestrictions`; spec `applyDifficultyRestrictions`
pub fn apply_difficulty_restrictions(d: Difficulty, ruleset_id: i32) -> Difficulty {
    let f0 = F32::from_bits(0);
    let f1 = F32::from_bits(0x3F80_0000);
    let f10 = F32::from_bits(0x4120_0000);
    Difficulty {
        drain_rate: clamp32(d.drain_rate, f0, f10),
        circle_size: if ruleset_id != 3 { clamp32(d.circle_size, f0, f10) } else { clamp32(d.circle_size, f1, MAX_MANIA_KEY_COUNT) },
        overall_difficulty: clamp32(d.overall_difficulty, f0, f10),
        approach_rate: clamp32(d.approach_rate, f0, f10),
        slider_multiplier: clamp64(d.slider_multiplier, F64::from_bits(0x3FD9_9999_9999_999A), F64::from_bits(0x400C_CCCC_CCCC_CCCD)),
        slider_tick_rate: clamp64(d.slider_tick_rate, F64::from_bits(0x3FE0_0000_0000_0000), F64::from_bits(0x4020_0000_0000_0000)),
    }
}

/// `postProcessBreaks` (new combo after each break); spec `postProcessBreaks`
pub fn post_process_breaks(breaks: &[BreakPeriod], hos: &mut Vec<ConvertHitObject>) {
    let mut current_break = 0;
    let mut i = 0;
    while i < hos.len() {
        let mut force = false;
        let mut k = 0;
        while k < breaks.len() {
            if current_break < breaks.len() && breaks[current_break].end_time.lt(hos[i].start_time) {
                force = true;
                current_break = current_break + 1;
            }
            k = k + 1;
        }
        hos[i].new_combo = hos[i].new_combo || force;
        i = i + 1;
    }
}

/// decoder `applyDefaults(hitObject)` for sliders; spec `applyDecodeDefaults`
pub fn apply_decode_defaults(cpi: &ControlPointInfo, h: &mut ConvertHitObject) {
    match h.kind {
        ConvertKind::Slider { .. } => {
            let dp = difficulty_point_at(cpi, h.start_time);
            h.generate_ticks = dp.generate_ticks;
            h.slider_velocity_multiplier = dp.slider_velocity;
        }
        _ => {}
    }
}

impl SortKey for ConvertHitObject {
    fn sort_key(&self) -> F64 {
        self.start_time
    }
}

/// `LegacyBeatmapDecoder.ParseStreamInto` for a decoder of the given version; spec `parseStreamInto`
pub fn parse_stream_into(format_version: i32, lines: &[Str]) -> DecodedBeatmap {
    let offset: i32 = if format_version < 5 { EARLY_VERSION_TIMING_OFFSET } else { 0 };
    let mut s = DecoderState {
        format_version,
        offset,
        sect: 0,
        ruleset_id: 0,
        stack_leniency: F32::from_bits(0x3F33_3333),
        audio_lead_in: D0,
        difficulty: DIFFICULTY_DEFAULT,
        has_approach_rate: false,
        cpi: cpi_empty(),
        pending: Pending { timing: Vec::new(), difficulty: Vec::new(), effect: Vec::new(), time: D0 },
        breaks: Vec::new(),
        parser: ParserState { offset: F64::from_i64(offset as i64), format_version, first_object: true, last_object_is_spinner: false },
        hit_objects: Vec::new(),
    };
    parse_lines(&mut s, lines);
    let difficulty = apply_difficulty_restrictions(s.difficulty, s.ruleset_id);
    flush_pending_points(&mut s);
    let mut hos = s.hit_objects.clone();
    stable_sort_by(&mut hos);
    post_process_breaks(&s.breaks, &mut hos);
    let mut i = 0;
    while i < hos.len() {
        apply_decode_defaults(&s.cpi, &mut hos[i]);
        i = i + 1;
    }
    DecodedBeatmap {
        format_version,
        ruleset_id: s.ruleset_id,
        difficulty,
        stack_leniency: s.stack_leniency,
        audio_lead_in: s.audio_lead_in,
        control_points: s.cpi,
        breaks: s.breaks,
        hit_objects: hos,
    }
}

/// `Decoder.GetDecoder<Beatmap>(stream)` + `Decode(stream)`; spec `LegacyBeatmapDecoder.decode`
pub fn decode(bytes: &[u8]) -> Result<DecodedBeatmap, DecodeError> {
    let chars = match stream_reader_decode(bytes) {
        Some(c) => c,
        None => return Err(DecodeError::Msg(M_UNSUPPORTED_TEXT_ENCODING_UTF_32_UNPAIRE)),
    };
    let lines = read_lines(&chars);
    let mut k = 0;
    let mut found = false;
    while !found && k < lines.len() {
        if trim(&lines[k]).len() != 0 {
            found = true;
        } else {
            k = k + 1;
        }
    }
    if k >= lines.len() {
        return Err(DecodeError::Msg(M_UNKNOWN_FILE_FORMAT_NO_CONTENT));
    }
    let first = trim(&lines[k]);
    let rest = &lines[k..];
    if starts_with(&first, b"osu file format v") {
        let parts = split(&first, 0x76);
        let last_part = &parts[parts.len() - 1];
        let version = tri!(lift_net(W_FORMAT_VERSION, parse_int_default(last_part)));
        Ok(parse_stream_into(version, rest))
    } else if starts_with(&first, b"{") {
        Err(DecodeError::Msg(M_JSON_BEATMAP_JSONBEATMAPDECODER_NOT_MODE))
    } else {
        Ok(parse_stream_into(LATEST_VERSION, rest))
    }
}
