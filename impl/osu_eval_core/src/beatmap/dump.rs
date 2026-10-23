//! Port of `OsuModel/Beatmap/Dump.lean`: the canonical text dump (same format as
//! `model/bmtest/Dumper.cs` and the Lean `bmdump`). Test harness only: ordinary Rust (string
//! formatting), excluded from the Charon translation (`impl/charon_check.sh`).
use super::hit_object_parser::DecodeError;
use super::mod_settings::{ModConfig, SettingValue};
use super::objects::*;
use super::playable::{LoadResult, ModState, ObjRef, PlayableBeatmap};
use super::slider_path;
use super::types::PathType;
use super::vector2::Vec2;
use crate::float::{F32, F64};
use crate::net::basic::NetExn;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt::Write;

pub fn d(x: F64) -> String {
    if x.is_nan() { String::from("7ff8000000000000") } else { format!("{:016x}", x.to_bits()) }
}
pub fn f(x: F32) -> String {
    if x.is_nan() { String::from("7fc00000") } else { format!("{:08x}", x.to_bits()) }
}
pub fn vv(p: Vec2) -> String {
    format!("{},{}", f(p.x), f(p.y))
}
pub fn b(x: bool) -> &'static str {
    if x { "1" } else { "0" }
}

pub fn str_of(s: &[u32]) -> String {
    let mut out = String::new();
    for &c in s {
        out.push(char::from_u32(c).unwrap_or('\u{FFFD}'));
    }
    out
}

pub fn net_exn_name(e: NetExn) -> &'static str {
    match e {
        NetExn::Format => "format",
        NetExn::Overflow => "overflow",
        NetExn::Argument => "argument",
        NetExn::ArgumentOutOfRange => "argumentOutOfRange",
        NetExn::Arithmetic => "arithmetic",
    }
}

/// the spec's error message (`liftNet`: `"{what}: {repr e}"`)
pub fn render(e: &DecodeError) -> String {
    match e {
        DecodeError::Msg(m) => String::from(super::errors::text::msg(*m)),
        DecodeError::Net(w, x) => format!("{}: OsuModel.Net.NetExn.{}", super::errors::text::what(*w), net_exn_name(*x)),
    }
}

fn path_type(t: &Option<PathType>) -> String {
    match t {
        None => "none".into(),
        Some(PathType::Catmull) => "catmull".into(),
        Some(PathType::Linear) => "linear".into(),
        Some(PathType::PerfectCurve) => "perfect".into(),
        Some(PathType::BSpline(None)) => "bezier".into(),
        Some(PathType::BSpline(Some(dg))) => format!("bspline{}", dg),
    }
}

fn windows(w: &Option<HitWindows>) -> String {
    match w {
        None => "null".into(),
        Some(HitWindows::Empty) => "empty".into(),
        Some(HitWindows::Osu { great, ok_, meh }) => format!("{},{},{},{}", d(*great), d(*ok_), d(*meh), d(MISS_WINDOW)),
    }
}

fn kind_name(k: &ObjectKind) -> &'static str {
    match k {
        ObjectKind::Circle => "circle",
        ObjectKind::Slider(_) => "slider",
        ObjectKind::Spinner(_) => "spinner",
    }
}

fn nested_name(k: NestedKind) -> &'static str {
    match k {
        NestedKind::Head => "head",
        NestedKind::Tail => "tail",
        NestedKind::Repeat => "repeat",
        NestedKind::Tick => "tick",
        NestedKind::SpinnerTick => "spintick",
        NestedKind::SpinnerBonusTick => "spinbonus",
    }
}

/// spec `Dump.dump`
pub fn dump(pb: &PlayableBeatmap, out: &mut String) {
    let _ = writeln!(out, "version {}", pb.format_version);
    let df = &pb.difficulty;
    let _ = writeln!(
        out,
        "difficulty hp={} cs={} od={} ar={} sm={} tr={}",
        f(df.drain_rate),
        f(df.circle_size),
        f(df.overall_difficulty),
        f(df.approach_rate),
        d(df.slider_multiplier),
        d(df.slider_tick_rate)
    );
    let _ = writeln!(out, "stackleniency {}", f(pb.stack_leniency));
    let _ = writeln!(out, "audioleadin {}", d(pb.audio_lead_in));
    for t in &pb.control_points.timing_points {
        let _ = writeln!(out, "timing {} {} {}", d(t.time), d(t.beat_length), t.time_signature);
    }
    for p in &pb.control_points.difficulty_points {
        let _ = writeln!(out, "diffpoint {} {} {}", d(p.time), d(p.slider_velocity), b(p.generate_ticks));
    }
    for e in &pb.control_points.effect_points {
        let _ = writeln!(out, "effect {} {} {}", d(e.time), b(e.kiai), d(e.scroll_speed));
    }
    for br in &pb.breaks {
        let _ = writeln!(out, "break {} {}", d(br.start_time), d(br.end_time));
    }
    for (i, h) in pb.hit_objects.iter().enumerate() {
        let _ = writeln!(
            out,
            "object {} {} end={} start={} pos={} stack={} scale={} radius={} preempt={} fadein={} stackoffset={} stackedpos={} ci={} ciwo={} icc={} hw={} mjo={} kiai={} nc={} co={} lic={}",
            i,
            kind_name(&h.kind),
            d(end_time(h)),
            d(h.start_time),
            vv(h.position),
            h.stack_height,
            f(h.scale),
            d(radius(h)),
            d(h.time_preempt),
            d(h.time_fade_in),
            vv(stack_offset(h)),
            vv(stacked_position(h)),
            h.combo_index,
            h.combo_index_with_offsets,
            h.index_in_current_combo,
            windows(&h.hit_windows),
            d(maximum_judgement_offset(h)),
            b(h.kiai),
            b(h.new_combo),
            h.combo_offset,
            b(h.last_in_combo)
        );
        match &h.kind {
            ObjectKind::Slider(s) => {
                let exp = match s.path.spec.expected_distance {
                    Some(e) => d(e),
                    None => "null".into(),
                };
                let _ = writeln!(
                    out,
                    "slider repeats={} vel={} tickdist={} tdm={} svm={} genticks={} dist={} cdist={} expected={} duration={} spandur={} endpos={} stackedendpos={} classic={}",
                    s.repeat_count,
                    d(s.velocity),
                    d(s.tick_distance),
                    d(s.tick_distance_multiplier),
                    d(s.slider_velocity_multiplier),
                    b(s.generate_ticks),
                    d(slider_path::distance(&s.path)),
                    d(slider_path::calculated_distance(&s.path)),
                    exp,
                    d(duration(h)),
                    d(span_duration(h)),
                    vv(end_position(h)),
                    vv(stacked_end_position(h)),
                    b(s.classic_slider_behaviour)
                );
                for cp in &s.path.spec.control_points {
                    let _ = writeln!(out, "cp {} {}", vv(cp.position), path_type(&cp.ptype));
                }
                for p in &s.path.calculated_path {
                    let _ = writeln!(out, "pp {}", vv(*p));
                }
                for c in &s.path.cumulative_length {
                    let _ = writeln!(out, "cl {}", d(*c));
                }
            }
            ObjectKind::Spinner(s) => {
                let _ = writeln!(out, "spinner duration={} req={} bonus={}", d(s.duration), s.spins_required, s.maximum_bonus_spins);
            }
            ObjectKind::Circle => {}
        }
        for (j, n) in h.nested.iter().enumerate() {
            let extra = match n.kind {
                NestedKind::Tick => format!(" prog={} span={} spanstart={}", d(n.path_progress), n.span_index, d(n.span_start_time)),
                NestedKind::Repeat => format!(" prog={} rep={}", d(n.path_progress), n.repeat_index),
                NestedKind::Tail => format!(" rep={} classic={} st={}", n.repeat_index, b(n.classic_slider_behaviour), b(n.strict_tracking_tail)),
                NestedKind::SpinnerTick | NestedKind::SpinnerBonusTick => format!(" spindur={}", d(n.spinner_duration)),
                NestedKind::Head => format!(" classic={}", b(n.classic_slider_behaviour)),
            };
            let _ = writeln!(
                out,
                "nested {} {} start={} pos={} stack={} scale={} radius={} preempt={} fadein={} stackoffset={} stackedpos={} ci={} ciwo={} icc={} hw={} mjo={} kiai={}{}",
                j,
                nested_name(n.kind),
                d(n.start_time),
                vv(n.position),
                n.stack_height,
                f(n.scale),
                d(nested_radius(n)),
                d(n.time_preempt),
                d(n.time_fade_in),
                vv(nested_stack_offset(n)),
                vv(nested_stacked_position(n)),
                h.combo_index,
                h.combo_index_with_offsets,
                h.index_in_current_combo,
                windows(&Some(n.hit_windows)),
                d(nested_maximum_judgement_offset(n)),
                b(n.kiai),
                extra
            );
        }
    }
}

fn setting_value(v: &SettingValue) -> String {
    match v {
        SettingValue::Bool(x) => b(*x).into(),
        SettingValue::Int(x) | SettingValue::Enum(x) => format!("{}", x),
        SettingValue::Double(x) => d(*x),
        SettingValue::Float(x) => f(*x),
        SettingValue::OptInt(None) | SettingValue::OptFloat(None) => "null".into(),
        SettingValue::OptInt(Some(x)) => format!("{}", x),
        SettingValue::OptFloat(Some(x)) => f(*x),
    }
}

/// spec `Dump.modLines`
pub fn mod_lines(mods: &[ModConfig], out: &mut String) {
    for (i, m) in mods.iter().enumerate() {
        if !m.known {
            let _ = writeln!(out, "mod {} unknown {}??", i, str_of(&m.acronym));
        } else {
            let _ = write!(out, "mod {} {}", i, str_of(&m.acronym));
            for (k, v) in &m.settings {
                let _ = write!(out, " {}={}", super::names::strings::key_str(*k), setting_value(v));
            }
            out.push('\n');
        }
    }
}

fn obj_ref(pb: &PlayableBeatmap, r: &Option<ObjRef>) -> String {
    match r {
        None => "null".into(),
        Some(r) => {
            if r.epoch != pb.epoch {
                "gone".into()
            } else {
                match r.nested {
                    None => format!("{}", r.index),
                    Some(j) => format!("{}.{}", r.index, j),
                }
            }
        }
    }
}

/// spec `Dump.modStateLines`
pub fn mod_state_lines(pb: &PlayableBeatmap, nmods: usize, out: &mut String) {
    for i in 0..nmods {
        for (k, st) in &pb.mod_states {
            if *k != i {
                continue;
            }
            match st {
                ModState::FirstObject(r) => {
                    let _ = writeln!(out, "modstate {} firstobject {}", i, obj_ref(pb, r));
                }
                ModState::TimeRamp(bt, ft) => {
                    let _ = writeln!(out, "modstate {} timeramp {} {}", i, d(*bt), d(*ft));
                }
                ModState::PrecedingEndTimes(es) => {
                    for (r, t) in es {
                        let _ = writeln!(out, "modstate {} preceding {} {}", i, obj_ref(pb, &Some(*r)), d(*t));
                    }
                }
            }
        }
    }
}

/// spec `Dump.dumpLoad`
pub fn dump_load(r: &LoadResult, mods: &[ModConfig]) -> String {
    let mut out = String::new();
    match r {
        LoadResult::DecodeError(e) => {
            let _ = writeln!(out, "error decode {}", render(e));
        }
        LoadResult::OtherRuleset(id) => {
            let _ = writeln!(out, "mode {}", id);
        }
        LoadResult::PlayableError(e) => {
            out.push_str("mode 0\n");
            let _ = writeln!(out, "error playable {}", render(e));
        }
        LoadResult::Ok(pb) => {
            out.push_str("mode 0\n");
            mod_lines(mods, &mut out);
            dump(pb, &mut out);
            mod_state_lines(pb, mods.len(), &mut out);
        }
    }
    out
}

#[allow(dead_code)]
fn _unused(_: Vec<u8>) {}
