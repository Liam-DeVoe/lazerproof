//! osu_eval: the Rust end-to-end evaluator (`osu_eval_core::eval::evaluate`), with the CLI and the
//! byte-identical JSON output of the Lean `evaltest` (`model/EvalTest/Main.lean`):
//! ```text
//! osu_eval BEATMAP.osu REPLAY.osr [--schedule catchup|perframe|dense1ms|explicit:FILE] [--mods JSON]
//!          [--replace-mods] [--no-classic] [--no-judgements] [--steps] [--timing] [--dump-playable PATH]
//! ```
//! Additionally `--batch LIST` runs many jobs in one process (one job per line:
//! `BEATMAP OSR OUT [MODS-JSON]`; the flags of the command line apply to every job; each job's stdout
//! is written to OUT) for throughput measurements. `--sim-playable` (a localisation-only option of
//! the spec) is not supported. This file is a test/CLI shell (not translated).
use osu_eval_core::beatmap::dump::render as render_decode_error;
use osu_eval_core::beatmap::mod_settings::{ModConfig, SettingValue};
use osu_eval_core::beatmap::names::strings::key_str;
use osu_eval_core::eval::adapter::text::type_name;
use osu_eval_core::eval::env::default_env;
use osu_eval_core::eval::mods_json::{parse_mods, text::mods_json_err};
use osu_eval_core::eval::osr::text::osr_err;
use osu_eval_core::eval::text::stage as stage_text;
use osu_eval_core::eval::{evaluate, playable_for, EvalResult, Options, Reason, Rejection, Schedule, ScheduleErr, SemResult};
use osu_eval_core::float::{F32, F64};
use osu_eval_core::net::basic::NetExn;
use osu_eval_core::net::parse::double_parse;
use osu_eval_core::sim::basic::{hr_index, HitResult};
use osu_eval_core::sim::err::{Internal, SimErr};
use osu_eval_core::sim::playable::{HObj, Kind, Playable, TopObj};
use osu_eval_core::sim::schedule::ScheduleKind;
use osu_eval_core::sim::scoring::Rank;
use std::fmt::Write as _;
use std::io::Write as _;

// ---------------------------------------------------------------------------------------------
// Lean-compatible rendering
// ---------------------------------------------------------------------------------------------

/// `Lean.Json.compress (Lean.Json.str s)` (`Lean.Json.escape`: `"`, `\`, `\n`, `\r` escaped,
/// other characters below 0x20 as `\u00xx` with lowercase hex)
fn jstr(s: &str) -> String {
    let mut o = String::with_capacity(s.len() + 2);
    o.push('"');
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            '\r' => o.push_str("\\r"),
            c if (c as u32) < 0x20 => {
                let _ = write!(o, "\\u{:04x}", c as u32);
            }
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

fn str_of(s: &[u32]) -> String {
    s.iter().map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}')).collect()
}

/// `F64.hex` (`Float.toBits` canonicalises NaN in the Lean runtime)
fn hex64(x: F64) -> String {
    let b = x.to_bits();
    let b = if f64::from_bits(b).is_nan() { 0x7ff8000000000000 } else { b };
    format!("0x{:016x}", b)
}
fn hex32(x: F32) -> String {
    let b = x.to_bits();
    let b = if f32::from_bits(b).is_nan() { 0x7fc00000 } else { b };
    format!("0x{:08x}", b)
}
/// `hexD`
fn hex_d(x: F64) -> String {
    format!("\"{}\"", hex64(x))
}

const RESULTS: [(&str, HitResult); 18] = [
    ("None", HitResult::None),
    ("Miss", HitResult::Miss),
    ("Meh", HitResult::Meh),
    ("Ok", HitResult::Ok_),
    ("Good", HitResult::Good),
    ("Great", HitResult::Great),
    ("Perfect", HitResult::Perfect),
    ("SmallTickMiss", HitResult::SmallTickMiss),
    ("SmallTickHit", HitResult::SmallTickHit),
    ("LargeTickMiss", HitResult::LargeTickMiss),
    ("LargeTickHit", HitResult::LargeTickHit),
    ("SmallBonus", HitResult::SmallBonus),
    ("LargeBonus", HitResult::LargeBonus),
    ("IgnoreMiss", HitResult::IgnoreMiss),
    ("IgnoreHit", HitResult::IgnoreHit),
    ("ComboBreak", HitResult::ComboBreak),
    ("SliderTailHit", HitResult::SliderTailHit),
    ("LegacyComboIncrease", HitResult::LegacyComboIncrease),
];

/// `HitResult.name`
fn result_name(r: HitResult) -> &'static str {
    RESULTS[hr_index(r)].0
}

/// `Kind.typeName`
fn kind_type_name(k: Kind) -> &'static str {
    match k {
        Kind::Circle => "HitCircle",
        Kind::Slider => "Slider",
        Kind::Spinner => "Spinner",
        Kind::Head => "SliderHeadCircle",
        Kind::Tick => "SliderTick",
        Kind::Repeat => "SliderRepeat",
        Kind::Tail => "SliderTailCircle",
        Kind::SpinnerTick => "SpinnerTick",
        Kind::SpinnerBonusTick => "SpinnerBonusTick",
    }
}

/// `Rank.name`
fn rank_name(r: Rank) -> &'static str {
    match r {
        Rank::D => "D",
        Rank::C => "C",
        Rank::B => "B",
        Rank::A => "A",
        Rank::S => "S",
        Rank::SH => "SH",
        Rank::X => "X",
        Rank::XH => "XH",
        Rank::F => "F",
    }
}

/// `repr` of a `NetExn`
fn netexn_repr(e: NetExn) -> &'static str {
    match e {
        NetExn::Format => "OsuModel.Net.NetExn.format",
        NetExn::Overflow => "OsuModel.Net.NetExn.overflow",
        NetExn::Argument => "OsuModel.Net.NetExn.argument",
        NetExn::ArgumentOutOfRange => "OsuModel.Net.NetExn.argumentOutOfRange",
        NetExn::Arithmetic => "OsuModel.Net.NetExn.arithmetic",
    }
}

/// Lean `toString` of a `Float` (`%f`; `NaN`, `inf`, `-inf`)
fn lean_float_str(x: F64) -> String {
    let v = f64::from_bits(x.to_bits());
    if v.is_nan() {
        "NaN".to_string()
    } else if v.is_infinite() {
        if v > 0.0 { "inf".to_string() } else { "-inf".to_string() }
    } else {
        format!("{:.6}", v)
    }
}

/// `repr` of a `Kind`
fn kind_repr(k: Kind) -> &'static str {
    match k {
        Kind::Circle => "OsuModel.Sim.Kind.circle",
        Kind::Slider => "OsuModel.Sim.Kind.slider",
        Kind::Spinner => "OsuModel.Sim.Kind.spinner",
        Kind::Head => "OsuModel.Sim.Kind.head",
        Kind::Tick => "OsuModel.Sim.Kind.tick",
        Kind::Repeat => "OsuModel.Sim.Kind.repeat",
        Kind::Tail => "OsuModel.Sim.Kind.tail",
        Kind::SpinnerTick => "OsuModel.Sim.Kind.spinnerTick",
        Kind::SpinnerBonusTick => "OsuModel.Sim.Kind.spinnerBonusTick",
    }
}

/// The Sim's rejection message (Lean `e0e8215`+, as `simtest_rs`).
fn sim_err_message(e: &SimErr) -> String {
    match *e {
        SimErr::Net(x) => format!("lazer would throw: {}", netexn_repr(x)),
        SimErr::ClampFrames(x, idx) => {
            format!("lazer would throw: Math.Clamp {} (frame times out of order at {})", netexn_repr(x), idx)
        }
        SimErr::ClampDrain(x) => format!("lazer would throw: Math.Clamp {} (drain bounds)", netexn_repr(x)),
        SimErr::SignDrain(x) => format!("lazer would throw: Math.Sign {} (ComputeDrainRate)", netexn_repr(x)),
        SimErr::SignSpin(x) => format!("lazer would throw: Math.Sign {} (SpinnerSpinHistory)", netexn_repr(x)),
        SimErr::EmptyPath => "lazer would throw: Path.Vertices[0] on an empty slider path (SnakingSliderBody.cs:119)".to_string(),
        SimErr::CumLen(k) => format!("lazer would throw: cumulativeLength[{}] out of range", k),
        SimErr::PeriodInvalid => "InputBlockingMod: invalid period (start >= end), lazer throws".to_string(),
        SimErr::PeriodNoFollowing => "InputBlockingMod: break without a following object, lazer throws".to_string(),
        SimErr::SliderWithout(start, k) => {
            format!("malformed playable: slider at {} without a {}", lean_float_str(start), kind_repr(k))
        }
        SimErr::NoSliderData => "malformed: slider without slider data".to_string(),
        SimErr::DenseFuel => "schedule: dense reference list exceeds 1e8 entries".to_string(),
        SimErr::StepFuel => "schedule: step fuel exhausted".to_string(),
        SimErr::AutogenFuel(w) => format!(
            "autogen: fuel exhausted in {}",
            match w {
                0 => "time < h.start",
                1 => "nextFrame < endT",
                _ => "j < sd.duration",
            }
        ),
        SimErr::Internal(i) => match i {
            Internal::ReportDeltaFuel => "internal: ReportDelta fuel exhausted".to_string(),
            Internal::BonusFuel => "internal: updateBonusScore fuel exhausted".to_string(),
            Internal::DrainFuel => "internal: ComputeDrainRate fuel exhausted".to_string(),
            Internal::LegacyDrainFuel => "internal: legacy ComputeDrainRate fuel exhausted".to_string(),
            Internal::HandleHitDepth => "internal: HandleHit recursion deeper than the object count".to_string(),
            Internal::DeadNotAlive(i) => format!("internal: dead object {} not in the alive dictionary", i),
            Internal::MissingSliderData => "internal: missing slider data".to_string(),
        },
    }
}

/// `Rejection.reason` text (spec: the `String` of the lifted error / the literal message)
fn reason_text(r: &Reason) -> String {
    match r {
        Reason::Decode(e) => render_decode_error(e),
        Reason::OtherRuleset(id) => format!("beatmap ruleset {}: conversion of non-osu! beatmaps is not modelled", id),
        Reason::Osr(e) => osr_err(*e),
        Reason::UnknownMod(a) => format!("unknown mod acronym: {}", str_of(a)),
        Reason::Autoplay => "autoplay-type mods are not supported (they replace the replay)".to_string(),
        Reason::Unseeded(a) => format!("{} without a seed is not reproducible (lazer uses RNG.Next(); ISSUES G5)", str_of(a)),
        Reason::Frames(x) => netexn_repr(*x).to_string(),
        Reason::Sim(e) => sim_err_message(e),
        Reason::Schedule(e) => match e {
            ScheduleErr::Empty => "explicit schedule is empty",
            ScheduleErr::NonFinite => "explicit schedule: a reference time is not finite",
            ScheduleErr::Decreasing => "explicit schedule must be non-decreasing",
            ScheduleErr::FrameIndex => "schedule: a step's replay frame index passes the last frame (an FSC time of +inf)",
        }
        .to_string(),
    }
}

/// `settingJson`
fn setting_json(v: &SettingValue) -> String {
    match v {
        SettingValue::Bool(b) => b.to_string(),
        SettingValue::Int(x) => x.to_string(),
        SettingValue::Enum(x) => x.to_string(),
        SettingValue::Double(x) => hex_d(*x),
        SettingValue::Float(x) => jstr(&hex32(*x)),
        SettingValue::OptInt(None) => "null".to_string(),
        SettingValue::OptFloat(None) => "null".to_string(),
        SettingValue::OptInt(Some(x)) => x.to_string(),
        SettingValue::OptFloat(Some(x)) => jstr(&hex32(*x)),
    }
}

/// `modsJson`
fn mods_json(ms: &[ModConfig]) -> String {
    let parts: Vec<String> = ms
        .iter()
        .map(|m| {
            let settings: Vec<String> = m.settings.iter().map(|(k, v)| format!("{}:{}", jstr(key_str(*k)), setting_json(v))).collect();
            format!(
                "{{\"acronym\":{}{},\"settings\":{{{}}}}}",
                jstr(&str_of(&m.acronym)),
                if m.known { "" } else { ",\"unknown\":true" },
                settings.join(",")
            )
        })
        .collect();
    format!("[{}]", parts.join(","))
}

/// `acrJson`
fn acr_json(ms: &[ModConfig]) -> String {
    let parts: Vec<String> = ms.iter().map(|m| jstr(&str_of(&m.acronym))).collect();
    format!("[{}]", parts.join(","))
}

/// `statsJson`
fn stats_json(a: &[u64; 18]) -> String {
    let mut parts: Vec<String> = Vec::new();
    for (name, r) in RESULTS.iter() {
        let n = a[hr_index(*r)];
        if n != 0 {
            parts.push(format!("{}:{}", jstr(name), n));
        }
    }
    format!("{{{}}}", parts.join(","))
}

/// `semJson`
fn sem_json(out: &mut String, r: &EvalResult, sem: &SemResult, name: &str, with_j: bool, live: bool) {
    let sc = &sem.score;
    let h = &sem.health;
    let rank = if h.failed { Rank::F } else { sc.rank };
    let ft = match h.fail_time {
        Some(t) => hex_d(t),
        None => "null".to_string(),
    };
    let _ = write!(
        out,
        "{{\"semantics\":{},\"failed\":{},\"fail_time\":{},\"fail_trigger_count\":{},\"rank\":{},\"total_score\":{},\"total_score_without_mods\":{},\"accuracy\":{},\"max_combo\":{},\"final_combo\":{},\"final_health\":{},\"completed\":{},\"statistics\":{},\"maximum_statistics\":{},\"legacy_counts\":{{\"300\":{},\"100\":{},\"50\":{},\"miss\":{}}},\"judgement_count\":{}",
        jstr(name),
        h.failed,
        ft,
        h.fail_triggers,
        jstr(rank_name(rank)),
        sc.total_score,
        sc.total_score_without_mods,
        hex_d(sc.accuracy),
        sc.highest_combo,
        sc.combo,
        hex_d(h.health),
        sc.has_completed,
        stats_json(&sc.stats),
        stats_json(&r.max_stats),
        sc.stats[hr_index(HitResult::Great)],
        sc.stats[hr_index(HitResult::Ok_)],
        sc.stats[hr_index(HitResult::Meh)],
        sc.stats[hr_index(HitResult::Miss)],
        r.judgements.len()
    );
    if with_j {
        out.push_str(",\"judgements\":[");
        for (k, j) in r.judgements.iter().enumerate() {
            if k > 0 {
                out.push(',');
            }
            let tn = type_name(j.type_id);
            let ty = if tn.is_empty() { kind_type_name(j.kind) } else { tn };
            let (combo, health, failed) = if live { (j.combo, j.health, j.failed) } else { (j.combo_rp, j.health_rp, j.failed_rp) };
            let _ = write!(
                out,
                "{{\"i\":{},\"n\":{},\"type\":{},\"result\":{},\"time\":{},\"combo\":{},\"health\":{},\"failed\":{}}}",
                j.top,
                j.nested,
                jstr(ty),
                jstr(result_name(j.result)),
                hex_d(j.time),
                combo,
                hex_d(health),
                failed
            );
        }
        out.push(']');
    }
    out.push('}');
}

// ---------------------------------------------------------------------------------------------
// `playableJson` (Adapter.lean, section Dump)
// ---------------------------------------------------------------------------------------------

fn js(s: &str) -> String {
    format!("\"{}\"", s)
}
fn hx(x: F64) -> String {
    js(&hex64(x))
}
fn hf(x: F32) -> String {
    js(&hex32(x))
}
fn obj(kvs: &[(&str, String)]) -> String {
    let parts: Vec<String> = kvs.iter().map(|(k, v)| format!("{}:{}", js(k), v)).collect();
    format!("{{{}}}", parts.join(","))
}
fn arr(xs: &[String]) -> String {
    format!("[{}]", xs.join(","))
}
fn kind_key(k: Kind) -> &'static str {
    match k {
        Kind::Circle => "circle",
        Kind::Slider => "slider",
        Kind::Spinner => "spinner",
        Kind::Head => "head",
        Kind::Tick => "tick",
        Kind::Repeat => "repeat",
        Kind::Tail => "tail",
        Kind::SpinnerTick => "spinner_tick",
        Kind::SpinnerBonusTick => "spinner_bonus_tick",
    }
}
fn hobj_kvs(h: &HObj) -> Vec<(&'static str, String)> {
    let z = F64::from_bits(0);
    let hw = match &h.hit_windows {
        Some(w) => arr(&[hx(w.great), hx(w.ok_), hx(w.meh), hx(w.miss)]),
        None => arr(&[hx(z), hx(z), hx(z), hx(z)]),
    };
    let tn = type_name(h.type_id);
    vec![
        ("kind", js(kind_key(h.kind))),
        ("type", js(tn)),
        ("start", hx(h.start)),
        ("end", hx(h.end_time)),
        ("pos", arr(&[hf(h.pos.x), hf(h.pos.y)])),
        ("stacked", arr(&[hf(h.stacked.x), hf(h.stacked.y)])),
        ("stack_height", h.stack_height.to_string()),
        ("scale", hf(h.scale)),
        ("radius", hx(h.radius)),
        ("preempt", hx(h.preempt)),
        ("fade_in", hx(h.fade_in)),
        ("max_judgement_offset", hx(h.max_judgement_offset)),
        ("hit_windows", hw),
        ("max_result", js(result_name(h.max_result))),
        ("min_result", js(result_name(h.min_result))),
        ("new_combo", h.new_combo.to_string()),
        ("combo_index", h.combo_index.to_string()),
        ("index_in_combo", h.index_in_combo.to_string()),
        ("last_in_combo", h.last_in_combo.to_string()),
    ]
}
fn nested_json(h: &HObj) -> String {
    let mut kv = hobj_kvs(h);
    match h.kind {
        Kind::Tick => {
            kv.push(("span_index", h.span_index.to_string()));
            kv.push(("span_start", hx(h.span_start)));
            kv.push(("path_progress", hx(h.path_progress)));
        }
        Kind::Repeat => {
            kv.push(("repeat_index", h.repeat_index.to_string()));
            kv.push(("path_progress", hx(h.path_progress)));
        }
        Kind::Tail => kv.push(("repeat_index", h.repeat_index.to_string())),
        _ => {}
    }
    obj(&kv)
}
fn top_json(o: &TopObj) -> String {
    let mut kv = hobj_kvs(&o.h);
    match (&o.slider, &o.spinner) {
        (Some(s), _) => {
            kv.push(("span_count", s.span_count.to_string()));
            kv.push(("duration", hx(s.duration)));
            kv.push(("span_duration", hx(s.span_duration)));
            kv.push(("velocity", hx(s.velocity)));
            kv.push(("path_distance", hx(s.path_distance)));
            kv.push(("classic", s.classic.to_string()));
            let p: Vec<String> = s.path.iter().flat_map(|v| [hf(v.x), hf(v.y)]).collect();
            kv.push(("path", arr(&p)));
            let c: Vec<String> = s.cum_len.iter().map(|x| hx(*x)).collect();
            kv.push(("cumulative_length", arr(&c)));
        }
        (None, Some(s)) => {
            kv.push(("duration", hx(s.duration)));
            kv.push(("spins_required", s.spins_required.to_string()));
            kv.push(("maximum_bonus_spins", s.max_bonus_spins.to_string()));
        }
        (None, None) => {}
    }
    let ns: Vec<String> = o.nested.iter().map(nested_json).collect();
    kv.push(("nested", arr(&ns)));
    obj(&kv)
}
fn diff_json(d: &osu_eval_core::sim::playable::Difficulty, extra: Vec<(&'static str, String)>) -> String {
    let mut kv = vec![("cs", hf(d.cs)), ("hp", hf(d.hp)), ("od", hf(d.od)), ("ar", hf(d.ar))];
    kv.extend(extra);
    obj(&kv)
}
/// `playableJson`
fn playable_json(p: &Playable) -> String {
    let br: Vec<String> = p.breaks.iter().map(|b| arr(&[hx(b.start), hx(b.end)])).collect();
    let os: Vec<String> = p.objects.iter().map(top_json).collect();
    obj(&[
        ("format", js("playable-1")),
        ("beatmap_version", p.beatmap_version.to_string()),
        ("audio_lead_in", hx(p.audio_lead_in)),
        ("difficulty", diff_json(&p.difficulty, vec![("slider_multiplier", hx(p.slider_multiplier)), ("slider_tick_rate", hx(p.slider_tick_rate))])),
        ("base_difficulty", diff_json(&p.base_difficulty, vec![])),
        ("breaks", arr(&br)),
        ("objects", arr(&os)),
    ])
}

// ---------------------------------------------------------------------------------------------
// main
// ---------------------------------------------------------------------------------------------

/// `parseExplicit`
fn parse_explicit(path: &str) -> Result<Vec<F64>, (i32, String)> {
    let txt = std::fs::read_to_string(path).map_err(|e| (1, format!("uncaught exception: {}", e)))?;
    let mut out = Vec::new();
    for l in txt.split('\n') {
        let l = l.trim_matches(|c: char| c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c');
        if l.is_empty() {
            continue;
        }
        let cs: Vec<u32> = l.chars().map(|c| c as u32).collect();
        match double_parse(&cs) {
            Ok(v) => out.push(v),
            Err(_) => return Err((2, format!("bad reference time {}", l))),
        }
    }
    Ok(out)
}

struct Cli {
    pos: Vec<String>,
    sched_s: String,
    mods_arg: Option<String>,
    replace_mods: bool,
    no_classic: bool,
    with_j: bool,
    with_steps: bool,
    timing: bool,
    dump_playable: Option<String>,
    batch: Option<String>,
}

fn rejected_line(e: &Rejection, bm: &str, rp: &str) -> String {
    format!(
        "{{\"rejected\":{},\"stage\":{},\"input\":{{\"beatmap\":{},\"replay\":{}}}}}\n",
        jstr(&reason_text(&e.reason)),
        jstr(stage_text(e.stage)),
        jstr(bm),
        jstr(rp)
    )
}

/// One job: (exit code, stdout, stderr).
fn run_job(cli: &Cli, bm_path: &str, rp_path: &str, mods_arg: &Option<String>) -> (i32, String, String) {
    let t0 = std::time::Instant::now();
    let mut opts = Options { mods_override: None, replace_mods: cli.replace_mods, no_classic: cli.no_classic };
    if let Some(m) = mods_arg {
        let cs: Vec<u32> = m.chars().map(|c| c as u32).collect();
        match parse_mods(&cs) {
            Ok(ms) => opts.mods_override = Some(ms),
            Err(e) => {
                return (1, format!("{{\"rejected\":{},\"stage\":\"mods\"}}\n", jstr(&format!("mods JSON: {}", mods_json_err(e)))), String::new())
            }
        }
    }
    let sched = if let Some(f) = cli.sched_s.strip_prefix("explicit:") {
        match parse_explicit(f) {
            Ok(refs) => Schedule::Explicit(refs),
            Err((code, msg)) => return (code, String::new(), msg + "\n"),
        }
    } else {
        match cli.sched_s.as_str() {
            "catchup" => Schedule::Kind(ScheduleKind::Catchup),
            "perframe" => Schedule::Kind(ScheduleKind::Perframe),
            "dense1ms" => Schedule::Kind(ScheduleKind::Dense1ms),
            s => return (2, String::new(), format!("unknown schedule {}\n", s)),
        }
    };
    let bm = match std::fs::read(bm_path) {
        Ok(b) => b,
        Err(e) => return (1, String::new(), format!("uncaught exception: {}\n", e)),
    };
    let osr = match std::fs::read(rp_path) {
        Ok(b) => b,
        Err(e) => return (1, String::new(), format!("uncaught exception: {}\n", e)),
    };
    if let Some(p) = &cli.dump_playable {
        return match playable_for(&bm, &osr, &opts) {
            Ok(spb) => match std::fs::write(p, playable_json(&spb)) {
                Ok(_) => (0, "{\"dumped\":true}\n".to_string(), String::new()),
                Err(e) => (1, String::new(), format!("uncaught exception: {}\n", e)),
            },
            Err(e) => (1, rejected_line(&e, bm_path, rp_path), String::new()),
        };
    }
    match evaluate(default_env(), &bm, &osr, &opts, &sched) {
        Err(e) => (1, rejected_line(&e, bm_path, rp_path), String::new()),
        Ok(r) => {
            let mut out = String::with_capacity(160 * r.judgements.len() + 4096);
            let lf = match r.last_frame_time {
                Some(t) => format!(",\"last_frame_time\":{}", hex_d(t)),
                None => String::new(),
            };
            let mods_arg_j = match mods_arg {
                Some(m) => format!(",\"mods_arg\":{}", jstr(m)),
                None => String::new(),
            };
            let hash = match &r.replay_beatmap_hash {
                Some(h) => jstr(&str_of(h)),
                None => "null".to_string(),
            };
            let sched_name = match r.schedule_kind {
                Some(ScheduleKind::Catchup) => "catchup",
                Some(ScheduleKind::Perframe) => "perframe",
                Some(ScheduleKind::Dense1ms) => "dense1ms",
                None => "explicit",
            };
            let _ = write!(
                out,
                "{{\"model\":\"OsuModel.Eval\",\"input\":{{\"beatmap\":{},\"replay\":{},\"replay_beatmap_md5\":{},\"replay_version\":{},\"is_legacy_score\":{}{},\"no_classic\":{},\"replace_mods\":{},\"decoded_mods_acronyms\":{},\"mods_acronyms\":{},\"decoded_mods\":{},\"mods\":{},\"true_gameplay_rate\":{},\"hit_objects\":{},\"frames\":{}}},",
                jstr(bm_path),
                jstr(rp_path),
                hash,
                r.replay_version,
                r.is_legacy_score,
                mods_arg_j,
                opts.no_classic,
                opts.replace_mods,
                acr_json(&r.decoded_mods),
                acr_json(&r.mods),
                mods_json(&r.decoded_mods),
                mods_json(&r.mods),
                hex_d(r.true_gameplay_rate),
                r.hit_objects,
                r.frames
            );
            let _ = write!(
                out,
                "\"schedule\":{{\"kind\":{},\"r0\":{},\"end\":{},\"gameplay_start_time\":{}{},\"references\":{},\"steps\":{}}},\"score_multiplier\":{},\"live\":",
                jstr(sched_name),
                hex_d(r.r0),
                hex_d(r.end_time),
                hex_d(r.gameplay_start_time),
                lf,
                r.references,
                r.steps,
                hex_d(r.score_multiplier)
            );
            sem_json(&mut out, &r, &r.live, "live", cli.with_j, true);
            out.push_str(",\"replay_player\":");
            match &r.replay_player {
                Some(rp) => sem_json(&mut out, &r, rp, "replay_player", cli.with_j, false),
                None => out.push_str("\"same_as_live\""),
            }
            if cli.with_steps {
                out.push_str(",\"step_times\":[");
                let ts: Vec<String> = r.step_times.iter().map(|t| hex_d(*t)).collect();
                out.push_str(&ts.join(","));
                out.push(']');
            }
            if cli.timing {
                let _ = write!(out, ",\"wall_ms\":{}", t0.elapsed().as_millis());
            }
            out.push_str("}\n");
            (0, out, String::new())
        }
    }
}

/// Stack of the evaluation thread. The translated JSON reader (`eval::mods_json`) recurses once per
/// array/object item (`array_items_rec`/`object_items_rec`, the Aeneas-provable form, D35/D49) and once
/// per nesting level (`value_f`), so the depth is bounded by the score-info/mods JSON length, which a tiny
/// LZMA-compressed .osr can make large (a 200k-item array overflowed the default 8 MiB main stack).
/// Reserved virtual memory only (pages are committed as touched); if the reservation is refused we fall
/// back to the main thread.
const EVAL_STACK: usize = 4 << 30;

fn main() {
    match std::thread::Builder::new().name("eval".into()).stack_size(EVAL_STACK).spawn(real_main) {
        Ok(h) => {
            if h.join().is_err() {
                std::process::exit(101);
            }
        }
        Err(_) => real_main(),
    }
}

fn real_main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut cli = Cli {
        pos: Vec::new(),
        sched_s: "catchup".to_string(),
        mods_arg: None,
        replace_mods: false,
        no_classic: false,
        with_j: true,
        with_steps: false,
        timing: false,
        dump_playable: None,
        batch: None,
    };
    // the spec's list pattern match: an option that needs a value but is last falls through to
    // "unknown option"
    let mut i = 0;
    while i < args.len() {
        let a = args[i].as_str();
        let has_v = i + 1 < args.len();
        match a {
            "--schedule" if has_v => {
                cli.sched_s = args[i + 1].clone();
                i += 2;
            }
            "--mods" if has_v => {
                cli.mods_arg = Some(args[i + 1].clone());
                i += 2;
            }
            "--replace-mods" => {
                cli.replace_mods = true;
                i += 1;
            }
            "--no-classic" => {
                cli.no_classic = true;
                i += 1;
            }
            "--no-judgements" => {
                cli.with_j = false;
                i += 1;
            }
            "--steps" => {
                cli.with_steps = true;
                i += 1;
            }
            "--timing" => {
                cli.timing = true;
                i += 1;
            }
            "--dump-playable" if has_v => {
                cli.dump_playable = Some(args[i + 1].clone());
                i += 2;
            }
            "--batch" if has_v => {
                cli.batch = Some(args[i + 1].clone());
                i += 2;
            }
            _ => {
                if a.starts_with("--") {
                    eprintln!("unknown option {}", a);
                    std::process::exit(2);
                }
                cli.pos.push(a.to_string());
                i += 1;
            }
        }
    }
    if let Some(list) = cli.batch.clone() {
        // BEATMAP OSR OUT [MODS-JSON]
        let text = std::fs::read_to_string(&list).expect("batch list");
        let mut bad = 0;
        for line in text.lines() {
            let p: Vec<&str> = line.splitn(4, ' ').collect();
            if p.len() < 3 {
                continue;
            }
            let m = if p.len() > 3 { Some(p[3].to_string()) } else { cli.mods_arg.clone() };
            let (code, out, err) = run_job(&cli, p[0], p[1], &m);
            if code != 0 {
                bad += 1;
            }
            std::fs::write(p[2], out + &err).expect("write output");
        }
        std::process::exit(if bad == 0 { 0 } else { 1 });
    }
    if cli.pos.len() != 2 {
        eprintln!("usage: osu_eval BEATMAP.osu REPLAY.osr [options]");
        std::process::exit(2);
    }
    let (bm, rp) = (cli.pos[0].clone(), cli.pos[1].clone());
    let m = cli.mods_arg.clone();
    let (code, out, err) = run_job(&cli, &bm, &rp, &m);
    let mut so = std::io::stdout().lock();
    let _ = so.write_all(out.as_bytes());
    let _ = so.flush();
    if !err.is_empty() {
        eprint!("{}", err);
    }
    std::process::exit(code);
}
