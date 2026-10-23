//! simtest_rs: the Rust port of the Sim model, with the same CLI and output as the Lean `simtest`
//! (`model/SimTest/Main.lean`):
//! ```
//! simtest_rs --playable P.json --frames F.txt --env ENV.json [--schedule catchup|perframe|dense1ms]
//!            [--mods CL,NF,...] [--mods-json JSON] [--lazer-replay] [--steps]
//! ```
//! Additionally `--batch LIST` runs many jobs in one process (one line per job:
//! `PLAYABLE FRAMES OUT [SCHEDULE [MODS]]`, writing each output to OUT) for throughput measurements.
//! Port scope: the Lean Sim at commit 3f88501 (M0-M6: all sim-side mods of that spec; any mod list is accepted, as in Lean).
mod json;
mod load;

use osu_eval_core::float::F64;
use osu_eval_core::replay::frames;
use osu_eval_core::net::basic::NetExn;
use osu_eval_core::sim::basic::{hr_index, HitResult};
use osu_eval_core::beatmap::mod_settings::{to_mod, JsonVal, ModConfig};
use osu_eval_core::net::parse::double_parse;
use osu_eval_core::sim::mods::config_of_mods;
use osu_eval_core::sim::geometry::compose_chain;
use osu_eval_core::sim::schedule::ScheduleKind;
use osu_eval_core::sim::scoring::{HealthSt, Rank, ScoreSt};
use osu_eval_core::sim::err::{Internal, SimErr};
use osu_eval_core::sim::playable::Kind;
use osu_eval_core::sim::step::simulate;
use std::fmt::Write as _;
use std::io::Write as _;

/// Newtonsoft-like classification of a JSON settings value (spec `SimJson.toSetting`, `Sim/ModsJson.lean`).
fn to_setting(v: &json::J) -> JsonVal {
    match v {
        json::J::Num(t) => {
            if t.chars().any(|c| c == '.' || c == 'e' || c == 'E') {
                let cs: Vec<u32> = t.chars().map(|c| c as u32).collect();
                match double_parse(&cs) {
                    Ok(d) => JsonVal::Double(d),
                    Err(_) => JsonVal::Null,
                }
            } else {
                // Lean `String.toNat!` (non-digits -> 0)
                let (neg, digits) = if let Some(r) = t.strip_prefix('-') { (true, r) } else { (false, t.as_str()) };
                let m: Option<u128> = if digits.is_empty() || !digits.chars().all(|c| c.is_ascii_digit()) {
                    Some(0)
                } else {
                    let mut v: Option<u128> = Some(0);
                    for c in digits.chars() {
                        v = v.and_then(|x| x.checked_mul(10)).and_then(|x| x.checked_add(c as u128 - '0' as u128));
                    }
                    v
                };
                match m {
                    None => JsonVal::Big,
                    Some(m) => {
                        let n: i128 = if neg { -(m as i128) } else { m as i128 };
                        if n < i64::MIN as i128 || n > i64::MAX as i128 {
                            JsonVal::Big
                        } else {
                            JsonVal::Long(n as i64)
                        }
                    }
                }
            }
        }
        json::J::Str(x) => JsonVal::Str(s32(x)),
        json::J::Bool(b) => JsonVal::Bool(*b),
        json::J::Null => JsonVal::Null,
        _ => JsonVal::Big,
    }
}

fn s32(s: &str) -> Vec<u32> {
    s.chars().map(|c| c as u32).collect()
}

/// `SimJson.parseMods`: `List<APIMod>` JSON -> decoded mods (`APIMod.ToMod`)
fn parse_mods_json(s: &str) -> Result<Vec<ModConfig>, String> {
    let v = json::parse(s)?;
    let mut out = Vec::new();
    for m in v.arr().map_err(|_| "mods is not an array".to_string())? {
        let json::J::Obj(kvs) = m else { return Err("mod is not an object".into()) };
        let acr: Vec<u32> = match kvs.iter().find(|(k, _)| k == "acronym") {
            Some((_, json::J::Str(a))) => s32(a),
            _ => vec![],
        };
        let settings: Vec<(Vec<u32>, JsonVal)> = match kvs.iter().find(|(k, _)| k == "settings") {
            Some((_, json::J::Obj(ss))) => ss.iter().map(|(k, v)| (s32(k), to_setting(v))).collect(),
            _ => vec![],
        };
        out.push(to_mod(&acr, &settings));
    }
    Ok(out)
}

fn mat_bit_eq(a: &osu_eval_core::sim::basic::Mat3, b: &osu_eval_core::sim::basic::Mat3) -> bool {
    let fa = [a.m11, a.m12, a.m13, a.m21, a.m22, a.m23, a.m31, a.m32, a.m33];
    let fb = [b.m11, b.m12, b.m13, b.m21, b.m22, b.m23, b.m31, b.m32, b.m33];
    fa.iter().zip(fb.iter()).all(|(x, y)| x.to_bits() == y.to_bits())
}

fn hex64(x: F64) -> String {
    format!("0x{:016x}", x.to_bits())
}

fn stats_json(a: &[u64; 18]) -> String {
    let mut parts: Vec<String> = Vec::new();
    for (name, r) in load::RESULT_NAMES.iter() {
        let n = a[hr_index(*r)];
        if n != 0 {
            parts.push(format!("\"{}\":{}", name, n));
        }
    }
    format!("{{{}}}", parts.join(","))
}

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

fn result_json(sc: &ScoreSt, h: &HealthSt, sem: &str, max_stats: &[u64; 18]) -> String {
    let rank = if h.failed { Rank::F } else { sc.rank };
    let ft = match h.fail_time {
        Some(t) => format!("\"{}\"", hex64(t)),
        None => "null".into(),
    };
    format!(
        "{{\"semantics\":\"{}\",\"failed\":{},\"fail_time\":{},\"fail_trigger_count\":{},\"rank\":\"{}\",\"total_score\":{},\"total_score_without_mods\":{},\"accuracy\":\"{}\",\"max_combo\":{},\"final_combo\":{},\"final_health\":\"{}\",\"completed\":{},\"statistics\":{},\"maximum_statistics\":{},\"legacy_counts\":{{\"300\":{},\"100\":{},\"50\":{},\"miss\":{}}}}}",
        sem,
        h.failed,
        ft,
        h.fail_triggers,
        rank_name(rank),
        sc.total_score,
        sc.total_score_without_mods,
        hex64(sc.accuracy),
        sc.highest_combo,
        sc.combo,
        hex64(h.health),
        sc.has_completed,
        stats_json(&sc.stats),
        stats_json(max_stats),
        sc.stats[hr_index(HitResult::Great)],
        sc.stats[hr_index(HitResult::Ok_)],
        sc.stats[hr_index(HitResult::Meh)],
        sc.stats[hr_index(HitResult::Miss)],
    )
}

fn netexn_repr(e: NetExn) -> &'static str {
    match e {
        NetExn::Format => "OsuModel.Net.NetExn.format",
        NetExn::Overflow => "OsuModel.Net.NetExn.overflow",
        NetExn::Argument => "OsuModel.Net.NetExn.argument",
        NetExn::ArgumentOutOfRange => "OsuModel.Net.NetExn.argumentOutOfRange",
        _ => "OsuModel.Net.NetExn.arithmetic",
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

/// Lean `repr` of a `Kind`
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

/// The spec's rejection message for a `SimErr` (Lean `e0e8215`, `throw` sites named in `sim::err`).
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

struct Job {
    playable: String,
    frames: String,
    env: String,
    sched: ScheduleKind,
    mods: Option<Vec<String>>,
    mods_json: Option<String>,
    lazer_replay: bool,
    print_steps: bool,
}

/// Runs one job; returns (exit code, stdout text, stderr text).
fn run_job(j: &Job, env_cache: &mut Option<(String, osu_eval_core::sim::geometry::Env)>) -> (i32, String, String) {
    let mut names = load::Names { names: vec![String::new()] };
    let pt = match std::fs::read_to_string(&j.playable) {
        Ok(t) => t,
        Err(e) => return (1, String::new(), format!("playable: {}\n", e)),
    };
    let pb = match json::parse(&pt).and_then(|v| load::playable(&v, &mut names)) {
        Ok(p) => p,
        Err(e) => return (1, String::new(), format!("playable: {}\n", e)),
    };
    let env = match env_cache {
        Some((p, e)) if *p == j.env => e.clone(),
        _ => {
            let et = match std::fs::read_to_string(&j.env) {
                Ok(t) => t,
                Err(e) => return (1, String::new(), format!("env: {}\n", e)),
            };
            match json::parse(&et).and_then(|v| load::env(&v)) {
                Ok(e) => {
                    *env_cache = Some((j.env.clone(), e.clone()));
                    e
                }
                Err(e) => return (1, String::new(), format!("env: {}\n", e)),
            }
        }
    };
    let text = match std::fs::read(&j.frames) {
        Ok(b) => match String::from_utf8(b) {
            Ok(t) => t,
            Err(_) => return (1, String::new(), "frames: invalid UTF-8\n".into()),
        },
        Err(e) => return (1, String::new(), format!("frames: {}\n", e)),
    };
    let cps: Vec<u32> = text.chars().map(|c| c as u32).collect();
    let fr = match frames::decode(&cps, pb.beatmap_version) {
        Ok(f) => f,
        Err(e) => return (1, format!("{{\"error\": \"frame decode: {}\"}}\n", netexn_repr(e)), String::new()),
    };
    if !env.chain.is_empty() {
        // the recomposed ancestor chain must reproduce the dumped HitObjectContainer matrices bit-exactly
        let a = compose_chain(&env.chain, None);
        let b = compose_chain(&env.chain_first, None);
        if !(mat_bit_eq(&a.matrix, &env.hoc.matrix)
            && mat_bit_eq(&a.inverse, &env.hoc.inverse)
            && mat_bit_eq(&b.matrix, &env.hoc_first.matrix)
            && mat_bit_eq(&b.inverse, &env.hoc_first.inverse))
        {
            return (1, String::new(), "env: hoc_chain does not reproduce the HitObjectContainer DrawInfo\n".into());
        }
    }
    let mod_list = match &j.mods_json {
        Some(s) => match parse_mods_json(s) {
            Ok(m) => m,
            Err(e) => return (2, String::new(), format!("mods json: {}\n", e)),
        },
        None => {
            let mut v = Vec::new();
            for a in j.mods.as_deref().unwrap_or(&[]) {
                v.push(to_mod(&s32(a), &[]));
            }
            v
        }
    };
    let cfg = config_of_mods(&mod_list, &pb, j.lazer_replay);
    let score_multiplier = cfg.score_multiplier;
    let n_frames = fr.len();
    let (c, s) = match simulate(env, cfg, pb, fr, j.sched) {
        Ok(cs) => cs,
        // rejection (malformed input, or a computation lazer would throw on): reported, never a default result
        Err(e) => return (1, format!("{{\"error\":\"sim: {}\"}}\n", sim_err_message(&e)), String::new()),
    };
    let mut out = String::with_capacity(64 * s.out.len() + 4096);
    let sched_name = match j.sched {
        ScheduleKind::Catchup => "catchup",
        ScheduleKind::Perframe => "perframe",
        ScheduleKind::Dense1ms => "dense1ms",
    };
    out.push('{');
    let _ = write!(
        out,
        "\"model\":\"OsuModel.Sim\",\"schedule\":\"OsuModel.Sim.ScheduleKind.{}\",\"frames\":{},\"steps\":{},",
        sched_name,
        n_frames,
        c.steps.len()
    );
    if j.print_steps {
        out.push_str("\"step_times\":[");
        for (k, st) in c.steps.iter().enumerate() {
            if k > 0 {
                out.push(',');
            }
            let _ = write!(out, "\"{}\"", hex64(st.time));
        }
        out.push_str("],");
    }
    let _ = write!(out, "\"score_multiplier\":\"{}\",", hex64(score_multiplier));
    let _ = write!(
        out,
        "\"drain_rate\":\"{}\",\"hp_multiplier\":\"{}\",",
        hex64(c.hcfg.drain_rate),
        hex64(c.hcfg.hp_multiplier_normal)
    );
    let _ = write!(
        out,
        "\"live\":{},\"replay_player\":{},",
        result_json(&s.score, &s.health, "live", &c.smax.max_stats),
        result_json(&s.score_rp, &s.health_rp, "replay_player", &c.smax.max_stats)
    );
    let _ = write!(
        out,
        "\"max_combo\":{},\"final_combo\":{},\"judgement_count\":{},",
        s.score.highest_combo,
        s.score.combo,
        s.out.len()
    );
    let _ = write!(out, "\"statistics\":{},\"judgements\":[", stats_json(&s.score.stats));
    for (k, jr) in s.out.iter().enumerate() {
        if k > 0 {
            out.push(',');
        }
        let tn = &names.names[jr.type_id as usize];
        let tname: &str = if tn.is_empty() { load::kind_type_name(jr.kind) } else { tn };
        let _ = write!(
            out,
            "{{\"i\":{},\"n\":{},\"type\":\"{}\",\"result\":\"{}\",\"time\":\"{}\",\"combo\":{},\"health\":\"{}\",\"failed\":{},\"rp_combo\":{},\"rp_health\":\"{}\",\"rp_failed\":{}}}",
            jr.top,
            jr.nested,
            tname,
            load::result_name(jr.result),
            hex64(jr.time),
            jr.combo,
            hex64(jr.health),
            jr.failed,
            jr.combo_rp,
            hex64(jr.health_rp),
            jr.failed_rp
        );
    }
    out.push_str("]}\n");
    (0, out, String::new())
}

fn sched_of(v: &str) -> Option<ScheduleKind> {
    match v {
        "catchup" => Some(ScheduleKind::Catchup),
        "perframe" => Some(ScheduleKind::Perframe),
        "dense1ms" => Some(ScheduleKind::Dense1ms),
        _ => None,
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut job = Job {
        playable: String::new(),
        frames: String::new(),
        env: String::new(),
        sched: ScheduleKind::Catchup,
        mods: None,
        mods_json: None,
        lazer_replay: false,
        print_steps: false,
    };
    let mut batch: Option<String> = None;
    let mut i = 0;
    while i < args.len() {
        let a = args[i].as_str();
        let val = || args.get(i + 1).cloned().unwrap_or_default();
        match a {
            "--playable" => {
                job.playable = val();
                i += 2;
            }
            "--frames" => {
                job.frames = val();
                i += 2;
            }
            "--env" => {
                job.env = val();
                i += 2;
            }
            "--schedule" => {
                let v = val();
                match sched_of(&v) {
                    Some(k) => job.sched = k,
                    None => {
                        eprintln!("unknown schedule {}", v);
                        std::process::exit(2);
                    }
                }
                i += 2;
            }
            "--mods" => {
                job.mods = Some(val().split(',').filter(|x| !x.is_empty()).map(|x| x.to_string()).collect());
                i += 2;
            }
            "--mods-json" => {
                job.mods_json = Some(val());
                i += 2;
            }
            "--lazer-replay" => {
                job.lazer_replay = true;
                i += 1;
            }
            "--steps" => {
                job.print_steps = true;
                i += 1;
            }
            "--batch" => {
                batch = Some(val());
                i += 2;
            }
            _ => {
                eprintln!("unknown argument {}", a);
                std::process::exit(2);
            }
        }
    }
    let mut env_cache = None;
    match batch {
        None => {
            let (code, out, err) = run_job(&job, &mut env_cache);
            let mut so = std::io::stdout().lock();
            let _ = so.write_all(out.as_bytes());
            let _ = so.flush();
            if !err.is_empty() {
                eprint!("{}", err);
            }
            std::process::exit(code);
        }
        Some(list) => {
            // PLAYABLE FRAMES OUT [SCHEDULE [MODS-CSV|-]] ; env/flags from the command line
            let text = std::fs::read_to_string(&list).expect("batch list");
            let mut bad = 0;
            for line in text.lines() {
                let p: Vec<&str> = line.split_whitespace().collect();
                if p.len() < 3 {
                    continue;
                }
                let mut j = Job {
                    playable: p[0].into(),
                    frames: p[1].into(),
                    env: job.env.clone(),
                    sched: job.sched,
                    mods: job.mods.clone(),
                    mods_json: job.mods_json.clone(),
                    lazer_replay: job.lazer_replay,
                    print_steps: job.print_steps,
                };
                if p.len() > 3 {
                    j.sched = sched_of(p[3]).expect("schedule");
                }
                if p.len() > 4 {
                    j.mods = Some(if p[4] == "-" { vec![] } else { p[4].split(',').map(|x| x.to_string()).collect() });
                    j.mods_json = None;
                }
                let (code, out, err) = run_job(&j, &mut env_cache);
                if code != 0 {
                    bad += 1;
                }
                std::fs::write(p[2], out + &err).expect("write output");
            }
            std::process::exit(if bad == 0 { 0 } else { 1 });
        }
    }
}
