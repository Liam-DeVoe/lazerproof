//! tracktrace: debugging companion of simtest_rs (difftest/tracking_trace.py, docs/server-agreement.md).
//! Runs the Rust Sim exactly like `simtest_rs` (same loaders, `mk_ctx`/`init_state`/`step_once` loop of
//! `step::run`) and additionally prints, for every slider, the per-step changes of its tracking-relevant state
//! after each frame-stable step:
//!   [t, tracking, mouse in follow area (r), mouse in expanded follow area (2.4 r), any valid tracking action,
//!    pressed (bit 1 = left, 2 = right), hit_action (0 none / 1 left / 2 right), accept_any_after (or null), life]
//! Only NF/CL are simulated; other mods must already be baked into the playable dump (beatmap-side mods) or be
//! judgement-neutral for lazer-replay playback. They are listed under "ignored_mods".
//! Usage: tracktrace --playable P.json --frames F.txt --env ENV.json [--schedule S] [--mods CSV] [--lazer-replay]
//! Output (stdout, one JSON object): {"judgements": [[i, n, type, result, time], ...], "statistics": {...},
//!   "tracking": {"<slider index>": [[...], ...]}, "ignored_mods": [...]}
#[path = "../json.rs"]
mod json;
#[path = "../load.rs"]
#[allow(dead_code)]
mod load;

use osu_eval_core::float::F64;
use osu_eval_core::replay::frames::{self, act_contains, Action};
use osu_eval_core::sim::basic::hr_index;
use osu_eval_core::sim::mods::config_of_mods;
use osu_eval_core::beatmap::mod_settings::to_mod;
use osu_eval_core::sim::playable::Kind;
use osu_eval_core::sim::schedule::ScheduleKind;
use osu_eval_core::sim::state::Life;
use osu_eval_core::sim::step::{any_valid_tracking_action, init_state, mk_ctx, mouse_in_follow_area, step_once};
use std::fmt::Write as _;

fn f(x: F64) -> f64 {
    f64::from_bits(x.to_bits())
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (mut playable, mut frames_p, mut env_p, mut sched, mut mods, mut lazer) =
        (String::new(), String::new(), String::new(), ScheduleKind::Catchup, Vec::<String>::new(), false);
    let mut i = 0;
    while i < args.len() {
        let v = args.get(i + 1).cloned().unwrap_or_default();
        match args[i].as_str() {
            "--playable" => playable = v,
            "--frames" => frames_p = v,
            "--env" => env_p = v,
            "--schedule" => {
                sched = match v.as_str() {
                    "perframe" => ScheduleKind::Perframe,
                    "dense1ms" => ScheduleKind::Dense1ms,
                    _ => ScheduleKind::Catchup,
                }
            }
            "--mods" => mods = v.split(',').filter(|x| !x.is_empty()).map(|x| x.to_ascii_uppercase()).collect(),
            "--lazer-replay" => {
                lazer = true;
                i += 1;
                continue;
            }
            a => {
                eprintln!("unknown argument {}", a);
                std::process::exit(2);
            }
        }
        i += 2;
    }
    let mut names = load::Names { names: vec![String::new()] };
    let pb = json::parse(&std::fs::read_to_string(&playable).expect("playable"))
        .and_then(|v| load::playable(&v, &mut names))
        .expect("playable parse");
    let env = json::parse(&std::fs::read_to_string(&env_p).expect("env")).and_then(|v| load::env(&v)).expect("env parse");
    let text = std::fs::read_to_string(&frames_p).expect("frames");
    let cps: Vec<u32> = text.chars().map(|c| c as u32).collect();
    let fr = match frames::decode(&cps, pb.beatmap_version) {
        Ok(f) => f,
        Err(_) => {
            eprintln!("frame decode error");
            std::process::exit(1);
        }
    };
    let mut ml = Vec::new();
    let mut ignored = Vec::new();
    for m in &mods {
        match m.as_str() {
            "NF" | "CL" => ml.push(to_mod(&m.chars().map(|c| c as u32).collect::<Vec<u32>>(), &[])),
            _ => ignored.push(m.clone()),
        }
    }
    let cfg = config_of_mods(&ml, &pb, lazer);
    let c = match mk_ctx(env, cfg, pb, fr, sched) {
        Ok(c) => c,
        Err(_) => {
            eprintln!("rejected by the simulation (run simtest_rs for the message)");
            std::process::exit(1);
        }
    };
    let mut s = match init_state(&c.cfg, &c.pb, c.smax.init_without_mods) {
        Ok(s) => s,
        Err(_) => {
            eprintln!("rejected by the simulation (run simtest_rs for the message)");
            std::process::exit(1);
        }
    };
    let nobj = c.pb.objects.len();
    let mut last: Vec<Option<String>> = vec![None; nobj];
    let mut trace: Vec<String> = vec![String::new(); nobj];
    let mut k = 0;
    while k < c.steps.len() {
        s.k = k;
        s.t = c.steps[k].time;
        if step_once(&c, &mut s).is_err() {
            eprintln!("rejected by the simulation (run simtest_rs for the message)");
            std::process::exit(1);
        }
        for i in 0..nobj {
            if c.pb.objects[i].h.kind != Kind::Slider {
                continue;
            }
            let os = &s.objs[i];
            if os.life != Life::Alive && last[i].is_none() {
                continue;
            }
            let pressed = (act_contains(&s.pressed, Action::Left) as u8) | ((act_contains(&s.pressed, Action::Right) as u8) << 1);
            let ha = match os.hit_action {
                None => 0,
                Some(Action::Left) => 1,
                Some(Action::Right) => 2,
                Some(Action::Smoke) => 3,
            };
            let aaa = match os.accept_any_after {
                None => "null".to_string(),
                Some(x) => format!("{}", f(x)),
            };
            let life = match os.life {
                Life::Future => "F",
                Life::Alive => "A",
                Life::Past => "P",
            };
            let st = format!(
                "{},{},{},{},{},{},{},\"{}\"",
                os.tracking,
                mouse_in_follow_area(&c, &s, i, false).unwrap_or(false),
                mouse_in_follow_area(&c, &s, i, true).unwrap_or(false),
                any_valid_tracking_action(os, s.t, &s.pressed),
                pressed,
                ha,
                aaa,
                life
            );
            if last[i].as_deref() != Some(st.as_str()) {
                if !trace[i].is_empty() {
                    trace[i].push(',');
                }
                let _ = write!(trace[i], "[{},{}]", f(s.t), st);
                last[i] = Some(st);
            }
            if os.life == Life::Past {
                last[i] = None;
            }
        }
        k += 1;
    }
    let mut out = String::new();
    out.push_str("{\"judgements\":[");
    for (q, jr) in s.out.iter().enumerate() {
        if q > 0 {
            out.push(',');
        }
        let tn = &names.names[jr.type_id as usize];
        let tname: &str = if tn.is_empty() { load::kind_type_name(jr.kind) } else { tn };
        let _ = write!(out, "[{},{},\"{}\",\"{}\",{}]", jr.top, jr.nested, tname, load::result_name(jr.result), f(jr.time));
    }
    out.push_str("],\"statistics\":{");
    let mut first = true;
    for (name, r) in load::RESULT_NAMES.iter() {
        let n = s.score.stats[hr_index(*r)];
        if n != 0 {
            let _ = write!(out, "{}\"{}\":{}", if first { "" } else { "," }, name, n);
            first = false;
        }
    }
    out.push_str("},\"tracking\":{");
    let mut first = true;
    for (i, t) in trace.iter().enumerate() {
        if !t.is_empty() {
            let _ = write!(out, "{}\"{}\":[{}]", if first { "" } else { "," }, i, t);
            first = false;
        }
    }
    let _ = write!(out, "}},\"ignored_mods\":[{}]}}\n",
                   ignored.iter().map(|m| format!("\"{}\"", m)).collect::<Vec<_>>().join(","));
    print!("{}", out);
}
