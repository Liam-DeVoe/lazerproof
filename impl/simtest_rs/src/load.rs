//! Loaders mirroring `OsuModel.Sim.Load` (Sim/Playable.lean) and `loadEnv` (SimTest/Main.lean). Not translated.
use crate::json::J;
use osu_eval_core::float::{F32, F64};
use osu_eval_core::sim::basic::{DrawInfo, HitResult, Mat3, Vec2};
use osu_eval_core::sim::geometry::{ChainNode, Env};
use osu_eval_core::sim::playable::*;

pub const RESULT_NAMES: [(&str, HitResult); 18] = [
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

pub fn result_name(r: HitResult) -> &'static str {
    RESULT_NAMES[osu_eval_core::sim::basic::hr_index(r)].0
}

pub fn kind_type_name(k: Kind) -> &'static str {
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

fn kind_of(s: &str) -> Option<Kind> {
    Some(match s {
        "circle" => Kind::Circle,
        "slider" => Kind::Slider,
        "spinner" => Kind::Spinner,
        "head" => Kind::Head,
        "tick" => Kind::Tick,
        "repeat" => Kind::Repeat,
        "tail" => Kind::Tail,
        "spinner_tick" => Kind::SpinnerTick,
        "spinner_bonus_tick" => Kind::SpinnerBonusTick,
        _ => return None,
    })
}

/// `Load.hexVal`
pub fn hex_val(s: &str) -> Result<u128, String> {
    let t = s.strip_prefix("0x").unwrap_or(s);
    let mut v: u128 = 0;
    for c in t.chars() {
        let d = c.to_digit(16).ok_or_else(|| format!("bad hex digit in {}", s))?;
        v = v.wrapping_mul(16).wrapping_add(d as u128);
    }
    Ok(v)
}
pub fn f64j(j: &J) -> Result<F64, String> {
    Ok(F64::from_bits(hex_val(j.str()?)? as u64))
}
pub fn f32j(j: &J) -> Result<F32, String> {
    Ok(F32::from_bits(hex_val(j.str()?)? as u32))
}
pub fn vec2j(j: &J) -> Result<Vec2, String> {
    let a = j.arr()?;
    if a.len() != 2 {
        return Err("vec2: expected 2 elements".into());
    }
    Ok(Vec2 { x: f32j(&a[0])?, y: f32j(&a[1])? })
}

fn fres(j: &J, k: &str) -> Result<HitResult, String> {
    let s = j.field(k)?.str()?;
    RESULT_NAMES.iter().find(|(n, _)| *n == s).map(|(_, r)| *r).ok_or_else(|| format!("unknown HitResult {}", s))
}

/// Type-name table (`HObj.typeName` strings ↔ `type_id`); id 0 = "".
pub struct Names {
    pub names: Vec<String>,
}
impl Names {
    pub fn id(&mut self, s: &str) -> u32 {
        if let Some(i) = self.names.iter().position(|x| x == s) {
            return i as u32;
        }
        self.names.push(s.to_string());
        (self.names.len() - 1) as u32
    }
}

fn hobj(j: &J, names: &mut Names) -> Result<HObj, String> {
    let ks = j.field("kind")?.str()?;
    let kind = kind_of(ks).ok_or_else(|| format!("unknown kind {}", ks))?;
    let hw_a = j.field("hit_windows")?.arr()?;
    let mut hit_windows = if hw_a.len() == 4 {
        Some(HitWindows { great: f64j(&hw_a[0])?, ok_: f64j(&hw_a[1])?, meh: f64j(&hw_a[2])?, miss: f64j(&hw_a[3])? })
    } else {
        None
    };
    if let Some(hw) = hit_windows {
        if hw.miss.eq(F64::from_bits(0)) {
            hit_windows = None;
        }
    }
    let type_name = match j.get("type") {
        Some(v) => v.str()?.to_string(),
        None => kind_type_name(kind).to_string(),
    };
    let mut h = hobj_default();
    h.kind = kind;
    h.hit_windows = hit_windows;
    h.type_id = names.id(&type_name);
    h.strict_tail = type_name == "StrictTrackingSliderTailCircle";
    h.start = f64j(j.field("start")?)?;
    h.end_time = f64j(j.field("end")?)?;
    h.pos = vec2j(j.field("pos")?)?;
    h.stacked = vec2j(j.field("stacked")?)?;
    h.stack_height = j.field("stack_height")?.int()?;
    h.scale = f32j(j.field("scale")?)?;
    h.radius = f64j(j.field("radius")?)?;
    h.preempt = f64j(j.field("preempt")?)?;
    if let Some(v) = j.get("fade_in") {
        h.fade_in = f64j(v)?;
    }
    h.max_judgement_offset = f64j(j.field("max_judgement_offset")?)?;
    h.max_result = fres(j, "max_result")?;
    h.min_result = fres(j, "min_result")?;
    h.new_combo = j.field("new_combo")?.bool()?;
    h.combo_index = j.field("combo_index")?.nat()?;
    h.index_in_combo = j.field("index_in_combo")?.nat()?;
    h.last_in_combo = j.field("last_in_combo")?.bool()?;
    if let Some(v) = j.get("span_index") {
        h.span_index = v.nat()?;
    }
    if let Some(v) = j.get("span_start") {
        h.span_start = f64j(v)?;
    }
    if let Some(v) = j.get("path_progress") {
        h.path_progress = f64j(v)?;
    }
    if let Some(v) = j.get("repeat_index") {
        h.repeat_index = v.nat()?;
    }
    Ok(h)
}

fn top_obj(j: &J, names: &mut Names) -> Result<TopObj, String> {
    let h = hobj(j, names)?;
    let mut nested = Vec::new();
    for n in j.field("nested")?.arr()? {
        nested.push(hobj(n, names)?);
    }
    match h.kind {
        Kind::Slider => {
            let pa = j.field("path")?.arr()?;
            if pa.len() % 2 != 0 {
                return Err("slider path: odd number of coordinates".into());
            }
            let mut path = Vec::new();
            for i in 0..pa.len() / 2 {
                path.push(Vec2 { x: f32j(&pa[2 * i])?, y: f32j(&pa[2 * i + 1])? });
            }
            let mut cum_len = Vec::new();
            for v in j.field("cumulative_length")?.arr()? {
                cum_len.push(f64j(v)?);
            }
            Ok(TopObj {
                h,
                nested,
                spinner: None,
                slider: Some(SliderData {
                    span_count: j.field("span_count")?.nat()?,
                    duration: f64j(j.field("duration")?)?,
                    span_duration: f64j(j.field("span_duration")?)?,
                    velocity: f64j(j.field("velocity")?)?,
                    path_distance: f64j(j.field("path_distance")?)?,
                    classic: j.field("classic")?.bool()?,
                    path,
                    cum_len,
                }),
            })
        }
        Kind::Spinner => Ok(TopObj {
            h,
            nested,
            slider: None,
            spinner: Some(SpinnerData {
                duration: f64j(j.field("duration")?)?,
                spins_required: j.field("spins_required")?.int()?,
                max_bonus_spins: j.field("maximum_bonus_spins")?.int()?,
            }),
        }),
        _ => Ok(TopObj { h, nested, slider: None, spinner: None }),
    }
}

fn difficulty(j: &J) -> Result<Difficulty, String> {
    Ok(Difficulty {
        cs: f32j(j.field("cs")?)?,
        hp: f32j(j.field("hp")?)?,
        od: f32j(j.field("od")?)?,
        ar: f32j(j.field("ar")?)?,
    })
}

/// `Load.playable`
pub fn playable(j: &J, names: &mut Names) -> Result<Playable, String> {
    let fmt = j.field("format")?.str()?;
    if fmt != "playable-1" {
        return Err(format!("unsupported playable format {}", fmt));
    }
    let d = j.field("difficulty")?;
    let mut breaks = Vec::new();
    for b in j.field("breaks")?.arr()? {
        let a = b.arr()?;
        if a.len() != 2 {
            return Err("break: expected [start, end]".into());
        }
        breaks.push(Period { start: f64j(&a[0])?, end: f64j(&a[1])? });
    }
    let mut objects = Vec::new();
    for o in j.field("objects")?.arr()? {
        objects.push(top_obj(o, names)?);
    }
    Ok(Playable {
        beatmap_version: j.field("beatmap_version")?.int()?,
        audio_lead_in: f64j(j.field("audio_lead_in")?)?,
        difficulty: difficulty(d)?,
        base_difficulty: difficulty(j.field("base_difficulty")?)?,
        slider_multiplier: f64j(d.field("slider_multiplier")?)?,
        slider_tick_rate: f64j(d.field("slider_tick_rate")?)?,
        breaks,
        objects,
    })
}

fn mat(v: &J) -> Result<Mat3, String> {
    let a = v.arr()?;
    if a.len() != 9 {
        return Err("matrix: expected 9 entries".into());
    }
    let f = |k: usize| f32j(&a[k]);
    Ok(Mat3 { m11: f(0)?, m12: f(1)?, m13: f(2)?, m21: f(3)?, m22: f(4)?, m23: f(5)?, m31: f(6)?, m32: f(7)?, m33: f(8)? })
}

/// `loadEnv`
pub fn env(j: &J) -> Result<Env, String> {
    let hoc = DrawInfo { matrix: mat(j.field("hit_object_container_matrix")?)?, inverse: mat(j.field("hit_object_container_inverse")?)? };
    let hist = j.field("hit_object_container_history")?.arr()?;
    let hoc_first = if !hist.is_empty() {
        DrawInfo { matrix: mat(hist[0].field("matrix")?)?, inverse: mat(hist[0].field("inverse")?)? }
    } else {
        hoc
    };
    let chain_of = |k: &str| -> Result<Vec<ChainNode>, String> {
        let mut out = Vec::new();
        if let Some(v) = j.get(k) {
            for n in v.arr()? {
                out.push(ChainNode {
                    is_pac: n.field("type")?.str()? == "OsuPlayfieldAdjustmentContainer",
                    pos: vec2j(n.field("pos")?)?,
                    scale: vec2j(n.field("scale")?)?,
                    rot: f32j(n.field("rotation")?)?,
                    origin: vec2j(n.field("origin")?)?,
                });
            }
        }
        Ok(out)
    };
    Ok(Env {
        hoc_first,
        hoc,
        argon_path_radius: f32j(j.field("argon_path_radius")?)?,
        hoc_size: vec2j(j.field("hit_object_container_draw_size")?)?,
        chain_first: chain_of("hoc_chain_first")?,
        chain: chain_of("hoc_chain")?,
    })
}
