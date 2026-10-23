//! Port of `OsuModel/Eval.lean`: the end-to-end model (`.osu` bytes + `.osr` bytes (+ mod override) +
//! schedule -> result, or a rejection with a stage and a reason; docs/model-eval.md):
//! ```text
//! evaluate env beatmapBytes osrBytes opts schedule
//!   = beatmap decode            (crate::beatmap, LegacyBeatmapDecoder)
//!     .osr decode               (eval::osr, LegacyScoreDecoder.Parse; LZMA = trusted crate::lzma)
//!     decode-time playable      (LegacyScoreDecoder.cs:94, only its failure matters)
//!     mod resolution            (oracle ResolveMods: --replace-mods / --no-classic / --mods)
//!     gameplay playable         (GetPlayableBeatmap with the gameplay mods) -> eval::adapter -> Sim.Playable
//!     frames                    (crate::replay::frames, beatmap version offset)
//!     schedule + simulation     (crate::sim: Config.ofMods, steps, Sim.run)
//! ```
//! Modules: `mods_json` (spec `Sim/ModsJson.lean`), `osr` (`Replay/Osr.lean`), `adapter`
//! (`Eval/Adapter.lean`), `env` (`Eval/Env.lean`); this file is `Eval.lean`.
pub mod adapter;
pub mod env;
pub mod mods_json;
pub mod osr;

use crate::beatmap::decoder;
use crate::beatmap::dotnet::{str_eq, str_eq2, Str};
use crate::beatmap::hit_object_parser::DecodeError;
use crate::beatmap::mod_settings::{get_opt_int, setting_value_beq, ModConfig};
use crate::beatmap::names::K_SEED;
use crate::beatmap::playable::{get_playable_beatmap, PlayableBeatmap};
use crate::beatmap::types::DecodedBeatmap;
use crate::float::F64;
use crate::net::basic::NetExn;
use crate::replay::frames::{self, Frame};
use crate::sim::err::SimErr;
use crate::sim::geometry::Env;
use crate::sim::mods::{config_of_mods, dyn_rate_initial_speed, true_rate, Config, DynRate};
use crate::sim::netx::{F64_NEG_INF, F64_ZERO};
use crate::sim::schedule::{frame_times, gameplay_start_time, reference_end, reference_start, references, simulate_steps, ScheduleKind, Step};
use crate::sim::scoring::{HealthSt, ScoreSt};
use crate::sim::state::JRec;
use crate::sim::step::{mk_ctx, run_with};
use alloc::vec::Vec;
use osr::OsrErr;

/// spec `Schedule` (D9): a reference schedule kind or an explicit reference-time list
#[derive(Clone)]
pub enum Schedule {
    Kind(ScheduleKind),
    Explicit(Vec<F64>),
}

/// spec `Options` (`oracle/Program.cs` `ResolveMods`)
#[derive(Clone)]
pub struct Options {
    /// `--mods`: APIMods (already `ToMod`-decoded)
    pub mods_override: Option<Vec<ModConfig>>,
    /// `--replace-mods`
    pub replace_mods: bool,
    /// `--no-classic`
    pub no_classic: bool,
}

/// `Rejection.stage` (texts in `text::stage`)
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Stage {
    /// "beatmap-decode"
    BeatmapDecode,
    /// "replay-decode"
    ReplayDecode,
    /// "replay-decode (decode-time GetPlayableBeatmap)"
    DecodeTimePlayable,
    /// "mods"
    Mods,
    /// "playable"
    Playable,
    /// "replay-frames"
    ReplayFrames,
    /// "sim"
    Sim,
}

/// `Rejection.reason` (the spec's strings: `toString` of the lifted error, or the literal messages)
#[derive(Clone)]
pub enum Reason {
    /// a beatmap decoder / `GetPlayableBeatmap` error (`toString e`)
    Decode(DecodeError),
    /// `s!"beatmap ruleset {d.rulesetId}: conversion of non-osu! beatmaps is not modelled"`
    OtherRuleset(i32),
    /// an `.osr` decoding error
    Osr(OsrErr),
    /// `s!"unknown mod acronym: {m.acronym}"`
    UnknownMod(Str),
    /// "autoplay-type mods are not supported (they replace the replay)"
    Autoplay,
    /// `s!"{m.acronym} without a seed is not reproducible (lazer uses RNG.Next(); ISSUES G5)"`
    Unseeded(Str),
    /// a frame-parsing exception (`toString` = `repr` of the `NetExn`)
    Frames(NetExn),
    /// a simulation rejection (`Except String` of the Sim)
    Sim(SimErr),
    /// an explicit-schedule contract or step frame-index rejection (spec `explicitRefsCheck` / `stepFramesOk`)
    Schedule(ScheduleErr),
}

/// spec `explicitRefsCheck` / `stepFramesOk` rejections (texts in the shell)
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ScheduleErr {
    /// "explicit schedule is empty"
    Empty,
    /// "explicit schedule: a reference time is not finite"
    NonFinite,
    /// "explicit schedule must be non-decreasing"
    Decreasing,
    /// "schedule: a step's replay frame index passes the last frame (an FSC time of +inf)"
    FrameIndex,
}

/// spec `Rejection`
#[derive(Clone)]
pub struct Rejection {
    pub stage: Stage,
    pub reason: Reason,
}

/// spec `reject`
pub fn reject(stage: Stage, reason: Reason) -> Rejection {
    Rejection { stage, reason }
}

/// spec `SemResult` (per fail semantics)
#[derive(Clone)]
pub struct SemResult {
    pub score: ScoreSt,
    pub health: HealthSt,
}

/// spec `Result` (without the `playable` field, which `evaltest` never prints)
#[derive(Clone)]
pub struct EvalResult {
    pub is_legacy_score: bool,
    pub replay_version: i32,
    pub replay_beatmap_hash: Option<Str>,
    pub decoded_mods: Vec<ModConfig>,
    pub mods: Vec<ModConfig>,
    pub true_gameplay_rate: F64,
    pub hit_objects: usize,
    pub frames: usize,
    /// `scheduleName` (`None` = "explicit")
    pub schedule_kind: Option<ScheduleKind>,
    pub r0: F64,
    pub end_time: F64,
    pub gameplay_start_time: F64,
    pub last_frame_time: Option<F64>,
    pub references: usize,
    pub steps: usize,
    pub step_times: Vec<F64>,
    pub live: SemResult,
    /// `None`: identical to live (the health processor never attempted to fail)
    pub replay_player: Option<SemResult>,
    pub max_stats: [u64; 18],
    /// processor-order judgements
    pub judgements: Vec<JRec>,
    pub score_multiplier: F64,
}

/// part of spec `sameMods`: settings equality (key, then `BEq SettingValue`)
pub fn same_settings(x: &ModConfig, y: &ModConfig) -> bool {
    if x.settings.len() != y.settings.len() {
        false
    } else {
        let mut r = true;
        let mut i = 0;
        while i < x.settings.len() {
            if !(x.settings[i].0 == y.settings[i].0 && setting_value_beq(x.settings[i].1, y.settings[i].1)) {
                r = false;
            }
            i = i + 1;
        }
        r
    }
}

/// part of spec `sameMods`: one pair
pub fn same_mod(x: &ModConfig, y: &ModConfig) -> bool {
    str_eq2(&x.acronym, &y.acronym) && x.known == y.known && same_settings(x, y)
}

/// spec `sameMods` (structural equality of decoded mod lists)
pub fn same_mods(a: &[ModConfig], b: &[ModConfig]) -> bool {
    if a.len() != b.len() {
        false
    } else {
        let mut r = true;
        let mut i = 0;
        while i < a.len() {
            if !same_mod(&a[i], &b[i]) {
                r = false;
            }
            i = i + 1;
        }
        r
    }
}

/// spec `unseededRandom` (Random / Target Practice without a seed; ISSUES G5)
pub fn unseeded_random(m: &ModConfig) -> bool {
    m.known && (str_eq(&m.acronym, b"RD") || str_eq(&m.acronym, b"TP")) && get_opt_int(m, K_SEED).is_none()
}

/// part of spec `evaluate`: `sc.bitfieldMods.filter (!unseededRandom ·)`
pub fn without_unseeded(ms: &[ModConfig]) -> Vec<ModConfig> {
    let mut out: Vec<ModConfig> = Vec::new();
    let mut i = 0;
    while i < ms.len() {
        if !unseeded_random(&ms[i]) {
            out.push(ms[i].clone());
        }
        i = i + 1;
    }
    out
}

/// part of spec `resolveMods`: `mods.filter fun m => !(m.known && m.acronym == "CL")`
pub fn without_classic(ms: Vec<ModConfig>) -> Vec<ModConfig> {
    let mut out: Vec<ModConfig> = Vec::new();
    let mut i = 0;
    while i < ms.len() {
        if !(ms[i].known && str_eq(&ms[i].acronym, b"CL")) {
            out.push(ms[i].clone());
        }
        i = i + 1;
    }
    out
}

/// part of spec `resolveMods`: `mods.filter (·.acronym != m.acronym) ++ [m]`
pub fn replace_or_append(ms: Vec<ModConfig>, m: &ModConfig) -> Vec<ModConfig> {
    let mut out: Vec<ModConfig> = Vec::new();
    let mut i = 0;
    while i < ms.len() {
        if !str_eq2(&ms[i].acronym, &m.acronym) {
            out.push(ms[i].clone());
        }
        i = i + 1;
    }
    out.push(m.clone());
    out
}

/// part of spec `resolveMods`: the `for m in ov` loop
pub fn apply_overrides(ms0: Vec<ModConfig>, ov: &[ModConfig]) -> Result<Vec<ModConfig>, Rejection> {
    let mut ms = ms0;
    let mut err: Option<Str> = None;
    let mut i = 0;
    while err.is_none() && i < ov.len() {
        if !ov[i].known {
            err = Some(ov[i].acronym.clone());
        } else {
            ms = replace_or_append(ms, &ov[i]);
        }
        i = i + 1;
    }
    match err {
        Some(a) => Err(reject(Stage::Mods, Reason::UnknownMod(a))),
        None => Ok(ms),
    }
}

/// part of spec `resolveMods`: `mods.any fun m => m.known && (m.acronym == "AT" || m.acronym == "CN")`
pub fn has_autoplay(ms: &[ModConfig]) -> bool {
    // unconditional accumulator update (Aeneas: a conditional `r = true` here failed with "Could not match the contexts")
    let mut r = false;
    let mut i = 0;
    while i < ms.len() {
        r = r || is_autoplay(&ms[i]);
        i = i + 1;
    }
    r
}

/// part of spec `resolveMods`: `m is ModAutoplay` (`OsuModAutoplay`, `OsuModCinema`)
pub fn is_autoplay(m: &ModConfig) -> bool {
    m.known && (str_eq(&m.acronym, b"AT") || str_eq(&m.acronym, b"CN"))
}

/// spec `resolveMods` (`oracle/Program.cs:194-219`, then the Autoplay check `:234-235`)
pub fn resolve_mods(decoded: &[ModConfig], o: &Options) -> Result<Vec<ModConfig>, Rejection> {
    let ms0: Vec<ModConfig> = if o.replace_mods && o.mods_override.is_some() { Vec::new() } else { decoded.to_vec() };
    let ms1 = if o.no_classic { without_classic(ms0) } else { ms0 };
    let ms2 = match &o.mods_override {
        Some(ov) => tri!(apply_overrides(ms1, ov)),
        None => ms1,
    };
    if has_autoplay(&ms2) {
        Err(reject(Stage::Mods, Reason::Autoplay))
    } else {
        Ok(ms2)
    }
}

/// spec `playableOf` (`getPlayableBeatmap d (mods.map ModConfig.allHooks)`: the Rust beatmap port
/// dispatches the hooks on the acronym)
pub fn playable_of(d: &DecodedBeatmap, mods: &[ModConfig]) -> Result<PlayableBeatmap, DecodeError> {
    get_playable_beatmap(d, mods)
}

/// part of spec `evaluate`: `mods.find? unseededRandom`
pub fn find_unseeded(ms: &[ModConfig]) -> Option<usize> {
    let mut r: Option<usize> = None;
    let mut i = 0;
    while r.is_none() && i < ms.len() {
        if unseeded_random(&ms[i]) {
            r = Some(i);
        }
        i = i + 1;
    }
    r
}

/// part of spec `evaluate`: beatmap decode + ruleset check
pub fn decode_beatmap(beatmap_bytes: &[u8]) -> Result<DecodedBeatmap, Rejection> {
    match decoder::decode(beatmap_bytes) {
        Err(e) => Err(reject(Stage::BeatmapDecode, Reason::Decode(e))),
        Ok(d) => {
            if d.ruleset_id != 0 {
                Err(reject(Stage::BeatmapDecode, Reason::OtherRuleset(d.ruleset_id)))
            } else {
                Ok(d)
            }
        }
    }
}

/// part of spec `evaluate`: `.osr` decode
pub fn decode_osr(osr: &[u8]) -> Result<osr::DecodedScore, Rejection> {
    match osr::decode(osr) {
        Err(e) => Err(reject(Stage::ReplayDecode, Reason::Osr(e))),
        Ok(sc) => Ok(sc),
    }
}

/// part of spec `evaluate`: the decode-time `GetPlayableBeatmap(bitfield mods (+ Classic))`
/// (`LegacyScoreDecoder.cs:94`), skipped when its mods equal the gameplay mods; only its failure
/// is observable
pub fn decode_time_check(d: &DecodedBeatmap, decode_time_mods: &[ModConfig], mods: &[ModConfig]) -> Result<(), Rejection> {
    if same_mods(decode_time_mods, mods) {
        Ok(())
    } else {
        match playable_of(d, decode_time_mods) {
            Err(e) => Err(reject(Stage::DecodeTimePlayable, Reason::Decode(e))),
            Ok(_) => Ok(()),
        }
    }
}

/// part of spec `evaluate`: the gameplay playable (unseeded RD/TP reject first)
pub fn gameplay_playable(d: &DecodedBeatmap, mods: &[ModConfig]) -> Result<PlayableBeatmap, Rejection> {
    match find_unseeded(mods) {
        Some(i) => Err(reject(Stage::Playable, Reason::Unseeded(mods[i].acronym.clone()))),
        None => match playable_of(d, mods) {
            Err(e) => Err(reject(Stage::Playable, Reason::Decode(e))),
            Ok(pb) => Ok(pb),
        },
    }
}

/// part of spec `evaluate`: the frames (`readLegacyReplay`, offset from the beatmap version)
pub fn decode_frames(text: &Option<Str>, beatmap_version: i64) -> Result<Vec<Frame>, Rejection> {
    match text {
        Some(t) => match frames::decode(t, beatmap_version) {
            Err(e) => Err(reject(Stage::ReplayFrames, Reason::Frames(e))),
            Ok(fs) => Ok(fs),
        },
        None => Ok(Vec::new()),
    }
}

/// `liftE "sim"`
pub fn sim_rej(e: SimErr) -> Rejection {
    reject(Stage::Sim, Reason::Sim(e))
}

/// part of spec `evaluate`: `cfg.dynRates.mapM (·.initialSpeed)` (under `netStr`)
pub fn initial_speeds(ds: &[DynRate]) -> Result<Vec<F64>, NetExn> {
    let mut out: Vec<F64> = Vec::new();
    let mut err: Option<NetExn> = None;
    let mut i = 0;
    while err.is_none() && i < ds.len() {
        match dyn_rate_initial_speed(ds[i]) {
            Ok(v) => out.push(v),
            Err(e) => err = Some(e),
        }
        i = i + 1;
    }
    match err {
        Some(e) => Err(e),
        None => Ok(out),
    }
}

/// part of spec `evaluate`: `cfg.trueRate (← netStr (cfg.dynRates.mapM (·.initialSpeed)))`
pub fn true_gameplay_rate(cfg: &Config) -> Result<F64, Rejection> {
    match initial_speeds(&cfg.dyn_rates) {
        Err(e) => Err(sim_rej(SimErr::Net(e))),
        Ok(sp) => Ok(true_rate(cfg, &sp)),
    }
}

/// part of spec `evaluate`: `c.steps.map (·.time)`
pub fn step_times_of(c: &crate::sim::state::Ctx) -> Vec<F64> {
    let mut out: Vec<F64> = Vec::with_capacity(c.steps.len());
    let mut i = 0;
    while i < c.steps.len() {
        out.push(c.steps[i].time);
        i = i + 1;
    }
    out
}

/// spec `explicitRefsCheck` (D80b, D79 N2): non-empty, every reference finite (`r - r == 0`), non-decreasing
pub fn explicit_refs_check(refs: &[F64]) -> Result<(), Rejection> {
    if refs.len() == 0 {
        return Err(reject(Stage::Sim, Reason::Schedule(ScheduleErr::Empty)));
    }
    let mut prev = F64_NEG_INF;
    let mut i: usize = 0;
    while i < refs.len() {
        let r = refs[i];
        if !r.sub(r).eq(F64_ZERO) {
            return Err(reject(Stage::Sim, Reason::Schedule(ScheduleErr::NonFinite)));
        }
        if r.lt(prev) {
            return Err(reject(Stage::Sim, Reason::Schedule(ScheduleErr::Decreasing)));
        }
        prev = r;
        i += 1;
    }
    Ok(())
}

/// spec `stepFramesOk`: every step's frame index lies in `[-1, n_frames)` (D79 N2)
pub fn step_frames_ok(steps: &[Step], n_frames: usize) -> bool {
    let mut i: usize = 0;
    while i < steps.len() {
        let fi = steps[i].frame_index;
        if fi < -1 {
            return false;
        }
        if fi >= 0 && fi as usize >= n_frames {
            return false;
        }
        i += 1;
    }
    true
}

/// part of spec `evaluate`: the context for the schedule (`sched_ctx0`), then the `stepFramesOk` check;
/// returns (refsN, ctx)
pub fn sched_ctx(env: Env, cfg: Config, spb: crate::sim::playable::Playable, fs: Vec<Frame>, sched: &Schedule) -> Result<(usize, crate::sim::state::Ctx), Rejection> {
    let (n, c) = tri!(sched_ctx0(env, cfg, spb, fs, sched));
    if !step_frames_ok(&c.steps, c.frames.len()) {
        return Err(reject(Stage::Sim, Reason::Schedule(ScheduleErr::FrameIndex)));
    }
    Ok((n, c))
}

/// part of spec `evaluate`: the context for the schedule (kind: `references` first, then `mkCtx`;
/// explicit: `explicitRefsCheck`, then `mkCtx … .catchup` with `steps := simulateSteps refs ft gst`); returns (refsN, ctx)
pub fn sched_ctx0(env: Env, cfg: Config, spb: crate::sim::playable::Playable, fs: Vec<Frame>, sched: &Schedule) -> Result<(usize, crate::sim::state::Ctx), Rejection> {
    let ft = frame_times(&fs);
    let gst = gameplay_start_time(&spb);
    let r0 = reference_start(&spb);
    let end_t = reference_end(&spb);
    match sched {
        Schedule::Kind(k) => {
            let refs = match references(*k, r0, end_t, &ft) {
                Ok(r) => r,
                Err(e) => return Err(sim_rej(e)),
            };
            match mk_ctx(env, cfg, spb, fs, *k) {
                Ok(c) => Ok((refs.len(), c)),
                Err(e) => Err(sim_rej(e)),
            }
        }
        Schedule::Explicit(refs) => {
            tri!(explicit_refs_check(refs));
            let mut c0 = match mk_ctx(env, cfg, spb, fs, ScheduleKind::Catchup) {
                Ok(c) => c,
                Err(e) => return Err(sim_rej(e)),
            };
            match simulate_steps(refs, &ft, gst) {
                Ok(st) => {
                    c0.steps = st;
                    Ok((refs.len(), c0))
                }
                Err(e) => Err(sim_rej(e)),
            }
        }
    }
}

/// spec `evaluate` (the end-to-end evaluation; `playableOverride` is a debugging option of the spec
/// and not ported)
pub fn evaluate(env: Env, beatmap_bytes: &[u8], osr_bytes: &[u8], opts: &Options, sched: &Schedule) -> Result<EvalResult, Rejection> {
    let d = tri!(decode_beatmap(beatmap_bytes));
    let sc = tri!(decode_osr(osr_bytes));
    let decode_time_mods = without_unseeded(&sc.bitfield_mods);
    let mods = tri!(resolve_mods(&sc.mods, opts));
    tri!(decode_time_check(&d, &decode_time_mods, &mods));
    let pb = tri!(gameplay_playable(&d, &mods));
    let spb = adapter::to_sim_playable(&pb);
    let fs = tri!(decode_frames(&sc.frame_text, spb.beatmap_version));
    let cfg = config_of_mods(&mods, &spb, !sc.is_legacy_score);
    let gst = gameplay_start_time(&spb);
    let r0 = reference_start(&spb);
    let end_t = reference_end(&spb);
    let hit_objects = spb.objects.len();
    let n_frames = fs.len();
    let (refs_n, c) = tri!(sched_ctx(env, cfg, spb, fs, sched));
    let s = match run_with(&c) {
        Ok(s) => s,
        Err(e) => return Err(sim_rej(e)),
    };
    let rate = tri!(true_gameplay_rate(&c.cfg));
    let replay_player = if s.health.fail_triggers == 0 {
        None
    } else {
        Some(SemResult { score: s.score_rp, health: s.health_rp.clone() })
    };
    let schedule_kind = match sched {
        Schedule::Kind(k) => Some(*k),
        Schedule::Explicit(_) => None,
    };
    Ok(EvalResult {
        is_legacy_score: sc.is_legacy_score,
        replay_version: sc.container.version,
        replay_beatmap_hash: sc.container.beatmap_hash.clone(),
        decoded_mods: sc.mods.clone(),
        mods,
        true_gameplay_rate: rate,
        hit_objects,
        frames: n_frames,
        schedule_kind,
        r0,
        end_time: end_t,
        gameplay_start_time: gst,
        last_frame_time: c.last_frame_time,
        references: refs_n,
        steps: c.steps.len(),
        step_times: step_times_of(&c),
        live: SemResult { score: s.score, health: s.health.clone() },
        replay_player,
        max_stats: c.smax.max_stats,
        judgements: s.out,
        score_multiplier: c.cfg.score_multiplier,
    })
}

/// spec `playableFor` (only the adapter output, for `--dump-playable`; no ruleset or decode-time
/// checks, as in the spec)
pub fn playable_for(beatmap_bytes: &[u8], osr_bytes: &[u8], opts: &Options) -> Result<crate::sim::playable::Playable, Rejection> {
    let d = match decoder::decode(beatmap_bytes) {
        Err(e) => return Err(reject(Stage::BeatmapDecode, Reason::Decode(e))),
        Ok(d) => d,
    };
    let sc = tri!(decode_osr(osr_bytes));
    let mods = tri!(resolve_mods(&sc.mods, opts));
    match playable_of(&d, &mods) {
        Err(e) => Err(reject(Stage::Playable, Reason::Decode(e))),
        Ok(pb) => Ok(adapter::to_sim_playable(&pb)),
    }
}

/// Texts (not translated; excluded from Charon).
pub mod text {
    use super::Stage;
    /// the spec's stage strings
    pub fn stage(s: Stage) -> &'static str {
        match s {
            Stage::BeatmapDecode => "beatmap-decode",
            Stage::ReplayDecode => "replay-decode",
            Stage::DecodeTimePlayable => "replay-decode (decode-time GetPlayableBeatmap)",
            Stage::Mods => "mods",
            Stage::Playable => "playable",
            Stage::ReplayFrames => "replay-frames",
            Stage::Sim => "sim",
        }
    }
}
