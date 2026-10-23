//! Sim-side mod configuration (M5-M7). Spec: `model/OsuModel/Sim/Mods.lean` at Lean commit `7cffd29`
//! (`Config`, `Config.ofMods`, rate aggregation, TimeRamp/AdaptiveSpeed bindables, `scoreMultiplierV2`).
//! Mods are the decoded `APIMod`s of the Beatmap port (`beatmap::mod_settings::ModConfig`, = `Settings.toMod`).
use crate::beatmap::dotnet::str_eq;
use crate::beatmap::mod_settings::{get_bool, get_double, get_float, get_int, get_opt_float, ModConfig};
use crate::beatmap::names::*;
use crate::float::{F32, F64};
use crate::net;
use crate::net::basic::NetExn;
use crate::net::framework::{bd_create, bd_set_max, bd_set_min, bd_set_precision, bd_set_value, BD};
use crate::net::mathops::f64_round_digits;
use crate::net::mathops::f64_clamp;
use crate::sim::playable::{Difficulty, Playable};
use alloc::vec::Vec;

pub const F64_0: F64 = F64::from_bits(0);
pub const F64_ONE: F64 = F64::from_bits(0x3FF0_0000_0000_0000);

/// `AudioProp`
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum AudioProp {
    Frequency,
    Tempo,
}

/// `RateVal`
#[derive(Clone, Copy)]
pub enum RateVal {
    Const(F64),
    /// `SpeedChange` of the k-th time-varying rate mod
    Dyn(usize),
}

/// a rate source `(AudioProp × RateVal)`
#[derive(Clone, Copy)]
pub struct RateSource {
    pub prop: AudioProp,
    pub val: RateVal,
}

/// `DynRate`
#[derive(Clone, Copy)]
pub enum DynRate {
    /// `timeRamp initial final begin finalTime`
    TimeRamp(F64, F64, F64, F64),
    Adaptive(F64),
}

/// `FailOverride`
#[derive(Clone, Copy)]
pub enum FailOverride {
    Veto,
    Easy(usize),
    Allow,
}

/// `FailCond`
#[derive(Clone, Copy)]
pub enum FailCond {
    SuddenDeath(bool),
    Perfect,
    TargetPractice,
}

/// `RateMod`
#[derive(Clone, Copy)]
pub enum RateMod {
    Speed(F64),
    TimeRamp(F64, F64, F64, F64),
    Adaptive(F64),
}

/// `Updatable`
#[derive(Clone, Copy)]
pub enum Updatable {
    DynRate(usize),
    Depth,
    Magnetised,
    Repel,
    BarrelRoll,
    Relax,
    Autopilot,
    InputBlock(usize),
}

/// `VisMod` (`ApplyCustomUpdateState` handlers of drawable-transform mods, mod order)
#[derive(Clone, Copy)]
pub enum VisMod {
    ScaleTween(F32),
    SpinIn,
    Transform,
    Wiggle(F64),
    TargetPractice,
    Hidden(bool),
    Inert,
    ClassicEarlyFade,
}

/// `VisMod.skipsSpinners`
pub fn vis_mod_skips_spinners(v: VisMod) -> bool {
    match v {
        VisMod::Hidden(_) => true,
        _ => false,
    }
}

/// `PolicyKind`
#[derive(Clone, Copy)]
pub enum PolicyKind {
    StartTimeOrdered,
    Legacy(F64),
}

/// an AC entry `(MinimumAccuracy, AccuracyJudgeMode == Standard)`
#[derive(Clone, Copy)]
pub struct AccChallenge {
    pub min_acc: F64,
    pub standard: bool,
}

/// `Config` (the spec's `mods : List String` field is not read by the simulation and is omitted)
#[derive(Clone)]
pub struct Config {
    pub policy: PolicyKind,
    pub classic_head_block: bool,
    pub legacy_health: bool,
    pub fail_overrides: Vec<FailOverride>,
    pub easy_retries: Vec<u64>,
    pub fail_conds: Vec<FailCond>,
    pub acc_challenges: Vec<AccChallenge>,
    pub rank_adjust: bool,
    pub rate_sources: Vec<RateSource>,
    pub dyn_rates: Vec<DynRate>,
    pub score_multiplier: F64,
    pub updatables: Vec<Updatable>,
    pub input_blockers: Vec<bool>,
    pub spun_out: bool,
    pub strict_tracking: bool,
    pub lazer_replay: bool,
    pub rate_mods: Vec<RateMod>,
    pub vis_mods: Vec<VisMod>,
    pub depth_max: F32,
    pub magnet_strength: F32,
    pub repel_strength: F32,
    /// BarrelRoll: (`SpinSpeed`, `Direction == Counterclockwise`)
    pub barrel_roll: Option<(F64, bool)>,
}

// ------------------------------------------------------------------------------------------- Rate

/// `aggregate` over the sources of one property: `initial(1) * own(1) * v1 * v2 …`
pub fn aggregate(c: &Config, speed: &[F64], prop: AudioProp) -> F64 {
    let mut acc = F64_ONE.mul(F64_ONE);
    let mut i: usize = 0;
    while i < c.rate_sources.len() {
        let src = c.rate_sources[i];
        if src.prop == prop {
            let v = match src.val {
                RateVal::Const(x) => x,
                RateVal::Dyn(k) => speed[k],
            };
            acc = acc.mul(v);
        }
        i += 1;
    }
    acc
}

/// `Config.trueRate`
pub fn true_rate(c: &Config, speed: &[F64]) -> F64 {
    let f = aggregate(c, speed, AudioProp::Frequency);
    let t = aggregate(c, speed, AudioProp::Tempo);
    F64_ONE.mul(f).mul(t)
}

/// `default : BD`
pub const BD_DEFAULT: BD = BD { value: F64_0, min_v: F64_0, max_v: F64_0, prec: F64_0 };

/// `timeRampBindable` (`new BindableDouble(1) { Precision = 0.01 }`)
pub fn time_ramp_bindable() -> Result<BD, NetExn> {
    let s = bd_create(F64_ONE)?;
    bd_set_precision(s, F64::from_bits(0x3F847AE147AE147B) /* 0.01 */)
}

/// `adaptiveBindable` (`new BindableDouble(1) { MinValue = 0.4, MaxValue = 2.5 }`)
pub fn adaptive_bindable() -> Result<BD, NetExn> {
    let s = bd_create(F64_ONE)?;
    let s2 = bd_set_min(s, F64::from_bits(0x3FD999999999999A) /* 0.4 */)?;
    bd_set_max(s2, F64::from_bits(0x4004000000000000) /* 2.5 */)
}

/// `timeRampRate`
pub fn time_ramp_rate(initial: F64, fin: F64, begin: F64, final_time: F64, time: F64) -> Result<F64, NetExn> {
    let amount = time.sub(begin).div(net::max(F64_ONE, final_time.sub(begin)));
    let ramp = initial.add(fin.sub(initial).mul(f64_clamp(amount, F64_0, F64_ONE)?));
    Ok(F64_ONE.mul(f64_round_digits(ramp, 2)?))
}

/// `DynRate.setSpeed`
pub fn dyn_rate_set_speed(d: DynRate, old: F64, v: F64) -> Result<F64, NetExn> {
    let b = match d {
        DynRate::TimeRamp(_, _, _, _) => time_ramp_bindable()?,
        DynRate::Adaptive(_) => adaptive_bindable()?,
    };
    let bo = BD { value: old, min_v: b.min_v, max_v: b.max_v, prec: b.prec };
    Ok(bd_set_value(bo, v)?.value)
}

/// `DynRate.initialSpeed`
pub fn dyn_rate_initial_speed(d: DynRate) -> Result<F64, NetExn> {
    match d {
        DynRate::TimeRamp(i, f, b, ft) => {
            let r = time_ramp_rate(i, f, b, ft, crate::sim::netx::F64_POS_INF)?;
            dyn_rate_set_speed(d, F64_ONE, r)
        }
        DynRate::Adaptive(i) => dyn_rate_set_speed(d, F64_ONE, i),
    }
}

// ------------------------------------------------------------------------------- Score multiplier

/// `htMultiplier`
pub fn ht_multiplier(s: F64) -> F64 {
    F64::from_i64(s.mul(F64::from_bits(0x4034000000000000) /* 20 */).to_i32_sat() as i64).div(F64::from_bits(0x4034000000000000) /* 20.0 */).mul(F64::from_bits(0x3FF6666666666666) /* 1.4 */).sub(F64::from_bits(0x3FE0000000000000) /* 0.5 */)
}

/// `dtMultiplier`
pub fn dt_multiplier(s: F64) -> F64 {
    let v = F64::from_i64(s.mul(F64::from_bits(0x4024000000000000) /* 10 */).to_i32_sat() as i64).div(F64::from_bits(0x4024000000000000) /* 10.0 */);
    let penalty = if !v.eq(F64::from_bits(0x3FF8000000000000) /* 1.5 */) && !v.eq(F64::from_bits(0x3FF0000000000000) /* 1.0 */) { F64::from_bits(0x3F847AE147AE147B) /* 0.01 */ } else { F64::from_bits(0x0000000000000000) /* 0.0 */ };
    v.sub(F64_ONE).mul(F64::from_bits(0x3FDD70A3D70A3D71) /* 0.46 */).add(F64_ONE).sub(penalty)
}

/// `hdMultiplier`
pub fn hd_multiplier(m: &ModConfig, other_timing: bool) -> F64 {
    let mut v = F64::from_bits(0x3FF0A3D70A3D70A4) /* 1.04 */;
    if get_bool(m, K_ONLY_FADE_APPROACH_CIRCLES) {
        v = v.sub(F64::from_bits(0x3F947AE147AE147B) /* 0.02 */);
    }
    if other_timing {
        v = v.sub(F64::from_bits(0x3F947AE147AE147B) /* 0.02 */);
    }
    v
}

pub const F32_ONE: F32 = F32::from_bits(0x3F80_0000);
pub const F32_TWO: F32 = F32::from_bits(0x4000_0000);

/// `flMultiplier`
pub fn fl_multiplier(m: &ModConfig) -> F64 {
    let size = get_float(m, K_SIZE_MULTIPLIER);
    let v = net::max(F64::from_bits(0x3FF051EB851EB852) /* 1.02 */, net::min(F64::from_bits(0x3FF3333333333333) /* 1.2 */, F64::from_bits(0x3FF3333333333333) /* 1.2 */.sub(F64::from_bits(0x3FC999999999999A) /* 0.2 */.mul(size.sub(F32_ONE).to_f64()))));
    if !get_bool(m, K_COMBO_BASED_SIZE) { F64_ONE.add(v.sub(F64_ONE).div(F64::from_bits(0x4014000000000000) /* 5 */)) } else { v }
}

/// `dfMultiplier`
pub fn df_multiplier(m: &ModConfig) -> F64 {
    F64::from_bits(0x3FF0000000000000) /* 1.0 */.sub(net::max(F64_0, F64::from_bits(0x3F947AE147AE147B) /* 0.02 */.mul(get_float(m, K_START_SCALE).sub(F32_TWO).to_f64())))
}

/// `ezMultiplier`
pub fn ez_multiplier(m: &ModConfig) -> F64 {
    let v = F64::from_bits(0x3FE999999999999A) /* 0.8 */.sub(net::max(F64_0, F64::from_bits(0x3FB999999999999A) /* 0.1 */.mul(F64::from_i64(get_int(m, K_RETRIES).wrapping_sub(2) as i64))));
    net::max(F64::from_bits(0x3FD999999999999A) /* 0.4 */, v)
}

/// the `sel` of `daMultiplier`
pub fn da_sel(m: &ModConfig, key: u32, b: F32) -> F64 {
    match get_opt_float(m, key) {
        Some(x) => x.to_f64(),
        None => b.to_f64(),
    }
}

/// `daMultiplier`
pub fn da_multiplier(m: &ModConfig, base: &Difficulty) -> F64 {
    let cs = da_sel(m, K_CIRCLE_SIZE, base.cs).sub(base.cs.to_f64()).abs();
    let hp = da_sel(m, K_DRAIN_RATE, base.hp).sub(base.hp.to_f64()).abs();
    let od = da_sel(m, K_OVERALL_DIFFICULTY, base.od).sub(base.od.to_f64()).abs();
    let ar = da_sel(m, K_APPROACH_RATE, base.ar).sub(base.ar.to_f64()).abs();
    let mc = net::max(F64::from_bits(0x3FB999999999999A) /* 0.1 */, F64::from_bits(0x3FF0000000000000) /* 1.0 */.sub(cs.mul(F64::from_bits(0x3FE0000000000000) /* 0.5 */)));
    let mh = net::max(F64::from_bits(0x3FB999999999999A) /* 0.1 */, F64::from_bits(0x3FF0000000000000) /* 1.0 */.sub(hp.mul(F64::from_bits(0x3FE0000000000000) /* 0.5 */)));
    let mo = net::max(F64::from_bits(0x3FB999999999999A) /* 0.1 */, F64::from_bits(0x3FF0000000000000) /* 1.0 */.sub(od.mul(F64::from_bits(0x3FE0000000000000) /* 0.5 */)));
    let ma = net::max(F64::from_bits(0x3FB999999999999A) /* 0.1 */, F64::from_bits(0x3FF0000000000000) /* 1.0 */.sub(ar.mul(F64::from_bits(0x3FE0000000000000) /* 0.5 */)));
    net::max(F64::from_bits(0x3FB999999999999A) /* 0.1 */, mc.mul(mh).mul(mo).mul(ma))
}

/// the `mult` of `trMultiplier`
pub fn tr_mult(x: F64) -> F64 {
    if x.lt(F64_ONE) { ht_multiplier(x) } else { dt_multiplier(x) }
}

/// `trMultiplier`
pub fn tr_multiplier(m: &ModConfig) -> F64 {
    let i = get_double(m, K_INITIAL_RATE);
    let f = get_double(m, K_FINAL_RATE);
    let mn = net::min(i, f);
    let mx = net::max(i, f);
    F64::from_bits(0x3FE999999999999A) /* 0.8 */.mul(tr_mult(mn)).add(F64::from_bits(0x3FC999999999999A) /* 0.2 */.mul(tr_mult(mx)))
}

/// acronym test
pub fn acr_is(m: &ModConfig, a: &[u8]) -> bool {
    str_eq(&m.acronym, a)
}

/// `singleMultiplier`
pub fn single_multiplier(m: &ModConfig, base: &Difficulty) -> Option<F64> {
    if acr_is(m, b"EZ") {
        Some(ez_multiplier(m))
    } else if acr_is(m, b"NF") {
        Some(F64::from_bits(0x3FE0000000000000) /* 0.5 */)
    } else if acr_is(m, b"HT") || acr_is(m, b"DC") {
        Some(ht_multiplier(get_double(m, K_SPEED_CHANGE)))
    } else if acr_is(m, b"HR") {
        Some(F64::from_bits(0x3FF170A3D70A3D71) /* 1.09 */)
    } else if acr_is(m, b"DT") || acr_is(m, b"NC") {
        Some(dt_multiplier(get_double(m, K_SPEED_CHANGE)))
    } else if acr_is(m, b"HD") {
        Some(hd_multiplier(m, false))
    } else if acr_is(m, b"TC") {
        Some(F64::from_bits(0x3FF051EB851EB852) /* 1.02 */)
    } else if acr_is(m, b"FL") {
        Some(fl_multiplier(m))
    } else if acr_is(m, b"BL") {
        Some(F64::from_bits(0x3FF3D70A3D70A3D7) /* 1.24 */)
    } else if acr_is(m, b"TP") {
        Some(F64::from_bits(0x3F847AE147AE147B) /* 0.01 */)
    } else if acr_is(m, b"DA") {
        Some(da_multiplier(m, base))
    } else if acr_is(m, b"CL") {
        if get_bool(m, K_CLASSIC_NOTE_LOCK) { Some(F64::from_bits(0x3FEF851EB851EB85) /* 0.985 */) } else { Some(F64::from_bits(0x3FEEB851EB851EB8) /* 0.96 */) }
    } else if acr_is(m, b"RD") {
        Some(F64::from_bits(0x3FE6666666666666) /* 0.7 */)
    } else if acr_is(m, b"RX") || acr_is(m, b"AP") {
        Some(F64::from_bits(0x3FB999999999999A) /* 0.1 */)
    } else if acr_is(m, b"SO") {
        Some(F64::from_bits(0x3FEE666666666666) /* 0.95 */)
    } else if acr_is(m, b"DF") {
        Some(df_multiplier(m))
    } else if acr_is(m, b"WU") || acr_is(m, b"WD") {
        Some(tr_multiplier(m))
    } else if acr_is(m, b"AD") {
        Some(F64::from_bits(0x3FE6666666666666) /* 0.7 */)
    } else if acr_is(m, b"MG") {
        Some(F64::from_bits(0x3FE6666666666666) /* 0.7 */.sub(get_float(m, K_ATTRACTION_STRENGTH).to_f64().mul(F64::from_bits(0x3FE3333333333333) /* 0.6 */)))
    } else if acr_is(m, b"AS") {
        Some(F64::from_bits(0x3FB999999999999A) /* 0.1 */)
    } else if acr_is(m, b"SY") {
        Some(F64::from_bits(0x3FEFAE147AE147AE) /* 0.99 */)
    } else {
        None
    }
}

/// one entry `(a, b, f)` of `combinations` (index `k` selects `f`, `combo_multiplier`): if both acronyms are still
/// remaining, multiply and remove them (`scoreMultiplierV2`'s loop body)
pub fn apply_combo(k: usize, a: &[u8], b: &[u8], by_type: &[ModConfig], remaining: &mut Vec<bool>, r: F64) -> F64 {
    if rem_contains(remaining, by_type, a) && rem_contains(remaining, by_type, b) {
        match (find_by_lit(by_type, a), find_by_lit(by_type, b)) {
            (Some(ia), Some(ib)) => {
                let r2 = r.mul(combo_multiplier(k, &by_type[ia], &by_type[ib]));
                remaining[ia] = false;
                remaining[ib] = false;
                r2
            }
            _ => r,
        }
    } else {
        r
    }
}

/// the multiplier function of the k-th `combinations` entry
pub fn combo_multiplier(k: usize, ma: &ModConfig, mb: &ModConfig) -> F64 {
    if k == 0 || k == 6 {
        F64::from_bits(0x3FF3D70A3D70A3D7) /* 1.24 */
    } else if k == 3 {
        hd_multiplier(ma, true).mul(df_multiplier(mb))
    } else if k == 7 {
        F64_ONE.add(fl_multiplier(ma).sub(F64_ONE).div(F64::from_bits(0x4000000000000000) /* 2 */))
    } else {
        hd_multiplier(ma, true)
    }
}

/// `m.acronym == a`
pub fn acr_eq(m: &ModConfig, a: &[u32]) -> bool {
    crate::beatmap::dotnet::str_eq2(&m.acronym, a)
}

/// is a mod of `m`'s acronym already in `by_type`
pub fn by_type_has(by_type: &[ModConfig], m: &ModConfig) -> bool {
    find_by_acr(by_type, &m.acronym).is_some()
}

/// `byType.find? (·.acronym == a)` (index)
pub fn find_by_acr(by_type: &[ModConfig], a: &[u32]) -> Option<usize> {
    let mut i: usize = 0;
    let mut r: Option<usize> = None;
    while i < by_type.len() && r.is_none() {
        if acr_eq(&by_type[i], a) {
            r = Some(i);
        }
        i += 1;
    }
    r
}

/// `byType.find? (·.acronym == lit)` (index)
pub fn find_by_lit(by_type: &[ModConfig], a: &[u8]) -> Option<usize> {
    let mut i: usize = 0;
    let mut r: Option<usize> = None;
    while i < by_type.len() && r.is_none() {
        if acr_is(&by_type[i], a) {
            r = Some(i);
        }
        i += 1;
    }
    r
}

/// `remaining.contains lit`
pub fn rem_contains(rem: &[bool], by_type: &[ModConfig], a: &[u8]) -> bool {
    match find_by_lit(by_type, a) {
        Some(i) => rem[i],
        None => false,
    }
}

/// `scoreMultiplierV2`. `remaining` is kept as a flag per `byType` entry (its order is `byType`'s, and only
/// removals happen, so iterating the flags in order is the spec's iteration of `remaining`).
pub fn score_multiplier_v2(mods: &[ModConfig], base: &Difficulty) -> F64 {
    let mut by_type: Vec<ModConfig> = Vec::new();
    let mut unknown: usize = 0;
    let mut i: usize = 0;
    while i < mods.len() {
        if mods[i].known {
            if !by_type_has(&by_type, &mods[i]) {
                by_type.push(mods[i].clone());
            }
        } else {
            unknown += 1;
        }
        i += 1;
    }
    let count = by_type.len() + unknown;
    if count == 0 {
        F64_ONE
    } else {
        let mut remaining: Vec<bool> = Vec::new();
        let mut k: usize = 0;
        while k < by_type.len() {
            remaining.push(true);
            k += 1;
        }
        let mut r = F64_ONE;
        if count > 1 {
            // `combinations` in registration order (unrolled: a constant table of byte-string pairs does not
            // translate through Aeneas)
            r = apply_combo(0, b"HD", b"BL", &by_type, &mut remaining, r);
            r = apply_combo(1, b"HD", b"WG", &by_type, &mut remaining, r);
            r = apply_combo(2, b"HD", b"GR", &by_type, &mut remaining, r);
            r = apply_combo(3, b"HD", b"DF", &by_type, &mut remaining, r);
            r = apply_combo(4, b"HD", b"RP", &by_type, &mut remaining, r);
            r = apply_combo(5, b"HD", b"DP", &by_type, &mut remaining, r);
            r = apply_combo(6, b"TC", b"BL", &by_type, &mut remaining, r);
            r = apply_combo(7, b"FL", b"FR", &by_type, &mut remaining, r);
        }
        let mut t: usize = 0;
        while t < by_type.len() {
            if remaining[t] {
                match single_multiplier(&by_type[t], base) {
                    Some(v) => {
                        r = r.mul(v);
                    }
                    None => {}
                }
            }
            t += 1;
        }
        r
    }
}

// ------------------------------------------------------------------------------- Building the config

/// `linqMax` (`Enumerable.Max`, NaN propagates); `xs` non-empty
pub fn linq_max(xs: &[F64]) -> F64 {
    let mut v = xs[0];
    let mut done = v.is_nan();
    let mut i: usize = 1;
    while i < xs.len() && !done {
        let x = xs[i];
        if v.lt(x) {
            v = x;
        } else if x.is_nan() {
            v = x;
            done = true;
        }
        i += 1;
    }
    v
}

/// `timeRampTimes`: (begin, finalRateTime)
pub fn time_ramp_times(pb: &Playable) -> (F64, F64) {
    let n = pb.objects.len();
    let first = if n > 0 { pb.objects[0].h.start } else { F64_0 };
    let last_end = if n > 0 {
        let mut ends: Vec<F64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            ends.push(pb.objects[i].h.end_time);
            i += 1;
        }
        linq_max(&ends)
    } else {
        F64_0
    };
    (first, first.add(F64::from_bits(0x3FE8000000000000) /* 0.75 */.mul(last_end.sub(first))))
}

/// `LegacyHitPolicy` range `400 - (AP ? 200 : 0)`
pub fn legacy_range(has_ap: bool) -> F64 {
    F64::from_bits(0x4079000000000000) /* 400 */.sub(if has_ap { F64::from_bits(0x4069000000000000) /* 200 */ } else { F64_0 })
}

/// audio property of a rate mod (`adjust_pitch` → Frequency)
pub fn pitch_prop(m: &ModConfig) -> AudioProp {
    if get_bool(m, K_ADJUST_PITCH) { AudioProp::Frequency } else { AudioProp::Tempo }
}

/// the per-mod step of `Config.ofMods`' loop
pub fn config_add_mod(c: &mut Config, m: &ModConfig, has_ap: bool, hidden_fading: bool, rb: F64, rf: F64) {
    if acr_is(m, b"CL") {
        if get_bool(m, K_CLASSIC_NOTE_LOCK) {
            c.policy = PolicyKind::Legacy(legacy_range(has_ap));
            c.classic_head_block = true;
        }
        if get_bool(m, K_FADE_HIT_CIRCLE_EARLY) && !hidden_fading {
            c.vis_mods.push(VisMod::ClassicEarlyFade);
        }
    } else if acr_is(m, b"NF") || acr_is(m, b"CN") {
        c.fail_overrides.push(FailOverride::Veto);
    } else if acr_is(m, b"EZ") {
        c.fail_overrides.push(FailOverride::Easy(c.easy_retries.len()));
        let r = get_int(m, K_RETRIES);
        c.easy_retries.push(if r < 0 { 0 } else { r as u64 });
    } else if acr_is(m, b"SD") {
        c.fail_overrides.push(FailOverride::Allow);
        c.fail_conds.push(FailCond::SuddenDeath(get_bool(m, K_FAIL_ON_SLIDER_TAIL)));
    } else if acr_is(m, b"PF") {
        c.fail_overrides.push(FailOverride::Allow);
        c.fail_conds.push(FailCond::Perfect);
    } else if acr_is(m, b"AC") {
        c.fail_overrides.push(FailOverride::Allow);
        c.acc_challenges.push(AccChallenge {
            min_acc: get_double(m, K_MINIMUM_ACCURACY),
            standard: get_int(m, K_ACCURACY_JUDGE_MODE) == 1,
        });
    } else if acr_is(m, b"TP") {
        c.fail_conds.push(FailCond::TargetPractice);
        c.vis_mods.push(VisMod::TargetPractice);
    } else if acr_is(m, b"HD") {
        c.rank_adjust = true;
        c.vis_mods.push(VisMod::Hidden(get_bool(m, K_ONLY_FADE_APPROACH_CIRCLES)));
    } else if acr_is(m, b"FL") {
        c.rank_adjust = true;
    } else {
        config_add_mod_b(c, m, rb, rf);
    }
}

/// Second part of the acronym `if` chain of `config_add_mod` (rate and input mods). The chain is split into three
/// fns because the Lean elaborator fails on the Aeneas translation of one 28-branch nested `if`.
pub fn config_add_mod_b(c: &mut Config, m: &ModConfig, rb: F64, rf: F64) {
    if acr_is(m, b"HT") || acr_is(m, b"DT") {
        let s = get_double(m, K_SPEED_CHANGE);
        c.rate_sources.push(RateSource { prop: pitch_prop(m), val: RateVal::Const(s) });
        c.rate_mods.push(RateMod::Speed(s));
    } else if acr_is(m, b"NC") || acr_is(m, b"DC") {
        let d = if acr_is(m, b"NC") { F64::from_bits(0x3FF8000000000000) /* 1.5 */ } else { F64::from_bits(0x3FE8000000000000) /* 0.75 */ };
        let s = get_double(m, K_SPEED_CHANGE);
        c.rate_sources.push(RateSource { prop: AudioProp::Frequency, val: RateVal::Const(d) });
        c.rate_sources.push(RateSource { prop: AudioProp::Tempo, val: RateVal::Const(s.div(d)) });
        c.rate_mods.push(RateMod::Speed(s));
    } else if acr_is(m, b"WU") || acr_is(m, b"WD") {
        let k = c.dyn_rates.len();
        let i = get_double(m, K_INITIAL_RATE);
        let f = get_double(m, K_FINAL_RATE);
        c.rate_sources.push(RateSource { prop: pitch_prop(m), val: RateVal::Dyn(k) });
        c.updatables.push(Updatable::DynRate(k));
        c.rate_mods.push(RateMod::TimeRamp(i, f, rb, rf));
        c.dyn_rates.push(DynRate::TimeRamp(i, f, rb, rf));
    } else if acr_is(m, b"AS") {
        let k = c.dyn_rates.len();
        let i = get_double(m, K_INITIAL_RATE);
        c.rate_sources.push(RateSource { prop: pitch_prop(m), val: RateVal::Dyn(k) });
        c.updatables.push(Updatable::DynRate(k));
        c.rate_mods.push(RateMod::Adaptive(i));
        c.dyn_rates.push(DynRate::Adaptive(i));
    } else if acr_is(m, b"RX") {
        c.updatables.push(Updatable::Relax);
    } else if acr_is(m, b"AP") {
        c.updatables.push(Updatable::Autopilot);
    } else if acr_is(m, b"AL") || acr_is(m, b"SG") {
        c.updatables.push(Updatable::InputBlock(c.input_blockers.len()));
        c.input_blockers.push(acr_is(m, b"AL"));
    } else if acr_is(m, b"SO") {
        c.spun_out = true;
    } else {
        config_add_mod_c(c, m);
    }
}

/// Third part of the acronym `if` chain of `config_add_mod` (visual / geometry mods, ST).
pub fn config_add_mod_c(c: &mut Config, m: &ModConfig) {
    if acr_is(m, b"GR") || acr_is(m, b"DF") {
        c.vis_mods.push(VisMod::ScaleTween(get_float(m, K_START_SCALE)));
    } else if acr_is(m, b"SI") {
        c.vis_mods.push(VisMod::SpinIn);
    } else if acr_is(m, b"TR") {
        c.vis_mods.push(VisMod::Transform);
    } else if acr_is(m, b"WG") {
        c.vis_mods.push(VisMod::Wiggle(get_double(m, K_STRENGTH)));
    } else if acr_is(m, b"TC") || acr_is(m, b"AD") {
        c.vis_mods.push(VisMod::Inert);
    } else if acr_is(m, b"DP") {
        c.vis_mods.push(VisMod::Inert);
        c.updatables.push(Updatable::Depth);
        c.depth_max = get_float(m, K_MAX_DEPTH);
    } else if acr_is(m, b"BR") {
        c.updatables.push(Updatable::BarrelRoll);
        c.barrel_roll = Some((get_double(m, K_SPIN_SPEED), get_int(m, K_DIRECTION) == 1));
    } else if acr_is(m, b"MG") {
        c.updatables.push(Updatable::Magnetised);
        c.magnet_strength = get_float(m, K_ATTRACTION_STRENGTH);
    } else if acr_is(m, b"RP") {
        c.updatables.push(Updatable::Repel);
        c.repel_strength = get_float(m, K_REPULSION_STRENGTH);
    } else if acr_is(m, b"ST") {
        c.strict_tracking = true;
    }
}

/// `Config.ofMods` (with `lazerReplay` set as simtest does: `{ Config.ofMods modList pb with lazerReplay }`)
pub fn config_of_mods(mods: &[ModConfig], pb: &Playable, lazer_replay: bool) -> Config {
    let mut c = Config {
        policy: PolicyKind::StartTimeOrdered,
        classic_head_block: false,
        legacy_health: false,
        fail_overrides: Vec::new(),
        easy_retries: Vec::new(),
        fail_conds: Vec::new(),
        acc_challenges: Vec::new(),
        rank_adjust: false,
        rate_sources: Vec::new(),
        dyn_rates: Vec::new(),
        score_multiplier: score_multiplier_v2(mods, &pb.base_difficulty),
        updatables: Vec::new(),
        input_blockers: Vec::new(),
        spun_out: false,
        strict_tracking: false,
        lazer_replay,
        rate_mods: Vec::new(),
        vis_mods: Vec::new(),
        depth_max: F32::from_bits(0x42C8_0000),      // 100
        magnet_strength: F32::from_bits(0x3F00_0000), // 0.5
        repel_strength: F32::from_bits(0x3F00_0000),  // 0.5
        barrel_roll: None,
    };
    let mut has_ap = false;
    let mut i: usize = 0;
    while i < mods.len() {
        if mods[i].known && acr_is(&mods[i], b"AP") {
            has_ap = true;
        }
        i += 1;
    }
    // first IApplicableHealthProcessor (only CL)
    let mut j: usize = 0;
    let mut found = false;
    while j < mods.len() && !found {
        if mods[j].known && acr_is(&mods[j], b"CL") {
            c.legacy_health = get_bool(&mods[j], K_CLASSIC_HEALTH);
            found = true;
        }
        j += 1;
    }
    // `usingHiddenFading`: the first (known) HD has `OnlyFadeApproachCircles == false`
    let mut hidden_fading = false;
    let mut q: usize = 0;
    let mut hd_found = false;
    while q < mods.len() && !hd_found {
        if mods[q].known && acr_is(&mods[q], b"HD") {
            hidden_fading = !get_bool(&mods[q], K_ONLY_FADE_APPROACH_CIRCLES);
            hd_found = true;
        }
        q += 1;
    }
    let (rb, rf) = time_ramp_times(pb);
    let mut k: usize = 0;
    while k < mods.len() {
        if mods[k].known {
            config_add_mod(&mut c, &mods[k], has_ap, hidden_fading, rb, rf);
        }
        k += 1;
    }
    c
}
