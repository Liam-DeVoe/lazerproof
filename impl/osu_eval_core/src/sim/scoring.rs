//! Score and health processors (M4). Spec: `model/OsuModel/Sim/Scoring.lean`.
use crate::float::F64;
use crate::net;
use crate::sim::basic::*;
use crate::sim::err::{Internal, SimErr};
use crate::sim::netx::{self, f64_clamp_or, f64_round};
use crate::sim::playable::{Kind, Period, Playable};
use alloc::vec::Vec;

pub const F64_0: F64 = F64::from_bits(0);
pub const F64_1: F64 = F64::from_bits(0x3FF0_0000_0000_0000);
pub const F64_5: F64 = F64::from_bits(0x4014_0000_0000_0000);

/// `difficultyRange`
pub fn difficulty_range(d: F64, mn: F64, mid: F64, mx: F64) -> F64 {
    if F64_5.lt(d) {
        mid.add(mx.sub(mid).mul(d.sub(F64_5).div(F64_5)))
    } else if d.lt(F64_5) {
        mid.add(mid.sub(mn).mul(d.sub(F64_5).div(F64_5)))
    } else {
        mid
    }
}

/// `baseScore`
pub fn base_score(r: HitResult) -> u64 {
    match r {
        HitResult::SmallTickHit => 10,
        HitResult::LargeTickHit => 30,
        HitResult::SliderTailHit => 150,
        HitResult::Meh => 50,
        HitResult::Ok_ => 100,
        HitResult::Good => 200,
        HitResult::Great | HitResult::Perfect => 300,
        HitResult::SmallBonus => 10,
        HitResult::LargeBonus => 50,
        _ => 0,
    }
}

/// `JInfo`
#[derive(Clone, Copy)]
pub struct JInfo {
    pub kind: Kind,
    pub max_result: HitResult,
    pub min_result: HitResult,
    pub ty: HitResult,
    pub time_absolute: F64,
    pub end_time: F64,
    pub time_offset: F64,
    pub new_combo: bool,
    pub last_in_combo: bool,
}

/// `Rank`
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Rank {
    D,
    C,
    B,
    A,
    S,
    SH,
    X,
    XH,
    F,
}

/// `ScoreSt` (statistics indexed by `hr_index`)
#[derive(Clone, Copy)]
pub struct ScoreSt {
    pub combo: u64,
    pub highest_combo: u64,
    pub stats: [u64; HIT_RESULT_COUNT],
    pub current_maximum_base_score: F64,
    pub current_base_score: F64,
    pub current_accuracy_judgement_count: u64,
    pub current_combo_portion: F64,
    pub current_bonus_portion: F64,
    pub accuracy: F64,
    pub total_score_without_mods: i64,
    pub total_score: i64,
    pub judged_hits: u64,
    pub last_time_absolute: Option<F64>,
    pub has_completed: bool,
    pub maximum_accuracy: F64,
    pub rank: Rank,
}

/// `{} : ScoreSt`
pub const SCORE_ST_INIT: ScoreSt = ScoreSt {
    combo: 0,
    highest_combo: 0,
    stats: [0; HIT_RESULT_COUNT],
    current_maximum_base_score: F64_0,
    current_base_score: F64_0,
    current_accuracy_judgement_count: 0,
    current_combo_portion: F64_0,
    current_bonus_portion: F64_0,
    accuracy: F64_1,
    total_score_without_mods: 0,
    total_score: 0,
    judged_hits: 0,
    last_time_absolute: None,
    has_completed: false,
    maximum_accuracy: F64_1,
    rank: Rank::X,
};

/// `ScoreMax`
#[derive(Clone, Copy)]
pub struct ScoreMax {
    pub maximum_base_score: F64,
    pub maximum_combo_portion: F64,
    pub maximum_accuracy_judgement_count: u64,
    pub max_stats: [u64; HIT_RESULT_COUNT],
    pub max_hits: u64,
    pub score_multiplier: F64,
    pub rank_adjust: bool,
    /// `TotalScoreWithoutMods` after `ApplyBeatmap` (spec `initWithoutMods`, D80a)
    pub init_without_mods: i64,
}

/// `clamp01`
pub fn clamp01(x: F64) -> F64 {
    f64_clamp_or(x, F64_0, F64_1)
}

/// `rankFromScore`
pub fn rank_from_score(acc: F64, stats: &[u64; HIT_RESULT_COUNT]) -> Rank {
    let r = if acc.eq(F64_1) {
        Rank::X
    } else if F64::from_bits(0x3FEE666666666666) /* 0.95 */.le(acc) {
        Rank::S
    } else if F64::from_bits(0x3FECCCCCCCCCCCCD) /* 0.9 */.le(acc) {
        Rank::A
    } else if F64::from_bits(0x3FE999999999999A) /* 0.8 */.le(acc) {
        Rank::B
    } else if F64::from_bits(0x3FE6666666666666) /* 0.7 */.le(acc) {
        Rank::C
    } else {
        Rank::D
    };
    match r {
        Rank::S | Rank::X => {
            if stats[hr_index(HitResult::Miss)] > 0 { Rank::A } else { r }
        }
        _ => r,
    }
}

/// `adjustRank`
pub fn adjust_rank(adj: bool, r: Rank) -> Rank {
    if !adj {
        r
    } else {
        match r {
            Rank::X => Rank::XH,
            Rank::S => Rank::SH,
            _ => r,
        }
    }
}

pub const F64_500000: F64 = F64::from_bits(0x411E_8480_0000_0000);

/// `max 0 (F64.toInt64 (F64.round x)).toInt`
pub fn round_nonneg(x: F64) -> i64 {
    let v = f64_round(x).to_i64_sat();
    if v < 0 { 0 } else { v }
}

/// the `rank` of `ScoreSt.updateScore` (`Accuracy.ValueChanged += updateRank`; a separate fn so that the
/// translation does not thread `m` through the branch)
pub fn update_rank(s: &ScoreSt, accuracy: F64, rank_adjust: bool) -> Rank {
    if netx::equals_d(s.accuracy, accuracy) || s.rank == Rank::F {
        s.rank
    } else {
        adjust_rank(rank_adjust, rank_from_score(accuracy, &s.stats))
    }
}

/// `ScoreSt.updateScore`
pub fn update_score(s: &ScoreSt, m: &ScoreMax) -> ScoreSt {
    let accuracy = clamp01(if F64_0.lt(s.current_maximum_base_score) {
        s.current_base_score.div(s.current_maximum_base_score)
    } else {
        F64_1
    });
    let rank = update_rank(s, accuracy, m.rank_adjust);
    let maximum_accuracy = clamp01(if F64_0.lt(m.maximum_base_score) {
        s.current_base_score.add(m.maximum_base_score.sub(s.current_maximum_base_score)).div(m.maximum_base_score)
    } else {
        F64_1
    });
    let combo_progress = if F64_0.lt(m.maximum_combo_portion) {
        s.current_combo_portion.div(m.maximum_combo_portion)
    } else {
        F64_1
    };
    let accuracy_progress = if m.maximum_accuracy_judgement_count > 0 {
        F64::from_u64(s.current_accuracy_judgement_count).div(F64::from_u64(m.maximum_accuracy_judgement_count))
    } else {
        F64_1
    };
    let total = F64_500000
        .mul(accuracy)
        .mul(combo_progress)
        .add(F64_500000.mul(accuracy.pow(F64_5)).mul(accuracy_progress))
        .add(s.current_bonus_portion);
    let without_mods = round_nonneg(total);
    let tot = round_nonneg(F64::from_i64(without_mods).mul(m.score_multiplier));
    ScoreSt { accuracy, total_score_without_mods: without_mods, total_score: tot, rank, maximum_accuracy, ..*s }
}

pub const F64_0_5: F64 = F64::from_bits(0x3FE0_0000_0000_0000);

/// `ScoreSt.apply`: returns the new state and `ComboAfterJudgement`.
pub fn score_apply(s0: &ScoreSt, m: &ScoreMax, j: &JInfo, failed_at_judgement: bool, simulating: bool) -> (ScoreSt, u64) {
    let mut s = *s0;
    s.judged_hits += 1;
    s.last_time_absolute = Some(j.time_absolute);
    if failed_at_judgement {
        (s, 0)
    } else {
        let ty = j.ty;
        s.stats[hr_index(ty)] += 1;
        let combo = if increases_combo(ty) {
            s.combo + 1
        } else if breaks_combo(ty) {
            0
        } else {
            s.combo
        };
        s.combo = combo;
        s.highest_combo = if s.highest_combo < combo { combo } else { s.highest_combo };
        if affects_accuracy(j.max_result) {
            s.current_maximum_base_score = s.current_maximum_base_score.add(F64::from_u64(base_score(j.max_result)));
            s.current_accuracy_judgement_count += 1;
        }
        if affects_accuracy(ty) {
            s.current_base_score = s.current_base_score.add(F64::from_u64(base_score(ty)));
        }
        if is_bonus(ty) {
            s.current_bonus_portion = s.current_bonus_portion.add(F64::from_u64(base_score(ty)));
        } else if is_scorable(ty) {
            s.current_combo_portion = s
                .current_combo_portion
                .add(F64::from_u64(base_score(j.max_result)).mul(F64::from_u64(combo).pow(F64_0_5)));
        }
        let s2 = if simulating { s } else { update_score(&s, m) };
        (s2, combo)
    }
}

/// `osuHealthIncrease`
pub fn osu_health_increase(hp: F64, kind: Kind, ty: HitResult) -> F64 {
    match ty {
        HitResult::SmallTickMiss | HitResult::LargeTickMiss => difficulty_range(hp, F64::from_bits(0xBF947AE147AE147B) /* -0.02 */, F64::from_bits(0xBFB3333333333333) /* -0.075 */, F64::from_bits(0xBFC1EB851EB851EC) /* -0.14 */),
        HitResult::Miss => difficulty_range(hp, F64::from_bits(0xBF9EB851EB851EB8) /* -0.03 */, F64::from_bits(0xBFC0000000000000) /* -0.125 */, F64::from_bits(0xBFC999999999999A) /* -0.2 */),
        HitResult::SmallTickHit => F64::from_bits(0x3F947AE147AE147B) /* 0.02 */,
        HitResult::SliderTailHit | HitResult::LargeTickHit => match kind {
            Kind::Tick => F64::from_bits(0x3F8EB851EB851EB8) /* 0.015 */,
            Kind::Head | Kind::Tail | Kind::Repeat => F64::from_bits(0x3F947AE147AE147B) /* 0.02 */,
            _ => F64_0,
        },
        HitResult::Meh => F64::from_bits(0x3F60624DD2F1A9FC) /* 0.002 */,
        HitResult::Ok_ => F64::from_bits(0x3F86872B020C49BA) /* 0.011 */,
        HitResult::Great => F64::from_bits(0x3F9EB851EB851EB8) /* 0.03 */,
        HitResult::SmallBonus => F64::from_bits(0x3F816872B020C49C) /* 0.0085 */,
        HitResult::LargeBonus => F64::from_bits(0x3F847AE147AE147B) /* 0.01 */,
        _ => F64_0,
    }
}

/// `legacyHealthIncrease`
pub fn legacy_health_increase(hp: F64, mult: F64, kind: Kind, ty: HitResult) -> F64 {
    match ty {
        HitResult::SmallTickMiss | HitResult::LargeTickMiss => difficulty_range(hp, F64::from_bits(0xBF947AE147AE147B) /* -0.02 */, F64::from_bits(0xBFB3333333333333) /* -0.075 */, F64::from_bits(0xBFC1EB851EB851EC) /* -0.14 */),
        HitResult::Miss => difficulty_range(hp, F64::from_bits(0xBF9EB851EB851EB8) /* -0.03 */, F64::from_bits(0xBFC0000000000000) /* -0.125 */, F64::from_bits(0xBFC999999999999A) /* -0.2 */),
        _ => {
            let inc = match ty {
                HitResult::SmallTickHit => F64::from_bits(0x3F947AE147AE147B) /* 0.02 */,
                HitResult::SliderTailHit | HitResult::LargeTickHit => {
                    if kind == Kind::Tick { F64::from_bits(0x3F8EB851EB851EB8) /* 0.015 */ } else { F64::from_bits(0x3F947AE147AE147B) /* 0.02 */ }
                }
                HitResult::Meh => F64::from_bits(0x3F60624DD2F1A9FC) /* 0.002 */,
                HitResult::Ok_ => F64::from_bits(0x3F86872B020C49BA) /* 0.011 */,
                HitResult::Great => F64::from_bits(0x3F9EB851EB851EB8) /* 0.03 */,
                HitResult::SmallBonus => F64::from_bits(0x3F816872B020C49C) /* 0.0085 */,
                HitResult::LargeBonus => F64::from_bits(0x3F847AE147AE147B) /* 0.01 */,
                _ => F64_0,
            };
            mult.mul(inc)
        }
    }
}

/// `HealthSt`
#[derive(Clone)]
pub struct HealthSt {
    pub health: F64,
    pub has_failed: bool,
    pub combo_result: u64,
    pub nearest_index: usize,
    pub fail_triggers: u64,
    pub failed: bool,
    pub fail_time: Option<F64>,
    pub retries: Vec<u64>,
}

/// `{} : HealthSt` with `retries`
pub fn health_st_init(retries: Vec<u64>) -> HealthSt {
    HealthSt {
        health: F64_1,
        has_failed: false,
        combo_result: 2,
        nearest_index: 0,
        fail_triggers: 0,
        failed: false,
        fail_time: None,
        retries,
    }
}

/// `HealthCfg`
#[derive(Clone)]
pub struct HealthCfg {
    pub legacy: bool,
    pub hp: F64,
    pub drain_rate: F64,
    pub hp_multiplier_normal: F64,
    pub drain_start_time: F64,
    pub gameplay_end_time: F64,
    pub periods: Vec<Period>,
}

/// `Nat.min`
pub fn nat_min(a: u64, b: u64) -> u64 {
    if a < b { a } else { b }
}

/// `HealthSt.increaseFor`: returns the new combo result and the increase (the state's other fields are unchanged).
pub fn increase_for(h: &HealthSt, c: &HealthCfg, j: &JInfo, simulating: bool) -> (u64, F64) {
    if c.legacy {
        (h.combo_result, legacy_health_increase(c.hp, c.hp_multiplier_normal, j.kind, j.ty))
    } else if simulating {
        (h.combo_result, osu_health_increase(c.hp, j.kind, j.ty))
    } else {
        let cr0 = if j.new_combo { 2 } else { h.combo_result };
        let cr1 = match j.ty {
            HitResult::LargeTickMiss | HitResult::Ok_ => nat_min(cr0, 1),
            HitResult::Meh | HitResult::Miss => nat_min(cr0, 0),
            _ => cr0,
        };
        let cr2 = if j.kind == Kind::Tail && !is_hit(j.ty) { nat_min(cr1, 1) } else { cr1 };
        let base = osu_health_increase(c.hp, j.kind, j.ty);
        let inc = if j.last_in_combo && is_hit(j.ty) {
            if cr2 == 2 {
                base.add(F64::from_bits(0x3FB1EB851EB851EC) /* 0.07 */)
            } else if cr2 == 1 {
                base.add(F64::from_bits(0x3FA999999999999A) /* 0.05 */)
            } else {
                base.add(F64::from_bits(0x3F9EB851EB851EB8) /* 0.03 */)
            }
        } else {
            base
        };
        (cr2, inc)
    }
}

/// `defaultFailCondition`
pub fn default_fail_condition(h: &HealthSt, j: &JInfo) -> bool {
    if is_bonus(j.max_result) || j.ty == HitResult::IgnoreHit {
        false
    } else {
        h.health.sub(ALMOST_EQUALS_EPS).lt(F64_0)
    }
}

/// `periodIsInAny`
pub fn period_is_in_any(ps: &[Period], idx: usize, time: F64) -> (bool, usize) {
    if ps.len() == 0 {
        (false, idx)
    } else {
        let mut i = idx;
        if ps[i].end.lt(time) {
            while ps[i].end.lt(time) && i < ps.len() - 1 {
                i += 1;
            }
        } else {
            while time.lt(ps[i].start) && i > 0 {
                i -= 1;
            }
        }
        let p = ps[i];
        (p.start.le(time) && time.le(p.end), i)
    }
}

/// `HealthSt.drain` (in place)
pub fn drain(h: &mut HealthSt, c: &HealthCfg, t: F64, elapsed: F64) -> Result<(), SimErr> {
    let (in_any, idx) = period_is_in_any(&c.periods, h.nearest_index, t);
    h.nearest_index = idx;
    if !in_any {
        // `Math.Clamp(…, drainStartTime, gameplayEndTime)` throws if the bounds are inverted
        let last_t = drain_clamp(t.sub(elapsed), c)?;
        let cur_t = drain_clamp(t, c)?;
        h.health = clamp01(h.health.sub(c.drain_rate.mul(cur_t.sub(last_t))));
    }
    Ok(())
}

/// the `cl` of `HealthSt.drain`
pub fn drain_clamp(x: F64, c: &HealthCfg) -> Result<F64, SimErr> {
    match crate::net::mathops::f64_clamp(x, c.drain_start_time, c.gameplay_end_time) {
        Ok(v) => Ok(v),
        Err(e) => Err(SimErr::ClampDrain(e)),
    }
}

/// `simulatedJudgements`
pub fn simulated_judgements(pb: &Playable) -> Vec<JInfo> {
    let mut out: Vec<JInfo> = Vec::new();
    let mut i: usize = 0;
    while i < pb.objects.len() {
        push_simulated(&mut out, &pb.objects[i]);
        i += 1;
    }
    out
}

/// `JInfo` of a simulated (max-result) judgement of `n`
pub fn sim_jinfo(n: &crate::sim::playable::HObj) -> JInfo {
    JInfo {
        kind: n.kind,
        max_result: n.max_result,
        min_result: HitResult::None,
        ty: n.max_result,
        time_absolute: n.end_time,
        end_time: n.end_time,
        time_offset: F64_0,
        new_combo: n.new_combo,
        last_in_combo: n.last_in_combo,
    }
}

/// the body of `simulatedJudgements`' loop: nested first, then the object
pub fn push_simulated(out: &mut Vec<JInfo>, o: &crate::sim::playable::TopObj) {
    let mut k: usize = 0;
    while k < o.nested.len() {
        out.push(sim_jinfo(&o.nested[k]));
        k += 1;
    }
    out.push(sim_jinfo(&o.h));
}

/// `scoreMaxima` (with `rankAdjust` from the config, as `mkCtx` sets it)
pub fn score_maxima(pb: &Playable, mult: F64, rank_adjust: bool) -> ScoreMax {
    let m0 = ScoreMax {
        maximum_base_score: F64_0,
        maximum_combo_portion: F64_0,
        maximum_accuracy_judgement_count: 0,
        max_stats: [0; HIT_RESULT_COUNT],
        max_hits: 0,
        score_multiplier: mult,
        rank_adjust,
        init_without_mods: 0,
    };
    let js = simulated_judgements(pb);
    let mut s = SCORE_ST_INIT;
    let mut i: usize = 0;
    while i < js.len() {
        let (s2, _) = score_apply(&s, &m0, &js[i], false, true);
        s = s2;
        i += 1;
    }
    ScoreMax {
        maximum_base_score: s.current_base_score,
        maximum_combo_portion: s.current_combo_portion,
        maximum_accuracy_judgement_count: s.current_accuracy_judgement_count,
        max_stats: s.stats,
        max_hits: s.judged_hits,
        init_without_mods: update_score(&s, &m0).total_score_without_mods,
        ..m0
    }
}

/// A simulated health increase `(time, increase)`.
#[derive(Clone, Copy)]
pub struct Inc {
    pub time: F64,
    pub amount: F64,
}

/// One pass of `computeDrainRate`'s outer loop: the lowest health reached with drain rate `result`.
pub fn drain_pass(incs: &[Inc], breaks: &[Period], drain_start: F64, result: F64) -> F64 {
    let mut current_health = F64_1;
    let mut lowest_health = F64_1;
    let mut current_break: usize = 0;
    let mut i: usize = 0;
    let mut stop = false;
    while i < incs.len() && !stop {
        let current_time = incs[i].time;
        let mut last_time = if i > 0 { incs[i - 1].time } else { drain_start };
        while current_break < breaks.len() && breaks[current_break].end.le(current_time) {
            last_time = current_time;
            current_break += 1;
        }
        current_health = current_health.sub(current_time.sub(last_time).mul(result));
        lowest_health = net::min(lowest_health, current_health);
        current_health = net::min(F64_1, current_health.add(incs[i].amount));
        if lowest_health.lt(F64_0) {
            stop = true;
        }
        i += 1;
    }
    lowest_health
}

/// `computeDrainRate`
pub fn compute_drain_rate(incs: &[Inc], breaks: &[Period], drain_start: F64, target: F64) -> Result<F64, SimErr> {
    if incs.len() <= 1 {
        Ok(F64_0)
    } else {
        let mut adjustment: i32 = 1;
        let mut result = F64_1;
        // `adjustment` doubles each round, so the Int32 overflows to <= 0 within 32 rounds; the fuel never runs out
        let mut fuel: u32 = 100000;
        let mut stop = false;
        while 0 < adjustment && fuel > 0 && !stop {
            fuel -= 1;
            let lowest_health = drain_pass(incs, breaks, drain_start, result);
            if lowest_health.sub(target).abs().le(F64::from_bits(0x3F847AE147AE147B) /* 0.01 */) {
                stop = true;
            } else {
                adjustment = adjustment.wrapping_mul(2);
                // `Math.Sign(NaN)` throws `ArithmeticException`
                let sgn: i64 = match crate::net::mathops::f64_sign(lowest_health.sub(target)) {
                    Ok(v) => v as i64,
                    Err(e) => return Err(SimErr::SignDrain(e)),
                };
                result = result.add(F64::from_bits(0x3FF0000000000000) /* 1.0 */.div(F64::from_i64(adjustment as i64)).mul(F64::from_i64(sgn)));
            }
        }
        if fuel == 0 && 0 < adjustment {
            return Err(SimErr::Internal(Internal::DrainFuel));
        }
        Ok(result)
    }
}

/// State of one `computeLegacyDrainRate` pass.
#[derive(Clone, Copy)]
pub struct LegacyPass {
    pub fail: bool,
    pub test_drop: F64,
    pub current_hp: F64,
    pub current_hp_uncapped: F64,
    pub top_level_object_count: u64,
}

/// `max 0 (min 1 x)`
pub fn cap01(x: F64) -> F64 {
    net::max(F64_0, net::min(F64_1, x))
}

/// The nested-object loop of a legacy pass: returns `(currentHp, currentHpUncapped)`.
pub fn legacy_nested(pb: &Playable, oi: usize, hp: F64, mult: F64, hp0: F64, unc0: F64) -> (F64, F64) {
    legacy_nested_loop(&pb.objects[oi], hp, mult, hp0, unc0)
}

/// the loop of `legacy_nested`
pub fn legacy_nested_loop(o: &crate::sim::playable::TopObj, hp: F64, mult: F64, hp0: F64, unc0: F64) -> (F64, F64) {
    let hk = o.h.kind;
    let mut current_hp = hp0;
    let mut current_hp_uncapped = unc0;
    let mut k: usize = 0;
    while k < o.nested.len() {
        let nk = o.nested[k].kind;
        let nmax = o.nested[k].max_result;
        let skip = (hk == Kind::Spinner && nk == Kind::SpinnerBonusTick) || (hk != Kind::Slider && hk != Kind::Spinner);
        if !skip {
            let amount = legacy_health_increase(hp, mult, nk, nmax);
            current_hp_uncapped = current_hp_uncapped.add(amount);
            current_hp = cap01(current_hp.add(amount));
        }
        k += 1;
    }
    (current_hp, current_hp_uncapped)
}

/// The object loop of one `computeLegacyDrainRate` pass.
pub fn legacy_pass(pb: &Playable, hp: F64, drain_start: F64, mult: F64, test_drop0: F64, lowest_hp_ever: F64) -> LegacyPass {
    let mut p = LegacyPass {
        fail: false,
        test_drop: test_drop0,
        current_hp: F64_1,
        current_hp_uncapped: F64_1,
        top_level_object_count: 0,
    };
    let mut lowest_hp = p.current_hp;
    let mut last_time = drain_start;
    let mut current_break: usize = 0;
    let mut i: usize = 0;
    while i < pb.objects.len() && !p.fail {
        p.top_level_object_count += 1;
        let h = &pb.objects[i].h;
        while current_break < pb.breaks.len() && pb.breaks[current_break].end.le(h.start) {
            last_time = h.start;
            current_break += 1;
        }
        let amt = p.test_drop.mul(h.start.sub(last_time));
        p.current_hp_uncapped = net::max(F64_0, p.current_hp_uncapped.sub(amt));
        p.current_hp = net::max(F64_0, p.current_hp.sub(amt));
        last_time = h.end_time;
        if p.current_hp.lt(lowest_hp) {
            lowest_hp = p.current_hp;
        }
        if p.current_hp.le(lowest_hp_ever) {
            p.fail = true;
            p.test_drop = p.test_drop.mul(F64::from_bits(0x3FEEB851EB851EB8) /* 0.96 */);
        } else {
            let hp_reduction = p.test_drop.mul(h.end_time.sub(h.start));
            let hp_overkill = net::max(F64_0, hp_reduction.sub(p.current_hp));
            p.current_hp_uncapped = net::max(F64_0, p.current_hp_uncapped.sub(hp_reduction));
            p.current_hp = net::max(F64_0, p.current_hp.sub(hp_reduction));
            let (chp, cunc) = legacy_nested(pb, i, hp, mult, p.current_hp, p.current_hp_uncapped);
            p.current_hp = chp;
            p.current_hp_uncapped = cunc;
            if F64_0.lt(hp_overkill) && p.current_hp.sub(hp_overkill).le(lowest_hp_ever) {
                p.fail = true;
                p.test_drop = p.test_drop.mul(F64::from_bits(0x3FEEB851EB851EB8) /* 0.96 */);
            } else {
                let amount = legacy_health_increase(hp, mult, h.kind, h.max_result);
                p.current_hp_uncapped = p.current_hp_uncapped.add(amount);
                p.current_hp = cap01(p.current_hp.add(amount));
            }
        }
        i += 1;
    }
    p
}

/// `(testDrop, HpMultiplierNormal)`
#[derive(Clone, Copy)]
pub struct LegacyRate {
    pub test_drop: F64,
    pub mult: F64,
}

pub const F64_POS_INF: F64 = F64::from_bits(0x7FF0_0000_0000_0000);
pub const F64_NEG_INF: F64 = F64::from_bits(0xFFF0_0000_0000_0000);

/// `computeLegacyDrainRate`
pub fn compute_legacy_drain_rate(pb: &Playable, hp: F64, drain_start: F64) -> Result<LegacyRate, SimErr> {
    let lowest_hp_ever = difficulty_range(hp, F64::from_bits(0x3FEF333333333333) /* 0.975 */, F64::from_bits(0x3FE999999999999A) /* 0.8 */, F64::from_bits(0x3FD3333333333333) /* 0.3 */);
    let lowest_hp_end = difficulty_range(hp, F64::from_bits(0x3FEFAE147AE147AE) /* 0.99 */, F64::from_bits(0x3FECCCCCCCCCCCCD) /* 0.9 */, F64::from_bits(0x3FD999999999999A) /* 0.4 */);
    let hp_recovery_available = difficulty_range(hp, F64::from_bits(0x3FA47AE147AE147B) /* 0.04 */, F64::from_bits(0x3F947AE147AE147B) /* 0.02 */, F64_0);
    let mut mult = F64_1;
    let mut test_drop = F64::from_bits(0x3F30624DD2F1A9FC) /* 0.00025 */;
    let mut fuel: u32 = 1000000;
    let mut done: Option<LegacyRate> = None;
    while fuel > 0 && done.is_none() {
        fuel -= 1;
        let p = legacy_pass(pb, hp, drain_start, mult, test_drop, lowest_hp_ever);
        let mut fail = p.fail;
        test_drop = p.test_drop;
        if p.top_level_object_count == 0 {
            done = Some(LegacyRate { test_drop, mult });
        } else {
            if !fail && p.current_hp.lt(lowest_hp_end) {
                fail = true;
                test_drop = test_drop.mul(F64::from_bits(0x3FEE147AE147AE14) /* 0.94 */);
                mult = mult.mul(F64::from_bits(0x3FF028F5C28F5C29) /* 1.01 */);
            }
            let recovery =
                p.current_hp_uncapped.sub(F64_1).div(net::max(F64_1, F64::from_u64(p.top_level_object_count)));
            if !fail && recovery.lt(hp_recovery_available) {
                fail = true;
                test_drop = test_drop.mul(F64::from_bits(0x3FEEB851EB851EB8) /* 0.96 */);
                mult = mult.mul(F64::from_bits(0x3FF028F5C28F5C29) /* 1.01 */);
            }
            if !fail && (mult.eq(F64_POS_INF) || mult.eq(F64_NEG_INF)) {
                done = Some(LegacyRate { test_drop: F64_0, mult: F64_1 });
            } else if !fail {
                done = Some(LegacyRate { test_drop, mult });
            }
        }
    }
    match done {
        Some(r) => Ok(r),
        None => Err(SimErr::Internal(Internal::LegacyDrainFuel)),
    }
}

/// `double.MaxValue`
pub const F64_DMAX: F64 = F64::from_bits(0x7FEF_FFFF_FFFF_FFFF);

/// insertion of `p` into `out` (stable: after the last element whose start is not greater)
pub fn insert_period_sorted(out: &mut Vec<Period>, p: Period) {
    let mut i = out.len();
    while i > 0 && p.start.lt(out[i - 1].start) {
        i -= 1;
    }
    out.push(p);
    let mut j = out.len() - 1;
    while j > i {
        out[j] = out[j - 1];
        j -= 1;
    }
    out[i] = p;
}

/// one break's period in `noDrainPeriods`
pub fn no_drain_period(pb: &Playable, bs: F64, be: F64) -> Period {
    let mut s = F64_DMAX.neg();
    let mut i: usize = 0;
    while i < pb.objects.len() {
        if pb.objects[i].h.end_time.le(bs) {
            s = pb.objects[i].h.end_time;
        }
        i += 1;
    }
    let mut e = F64_DMAX;
    let mut k: usize = 0;
    let mut found = false;
    while k < pb.objects.len() && !found {
        if be.le(pb.objects[k].h.start) {
            e = pb.objects[k].h.start;
            found = true;
        }
        k += 1;
    }
    Period { start: s, end: e }
}

/// `noDrainPeriods`
pub fn no_drain_periods(pb: &Playable) -> Vec<Period> {
    let mut out: Vec<Period> = Vec::new();
    let mut i: usize = 0;
    while i < pb.breaks.len() {
        let p = no_drain_period(pb, pb.breaks[i].start, pb.breaks[i].end);
        insert_period_sorted(&mut out, p);
        i += 1;
    }
    out
}

/// `mkHealthCfg`
pub fn mk_health_cfg(pb: &Playable, legacy: bool) -> Result<HealthCfg, SimErr> {
    let hp = pb.difficulty.hp.to_f64();
    let n = pb.objects.len();
    let drain_start = if n > 0 { pb.objects[0].h.start } else { F64_0 };
    let gameplay_end = if n > 0 { pb.objects[n - 1].h.end_time } else { F64_0 };
    let periods = no_drain_periods(pb);
    if legacy {
        let r = compute_legacy_drain_rate(pb, hp, drain_start)?;
        Ok(HealthCfg {
            legacy,
            hp,
            drain_rate: r.test_drop,
            hp_multiplier_normal: r.mult,
            drain_start_time: drain_start,
            gameplay_end_time: gameplay_end,
            periods,
        })
    } else {
        let target0 = difficulty_range(hp, F64::from_bits(0x3FEFAE147AE147AE) /* 0.99 */, F64::from_bits(0x3FECCCCCCCCCCCCD) /* 0.9 */, F64::from_bits(0x3FD999999999999A) /* 0.4 */);
        let target1 = target0.add(F64_0.mul(F64_1.sub(target0)));
        let target = f64_clamp_or(target1, F64_0, F64_1);
        let cfg0 = HealthCfg {
            legacy,
            hp,
            drain_rate: F64_0,
            hp_multiplier_normal: F64_1,
            drain_start_time: drain_start,
            gameplay_end_time: gameplay_end,
            periods,
        };
        let js = simulated_judgements(pb);
        let h0 = health_st_init(Vec::new());
        let mut incs: Vec<Inc> = Vec::new();
        let mut i: usize = 0;
        while i < js.len() {
            let j = &js[i];
            if !is_bonus(j.ty) {
                let (_, inc) = increase_for(&h0, &cfg0, j, true);
                incs.push(Inc { time: j.end_time.add(j.time_offset), amount: inc });
            }
            i += 1;
        }
        let rate = compute_drain_rate(&incs, &pb.breaks, drain_start, target)?;
        Ok(HealthCfg { drain_rate: rate, ..cfg0 })
    }
}
