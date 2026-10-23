//! The frame-stable step. Spec: `model/OsuModel/Sim/Step.lean` (namespace `OsuModel.Sim.Sim`, plus
//! `mkCtx`, `initState`, `simulate`). Every spec `def` has a function of the same (snake_case) name;
//! `SimM` actions take `(c: &Ctx, s: &mut St)`.
//!
//! Pinned spec: Lean commit `e0e8215` (M0-M7: core, sim-side mods, transform engine, pooled DHO instances; total
//! simulation, G17). `SimM` actions that can reject return `Result<_, SimErr>` (`sim::err`); the spec's
//! `internal: index … out of range` accessors (`getA`/`setA`/`need` on invariant-sized arrays) are plain indexing.
use crate::float::{F32, F64};
use crate::net;
use crate::replay::frames::{act_contains, act_eq, act_minus, act_push, act_remove, Action, ActList, Frame, ACTLIST_EMPTY};
use crate::sim::basic::*;
use crate::sim::err::{lift_net, Internal, SimErr};
use crate::sim::geometry::*;
use crate::sim::mods::{dyn_rate_initial_speed, dyn_rate_set_speed, time_ramp_rate, true_rate, vis_mod_skips_spinners, AccChallenge, Config, DynRate, FailCond, FailOverride, PolicyKind, Updatable, VisMod};
use crate::sim::transforms::*;
use crate::net::framework::Easing;
use crate::net::osutk::{v2_clamp, v2_distance};
use crate::sim::netx::{self, f32_clamp_or, f32_max, f32_min, f64_clamp_or};
use crate::sim::playable::*;
use crate::sim::schedule::{steps, ScheduleKind};
use crate::sim::scoring::*;
use crate::sim::state::*;
use alloc::vec::Vec;

/// `Ref` = (top-level index, nested index; `-1` = the object itself)
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Ref {
    pub top: usize,
    pub nested: i64,
}

pub const F64_0: F64 = F64::from_bits(0);
pub const F64_1: F64 = F64::from_bits(0x3FF0_0000_0000_0000);

/// `hobjOf`
pub fn hobj_of(c: &Ctx, r: Ref) -> HObj {
    let o = &c.pb.objects[r.top];
    if r.nested < 0 { o.h } else { o.nested[r.nested as usize] }
}

/// `resOf`
pub fn res_of(s: &St, r: Ref) -> Option<Res> {
    let o = &s.objs[r.top];
    if r.nested < 0 { o.result } else { o.nested[r.nested as usize] }
}

/// `judged`
pub fn judged(s: &St, r: Ref) -> bool {
    res_of(s, r).is_some()
}

/// `allJudged`
pub fn all_judged(s: &St, i: usize) -> bool {
    os_all_judged(&s.objs[i])
}

/// `allJudged` on one object state
pub fn os_all_judged(o: &OState) -> bool {
    if o.result.is_none() {
        false
    } else {
        let mut k: usize = 0;
        let mut all = true;
        while k < o.nested.len() {
            if o.nested[k].is_none() {
                all = false;
            }
            k += 1;
        }
        all
    }
}

/// `isHitRef`
pub fn is_hit_ref(s: &St, r: Ref) -> bool {
    match res_of(s, r) {
        Some(x) => is_hit(x.ty),
        None => false,
    }
}

// ---------------------------------------------------------------------------------------------
// Pooled DHO instances, transformable state, presence, current geometry (M7, Lean 7cffd29)

/// `Part`
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Part {
    Top,
    Head,
}

/// `partInst`
pub fn part_inst(s: &St, i: usize, p: Part) -> usize {
    if p == Part::Top { s.objs[i].inst } else { s.objs[i].head_inst }
}

/// `partRef`
pub fn part_ref(c: &Ctx, i: usize, p: Part) -> Ref {
    if p == Part::Top { Ref { top: i, nested: -1 } } else { Ref { top: i, nested: c.head_idx[i] as i64 } }
}

/// `partArmed`
pub fn part_armed(s: &St, i: usize, p: Part) -> Armed {
    if p == Part::Top { s.objs[i].armed } else { s.objs[i].head_armed }
}

/// `poolGet`
pub fn pool_get(s: &mut St, pk: usize) -> usize {
    match s.pools[pk].pop() {
        Some(Some(k)) => k,
        Some(None) => {
            s.insts.push(inst_new());
            s.insts.len() - 1
        }
        None => {
            s.insts.push(inst_new());
            s.insts.len() - 1
        }
    }
}

/// `poolReturn`
pub fn pool_return(s: &mut St, pk: usize, k: usize) {
    if s.pools[pk].len() < POOL_MAX[pk] {
        s.pools[pk].push(Some(k));
    }
}

/// `poolKind`
pub fn pool_kind(k: Kind) -> usize {
    match k {
        Kind::Circle => 0,
        Kind::Slider => 1,
        Kind::Head => 2,
        _ => 3,
    }
}

/// `placementOf`
pub fn placement_of(tf: &TObj) -> Placement {
    Placement { pos: tf.pos, scale: tf.scale, rot: tf.rot }
}

/// `1e-4f` (`Drawable.IsPresent` alpha threshold)
pub const ALPHA_PRESENT: F32 = F32::from_bits(0x38D1_B717);

/// `presentTf`
pub fn present_tf(tf: &TObj, armed: Armed, now: F64, lifetime_start: F64) -> bool {
    (ALPHA_PRESENT.lt(tf.alpha) && !tf.scale.x.eq(F32_0) && !tf.scale.y.eq(F32_0))
        || (armed == Armed::Idle && lifetime_start.le(now))
}

/// `partPresent` (`dbgNoPresence` is a debugging switch of the spec, not modelled)
pub fn part_present(c: &Ctx, s: &St, i: usize, p: Part) -> bool {
    let k = part_inst(s, i, p);
    let ls = if p == Part::Top {
        s.objs[i].lifetime_start
    } else {
        let hd = c.pb.objects[i].nested[c.head_idx[i]];
        hd.start.sub(hd.preempt)
    };
    present_tf(&s.insts[k].tf, part_armed(s, i, p), s.t, ls)
}

/// `brScale`
pub fn br_scale(env: &Env) -> Vec2 {
    let sz = env.hoc_size;
    let mn = f32_min(sz.x, sz.y);
    let mx = f32_max(sz.x, sz.y);
    Vec2 { x: mn.div(mx), y: mn.div(mx) }
}

/// `curHoc`
pub fn cur_hoc(c: &Ctx, s: &St) -> DrawInfo {
    match c.cfg.barrel_roll {
        None => {
            if s.k == 0 { c.env.hoc_first } else { c.env.hoc }
        }
        Some(_) => {
            let nodes = if s.k == 0 { &c.env.chain_first } else { &c.env.chain };
            compose_chain(nodes, Some((s.br_rot, br_scale(&c.env))))
        }
    }
}

/// `curEnv`'s HitObjectContainer DrawInfo (`hoc` replaced by `curHoc` with BarrelRoll)
pub fn cur_env_hoc(c: &Ctx, s: &St) -> DrawInfo {
    match c.cfg.barrel_roll {
        None => c.env.hoc,
        Some(_) => cur_hoc(c, s),
    }
}

/// `curCircleReceptor`
pub fn cur_circle_receptor(c: &Ctx, s: &St, i: usize) -> DrawInfo {
    let ins = &s.insts[s.objs[i].inst];
    receptor_from_placement(&cur_env_hoc(c, s), placement_of(&ins.tf), VEC2_ZERO, c.pb.objects[i].h.scale)
}

/// `curSliderGeom`
pub fn cur_slider_geom(c: &Ctx, s: &St, i: usize) -> SliderGeom {
    let ins = &s.insts[s.objs[i].inst];
    let hins = &s.insts[s.objs[i].head_inst];
    slider_geom_p(
        &cur_env_hoc(c, s),
        c.env.argon_path_radius,
        &c.pb.objects[i].h,
        placement_of(&ins.tf),
        ins.size,
        ins.origin,
        ins.rel_anchor,
        placement_of(&hins.tf),
    )
}

/// `curSpinnerGeom`
pub fn cur_spinner_geom(c: &Ctx, s: &St, i: usize) -> SpinnerGeom {
    let ins = &s.insts[s.objs[i].inst];
    spinner_geom_p(&cur_env_hoc(c, s), c.env.hoc_size, placement_of(&ins.tf))
}

// ---------------------------------------------------------------------------------------------
// Lifetimes from hit-state transforms

/// `latestTransformEndTime s [e]` (all uses have a single transform)
pub fn latest_transform_end_time(s: F64, e: F64) -> F64 {
    if s.lt(e) { e.add(F64_1) } else { s }
}

/// `seqStart`
pub fn seq_start(ct: F64, t: F64) -> F64 {
    ct.add(t.sub(ct))
}

pub const F64_100: F64 = F64::from_bits(0x4059_0000_0000_0000);
pub const F64_800: F64 = F64::from_bits(0x4089_0000_0000_0000);
pub const F64_240: F64 = F64::from_bits(0x406E_0000_0000_0000);

/// `circleLifetimeEnd`; `state`: `Some(false)` = Miss, `Some(true)` = Hit, `None` = Idle
pub fn circle_lifetime_end(ct: F64, t: F64, state: Option<bool>) -> F64 {
    let s = seq_start(ct, t);
    match state {
        Some(false) => latest_transform_end_time(s, s.add(F64_100)),
        _ => latest_transform_end_time(s, s.add(F64_800).add(F64_0)),
    }
}

/// `sliderLifetimeEnd`
pub fn slider_lifetime_end(ct: F64, t: F64) -> F64 {
    let s = seq_start(ct, t);
    latest_transform_end_time(s, s.add(F64_240))
}

/// `timeAbsolute`
pub fn time_absolute(h: &HObj, raw: F64) -> F64 {
    net::min(raw, h.end_time.add(h.max_judgement_offset))
}

// ---------------------------------------------------------------------------------------------
// Processors: fail, health, score

/// `triggerFailure`
pub fn trigger_failure(c: &Config, h0: &HealthSt, t: F64, replay_player: bool, last_frame_time: Option<F64>) -> HealthSt {
    if h0.has_failed {
        return h0.clone();
    }
    let mut h = h0.clone();
    h.fail_triggers += 1;
    if replay_player {
        match last_frame_time {
            Some(lf) => {
                if !lf.le(t) {
                    return h;
                }
            }
            None => {
                return h;
            }
        }
    }
    // `All(PerformFail)` with short-circuit: `stop` = some override returned false
    let mut stop = false;
    let mut i: usize = 0;
    while i < c.fail_overrides.len() && !stop {
        match c.fail_overrides[i] {
            FailOverride::Veto => {
                stop = true;
            }
            FailOverride::Allow => {}
            FailOverride::Easy(k) => {
                let r: u64 = h.retries[k];
                if r != 0 {
                    h.health = F64_1;
                    h.retries[k] = r.wrapping_sub(1);
                    stop = true;
                }
            }
        }
        i += 1;
    }
    if !stop {
        h.has_failed = true;
        h.failed = true;
        h.fail_time = Some(t);
    }
    h
}

/// `failCondition`
pub fn fail_condition(j: &JInfo, fc: FailCond) -> bool {
    match fc {
        FailCond::SuddenDeath(tail) => {
            (affects_combo(j.ty) && !is_hit(j.ty)) || (tail && j.kind == Kind::Tail && !is_hit(j.ty))
        }
        FailCond::Perfect => {
            let rel_min = affects_accuracy(j.min_result) || affects_combo(j.min_result);
            let rel_max = affects_accuracy(j.max_result) || affects_combo(j.max_result);
            let rel_ty = affects_accuracy(j.ty) || affects_combo(j.ty);
            (rel_min || rel_max || rel_ty) && j.ty != j.max_result
        }
        FailCond::TargetPractice => affects_combo(j.ty) && !is_hit(j.ty),
    }
}

/// `c.failConds.any (failCondition j)`
pub fn any_fail_condition(c: &Config, j: &JInfo) -> bool {
    let mut i: usize = 0;
    let mut any = false;
    while i < c.fail_conds.len() {
        if fail_condition(j, c.fail_conds[i]) {
            any = true;
        }
        i += 1;
    }
    any
}

/// `healthApply`: returns the new state and `FailedAtJudgement`
pub fn health_apply(h0: &HealthSt, hc: &HealthCfg, c: &Config, j: &JInfo, t: F64, replay_player: bool, last_frame_time: Option<F64>) -> (HealthSt, bool) {
    if h0.has_failed {
        (h0.clone(), true)
    } else {
        let (cr, inc) = increase_for(h0, hc, j, false);
        let mut h = h0.clone();
        h.combo_result = cr;
        h.health = clamp01(h.health.add(inc));
        if default_fail_condition(&h, j) || any_fail_condition(c, j) {
            (trigger_failure(c, &h, t, replay_player, last_frame_time), false)
        } else {
            (h, false)
        }
    }
}

/// `accChallenge` (HOOK(M5+): `accChallenges` is empty in the ported scope)
pub fn acc_challenge(c: &Config, h0: HealthSt, old: &ScoreSt, new: &ScoreSt, t: F64, replay_player: bool, last_frame_time: Option<F64>) -> HealthSt {
    let mut h = h0;
    let mut pass: usize = 0;
    while pass < 2 {
        let std = pass == 0;
        let o = if std { old.accuracy } else { old.maximum_accuracy };
        let n = if std { new.accuracy } else { new.maximum_accuracy };
        if !netx::equals_d(o, n) {
            let mut k: usize = 0;
            while k < c.acc_challenges.len() {
                let ac: AccChallenge = c.acc_challenges[k];
                if ac.standard == std && n.lt(ac.min_acc) {
                    h = trigger_failure(c, &h, t, replay_player, last_frame_time);
                }
                k += 1;
            }
        }
        pass += 1;
    }
    h
}

/// the `one` of `emit`: one fail semantics' processors
pub fn emit_one(c: &Ctx, j: &JInfo, t: F64, hs: &HealthSt, ss: &ScoreSt, rp: bool) -> (HealthSt, ScoreSt, bool, u64) {
    let (hs1, fl) = health_apply(hs, &c.hcfg, &c.cfg, j, t, rp, c.last_frame_time);
    let (ss2, combo) = score_apply(ss, &c.smax, j, fl, false);
    let hs2 = acc_challenge(&c.cfg, hs1, ss, &ss2, t, rp, c.last_frame_time);
    (hs2, ss2, fl, combo)
}

/// `emit`
pub fn emit(c: &Ctx, s: &mut St, r: Ref, ty: HitResult, t: F64) {
    let h = hobj_of(c, r);
    let j = JInfo {
        kind: h.kind,
        max_result: h.max_result,
        min_result: h.min_result,
        ty,
        time_absolute: net::min(t, h.end_time.add(h.max_judgement_offset)),
        end_time: h.end_time,
        time_offset: net::min(t.sub(h.end_time), h.max_judgement_offset),
        new_combo: h.new_combo,
        last_in_combo: h.last_in_combo,
    };
    let (hl, sl, fl, combo) = emit_one(c, &j, t, &s.health, &s.score, false);
    let (hr, sr, fr, combo_r) = emit_one(c, &j, t, &s.health_rp, &s.score_rp, true);
    let health_after = hl.health;
    let health_after_rp = hr.health;
    s.health = hl;
    s.score = sl;
    s.health_rp = hr;
    s.score_rp = sr;
    s.out.push(JRec {
        top: r.top,
        nested: r.nested,
        kind: h.kind,
        type_id: h.type_id,
        result: ty,
        time: t,
        combo,
        health: health_after,
        failed: fl,
        combo_rp: combo_r,
        health_rp: health_after_rp,
        failed_rp: fr,
    });
}

// ---------------------------------------------------------------------------------------------
// Alive objects and input order

/// `Array.insertIdx!` for index lists
pub fn insert_idx(v: &mut Vec<usize>, i: usize, x: usize) {
    v.push(x);
    let mut j = v.len() - 1;
    while j > i {
        v[j] = v[j - 1];
        j -= 1;
    }
    v[i] = x;
}

/// `stableSortBy … (start <)`: the sort of `aliveObjects`
pub fn stable_sort_by_start(c: &Ctx, xs: &[usize]) -> Vec<usize> {
    let mut out: Vec<usize> = Vec::new();
    let mut k: usize = 0;
    while k < xs.len() {
        let x = xs[k];
        let sx = c.pb.objects[x].h.start;
        let mut i = out.len();
        while i > 0 && sx.lt(c.pb.objects[out[i - 1]].h.start) {
            i -= 1;
        }
        insert_idx(&mut out, i, x);
        k += 1;
    }
    out
}

/// `aliveObjects`
pub fn alive_objects(c: &Ctx, s: &St) -> Vec<usize> {
    let mut enum_order: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < s.dict_slots.len() {
        match s.dict_slots[i] {
            Some(x) => enum_order.push(x),
            None => {}
        }
        i += 1;
    }
    stable_sort_by_start(c, &enum_order)
}

/// the `lt` of `inputOrder`
pub fn input_lt(c: &Ctx, s: &St, a: usize, b: usize) -> bool {
    let sa = c.pb.objects[a].h.start;
    let sb = c.pb.objects[b].h.start;
    sa.lt(sb) || (sa.eq(sb) && s.objs[a].child_id < s.objs[b].child_id)
}

/// `inputOrder`
pub fn input_order(c: &Ctx, s: &St) -> Vec<usize> {
    let mut out: Vec<usize> = Vec::new();
    let mut k: usize = 0;
    while k < s.active.len() {
        let x = s.active[k];
        let mut i = out.len();
        while i > 0 && input_lt(c, s, x, out[i - 1]) {
            i -= 1;
        }
        insert_idx(&mut out, i, x);
        k += 1;
    }
    out
}

/// `updateOrder`
pub fn update_order(c: &Ctx, s: &St) -> Vec<usize> {
    let io = input_order(c, s);
    let mut out: Vec<usize> = Vec::new();
    let mut k = io.len();
    while k > 0 {
        k -= 1;
        out.push(io[k]);
    }
    out
}

// ---------------------------------------------------------------------------------------------
// Hit policies

/// `ClickAction`
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ClickAction {
    Ignore,
    Shake,
    Hit,
}

/// the inner loop of `enumerateUpTo`
pub fn push_nested_up_to(out: &mut Vec<Ref>, o: &TopObj, i: usize, target: F64) {
    let mut j: usize = 0;
    let mut stop = false;
    while j < o.nested.len() && !stop {
        if !o.nested[j].start.lt(target) {
            stop = true;
        } else {
            out.push(Ref { top: i, nested: j as i64 });
            j += 1;
        }
    }
}

/// `enumerateUpTo`
pub fn enumerate_up_to(c: &Ctx, s: &St, target: F64) -> Vec<Ref> {
    let alive = alive_objects(c, s);
    let mut out: Vec<Ref> = Vec::new();
    let mut k: usize = 0;
    let mut stop = false;
    while k < alive.len() && !stop {
        let i = alive[k];
        let o = &c.pb.objects[i];
        if !o.h.start.lt(target) {
            stop = true;
        } else {
            out.push(Ref { top: i, nested: -1 });
            push_nested_up_to(&mut out, o, i, target);
            k += 1;
        }
    }
    out
}

/// `circleLike`
pub fn circle_like(c: &Ctx, r: Ref) -> bool {
    is_circle_like(hobj_of(c, r).kind)
}

/// `checkHittable` for `.startTimeOrdered`
pub fn check_hittable_sto(c: &Ctx, s: &St, h: &HObj, time: F64, result: HitResult) -> ClickAction {
    let objs = enumerate_up_to(c, s, h.start);
    let mut blocking: Option<Ref> = None;
    let mut k: usize = 0;
    while k < objs.len() {
        if circle_like(c, objs[k]) {
            blocking = Some(objs[k]);
        }
        k += 1;
    }
    let blocked = match blocking {
        Some(b) => {
            let bh = hobj_of(c, b);
            !judged(s, b) && time.lt(bh.start)
        }
        None => false,
    };
    if blocked {
        ClickAction::Shake
    } else if result == HitResult::None {
        ClickAction::Shake
    } else {
        ClickAction::Hit
    }
}

/// `alive.idxOf? x`
pub fn idx_of(v: &[usize], x: usize) -> Option<usize> {
    let mut k: usize = 0;
    let mut found: Option<usize> = None;
    while k < v.len() && found.is_none() {
        if v[k] == x {
            found = Some(k);
        }
        k += 1;
    }
    found
}

pub const F64_3: F64 = F64::from_bits(0x4008_0000_0000_0000);

/// the `for p in alive` loop of the legacy `checkHittable`: `true` = shake
pub fn legacy_blocked_by_earlier(c: &Ctx, s: &St, alive: &[usize], r: Ref, h: &HObj) -> bool {
    let mut k: usize = 0;
    let mut stop = false;
    let mut shake = false;
    while k < alive.len() && !stop {
        let p = alive[k];
        if !all_judged(s, p) {
            if r.nested < 0 && p == r.top {
                stop = true;
            } else if c.pb.objects[p].h.end_time.add(F64_3).lt(h.start) {
                shake = true;
                stop = true;
            }
        }
        k += 1;
    }
    shake
}

/// `checkHittable` for `.legacy hittableRange`
pub fn check_hittable_legacy(c: &Ctx, s: &St, r: Ref, h: &HObj, time: F64, result: HitResult, hittable_range: F64) -> ClickAction {
    let alive = alive_objects(c, s);
    let mut ignore = false;
    if r.nested < 0 {
        match idx_of(&alive, r.top) {
            Some(idx) => {
                if idx > 0 {
                    let p = alive[idx - 1];
                    let ph = &c.pb.objects[p].h;
                    if ph.stack_height > 0 && !all_judged(s, p) {
                        ignore = true;
                    }
                }
            }
            None => {}
        }
    }
    if ignore {
        ClickAction::Ignore
    } else if result == HitResult::None {
        ClickAction::Shake
    } else if legacy_blocked_by_earlier(c, s, &alive, r, h) {
        ClickAction::Shake
    } else if h.start.sub(time).abs().lt(hittable_range) {
        ClickAction::Hit
    } else {
        ClickAction::Shake
    }
}

/// `checkHittable`
pub fn check_hittable(c: &Ctx, s: &St, r: Ref, time: F64, result: HitResult) -> ClickAction {
    let h = hobj_of(c, r);
    match c.cfg.policy {
        PolicyKind::StartTimeOrdered => check_hittable_sto(c, s, &h, time, result),
        PolicyKind::Legacy(range) => check_hittable_legacy(c, s, r, &h, time, result, range),
    }
}

// ---------------------------------------------------------------------------------------------
// Judgement application

/// `adaptiveSpeedOnResult`
pub fn adaptive_speed_on_result(c: &Ctx, s: &mut St, r: Ref, ty: HitResult, t: F64) -> Result<(), SimErr> {
    if c.cfg.dyn_rates.len() == 0 {
        return Ok(());
    }
    let h = hobj_of(c, r);
    let mut ai: usize = 0;
    let mut k: usize = 0;
    while k < c.cfg.dyn_rates.len() {
        match c.cfg.dyn_rates[k] {
            DynRate::Adaptive(_) => {
                let prev = prec_end_of(c, r);
                adaptive_speed_one(s, k, ai, r, &h, ty, t, prev)?;
                ai += 1;
            }
            DynRate::TimeRamp(_, _, _, _) => {}
        }
        k += 1;
    }
    Ok(())
}

/// `prev?` of `adaptiveSpeedOnResult`: `ModAdaptiveSpeed.precedingEndTimes` of the judged object (the spec's
/// `getA c.precEnd r.1` / `getA ns r.2`: in range, `precEnd` has an entry per object when an AS mod is active)
pub fn prec_end_of(c: &Ctx, r: Ref) -> Option<F64> {
    let pe = &c.prec_end[r.top];
    if r.nested < 0 { pe.top } else { pe.nested[r.nested as usize] }
}

/// `ratesForRewinding.ContainsKey(r)` (`seen.contains r`)
pub fn ref_seen(seen: &[Ref], r: Ref) -> bool {
    let mut i: usize = 0;
    let mut found = false;
    while i < seen.len() {
        if seen[i].top == r.top && seen[i].nested == r.nested {
            found = true;
        }
        i += 1;
    }
    found
}

/// `liftNet (F64.clamp x lo hi)`
pub fn clamp_net(x: F64, lo: F64, hi: F64) -> Result<F64, SimErr> {
    lift_net(crate::net::mathops::f64_clamp(x, lo, hi))
}

/// the AS step of `adaptiveSpeedOnResult` for the `ai`-th AS mod (dyn rate index `k`)
pub fn adaptive_speed_one(s: &mut St, k: usize, ai: usize, r: Ref, h: &HObj, ty: HitResult, t: F64, prev_opt: Option<F64>) -> Result<(), SimErr> {
    if !ref_seen(&s.as_seen[ai], r) && affects_accuracy(ty) {
        match prev_opt {
            Some(prev) => {
                let rel = if !is_hit(ty) {
                    F64::from_bits(0x3FEE666666666666) /* 0.95 */
                } else {
                    clamp_net(h.end_time.sub(prev).div(time_absolute(h, t).sub(prev)), F64::from_bits(0x3FECCCCCCCCCCCCD) /* 0.9 */, F64::from_bits(0x3FF1C28F5C28F5C3) /* 1.11 */)?
                };
                let speed = s.speed[k];
                let mut recent: Vec<F64> = Vec::new();
                let mut q: usize = 1;
                while q < 8 && q < s.as_recent[ai].len() {
                    recent.push(s.as_recent[ai][q]);
                    q += 1;
                }
                let last = clamp_net(rel.mul(speed), F64::from_bits(0x3FD999999999999A) /* 0.4 */, F64::from_bits(0x4004000000000000) /* 2.5 */)?;
                recent.push(last);
                let mut consistency: i64 = 0;
                let mut i: usize = 1;
                while i < recent.len() {
                    let sg: i64 = lift_net(crate::net::mathops::f64_sign(recent[i].sub(recent[i - 1])))? as i64;
                    consistency += sg;
                    i += 1;
                }
                let avg = lift_net(crate::net::sysmisc::average_f64(&recent))?;
                let abs_c: i64 = if consistency < 0 { -consistency } else { consistency };
                let target = crate::net::framework::lerp(
                    s.as_target[ai],
                    avg,
                    F64::from_i64(abs_c).div(F64::from_i64(8).sub(F64_1)),
                );
                s.as_seen[ai].push(r);
                s.as_recent[ai] = recent;
                s.as_target[ai] = target;
            }
            None => {}
        }
    }
    Ok(())
}

/// `dynRateUpdate`
pub fn dyn_rate_update(c: &Ctx, s: &mut St, k: usize) -> Result<(), SimErr> {
    let elapsed = if s.k == 0 { F64_0 } else { s.t.sub(c.steps[s.k - 1].time) };
    let d = c.cfg.dyn_rates[k];
    let mut ai: usize = 0;
    let mut j: usize = 0;
    while j < k {
        match c.cfg.dyn_rates[j] {
            DynRate::Adaptive(_) => {
                ai += 1;
            }
            DynRate::TimeRamp(_, _, _, _) => {}
        }
        j += 1;
    }
    let old = s.speed[k];
    let v = match d {
        DynRate::TimeRamp(i, f, b, ft) => lift_net(time_ramp_rate(i, f, b, ft, s.t))?,
        DynRate::Adaptive(_) => crate::net::framework::damp_continuously(old, s.as_target[ai], F64::from_bits(0x4049000000000000) /* 50 */, elapsed),
    };
    let nv = lift_net(dyn_rate_set_speed(d, old, v))?;
    s.speed[k] = nv;
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// DHO state updates (M7, Lean 7cffd29)

pub const F32_1C: F32 = F32::from_bits(0x3F80_0000);
pub const F32_0_5C: F32 = F32::from_bits(0x3F00_0000);
pub const F32_360C: F32 = F32::from_bits(0x43B4_0000);
pub const F32_1000: F32 = F32::from_bits(0x447A_0000);

/// the begin of `withAbs`: `BeginAbsoluteSequence(t)` on a part's transformable; returns the saved delay
pub fn with_abs_begin(s: &mut St, k: usize, now: F64, t: F64) -> F64 {
    let saved = s.insts[k].tf.delay;
    abs_seq(&mut s.insts[k].tf, now, t);
    saved
}

/// the end of `withAbs`: restore the delay
pub fn with_abs_end(s: &mut St, k: usize, saved: F64) {
    s.insts[k].tf.delay = saved;
}

/// `vs 0`, `vs 1`, `(x, x)`
pub fn v_xy(x: F32, y: F32) -> Vec2 {
    Vec2 { x, y }
}

/// one `wig` of `OsuModWiggle`
pub fn wiggle_one(rng: crate::net::random::State, strength: F64, origin: Vec2) -> (Vec2, crate::net::random::State) {
    let (a, rng1) = crate::net::random::sample(rng);
    let (b, rng2) = crate::net::random::sample(rng1);
    let ang = a.mul(F64::from_bits(0x4000000000000000) /* 2 */).mul(crate::net::framework::PI).to_f32();
    let dist = b.mul(strength).mul(F64::from_bits(0x401C000000000000) /* 7 */).to_f32();
    let v = Vec2 {
        x: dist.to_f64().mul(ang.to_f64().cos()).add(origin.x.to_f64()).to_f32(),
        y: dist.to_f64().mul(ang.to_f64().sin()).add(origin.y.to_f64()).to_f32(),
    };
    (v, rng2)
}

/// `count / 100` for a positive `Int` count (non-positive -> no iterations)
pub fn hundreds(n: i64) -> u64 {
    if n <= 0 { 0 } else { (n / 100) as u64 }
}

/// the `.wiggle` handler of `customState`
pub fn wiggle_state(c: &Ctx, s: &mut St, i: usize, p: Part, k: usize, h: &HObj, strength: F64, now: F64) {
    let o = &c.pb.objects[i];
    let origin = s.insts[k].tf.pos;
    let mut rng = crate::net::random::create(h.start.to_i32_sat());
    let mut seg_t: Vec<F64> = Vec::new();
    let mut seg_v: Vec<Vec2> = Vec::new();
    let n1 = hundreds(h.preempt.to_i32_sat() as i64);
    let mut q: u64 = 0;
    while q < n1 {
        let (v, r2) = wiggle_one(rng, strength, origin);
        rng = r2;
        seg_t.push(h.start.sub(h.preempt).add(F64::from_u64(q * 100)));
        seg_v.push(v);
        q += 1;
    }
    let dur: Option<F64> = if p == Part::Top {
        match o.h.kind {
            Kind::Slider => match &o.slider {
                Some(sd) => Some(sd.duration),
                None => None,
            },
            Kind::Spinner => match o.spinner {
                Some(sp) => Some(sp.duration),
                None => None,
            },
            _ => None,
        }
    } else {
        None
    };
    match dur {
        Some(d) => {
            let n2v = d.div(F64::from_bits(0x4059000000000000) /* 100 */).to_i32_sat() as i64;
            let n2: u64 = if n2v <= 0 { 0 } else { n2v as u64 };
            let mut q2: u64 = 0;
            while q2 < n2 {
                let (v, r2) = wiggle_one(rng, strength, origin);
                rng = r2;
                seg_t.push(h.start.add(F64::from_u64(q2 * 100)));
                seg_v.push(v);
                q2 += 1;
            }
        }
        None => {}
    }
    let mut z: usize = 0;
    while z < seg_t.len() {
        let saved = with_abs_begin(s, k, now, seg_t[z]);
        transform_to(&mut s.insts[k].tf, now, Member::Position, seg_v[z], F64::from_bits(0x4059000000000000) /* 100 */, Easing::None, None);
        with_abs_end(s, k, saved);
        z += 1;
    }
}

/// the `.transform` handler of `customState` (`OsuModTransform.applyTransform`)
pub fn transform_state(s: &mut St, k: usize, h: &HObj, now: F64) {
    let appear_distance = h.preempt.sub(h.fade_in).to_f32().div(F32_2);
    let th = s.theta;
    let orig = s.insts[k].tf.pos;
    let off = Vec2 { x: th.cos(), y: th.sin() }.scale(appear_distance);
    let appear_time = h.start.sub(h.preempt).sub(F64_1);
    let move_duration = h.preempt.add(F64_1);
    let saved = with_abs_begin(s, k, now, appear_time);
    let sq = transform_to(&mut s.insts[k].tf, now, Member::Position, VEC2_ZERO, F64_0, Easing::None, Some(off));
    seq_append(sq, &mut s.insts[k].tf, now, Member::Position, orig, move_duration, Easing::InOutSine, None);
    with_abs_end(s, k, saved);
    s.theta = s.theta.add(h.fade_in.to_f32().div(F32_1000));
}

/// the `.hidden` handler of `customState`
pub fn hidden_state(s: &mut St, k: usize, h: &HObj, kind: Kind, increased: bool, now: F64) {
    let fade_start = h.start.sub(h.preempt).add(h.fade_in);
    let fade_dur = h.preempt.mul(F64::from_bits(0x3FD3333333333333) /* 0.3 */);
    let long_dur = h.end_time.sub(fade_start);
    if kind == Kind::Circle || kind == Kind::Head {
        if !increased {
            let saved = with_abs_begin(s, k, now, fade_start);
            transform_to(&mut s.insts[k].tf, now, Member::Alpha, vs(F32_0), fade_dur, Easing::None, None);
            with_abs_end(s, k, saved);
        }
    } else if kind == Kind::Slider {
        let saved = s.insts[k].body_tf.delay;
        abs_seq(&mut s.insts[k].body_tf, now, fade_start);
        transform_to(&mut s.insts[k].body_tf, now, Member::Alpha, vs(F32_0), long_dur, Easing::Out, None);
        s.insts[k].body_tf.delay = saved;
    } else if kind == Kind::Spinner {
        let saved = with_abs_begin(s, k, now, fade_start.add(long_dur));
        transform_to(&mut s.insts[k].tf, now, Member::Alpha, vs(F32_0), fade_dur, Easing::None, None);
        with_abs_end(s, k, saved);
    }
}

/// the `.spinIn` handler of `customState`
pub fn spin_in_state(s: &mut St, k: usize, h: &HObj, kind: Kind, state: Armed, now: F64) {
    let s0 = h.start.sub(h.preempt);
    let is_circle_dho = kind == Kind::Circle || kind == Kind::Head;
    if is_circle_dho {
        let saved = with_abs_begin(s, k, now, s0);
        let tf = &mut s.insts[k].tf;
        let sq = transform_to(tf, now, Member::Rotation, vs(F32_360C), F64_0, Easing::None, None);
        seq_append(seq_then(sq), tf, now, Member::Rotation, vs(F32_0), h.preempt, Easing::InOutSine, None);
        let sq2 = transform_to(tf, now, Member::Scale, v_xy(F32_2, F32_0), F64_0, Easing::None, None);
        seq_append(seq_then(sq2), tf, now, Member::Scale, v_xy(F32_1C, F32_1C), h.preempt, Easing::InOutSine, None);
        if state == Armed::Idle {
            transform_to(tf, now, Member::Alpha, vs(F32_1C), F64_0, Easing::None, None);
        }
        with_abs_end(s, k, saved);
    } else if kind == Kind::Slider {
        let saved = with_abs_begin(s, k, now, s0);
        let tf = &mut s.insts[k].tf;
        let sq = transform_to(tf, now, Member::Scale, v_xy(F32_0, F32_0), F64_0, Easing::None, None);
        seq_append(seq_then(sq), tf, now, Member::Scale, v_xy(F32_1C, F32_1C), h.preempt, Easing::InOutSine, None);
        if state == Armed::Idle {
            transform_to(tf, now, Member::Alpha, vs(F32_1C), F64_0, Easing::None, None);
        }
        with_abs_end(s, k, saved);
    }
}

/// one handler of `customState` (`vi`-th entry of `Config.visMods`)
pub fn custom_state_one(c: &Ctx, s: &mut St, i: usize, p: Part, k: usize, h: &HObj, vi: usize, state: Armed, forwarded: bool, now: F64) {
    let kind = h.kind;
    let s0 = h.start.sub(h.preempt);
    let is_circle_dho = kind == Kind::Circle || kind == Kind::Head;
    let increased = match c.first_obj[vi] {
        Some(fo) => fo == i,
        None => false,
    };
    match c.cfg.vis_mods[vi] {
        VisMod::ClassicEarlyFade => {
            if !(forwarded || !is_circle_dho || state == Armed::Hit) {
                match h.hit_windows {
                    Some(hw) => {
                        let saved = with_abs_begin(s, k, now, h.start);
                        let tf = &mut s.insts[k].tf;
                        let d = delay_seq(tf, now, hw.ok_);
                        seq_append(d, tf, now, Member::Alpha, vs(F32_0), hw.meh.sub(hw.ok_), Easing::None, None);
                        with_abs_end(s, k, saved);
                    }
                    None => {}
                }
            }
        }
        VisMod::ScaleTween(sc) => {
            if !(increased || !(kind == Kind::Circle || kind == Kind::Slider)) {
                let saved = with_abs_begin(s, k, now, s0);
                let tf = &mut s.insts[k].tf;
                let sq = transform_to(tf, now, Member::Scale, v_xy(sc, sc), F64_0, Easing::None, None);
                seq_append(seq_then(sq), tf, now, Member::Scale, v_xy(F32_1C, F32_1C), h.preempt, Easing::OutSine, None);
                with_abs_end(s, k, saved);
            }
        }
        VisMod::SpinIn => {
            if !increased {
                spin_in_state(s, k, h, kind, state, now);
            }
        }
        VisMod::TargetPractice => {
            if !(increased || !is_circle_dho) {
                let saved = with_abs_begin(s, k, now, s0);
                let tf = &mut s.insts[k].tf;
                transform_to(tf, now, Member::Scale, v_xy(F32_0_5C, F32_0_5C), F64_0, Easing::None, None);
                transform_to(tf, now, Member::Scale, v_xy(F32_1C, F32_1C), h.preempt, Easing::None, None);
                with_abs_end(s, k, saved);
            }
        }
        VisMod::Hidden(only_approach) => {
            if !only_approach {
                hidden_state(s, k, h, kind, increased, now);
            }
        }
        VisMod::Transform => {
            if kind == Kind::Circle || kind == Kind::Slider || kind == Kind::Spinner {
                transform_state(s, k, h, now);
            }
        }
        VisMod::Wiggle(strength) => wiggle_state(c, s, i, p, k, h, strength, now),
        VisMod::Inert => {}
    }
}

/// `customState`
pub fn custom_state(c: &Ctx, s: &mut St, i: usize, p: Part, state: Armed, forwarded: bool) {
    let r = part_ref(c, i, p);
    let h = hobj_of(c, r);
    let k = part_inst(s, i, p);
    let now = s.t;
    let mut vi: usize = 0;
    while vi < c.cfg.vis_mods.len() {
        custom_state_one(c, s, i, p, k, &h, vi, state, forwarded, now);
        vi += 1;
    }
}

pub const F64_800C: F64 = F64::from_bits(0x4089_0000_0000_0000);

/// the circle/head `UpdateHitStateTransforms` of `updateState`; returns the lifetime end
pub fn circle_hit_state(tf: &mut TObj, now: F64, new_state: Armed) -> F64 {
    let d = delay_seq(tf, now, F64_800C);
    let _ = seq_append(d, tf, now, Member::Alpha, vs(F32_0), F64_0, Easing::None, None);
    if new_state == Armed::Miss {
        let _ = transform_to(tf, now, Member::Alpha, vs(F32_0), F64_100, Easing::None, None);
    }
    latest_end(tf, now)
}

/// the slider `UpdateHitStateTransforms` of `updateState`; returns the lifetime end
pub fn slider_hit_state(tf: &mut TObj, body: &mut TObj, now: F64, new_state: Armed, head_hit: bool) -> F64 {
    if new_state == Armed::Hit && head_hit {
        let _ = transform_to(body, now, Member::Alpha, vs(F32_0), F64::from_bits(0x4044000000000000) /* 40 */, Easing::None, None);
    }
    let sq = transform_to(tf, now, Member::Alpha, vs(F32_0), F64_240, Easing::None, None);
    let mut tmp = tf.clone();
    abs_seq(&mut tmp, now, sq.current_time);
    latest_end(&tmp, now)
}

/// the spinner `UpdateHitStateTransforms` of `updateState`; returns the lifetime end
pub fn other_hit_state(tf: &mut TObj, now: F64) -> F64 {
    let _ = transform_to(tf, now, Member::Alpha, vs(F32_0), F64_240, Easing::None, None);
    latest_end(tf, now)
}

/// `updateState`
pub fn update_state(c: &Ctx, s: &mut St, i: usize, p: Part, new_state: Armed, force: bool, passes: u64) {
    if part_armed(s, i, p) == new_state && !force {
        return;
    }
    let now = s.t;
    let k = part_inst(s, i, p);
    let o = &c.pb.objects[i];
    let r = part_ref(c, i, p);
    let h = hobj_of(c, r);
    let hst = match res_of(s, r) {
        Some(x) => time_absolute(&h, x.time),
        None => h.end_time,
    };
    let is_slider = p == Part::Top && o.h.kind == Kind::Slider;
    let mut tf = s.insts[k].tf.clone();
    clear_state(&mut tf);
    let mut body = s.insts[k].body_tf.clone();
    if is_slider {
        clear_state(&mut body);
    }
    let t0 = h.start.sub(h.preempt);
    abs_seq(&mut tf, now, t0);
    fade_in_from_zero(&mut tf, now, F64_0, Easing::None);
    if is_slider {
        abs_seq(&mut body, now, t0);
        fade_in_from_zero(&mut body, now, h.fade_in, Easing::None);
    }
    tf.delay = F64_0;
    body.delay = F64_0;
    abs_seq(&mut tf, now, hst);
    abs_seq(&mut body, now, hst);
    let life_end = if h.kind == Kind::Circle || h.kind == Kind::Head {
        circle_hit_state(&mut tf, now, new_state)
    } else if h.kind == Kind::Slider {
        let head_hit = is_hit_ref(s, Ref { top: i, nested: c.head_idx[i] as i64 });
        slider_hit_state(&mut tf, &mut body, now, new_state, head_hit)
    } else {
        other_hit_state(&mut tf, now)
    };
    tf.delay = F64_0;
    body.delay = F64_0;
    s.insts[k].tf = tf;
    s.insts[k].body_tf = body;
    if p == Part::Top {
        s.objs[i].armed = new_state;
        s.objs[i].lifetime_end = life_end;
    } else {
        s.objs[i].head_armed = new_state;
        s.objs[i].head_lifetime_end = life_end;
    }
    custom_state(c, s, i, p, new_state, false);
    if passes >= 2 {
        custom_state(c, s, i, p, new_state, true);
    }
}

/// `tickState`
pub fn tick_state(c: &Ctx, s: &mut St, i: usize, j: usize, passes: u64, new_state: Armed, force: bool) {
    let fade_in = c.pb.objects[i].nested[j].fade_in;
    let tk = s.objs[i].tick_insts[j];
    if s.insts[tk].armed == new_state && !force {
        return;
    }
    s.insts[tk].armed = new_state;
    let mut q: u64 = 0;
    while q < passes {
        let mut vi: usize = 0;
        while vi < c.cfg.vis_mods.len() {
            match c.cfg.vis_mods[vi] {
                VisMod::Transform => {
                    s.theta = s.theta.add(fade_in.to_f32().div(F32_1000));
                }
                _ => {}
            }
            vi += 1;
        }
        q += 1;
    }
}

/// `updateStateFromResult`
pub fn update_state_from_result(c: &Ctx, s: &mut St, i: usize, p: Part, passes: u64) {
    let r = part_ref(c, i, p);
    let st2 = match res_of(s, r) {
        Some(x) => {
            if is_hit(x.ty) { Armed::Hit } else { Armed::Miss }
        }
        None => Armed::Idle,
    };
    update_state(c, s, i, p, st2, true, passes);
}

/// `applyResult`
pub fn apply_result(c: &Ctx, s: &mut St, fuel: u64, r: Ref, ty: HitResult) -> Result<(), SimErr> {
    let t = s.t;
    let h = hobj_of(c, r);
    if r.nested < 0 {
        s.objs[r.top].result = Some(Res { ty, time: t });
    } else {
        s.objs[r.top].nested[r.nested as usize] = Some(Res { ty, time: t });
    }
    // UpdateState(Hit/Miss): hit-state transforms -> lifetime (nested heads: two handler passes)
    let ns = if is_hit(ty) { Armed::Hit } else { Armed::Miss };
    match h.kind {
        Kind::Circle | Kind::Slider | Kind::Spinner => update_state(c, s, r.top, Part::Top, ns, false, 1),
        Kind::Head => update_state(c, s, r.top, Part::Head, ns, false, 2),
        Kind::SpinnerTick | Kind::SpinnerBonusTick => tick_state(c, s, r.top, r.nested as usize, 2, ns, false),
        _ => {}
    }
    adaptive_speed_on_result(c, s, r, ty, t)?;
    if fuel == 0 {
        return Err(SimErr::Internal(Internal::HandleHitDepth));
    }
    handle_hit(c, s, fuel - 1, r)?;
    emit(c, s, r, ty, t);
    Ok(())
}

/// `handleHit`
pub fn handle_hit(c: &Ctx, s: &mut St, fuel: u64, r: Ref) -> Result<(), SimErr> {
    match c.cfg.policy {
        PolicyKind::Legacy(_) => Ok(()),
        PolicyKind::StartTimeOrdered => {
            if circle_like(c, r) { handle_hit_sto(c, s, fuel, r) } else { Ok(()) }
        }
    }
}

/// `StartTimeOrderedHitPolicy.HandleHit`: miss every earlier unjudged circle-like object
pub fn handle_hit_sto(c: &Ctx, s: &mut St, fuel: u64, r: Ref) -> Result<(), SimErr> {
    let h = hobj_of(c, r);
    let objs = enumerate_up_to(c, s, h.start);
    handle_hit_sto_from(c, s, fuel, &objs, 0)
}

/// The loop of `handle_hit_sto` over `objs[k..]`, written as recursion: it is part of the mutually recursive
/// `apply_result`/`handle_hit` group, and Aeneas' `loop` combinator cannot be shown monotone inside a
/// `partial_fixpoint` group (the Lean elaborator rejects the translation).
pub fn handle_hit_sto_from(c: &Ctx, s: &mut St, fuel: u64, objs: &[Ref], k: usize) -> Result<(), SimErr> {
    if k < objs.len() {
        let o = objs[k];
        if !judged(s, o) && circle_like(c, o) {
            let oh = hobj_of(c, o);
            apply_result(c, s, fuel, o, oh.min_result)?;
        }
        handle_hit_sto_from(c, s, fuel, objs, k + 1)
    } else {
        Ok(())
    }
}

/// `maxFuel`
pub fn max_fuel(c: &Ctx) -> u64 {
    c.pb.objects.len() as u64 + 4
}

/// `hitForcefully`
pub fn hit_forcefully(c: &Ctx, s: &mut St, r: Ref) -> Result<(), SimErr> {
    let h = hobj_of(c, r);
    apply_result(c, s, max_fuel(c), r, h.max_result)
}

/// `missForcefully`
pub fn miss_forcefully(c: &Ctx, s: &mut St, r: Ref) -> Result<(), SimErr> {
    let h = hobj_of(c, r);
    apply_result(c, s, max_fuel(c), r, h.min_result)
}

// ---------------------------------------------------------------------------------------------
// Sliders (SliderInputManager)

/// `sliderData` (`need (← topObj i).slider "slider data"`)
pub fn slider_data(c: &Ctx, i: usize) -> Result<&SliderData, SimErr> {
    match &c.pb.objects[i].slider {
        Some(sd) => Ok(sd),
        None => Err(SimErr::Internal(Internal::MissingSliderData)),
    }
}

/// `mouseInFollowArea`
pub fn mouse_in_follow_area(c: &Ctx, s: &St, i: usize, expanded: bool) -> Result<bool, SimErr> {
    let o = &c.pb.objects[i];
    let sd = slider_data(c, i)?;
    let g = cur_slider_geom(c, s, i);
    is_mouse_in_follow_area(&o.h, sd, &g, s.objs[i].slider_mouse, s.t, expanded)
}

/// `a == .left || a == .right`
pub fn is_left_or_right(a: Action) -> bool {
    a == Action::Left || a == Action::Right
}

/// `isValidTrackingAction`
pub fn is_valid_tracking_action(os: &OState, t: F64, a: Action) -> bool {
    match os.hit_action {
        Some(ha) => {
            let strict = match os.accept_any_after {
                None => true,
                Some(x) => t.le(x),
            };
            if strict { a == ha } else { is_left_or_right(a) }
        }
        None => is_left_or_right(a),
    }
}

/// `pressed.any (isValidTrackingAction os t)`
pub fn any_valid_tracking_action(os: &OState, t: F64, pressed: &ActList) -> bool {
    let mut k: usize = 0;
    let mut any = false;
    while k < pressed.len {
        if is_valid_tracking_action(os, t, pressed.items[k]) {
            any = true;
        }
        k += 1;
    }
    any
}

/// `updateTracking`
pub fn update_tracking(c: &Ctx, s: &mut St, i: usize, valid_pos: bool) {
    let t = s.t;
    let pressed = s.pressed;
    let aj = all_judged(s, i);
    let end_t = c.pb.objects[i].h.end_time;
    let os = &mut s.objs[i];
    if os.hit_action.is_none() {
        os.accept_any_after = None;
    }
    match os.hit_action {
        Some(ha) => {
            if os.accept_any_after.is_none() {
                let other = if ha == Action::Right { Action::Left } else { Action::Right };
                if !act_contains(&os.last_pressed, other) {
                    os.accept_any_after = Some(t);
                }
            }
        }
        None => {}
    }
    let valid = any_valid_tracking_action(os, t, &pressed);
    os.last_pressed = pressed;
    os.tracking = (!aj || t.le(end_t)) && valid_pos && valid;
}

pub const F64_ZERO_C: F64 = F64::from_bits(0);

/// the first loop of `postProcessHeadJudgement`: whether every unjudged started nested object is in the follow area
pub fn all_nested_in_follow_area(c: &Ctx, s: &St, i: usize, m: Vec2) -> Result<bool, SimErr> {
    nested_in_follow_area_loop(s, i, &c.pb.objects[i], slider_data(c, i)?, m)
}

/// the loop of `all_nested_in_follow_area`
pub fn nested_in_follow_area_loop(s: &St, i: usize, o: &TopObj, sd: &SliderData, m: Vec2) -> Result<bool, SimErr> {
    let t = s.t;
    let mut all_in = true;
    let mut j: usize = 0;
    let mut stop = false;
    while j < o.nested.len() && !stop {
        if !judged(s, Ref { top: i, nested: j as i64 }) {
            let n_start = o.nested[j].start;
            if t.lt(n_start) {
                stop = true;
            } else {
                let radius = follow_radius(&o.h, true);
                let p0 = n_start.sub(o.h.start).div(sd.duration);
                // `Math.Clamp(…, 0, 1)`, literal bounds (`clampK`)
                let progress = f64_clamp_or(p0, F64_0, F64_1);
                let pos = curve_position_at(sd, progress)?;
                if radius.mul(radius).lt(pos.sub(m).length_squared()) {
                    all_in = false;
                    stop = true;
                }
            }
        }
        j += 1;
    }
    Ok(all_in)
}

/// the second loop of `postProcessHeadJudgement`
pub fn judge_started_nested(c: &Ctx, s: &mut St, i: usize, all_in: bool) -> Result<(), SimErr> {
    let n_nested = c.pb.objects[i].nested.len();
    let mut j: usize = 0;
    let mut stop = false;
    while j < n_nested && !stop {
        let r = Ref { top: i, nested: j as i64 };
        if !judged(s, r) {
            let n_start = c.pb.objects[i].nested[j].start;
            if s.t.lt(n_start) {
                stop = true;
            } else if all_in {
                hit_forcefully(c, s, r)?;
            } else {
                miss_forcefully(c, s, r)?;
            }
        }
        j += 1;
    }
    Ok(())
}

/// `postProcessHeadJudgement`
pub fn post_process_head_judgement(c: &Ctx, s: &mut St, i: usize) -> Result<(), SimErr> {
    let head_ref = Ref { top: i, nested: c.head_idx[i] as i64 };
    if !judged(s, head_ref) || !is_hit_ref(s, head_ref) {
        return Ok(());
    }
    if !mouse_in_follow_area(c, s, i, true)? {
        return Ok(());
    }
    let g = cur_slider_geom(c, s, i);
    let mouse = match s.objs[i].slider_mouse {
        Some(m) => m,
        None => {
            return Ok(());
        }
    };
    let m = mouse_in_slider(&g, mouse);
    let all_in = all_nested_in_follow_area(c, s, i, m)?;
    judge_started_nested(c, s, i, all_in)?;
    let in_ball = mouse_in_follow_area(c, s, i, false)?;
    update_tracking(c, s, i, all_in || in_ball);
    Ok(())
}

/// `SliderEventGenerator.TAIL_LENIENCY` = -36
pub const TAIL_LENIENCY: F64 = F64::from_bits(0xC042_0000_0000_0000);

/// last index of a tick or repeat (`lastTick` of `tryJudgeNested`)
pub fn last_tick_index(o: &TopObj) -> Option<usize> {
    let mut last: Option<usize> = None;
    let mut k: usize = 0;
    while k < o.nested.len() {
        let kd = o.nested[k].kind;
        if kd == Kind::Tick || kd == Kind::Repeat {
            last = Some(k);
        }
        k += 1;
    }
    last
}

/// `tryJudgeNested`
pub fn try_judge_nested(c: &Ctx, s: &mut St, i: usize, j: usize) -> Result<(), SimErr> {
    let o = &c.pb.objects[i];
    let n = &o.nested[j];
    let t = s.t;
    let offset = t.sub(n.end_time);
    let proceed = match n.kind {
        Kind::Tick | Kind::Repeat => !offset.lt(F64_0),
        Kind::Tail => {
            if offset.lt(TAIL_LENIENCY) {
                false
            } else {
                match last_tick_index(o) {
                    Some(k) => judged(s, Ref { top: i, nested: k as i64 }),
                    None => true,
                }
            }
        }
        _ => false,
    };
    if !proceed {
        return Ok(());
    }
    if !judged(s, Ref { top: i, nested: c.head_idx[i] as i64 }) {
        return Ok(());
    }
    let r = Ref { top: i, nested: j as i64 };
    if s.objs[i].tracking {
        hit_forcefully(c, s, r)?;
    } else if F64_0.le(offset) {
        miss_forcefully(c, s, r)?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// Circles and slider heads

/// `circleCheckForResult`
pub fn circle_check_for_result(c: &Ctx, s: &mut St, r: Ref, user_triggered: bool) -> Result<(), SimErr> {
    let h = hobj_of(c, r);
    let t = s.t;
    let offset = t.sub(h.end_time);
    let hw = match h.hit_windows {
        Some(hw) => hw,
        None => {
            return Ok(());
        }
    };
    if !user_triggered {
        if !can_be_hit(&hw, offset) {
            miss_forcefully(c, s, r)?;
        }
    } else {
        let base = result_for(&hw, offset);
        let classic_head = is_classic_head(c, r.top, h.kind)?;
        let result = if classic_head {
            if is_hit(base) { HitResult::LargeTickHit } else { HitResult::LargeTickMiss }
        } else {
            base
        };
        let action = check_hittable(c, s, r, t, result);
        if !(result == HitResult::None || action != ClickAction::Hit) {
            apply_result(c, s, max_fuel(c), r, result)?;
        }
    }
    if h.kind == Kind::Head {
        post_process_head_judgement(c, s, r.top)?;
    }
    Ok(())
}

/// `classicHead` of `circleCheckForResult` (no `&&` with a nested `(← …)` in the spec: `sliderData` only for heads)
pub fn is_classic_head(c: &Ctx, i: usize, kind: Kind) -> Result<bool, SimErr> {
    if kind == Kind::Head {
        let sd = slider_data(c, i)?;
        Ok(sd.classic)
    } else {
        Ok(false)
    }
}

/// `circleUpdateResult`
pub fn circle_update_result(c: &Ctx, s: &mut St, r: Ref, user_triggered: bool) -> Result<(), SimErr> {
    if judged(s, r) {
        return Ok(());
    }
    circle_check_for_result(c, s, r, user_triggered)
}

/// number of hit nested results
pub fn count_nested_hits(os: &OState) -> u64 {
    let mut n: u64 = 0;
    let mut k: usize = 0;
    while k < os.nested.len() {
        match os.nested[k] {
            Some(x) => {
                if is_hit(x.ty) {
                    n += 1;
                }
            }
            None => {}
        }
        k += 1;
    }
    n
}

/// `sliderCheckForResult`
pub fn slider_check_for_result(c: &Ctx, s: &mut St, i: usize) -> Result<(), SimErr> {
    let o = &c.pb.objects[i];
    let t = s.t;
    let tail_j = judged(s, Ref { top: i, nested: c.tail_idx[i] as i64 });
    if !tail_j || t.lt(o.h.end_time) {
        return Ok(());
    }
    let classic = slider_data(c, i)?.classic;
    let total = o.nested.len() as u64;
    let hits = count_nested_hits(&s.objs[i]);
    let ty = slider_result(classic, hits, total, o.h.max_result, o.h.min_result);
    apply_result(c, s, max_fuel(c), Ref { top: i, nested: -1 }, ty)
}

/// the result computation of `sliderCheckForResult`
pub fn slider_result(classic: bool, hits: u64, total: u64, max_result: HitResult, min_result: HitResult) -> HitResult {
    if classic {
        if hits == total {
            HitResult::Great
        } else if hits == 0 {
            HitResult::Miss
        } else {
            let frac = F64::from_u64(hits).div(F64::from_u64(total));
            if F64::from_bits(0x3FE0000000000000) /* 0.5 */.le(frac) { HitResult::Ok_ } else { HitResult::Meh }
        }
    } else if hits > 0 {
        max_result
    } else {
        min_result
    }
}

// ---------------------------------------------------------------------------------------------
// Per-step DHO updates

/// the `for j` loop of `updateSlider` for one nested kind
pub fn update_slider_nested_kind(c: &Ctx, s: &mut St, i: usize, kind: Kind) -> Result<(), SimErr> {
    let n_nested = c.pb.objects[i].nested.len();
    let mut j: usize = 0;
    while j < n_nested {
        if c.pb.objects[i].nested[j].kind == kind && !judged(s, Ref { top: i, nested: j as i64 }) {
            try_judge_nested(c, s, i, j)?;
        }
        j += 1;
    }
    Ok(())
}

/// the StrictTracking branch of `updateSlider`: miss the first `StrictTrackingSliderTailCircle` if unjudged
pub fn strict_tracking_miss(c: &Ctx, s: &mut St, i: usize) -> Result<(), SimErr> {
    let n = c.pb.objects[i].nested.len();
    let mut j: usize = 0;
    let mut done = false;
    while j < n && !done {
        if c.pb.objects[i].nested[j].strict_tail {
            let r = Ref { top: i, nested: j as i64 };
            if !judged(s, r) {
                miss_forcefully(c, s, r)?;
            }
            done = true;
        }
        j += 1;
    }
    Ok(())
}

/// `updateSlider`
pub fn update_slider(c: &Ctx, s: &mut St, i: usize) -> Result<(), SimErr> {
    let t = s.t;
    let k = s.objs[i].inst;
    let os_tracking = s.objs[i].tracking;
    let os_unjudged = s.objs[i].result.is_none();
    // DrawableSlider.Update: `Tracking.Value = SliderInputManager.Tracking` (bindable on the pooled instance)
    if os_tracking != s.insts[k].drawable_tracking {
        s.insts[k].drawable_tracking = os_tracking;
        // OsuModStrictTracking: on true -> false (unless judged or before StartTime) miss the strict tail
        if c.cfg.strict_tracking && !os_tracking && os_unjudged && !t.lt(c.pb.objects[i].h.start) {
            strict_tracking_miss(c, s, i)?;
        }
    }
    let tr = s.objs[i].tracking;
    let in_area = mouse_in_follow_area(c, s, i, tr)?;
    update_tracking(c, s, i, in_area);
    slider_body_update(c, s, i, k, t)?;
    update_slider_nested_kind(c, s, i, Kind::Tick)?;
    update_slider_nested_kind(c, s, i, Kind::Repeat)?;
    update_slider_nested_kind(c, s, i, Kind::Tail)?;
    let hj = c.head_idx[i];
    let head = c.pb.objects[i].nested[hj];
    let head_alive = !t.lt(head.start.sub(head.preempt)) && t.lt(s.objs[i].head_lifetime_end);
    s.objs[i].head_alive = head_alive;
    if head_alive {
        let hk = s.objs[i].head_inst;
        if !s.insts[hk].loaded {
            s.insts[hk].loaded = true;
            update_state_from_result(c, s, i, Part::Head, 2);
        }
        update_transforms(&mut s.insts[hk].tf, t, false);
        if part_present(c, s, i, Part::Head) {
            circle_update_result(c, s, Ref { top: i, nested: hj as i64 }, false)?;
        }
    }
    // DrawableSlider.UpdateAfterChildren: Size/OriginPosition from the body, head RelativeAnchorPosition, ball position
    let sd = slider_data(c, i)?;
    let p0 = t.sub(c.pb.objects[i].h.start).div(sd.duration);
    let prog = clamp_net(p0, F64_0, F64_1)?;
    let ball = curve_position_at(sd, prog)?;
    let ins = &mut s.insts[k];
    ins.size = ins.body_size;
    ins.origin = ins.body_offset;
    ins.rel_anchor = ins.body_offset.cdiv(ins.body_size);
    ins.ball_pos = ball;
    if s.objs[i].result.is_none() {
        slider_check_for_result(c, s, i)?;
    }
    Ok(())
}

/// the slider body part of `updateSlider` (first update = LoadComplete with the argon radius; transforms; the
/// scheduled `Refresh` only while the body is present)
pub fn slider_body_update(c: &Ctx, s: &mut St, i: usize, k: usize, t: F64) -> Result<(), SimErr> {
    let sd = slider_data(c, i)?;
    let scale = c.pb.objects[i].h.scale;
    let ins = &mut s.insts[k];
    if !ins.body_loaded {
        let r = c.env.argon_path_radius.mul(scale);
        ins.body_loaded = true;
        if !ins.body_radius.eq(r) {
            let (sz, off) = body_refresh(sd, r)?;
            ins.body_radius = r;
            ins.body_size = sz;
            ins.body_offset = off;
        }
    }
    update_transforms(&mut ins.body_tf, t, false);
    if ins.refresh_pending
        && ALPHA_PRESENT.lt(ins.body_tf.alpha)
        && !ins.body_tf.scale.x.eq(F32_0)
        && !ins.body_tf.scale.y.eq(F32_0)
    {
        let (sz, off) = body_refresh(sd, ins.body_radius)?;
        ins.refresh_pending = false;
        ins.body_size = sz;
        ins.body_offset = off;
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// Spinners

pub const F32_360: F32 = F32::from_bits(0x43B4_0000);
pub const F32_180C: F32 = F32::from_bits(0x4334_0000);

/// `totalRotation`
pub fn total_rotation(os: &OState) -> F32 {
    F32::from_i64(360 * os.completed_spins as i64).add(os.current_spin_max)
}

/// `spinnerProgress`
pub fn spinner_progress(sp: &SpinnerData, os: &OState) -> F32 {
    if sp.spins_required == 0 {
        F32_1
    } else {
        let p = total_rotation(os).div(F32_360).div(F32::from_i64(sp.spins_required));
        // `Math.Clamp(p, 0, 1)`: literal bounds, the throwing branch is dead
        f32_clamp_or(p, F32_0, F32_1)
    }
}

/// `reportDelta` (in place)
pub fn report_delta(os: &mut OState, t: F64, delta: F32) -> Result<(), SimErr> {
    if delta.eq(F32_0) {
        return Ok(());
    }
    os.total_accumulated = os.total_accumulated.add(delta);
    if os.last_report_time.le(t) {
        let cur = os.total_accumulated.sub(os.accumulated_at_last_completion);
        os.current_spin_max = f32_max(os.current_spin_max, cur.abs());
        let mut fuel: u32 = 1000000;
        while F32_360.le(os.current_spin_max) && fuel > 0 {
            fuel -= 1;
            let cur2 = os.total_accumulated.sub(os.accumulated_at_last_completion);
            // `Math.Sign(float)` throws on NaN
            let dir: i64 = match crate::net::mathops::f32_sign(cur2) {
                Ok(v) => v as i64,
                Err(e) => return Err(SimErr::SignSpin(e)),
            };
            os.completed_spins += 1;
            os.accumulated_at_last_completion = os.accumulated_at_last_completion.add(F32::from_i64(dir * 360));
            os.current_spin_max = os.total_accumulated.sub(os.accumulated_at_last_completion).abs();
        }
        if fuel == 0 && F32_360.le(os.current_spin_max) {
            return Err(SimErr::Internal(Internal::ReportDeltaFuel));
        }
    } else {
        os.current_spin_max = os.total_accumulated.sub(os.accumulated_at_last_completion).abs();
    }
    os.last_report_time = t;
    Ok(())
}

/// first unjudged nested index
pub fn first_unjudged_nested(s: &St, i: usize) -> Option<usize> {
    os_first_unjudged_nested(&s.objs[i])
}

/// first unjudged nested index of one object state
pub fn os_first_unjudged_nested(os: &OState) -> Option<usize> {
    let mut j: usize = 0;
    let mut found: Option<usize> = None;
    while j < os.nested.len() && found.is_none() {
        if os.nested[j].is_none() {
            found = Some(j);
        }
        j += 1;
    }
    found
}

/// `updateBonusScore`
pub fn update_bonus_score(c: &Ctx, s: &mut St, i: usize) -> Result<(), SimErr> {
    if c.pb.objects[i].nested.len() == 0 {
        return Ok(());
    }
    let spins: i64 = total_rotation(&s.objs[i]).div(F32_360).to_i32_sat() as i64;
    if spins < s.objs[i].completed_full_spins {
        s.objs[i].completed_full_spins = spins;
        return Ok(());
    }
    let fuel = bonus_spins(c, s, i, spins)?;
    if fuel == 0 && s.objs[i].completed_full_spins != spins {
        return Err(SimErr::Internal(Internal::BonusFuel));
    }
    Ok(())
}

/// the loop of `updateBonusScore`; returns the fuel left
pub fn bonus_spins(c: &Ctx, s: &mut St, i: usize, spins: i64) -> Result<u32, SimErr> {
    let mut fuel: u32 = 10000000;
    while fuel > 0 && s.objs[i].completed_full_spins != spins {
        fuel -= 1;
        bonus_spin(c, s, i)?;
    }
    Ok(fuel)
}

/// one completed full spin of `updateBonusScore`: hit the first unjudged tick, count the spin
pub fn bonus_spin(c: &Ctx, s: &mut St, i: usize) -> Result<(), SimErr> {
    match first_unjudged_nested(s, i) {
        Some(j) => {
            hit_forcefully(c, s, Ref { top: i, nested: j as i64 })?;
        }
        None => {}
    }
    s.objs[i].completed_full_spins += 1;
    Ok(())
}

/// miss every unjudged nested object (spinner end)
pub fn miss_unjudged_nested(c: &Ctx, s: &mut St, i: usize) -> Result<(), SimErr> {
    let n = c.pb.objects[i].nested.len();
    let mut j: usize = 0;
    while j < n {
        let r = Ref { top: i, nested: j as i64 };
        if !judged(s, r) {
            miss_forcefully(c, s, r)?;
        }
        j += 1;
    }
    Ok(())
}

/// the spinner result by progress (`CheckForResult` at the end)
pub fn spinner_result(o: &TopObj, sp: &SpinnerData, os: &OState) -> HitResult {
    let p = spinner_progress(sp, os);
    if F32_1.le(p) {
        HitResult::Great
    } else if F64::from_bits(0x3FECCCCCCCCCCCCD) /* 0.9 */.lt(p.to_f64()) {
        HitResult::Ok_
    } else if F64::from_bits(0x3FE8000000000000) /* 0.75 */.lt(p.to_f64()) {
        HitResult::Meh
    } else {
        o.h.min_result
    }
}

/// `SpinnerRotationTracker.Update` part of `updateSpinner`
pub fn spinner_tracker_update(c: &Ctx, s: &mut St, i: usize, spinnable: bool) -> Result<(), SimErr> {
    let g = cur_spinner_geom(c, s, i);
    let t = s.t;
    let rate = true_rate(&c.cfg, &s.speed);
    let os = &mut s.objs[i];
    match os.spin_mouse {
        Some(pos) => {
            let this_angle = radians_to_degrees(
                pos.x.sub(g.tracker_size.x.div(F32_2)).atan2(pos.y.sub(g.tracker_size.y.div(F32_2))),
            )
            .neg();
            let mut delta = match os.last_angle {
                None => F32_0,
                Some(la) => this_angle.sub(la),
            };
            if F32_180C.lt(delta) {
                delta = delta.sub(F32_360);
            }
            if delta.lt(F32_180C.neg()) {
                delta = delta.add(F32_360);
            }
            if os.spin_tracking && spinnable {
                let d = delta.to_f64().mul(rate.abs()).to_f32();
                report_delta(os, t, d)?;
            }
            os.last_angle = Some(this_angle);
        }
        None => {}
    }
    Ok(())
}

pub const F32_2C: F32 = F32::from_bits(0x4000_0000);

/// `DrawableSpinner.Update` tick lifetimes + the ticks container update (a fresh tick instance's first update is
/// `LoadComplete`: two handler passes)
pub fn spinner_ticks_update(c: &Ctx, s: &mut St, i: usize) {
    let t = s.t;
    match first_unjudged_nested(s, i) {
        Some(j) => {
            s.objs[i].tick_live[j] = true;
        }
        None => {}
    }
    let n = c.pb.objects[i].nested.len();
    let start = c.pb.objects[i].h.start;
    let mut j: usize = 0;
    while j < n {
        if s.objs[i].tick_live[j] && start.le(t) && !judged(s, Ref { top: i, nested: j as i64 }) {
            let tk = s.objs[i].tick_insts[j];
            if !s.insts[tk].loaded {
                s.insts[tk].loaded = true;
                tick_state(c, s, i, j, 2, Armed::Idle, true);
            }
        }
        j += 1;
    }
}

/// the SpunOut rotation of `updateSpinner` (`OsuModSpunOut.cs:35-54`)
pub fn spun_out_update(c: &Ctx, s: &mut St, i: usize, sp: &SpinnerData, spinnable: bool) -> Result<(), SimErr> {
    if !almost_equals_d(s.clock_rate, F64_0) {
        let elapsed = if s.k == 0 { F64_0 } else { s.t.sub(c.steps[s.k - 1].time) };
        let e = elapsed.div(s.clock_rate);
        let speed = F64::from_bits(0x3FF028F5C28F5C29) /* 1.01 */.mul(F64::from_i64(sp.spins_required)).div(sp.duration).to_f32();
        let deg = radians_to_degrees(e.to_f32().mul(speed).mul(F32_PI).mul(F32_2C));
        if spinnable {
            let d = deg.to_f64().mul(true_rate(&c.cfg, &s.speed).abs()).to_f32();
            let t = s.t;
            report_delta(&mut s.objs[i], t, d)?;
        }
    }
    Ok(())
}

/// `updateSpinner`
pub fn update_spinner(c: &Ctx, s: &mut St, i: usize) -> Result<(), SimErr> {
    if s.objs[i].result.is_some() {
        return Ok(());
    }
    let o = &c.pb.objects[i];
    let sp = match o.spinner {
        Some(sp) => sp,
        None => {
            return Ok(());
        }
    };
    let t = s.t;
    let spinnable = o.h.start.le(t) && t.lt(o.h.end_time);
    if !c.cfg.spun_out {
        let tracking = spinnable
            && s.objs[i].result.is_none()
            && (act_contains(&s.pressed, Action::Left) || act_contains(&s.pressed, Action::Right));
        s.objs[i].spin_tracking = tracking;
    } else {
        // OsuModSpunOut.onSpinnerUpdate
        s.objs[i].spin_tracking = spinnable;
        spun_out_update(c, s, i, &sp, spinnable)?;
    }
    spinner_ticks_update(c, s, i);
    spinner_tracker_update(c, s, i, spinnable)?;
    if s.objs[i].result.is_none() && o.h.start.le(t) && !t.lt(o.h.end_time) {
        miss_unjudged_nested(c, s, i)?;
        let ty = spinner_result(o, &sp, &s.objs[i]);
        apply_result(c, s, max_fuel(c), Ref { top: i, nested: -1 }, ty)?;
    }
    update_bonus_score(c, s, i)
}

/// `updateDho`
pub fn update_dho(c: &Ctx, s: &mut St, i: usize) -> Result<(), SimErr> {
    let k = s.objs[i].inst;
    if !s.insts[k].loaded {
        s.insts[k].loaded = true;
        update_state_from_result(c, s, i, Part::Top, 1);
    }
    let t = s.t;
    update_transforms(&mut s.insts[k].tf, t, false);
    if !part_present(c, s, i, Part::Top) {
        return Ok(());
    }
    match c.pb.objects[i].h.kind {
        Kind::Circle => circle_update_result(c, s, Ref { top: i, nested: -1 }, false),
        Kind::Slider => update_slider(c, s, i),
        Kind::Spinner => update_spinner(c, s, i),
        _ => Ok(()),
    }
}

/// `onKilled`
pub fn on_killed(c: &Ctx, s: &mut St, i: usize) -> Result<(), SimErr> {
    let o = &c.pb.objects[i];
    match o.h.kind {
        Kind::Circle => circle_update_result(c, s, Ref { top: i, nested: -1 }, false)?,
        Kind::Slider => {
            let mut j: usize = 0;
            while j < c.pb.objects[i].nested.len() {
                let r = Ref { top: i, nested: j as i64 };
                if !judged(s, r) {
                    if c.pb.objects[i].nested[j].kind == Kind::Head {
                        circle_update_result(c, s, r, false)?;
                    } else {
                        try_judge_nested(c, s, i, j)?;
                    }
                }
                j += 1;
            }
            if s.objs[i].result.is_none() {
                slider_check_for_result(c, s, i)?;
            }
        }
        Kind::Spinner => {
            let t = s.t;
            if s.objs[i].result.is_none() && o.h.start.le(t) && !t.lt(o.h.end_time) {
                miss_unjudged_nested(c, s, i)?;
                match o.spinner {
                    Some(sp) => {
                        let ty = spinner_result(o, &sp, &s.objs[i]);
                        apply_result(c, s, max_fuel(c), Ref { top: i, nested: -1 }, ty)?;
                    }
                    None => {}
                }
            }
        }
        _ => {}
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// Lifetime management

/// index of the first nested slider head
pub fn first_head(o: &TopObj) -> Option<usize> {
    let mut j: usize = 0;
    let mut found: Option<usize> = None;
    while j < o.nested.len() && found.is_none() {
        if o.nested[j].kind == Kind::Head {
            found = Some(j);
        }
        j += 1;
    }
    found
}

/// `becameAlive`
pub fn became_alive(c: &Ctx, s: &mut St, i: usize) -> Result<(), SimErr> {
    let kind = c.pb.objects[i].h.kind;
    match s.free_list.pop() {
        Some(slot) => {
            s.dict_slots[slot] = Some(i);
        }
        None => {
            s.dict_slots.push(Some(i));
        }
    }
    s.child_counter += 1;
    s.active.push(i);
    let cid = s.child_counter;
    let k = pool_get(s, pool_kind(kind));
    let hk = if kind == Kind::Slider { pool_get(s, 2) } else { 0 };
    let a0 = s.insts[k].armed;
    let ha0 = if kind == Kind::Slider { s.insts[hk].armed } else { Armed::Idle };
    let os = &mut s.objs[i];
    os.armed = a0;
    os.head_armed = ha0;
    os.life = Life::Alive;
    os.child_id = cid;
    os.hit_action = None;
    os.inst = k;
    os.head_inst = hk;
    os.hovered = false;
    os.tracking = false;
    os.accept_any_after = None;
    os.last_pressed = ACTLIST_EMPTY;
    os.slider_mouse = None;
    os.head_alive = false;
    os.head_lifetime_end = netx::F64_POS_INF;
    os.spin_tracking = false;
    os.spin_mouse = None;
    os.last_angle = None;
    os.total_accumulated = F32_0;
    os.accumulated_at_last_completion = F32_0;
    os.current_spin_max = F32_0;
    os.completed_spins = 0;
    os.last_report_time = netx::F64_NEG_INF;
    os.completed_full_spins = 0;
    // `Apply` runs `updateStateFromResult` only if the pooled instance is already loaded
    if kind == Kind::Slider {
        apply_bindings(c, s, i, Part::Head, hk)?;
        if s.insts[hk].loaded {
            update_state_from_result(c, s, i, Part::Head, 1);
        }
    }
    if kind == Kind::Spinner {
        spinner_ticks_get(c, s, i);
    }
    apply_bindings(c, s, i, Part::Top, k)?;
    if s.insts[k].loaded {
        update_state_from_result(c, s, i, Part::Top, 1);
    }
    Ok(())
}

/// the spinner-tick part of `becameAlive`: pooled tick instances, then their `Apply` state updates
pub fn spinner_ticks_get(c: &Ctx, s: &mut St, i: usize) {
    let n = c.pb.objects[i].nested.len();
    let mut tis: Vec<usize> = Vec::new();
    let mut live: Vec<bool> = Vec::new();
    let mut j: usize = 0;
    while j < n {
        let pk = if c.pb.objects[i].nested[j].kind == Kind::SpinnerBonusTick { 5 } else { 4 };
        tis.push(pool_get(s, pk));
        live.push(false);
        j += 1;
    }
    s.objs[i].tick_insts = tis;
    s.objs[i].tick_live = live;
    let mut q: usize = 0;
    while q < n {
        let tk = s.objs[i].tick_insts[q];
        if s.insts[tk].loaded {
            tick_state(c, s, i, q, 1, Armed::Idle, true);
        }
        q += 1;
    }
}

/// the `vEq` of `applyBindings` (bindable `Equals`: `==` or both NaN, per component)
pub fn v_eq_bindable(a: Vec2, b: Vec2) -> bool {
    (a.x.eq(b.x) || (a.x.is_nan() && b.x.is_nan())) && (a.y.eq(b.y) || (a.y.is_nan() && b.y.is_nan()))
}

/// `applyBindings`
pub fn apply_bindings(c: &Ctx, s: &mut St, i: usize, p: Part, k: usize) -> Result<(), SimErr> {
    let o = &c.pb.objects[i];
    let h = if p == Part::Top { o.h } else { o.nested[c.head_idx[i]] };
    let ins = &mut s.insts[k];
    let pos_changed = !v_eq_bindable(ins.bound_pos, h.pos);
    ins.bound_pos = h.pos;
    if pos_changed {
        if h.kind == Kind::Circle || h.kind == Kind::Slider {
            tobj_set(&mut ins.tf, Member::Position, h.stacked);
        } else if h.kind == Kind::Spinner {
            tobj_set(&mut ins.tf, Member::Position, h.pos);
        }
    }
    if h.kind != Kind::Spinner {
        let stack_changed = ins.bound_stack != h.stack_height;
        ins.bound_stack = h.stack_height;
        if stack_changed && (h.kind == Kind::Circle || h.kind == Kind::Slider) {
            tobj_set(&mut ins.tf, Member::Position, h.stacked);
        }
    }
    let scale_changed = !(ins.bound_scale.eq(h.scale) || (ins.bound_scale.is_nan() && h.scale.is_nan()));
    ins.bound_scale = h.scale;
    if p == Part::Top && o.h.kind == Kind::Slider {
        let sd = slider_data(c, i)?;
        if scale_changed {
            let r1 = OBJECT_RADIUS.mul(h.scale);
            if !ins.body_radius.eq(r1) {
                let (sz, off) = body_refresh(sd, r1)?;
                ins.body_radius = r1;
                ins.body_size = sz;
                ins.body_offset = off;
            }
            if ins.body_loaded {
                let r2 = c.env.argon_path_radius.mul(h.scale);
                if !ins.body_radius.eq(r2) {
                    let (sz, off) = body_refresh(sd, r2)?;
                    ins.body_radius = r2;
                    ins.body_size = sz;
                    ins.body_offset = off;
                }
            }
        }
        ins.refresh_pending = true;
    }
    Ok(())
}

/// `dictSlots.idxOf? (some i)`
pub fn dict_slot_of(s: &St, i: usize) -> Option<usize> {
    let mut k: usize = 0;
    let mut found: Option<usize> = None;
    while k < s.dict_slots.len() && found.is_none() {
        match s.dict_slots[k] {
            Some(x) => {
                if x == i {
                    found = Some(k);
                }
            }
            None => {}
        }
        k += 1;
    }
    found
}

/// `becameDead`
pub fn became_dead(c: &Ctx, s: &mut St, i: usize) -> Result<(), SimErr> {
    match dict_slot_of(s, i) {
        Some(slot) => {
            s.dict_slots[slot] = None;
            s.free_list.push(slot);
        }
        None => {
            return Err(SimErr::Internal(Internal::DeadNotAlive(i)));
        }
    }
    s.objs[i].life = Life::Past;
    on_killed(c, s, i)?;
    // removal -> `Return` -> `OnFree` (nested heads first, then clearExistingStateTransforms) -> pool
    let kind = c.pb.objects[i].h.kind;
    if kind == Kind::Slider {
        let hk = s.objs[i].head_inst;
        clear_state(&mut s.insts[hk].tf);
        s.insts[hk].armed = s.objs[i].head_armed;
        pool_return(s, 2, hk);
    }
    if kind == Kind::Spinner {
        let mut j: usize = 0;
        while j < s.objs[i].tick_insts.len() {
            let pk = if c.pb.objects[i].nested[j].kind == Kind::SpinnerBonusTick { 5 } else { 4 };
            let tk = s.objs[i].tick_insts[j];
            pool_return(s, pk, tk);
            j += 1;
        }
    }
    let k = s.objs[i].inst;
    clear_state(&mut s.insts[k].tf);
    clear_state(&mut s.insts[k].body_tf);
    s.insts[k].armed = s.objs[i].armed;
    pool_return(s, pool_kind(kind), k);
    Ok(())
}

/// `stableSortBy fut (lifetimeStart <)`
pub fn sort_by_lifetime_start(s: &St, xs: &[usize]) -> Vec<usize> {
    let mut out: Vec<usize> = Vec::new();
    let mut k: usize = 0;
    while k < xs.len() {
        let x = xs[k];
        let lx = s.objs[x].lifetime_start;
        let mut i = out.len();
        while i > 0 && lx.lt(s.objs[out[i - 1]].lifetime_start) {
            i -= 1;
        }
        insert_idx(&mut out, i, x);
        k += 1;
    }
    out
}

/// the first-update branch of `lifetimeUpdate`
pub fn lifetime_first_update(c: &Ctx, s: &mut St) -> Result<(), SimErr> {
    let t = s.t;
    s.first_lifetime_update = false;
    let mut fut: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < c.pb.objects.len() {
        if t.lt(s.objs[i].lifetime_start) {
            fut.push(i);
        } else if s.objs[i].lifetime_end.le(t) {
            s.objs[i].life = Life::Past;
        } else {
            became_alive(c, s, i)?;
        }
        i += 1;
    }
    let sorted = sort_by_lifetime_start(s, &fut);
    s.future_order = sorted;
    s.next_future = 0;
    Ok(())
}

/// the later-update branch of `lifetimeUpdate`
pub fn lifetime_future_update(c: &Ctx, s: &mut St) -> Result<(), SimErr> {
    let t = s.t;
    let mut fuel = c.pb.objects.len() + 1;
    let mut stop = false;
    while fuel > 0 && !stop {
        fuel -= 1;
        if s.next_future < s.future_order.len() {
            let i = s.future_order[s.next_future];
            if t.lt(s.objs[i].lifetime_start) {
                stop = true;
            } else {
                s.next_future += 1;
                if s.objs[i].lifetime_end.le(t) {
                    s.objs[i].life = Life::Past;
                } else {
                    became_alive(c, s, i)?;
                }
            }
        } else {
            stop = true;
        }
    }
    Ok(())
}

/// `lifetimeUpdate`
pub fn lifetime_update(c: &Ctx, s: &mut St) -> Result<(), SimErr> {
    let t = s.t;
    if s.first_lifetime_update {
        lifetime_first_update(c, s)?;
    } else {
        lifetime_future_update(c, s)?;
    }
    let snapshot = s.active.clone();
    let mut k: usize = 0;
    while k < snapshot.len() {
        let i = snapshot[k];
        if s.objs[i].lifetime_end.le(t) || t.lt(s.objs[i].lifetime_start) {
            became_dead(c, s, i)?;
        }
        k += 1;
    }
    let mut kept: Vec<usize> = Vec::new();
    let mut m: usize = 0;
    while m < s.active.len() {
        let i = s.active[m];
        if s.objs[i].life == Life::Alive {
            kept.push(i);
        }
        m += 1;
    }
    s.active = kept;
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// Input

/// `interpolate` (`Interpolation.ValueAt`)
pub fn interpolate(time: F64, v1: Vec2, v2: Vec2, t0: F64, t1: F64) -> Vec2 {
    let current = time.sub(t0).to_f32();
    let duration = t1.sub(t0).to_f32();
    if duration.eq(F32_0) || current.eq(F32_0) {
        v1
    } else {
        let tt = current.div(duration);
        v1.add(v2.sub(v1).scale(tt))
    }
}

/// `replayPosition`
pub fn replay_position(frames: &[Frame], idx: i64, t: F64) -> Vec2 {
    let a = if idx < 0 { 0 } else { idx };
    let last = frames.len() as i64 - 1;
    let b = if idx + 1 < last { idx + 1 } else { last };
    let sf = &frames[a as usize];
    let ef = &frames[b as usize];
    interpolate(t, sf.pos, ef.pos, sf.time, ef.time)
}

/// `updateHover`
pub fn update_hover(c: &Ctx, s: &mut St) {
    let mouse = s.mouse;
    let mut i: usize = 0;
    while i < c.pb.objects.len() {
        let hov = if s.objs[i].life != Life::Alive {
            false
        } else {
            match c.pb.objects[i].h.kind {
                Kind::Circle => receptor_contains(&cur_circle_receptor(c, s, i), mouse, c.corner_pow),
                Kind::Slider => {
                    s.objs[i].head_alive
                        && receptor_contains(&cur_slider_geom(c, s, i).head_receptor, mouse, c.corner_pow)
                }
                _ => false,
            }
        };
        if hov != s.objs[i].hovered {
            s.objs[i].hovered = hov;
        }
        i += 1;
    }
}

/// `sliderMouseMove`
pub fn slider_mouse_move(c: &Ctx, s: &mut St) {
    let mut k: usize = 0;
    while k < s.active.len() {
        let i = s.active[k];
        if c.pb.objects[i].h.kind == Kind::Slider {
            s.objs[i].slider_mouse = Some(s.mouse);
        }
        k += 1;
    }
}

/// `spinnerMouseMove`
pub fn spinner_mouse_move(c: &Ctx, s: &mut St) {
    if c.cfg.spun_out {
        return;
    }
    let mut k: usize = 0;
    while k < s.active.len() {
        let i = s.active[k];
        if c.pb.objects[i].h.kind == Kind::Spinner {
            let g = cur_spinner_geom(c, s, i);
            s.objs[i].spin_mouse = Some(to_local(&g.aspect, s.mouse));
        }
        k += 1;
    }
}

/// `receptorCanBeHit`
pub fn receptor_can_be_hit(c: &Ctx, s: &St, r: Ref) -> bool {
    if r.nested < 0 || c.cfg.classic_head_block {
        !all_judged(s, r.top)
    } else {
        !judged(s, r)
    }
}

/// The HitReceptor of an alive DHO in the input queue (circle, or the alive slider head).
pub fn receptor_ref(c: &Ctx, s: &St, i: usize) -> Option<Ref> {
    match c.pb.objects[i].h.kind {
        Kind::Circle => Some(Ref { top: i, nested: -1 }),
        Kind::Slider => {
            if s.objs[i].head_alive { Some(Ref { top: i, nested: c.head_idx[i] as i64 }) } else { None }
        }
        _ => None,
    }
}

/// `interceptPress`: whether the k-th AL/SG blocks the press
pub fn intercept_press(c: &Ctx, s: &mut St, k: usize, a: Action) -> bool {
    let (in_any, idx) = period_is_in_any(&c.block_periods, s.block_idx[k], s.t);
    s.block_idx[k] = idx;
    if in_any {
        false
    } else if !is_left_or_right(a) {
        false
    } else {
        let last = s.block_last[k];
        let alternate = c.cfg.input_blockers[k];
        let same = match last {
            Some(l) => l == a,
            None => false,
        };
        let valid = if alternate { !same } else { last.is_none() || same };
        if valid {
            s.block_last[k] = Some(a);
            false
        } else {
            true
        }
    }
}

/// `propagatePress`
pub fn propagate_press(c: &Ctx, s: &mut St, a: Action) -> Result<(), SimErr> {
    // the interceptors are the last children of the KeyBindingInputManager: the last-added one first
    let nb = c.cfg.input_blockers.len();
    let mut kk: usize = 0;
    let mut blocked = false;
    while kk < nb && !blocked {
        if intercept_press(c, s, nb - 1 - kk, a) {
            blocked = true;
        }
        kk += 1;
    }
    if blocked {
        return Ok(());
    }
    let order = input_order(c, s);
    let mut k: usize = 0;
    let mut done = false;
    while k < order.len() && !done {
        let i = order[k];
        let hovered = s.objs[i].hovered;
        match receptor_ref(c, s, i) {
            None => {}
            Some(r) => {
                if receptor_can_be_hit(c, s, r) && is_left_or_right(a) && hovered {
                    circle_update_result(c, s, r, true)?;
                    if s.objs[i].hit_action.is_none() {
                        s.objs[i].hit_action = Some(a);
                    }
                    done = true;
                }
            }
        }
        k += 1;
    }
    Ok(())
}

/// `triggerPressed`
pub fn trigger_pressed(c: &Ctx, s: &mut St, a: Action) -> Result<(), SimErr> {
    if act_contains(&s.pressed, a) {
        return Ok(());
    }
    s.pressed = act_push(s.pressed, a);
    propagate_press(c, s, a)
}

/// `triggerReleased`
pub fn trigger_released(s: &mut St, a: Action) {
    s.pressed = act_remove(s.pressed, a);
}

/// `replayStateDiff`: (released, pressed)
pub fn replay_state_diff(last: Option<ActList>, cur: &ActList) -> (ActList, ActList) {
    match last {
        None => (ACTLIST_EMPTY, *cur),
        Some(l) => {
            if l.len == 0 {
                (ACTLIST_EMPTY, *cur)
            } else if cur.len == 0 {
                (l, ACTLIST_EMPTY)
            } else if act_eq(&l, cur) {
                (ACTLIST_EMPTY, ACTLIST_EMPTY)
            } else {
                (act_minus(&l, cur), act_minus(cur, &l))
            }
        }
    }
}

/// `inputPhase`
pub fn input_phase(c: &Ctx, s: &mut St) -> Result<(), SimErr> {
    if c.frames.len() == 0 {
        return Ok(());
    }
    let step = c.steps[s.k];
    let gp = replay_position(&c.frames, step.frame_index, s.t);
    let hoc = cur_hoc(c, s);
    let screen = to_screen(&hoc, gp);
    let mut hover_done = false;
    if !s.mouse_valid || !s.mouse.eq(screen) {
        s.mouse_valid = true;
        s.mouse = screen;
        slider_mouse_move(c, s);
        spinner_mouse_move(c, s);
        update_hover(c, s);
        hover_done = true;
    }
    let cur = if step.frame_index < 0 { ACTLIST_EMPTY } else { c.frames[step.frame_index as usize].actions };
    let (released, pressed) = replay_state_diff(s.last_replay, &cur);
    s.last_replay = Some(cur);
    let mut k: usize = 0;
    while k < released.len {
        trigger_released(s, released.items[k]);
        k += 1;
    }
    let mut m: usize = 0;
    while m < pressed.len {
        trigger_pressed(c, s, pressed.items[m])?;
        m += 1;
    }
    if s.mouse_valid {
        slider_mouse_move(c, s);
        s.cursor_pos = to_local(&hoc, s.mouse);
    }
    if !hover_done {
        update_hover(c, s);
    }
    Ok(())
}

/// `playfieldUpdate`
pub fn playfield_update(c: &Ctx, s: &mut St) -> Result<(), SimErr> {
    let mut i: usize = 0;
    while i < c.cfg.updatables.len() {
        match c.cfg.updatables[i] {
            Updatable::DynRate(k) => dyn_rate_update(c, s, k)?,
            Updatable::Depth => depth_update(c, s)?,
            Updatable::BarrelRoll => barrel_roll_update(c, s),
            Updatable::Magnetised => magnet_update(c, s, false),
            Updatable::Repel => magnet_update(c, s, true),
            Updatable::Relax => relax_update(c, s)?,
            Updatable::Autopilot => autopilot_update(c, s),
            Updatable::InputBlock(k) => input_block_update(c, s, k),
        }
        i += 1;
    }
    Ok(())
}

/// `scaleForDepth`
pub fn scale_for_depth(z: F32, cam_z: F32) -> F32 {
    cam_z.neg().div(f32_max(F32_1C, z.sub(cam_z)))
}

/// the circle depth of `depthUpdate`
pub fn circle_depth(h: &HObj, max_depth: F32, time: F64) -> F32 {
    let speed = max_depth.to_f64().div(h.preempt);
    let appear = h.start.sub(h.preempt);
    max_depth.sub(net::max(time, appear).sub(appear).mul(speed).to_f32())
}

/// the slider depth of `depthUpdate`
pub fn slider_depth(h: &HObj, dur: F64, max_depth: F32, slider_min_depth: F32, time: F64) -> F32 {
    let base_speed = max_depth.to_f64().div(h.preempt);
    let appear = h.start.sub(h.preempt);
    let z_end = max_depth.sub(net::max(h.start.add(dur), appear).sub(appear).mul(base_speed).to_f32());
    if slider_min_depth.lt(z_end) {
        circle_depth(h, max_depth, time)
    } else {
        let offset_after = dur.add(F64::from_bits(0x407F400000000000) /* 500 */);
        let slow_speed = net::min(slider_min_depth.neg().to_f64().div(offset_after), base_speed);
        let dec_t = h.preempt.mul(F64::from_bits(0x3FC999999999999A) /* 0.2 */);
        let dec_d = dec_t.mul(base_speed.add(slow_speed)).mul(F64::from_bits(0x3FE0000000000000) /* 0.5 */).to_f32();
        if time.lt(h.start.sub(dec_t)) {
            let full = dec_d.add(base_speed.mul(h.preempt.sub(dec_t)).to_f32());
            full.sub(net::max(time, appear).sub(appear).mul(base_speed).to_f32())
        } else if time.lt(h.start) {
            let to = time.sub(h.start.sub(dec_t));
            let dec = slow_speed.sub(base_speed).div(dec_t);
            dec_d.sub(base_speed.mul(to).add(dec.mul(to).mul(to).mul(F64::from_bits(0x3FE0000000000000) /* 0.5 */)).to_f32())
        } else {
            let end_t = h.start.add(offset_after);
            net::min(time, end_t).sub(h.start).mul(slow_speed).to_f32().neg()
        }
    }
}

/// the `dur` of `depthUpdate` (sliders: `need o.slider`; others 0)
pub fn depth_slider_duration(c: &Ctx, i: usize) -> Result<F64, SimErr> {
    if c.pb.objects[i].h.kind == Kind::Slider {
        let sd = slider_data(c, i)?;
        Ok(sd.duration)
    } else {
        Ok(F64_0)
    }
}

/// `depthUpdate` (`OsuModDepth.Update`)
pub fn depth_update(c: &Ctx, s: &mut St) -> Result<(), SimErr> {
    let time = s.t;
    let cam_z = F32::from_bits(0xC348_0000); // -200
    let cam_xy = Vec2 { x: F32::from_bits(0x4380_0000), y: F32::from_bits(0x4340_0000) }; // (256, 192)
    let max_depth = c.cfg.depth_max;
    let slider_min_depth = cam_z.neg().div(F32::from_bits(0x3FC0_0000)).add(cam_z); // -camZ / 1.5f + camZ
    let active = s.active.clone();
    let mut q: usize = 0;
    while q < active.len() {
        let i = active[q];
        let o = &c.pb.objects[i];
        let k = s.objs[i].inst;
        let dur = depth_slider_duration(c, i)?;
        let z: Option<F32> = match o.h.kind {
            Kind::Circle => Some(circle_depth(&o.h, max_depth, time)),
            Kind::Slider => Some(slider_depth(&o.h, dur, max_depth, slider_min_depth, time)),
            _ => None,
        };
        match z {
            Some(zv) => {
                let sc = scale_for_depth(zv, cam_z);
                let p = o.h.stacked.sub(cam_xy).scale(sc).add(cam_xy);
                tobj_set(&mut s.insts[k].tf, Member::Position, p);
                tobj_set(&mut s.insts[k].tf, Member::Scale, Vec2 { x: sc, y: sc });
            }
            None => {}
        }
        q += 1;
    }
    Ok(())
}

/// the slider bounds of `magnetUpdate`'s repel destination (`CalculatePossibleMovementBounds`)
pub fn repel_slider_clamp(sd: &SliderData, radius: F64, d: Vec2) -> Vec2 {
    let r = radius.to_f32();
    let mut mn_x = netx::F32_POS_INF;
    let mut mx_x = netx::F32_NEG_INF;
    let mut mn_y = netx::F32_POS_INF;
    let mut mx_y = netx::F32_NEG_INF;
    let mut j: usize = 0;
    while j < sd.path.len() {
        let v = sd.path[j];
        mn_x = f32_min(mn_x, v.x);
        mx_x = f32_max(mx_x, v.x);
        mn_y = f32_min(mn_y, v.y);
        mx_y = f32_max(mx_y, v.y);
        j += 1;
    }
    let left = mn_x.sub(r).neg();
    let right = F32::from_bits(0x4400_0000).sub(mx_x.add(r)); // 512
    let top = mn_y.sub(r).neg();
    let bottom = F32::from_bits(0x43C0_0000).sub(mx_y.add(r)); // 384
    let w = right.sub(left);
    let hh = bottom.sub(top);
    of_tk(v2_clamp(to_tk(d), to_tk(Vec2 { x: left, y: top }), to_tk(Vec2 { x: left.add(w), y: top.add(hh) })))
}

/// `magnetUpdate` (`OsuModMagnetised.Update` / `OsuModRepel.Update`)
pub fn magnet_update(c: &Ctx, s: &mut St, repel: bool) {
    let cursor_pos = s.cursor_pos;
    let elapsed = if s.k == 0 { F64_0 } else { s.t.sub(c.steps[s.k - 1].time) };
    let active = s.active.clone();
    let mut q: usize = 0;
    while q < active.len() {
        magnet_one(c, s, active[q], repel, cursor_pos, elapsed);
        q += 1;
    }
}

/// the repel destination of `magnetUpdate`
pub fn repel_dest(o: &TopObj, pos: Vec2, cursor_pos: Vec2) -> Vec2 {
    let d = of_tk(v2_clamp(
        to_tk(pos.scale(F32_2).sub(cursor_pos)),
        to_tk(VEC2_ZERO),
        to_tk(Vec2 { x: F32::from_bits(0x4400_0000), y: F32::from_bits(0x43C0_0000) }),
    ));
    match &o.slider {
        Some(sd) => repel_slider_clamp(sd, o.h.radius, d),
        None => d,
    }
}

/// the slider-head judged test of `magnetUpdate`
pub fn magnet_head_judged(c: &Ctx, s: &St, i: usize) -> bool {
    if c.pb.objects[i].h.kind == Kind::Slider {
        judged(s, Ref { top: i, nested: c.head_idx[i] as i64 })
    } else {
        false
    }
}

/// the body of `magnetUpdate`'s loop for object `i`
pub fn magnet_one(c: &Ctx, s: &mut St, i: usize, repel: bool, cursor_pos: Vec2, elapsed: F64) {
    let k = s.objs[i].inst;
    let pos = s.insts[k].tf.pos;
    let ball = s.insts[k].ball_pos;
    let head_judged = magnet_head_judged(c, s, i);
    let kind = c.pb.objects[i].h.kind;
    let dest0 = if !repel { cursor_pos } else { repel_dest(&c.pb.objects[i], pos, cursor_pos) };
    if kind == Kind::Circle || kind == Kind::Slider {
        let dest = if kind == Kind::Slider && head_judged { dest0.sub(ball) } else { dest0 };
        let damp = magnet_damp(c, repel, pos, cursor_pos);
        let x = crate::net::framework::damp_continuously(pos.x.to_f64(), dest.x.to_f64(), damp, elapsed).to_f32();
        let y = crate::net::framework::damp_continuously(pos.y.to_f64(), dest.y.to_f64(), damp, elapsed).to_f32();
        tobj_set(&mut s.insts[k].tf, Member::Position, Vec2 { x, y });
    }
}

/// the damping half-time of `magnetUpdate`
pub fn magnet_damp(c: &Ctx, repel: bool, pos: Vec2, cursor_pos: Vec2) -> F64 {
    if repel {
        v2_distance(to_tk(pos), to_tk(cursor_pos)).to_f64().div(F64::from_bits(0x3FA47AE147AE147B) /* 0.04 */.mul(c.cfg.repel_strength.to_f64()).add(F64::from_bits(0x3FA47AE147AE147B) /* 0.04 */))
    } else {
        crate::net::framework::lerp(F64::from_bits(0x40A7700000000000) /* 3000 */, F64::from_bits(0x4044000000000000) /* 40 */, c.cfg.magnet_strength.to_f64())
    }
}

/// the `.barrelRoll` branch of `playfieldUpdate` (`ModBarrelRoll.Update`)
pub fn barrel_roll_update(c: &Ctx, s: &mut St) {
    match c.cfg.barrel_roll {
        Some((speed, ccw)) => {
            let sign: i64 = if ccw { -1 } else { 1 };
            s.br_rot = F32::from_i64(sign * 360).mul(s.t.div(F64::from_bits(0x40ED4C0000000000) /* 60000 */).mul(speed).to_f32());
        }
        None => {}
    }
}

/// `RELAX_LENIENCY = 12`
pub const RELAX_LENIENCY: F64 = F64::from_bits(0x4028_0000_0000_0000);

/// the `hitCircle` of `relaxUpdate`
pub fn relax_hit_circle(h: &HObj, hovered: bool, time: F64) -> bool {
    match h.hit_windows {
        Some(hw) => hovered && can_be_hit(&hw, time.sub(h.start)),
        None => false,
    }
}

/// (requiresHit, requiresHold) of `relaxUpdate`'s object loop
pub fn relax_requirements(c: &Ctx, s: &St, time: F64) -> Result<(bool, bool), SimErr> {
    let alive = alive_objects(c, s);
    let mut requires_hold = false;
    let mut requires_hit = false;
    let mut k: usize = 0;
    let mut stop = false;
    while k < alive.len() && !stop {
        let i = alive[k];
        let kind = c.pb.objects[i].h.kind;
        if time.lt(c.pb.objects[i].h.start.sub(RELAX_LENIENCY)) {
            stop = true;
        } else {
            let skip = is_hit_ref(s, Ref { top: i, nested: -1 })
                || ((kind == Kind::Slider || kind == Kind::Spinner) && c.pb.objects[i].h.end_time.lt(time));
            if !skip {
                let hovered = s.objs[i].hovered;
                if kind == Kind::Circle {
                    requires_hit = requires_hit || relax_hit_circle(&c.pb.objects[i].h, hovered, time);
                } else if kind == Kind::Slider {
                    let hj = c.head_idx[i];
                    if !is_hit_ref(s, Ref { top: i, nested: hj as i64 }) {
                        requires_hit = requires_hit || relax_hit_circle(&c.pb.objects[i].nested[hj], hovered, time);
                    }
                    let in_area = mouse_in_follow_area(c, s, i, s.insts[s.objs[i].inst].drawable_tracking)?;
                    requires_hold = requires_hold || in_area;
                } else if kind == Kind::Spinner {
                    let spins = match c.pb.objects[i].spinner {
                        Some(sp) => sp.spins_required > 0,
                        None => false,
                    };
                    requires_hold = requires_hold || spins;
                }
            }
            k += 1;
        }
    }
    Ok((requires_hit, requires_hold))
}

/// the `changeState` of `relaxUpdate`
pub fn relax_change_state(c: &Ctx, s: &mut St, down: bool, time: F64) -> Result<(), SimErr> {
    if s.relax_down == down {
        return Ok(());
    }
    let was_left = s.relax_was_left;
    s.relax_down = down;
    s.relax_last = time;
    if down {
        trigger_pressed(c, s, if was_left { Action::Left } else { Action::Right })?;
        s.relax_was_left = !s.relax_was_left;
    } else {
        trigger_released(s, if was_left { Action::Right } else { Action::Left });
    }
    Ok(())
}

/// `relaxUpdate`
pub fn relax_update(c: &Ctx, s: &mut St) -> Result<(), SimErr> {
    if c.cfg.lazer_replay {
        return Ok(());
    }
    let time = s.t;
    let (requires_hit, requires_hold) = relax_requirements(c, s, time)?;
    if requires_hit {
        relax_change_state(c, s, false, time)?;
        relax_change_state(c, s, true, time)?;
    }
    if requires_hold {
        relax_change_state(c, s, true, time)?;
    } else if s.relax_down && F64::from_bits(0x4049000000000000) /* 50 */.lt(time.sub(s.relax_last)) {
        relax_change_state(c, s, false, time)?;
    }
    Ok(())
}

/// `autopilotUpdate`
pub fn autopilot_update(c: &Ctx, s: &mut St) {
    let n = c.ap_frames.len() as i64;
    if s.ap_frame == n - 1 {
        return;
    }
    let time = s.t;
    let cur = s.ap_frame;
    let advance = cur < 0
        || c.ap_frames[(cur + 1) as usize].time.sub(time).abs().le(c.ap_frames[cur as usize].time.sub(time).abs());
    if advance {
        let nx = (cur + 1) as usize;
        s.ap_frame = cur + 1;
        let hoc = cur_env_hoc(c, s);
        let screen = to_screen(&hoc, c.ap_frames[nx].pos);
        if !s.mouse_valid || !s.mouse.eq(screen) {
            // MouseMove also reaches the CursorContainer (`ActiveCursor.Position`, read by MG/RP later in this P3)
            s.mouse_valid = true;
            s.mouse = screen;
            s.cursor_pos = to_local(&hoc, screen);
            slider_mouse_move(c, s);
            spinner_mouse_move(c, s);
            update_hover(c, s);
        }
    }
}

/// `inputBlockUpdate`
pub fn input_block_update(c: &Ctx, s: &mut St, k: usize) {
    if s.block_last[k].is_some() {
        let (in_any, idx) = period_is_in_any(&c.block_periods, s.block_idx[k], s.t);
        s.block_idx[k] = idx;
        if in_any {
            s.block_last[k] = None;
        }
    }
}

/// the `completed` of `processorsPhase`
pub fn completed(sc: &ScoreSt, max_hits: u64, t: F64) -> ScoreSt {
    let done = sc.judged_hits == max_hits
        && (sc.judged_hits == 0
            || match sc.last_time_absolute {
                Some(ta) => ta.lt(t),
                None => true,
            });
    ScoreSt { has_completed: done, ..*sc }
}

/// `processorsPhase`
pub fn processors_phase(c: &Ctx, s: &mut St) -> Result<(), SimErr> {
    let elapsed = if s.k == 0 { F64_0 } else { s.t.sub(c.steps[s.k - 1].time) };
    let rate = true_rate(&c.cfg, &s.speed);
    s.clock_rate = rate.abs().mul(F64_1);
    s.score = completed(&s.score, c.smax.max_hits, s.t);
    s.score_rp = completed(&s.score_rp, c.smax.max_hits, s.t);
    let t = s.t;
    drain(&mut s.health, &c.hcfg, t, elapsed)?;
    drain(&mut s.health_rp, &c.hcfg, t, elapsed)
}

/// `stepOnce`
pub fn step_once(c: &Ctx, s: &mut St) -> Result<(), SimErr> {
    processors_phase(c, s)?;
    input_phase(c, s)?;
    playfield_update(c, s)?;
    lifetime_update(c, s)?;
    let order = update_order(c, s);
    let mut k: usize = 0;
    while k < order.len() {
        let i = order[k];
        if s.objs[i].life == Life::Alive {
            update_dho(c, s, i)?;
        }
        k += 1;
    }
    Ok(())
}

/// `run`
pub fn run(c: &Ctx, s: &mut St) -> Result<(), SimErr> {
    let n = c.steps.len();
    let mut k: usize = 0;
    while k < n {
        s.k = k;
        s.t = c.steps[k].time;
        step_once(c, s)?;
        k += 1;
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// Context and initial state

/// `idxOf o k last` of `mkCtx`: 0 for non-sliders; a slider without a nested object of kind `k` is malformed
pub fn idx_of_kind(o: &TopObj, k: Kind, last: bool) -> Result<usize, SimErr> {
    if o.h.kind != Kind::Slider {
        return Ok(0);
    }
    let r = if last { last_idx_of_kind(o, k) } else { first_idx_of_kind(o, k) };
    match r {
        Some(j) => Ok(j),
        None => Err(SimErr::SliderWithout(o.h.start, k)),
    }
}

/// first index of kind `k`
pub fn first_idx_of_kind(o: &TopObj, k: Kind) -> Option<usize> {
    let mut found: Option<usize> = None;
    let mut j: usize = 0;
    while j < o.nested.len() && found.is_none() {
        if o.nested[j].kind == k {
            found = Some(j);
        }
        j += 1;
    }
    found
}

/// last index of kind `k`
pub fn last_idx_of_kind(o: &TopObj, k: Kind) -> Option<usize> {
    let mut last: Option<usize> = None;
    let mut j: usize = 0;
    while j < o.nested.len() {
        let kd = o.nested[j].kind;
        if kd == k {
            last = Some(j);
        }
        j += 1;
    }
    last
}

/// `pb.objects.mapM (idxOf · k last)`
pub fn idx_list(pb: &Playable, k: Kind, last: bool) -> Result<Vec<usize>, SimErr> {
    let mut out: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < pb.objects.len() {
        let j = idx_of_kind(&pb.objects[i], k, last)?;
        out.push(j);
        i += 1;
    }
    Ok(out)
}

/// `mkCtx`. Rejections in the spec's order: AutoGen (Autopilot), steps, health configuration, input-block
/// periods, preceding end times, slider heads, slider tails.
pub fn mk_ctx(env: Env, cfg: Config, pb: Playable, frames: Vec<Frame>, kind: ScheduleKind) -> Result<Ctx, SimErr> {
    let ap_frames = if has_autopilot(&cfg) { ap_frames_of(&pb, &cfg)? } else { Vec::new() };
    let st = steps(kind, &pb, &frames)?;
    let hcfg = mk_health_cfg(&pb, cfg.legacy_health)?;
    let block_periods = if cfg.input_blockers.len() == 0 { Vec::new() } else { input_block_periods(&pb)? };
    let prec_end = if has_adaptive(&cfg) { preceding_end_times(&pb) } else { Vec::new() };
    let head_idx = idx_list(&pb, Kind::Head, false)?;
    let tail_idx = idx_list(&pb, Kind::Tail, true)?;
    let smax = score_maxima(&pb, cfg.score_multiplier, cfg.rank_adjust);
    let n = frames.len();
    let last_frame_time = if n > 0 { Some(frames[n - 1].time) } else { None };
    let first_obj = first_objects(&cfg, &pb);
    Ok(Ctx {
        env,
        cfg,
        pb,
        frames,
        steps: st,
        head_idx,
        tail_idx,
        smax,
        hcfg,
        last_frame_time,
        corner_pow: receptor_corner_radius_pow(),
        prec_end,
        ap_frames,
        block_periods,
        first_obj,
    })
}

/// `firstObj` of `mkCtx` (`ModWithVisibilityAdjustment` FirstObject; HD skips spinners)
pub fn first_objects(cfg: &Config, pb: &Playable) -> Vec<Option<usize>> {
    let mut out: Vec<Option<usize>> = Vec::new();
    let mut vi: usize = 0;
    while vi < cfg.vis_mods.len() {
        let skips = vis_mod_skips_spinners(cfg.vis_mods[vi]);
        let mut r: Option<usize> = None;
        let mut i: usize = 0;
        while i < pb.objects.len() && r.is_none() {
            if !(skips && pb.objects[i].h.kind == Kind::Spinner) {
                r = Some(i);
            }
            i += 1;
        }
        out.push(r);
        vi += 1;
    }
    out
}

/// `cfg.updatables.any (· = .autopilot)`
pub fn has_autopilot(cfg: &Config) -> bool {
    let mut i: usize = 0;
    let mut r = false;
    while i < cfg.updatables.len() {
        match cfg.updatables[i] {
            Updatable::Autopilot => {
                r = true;
            }
            _ => {}
        }
        i += 1;
    }
    r
}

/// `cfg.dynRates.any (· = .adaptive _)`
pub fn has_adaptive(cfg: &Config) -> bool {
    let mut i: usize = 0;
    let mut r = false;
    while i < cfg.dyn_rates.len() {
        match cfg.dyn_rates[i] {
            DynRate::Adaptive(_) => {
                r = true;
            }
            DynRate::TimeRamp(_, _, _, _) => {}
        }
        i += 1;
    }
    r
}

/// `apFrames` of `mkCtx`: `AutoGen.generate pb cfg.rateMods`, mapped to (time, position)
pub fn ap_frames_of(pb: &Playable, cfg: &Config) -> Result<Vec<ApFrame>, SimErr> {
    let fs = crate::sim::autogen::generate(pb, &cfg.rate_mods)?;
    let mut out: Vec<ApFrame> = Vec::new();
    let mut i: usize = 0;
    while i < fs.len() {
        out.push(ApFrame { time: fs[i].time, pos: Vec2 { x: fs[i].pos.x, y: fs[i].pos.y } });
        i += 1;
    }
    Ok(out)
}

/// stable insertion of `x` into the ascending list `v` (`Order()`: `double.CompareTo`, `compare_d(x, e) < 0`)
pub fn insert_sorted_f64(v: &mut Vec<F64>, x: F64) {
    let mut i = v.len();
    while i > 0 && compare_d(x, v[i - 1]) < 0 {
        i -= 1;
    }
    crate::beatmap::dotnet::insert_at(v, i, x);
}

/// the `look` of `precedingEndTimes`
pub fn prec_look(end_times: &[F64], hw: Option<HitWindows>, e: F64) -> Option<F64> {
    match hw {
        None => None,
        Some(_) => {
            let b = binary_search_d(end_times, e);
            let idx = (if b < 0 { -b - 1 } else { b }) - 1;
            if idx >= 0 { Some(end_times[idx as usize]) } else { None }
        }
    }
}

/// the end times of hit-windowed objects of one top-level object (pre-order)
pub fn push_windowed_end_times(ts: &mut Vec<F64>, o: &TopObj) {
    if o.h.hit_windows.is_some() {
        insert_sorted_f64(ts, o.h.end_time);
    }
    let mut j: usize = 0;
    while j < o.nested.len() {
        if o.nested[j].hit_windows.is_some() {
            insert_sorted_f64(ts, o.nested[j].end_time);
        }
        j += 1;
    }
}

/// `precedingEndTimes`. Mirrors the spec's `stableSortBy ts (compareD a b < 0)` (lazer `Order()`: stable, `double.CompareTo`)
/// as an incremental stable insertion sort (`insert_sorted_f64`, same scan-from-the-end insertion point), then `Distinct`. D55.
pub fn preceding_end_times(pb: &Playable) -> Vec<PrecEnd> {
    let mut sorted: Vec<F64> = Vec::new();
    let mut i: usize = 0;
    while i < pb.objects.len() {
        push_windowed_end_times(&mut sorted, &pb.objects[i]);
        i += 1;
    }
    let mut end_times: Vec<F64> = Vec::new();
    let mut k: usize = 0;
    while k < sorted.len() {
        let x = sorted[k];
        let n = end_times.len();
        if n == 0 || !netx::equals_d(end_times[n - 1], x) {
            end_times.push(x);
        }
        k += 1;
    }
    let mut out: Vec<PrecEnd> = Vec::new();
    let mut q: usize = 0;
    while q < pb.objects.len() {
        out.push(prec_end_entry(&end_times, &pb.objects[q]));
        q += 1;
    }
    out
}

/// one entry of `precedingEndTimes`
pub fn prec_end_entry(end_times: &[F64], o: &TopObj) -> PrecEnd {
    let mut nested: Vec<Option<F64>> = Vec::new();
    let mut j: usize = 0;
    while j < o.nested.len() {
        nested.push(prec_look(end_times, o.nested[j].hit_windows, o.nested[j].end_time));
        j += 1;
    }
    PrecEnd { top: prec_look(end_times, o.h.hit_windows, o.h.end_time), nested }
}

/// `vt` of `inputBlockPeriods`
pub fn block_vt(h: &HObj) -> F64 {
    h.start.sub(match h.hit_windows {
        Some(hw) => hw.meh,
        None => F64_0,
    })
}

/// first object with `be <= StartTime`
pub fn first_object_after(pb: &Playable, be: F64) -> Option<usize> {
    let mut i: usize = 0;
    let mut r: Option<usize> = None;
    while i < pb.objects.len() && r.is_none() {
        if be.le(pb.objects[i].h.start) {
            r = Some(i);
        }
        i += 1;
    }
    r
}

/// `period` of `inputBlockPeriods`: `new Period(start, end)` throws for `start >= end`
pub fn block_period(a: F64, b: F64) -> Result<Period, SimErr> {
    if a.lt(b) { Ok(Period { start: a, end: b }) } else { Err(SimErr::PeriodInvalid) }
}

/// the period of the `b`-th break: `(break.Start, V(first object with StartTime >= break.End) - 1)`
pub fn break_block_period(pb: &Playable, b: usize) -> Result<Period, SimErr> {
    match first_object_after(pb, pb.breaks[b].end) {
        Some(oi) => block_period(pb.breaks[b].start, block_vt(&pb.objects[oi].h).sub(F64_1)),
        None => Err(SimErr::PeriodNoFollowing),
    }
}

/// `inputBlockPeriods` (a break without a following object: `First(…)` throws in lazer)
pub fn input_block_periods(pb: &Playable) -> Result<Vec<Period>, SimErr> {
    if pb.objects.len() == 0 {
        return Ok(Vec::new());
    }
    let mut ps: Vec<Period> = Vec::new();
    let p0 = block_period(F64::from_i64(-2147483648), block_vt(&pb.objects[0].h).sub(F64_1))?;
    ps.push(p0);
    let mut b: usize = 0;
    while b < pb.breaks.len() {
        let p = break_block_period(pb, b)?;
        ps.push(p);
        b += 1;
    }
    let mut out: Vec<Period> = Vec::new();
    let mut k: usize = 0;
    while k < ps.len() {
        insert_period_sorted(&mut out, ps[k]);
        k += 1;
    }
    Ok(out)
}

/// `poolInitial.map fun n => List.replicate n none`
pub fn initial_pools() -> Vec<Vec<Option<usize>>> {
    let mut pools: Vec<Vec<Option<usize>>> = Vec::new();
    let mut pk: usize = 0;
    while pk < 6 {
        let mut p: Vec<Option<usize>> = Vec::new();
        let mut q: usize = 0;
        while q < POOL_INITIAL[pk] {
            p.push(None);
            q += 1;
        }
        pools.push(p);
        pk += 1;
    }
    pools
}

/// `asInit` of `initState`: `DynRate.setSpeed (.adaptive i) 1 i` per AS mod
pub fn as_init(cfg: &Config) -> Result<Vec<F64>, SimErr> {
    let mut out: Vec<F64> = Vec::new();
    let mut d: usize = 0;
    while d < cfg.dyn_rates.len() {
        let dr = cfg.dyn_rates[d];
        let v = as_init_one(dr)?;
        match v {
            Some(x) => out.push(x),
            None => {}
        }
        d += 1;
    }
    Ok(out)
}

/// one entry of `as_init` (`None` for a TimeRamp)
pub fn as_init_one(dr: DynRate) -> Result<Option<F64>, SimErr> {
    match dr {
        DynRate::Adaptive(ir) => {
            let v = lift_net(dyn_rate_set_speed(dr, F64_1, ir))?;
            Ok(Some(v))
        }
        DynRate::TimeRamp(_, _, _, _) => Ok(None),
    }
}

/// `speed` of `initState`: every dynamic rate's `initialSpeed`
pub fn initial_speeds(cfg: &Config) -> Result<Vec<F64>, SimErr> {
    let mut out: Vec<F64> = Vec::new();
    let mut d: usize = 0;
    while d < cfg.dyn_rates.len() {
        let sp = lift_net(dyn_rate_initial_speed(cfg.dyn_rates[d]))?;
        out.push(sp);
        d += 1;
    }
    Ok(out)
}

/// `initState` (rejections: the AS bindables first, then every dynamic rate's initial speed);
/// `init_without_mods` = `ScoreMax.init_without_mods` (D80a)
pub fn init_state(cfg: &Config, pb: &Playable, init_without_mods: i64) -> Result<St, SimErr> {
    let mut score = SCORE_ST_INIT;
    score.rank = adjust_rank(cfg.rank_adjust, Rank::X);
    score.total_score_without_mods = init_without_mods;
    let health = health_st_init(cfg.easy_retries.clone());
    let mut objs: Vec<OState> = Vec::new();
    let mut i: usize = 0;
    while i < pb.objects.len() {
        let o = &pb.objects[i];
        let miss = match o.h.hit_windows {
            Some(hw) => hw.miss,
            None => F64_0,
        };
        objs.push(ostate_init(o.h.start.sub(o.h.preempt), o.h.end_time.add(miss), o.nested.len()));
        i += 1;
    }
    let as_target = as_init(cfg)?;
    let speed = initial_speeds(cfg)?;
    let mut as_recent: Vec<Vec<F64>> = Vec::new();
    let mut as_seen: Vec<Vec<Ref>> = Vec::new();
    let mut d: usize = 0;
    while d < cfg.dyn_rates.len() {
        let dr = cfg.dyn_rates[d];
        match dr {
            DynRate::Adaptive(ir) => {
                let mut rec: Vec<F64> = Vec::new();
                let mut q: usize = 0;
                while q < 8 {
                    rec.push(ir);
                    q += 1;
                }
                as_recent.push(rec);
                as_seen.push(Vec::new());
            }
            DynRate::TimeRamp(_, _, _, _) => {}
        }
        d += 1;
    }
    let mut block_last: Vec<Option<Action>> = Vec::new();
    let mut block_idx: Vec<usize> = Vec::new();
    let mut b: usize = 0;
    while b < cfg.input_blockers.len() {
        block_last.push(None);
        block_idx.push(0);
        b += 1;
    }
    Ok(St {
        k: 0,
        t: F64_0,
        objs,
        first_lifetime_update: true,
        next_future: 0,
        future_order: Vec::new(),
        active: Vec::new(),
        dict_slots: Vec::new(),
        free_list: Vec::new(),
        child_counter: 0,
        mouse_valid: false,
        mouse: VEC2_ZERO,
        last_replay: None,
        pressed: ACTLIST_EMPTY,
        score,
        health: health.clone(),
        score_rp: score,
        health_rp: health,
        out: Vec::new(),
        speed,
        as_target,
        as_recent,
        as_seen,
        clock_rate: F64_1,
        relax_down: false,
        relax_was_left: false,
        relax_last: F64_0,
        ap_frame: -1,
        block_last,
        block_idx,
        insts: Vec::new(),
        pools: initial_pools(),
        br_rot: F32_0,
        theta: F32_0,
        cursor_pos: VEC2_ZERO,
    })
}

/// `runWith`
pub fn run_with(c: &Ctx) -> Result<St, SimErr> {
    let mut s = init_state(&c.cfg, &c.pb, c.smax.init_without_mods)?;
    run(c, &mut s)?;
    Ok(s)
}

/// `simulate`
pub fn simulate(env: Env, cfg: Config, pb: Playable, frames: Vec<Frame>, kind: ScheduleKind) -> Result<(Ctx, St), SimErr> {
    let c = mk_ctx(env, cfg, pb, frames, kind)?;
    let s = run_with(&c)?;
    Ok((c, s))
}
