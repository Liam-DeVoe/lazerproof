/-
proc (D73): the frame of `sim::step::processors_phase` and the health drain-cursor invariant.
* `sim.scoring.period_is_in_any_refines_bound`: `period_is_in_any_refines` + the returned cursor stays in range.
* `pr_drain_fr`: `drain` only writes `health` and `nearest_index` (in range when the input was).
* `pr_PFr` / `sim.step.processors_phase_refines_fr`: `processors_phase` = `processors_phase_refines` + on `Ok` the
  exact frame (only `score.has_completed`, `score_rp.has_completed`, `health.{health,nearest_index}`,
  `health_rp.{health,nearest_index}` and `clock_rate` change) + the cursor bound `pr_HB` for the new state.
* `pr_proc_phc` / `pr_proc_phc'`: the phase contract `sc2PhC` (Sim/StepLoop) for the step loop: `processors_phase`
  preserves `pr_HB c ∧ I` for any `I` closed under `pr_PFr`. `pr_HB_keep`: every `simKeepS` frame (apply_result
  chain, simARFr / simJFr / s4Fr / s7Fr / sc2DFr / s6HFr) keeps `pr_HB`; `pr_HB_s6keep`: so does `s6PFr` (s6KeepT).
-/
import OsuProofs.Sim.StepLoop
import OsuProofs.Sim.ApplyFrame
import OsuProofs.Sim.Press
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

open Aeneas Aeneas.Std Result
namespace OsuProofs
open OsuImpl OsuModel.Net

/-- `period_is_in_any_refines` with the bound conjunct: the returned cursor is in range (for a non-empty list) -/
theorem sim.scoring.period_is_in_any_refines_bound (ps : Slice sim.playable.Period) (idx : Usize) (time : F64)
    (hidx : ps.val.length ≠ 0 → idx.val < ps.val.length) :
    ∃ r, sim.scoring.period_is_in_any ps idx time = ok r ∧
      OsuModel.Sim.periodIsInAny (simPS ps).toArray idx.val time = .ok (r.1, r.2.val) ∧
      (ps.val.length ≠ 0 → r.2.val < ps.val.length) := by
  obtain ⟨r, hr, er⟩ := sim.scoring.period_is_in_any_refines ps idx time hidx
  refine ⟨r, hr, er, fun h0 => ?_⟩
  have hlen : (simPS ps).length = ps.val.length := by simp [simPS]
  have hi' : idx.val < (simPS ps).length := by rw [hlen]; exact hidx h0
  rw [simS_periodIsInAny (simPS ps) idx.val time hi'] at er
  dsimp only at er
  simp only [Except.ok.injEq, Prod.mk.injEq] at er
  rw [← er.2, ← hlen]
  split
  · exact sim_fwd_lt _ _ _ _ hi'
  · exact sim_bwd_lt _ _ _ _ hi'

/-- `drain` writes only `health` and `nearest_index`, and keeps the cursor in range -/
theorem pr_drain_fr (h : sim.scoring.HealthSt) (c : sim.scoring.HealthCfg) (t el : F64)
    (hidx : c.periods.val.length ≠ 0 → h.nearest_index.val < c.periods.val.length)
    (r : core.result.Result Unit sim.err.SimErr) (h2 : sim.scoring.HealthSt)
    (hd : sim.scoring.drain h c t el = ok (r, h2)) :
    h2 = { h with health := h2.health, nearest_index := h2.nearest_index } ∧
      (c.periods.val.length ≠ 0 → h2.nearest_index.val < c.periods.val.length) := by
  obtain ⟨⟨inAny, idx⟩, hp, -, hb⟩ := sim.scoring.period_is_in_any_refines_bound (alloc.vec.Vec.deref c.periods)
    h.nearest_index t (by simpa [alloc.vec.Vec.deref] using hidx)
  have hb' : c.periods.val.length ≠ 0 → idx.val < c.periods.val.length := by
    simpa [alloc.vec.Vec.deref] using hb
  have fin : ∀ X (Y : sim.scoring.HealthSt), sim.scoring.drain h c t el = ok (X, Y) →
      Y = { h with health := Y.health, nearest_index := idx } →
      h2 = { h with health := h2.health, nearest_index := h2.nearest_index } ∧
        (c.periods.val.length ≠ 0 → h2.nearest_index.val < c.periods.val.length) := by
    intro X Y e hY
    rw [e] at hd
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.ok_injective hd)
    rw [hY]; exact ⟨rfl, hb'⟩
  cases inAny
  · cases hc1 : F64.clamp (t - el) c.drain_start_time c.gameplay_end_time with
    | error e1 =>
      exact fin (.Err (.ClampDrain (exnI e1))) { h with nearest_index := idx }
        (by simp [sim.scoring.drain, hp, sim.scoring.drain_clamp, sim_mathops_f64_clamp, hc1, exceptI,
          core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, core.convert.From.from]) rfl
    | ok v1 =>
      cases hc2 : F64.clamp t c.drain_start_time c.gameplay_end_time with
      | error e2 =>
        exact fin (.Err (.ClampDrain (exnI e2))) { h with nearest_index := idx }
          (by simp [sim.scoring.drain, hp, sim.scoring.drain_clamp, sim_mathops_f64_clamp, hc1, hc2, exceptI,
            core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame, core.convert.From.from]) rfl
      | ok v2 =>
        obtain ⟨f4, hf4, -⟩ := sim.scoring.clamp01_refines (h.health - c.drain_rate * (v2 - v1))
        exact fin (.Ok ()) { h with health := f4, nearest_index := idx }
          (by simp [sim.scoring.drain, hp, sim.scoring.drain_clamp, sim_mathops_f64_clamp, hc1, hc2, exceptI,
            core.result.Result.Insts.CoreOpsTry.branch, float.F64.sub, float.F64.mul, hf4]) rfl
  · exact fin (.Ok ()) { h with nearest_index := idx } (by simp [sim.scoring.drain, hp]) rfl

/-- the health drain-cursor invariant: both cursors in range of `hcfg.periods` (vacuous for no periods) -/
def pr_HB (c : sim.state.Ctx) (s : sim.state.St) : Prop :=
  (c.hcfg.periods.val.length ≠ 0 → s.health.nearest_index.val < c.hcfg.periods.val.length) ∧
  (c.hcfg.periods.val.length ≠ 0 → s.health_rp.nearest_index.val < c.hcfg.periods.val.length)

/-- initial states (`health_st_init`: cursor 0) satisfy `pr_HB` -/
theorem pr_HB_zero (c : sim.state.Ctx) (s : sim.state.St) (h1 : s.health.nearest_index.val = 0)
    (h2 : s.health_rp.nearest_index.val = 0) : pr_HB c s :=
  ⟨fun h => by omega, fun h => by omega⟩

/-- every frame with `simKeepS s' = simKeepS s` keeps `pr_HB` -/
theorem pr_HB_keep {c : sim.state.Ctx} {s s' : sim.state.St} (h : simKeepS s' = simKeepS s) (hb : pr_HB c s) :
    pr_HB c s' := by
  obtain ⟨e1, e2⟩ := pr_keepS_ni h
  unfold pr_HB; rw [e1, e2]; exact hb

/-- the press-chain frame `s6PFr` (keep tuple `s6KeepT`) keeps `pr_HB` -/
theorem pr_HB_s6keep {c : sim.state.Ctx} {s s' : sim.state.St} (h : s6KeepT s' = s6KeepT s) (hb : pr_HB c s) :
    pr_HB c s' := by
  simp only [s6KeepT, Prod.mk.injEq] at h
  unfold pr_HB
  rw [h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
  exact hb

/-- `pr_HB` only reads the two cursors -/
theorem pr_HB_of_ni {c : sim.state.Ctx} {s s' : sim.state.St} (e1 : s'.health.nearest_index = s.health.nearest_index)
    (e2 : s'.health_rp.nearest_index = s.health_rp.nearest_index) (hb : pr_HB c s) : pr_HB c s' := by
  unfold pr_HB; rw [e1, e2]; exact hb

/-- the frame of `processors_phase` on `Ok`: exactly these fields change -/
def pr_PFr (s s' : sim.state.St) : Prop :=
  ∃ (ss ss1 : sim.scoring.ScoreSt) (hs hs1 : sim.scoring.HealthSt) (cr : F64),
    s' = { s with score := ss, health := hs, score_rp := ss1, health_rp := hs1, clock_rate := cr } ∧
    ss = { s.score with has_completed := ss.has_completed } ∧
    ss1 = { s.score_rp with has_completed := ss1.has_completed } ∧
    hs = { s.health with health := hs.health, nearest_index := hs.nearest_index } ∧
    hs1 = { s.health_rp with health := hs1.health, nearest_index := hs1.nearest_index }

theorem pr_completed_fr (sc : sim.scoring.ScoreSt) (mh : U64) (t : F64) (r : sim.scoring.ScoreSt)
    (h : sim.step.completed sc mh t = ok r) : r = { sc with has_completed := r.has_completed } := by
  unfold sim.step.completed at h
  split at h
  · split at h
    · cases Result.ok_injective h; rfl
    · split at h
      · cases Result.ok_injective h; rfl
      · simp only [float.F64.lt, bind_ok] at h; cases Result.ok_injective h; rfl
  · cases Result.ok_injective h; rfl

/-- the Rust side of `processors_phase`: it returns, and on `Ok` it has the frame `pr_PFr` and keeps `pr_HB` -/
theorem pr_proc_eval (c : sim.state.Ctx) (s : sim.state.St)
    (hstep : s.k.val ≠ 0 → s.k.val - 1 < c.steps.val.length)
    (hd : ∀ x ∈ c.cfg.rate_sources.val, ∀ k, x.val = .Dyn k → k.val < s.speed.val.length)
    (hb : pr_HB c s) :
    ∃ r s', sim.step.processors_phase c s = ok (r, s') ∧ (r = .Ok () → pr_PFr s s' ∧ pr_HB c s') := by
  let e : F64 := if s.k.val = 0 then 0 else s.t - ((c.steps.val[s.k.val - 1]?).map (·.time)).getD 0
  have hE : (if s.k = 0#usize then (do let e ← sim.step.F64_0; ok (c, e))
      else do let i ← s.k - 1#usize; let s1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice schedule.Step) c.steps i
              let e ← float.F64.sub s.t s1.time; ok (c, e)) = ok (c, e) := by
    by_cases h0 : s.k.val = 0
    · have : s.k = 0#usize := by scalar_tac
      simp [this, h0, e, sim.step.F64_0]
    · have h0' : ¬ s.k = 0#usize := fun h => h0 (by simp [h])
      have hl := hstep h0
      obtain ⟨i, hi, ei⟩ : ∃ z, s.k - 1#usize = ok z ∧ z.val = s.k.val - 1 := by
        obtain ⟨z, hz, hv, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := s.k) (y := 1#usize) (by simp; omega))
        exact ⟨z, hz, by simp at hv; omega⟩
      have hil : i.val < c.steps.val.length := by omega
      simp only [h0', ite_false, hi, bind_ok, vec_index_eq _ _ hil, float.F64.sub, e, h0]
      simp [List.getElem?_eq_getElem hl, ei]
  obtain ⟨rate, hr, -⟩ := sim.mods.true_rate_refines c.cfg (alloc.vec.Vec.deref s.speed)
    (by simpa [alloc.vec.Vec.deref] using hd)
  obtain ⟨ss, hss, -⟩ := sim.step.completed_refines s.score c.smax.max_hits s.t
  obtain ⟨ss1, hss1, -⟩ := sim.step.completed_refines s.score_rp c.smax.max_hits s.t
  obtain ⟨r1, hs1, hd1, -⟩ := sim.scoring.drain_refines s.health c.hcfg s.t e hb.1
  obtain ⟨r2, hs2, hd2, -⟩ := sim.scoring.drain_refines s.health_rp c.hcfg s.t e hb.2
  obtain ⟨f1, b1⟩ := pr_drain_fr s.health c.hcfg s.t e hb.1 r1 hs1 hd1
  obtain ⟨f2, b2⟩ := pr_drain_fr s.health_rp c.hcfg s.t e hb.2 r2 hs2 hd2
  have c1 := pr_completed_fr s.score c.smax.max_hits s.t ss hss
  have c2 := pr_completed_fr s.score_rp c.smax.max_hits s.t ss1 hss1
  unfold sim.step.processors_phase
  rw [hE]
  cases r1 with
  | Err x =>
    refine ⟨.Err x, { s with score := ss, health := hs1, score_rp := ss1, clock_rate := F64.abs rate * 1 }, ?_,
      fun h => by cases h⟩
    simp [hr, float.F64.abs, sim_step_F64_1, float.F64.mul, hss, hss1, hd1,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.From.from]
  | Ok u =>
    refine ⟨r2, { s with score := ss, health := hs1, score_rp := ss1, health_rp := hs2, clock_rate := F64.abs rate * 1 },
      ?_, fun _ => ⟨⟨ss, ss1, hs1, hs2, _, rfl, c1, c2, f1, f2⟩, b1, b2⟩⟩
    simp [hr, float.F64.abs, sim_step_F64_1, float.F64.mul, hss, hss1, hd1, hd2,
      core.result.Result.Insts.CoreOpsTry.branch]

/-- `processors_phase_refines` with the `Ok` frame conjunct (exact changed fields, cursor bound kept) -/
theorem sim.step.processors_phase_refines_fr (tn fo) (c : sim.state.Ctx) (s : sim.state.St)
    (hstep : s.k.val ≠ 0 → s.k.val - 1 < c.steps.val.length)
    (hd : ∀ x ∈ c.cfg.rate_sources.val, ∀ k, x.val = .Dyn k → k.val < s.speed.val.length)
    (hb : pr_HB c s) :
    ∃ r s', sim.step.processors_phase c s = ok (r, s') ∧
      simRelM tn s' r (OsuModel.Sim.Sim.processorsPhase (simCtxS tn fo c) (simStS tn s)) ∧
      (r = .Ok () → pr_PFr s s' ∧ pr_HB c s') := by
  obtain ⟨r, s', e, rel⟩ := sim.step.processors_phase_refines tn fo c s hstep hd hb.1 hb.2
  obtain ⟨r2, s2, e2, P⟩ := pr_proc_eval c s hstep hd hb
  rw [e] at e2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective e2)
  exact ⟨r, s', e, rel, P⟩

/-- the step-loop phase contract (simcore3): `processors_phase` from `pr_HB c ∧ I` establishes any `J` that follows
from `I` across the frame `pr_PFr` and the new cursor bound -/
theorem pr_proc_phc' (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (I J : sim.state.St → Prop)
    (hpre : ∀ s, I s → (s.k.val ≠ 0 → s.k.val - 1 < c.steps.val.length) ∧
      (∀ x ∈ c.cfg.rate_sources.val, ∀ k, x.val = .Dyn k → k.val < s.speed.val.length))
    (hcl : ∀ s s', I s → pr_HB c s → pr_PFr s s' → pr_HB c s' → J s') :
    sc2PhC tn fo c sim.step.processors_phase OsuModel.Sim.Sim.processorsPhase (fun s => pr_HB c s ∧ I s) J := by
  intro s ⟨hb, hI⟩
  obtain ⟨hstep, hd⟩ := hpre s hI
  obtain ⟨r, s', e, rel, P⟩ := sim.step.processors_phase_refines_fr tn fo c s hstep hd hb
  exact ⟨r, s', e, rel, fun h => let ⟨f, b⟩ := P h; hcl s s' hI hb f b⟩

/-- "`processors_phase` preserves `P`" for `P = pr_HB c ∧ I`, `I` closed under the frame `pr_PFr` -/
theorem pr_proc_phc (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (I : sim.state.St → Prop)
    (hpre : ∀ s, I s → (s.k.val ≠ 0 → s.k.val - 1 < c.steps.val.length) ∧
      (∀ x ∈ c.cfg.rate_sources.val, ∀ k, x.val = .Dyn k → k.val < s.speed.val.length))
    (hcl : ∀ s s', I s → pr_PFr s s' → I s') :
    sc2PhC tn fo c sim.step.processors_phase OsuModel.Sim.Sim.processorsPhase
      (fun s => pr_HB c s ∧ I s) (fun s => pr_HB c s ∧ I s) :=
  pr_proc_phc' tn fo c I _ hpre (fun s s' hI _ f b => ⟨b, hcl s s' hI f⟩)

/-! ## closure helpers for `pr_PFr` -/

theorem pr_PFr_eq {s s' : sim.state.St} (h : pr_PFr s s') :
    s'.k = s.k ∧ s'.t = s.t ∧ s'.objs = s.objs ∧ s'.insts = s.insts ∧ s'.active = s.active ∧
    s'.dict_slots = s.dict_slots ∧ s'.free_list = s.free_list ∧ s'.pressed = s.pressed ∧ s'.speed = s.speed ∧
    s'.out = s.out ∧ s'.pools = s.pools ∧ s'.future_order = s.future_order ∧ s'.next_future = s.next_future ∧
    s'.child_counter = s.child_counter ∧ s'.first_lifetime_update = s.first_lifetime_update ∧
    s'.block_last = s.block_last ∧ s'.block_idx = s.block_idx ∧ s'.as_target = s.as_target ∧
    s'.as_recent = s.as_recent ∧ s'.as_seen = s.as_seen ∧ s'.theta = s.theta := by
  obtain ⟨_, _, _, _, _, rfl, -⟩ := h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- the health / score counters `processors_phase` keeps (fail triggers, retries, judged hits, combo, stats, ...) -/
theorem pr_PFr_hs {s s' : sim.state.St} (h : pr_PFr s s') :
    s'.health.retries = s.health.retries ∧ s'.health.fail_triggers = s.health.fail_triggers ∧
    s'.health.has_failed = s.health.has_failed ∧ s'.health.failed = s.health.failed ∧
    s'.health_rp.retries = s.health_rp.retries ∧ s'.health_rp.fail_triggers = s.health_rp.fail_triggers ∧
    s'.health_rp.has_failed = s.health_rp.has_failed ∧ s'.health_rp.failed = s.health_rp.failed ∧
    s'.score.judged_hits = s.score.judged_hits ∧ s'.score.combo = s.score.combo ∧ s'.score.stats = s.score.stats ∧
    s'.score.current_accuracy_judgement_count = s.score.current_accuracy_judgement_count ∧
    s'.score_rp.judged_hits = s.score_rp.judged_hits ∧ s'.score_rp.combo = s.score_rp.combo ∧
    s'.score_rp.stats = s.score_rp.stats ∧
    s'.score_rp.current_accuracy_judgement_count = s.score_rp.current_accuracy_judgement_count := by
  obtain ⟨ss, ss1, hs, hs1, _, rfl, e1, e2, e3, e4⟩ := h
  simp only
  rw [e1, e2, e3, e4]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
end OsuProofs
