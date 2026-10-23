/-
`sim::step::processors_phase` (Rust) refines `OsuModel.Sim.Sim.processorsPhase` (score `completed`, clock rate
from `Config.trueRate` (Sim2/Mods), the two health drains). `simRelM`: Rust `(Result<(), SimErr>, St)` vs the spec
`SimM Unit` run (`Ok` ↦ `.ok ((), simStS tn s')`, `Err` ↦ some `.error`).
-/
import OsuProofs.Sim.InitCtx
import OsuProofs.Sim2.Mods
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- the `completed` of `processorsPhase` -/
def simCompleted (mh : Nat) (t : F64) (sc : OsuModel.Sim.ScoreSt) : OsuModel.Sim.ScoreSt :=
  { sc with hasCompleted := sc.judgedHits == mh &&
      (sc.judgedHits == 0 || (match sc.lastTimeAbsolute with | some ta => ta < t | none => true)) }

-- FRAGMENT-OF: OsuModel.Sim.Sim.processorsPhase (simCompleted = its local `completed`; bridged in sim.step.processors_phase_refines)
theorem sim.step.completed_refines (sc : sim.scoring.ScoreSt) (mh : U64) (t : F64) :
    ∃ r, sim.step.completed sc mh t = ok r ∧ simCompleted mh.val t (abs sc) = abs r := by
  unfold sim.step.completed simCompleted
  by_cases h1 : sc.judged_hits = mh
  · have h1' : sc.judged_hits.val = mh.val := by rw [h1]
    by_cases h2 : sc.judged_hits = 0#u64
    · have h2' : sc.judged_hits.val = 0 := by rw [h2]; rfl
      refine ⟨{ sc with has_completed := true }, by rw [if_pos h1, if_pos h2], ?_⟩
      simp only [abs, scoreS] at *; simp [h1', h2']; omega
    · have h2' : sc.judged_hits.val ≠ 0 := fun e => h2 (UScalar.eq_of_val_eq (by simpa using e))
      cases hl : sc.last_time_absolute with
      | none => refine ⟨{ sc with has_completed := true }, by rw [if_pos h1, if_neg h2, hl], ?_⟩; simp only [abs, scoreS] at *; simp [h1', h2', hl]
      | some ta =>
        refine ⟨{ sc with has_completed := decide (ta < t) }, by rw [if_pos h1, if_neg h2, hl]; simp [float.F64.lt], ?_⟩
        simp only [abs, scoreS] at *; simp [h1', h2', hl]; intro h; omega
  · have h1' : sc.judged_hits.val ≠ mh.val := fun e => h1 (UScalar.eq_of_val_eq e)
    refine ⟨{ sc with has_completed := false }, by rw [if_neg h1], ?_⟩
    simp only [abs, scoreS] at *; simp [h1']

def simRelM (tn : Nat → String) (s' : sim.state.St) :
    core.result.Result Unit sim.err.SimErr → Except String (Unit × OsuModel.Sim.St) → Prop
  | .Ok _, e => e = .ok ((), simStS tn s')
  | .Err _, e => ∃ m, e = .error m

theorem simS_elapsedNow' (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) (hstep : S.k ≠ 0 → S.k - 1 < C.steps.size) :
    OsuModel.Sim.Sim.elapsedNow C S = .ok (if S.k = 0 then 0 else S.t - (C.steps[S.k - 1]!).time, S) := by
  unfold OsuModel.Sim.Sim.elapsedNow OsuModel.Sim.Sim.stepAt
  by_cases h0 : S.k = 0
  · simp [h0, OsuModel.Sim.Sim.st, Except.bind]
  · have hl := hstep h0
    simp [h0, OsuModel.Sim.Sim.st, OsuModel.Sim.Sim.ctx, OsuModel.Sim.Sim.getA, hl, Except.bind, Except.map,
      getElem!_def]

theorem sim.step.processors_phase_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St)
    (hstep : s.k.val ≠ 0 → s.k.val - 1 < c.steps.val.length)
    (hd : ∀ x ∈ c.cfg.rate_sources.val, ∀ k, x.val = .Dyn k → k.val < s.speed.val.length)
    (hi1 : c.hcfg.periods.val.length ≠ 0 → s.health.nearest_index.val < c.hcfg.periods.val.length)
    (hi2 : c.hcfg.periods.val.length ≠ 0 → s.health_rp.nearest_index.val < c.hcfg.periods.val.length) :
    ∃ r s', sim.step.processors_phase c s = ok (r, s') ∧
      simRelM tn s' r (OsuModel.Sim.Sim.processorsPhase (simCtxS tn fo c) (simStS tn s)) := by
  -- elapsed
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
      simp only [h0', if_false, hi, bind_ok, vec_index_eq _ _ hil, float.F64.sub, e, h0]
      simp [List.getElem?_eq_getElem hl, ei]
  have hES : OsuModel.Sim.Sim.elapsedNow (simCtxS tn fo c) (simStS tn s) = .ok (e, simStS tn s) := by
    rw [simS_elapsedNow' _ _ (by intro h; simpa [simStS, simCtxS, abs] using hstep h)]
    simp only [e]
    by_cases h0 : s.k.val = 0
    · simp [simStS, h0]
    · simp [simStS, h0, simCtxS, abs, getElem!_def, List.getElem?_eq_getElem (hstep h0)]
  -- rate
  obtain ⟨rate, hr, er⟩ := sim.mods.true_rate_refines c.cfg (alloc.vec.Vec.deref s.speed)
    (by simpa [alloc.vec.Vec.deref] using hd)
  obtain ⟨ss, hss, ess⟩ := sim.step.completed_refines s.score c.smax.max_hits s.t
  obtain ⟨ss1, hss1, ess1⟩ := sim.step.completed_refines s.score_rp c.smax.max_hits s.t
  obtain ⟨r1, hs1, hd1, er1⟩ := sim.scoring.drain_refines s.health c.hcfg s.t e hi1
  obtain ⟨r2, hs2, hd2, er2⟩ := sim.scoring.drain_refines s.health_rp c.hcfg s.t e hi2
  have hspeed : (abs (alloc.vec.Vec.deref s.speed) : _root_.Array F64) = (simStS tn s).speed := by
    simp [abs, simStS, alloc.vec.Vec.deref]
  unfold OsuModel.Sim.Sim.processorsPhase
  simp only [simM_bind, OsuModel.Sim.Sim.ctx, OsuModel.Sim.Sim.st, simM_read, simM_get, Except.bind, hES]
  have hcfg : (simCtxS tn fo c).cfg = abs c.cfg := rfl
  rw [hcfg, ← hspeed, er]
  simp only [OsuModel.Sim.Sim.liftExcept, simM_pure, simM_bind, Except.bind]
  have hhc : (simCtxS tn fo c).hcfg = abs c.hcfg := rfl
  have hhs : (simStS tn s).health = abs s.health := rfl
  have hhr : (simStS tn s).healthRP = abs s.health_rp := rfl
  rw [hhc, hhs, hhr]
  unfold sim.step.processors_phase
  rw [hE]
  have hT : (simStS tn s).t = s.t := rfl
  rw [hT]
  cases r1 with
  | Err x =>
    obtain ⟨m, hm⟩ := er1
    refine ⟨.Err x, { s with score := ss, health := hs1, score_rp := ss1, clock_rate := F64.abs rate * 1 }, ?_, ?_⟩
    · simp [hr, float.F64.abs, sim_step_F64_1, float.F64.mul, hss, hss1, hd1,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
        core.convert.From.from]
    · rw [hm]; exact ⟨m, rfl⟩
  | Ok u =>
    simp only [simRel] at er1
    rw [er1]
    cases r2 with
    | Err x =>
      obtain ⟨m, hm⟩ := er2
      refine ⟨.Err x, { s with score := ss, health := hs1, score_rp := ss1, health_rp := hs2, clock_rate := F64.abs rate * 1 }, ?_, ?_⟩
      · simp [hr, float.F64.abs, sim_step_F64_1, float.F64.mul, hss, hss1, hd1, hd2,
          core.result.Result.Insts.CoreOpsTry.branch]
      · simp only [OsuModel.Sim.Sim.liftExcept, simM_pure]
        rw [hm]; exact ⟨m, rfl⟩
    | Ok u2 =>
      simp only [simRel] at er2
      rw [er2]
      refine ⟨.Ok u2, { s with score := ss, health := hs1, score_rp := ss1, health_rp := hs2, clock_rate := F64.abs rate * 1 }, ?_, ?_⟩
      · simp [hr, float.F64.abs, sim_step_F64_1, float.F64.mul, hss, hss1, hd1, hd2,
          core.result.Result.Insts.CoreOpsTry.branch]
      · simp only [simRelM, OsuModel.Sim.Sim.liftExcept, simM_pure, simM_set]
        simp only [simStS]
        rw [← ess, ← ess1]
        have hsp2 : (abs (alloc.vec.Vec.deref s.speed) : _root_.Array F64) = abs s.speed := by
          simp [abs, alloc.vec.Vec.deref]
        rw [hsp2]
        rfl
end OsuProofs
