/-
e2e2: `sim.step.simulate_refines_full`: simcore3's `simulate_refines` with its `hRW` discharged by `e2_runWith_field`
(unconditional `run_with`), under the spec-level facts the headline gets from its named rows (default debug fields
and mod-index ranges of `Config.ofMods`: e2_ofMods_dbg / e2_ofMods_idx; frame indices: SchedFramesIn; run budget and
D77 F3: RunBudgetIn).
-/
import OsuProofs.Sim.StepTop
import OsuProofs.Eval.E2Sim
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- `step::simulate` refines `simulate` (no open callee) -/
theorem sim.step.simulate_refines_full (h64 : System.Platform.numBits = 64) (env : sim.geometry.Env)
    (c : sim.mods.Config) (pb : sim.playable.Playable) (fs : alloc.vec.Vec replay.frames.Frame)
    (k : sim.schedule.ScheduleKind) (C : OsuModel.Sim.Config) (hc : ev_cfgRel c C) (hB : ev_mkBounds pb fs)
    (ht : C.traceObj = none) (hd : C.dbgNoPresence = false) (hidx : e2CfgIdx C)
    (hfi : ∀ CTX, OsuModel.Sim.mkCtx (abs env) C (playableS ev_tn pb) (fs.val.map abs).toArray (ev_kindS k) = .ok CTX →
      ∀ st ∈ CTX.steps.toList, -1 ≤ st.frameIndex ∧ st.frameIndex < CTX.frames.size)
    (hrb : ∀ CTX, OsuModel.Sim.mkCtx (abs env) C (playableS ev_tn pb) (fs.val.map abs).toArray (ev_kindS k) = .ok CTX →
      (∀ S0, OsuModel.Sim.initState CTX.cfg CTX.pb CTX.smax.initWithoutMods = .ok S0 → RunBudgetS CTX S0) ∧ e2AccBudS CTX):
    ∃ r, sim.step.simulate env c pb fs k = ok r ∧
    (match r, OsuModel.Sim.simulate (abs env) C (playableS ev_tn pb) (fs.val.map abs).toArray (ev_kindS k) with
     | .Ok (ctx, s), .ok (CTX, S) => ev_ctxRel ctx CTX ∧ simStS ev_tn s = S
     | .Err _, .error _ => True
     | _, _ => False) := by
  obtain ⟨r, hr, hrel⟩ := js_mk_ctx_full h64 env c pb fs k C hc hB
  have hwf := fun ctx (h : r = .Ok ctx) => sim.step.mk_ctx_wf h64 env c pb fs k C hc hB ctx (h ▸ hr)
  unfold sim.step.simulate OsuModel.Sim.simulate
  rw [hr]
  revert hrel
  cases r with
  | Err x =>
    cases OsuModel.Sim.mkCtx (abs env) C (playableS ev_tn pb) (fs.val.map abs).toArray (ev_kindS k) with
    | ok _ => intro h; exact h.elim
    | error e =>
      intro _
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ⟨_, rfl, trivial⟩
  | Ok ctx =>
    cases hM : OsuModel.Sim.mkCtx (abs env) C (playableS ev_tn pb) (fs.val.map abs).toArray (ev_kindS k) with
    | error _ => intro h; exact h.elim
    | ok CTX =>
      rintro ⟨e1, e2, e3, e4, hR⟩
      have hSt0 : CTX.steps = abs ctx.steps := by
        have := congrArg OsuModel.Sim.Ctx.steps hR.2; simpa [simCtxS] using this.symm
      have hFr0 : CTX.frames = abs ctx.frames := by
        have := congrArg OsuModel.Sim.Ctx.frames hR.2; simpa [simCtxS] using this.symm
      have hfi' : ∀ st ∈ ctx.steps.val, -1 ≤ st.frame_index.val ∧
          st.frame_index.val < (ctx.frames.val.length : Int) := by
        intro st hst
        have := hfi CTX hM (abs st) (by rw [hSt0]; simp [abs]; exact ⟨st, hst, rfl, rfl⟩)
        rw [hFr0] at this; simpa [abs] using this
      obtain ⟨r1, h1, hr1⟩ := e2_runWith_field h64 ctx CTX hR (hwf ctx rfl) (by rw [e2]; exact ht)
        (by rw [e2]; exact hd) (by rw [e2]; exact hidx) hfi' (hrb CTX hM).1 (hrb CTX hM).2
      rw [e2, e4] at hr1
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Bind.bind, Except.bind, Pure.pure, Except.pure]
      rw [h1]
      revert hr1
      cases r1 with
      | Ok s =>
        cases OsuModel.Sim.runWith CTX C (playableS ev_tn pb) with
        | error _ => intro h; exact h.elim
        | ok S =>
          intro h
          simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Bind.bind, Except.bind, Pure.pure, Except.pure]
          exact ⟨_, rfl, hR, h⟩
      | Err x =>
        cases OsuModel.Sim.runWith CTX C (playableS ev_tn pb) with
        | ok _ => intro h; exact h.elim
        | error _ =>
          intro _
          simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Bind.bind, Except.bind, Pure.pure, Except.pure]
          exact ⟨_, rfl, trivial⟩

end OsuProofs
