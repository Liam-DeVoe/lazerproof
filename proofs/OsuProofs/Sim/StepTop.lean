import OsuProofs.Sim.InitLife
import OsuProofs.Eval.JsonMkCtx2
import OsuProofs.Eval.JsonMkCtxWF

/-!
# `run_with_refines`, `simulate_refines` (simcore3)

The top of the simulation loop: `run_with` from simcore3's `sc3_run_with` (Sim/StepMain) with sim8's lifetime contract
(`sc3_lifeC`) and sim9's initial lifetime invariant (`s9_initLife`); `simulate` = `mk_ctx` (`js_mk_ctx_full`,
`mk_ctx_wf`) then `run_with`, given the `run_with` refinement in the shape of `EvalAssumptions.runWith`.
-/

open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- `step::run_with` refines `runWith` at the abstraction of the context (`ev_tn`, empty future order) -/
theorem sim.step.run_with_refines (h64 : System.Platform.numBits = 64) (c : sim.state.Ctx) (hW : ev_ctxWF c)
    (hG : sc3Cfg c) (hTK : s8TKCtx c) (hS9 : s9Ctx c)
    (hfi : ∀ st ∈ c.steps.val, -1 ≤ st.frame_index.val ∧ st.frame_index.val < (c.frames.val.length : Int))
    (hB : ∀ S0, OsuModel.Sim.initState (abs c.cfg) (playableS ev_tn c.pb) c.smax.init_without_mods.val = .ok S0 →
      RunBudgetS (simCtxS ev_tn (alloc.vec.Vec.new _) c) S0) :
    ∃ R, sim.step.run_with c = ok R ∧
      simRel (simStS ev_tn) R
        (OsuModel.Sim.runWith (simCtxS ev_tn (alloc.vec.Vec.new _) c) (abs c.cfg) (playableS ev_tn c.pb)) :=
  sc3_run_with h64 ev_tn _ c hW hG hW.frames_small hW.acts hfi (js_s7StrictOk c hW)
    (sc3_lifeC h64 ev_tn _ c hW hTK) (fun s0 h B CS => s9_initLife ev_tn _ c hS9 s0 h B _ CS) hB

/-- `step::simulate` refines `simulate`: `mk_ctx` by `js_mk_ctx_full`/`mk_ctx_wf`, then `run_with` by `hRW`
(the shape of `EvalAssumptions.runWith`, restricted to the contexts `mk_ctx` builds here) -/
theorem sim.step.simulate_refines (h64 : System.Platform.numBits = 64) (env : sim.geometry.Env)
    (c : sim.mods.Config) (pb : sim.playable.Playable) (fs : alloc.vec.Vec replay.frames.Frame)
    (k : sim.schedule.ScheduleKind) (C : OsuModel.Sim.Config) (hc : ev_cfgRel c C) (hB : ev_mkBounds pb fs)
    (hRW : ∀ (ctx : sim.state.Ctx) (CTX : OsuModel.Sim.Ctx), ev_ctxRel ctx CTX → ev_ctxWF ctx →
      ctx.cfg = c → ctx.pb = pb → CTX.cfg = C → CTX.pb = playableS ev_tn pb →
      ∃ r, sim.step.run_with ctx = ok r ∧ ev_eRel (simStS ev_tn) r (OsuModel.Sim.runWith CTX CTX.cfg CTX.pb)) :
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
      obtain ⟨r1, h1, hr1⟩ := hRW ctx CTX hR (hwf ctx rfl) e1 e3 e2 e4
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
