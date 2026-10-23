/-
e2e2: wiring simcore3's `sc3_run_with` (Sim/StepMain.lean) into the end-to-end layer.
`e2_sc3Cfg`: the mod-index ranges `sc3Cfg` of a Rust ctx from the spec-side `e2CfgIdx` (Config.ofMods) via configS.
-/
import OsuProofs.Sim.StepMain
import OsuProofs.Sim.LifetimeUpd
import OsuProofs.Sim.InitLife
import OsuProofs.Eval.E2Cong
import OsuProofs.Eval.E2RunCfg
import OsuProofs.Eval.JsonMkCtxWF
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl

theorem e2_sc3Cfg (c : sim.state.Ctx) (h : e2CfgIdx (configS c.cfg)) : sc3Cfg c := by
  obtain ⟨⟨h1, h2, h3⟩, -⟩ := h
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun x hx k hxk => ?_⟩
  · have := h1 k.val (by
      simp only [configS, abs, List.mem_toArray]
      exact List.mem_map_of_mem (f := fun u => (abs u : OsuModel.Sim.Updatable)) hk)
    simpa [configS, abs] using this
  · have := h2 k.val (by
      simp only [configS, abs, List.mem_toArray]
      exact List.mem_map_of_mem (f := fun u => (abs u : OsuModel.Sim.Updatable)) hk)
    simpa [configS, abs] using this
  · have := h3 (abs x.prop) k.val (by
      simp only [configS, abs, List.mem_toArray]
      have := List.mem_map_of_mem (f := fun u => (abs u : OsuModel.Sim.AudioProp × OsuModel.Sim.RateVal)) hx
      simpa [abs, hxk] using this)
    simpa [configS, abs] using this

/-- the `EvalAssumptions.runWith` field, unconditional: simcore3's `sc3_run_with` with sim8's lifetime contract
(`sc3_lifeC`, `ev_ctxWF.tk`) and sim9's initial lifetime invariant (`init_state_lifeInv`, F3 = `e2AccBudS`). -/
theorem e2_runWith_field (h64 : System.Platform.numBits = 64) :
    ∀ (ctx : sim.state.Ctx) (CTX : OsuModel.Sim.Ctx), ev_ctxRel ctx CTX → ev_ctxWF ctx →
    CTX.cfg.traceObj = none → CTX.cfg.dbgNoPresence = false → e2CfgIdx CTX.cfg →
    (∀ st ∈ ctx.steps.val, -1 ≤ st.frame_index.val ∧ st.frame_index.val < (ctx.frames.val.length : Int)) →
    (∀ S0, OsuModel.Sim.initState CTX.cfg CTX.pb CTX.smax.initWithoutMods = .ok S0 → RunBudgetS CTX S0) → e2AccBudS CTX →
    ∃ r, sim.step.run_with ctx = ok r ∧ ev_eRel (simStS ev_tn) r (OsuModel.Sim.runWith CTX CTX.cfg CTX.pb) := by
  intro ctx CTX hrel hwf ht hd hidx hfi hrb hacc
  have hG : sc3Cfg ctx := e2_sc3Cfg ctx (by rw [hrel.1]; exact hidx)
  have e := e2_ctx_norm ctx CTX hrel ht hd
  have hcfg : (abs ctx.cfg : OsuModel.Sim.Config) = { CTX.cfg with mods := [] } := by
    have := congrArg OsuModel.Sim.Ctx.cfg e; simpa [simCtxS, e2N] using this
  have hpb : playableS ev_tn ctx.pb = CTX.pb := by
    have := congrArg OsuModel.Sim.Ctx.pb e; simpa [simCtxS, e2N] using this
  have hsm : ctx.smax.init_without_mods.val = CTX.smax.initWithoutMods := by
    have := congrArg OsuModel.Sim.Ctx.smax e
    have h2 := congrArg OsuModel.Sim.ScoreMax.initWithoutMods this
    simpa [simCtxS, e2N, abs] using h2
  have hB : ∀ S0, OsuModel.Sim.initState (abs ctx.cfg) (playableS ev_tn ctx.pb) ctx.smax.init_without_mods.val = .ok S0 →
      RunBudgetS (simCtxS ev_tn (alloc.vec.Vec.new _) ctx) S0 := by
    intro S0 h0
    rw [hcfg, hpb, hsm, ← e2_initState] at h0
    rw [e]; exact (e2_runBudget_norm CTX S0).2 (hrb S0 h0)
  obtain ⟨R, eR, hR⟩ := sc3_run_with h64 ev_tn (alloc.vec.Vec.new _) ctx hwf hG hwf.frames_small hwf.acts hfi
    (js_s7StrictOk ctx hwf) (sc3_lifeC h64 ev_tn _ ctx hwf hwf.tk)
    (sim.step.init_state_lifeInv ctx CTX hrel hwf hidx hacc) hB
  refine ⟨R, eR, ?_⟩
  rw [e2_runWith_bridge ctx CTX hrel ht hd] at hR
  revert hR
  cases R <;> cases OsuModel.Sim.runWith CTX CTX.cfg CTX.pb <;> simp [simRel, ev_eRel] <;> exact fun h => h.symm

end OsuProofs
