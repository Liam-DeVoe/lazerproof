/-
`eval.evaluate_refines` with the EvalAssumptions fields that are proved plugged in (json agent):
utf8, scoreInfo (JsonDischarge), mkCtx (JsonMkCtx2 relation, JsonMkCtxWF well-formedness), frames, playable (here, from Sim2/FramesParse and Post/Playable3), config, trueRate (JsonWire2), gst, r0, endT, frameTimes, references, simulateSteps, dynInit (JsonWire).
`js_EvalOpen` now holds only the trusted LZMA boundary `lzmaBound` (§5); run_with is proved (Eval/E2Sim `e2_runWith_field`).
-/
import OsuProofs.Eval.EndToEnd
import OsuProofs.Eval.JsonWire
import OsuProofs.Eval.JsonDischarge
import OsuProofs.Sim2.FramesParse
import OsuProofs.Eval.JsonWire2
import OsuProofs.Eval.JsonMkCtx2
import OsuProofs.Eval.JsonMkCtxWF
import OsuProofs.Eval.E2Frames
import OsuProofs.Eval.E2Sim
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

/-- The `EvalAssumptions` field that is not proved: the TRUSTED LZMA boundary (§5). -/
structure js_EvalOpen : Prop where
  /-- (trusted LZMA boundary) `ev_lzmaBound` -/
  lzmaBound : ev_lzmaBound

theorem js_ev_frames : ∀ (t : Slice U32) (v : I64), ValidStr t → t.val.length < 2^62 →
    ∃ r, replay.frames.decode t v = ok r ∧
    ev_eRel (fun fs => (fs.val.map abs).toArray) r (OsuModel.Replay.decode (String.ofList (strS t)) v.val) ∧
    ∀ fs, r = .Ok fs → fs.val.length ≤ t.val.length ∧ ∀ f ∈ fs.val, f.actions.len.val ≤ 3 := by
  intro t v ht hn
  obtain ⟨r, hr, e, hl⟩ := replay.frames.decode_refines t v ht hn
  refine ⟨r, hr, ?_, fun fs h => ⟨hl fs h, e2_decode_acts t v ht hn fs (h ▸ hr)⟩⟩
  revert e
  cases r <;> cases OsuModel.Replay.decode (String.ofList (strS t)) v.val <;> simp [s2_eR, ev_eRel]

theorem js_ev_playable (h64 : System.Platform.numBits = 64) :
    ∀ (d : beatmap.types.DecodedBeatmap) (ms : Slice beatmap.mod_settings.ModConfig),
    (∀ m ∈ ms.val, ev_mcOk m) → ev_pbOk d ms → ∃ r, beatmap.playable.get_playable_beatmap d ms = ok r ∧
    ev_eRel abs r (OsuModel.Eval.playableOf (dec_dbS d) (ms.val.map mcS)) := by
  intro d ms hok hL
  have e : (ms.val.map mcS).map ModConfig.allHooks = ms.val.map (fun m => (mcS m).allHooks) := by
    rw [List.map_map]; rfl
  have hL' : LoadBounds (abs d) (ms.val.map (fun m => (mcS m).allHooks)) := by
    unfold ev_pbOk at hL; rw [e, gpb_dec_dbS] at hL; exact hL
  obtain ⟨h1, h2, h3, hN, hall⟩ := gpb_load_bounds d _ hL'
  have hacr : ∀ m ∈ ms.val, AcrOk m := by
    intro m hm u hu; simp [ms_deref_val] at hu; exact (hok m hm).1 u hu
  obtain ⟨r, hr, hrel⟩ := beatmap.playable.get_playable_beatmap_refines d ms h1 h2 h3 hN h64 hall hacr
    (fun m hm => (hok m hm).2.2) hL'.gpb
  refine ⟨r, hr, ?_⟩
  have eP : OsuModel.Eval.playableOf (dec_dbS d) (ms.val.map mcS) =
      getPlayableBeatmap (abs d) (ms.val.map (fun m => (mcS m).allHooks)) := by
    unfold OsuModel.Eval.playableOf; rw [gpb_dec_dbS, e]
  rw [eP]; revert hrel
  cases r <;> cases getPlayableBeatmap (abs d) (ms.val.map (fun m => (mcS m).allHooks)) <;> simp [hRel, ev_eRel]

theorem js_evalAssumptions (O : js_EvalOpen) (h64 : System.Platform.numBits = 64) : EvalAssumptions where
  playable := js_ev_playable h64
  frames := js_ev_frames
  config := js_ev_config h64
  gst := js_ev_gst
  r0 := js_ev_r0
  endT := js_ev_endT
  frameTimes := js_ev_frameTimes
  references := js_ev_references h64
  simulateSteps := js_ev_simulateSteps h64
  mkCtx := fun env c pb fs k C hc hB => by
    obtain ⟨r, hr, hrel⟩ := js_mk_ctx_full h64 env c pb fs k C hc hB
    exact ⟨r, hr, hrel, fun ctx h => sim.step.mk_ctx_wf h64 env c pb fs k C hc hB ctx (h ▸ hr)⟩
  runWith := e2_runWith_field h64
  dynInit := js_ev_dynInit
  trueRate := js_ev_trueRate
  utf8 := js_ev_utf8
  lzmaBound := O.lzmaBound
  scoreInfo := js_ev_scoreInfo h64

-- CONDITIONAL: O = js_EvalOpen: lzmaBound [TRUSTED, §5] only (run_with: simcore3 sc3_run_with + sim8 lifetime_update_refines + sim9 init_state_lifeInv via e2_runWith_field). Trusted hypotheses: InputBounds, PlayableBounds (§5, incl. simCtx), RunBudgetIn (§5). (D72: the step frame-index range, formerly the row SchedFramesIn, is checked by `sched_ctx`.)
/-- **End-to-end refinement**, open obligations reduced to `js_EvalOpen`. -/
theorem eval.evaluate_refines_open (O : js_EvalOpen) (env : sim.geometry.Env)
    (bm osr : Slice U8) (hb : InputBounds bm osr) (opts : eval.Options)
    (hopts : ∀ ov, opts.mods_override = some ov → (∀ m ∈ ov.val, ev_mcOk m) ∧ ov.val.length < 2^61)
    (hpb : PlayableBounds bm osr opts)
    (sched : eval.Schedule) (hsched : ∀ refs, sched = .Explicit refs → refs.val.length * 100000000 + 4 < 2^61)
    (hrb : RunBudgetIn (abs env) bm osr opts sched) :
    ∃ r, eval.evaluate env bm osr opts sched = ok r ∧
      ev_topRel r (OsuModel.Eval.evaluate (abs env) (bytesS bm) (bytesS osr) (ev_optsS opts) (ev_schedS sched)) :=
  eval.evaluate_refines (js_evalAssumptions O hb.h64) env bm osr hb opts hopts hpb sched hsched hrb

end OsuProofs
