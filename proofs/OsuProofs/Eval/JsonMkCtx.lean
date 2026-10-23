/-
`sim.step.mk_ctx_refines` (HANDOFF from sim core, json agent): Rust `mk_ctx` vs `OsuModel.Sim.mkCtx`, in the shape
of `EvalAssumptions.mkCtx` (relation part). Open callees as named hypotheses: `ap_frames_of` (hAP, needs sim2's
autogen.generate) and `preceding_end_times` (hPE).
-/
import OsuProofs.Eval.E2EBase
import OsuProofs.Eval.JsonWire
import OsuProofs.Sim.MkCtx
import OsuProofs.Sim.IdxKind
import OsuProofs.Sim.InitCtx
import OsuProofs.Sim.MkHealthCfg
import OsuProofs.Sim.Maxima
import OsuProofs.Sim2.Geometry
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

def js_isAP : OsuModel.Sim.Updatable → Bool | .autopilot => true | _ => false
def js_isAd : OsuModel.Sim.DynRate → Bool | .adaptive _ => true | _ => false

/-- `OsuModel.Sim.mkCtx` with its local `idxOf` named (`simIdxOfSpec`, Sim/MkCtx) and named `any` predicates. -/
def js_mkS (env : OsuModel.Sim.Env) (cfg : OsuModel.Sim.Config) (pb : OsuModel.Sim.Playable)
    (frames : _root_.Array OsuModel.Replay.Frame) (kind : OsuModel.Sim.ScheduleKind) : Except String OsuModel.Sim.Ctx := do
  let apFrames ← if cfg.updatables.any js_isAP
    then do pure ((← OsuModel.Sim.AutoGen.generate pb cfg.rateMods.toList).map fun f => (f.time, (⟨f.pos.x, f.pos.y⟩ : OsuModel.Sim.Vec2)))
    else pure #[]
  let stepsA ← OsuModel.Sim.steps kind pb frames
  let hcfg ← OsuModel.Sim.mkHealthCfg pb cfg.legacyHealth
  let blockPeriods ← if cfg.inputBlockers.isEmpty then pure #[] else OsuModel.Sim.inputBlockPeriods pb
  let precEnd ← if cfg.dynRates.any js_isAd
    then OsuModel.Sim.precedingEndTimes pb else pure #[]
  let headIdx ← pb.objects.mapM (simIdxOfSpec · .head false)
  let tailIdx ← pb.objects.mapM (simIdxOfSpec · .tail true)
  return {
    env, cfg, pb, frames, steps := stepsA, futureOrder := #[]
    smax := { OsuModel.Sim.scoreMaxima pb cfg.scoreMultiplier with rankAdjust := cfg.rankAdjust }, hcfg
    apFrames, blockPeriods
    firstObj := cfg.visMods.map fun vm =>
      pb.objects.findIdx? fun o => !(vm.skipsSpinners && o.h.kind == .spinner)
    precEnd
    lastFrameTime := frames.back?.map (·.time)
    headIdx, tailIdx }

theorem js_mkCtx_eq (env : OsuModel.Sim.Env) (cfg : OsuModel.Sim.Config) (pb : OsuModel.Sim.Playable)
    (frames : _root_.Array OsuModel.Replay.Frame) (kind : OsuModel.Sim.ScheduleKind) :
    OsuModel.Sim.mkCtx env cfg pb frames kind = js_mkS env cfg pb frames kind := by
  unfold OsuModel.Sim.mkCtx js_mkS
  rfl

theorem js_s2_ok {α β : Type} {f : α → β} {X : Except String β} {a : α} (h : s2_rel f X (.Ok a)) : X = .ok (f a) := by
  cases X with
  | ok b => simp only [s2_rel] at h; rw [h]
  | error _ => simp [s2_rel] at h

theorem js_s2_err {α β : Type} {f : α → β} {X : Except String β} {e} (h : s2_rel f X (.Err e)) : ∃ m, X = .error m := by
  cases X with
  | ok b => simp [s2_rel] at h
  | error m => exact ⟨m, rfl⟩

theorem js_idx_bridge (pb : sim.playable.Playable) (k : sim.playable.Kind) (K : OsuModel.Sim.Kind) (hK : kindS k = K)
    (last : Bool) (R : core.result.Result (alloc.vec.Vec Usize) sim.err.SimErr)
    (h : simRel (fun v : alloc.vec.Vec Usize => v.val.map (·.val)) R
      ((pb.objects.val.map (topS ev_tn)).mapM (simIdxOfS · (kindS k) last))) :
    simRel (fun v : alloc.vec.Vec Usize => (v.val.map (·.val)).toArray) R
      ((playableS ev_tn pb).objects.mapM (simIdxOfSpec · K last)) := by
  have e : (fun o => simIdxOfSpec o K last) = (fun o => simIdxOfS o (kindS k) last) := by
    funext o; rw [sim_idxOfSpec_eq, hK]
  simp only [playableS]
  rw [e, List.mapM_toArray]
  cases R with
  | Ok v => simp only [simRel] at h ⊢; rw [h]; rfl
  | Err _ => obtain ⟨m, hm⟩ := h; exact ⟨m, by rw [hm]; rfl⟩

theorem js_lft (fs : alloc.vec.Vec replay.frames.Frame) :
    (if alloc.vec.Vec.len fs > 0#usize then (do
        let i1 ← alloc.vec.Vec.len fs - 1#usize
        let f ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice replay.frames.Frame) fs i1
        ok (some f.time))
      else ok none) = ok ((((fs.val.map abs).toArray : _root_.Array OsuModel.Replay.Frame).back?).map (·.time)) := by
  by_cases h : 0 < fs.val.length
  · have h' : alloc.vec.Vec.len fs > 0#usize := by show (0#usize).val < (alloc.vec.Vec.len fs).val; simpa using h
    rw [if_pos h']
    obtain ⟨i1, hi1, hi1v⟩ := usize_sub_one (alloc.vec.Vec.len fs) (by simp; omega)
    have hl : i1.val < fs.val.length := by simp at hi1v; omega
    simp only [hi1, bind_ok, vec_index_eq' fs i1 hl]
    congr 1
    rw [Array.back?_eq_getElem?]
    simp only [List.size_toArray, List.length_map, List.getElem?_toArray, List.getElem?_map]
    have : fs.val.length - 1 = i1.val := by simp at hi1v; omega
    rw [this, List.getElem?_eq_getElem hl]; rfl
  · have h' : ¬ alloc.vec.Vec.len fs > 0#usize := by show ¬ (0#usize).val < (alloc.vec.Vec.len fs).val; simpa using h
    rw [if_neg h']
    have e : fs.val = [] := by simpa using h
    simp [e]

@[simp] theorem js_br_ok {T E : Type} (v : T) :
    core.result.Result.Insts.CoreOpsTry.branch (core.result.Result.Ok v : core.result.Result T E) =
      ok (core.ops.control_flow.ControlFlow.Continue v) := rfl
@[simp] theorem js_br_err {T E : Type} (e : E) :
    core.result.Result.Insts.CoreOpsTry.branch (core.result.Result.Err e : core.result.Result T E) =
      ok (core.ops.control_flow.ControlFlow.Break (core.result.Result.Err e)) := rfl
@[simp] theorem js_fr {T E : Type} (e : E) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T (core.convert.FromSame E)
      (core.result.Result.Err e) = ok (core.result.Result.Err e) := by
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
    core.convert.FromSame.from]

def js_apS (v : alloc.vec.Vec sim.state.ApFrame) : _root_.Array (F64 × OsuModel.Sim.Vec2) :=
  (v.val.map fun a => (a.time, (abs a.pos : OsuModel.Sim.Vec2))).toArray

def js_peS (v : alloc.vec.Vec sim.state.PrecEnd) : _root_.Array (Option F64 × _root_.Array (Option F64)) :=
  (v.val.map fun p => (p.top, (p.nested.val).toArray)).toArray

set_option hygiene false in
local macro "js_final" : tactic => `(tactic| (
  refine ⟨_, rfl, ?_⟩
  simp only [true_and, and_true]
  unfold ev_ctxRel
  refine ⟨hc, ?_⟩
  simp only at hMrel'
  rw [hMrel', ← hFOrel]
  rfl))

set_option hygiene false in
local macro "js_tail2" : tactic => `(tactic| (
  rcases Bool.eq_false_or_eq_true ((configS c).dynRates.any js_isAd) with hd | hd <;>
  simp only [hd, ↓reduceIte, Bool.false_eq_true, bind_ok, except_bind_ok, except_pure] <;>
  (cases I1 with
   | Err e =>
     obtain ⟨m, rfl⟩ := hI1r
     simp only [js_br_err, bind_ok, js_fr, except_bind_error]
     exact ⟨_, rfl, trivial⟩
   | Ok i1 =>
     simp only [simRel] at hI1r; rw [hI1r]
     simp only [js_br_ok, bind_ok, except_bind_ok]
     cases I2 with
     | Err e =>
       obtain ⟨m, rfl⟩ := hI2r
       simp only [js_br_err, bind_ok, js_fr, except_bind_error]
       exact ⟨_, rfl, trivial⟩
     | Ok i2 =>
       simp only [simRel] at hI2r; rw [hI2r]
       simp only [js_br_ok, bind_ok, except_bind_ok, except_pure]
       js_final)))

set_option hygiene false in
local macro "js_tail1" : tactic => `(tactic| (
  cases S with
  | Err e =>
    obtain ⟨m, rfl⟩ := js_s2_err hSrel
    simp only [js_br_err, bind_ok, js_fr, except_bind_error]
    exact ⟨_, rfl, trivial⟩
  | Ok sv =>
    rw [js_s2_ok hSrel]
    simp only [js_br_ok, bind_ok, except_bind_ok]
    cases H with
    | Err e =>
      obtain ⟨m, rfl⟩ := hHrel'
      simp only [js_br_err, bind_ok, js_fr, except_bind_error]
      exact ⟨_, rfl, trivial⟩
    | Ok hv =>
      simp only [simRel] at hHrel'; rw [hHrel']
      simp only [js_br_ok, bind_ok, except_bind_ok]
      by_cases hi : (configS c).inputBlockers.isEmpty = true
      · rw [if_pos (ei.mpr hi)]
        simp only [hi, ↓reduceIte, except_bind_ok, except_pure]
        js_tail2
      · rw [if_neg (mt ei.mp hi)]
        simp only [hi, ↓reduceIte, Bool.false_eq_true]
        cases B with
        | Err e =>
          obtain ⟨m, rfl⟩ := hBrel
          simp only [js_br_err, bind_ok, js_fr, except_bind_error]
          exact ⟨_, rfl, trivial⟩
        | Ok bv =>
          simp only [simRel] at hBrel; rw [hBrel]
          simp only [js_br_ok, bind_ok, except_bind_ok]
          js_tail2))

theorem js_mk_ctx_refines (h64 : System.Platform.numBits = 64) (env : sim.geometry.Env) (c : sim.mods.Config)
    (pb : sim.playable.Playable) (fs : alloc.vec.Vec replay.frames.Frame) (k : sim.schedule.ScheduleKind)
    (C : OsuModel.Sim.Config) (hc : ev_cfgRel c C)
    (hfs : fs.val.length < 2^32)
    (hcap : (pb.objects.val.map (fun o => o.nested.val.length + 1)).sum < Usize.max)
    (hbr : pb.breaks.val.length < Usize.max)
    (hAP : ∃ r, sim.step.ap_frames_of pb c = ok r ∧
      match r with
      | .Ok v => ∃ G, OsuModel.Sim.AutoGen.generate (playableS ev_tn pb) (configS c).rateMods.toList = .ok G ∧
          G.map (fun f => (f.time, ({ x := f.pos.x, y := f.pos.y } : OsuModel.Sim.Vec2))) = js_apS v
      | .Err _ => ∃ m, OsuModel.Sim.AutoGen.generate (playableS ev_tn pb) (configS c).rateMods.toList = .error m)
    (hPE : ∃ v, sim.step.preceding_end_times pb = ok v ∧
      OsuModel.Sim.precedingEndTimes (playableS ev_tn pb) = .ok (js_peS v)) :
    ∃ r, sim.step.mk_ctx env c pb fs k = ok r ∧
    (match r, OsuModel.Sim.mkCtx (abs env) C (playableS ev_tn pb) (fs.val.map abs).toArray (ev_kindS k) with
     | .Ok ctx, .ok CTX => ctx.cfg = c ∧ CTX.cfg = C ∧ ctx.pb = pb ∧ CTX.pb = playableS ev_tn pb ∧ ev_ctxRel ctx CTX
     | .Err _, .error _ => True
     | _, _ => False) := by
  have hU := usize_max_64 h64
  have hc' := hc; unfold ev_cfgRel at hc'
  have eU : C.updatables = (configS c).updatables := by rw [hc']
  have eD : C.dynRates = (configS c).dynRates := by rw [hc']
  have eI : C.inputBlockers = (configS c).inputBlockers := by rw [hc']
  have eR : C.rateMods = (configS c).rateMods := by rw [hc']
  have eV : C.visMods = (configS c).visMods := by rw [hc']
  have eM : C.scoreMultiplier = (configS c).scoreMultiplier := by rw [hc']
  have eA : C.rankAdjust = (configS c).rankAdjust := by rw [hc']
  have eL : C.legacyHealth = (configS c).legacyHealth := by rw [hc']
  have eSt : OsuModel.Sim.steps (ev_kindS k) (playableS ev_tn pb) (fs.val.map abs).toArray =
      OsuModel.Sim.steps (abs k) (abs pb) (abs (alloc.vec.Vec.deref fs)) := by
    rw [js_kindS]; unfold OsuModel.Sim.steps
    rw [(js_sch_tn pb).1, (js_sch_tn pb).2.1, (js_sch_tn pb).2.2]
    have ef : (abs (alloc.vec.Vec.deref fs) : _root_.Array OsuModel.Replay.Frame) = (fs.val.map abs).toArray := by
      show ((alloc.vec.Vec.deref fs).val.map abs).toArray = _; rw [ms_deref_val]
    rw [ef]
  obtain ⟨S, hS, hSrel⟩ := sim.schedule.steps_refines h64 k pb (alloc.vec.Vec.deref fs) (by simpa using hfs)
  obtain ⟨H, hH, hHrel⟩ := sim.scoring.mk_health_cfg_refines ev_tn pb c.legacy_health hcap
  have hHrel' : simRel (fun c => (abs c : OsuModel.Sim.HealthCfg)) H
      (OsuModel.Sim.mkHealthCfg (playableS ev_tn pb) (configS c).legacyHealth) := hHrel
  obtain ⟨B, hB, hBrel⟩ := sim.step.input_block_periods_refines ev_tn pb hbr
  obtain ⟨I1, hI1, hI1rel⟩ := sim.step.idx_list_refines ev_tn pb .Head false
  obtain ⟨I2, hI2, hI2rel⟩ := sim.step.idx_list_refines ev_tn pb .Tail true
  have hI1r := js_idx_bridge pb .Head .head rfl false I1 hI1rel
  have hI2r := js_idx_bridge pb .Tail .tail rfl true I2 hI2rel
  obtain ⟨M, hM, hMrel⟩ := sim.scoring.score_maxima_refines ev_tn pb c.score_multiplier c.rank_adjust hcap
  have hMrel' : { OsuModel.Sim.scoreMaxima (playableS ev_tn pb) (configS c).scoreMultiplier with
      rankAdjust := (configS c).rankAdjust } = abs M := hMrel
  obtain ⟨FO, hFO, hFOrel⟩ := sim.step.first_objects_refines ev_tn c pb
  obtain ⟨PE, hPE1, hPE2⟩ := hPE
  obtain ⟨A, hA, hArel⟩ := hAP
  rw [js_mkCtx_eq]
  unfold sim.step.mk_ctx js_mkS
  rw [sim.step.has_autopilot_refines c js_isAP (by intro u; cases u <;> rfl),
    sim.step.has_adaptive_refines c js_isAd (by intro u; cases u <;> rfl)]
  simp only [bind_ok]
  rw [eU, eD, eI, eR, eV, eM, eA, eL, eSt]
  simp only [hS, hH, hB, hI1, hI2, hM, hFO, hPE1, hA, hPE2, sim.geometry.receptor_corner_radius_pow_refines, bind_ok,
    js_lft]
  generalize OsuModel.Sim.steps (abs k) (abs pb) (abs (alloc.vec.Vec.deref fs)) = XS at hSrel ⊢
  generalize OsuModel.Sim.mkHealthCfg (playableS ev_tn pb) (configS c).legacyHealth = XH at hHrel' ⊢
  generalize OsuModel.Sim.inputBlockPeriods (playableS ev_tn pb) = XB at hBrel ⊢
  generalize Array.mapM (fun x => simIdxOfSpec x OsuModel.Sim.Kind.head false) (playableS ev_tn pb).objects = XI1 at hI1r ⊢
  generalize Array.mapM (fun x => simIdxOfSpec x OsuModel.Sim.Kind.tail true) (playableS ev_tn pb).objects = XI2 at hI2r ⊢
  generalize OsuModel.Sim.AutoGen.generate (playableS ev_tn pb) (configS c).rateMods.toList = XG at hArel ⊢
  have ei : alloc.vec.Vec.len c.input_blockers = 0#usize ↔ (configS c).inputBlockers.isEmpty = true := by
    have e1 : (alloc.vec.Vec.len c.input_blockers = 0#usize) ↔ c.input_blockers.val.length = 0 := by
      constructor
      · intro h; have := congrArg UScalar.val h; simpa using this
      · intro h; apply UScalar.eq_of_val_eq; simpa using h
    rw [e1]; simp [configS, abs]
  rcases Bool.eq_false_or_eq_true ((configS c).updatables.any js_isAP) with hb | hb
  · simp only [hb, ↓reduceIte]
    cases A with
    | Err e =>
      obtain ⟨m, rfl⟩ := hArel
      simp only [js_br_err, bind_ok, js_fr, except_bind_error]
      exact ⟨_, rfl, trivial⟩
    | Ok av =>
      obtain ⟨G, rfl, hG⟩ := hArel
      simp only [js_br_ok, bind_ok, except_bind_ok, except_pure, hG]
      js_tail1
  · simp only [hb, ↓reduceIte, Bool.false_eq_true, except_bind_ok, except_pure]
    js_tail1
-- CONDITIONAL: hAP, hPE -- both DISCHARGED: sim.step.ap_frames_of_refines (Eval/JsonApFrames), sim.step.preceding_end_times_refines (Eval/JsonPrecEnd); unconditional form js_mk_ctx_full (Eval/JsonMkCtx2, under ev_mkBounds)
/-- `mk_ctx` refines `mkCtx` (the relation part of `EvalAssumptions.mkCtx`), for configs related by `ev_cfgRel`, under
the size bounds of `steps` (frames < 2^32), `mk_health_cfg` / `score_maxima` (nested-object count) and
`input_block_periods` (breaks). -/
theorem sim.step.mk_ctx_refines (h64 : System.Platform.numBits = 64) (env : sim.geometry.Env) (c : sim.mods.Config)
    (pb : sim.playable.Playable) (fs : alloc.vec.Vec replay.frames.Frame) (k : sim.schedule.ScheduleKind)
    (C : OsuModel.Sim.Config) (hc : ev_cfgRel c C)
    (hfs : fs.val.length < 2^32)
    (hcap : (pb.objects.val.map (fun o => o.nested.val.length + 1)).sum < Usize.max)
    (hbr : pb.breaks.val.length < Usize.max)
    (hAP : ∃ r, sim.step.ap_frames_of pb c = ok r ∧
      match r with
      | .Ok v => ∃ G, OsuModel.Sim.AutoGen.generate (playableS ev_tn pb) (configS c).rateMods.toList = .ok G ∧
          G.map (fun f => (f.time, ({ x := f.pos.x, y := f.pos.y } : OsuModel.Sim.Vec2))) = js_apS v
      | .Err _ => ∃ m, OsuModel.Sim.AutoGen.generate (playableS ev_tn pb) (configS c).rateMods.toList = .error m)
    (hPE : ∃ v, sim.step.preceding_end_times pb = ok v ∧
      OsuModel.Sim.precedingEndTimes (playableS ev_tn pb) = .ok (js_peS v)) :
    ∃ r, sim.step.mk_ctx env c pb fs k = ok r ∧
    (match r, OsuModel.Sim.mkCtx (abs env) C (playableS ev_tn pb) (fs.val.map abs).toArray (ev_kindS k) with
     | .Ok ctx, .ok CTX => ctx.cfg = c ∧ CTX.cfg = C ∧ ctx.pb = pb ∧ CTX.pb = playableS ev_tn pb ∧ ev_ctxRel ctx CTX
     | .Err _, .error _ => True
     | _, _ => False) :=
  js_mk_ctx_refines h64 env c pb fs k C hc hfs hcap hbr hAP hPE

end OsuProofs
