/-
`sim::step::input_phase` (simcore2): the spec `Sim.inputPhase` factored as `sc2IPS` (`rfl`), the released/pressed
loops (`sc2_l0`, `sc2_l1`), the tail (high-frequency mouse move, hover), all generic over a caller invariant `I`
with the closure properties `sc2IPI` (sim3d's playfield frames, relax closure, `s3d_TPOk`, last_replay writes).
-/
import OsuProofs.Sim3.SD_Play2
import OsuProofs.Sim4.Spinner
import OsuProofs.Sim.InputPhase
import OsuProofs.Sim.ReplayDiff
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl OsuModel.Net

/-! ## the spec `inputPhase`, factored (checked by `rfl`) -/

/-- after the mouse block: `ReplayState.Apply` and the high-frequency mouse move -/
def sc2IPRest (hoc : OsuModel.Sim.DrawInfo) (hd : Bool) (cur : List OsuModel.Replay.Action) :
    OsuModel.Sim.SimM Unit := do
  let __do_lift ← get
  modify fun s => { s with lastReplay := some cur }
  forIn (OsuModel.Sim.Sim.replayStateDiff __do_lift.lastReplay cur).1 PUnit.unit fun a __s => do
    OsuModel.Sim.Sim.triggerReleased a
    pure (ForInStep.yield PUnit.unit)
  forIn (OsuModel.Sim.Sim.replayStateDiff __do_lift.lastReplay cur).2 PUnit.unit fun a __s => do
    OsuModel.Sim.Sim.triggerPressed a
    pure (ForInStep.yield PUnit.unit)
  let __do_lift ← get
  if __do_lift.mouseValid = true then do
    OsuModel.Sim.Sim.sliderMouseMove
    modify fun s => { s with cursorPos := hoc.toLocal s.mouse }
    if (!hd) = true then OsuModel.Sim.Sim.updateHover else pure ()
  else if (!hd) = true then OsuModel.Sim.Sim.updateHover else pure ()

/-- the current frame's actions -/
def sc2IPCur (C : OsuModel.Sim.Ctx) (step : OsuModel.Sim.Step) (K : List OsuModel.Replay.Action → OsuModel.Sim.SimM Unit) :
    OsuModel.Sim.SimM Unit :=
  if step.frameIndex < 0 then do
    let cur ← pure []
    K cur
  else do
    let __do_lift ← OsuModel.Sim.Sim.getA C.frames step.frameIndex.toNat "frames"
    let cur ← pure __do_lift.actions
    K cur

def sc2IPS : OsuModel.Sim.SimM Unit := fun C S =>
  (if (C.frames.size == 0) = true then pure ()
   else do
    let step ← OsuModel.Sim.Sim.stepAt S.k
    let gp ← OsuModel.Sim.Sim.replayPosition C.frames step.frameIndex S.t
    let hoc ← OsuModel.Sim.Sim.curHoc
    if (!S.mouseValid || !S.mouse.eq (hoc.toScreen gp)) = true then do
      modify fun (s : OsuModel.Sim.St) => { s with mouseValid := true, mouse := hoc.toScreen gp }
      OsuModel.Sim.Sim.sliderMouseMove
      OsuModel.Sim.Sim.spinnerMouseMove
      OsuModel.Sim.Sim.updateHover
      sc2IPCur C step (sc2IPRest hoc true)
    else sc2IPCur C step (sc2IPRest hoc false)) C S

theorem sc2_ip_eq (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) : OsuModel.Sim.Sim.inputPhase C S = sc2IPS C S := by
  rfl


/-- the tail after the pressed loop -/
def sc2TailS (hoc : OsuModel.Sim.DrawInfo) (hd : Bool) : OsuModel.Sim.SimM Unit := do
  let __do_lift ← get
  if __do_lift.mouseValid = true then do
    OsuModel.Sim.Sim.sliderMouseMove
    modify fun s => { s with cursorPos := hoc.toLocal s.mouse }
    if (!hd) = true then OsuModel.Sim.Sim.updateHover else pure ()
  else if (!hd) = true then OsuModel.Sim.Sim.updateHover else pure ()

theorem sc2_rest_eq (hoc : OsuModel.Sim.DrawInfo) (hd : Bool) (cur : List OsuModel.Replay.Action) :
    sc2IPRest hoc hd cur = (do
      let __do_lift ← get
      modify fun s => { s with lastReplay := some cur }
      forIn (OsuModel.Sim.Sim.replayStateDiff __do_lift.lastReplay cur).1 PUnit.unit fun a __s => do
        OsuModel.Sim.Sim.triggerReleased a
        pure (ForInStep.yield PUnit.unit)
      forIn (OsuModel.Sim.Sim.replayStateDiff __do_lift.lastReplay cur).2 PUnit.unit fun a __s => do
        OsuModel.Sim.Sim.triggerPressed a
        pure (ForInStep.yield PUnit.unit)
      sc2TailS hoc hd) := rfl

@[reducible] def sc2L1 (c : sim.state.Ctx) (s : sim.state.St) (hoc : sim.basic.DrawInfo) (hd : Bool)
    (pr : replay.frames.ActList) (m : Usize) :=
  sim.step.input_phase_loop1 c.env c.cfg c.pb c.frames c.steps c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time
    c.corner_pow c.prec_end c.ap_frames c.block_periods c.first_obj s hoc hd pr m

@[reducible] def sc2L1B (c : sim.state.Ctx) (s : sim.state.St) (hoc : sim.basic.DrawInfo) (hd : Bool)
    (pr : replay.frames.ActList) (m : Usize) :=
  sim.step.input_phase_loop1.body c.env c.cfg c.pb c.frames c.steps c.head_idx c.tail_idx c.smax c.hcfg
    c.last_frame_time c.corner_pow c.prec_end c.ap_frames c.block_periods c.first_obj hoc hd pr s m

theorem sc2_l1_step (c : sim.state.Ctx) (s : sim.state.St) (hoc : sim.basic.DrawInfo) (hd : Bool)
    (pr : replay.frames.ActList) (m : Usize) (r) (hb : sc2L1B c s hoc hd pr m = ok r) :
    sc2L1 c s hoc hd pr m = (match r with
      | .cont (s1, m1) => sc2L1 c s1 hoc hd pr m1
      | .done y => ok y) := by
  unfold sc2L1 sim.step.input_phase_loop1
  rw [loop_unfold]; dsimp only
  rw [show sim.step.input_phase_loop1.body _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = ok r from hb]
  simp only [bind_ok]
  cases r <;> rfl

theorem sc2_l1_done_mv (c : sim.state.Ctx) (s : sim.state.St) (hoc : sim.basic.DrawInfo) (hd : Bool)
    (pr : replay.frames.ActList) (m : Usize) (hm : ¬ m < pr.len) (hmv : s.mouse_valid = true) (s1 : sim.state.St)
    (hsm : sim.step.slider_mouse_move c s = ok s1) (v : sim.basic.Vec2) (hl : sim.basic.to_local hoc s1.mouse = ok v)
    (s2 : sim.state.St) (hu : hd = false → sim.step.update_hover c { s1 with cursor_pos := v } = ok s2) :
    sc2L1B c s hoc hd pr m = ok (.done (.Ok (), if hd then { s1 with cursor_pos := v } else s2)) := by
  have hc : (⟨c.env, c.cfg, c.pb, c.frames, c.steps, c.head_idx, c.tail_idx, c.smax, c.hcfg, c.last_frame_time,
      c.corner_pow, c.prec_end, c.ap_frames, c.block_periods, c.first_obj⟩ : sim.state.Ctx) = c := rfl
  simp only [sim.step.input_phase_loop1.body, hm, if_false, hc]
  rw [if_pos hmv]
  simp only [hsm, hl, bind_ok]
  cases hd
  · simp only [Bool.false_eq_true, if_false]
    have hu' := hu rfl
    exact (by simp only [show sim.step.update_hover c { s1 with cursor_pos := v } = ok s2 from hu', bind_ok] :
      (do let s3 ← sim.step.update_hover c { s1 with cursor_pos := v }; ok (ControlFlow.done (core.result.Result.Ok (), s3))) = ok (.done (.Ok (), s2)))
  · simp only [if_true]; rfl

theorem sc2_l1_done_nmv (c : sim.state.Ctx) (s : sim.state.St) (hoc : sim.basic.DrawInfo) (hd : Bool)
    (pr : replay.frames.ActList) (m : Usize) (hm : ¬ m < pr.len) (hmv : ¬ s.mouse_valid = true)
    (s2 : sim.state.St) (hu : hd = false → sim.step.update_hover c s = ok s2) :
    sc2L1B c s hoc hd pr m = ok (.done (.Ok (), if hd then s else s2)) := by
  have hc : (⟨c.env, c.cfg, c.pb, c.frames, c.steps, c.head_idx, c.tail_idx, c.smax, c.hcfg, c.last_frame_time,
      c.corner_pow, c.prec_end, c.ap_frames, c.block_periods, c.first_obj⟩ : sim.state.Ctx) = c := rfl
  simp only [sim.step.input_phase_loop1.body, hm, if_false, hc]
  rw [if_neg hmv]
  simp only [bind_ok]
  cases hd
  · simp only [Bool.false_eq_true, if_false]
    have hu' := hu rfl
    exact (by simp only [show sim.step.update_hover c s = ok s2 from hu', bind_ok] :
      (do let s3 ← sim.step.update_hover c s; ok (ControlFlow.done (core.result.Result.Ok (), s3))) = ok (.done (.Ok (), s2)))
  · simp only [if_true]; rfl

/-! ## the caller invariant -/

/-- what `input_phase` needs of the caller invariant `I` (as sim3d's `s3d_playfield_gen`) -/
structure sc2IPI (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (I : sim.state.St → Prop) : Prop where
  pinv : ∀ s, I s → s3d_PInv c s
  hfr : ∀ s s', I s → s3d_PInv c s' → s3d_HookFr c s s' → I s'
  cl : s3d_RelaxCl I
  tp : s3d_TPOk tn fo c I
  lr : ∀ s (l : replay.frames.ActList), I s → l.len.val ≤ 3 → I { s with last_replay := some l }
  lrk : ∀ s, I s → ∀ l, s.last_replay = some l → l.len.val ≤ 3

theorem sc2_I_ok {tn fo c I} (H : sc2IPI tn fo c I) {s s' : sim.state.St} (hI : I s) (h : s3d_OK c s s') : I s' := by
  have hP := H.pinv s hI
  have hik := s3d_OK_IK c s s' h hP.2.1
  obtain ⟨⟨o, rfl⟩, hinv, hl, hk, hkh⟩ := h
  exact H.hfr s _ hI (s3d_PInv_mk hP hinv hik rfl rfl hP.2.2.2.2.1 hP.2.2.2.2.2.1 rfl rfl rfl rfl hP.2.2.2.2.2.2.2.2)
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨s.ap_frame, s.mouse_valid, s.mouse, s.cursor_pos, o, rfl⟩, hinv, hl, hkh⟩))))

theorem sc2_I_mouse {tn fo c I} (H : sc2IPI tn fo c I) {s : sim.state.St} (hI : I s) (mv : Bool) (m cp : sim.basic.Vec2) :
    I { s with mouse_valid := mv, mouse := m, cursor_pos := cp } := by
  have hP := H.pinv s hI
  have hinv : SimInv c { s with mouse_valid := mv, mouse := m, cursor_pos := cp } := s3b_inv_of hP.1 rfl rfl
  exact H.hfr s _ hI (s3d_PInv_mk hP hinv (s3d_IK_of rfl rfl rfl rfl hP.2.1) rfl rfl hP.2.2.2.2.1 hP.2.2.2.2.2.1 rfl rfl
    rfl rfl hP.2.2.2.2.2.2.2.2)
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨s.ap_frame, mv, m, cp, s.objs, rfl⟩, hinv, rfl, fun _ _ _ => rfl⟩))))

theorem sc2_act {c : sim.state.Ctx} {s : sim.state.St} (hP : s3d_PInv c s) :
    ∀ i ∈ s.active.val, i.val < s.objs.val.length := fun i hi => hP.1.objs_len ▸ hP.2.2.1 i hi

/-- the tail after the pressed loop -/
theorem sc2_tail (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (I : sim.state.St → Prop)
    (H : sc2IPI tn fo c I) (hcp : c.corner_pow = OsuModel.Sim.receptorCornerRadiusPow) (hoc : sim.basic.DrawInfo)
    (hd : Bool) (s : sim.state.St) (hI : I s) (pr : replay.frames.ActList) (m : Usize) (hm : ¬ m < pr.len) :
    ∃ s', sc2L1B c s hoc hd pr m = ok (.done (.Ok (), s')) ∧
      sc2TailS (abs hoc) hd (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧ I s' := by
  have hP := H.pinv s hI
  by_cases hmv : s.mouse_valid = true
  · obtain ⟨s1, r1, e1, -⟩ := sim.step.slider_mouse_move_refines tn fo c s hP.1 (sc2_act hP)
    obtain ⟨k1, -, -⟩ := s3d_smm_OK c s s1 hP.1 (sc2_act hP) r1
    have hI1 := sc2_I_ok H hI k1
    obtain ⟨v, hv, ev⟩ := sim.basic.to_local_refines hoc s1.mouse
    have hI1' : I { s1 with cursor_pos := v } := sc2_I_mouse H hI1 s1.mouse_valid s1.mouse v
    have hP1 := H.pinv _ hI1'
    obtain ⟨s2, r2, e2, k2⟩ := s3d_uh_OK tn fo c { s1 with cursor_pos := v } hP1.1 hP1.2.1 hcp
    have hI2 := sc2_I_ok H hI1' k2
    have eS : ({ simStS tn s1 with cursorPos := (abs hoc : OsuModel.Sim.DrawInfo).toLocal (simStS tn s1).mouse } :
        OsuModel.Sim.St) = simStS tn { s1 with cursor_pos := v } := by
      rw [show (simStS tn s1).mouse = abs s1.mouse from rfl, ev]; rfl
    refine ⟨if hd then { s1 with cursor_pos := v } else s2,
      sc2_l1_done_mv c s hoc hd pr m hm hmv s1 r1 v hv s2 (fun _ => r2), ?_, by cases hd <;> simp [hI1', hI2]⟩
    simp only [sc2TailS, simM_bind, simM_get, Except.bind, show (simStS tn s).mouseValid = s.mouse_valid from rfl, hmv,
      if_true, e1, simM_modify, eS]
    cases hd
    · simp only [Bool.not_false, if_true, e2, Bool.false_eq_true, if_false]
    · simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true, simM_pure]
  · have hP1 := hP
    obtain ⟨s2, r2, e2, k2⟩ := s3d_uh_OK tn fo c s hP.1 hP.2.1 hcp
    have hI2 := sc2_I_ok H hI k2
    refine ⟨if hd then s else s2, sc2_l1_done_nmv c s hoc hd pr m hm hmv s2 (fun _ => r2), ?_,
      by cases hd <;> simp [hI, hI2]⟩
    simp only [sc2TailS, simM_bind, simM_get, Except.bind, show (simStS tn s).mouseValid = s.mouse_valid from rfl,
      hmv, Bool.false_eq_true, if_false]
    cases hd
    · simp only [Bool.not_false, if_true, e2, Bool.false_eq_true, if_false]
    · simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true, simM_pure]

theorem sc2_act_drop (l : replay.frames.ActList) (m : Nat) (hm : m < l.len.val) (hl : l.len.val ≤ 3) :
    (actListS l).drop m = actS (l.items.val[m]'(by rw [s2_items_len]; omega)) :: (actListS l).drop (m + 1) := by
  unfold actListS
  rw [List.drop_eq_getElem_cons (by simp [s2_items_len]; omega)]
  simp [List.getElem_map, List.getElem_take]


theorem sc2_l1 (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (I : sim.state.St → Prop)
    (H : sc2IPI tn fo c I) (hcp : c.corner_pow = OsuModel.Sim.receptorCornerRadiusPow) (hoc : sim.basic.DrawInfo)
    (hd : Bool) (pr : replay.frames.ActList) (hpr : pr.len.val ≤ 3) :
    ∀ n (m : Usize) (s : sim.state.St), pr.len.val - m.val = n → m.val ≤ pr.len.val → I s →
      ∃ r s', sc2L1 c s hoc hd pr m = ok (r, s') ∧
        s3b_rrel (fun _ => ()) (simStS tn s') r ((do
          forIn ((actListS pr).drop m.val) PUnit.unit (fun a __s => do
            OsuModel.Sim.Sim.triggerPressed a
            pure (ForInStep.yield PUnit.unit))
          sc2TailS (abs hoc) hd) (simCtxS tn fo c) (simStS tn s)) ∧ (r = .Ok () → I s') := by
  intro n
  induction n with
  | zero =>
    intro m s hn hm hI
    have hm' : ¬ m < pr.len := by intro h; have : m.val < pr.len.val := h; omega
    obtain ⟨s', e1, e2, hI'⟩ := sc2_tail tn fo c I H hcp hoc hd s hI pr m hm'
    refine ⟨.Ok (), s', by rw [sc2_l1_step c s hoc hd pr m _ e1], ?_, fun _ => hI'⟩
    have : (actListS pr).drop m.val = [] := List.drop_eq_nil_of_le (by simp [actListS, s2_items_len]; omega)
    simp only [this, List.forIn_nil, simM_bind, simM_pure, Except.bind, s3b_rrel, e2]
  | succ n ih =>
    intro m s hn hm hI
    have hml : m.val < pr.len.val := by omega
    have hmi : m.val < pr.items.val.length := by rw [s2_items_len]; omega
    have hlt : m < pr.len := hml
    obtain ⟨m1, hm1, hm1v⟩ := usize_add_one m (by scalar_tac)
    obtain ⟨r, s1, et, rt, it⟩ := H.tp s (pr.items.val[m.val]'hmi) hI
    have hc : (⟨c.env, c.cfg, c.pb, c.frames, c.steps, c.head_idx, c.tail_idx, c.smax, c.hcfg, c.last_frame_time,
        c.corner_pow, c.prec_end, c.ap_frames, c.block_periods, c.first_obj⟩ : sim.state.Ctx) = c := rfl
    rw [sc2_act_drop pr m.val hml hpr, List.forIn_cons]
    have eaS : (abs (pr.items.val[m.val]'hmi) : OsuModel.Replay.Action) = actS (pr.items.val[m.val]'hmi) := rfl
    cases r with
    | Err er =>
      obtain ⟨msg, hmsg⟩ := rt
      have hb : sc2L1B c s hoc hd pr m = ok (.done (.Err er, s1)) := by
        simp only [sim.step.input_phase_loop1.body, hlt, if_true, s2_arr_index _ _ hmi, bind_ok, hc, et,
          core.result.Result.Insts.CoreOpsTry.branch]
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]
      refine ⟨.Err er, s1, by rw [sc2_l1_step c s hoc hd pr m _ hb], ⟨msg, ?_⟩, fun h => by cases h⟩
      rw [eaS] at hmsg
      simp only [simM_bind, hmsg, Except.bind]
    | Ok u =>
      cases u
      have hI1 := it rfl
      have hb : sc2L1B c s hoc hd pr m = ok (.cont (s1, m1)) := by
        simp only [sim.step.input_phase_loop1.body, hlt, if_true, s2_arr_index _ _ hmi, bind_ok, hc, et,
          uncurry_apply_pair]
        simp [core.result.Result.Insts.CoreOpsTry.branch, hm1]
      obtain ⟨r2, s2, e2, rr2, i2⟩ := ih m1 s1 (by omega) (by omega) hI1
      refine ⟨r2, s2, by rw [sc2_l1_step c s hoc hd pr m _ hb]; exact e2, ?_, i2⟩
      simp only [s3b_rrel] at rt
      rw [eaS] at rt
      rw [show m.val + 1 = m1.val from hm1v.symm]
      simp only [simM_bind, rt, Except.bind, simM_pure] at rr2 ⊢
      exact rr2

theorem sc2_l0_step (s : sim.state.St) (rel : replay.frames.ActList) (k : Usize) (r)
    (hb : sim.step.input_phase_loop0.body rel s k = ok r) :
    sim.step.input_phase_loop0 s rel k = (match r with
      | .cont (s1, k1) => sim.step.input_phase_loop0 s1 rel k1
      | .done y => ok y) := by
  unfold sim.step.input_phase_loop0
  rw [loop_unfold]; dsimp only
  simp only [hb, bind_ok]
  cases r <;> rfl

theorem sc2_l0 (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (I : sim.state.St → Prop)
    (H : sc2IPI tn fo c I) (rel : replay.frames.ActList) (hrel : rel.len.val ≤ 3) :
    ∀ n (k : Usize) (s : sim.state.St), rel.len.val - k.val = n → k.val ≤ rel.len.val → I s →
      ∃ s', sim.step.input_phase_loop0 s rel k = ok s' ∧
        forIn (m := OsuModel.Sim.SimM) ((actListS rel).drop k.val) PUnit.unit (fun a __s => do
            OsuModel.Sim.Sim.triggerReleased a
            pure (ForInStep.yield PUnit.unit)) (simCtxS tn fo c) (simStS tn s) = .ok (PUnit.unit, simStS tn s') ∧
        I s' := by
  intro n
  induction n with
  | zero =>
    intro k s hn hk hI
    have hk' : ¬ k < rel.len := by intro h; have : k.val < rel.len.val := h; omega
    have hb : sim.step.input_phase_loop0.body rel s k = ok (.done s) := by
      simp [sim.step.input_phase_loop0.body, hk']
    refine ⟨s, by rw [sc2_l0_step s rel k _ hb], ?_, hI⟩
    have : (actListS rel).drop k.val = [] := List.drop_eq_nil_of_le (by simp [actListS, s2_items_len]; omega)
    simp only [this, List.forIn_nil, simM_pure]
  | succ n ih =>
    intro k s hn hk hI
    have hkl : k.val < rel.len.val := by omega
    have hki : k.val < rel.items.val.length := by rw [s2_items_len]; omega
    have hlt : k < rel.len := hkl
    obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by scalar_tac)
    obtain ⟨p, e1, hp, e2, hsub, -⟩ := s3d_trigger_released_frame tn fo c s (rel.items.val[k.val]'hki) (H.cl.1 s hI)
    have hI1 : I { s with pressed := p } := H.cl.2 s s.relax_down s.relax_last s.relax_was_left p hI hp hsub
    have hb : sim.step.input_phase_loop0.body rel s k = ok (.cont ({ s with pressed := p }, k1)) := by
      simp only [sim.step.input_phase_loop0.body, hlt, if_true, s2_arr_index _ _ hki, bind_ok, e1, hk1]
    obtain ⟨s', e3, e4, hI'⟩ := ih k1 _ (by omega) (by omega) hI1
    refine ⟨s', by rw [sc2_l0_step s rel k _ hb]; exact e3, ?_, hI'⟩
    rw [sc2_act_drop rel k.val hkl hrel, List.forIn_cons]
    have eaS : (abs (rel.items.val[k.val]'hki) : OsuModel.Replay.Action) = actS (rel.items.val[k.val]'hki) := rfl
    rw [eaS] at e2
    rw [show k.val + 1 = k1.val from hk1v.symm]
    simp only [simM_bind, e2, Except.bind, simM_pure]
    exact e4

/-- the current frame's actions (Rust `cur`) -/
theorem sc2_cur (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (step : schedule.Step)
    (hfi : step.frame_index.val < (c.frames.val.length : Int))
    (hfa : ∀ f ∈ c.frames.val, f.actions.len.val ≤ 3) :
    ∃ cur : replay.frames.ActList,
      (if step.frame_index < 0#i64 then ok replay.frames.ACTLIST_EMPTY else do
        let i1 ← lift (IScalar.hcast .Usize step.frame_index)
        let f ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice replay.frames.Frame) c.frames i1
        ok f.actions) = ok cur ∧ cur.len.val ≤ 3 ∧
      ∀ K S, sc2IPCur (simCtxS tn fo c) (abs step) K (simCtxS tn fo c) S = K (actListS cur) (simCtxS tn fo c) S := by
  have hfS : (abs step : OsuModel.Sim.Step).frameIndex = step.frame_index.val := rfl
  by_cases hn : step.frame_index < 0#i64
  · refine ⟨replay.frames.ACTLIST_EMPTY, by simp [hn], by simp [s2_empty_val.2], fun K S => ?_⟩
    have hn' : step.frame_index.val < 0 := hn
    simp only [sc2IPCur, hfS, hn', decide_true, if_true, simM_bind, simM_pure, Except.bind]
    rw [show actListS replay.frames.ACTLIST_EMPTY = [] from s2_abs_empty]
  · have hn' : ¬ step.frame_index.val < 0 := hn
    have h0 : 0 ≤ step.frame_index.val := by omega
    have hj : step.frame_index.val.toNat < c.frames.val.length := by omega
    have hcv : (IScalar.hcast .Usize step.frame_index).val = step.frame_index.val.toNat :=
      sim_i64_cast_usize _ h0 (by have := c.frames.property; omega)
    have hj' : (IScalar.hcast .Usize step.frame_index).val < c.frames.val.length := by rw [hcv]; exact hj
    refine ⟨(c.frames.val[step.frame_index.val.toNat]'hj).actions, ?_, hfa _ (List.getElem_mem hj), fun K S => ?_⟩
    · simp only [hn, if_false, lift, bind_ok, vec_index_eq _ _ hj']
      simp only [hcv]
    · have hjS : step.frame_index.val.toNat < (simCtxS tn fo c).frames.size := by simpa [simCtxS, abs] using hj
      simp only [sc2IPCur, hfS, hn', decide_false, Bool.false_eq_true, if_false, simM_bind, s4_getA _ _ _ hjS,
        Except.bind, simM_pure]
      have : ((simCtxS tn fo c).frames[step.frame_index.val.toNat]'hjS).actions =
          actListS (c.frames.val[step.frame_index.val.toNat]'hj).actions := by
        simp [simCtxS, abs]
      rw [this]

theorem sc2_rest (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (I : sim.state.St → Prop)
    (H : sc2IPI tn fo c I) (hcp : c.corner_pow = OsuModel.Sim.receptorCornerRadiusPow) (hoc : sim.basic.DrawInfo)
    (hd : Bool) (cur : replay.frames.ActList) (hcur : cur.len.val ≤ 3) (s2 : sim.state.St) (hI : I s2) :
    ∃ r s', (do
        let (released, pressed) ← sim.step.replay_state_diff s2.last_replay cur
        let s3 ← sim.step.input_phase_loop0 { s2 with last_replay := (some cur) } released 0#usize
        sc2L1 c s3 hoc hd pressed 0#usize) = ok (r, s') ∧
      s3b_rrel (fun _ => ()) (simStS tn s') r (sc2IPRest (abs hoc) hd (actListS cur) (simCtxS tn fo c) (simStS tn s2)) ∧
      (r = .Ok () → I s') := by
  obtain ⟨⟨rel, pr⟩, hrp, hr1, hr2, erp⟩ := sim.step.replay_state_diff_refines s2.last_replay cur (H.lrk s2 hI) hcur
  dsimp only at hr1 hr2 erp
  have hI1 := H.lr s2 cur hI hcur
  obtain ⟨s3, e3, f3, hI3⟩ := sc2_l0 tn fo c I H rel hr1 _ 0#usize _ rfl (by simp) hI1
  obtain ⟨r, s', e4, rr4, i4⟩ := sc2_l1 tn fo c I H hcp hoc hd pr hr2 _ 0#usize s3 rfl (by simp) hI3
  refine ⟨r, s', ?_, ?_, i4⟩
  · rw [hrp]; simp only [bind_ok]
    change (do let s3 ← sim.step.input_phase_loop0 { s2 with last_replay := some cur } rel 0#usize
               sc2L1 c s3 hoc hd pr 0#usize) = _
    rw [e3]; first | exact (bind_ok _ _).trans e4 | (rw [bind_ok]; exact e4) | simpa using e4
  · rw [sc2_rest_eq]
    have hLR : (simStS tn s2).lastReplay = s2.last_replay.map (fun l => (abs l : List OsuModel.Replay.Action)) := rfl
    have eM : ({ simStS tn s2 with lastReplay := some (actListS cur) } : OsuModel.Sim.St) =
        simStS tn { s2 with last_replay := some cur } := rfl
    have h00 : (0#usize).val = 0 := rfl
    simp only [h00, List.drop_zero] at f3 rr4
    simp only [simM_bind, simM_get, Except.bind, simM_modify, hLR, show actListS cur = (abs cur : List OsuModel.Replay.Action) from rfl, erp]
    rw [show (abs rel : List OsuModel.Replay.Action) = actListS rel from rfl,
      show (abs pr : List OsuModel.Replay.Action) = actListS pr from rfl, show (abs cur : List OsuModel.Replay.Action) = actListS cur from rfl, eM, f3]
    simp only [simM_bind] at rr4
    exact rr4

/-- `input_phase` (Rust) refines `Sim.inputPhase` for any caller invariant `I` with the `sc2IPI` closure properties -/
-- NOT-CONDITIONAL: hfl/hfi/hfa are context premises (schedule/frame well-formedness), hk the step index of `run`
theorem sim.step.input_phase_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (I : sim.state.St → Prop) (H : sc2IPI tn fo c I) (hcp : c.corner_pow = OsuModel.Sim.receptorCornerRadiusPow)
    (hfl : c.frames.val.length < 2 ^ 63)
    (hfi : ∀ st ∈ c.steps.val, -1 ≤ st.frame_index.val ∧ st.frame_index.val < (c.frames.val.length : Int))
    (hfa : ∀ f ∈ c.frames.val, f.actions.len.val ≤ 3)
    (s : sim.state.St) (hk : s.k.val < c.steps.val.length) (hI : I s) :
    ∃ r s', sim.step.input_phase c s = ok (r, s') ∧
      s3b_rrel (fun _ => ()) (simStS tn s') r (OsuModel.Sim.Sim.inputPhase (simCtxS tn fo c) (simStS tn s)) ∧
      (r = .Ok () → I s') := by
  rw [sc2_ip_eq]
  unfold sim.step.input_phase sc2IPS
  have hfS : (simCtxS tn fo c).frames.size = c.frames.val.length := by simp [simCtxS, abs]
  by_cases hf0 : c.frames.val.length = 0
  · have h0 : alloc.vec.Vec.len c.frames = 0#usize := by apply UScalar.eq_of_val_eq; simp [hf0]
    refine ⟨.Ok (), s, by simp [h0], ?_, fun _ => hI⟩
    simp [hfS, hf0, s3b_rrel]
  have h0 : ¬ alloc.vec.Vec.len c.frames = 0#usize := by
    intro h; apply hf0; have := congrArg UScalar.val h; simpa using this
  have hfb : ((simCtxS tn fo c).frames.size == 0) = false := by simp [hfS, hf0]
  simp only [h0, if_false, hfb, Bool.false_eq_true, vec_index_eq _ _ hk, bind_ok]
  generalize hst : c.steps.val[s.k.val]'hk = step
  have hstm : step ∈ c.steps.val := hst ▸ List.getElem_mem hk
  obtain ⟨hfi0, hfi1⟩ := hfi step hstm
  have hkS : s.k.val < (simCtxS tn fo c).steps.size := by simpa [simCtxS, abs] using hk
  have estep : OsuModel.Sim.Sim.stepAt (simStS tn s).k (simCtxS tn fo c) (simStS tn s) = .ok (abs step, simStS tn s) := by
    simp only [OsuModel.Sim.Sim.stepAt, OsuModel.Sim.Sim.ctx, simM_bind, simM_read, Except.bind]
    rw [show (simStS tn s).k = s.k.val from rfl, s4_getA _ _ _ hkS]
    simp [simCtxS, abs, ← hst]
  obtain ⟨gp, hgp, egp⟩ := sim.step.replay_position_refines (alloc.vec.Vec.deref c.frames) step.frame_index s.t
    (by simp [alloc.vec.Vec.deref]; omega) (by simpa [alloc.vec.Vec.deref] using hfl) hfi0 (by simpa [alloc.vec.Vec.deref] using hfi1)
  have egp' : OsuModel.Sim.Sim.replayPosition (simCtxS tn fo c).frames (abs step : OsuModel.Sim.Step).frameIndex
      (simStS tn s).t (simCtxS tn fo c) (simStS tn s) = .ok (abs gp, simStS tn s) := by
    have := egp (simCtxS tn fo c) (simStS tn s)
    simpa [alloc.vec.Vec.deref, simCtxS, abs] using this
  obtain ⟨d, hd, ed⟩ := sim.step.cur_hoc_refines tn fo c s
  obtain ⟨scr, hscr, escr⟩ := sim.basic.to_screen_refines d gp
  obtain ⟨b, hb, eb⟩ := sim.basic.Vec2.eq_refines s.mouse scr
  simp only [simM_bind, estep, Except.bind, egp', ed, hgp, hd, hscr, bind_ok, escr]
  rw [show (simStS tn s).mouse = abs s.mouse from rfl, show (simStS tn s).mouseValid = s.mouse_valid from rfl, eb]
  have hP := H.pinv s hI
  obtain ⟨cur, ecur, hcur, Ecur⟩ := sc2_cur tn fo c step hfi1 hfa
  by_cases hmb : s.mouse_valid = true ∧ b = true
  · obtain ⟨hm1, hm2⟩ := hmb
    have hc : (!s.mouse_valid || !(abs b : Bool)) = false := by simp [hm1, hm2, abs]
    simp only [hc, Bool.false_eq_true, if_false]
    rw [if_pos hm1]
    simp only [hb, hm2, bind_ok, if_true, ecur, Ecur]
    obtain ⟨r, s', e1, r1, i1⟩ := sc2_rest tn fo c I H hcp d false cur hcur s hI
    exact ⟨r, s', e1, r1, i1⟩
  · have hc : (!s.mouse_valid || !(abs b : Bool)) = true := by
      cases h1 : s.mouse_valid <;> cases h2 : b <;> simp_all [abs]
    simp only [hc, if_true, simM_modify]
    have hI1 : I { s with mouse_valid := true, mouse := scr } := sc2_I_mouse H hI true scr s.cursor_pos
    have hP1 := H.pinv _ hI1
    obtain ⟨s2, s3, s4, r2, r3, r4, e2, e3, e4, k4⟩ := s3d_mm_chain tn fo c { s with mouse_valid := true, mouse := scr }
      hP1.1 hP1.2.1 (sc2_act hP1) hcp
    have hI4 := sc2_I_ok H hI1 k4
    have eM : ({ simStS tn s with mouseValid := true, mouse := abs scr } : OsuModel.Sim.St) =
        simStS tn { s with mouse_valid := true, mouse := scr } := rfl
    simp only [simM_bind, simM_modify, Except.bind]
    simp only [eM, e2, e3, e4, Except.bind, Ecur]
    obtain ⟨r, s', e5, r5, i5⟩ := sc2_rest tn fo c I H hcp d true cur hcur s4 hI4
    refine ⟨r, s', ?_, r5, i5⟩
    have hR : (if s.mouse_valid = true then do
          let b ← sim.basic.Vec2.eq s.mouse scr
          if b = true then ok (s, false) else do
            let s3 ← sim.step.slider_mouse_move c { s with mouse := scr }
            let s4 ← sim.step.spinner_mouse_move c s3
            let s5 ← sim.step.update_hover c s4
            ok (s5, true)
        else do
          let s3 ← sim.step.slider_mouse_move c { s with mouse_valid := true, mouse := scr }
          let s4 ← sim.step.spinner_mouse_move c s3
          let s5 ← sim.step.update_hover c s4
          ok (s5, true)) = ok (s4, true) := by
      by_cases hm1 : s.mouse_valid = true
      · have hb2 : b = false := by cases b <;> simp_all
        have es : ({ s with mouse := scr } : sim.state.St) = { s with mouse_valid := true, mouse := scr } := by
          cases s; simp_all
        rw [if_pos hm1]; simp only [hb, hb2, bind_ok, Bool.false_eq_true, if_false, es, r2, r3, r4]
      · rw [if_neg hm1]; simp only [r2, r3, r4, bind_ok]
    rw [hR]; simp only [bind_ok, ecur]
    exact e5

end OsuProofs
