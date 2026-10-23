/-
sim3a (D37): slider tracking (`SliderInputManager`) leaves of `sim::step` (Rust) refine `OsuModel.Sim.Sim`
(Step.lean "Sliders"): `slider_data`, `mouse_in_follow_area`, `is_left_or_right`, `is_valid_tracking_action`,
`any_valid_tracking_action`, `update_tracking`.
Error relation for `Result<_, SimErr>` against a `SimM` value at a state: `s3aR` (Ok ↦ `.ok (f v, S')`, Err ↦ some
`.error`). State updates are stated as an explicit `Vec.set` of one `OState` (so `objs`/`insts` sizes and the
nested arrays are visibly preserved), and `SimInv` is carried over.
-/
import OsuProofs.Sim3.SA_Geom
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

/-- `Result<T, SimErr>` (Rust) vs a spec `SimM` evaluation: `Ok v` ↦ `.ok (f v, S)`, `Err` ↦ the spec rejects. -/
def s3aR {α β : Type} (f : α → β) (S : OsuModel.Sim.St) :
    core.result.Result α sim.err.SimErr → Except String (β × OsuModel.Sim.St) → Prop
  | .Ok v, e => e = .ok (f v, S)
  | .Err _, e => ∃ m, e = .error m

theorem s3a_s2actS : s2_actS = actS := by funext x; cases x <;> rfl

/-! ## SimInv after replacing one object state (same nested array) -/
theorem s3a_inv_set (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (o' : sim.state.OState)
    (hinv : SimInv c s) (hi : i.val < s.objs.val.length) (hn : o'.nested = (s.objs.val[i.val]'hi).nested) :
    SimInv c { s with objs := alloc.vec.Vec.set s.objs i o' } := by
  refine ⟨?_, ?_, hinv.nested_small, hinv.dict_in, hinv.dict_small⟩
  · simp [alloc.vec.Vec.set, hinv.objs_len]
  · intro j h1 h2
    have hv : (alloc.vec.Vec.set s.objs i o').val = s.objs.val.set i.val o' := vec_set_val' _ _ _
    have h1' : j < s.objs.val.length := by simpa [hv] using h1
    simp only [hv, List.getElem_set]
    split
    · rename_i hj; subst hj; rw [hn]; exact hinv.nested_len _ hi h2
    · exact hinv.nested_len _ h1' h2

theorem s3a_abs_get (v : alloc.vec.Vec sim.state.OState) (j : Nat) (h : j < (abs v : _root_.Array OsuModel.Sim.OState).size) :
    (abs v : _root_.Array OsuModel.Sim.OState)[j] = ostateS (v.val[j]'(by simpa [abs] using h)) := by simp [abs]

theorem s3a_objs_modify (tn) (s : sim.state.St) (i : Usize) (hi : i.val < s.objs.val.length)
    (f : OsuModel.Sim.OState → OsuModel.Sim.OState) (o' : sim.state.OState)
    (hf : f (ostateS (s.objs.val[i.val]'hi)) = ostateS o') :
    (simStS tn s).objs.modify i.val f = abs (alloc.vec.Vec.set s.objs i o') := by
  apply Array.ext
  · simp [simStS, abs, vec_set_val']
  · intro j h1 h2
    simp only [Array.getElem_modify]
    have hv : (alloc.vec.Vec.set s.objs i o').val = s.objs.val.set i.val o' := vec_set_val' _ _ _
    have e1 : ∀ k (hk : k < (simStS tn s).objs.size), (simStS tn s).objs[k]'hk = ostateS (s.objs.val[k]'(by simpa using hk)) :=
      fun k hk => sim_stS_obj tn s k hk
    rw [e1]
    rw [s3a_abs_get]
    simp only [hv, List.getElem_set]
    split
    · rename_i hj; subst hj; simp [hf]
    · rename_i hj; simp [hj]

theorem s3a_modifyObj (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (hi : i.val < s.objs.val.length)
    (f : OsuModel.Sim.OState → OsuModel.Sim.OState) (o' : sim.state.OState)
    (hf : f (ostateS (s.objs.val[i.val]'hi)) = ostateS o') :
    OsuModel.Sim.Sim.modifyObj i.val f (simCtxS tn fo c) (simStS tn s) =
      .ok ((), simStS tn { s with objs := alloc.vec.Vec.set s.objs i o' }) := by
  have hi' : i.val < (simStS tn s).objs.size := by simpa using hi
  simp only [OsuModel.Sim.Sim.modifyObj, OsuModel.Sim.Sim.checkIdx, OsuModel.Sim.Sim.st, simM_bind, simM_get,
    Except.bind, simM_ite, if_pos hi', simM_pure, simM_modify]
  rw [s3a_objs_modify tn s i hi f o' hf]
  rfl

/-! ## tracking actions -/
theorem sim.step.is_left_or_right_refines (a : replay.frames.Action) :
    sim.step.is_left_or_right a = ok (actS a == OsuModel.Replay.Action.left || actS a == OsuModel.Replay.Action.right) := by
  cases a <;> simp [sim.step.is_left_or_right, s2_actS, actS] <;> rfl

@[simp] theorem s3a_ostateS_hitAction (o : sim.state.OState) : (ostateS o).hitAction = o.hit_action.map actS := rfl
@[simp] theorem s3a_ostateS_acceptAnyAfter (o : sim.state.OState) : (ostateS o).acceptAnyAfter = o.accept_any_after := rfl

theorem sim.step.is_valid_tracking_action_refines (os : sim.state.OState) (t : F64) (a : replay.frames.Action) :
    sim.step.is_valid_tracking_action os t a = ok (OsuModel.Sim.Sim.isValidTrackingAction (abs os) t (abs a)) := by
  unfold sim.step.is_valid_tracking_action OsuModel.Sim.Sim.isValidTrackingAction
  show _ = ok (match (ostateS os).hitAction with
    | some ha => if (ostateS os).acceptAnyAfter.isNone || (match (ostateS os).acceptAnyAfter with | some x => t ≤ x | none => true) then actS a == ha
      else actS a == OsuModel.Replay.Action.left || actS a == OsuModel.Replay.Action.right
    | none => actS a == OsuModel.Replay.Action.left || actS a == OsuModel.Replay.Action.right)
  simp only [s3a_ostateS_hitAction, s3a_ostateS_acceptAnyAfter]
  cases hh : os.hit_action with
  | none => simp [sim.step.is_left_or_right_refines]
  | some ha =>
    rcases Option.eq_none_or_eq_some os.accept_any_after with hx | ⟨x, hx⟩
    · simp [hx, s3a_s2actS]
    · by_cases hl : t ≤ x
      · simp [hx, float.F64.le, hl, s3a_s2actS]
      · simp [hx, float.F64.le, hl, sim.step.is_left_or_right_refines]

theorem s3a_absAct (x : replay.frames.Action) : (abs x : OsuModel.Replay.Action) = actS x := by cases x <;> rfl

theorem sim.step.any_valid_tracking_action_refines (os : sim.state.OState) (t : F64) (pressed : replay.frames.ActList)
    (hl : pressed.len.val ≤ 3) :
    sim.step.any_valid_tracking_action os t pressed =
      ok ((actListS pressed).any (OsuModel.Sim.Sim.isValidTrackingAction (abs os) t)) := by
  have hp := pressed.items.property
  obtain ⟨items, len⟩ := pressed
  simp only at hl hp ⊢
  unfold sim.step.any_valid_tracking_action sim.step.any_valid_tracking_action_loop
  obtain ⟨x0, x1, x2, hx⟩ := s2_arr3 items
  rcases s2_usize_cases len hl with h | h | h | h <;> subst h <;>
  · repeat (rw [loop_unfold]; simp [sim.step.any_valid_tracking_action_loop.body, s2_arr3_i0 hx, s2_arr3_i1 hx,
      s2_arr3_i2 hx, sim.step.is_valid_tracking_action_refines])
    all_goals simp [actListS, hx, s3a_absAct, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc]

/-! ## updateTracking -/
theorem s3a_absAL (l : replay.frames.ActList) : (abs l : List OsuModel.Replay.Action) = actListS l := rfl
theorem s3a_abs_os (o : sim.state.OState) : (abs o : OsuModel.Sim.OState) = ostateS o := rfl
/-- the `acceptAnyAfter` that `updateTracking` writes -/
def s3aAA (o : sim.state.OState) (t : F64) : Option F64 :=
  match o.hit_action with
  | none => none
  | some ha => match o.accept_any_after with
    | some x => some x
    | none => if (actListS o.last_pressed).contains
        (if actS ha == OsuModel.Replay.Action.right then OsuModel.Replay.Action.left else OsuModel.Replay.Action.right)
        then none else some t

/-- the object state after `updateTracking` -/
def s3aTracked (o : sim.state.OState) (t endT : F64) (aj vp : Bool) (pressed : replay.frames.ActList) : sim.state.OState :=
  { o with accept_any_after := s3aAA o t, last_pressed := pressed,
           tracking := (!aj || decide (t ≤ endT)) && vp &&
             (actListS pressed).any (OsuModel.Sim.Sim.isValidTrackingAction (ostateS { o with accept_any_after := s3aAA o t }) t) }

/-- the object update of `updateTracking` (copied from Step.lean; `s3a_updateTracking_eq` checks it by `rfl`) -/
def s3aF (t : F64) (pressed : _root_.Array OsuModel.Replay.Action) (aj : Bool) (endT : F64) (validPos : Bool) :
    OsuModel.Sim.OState → OsuModel.Sim.OState := fun os => Id.run do
  let mut os := os
  if os.hitAction.isNone then os := { os with acceptAnyAfter := none }
  if let some ha := os.hitAction then
    if os.acceptAnyAfter.isNone then
      let other := if ha == .right then OsuModel.Replay.Action.left else OsuModel.Replay.Action.right
      if !(os.lastPressed.contains other) then os := { os with acceptAnyAfter := some t }
  let valid := pressed.any (OsuModel.Sim.Sim.isValidTrackingAction os t)
  { os with lastPressed := pressed.toList
            tracking := (!aj || t ≤ endT) && validPos && valid }

theorem s3a_updateTracking_eq (i : Nat) (vp : Bool) :
    OsuModel.Sim.Sim.updateTracking i vp = (do
      let t := (← OsuModel.Sim.Sim.st).t
      let pressed := (← OsuModel.Sim.Sim.st).pressed
      let aj ← OsuModel.Sim.Sim.allJudged i
      let endT := (← OsuModel.Sim.Sim.topObj i).h.endTime
      OsuModel.Sim.Sim.modifyObj i (s3aF t pressed aj endT vp)) := rfl

@[simp] theorem s3a_ostateS_lastPressed (o : sim.state.OState) : (ostateS o).lastPressed = actListS o.last_pressed := rfl

theorem s3a_F_eq (o : sim.state.OState) (t endT : F64) (aj vp : Bool) (pressed : replay.frames.ActList) :
    s3aF t (actListS pressed).toArray aj endT vp (ostateS o) = ostateS (s3aTracked o t endT aj vp pressed) := by
  obtain ⟨life, ls, le, cid, res, nest, ha, hov, hle, halive, tr, inst, hinst, arm, harm, ti, tl, aaa, lp, sm, spt,
    spm, la, ta, aalc, csm, cs, lrt, cfs⟩ := o
  unfold s3aF s3aTracked s3aAA
  simp only [List.any_toArray]
  rcases Option.eq_none_or_eq_some ha with hh | ⟨a0, hh⟩ <;> subst hh
  · simp only [Id.run, s3a_ostateS_hitAction, Option.map_none, Option.isNone_none, if_true]
    rfl
  · rcases Option.eq_none_or_eq_some aaa with hx | ⟨x, hx⟩ <;> subst hx
    · simp only [Id.run, s3a_ostateS_hitAction, Option.map_some, Option.isNone_some, Bool.false_eq_true, if_false,
        s3a_ostateS_acceptAnyAfter, Option.isNone_none, if_true, s3a_ostateS_lastPressed]
      by_cases hc : (actListS lp).contains
          (if actS a0 == OsuModel.Replay.Action.right then OsuModel.Replay.Action.left else OsuModel.Replay.Action.right) = true
      · simp only [hc, Bool.not_true, Bool.false_eq_true, if_false, if_true]
        rfl
      · simp only [hc, Bool.not_false, if_true, Bool.false_eq_true, if_false]
        rfl
    · simp only [Id.run, s3a_ostateS_hitAction, Option.map_some, Option.isNone_some, Bool.false_eq_true, if_false,
        s3a_ostateS_acceptAnyAfter]
      rfl

theorem sim.step.update_tracking_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (vp : Bool)
    (hinv : SimInv c s) (hi : i.val < s.objs.val.length)
    (hlp : (s.objs.val[i.val]'hi).last_pressed.len.val ≤ 3) (hp : s.pressed.len.val ≤ 3) :
    ∃ s', sim.step.update_tracking c s i vp = ok s' ∧
      OsuModel.Sim.Sim.updateTracking i.val vp (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧
      (∃ aj, s' = { s with objs := (alloc.vec.Vec.set s.objs i
        (s3aTracked (s.objs.val[i.val]'hi) s.t (c.pb.objects.val[i.val]'(by rw [← hinv.objs_len]; exact hi)).h.end_time aj vp s.pressed)) }) ∧
      SimInv c s' ∧ s'.objs.val.length = s.objs.val.length ∧ s'.insts = s.insts ∧ s'.future_order = s.future_order := by
  have h3 : i.val < c.pb.objects.val.length := by rw [← hinv.objs_len]; exact hi
  obtain ⟨aj, haj, eaj⟩ := sim.step.all_judged_refines tn fo c s i hi
  generalize ho : s.objs.val[i.val]'hi = o at hlp
  generalize he : (c.pb.objects.val[i.val]'h3).h.end_time = endT
  have hR : sim.step.update_tracking c s i vp =
      ok { s with objs := alloc.vec.Vec.set s.objs i (s3aTracked o s.t endT aj vp s.pressed) } := by
    unfold sim.step.update_tracking
    simp only [haj, vec_index_eq _ _ h3, vec_index_mut_eq _ _ hi, bind_ok, ho, he]
    obtain ⟨life, ls, le, cid, res, nest, ha, hov, hle, halive, tr, inst, hinst, arm, harm, ti, tl, aaa, lp, sm, spt,
      spm, la, ta, aalc, csm, cs, lrt, cfs⟩ := o
    simp only at hlp
    unfold s3aTracked s3aAA
    rcases Option.eq_none_or_eq_some ha with hh | ⟨a0, hh⟩ <;> subst hh
    · simp only [core.option.Option.is_none, Option.isNone_none, if_true, bind_ok,
        sim.step.any_valid_tracking_action_refines _ _ _ hp, s3a_abs_os]
      cases aj <;> cases vp <;> by_cases hl : s.t ≤ endT <;> simp [hl, float.F64.le]
    · have hac : ∀ a, replay.frames.act_contains lp a = ok ((abs lp : List OsuModel.Replay.Action).contains (abs a)) :=
        fun a => replay.frames.act_contains_refines lp a hlp
      rcases Option.eq_none_or_eq_some aaa with hx | ⟨x, hx⟩ <;> subst hx
      · simp only [core.option.Option.is_none, Option.isNone_none, Option.isNone_some, if_true, if_false, bind_ok,
          Bool.false_eq_true, s2_action_eq, replay.frames.act_contains_refines _ _ hlp,
          sim.step.any_valid_tracking_action_refines _ _ _ hp, s3a_abs_os]
        cases a0 <;> simp only [s2_actS, actS, s3a_absAct] <;>
          cases aj <;> cases vp <;> by_cases hl : s.t ≤ endT <;> simp [hl, float.F64.le, hac, s3a_absAct, actS, s3a_absAL]
      · simp only [core.option.Option.is_none, Option.isNone_some, if_false, bind_ok, Bool.false_eq_true,
          sim.step.any_valid_tracking_action_refines _ _ _ hp, s3a_abs_os]
        cases aj <;> cases vp <;> by_cases hl : s.t ≤ endT <;> simp [hl, float.F64.le]
  refine ⟨_, hR, ?_, ⟨aj, by rw [← ho]⟩, s3a_inv_set c s i _ hinv hi (by rw [ho]; rfl), by simp [vec_set_val'], rfl, rfl⟩
  rw [s3a_updateTracking_eq]
  simp only [OsuModel.Sim.Sim.st, simM_bind, simM_get, Except.bind, eaj, s3a_topObj _ _ _ _ _ h3, s3a_topS_h]
  refine s3a_modifyObj tn fo c s i hi _ _ ?_
  have hend : (hobjS tn (c.pb.objects.val[i.val]'h3).h).endTime = endT := by rw [← he]; rfl
  rw [hend, s3a_st_t, show (simStS tn s).pressed = (actListS s.pressed).toArray from rfl]
  simp only [ho]
  exact s3a_F_eq o s.t endT aj vp s.pressed

/-! ## slider data, follow area -/
@[simp] theorem s3a_topS_slider (tn) (o : sim.playable.TopObj) : (topS tn o).slider = o.slider.map abs := rfl

theorem sim.step.slider_data_refines (tn fo) (c : sim.state.Ctx) (i : Usize) (hi : i.val < c.pb.objects.val.length) :
    ∃ r, sim.step.slider_data c i = ok r ∧
      ∀ S, s3aR abs S r (OsuModel.Sim.Sim.sliderData i.val (simCtxS tn fo c) S) := by
  unfold sim.step.slider_data OsuModel.Sim.Sim.sliderData
  simp only [vec_index_eq _ _ hi, bind_ok]
  rcases Option.eq_none_or_eq_some (c.pb.objects.val[i.val]'hi).slider with hs | ⟨sd, hs⟩
  · refine ⟨_, by simp only [hs]; rfl, fun S => ?_⟩
    simp only [s3aR, simM_bind, s3a_topObj _ _ _ _ _ hi, Except.bind, s3a_topS_slider, hs, Option.map_none,
      OsuModel.Sim.Sim.need, simM_throw]
    exact ⟨_, rfl⟩
  · refine ⟨_, by simp only [hs]; rfl, fun S => ?_⟩
    simp only [s3aR, simM_bind, s3a_topObj _ _ _ _ _ hi, Except.bind, s3a_topS_slider, hs, Option.map_some,
      OsuModel.Sim.Sim.need, simM_pure]

theorem s3a_isMouseInFollowArea_tn (tn : Nat → String) (h : sim.playable.HObj) (sd : OsuModel.Sim.SliderData)
    (g : OsuModel.Sim.SliderGeom) (m : Option OsuModel.Sim.Vec2) (t : F64) (e : Bool) :
    OsuModel.Sim.isMouseInFollowArea (hobjS tn h) sd g m t e = OsuModel.Sim.isMouseInFollowArea (abs h) sd g m t e := by
  cases m <;> rfl

@[simp] theorem s3a_ostateS_sliderMouse (o : sim.state.OState) : (ostateS o).sliderMouse = o.slider_mouse.map abs := rfl

/-- the slider path sizes the follow-area lookup needs (`curve_position_at`) -/
def s3aPathOk (c : sim.state.Ctx) (i : Nat) : Prop :=
  ∀ (h : i < c.pb.objects.val.length) sd, (c.pb.objects.val[i]'h).slider = some sd →
    sd.cum_len.val.length < 2 ^ 62 ∧ sd.path.val.length < 2 ^ 62

theorem s3a_liftR {α : Type} (E : Except String α) (x : core.result.Result α sim.err.SimErr) (h : s2_rel id E x)
    (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) : s3aR id S x (OsuModel.Sim.Sim.liftExcept E C S) := by
  cases E <;> cases x <;> simp_all [s2_rel, s3aR, OsuModel.Sim.Sim.liftExcept] <;> rfl

theorem sim.step.mouse_in_follow_area_refines (h64 : System.Platform.numBits = 64) (tn fo) (c : sim.state.Ctx)
    (s : sim.state.St) (i : Usize) (expanded : Bool) (hinv : SimInv c s) (hi : s3aInstOk s i.val)
    (hp : s3aPathOk c i.val) :
    ∃ r, sim.step.mouse_in_follow_area c s i expanded = ok r ∧
      s3aR id (simStS tn s) r (OsuModel.Sim.Sim.mouseInFollowArea i.val expanded (simCtxS tn fo c) (simStS tn s)) := by
  have h1 := hi.1
  have h3 : i.val < c.pb.objects.val.length := by rw [← hinv.objs_len]; exact h1
  obtain ⟨g, hg, eg⟩ := sim.step.cur_slider_geom_refines tn fo c s i hinv hi
  unfold sim.step.mouse_in_follow_area OsuModel.Sim.Sim.mouseInFollowArea
  simp only [vec_index_eq _ _ h3, vec_index_eq _ _ h1, bind_ok, simM_bind, s3a_topObj _ _ _ _ _ h3, Except.bind]
  unfold sim.step.slider_data OsuModel.Sim.Sim.sliderData
  simp only [vec_index_eq _ _ h3, bind_ok, simM_bind, s3a_topObj _ _ _ _ _ h3, Except.bind, s3a_topS_slider]
  rcases Option.eq_none_or_eq_some (c.pb.objects.val[i.val]'h3).slider with hs | ⟨sd, hs⟩
  · simp only [hs, Option.map_none, OsuModel.Sim.Sim.need, simM_throw]
    refine ⟨.Err (.Internal .MissingSliderData), ?_, ⟨_, rfl⟩⟩
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · obtain ⟨hc, hpp⟩ := hp h3 sd hs
    obtain ⟨x, hx, ex⟩ := sim.geometry.is_mouse_in_follow_area_refines h64 (c.pb.objects.val[i.val]'h3).h sd g
      (s.objs.val[i.val]'h1).slider_mouse s.t expanded hc hpp
    simp only [hs, Option.map_some, OsuModel.Sim.Sim.need, simM_pure, simM_bind, eg, Except.bind,
      core.result.Result.Insts.CoreOpsTry.branch, hg, bind_ok, hx, s3a_ostate _ _ _ _ _ h1, OsuModel.Sim.Sim.st,
      simM_get, s3a_ostateS_sliderMouse, s3a_st_t, s3a_topS_h, s3a_isMouseInFollowArea_tn]
    exact ⟨x, rfl, s3a_liftR _ x ex _ _⟩

end OsuProofs
