/-
sim4 (D62): the spec `Sim.updateSpinner` split into continuation-passing fragments (the do-elaborator's join points
become the continuation `K`): `s4SpunF` (SpunOut rotation), `s4TicksF` (next-tick lifetime + tick container),
`s4TrackerF` (SpinnerRotationTracker.Update), `s4SpinTail` (CheckForResult + updateBonusScore). `s4_updSpinner_eq`
checks by `rfl` that the composition IS `Sim.updateSpinner` (so the fragment lemmas are bridged, not restated).
-/
import OsuProofs.Sim.Circle
import OsuProofs.Sim3.SA_Bonus
import OsuProofs.Sim3.SC_Upd
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- the "first unjudged tick" loop body of `updateSpinner` -/
def s4NextF (i : Nat) : Nat → Option Nat → OsuModel.Sim.SimM (ForInStep (Option Nat)) := fun j __s => do
  let b ← OsuModel.Sim.Sim.judged (i, (j : Int))
  if (!b) = true then pure (ForInStep.done (some j)) else pure (ForInStep.yield __s)

/-- the tick-container loop body of `updateSpinner` -/
def s4TickF (i : Nat) (o : OsuModel.Sim.TopObj) (t : F64) : Nat → PUnit → OsuModel.Sim.SimM (ForInStep PUnit) :=
  fun j __s => do
    let os ← OsuModel.Sim.Sim.ostate i
    let a ← OsuModel.Sim.Sim.getA os.tickLive j "tickLive"
    let b ← OsuModel.Sim.Sim.judged (i, (j : Int))
    if (a && decide (o.h.start ≤ t) && !b) = true then do
      let tk ← OsuModel.Sim.Sim.getA os.tickInsts j "tickInsts"
      let ins ← OsuModel.Sim.Sim.instOf tk
      if (!ins.loaded) = true then do
        OsuModel.Sim.Sim.modifyInst tk fun ins => { ins with loaded := true }
        OsuModel.Sim.Sim.tickState i j 2 OsuModel.Sim.Armed.idle true
        pure (ForInStep.yield PUnit.unit)
      else pure (ForInStep.yield PUnit.unit)
    else pure (ForInStep.yield PUnit.unit)

/-- next unjudged tick gets `tickLive`, then the tick container update, then `K` -/
def s4TicksF (i : Nat) (o : OsuModel.Sim.TopObj) (t : F64) (K : Unit → OsuModel.Sim.SimM Unit) :
    OsuModel.Sim.SimM Unit := do
  let __s ← forIn [:o.nested.size] none (s4NextF i)
  let jp : Unit → OsuModel.Sim.SimM Unit := fun _ => do
    forIn [:o.nested.size] PUnit.unit (s4TickF i o t)
    K ()
  match __s with
  | some j => do
    let os ← OsuModel.Sim.Sim.ostate i
    let tl ← OsuModel.Sim.Sim.setA os.tickLive j true "tickLive"
    let __r ← OsuModel.Sim.Sim.modifyObj i fun os => { os with tickLive := tl }
    jp __r
  | _ => jp ()

/-- `SpinnerRotationTracker.Update`, then `K` -/
def s4TrackerF (i : Nat) (t : F64) (spinnable : Bool) (K : Unit → OsuModel.Sim.SimM Unit) :
    OsuModel.Sim.SimM Unit := do
  let g ← OsuModel.Sim.Sim.curSpinnerGeom i
  let os ← OsuModel.Sim.Sim.ostate i
  match os.spinMouse with
  | some pos =>
    let thisAngle : F32 :=
      -OsuModel.Sim.radiansToDegrees ((pos.x - g.trackerSize.x / 2).atan2 (pos.y - g.trackerSize.y / 2))
    let delta : F32 := match os.lastAngle with
      | none => 0
      | some la => thisAngle - la
    let jp3 : Unit → OsuModel.Sim.OState → OsuModel.Sim.SimM Unit := fun _ os =>
      let os := { os with lastAngle := some thisAngle }
      do
      let __r ← OsuModel.Sim.Sim.modifyObj i fun _ => os
      K __r
    let jp2 : Unit → F32 → OsuModel.Sim.SimM Unit := fun _ delta =>
      if (os.spinTracking && spinnable) = true then do
        let c ← OsuModel.Sim.Sim.ctx
        let s ← OsuModel.Sim.Sim.st
        let rate ← OsuModel.Sim.Sim.liftExcept (c.cfg.trueRate s.speed)
        let d : F32 := (delta.toF64 * rate.abs).toF32
        let x ← OsuModel.Sim.Sim.liftExcept (OsuModel.Sim.Sim.reportDelta os t d)
        jp3 () x
      else jp3 () os
    let jp1 : Unit → F32 → OsuModel.Sim.SimM Unit := fun _ delta =>
      if delta < -180 then jp2 () (delta + 360) else jp2 () delta
    if 180 < delta then jp1 () (delta - 360) else jp1 () delta
  | _ => K ()

/-- the spinner's CheckForResult (miss unjudged ticks, judge by progress) and `updateBonusScore` -/
def s4SpinTail (i : Nat) (o : OsuModel.Sim.TopObj) (sp : OsuModel.Sim.SpinnerData) (t : F64) :
    OsuModel.Sim.SimM Unit := do
  let r ← OsuModel.Sim.Sim.ostate i
  let jp : Unit → OsuModel.Sim.SimM Unit := fun _ => OsuModel.Sim.Sim.updateBonusScore i
  if (r.result.isNone && decide (o.h.start ≤ t) && !decide (t < o.h.endTime)) = true then do
    forIn [:o.nested.size] PUnit.unit (fun (j : Nat) _ => do
      let b ← OsuModel.Sim.Sim.judged (i, (j : Int))
      if (!b) = true then do
        OsuModel.Sim.Sim.missForcefully (i, (j : Int))
        pure (ForInStep.yield PUnit.unit)
      else pure (ForInStep.yield PUnit.unit))
    let r ← OsuModel.Sim.Sim.ostate i
    let p : F32 := OsuModel.Sim.Sim.spinnerProgress sp r
    let ty : OsuModel.Sim.HitResult :=
      if 1 ≤ p then OsuModel.Sim.HitResult.great
      else if 0.9 < p.toF64 then OsuModel.Sim.HitResult.ok
      else if 0.75 < p.toF64 then OsuModel.Sim.HitResult.meh else o.h.minResult
    let f ← OsuModel.Sim.Sim.maxFuel
    let __r ← OsuModel.Sim.Sim.applyResult f (i, -1) ty
    jp __r
  else jp ()

/-- the SpunOut rotation after the `spinTracking` write (`OsuModSpunOut.onSpinnerUpdate`), then `K` -/
def s4SpunR (i : Nat) (sp : OsuModel.Sim.SpinnerData) (t : F64) (spinnable : Bool) (c : OsuModel.Sim.Ctx)
    (K : Unit → OsuModel.Sim.SimM Unit) : OsuModel.Sim.SimM Unit := do
  let s ← OsuModel.Sim.Sim.st
  if (!OsuModel.Sim.almostEqualsD s.clockRate 0) = true then do
    let elapsed ← OsuModel.Sim.Sim.elapsedNow
    let e : F64 := elapsed / s.clockRate
    let speed : F32 := (1.01 * F64.ofInt sp.spinsRequired / sp.duration).toF32
    let deg : F32 := OsuModel.Sim.radiansToDegrees (e.toF32 * speed * Float32.ofBits 1078530011 * 2)
    if spinnable = true then do
      let r ← OsuModel.Sim.Sim.liftExcept (c.cfg.trueRate s.speed)
      let d : F32 := (deg.toF64 * r.abs).toF32
      let os ← OsuModel.Sim.Sim.ostate i
      let os' ← OsuModel.Sim.Sim.liftExcept (OsuModel.Sim.Sim.reportDelta os t d)
      let __r ← OsuModel.Sim.Sim.modifyObj i fun _ => os'
      K __r
    else K ()
  else K ()

/-- the SpunOut branch (`OsuModSpunOut.onSpinnerUpdate`), then `K` -/
def s4SpunF (i : Nat) (sp : OsuModel.Sim.SpinnerData) (t : F64) (spinnable : Bool) (c : OsuModel.Sim.Ctx)
    (K : Unit → OsuModel.Sim.SimM Unit) : OsuModel.Sim.SimM Unit := do
  OsuModel.Sim.Sim.modifyObj i fun os => { os with spinTracking := spinnable }
  s4SpunR i sp t spinnable c K

/-- `Sim.updateSpinner` assembled from the fragments -/
def s4UpdSpinner (i : Nat) : OsuModel.Sim.SimM Unit := do
  let r ← OsuModel.Sim.Sim.ostate i
  if r.result.isSome = true then pure ()
  else do
    let o ← OsuModel.Sim.Sim.topObj i
    match o.spinner with
    | some sp => do
      let s1 ← OsuModel.Sim.Sim.st
      let t := s1.t
      let s2 ← OsuModel.Sim.Sim.st
      let pressed := s2.pressed
      let spinnable : Bool := decide (o.h.start ≤ t) && decide (t < o.h.endTime)
      let c ← OsuModel.Sim.Sim.ctx
      let jp : Unit → OsuModel.Sim.SimM Unit := fun _ =>
        s4TicksF i o t (fun _ => s4TrackerF i t spinnable (fun _ => s4SpinTail i o sp t))
      if (!c.cfg.spunOut) = true then do
        let r ← OsuModel.Sim.Sim.ostate i
        let tracking : Bool := spinnable && r.result.isNone &&
          (pressed.contains OsuModel.Replay.Action.left || pressed.contains OsuModel.Replay.Action.right)
        let __r ← OsuModel.Sim.Sim.modifyObj i fun os => { os with spinTracking := tracking }
        jp __r
      else s4SpunF i sp t spinnable c jp
    | _ => pure ()

theorem s4_updSpinner_eq (i : Nat) : OsuModel.Sim.Sim.updateSpinner i = s4UpdSpinner i := by
  unfold OsuModel.Sim.Sim.updateSpinner s4UpdSpinner s4SpunF s4SpunR s4TicksF s4TrackerF s4SpinTail s4NextF s4TickF
  rfl

end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

/-! ## Rust helpers -/

theorem sim.geometry.radians_to_degrees_eq (x : F32) :
    sim.geometry.radians_to_degrees x = ok (OsuModel.Sim.radiansToDegrees x) := by
  simp [sim.geometry.radians_to_degrees, sim.geometry.F32_180, sim.geometry.F32_PI, float.F32.mul, float.F32.div,
    float.F32.from_bits, OsuModel.Sim.radiansToDegrees]
  rw [show (18e1 : F32) = OsuModel.Sim.f32_180 by unfold OsuModel.Sim.f32_180; decide +kernel]

/-- the object fields neither `report_delta` nor the tracker's `last_angle` write touch -/
def s4KeepR (o : sim.state.OState) :=
  (o.life, o.lifetime_start, o.lifetime_end, o.child_id, o.result, o.nested, o.hit_action, o.hovered,
   o.head_lifetime_end, o.head_alive, o.tracking, o.inst, o.head_inst, o.armed, o.head_armed, o.tick_insts,
   o.tick_live, o.accept_any_after, o.last_pressed, o.slider_mouse, o.spin_tracking, o.spin_mouse,
   o.completed_full_spins)

theorem s4_rd_bound (ta : F32) : ∀ n acc cm k r, s3aRD ta n acc cm k = some r → r.2.2.1 ≤ k + n := by
  intro n
  induction n with
  | zero => intro acc cm k r h; simp [s3aRD] at h; subst h; simp
  | succ n ih =>
    intro acc cm k r h
    simp only [s3aRD] at h
    split at h
    · split at h
      · have := ih _ _ _ r h; omega
      · cases h
    · cases h; simp

theorem s4_report_delta_cs (os : sim.state.OState) (t : F64) (delta : F32)
    (hsp : os.completed_spins.val + 1000000 ≤ U64.max) (r : core.result.Result Unit sim.err.SimErr)
    (os' : sim.state.OState) (h : sim.step.report_delta os t delta = ok (r, os')) (hr : r = .Ok ()) :
    os'.completed_spins.val ≤ os.completed_spins.val + 1000000 := by
  unfold sim.step.report_delta at h
  by_cases hz : (delta == 0) = true
  · simp [float.F32.eq, sim_basic_F32_0, hz] at h; obtain ⟨-, rfl⟩ := h; omega
  have hz' : (delta == 0) = false := by simpa using hz
  by_cases hl : os.last_report_time ≤ t
  · obtain ⟨y, hy, hrel⟩ := s3a_rd_loop (os.total_accumulated + delta) os.last_report_time t 1000000 1000000#u32
      os.accumulated_at_last_completion (F32.max os.current_spin_max (F32.abs (os.total_accumulated + delta - os.accumulated_at_last_completion)))
      os.completed_spins rfl hsp
    simp only [float.F32.eq, sim_basic_F32_0, hz', bind_ok, Bool.false_eq_true, if_false, float.F32.add, float.F64.le, hl,
        decide_true, if_true, float.F32.sub, float.F32.abs, sim.netx.f32_max_refines, hy] at h
    revert hrel
    rcases hrd : s3aRD (os.total_accumulated + delta) 1000000 os.accumulated_at_last_completion
        (F32.max os.current_spin_max (F32.abs (os.total_accumulated + delta - os.accumulated_at_last_completion)))
        os.completed_spins.val with _ | ⟨a, c, k, f⟩
    · intro hrel; obtain ⟨e, he⟩ := hrel
      have : r = y.1 := by have := congrArg Prod.fst (Result.ok_injective h); exact this.symm
      rw [this, he] at hr; cases hr
    · intro hrel
      have hb := s4_rd_bound _ _ _ _ _ _ hrd
      have e2 : os'.completed_spins = y.2.2.2.1 := by
        have := congrArg (fun p => p.2.completed_spins) (Result.ok_injective h); exact this.symm
      rw [e2, hrel.2.2.1]; simpa using hb
  · simp [float.F32.eq, sim_basic_F32_0, hz', float.F64.le, hl, float.F32.add, float.F32.sub, float.F32.abs] at h
    obtain ⟨-, rfl⟩ := h; simp


@[simp] theorem s4_F32_180C : sim.step.F32_180C = ok (180 : F32) := by
  simp [sim.step.F32_180C]; decide +kernel

theorem s4_set_self (s : sim.state.St) (i : Usize) (hi : i.val < s.objs.val.length) :
    { s with objs := s.objs.set i (s.objs.val[i.val]'hi) } = s := by
  have : s.objs.set i (s.objs.val[i.val]'hi) = s.objs := by
    apply alloc.vec.Vec.ext; rw [vec_set_val']; exact List.set_getElem_self _
  rw [this]

/-- Rust `Result<(), SimErr>` + state vs a spec fragment run with continuation `K` -/
def s4KR (tn : Nat → String) (C : OsuModel.Sim.Ctx) (K : Unit → OsuModel.Sim.SimM Unit)
    (r : core.result.Result Unit sim.err.SimErr) (e : Except String (Unit × OsuModel.Sim.St)) (s' : sim.state.St) : Prop :=
  match r with
  | .Ok _ => e = K () C (simStS tn s')
  | .Err _ => ∃ m, e = .error m

set_option hygiene false in
/-- the tracker after `delta` is fixed: optional `report_delta`, then the `last_angle` write -/
macro "s4_trk_tail" : tactic => `(tactic| (
  by_cases hstk : (s.objs.val[i.val]'ho).spin_tracking = true
  · by_cases hspn : spinnable = true
    · rw [if_pos hstk, if_pos hspn,
        if_pos (show ((s.objs.val[i.val]'ho).spin_tracking && spinnable) = true by simp [hstk, hspn])]
      simp only [float.F32.to_f64, float.F64.abs, float.F64.mul, float.F64.to_f32, bind_ok, simM_bind,
        OsuModel.Sim.Sim.ctx, OsuModel.Sim.Sim.st, simM_read, simM_get, Except.bind, simM_read_bind, simM_get_bind]
      have hspeed : (abs (alloc.vec.Vec.deref s.speed) : _root_.Array F64) = (simStS tn s).speed := by
        simp [abs, simStS, alloc.vec.Vec.deref]
      have er' : (simCtxS tn fo c).cfg.trueRate (simStS tn s).speed = .ok rate := by
        rw [← hspeed]; exact er
      simp only [er', OsuModel.Sim.Sim.liftExcept, simM_pure, Except.bind]
      obtain ⟨r1, os1, e1, ⟨ta, acc, cm, sp, lrt, hos1⟩, rel⟩ := sim.step.report_delta_refines
        (s.objs.val[i.val]'ho) s.t _ (hcs ho)
      rw [e1]; simp only [bind_ok, uncurry_apply_pair, s3a_abs_os] at rel ⊢
      cases r1 with
      | Err er1 =>
        obtain ⟨m, hm1⟩ := rel
        refine ⟨.Err er1, _, by simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame], ⟨m, ?_⟩,
          ho, os1, rfl, by rw [hos1]; rfl, fun h => by cases h⟩
        first | rfl | (simp only [hm1]; rfl) | simp [hm1]
      | Ok u =>
        have hcs1 := s4_report_delta_cs _ s.t _ (hcs ho) _ os1 e1 rfl
        have hmo := s3a_modifyObj tn fo c s i ho
          (fun _ => { ostateS os1 with lastAngle := some θ }) { os1 with last_angle := some θ } rfl
        refine ⟨.Ok (), _, by simp [core.result.Result.Insts.CoreOpsTry.branch], ?_, ho,
          { os1 with last_angle := some θ }, rfl,
          by rw [hos1]; rfl, fun _ => by rw [hos1] at hcs1 ⊢; exact hcs1⟩
        simp only [s3aOR] at rel
        simp only [s4KR, rel, simM_pure, simM_bind, hmo, Except.bind]
    · rw [if_pos hstk, if_neg hspn,
        if_neg (show ¬ ((s.objs.val[i.val]'ho).spin_tracking && spinnable) = true by simp [hspn])]
      have hmo := s3a_modifyObj tn fo c s i ho
        (fun _ => { ostateS (s.objs.val[i.val]'ho) with spinTracking := (s.objs.val[i.val]'ho).spin_tracking, spinMouse := some (abs pos), lastAngle := some θ })
        { s.objs.val[i.val]'ho with last_angle := some θ } (by simp [ostateS, hm])
      refine ⟨.Ok (), _, rfl, ?_, ho, _, rfl, rfl, fun _ => Nat.le_add_right _ _⟩
      simp only [s4KR, simM_bind, hmo, Except.bind]
  · rw [if_neg hstk,
      if_neg (show ¬ ((s.objs.val[i.val]'ho).spin_tracking && spinnable) = true by simp [hstk])]
    have hmo := s3a_modifyObj tn fo c s i ho
      (fun _ => { ostateS (s.objs.val[i.val]'ho) with spinTracking := (s.objs.val[i.val]'ho).spin_tracking, spinMouse := some (abs pos), lastAngle := some θ })
      { s.objs.val[i.val]'ho with last_angle := some θ } (by simp [ostateS, hm])
    refine ⟨.Ok (), _, rfl, ?_, ho, _, rfl, rfl, fun _ => Nat.le_add_right _ _⟩
    simp only [s4KR, simM_bind, hmo, Except.bind]))

set_option hygiene false in
/-- the two `delta` wrap-around tests, then `s4_trk_tail` -/
macro "s4_trk_wrap " D:term:max : tactic => `(tactic| (
  by_cases h1 : (180 : F32) < $D
  · simp only [h1, decide_true, ite_true, bind_ok, if_pos h1]
    by_cases h2 : $D - 360 < -180
    · simp only [h2, decide_true, ite_true, bind_ok, if_pos h2]
      s4_trk_tail
    · simp only [h2, decide_false, Bool.false_eq_true, ite_false, bind_ok, if_neg h2]
      s4_trk_tail
  · simp only [h1, decide_false, Bool.false_eq_true, ite_false, bind_ok, if_neg h1]
    by_cases h2 : $D < -180
    · simp only [h2, decide_true, ite_true, bind_ok, if_pos h2]
      s4_trk_tail
    · simp only [h2, decide_false, Bool.false_eq_true, ite_false, bind_ok, if_neg h2]
      s4_trk_tail))

/-- `spinner_tracker_update` (Rust) refines the tracker fragment `s4TrackerF` of `Sim.updateSpinner` (bridged by
`s4_updSpinner_eq` in `update_spinner_refines`), for any continuation `K`. -/
-- FRAGMENT-OF: OsuModel.Sim.Sim.updateSpinner (s4TrackerF, checked = the spec by rfl in s4_updSpinner_eq); CONDITIONAL: hcs (completed_spins + 10^6 ≤ U64.max, report_delta's premise)
theorem sim.step.spinner_tracker_update_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize)
    (spinnable : Bool) (hinst : s3aInstOk s i.val)
    (hd : ∀ x ∈ c.cfg.rate_sources.val, ∀ k, x.val = .Dyn k → k.val < s.speed.val.length)
    (hcs : ∀ h : i.val < s.objs.val.length, (s.objs.val[i.val]'h).completed_spins.val + 1000000 ≤ U64.max)
    (K : Unit → OsuModel.Sim.SimM Unit) :
    ∃ r s', sim.step.spinner_tracker_update c s i spinnable = ok (r, s') ∧
      s4KR tn (simCtxS tn fo c) K r (s4TrackerF i.val s.t spinnable K (simCtxS tn fo c) (simStS tn s)) s' ∧
      ∃ (h : i.val < s.objs.val.length) (o' : sim.state.OState), s' = { s with objs := s.objs.set i o' } ∧
        s4KeepR o' = s4KeepR (s.objs.val[i.val]'h) ∧
        (r = .Ok () → o'.completed_spins.val ≤ (s.objs.val[i.val]'h).completed_spins.val + 1000000) := by
  have ho := hinst.fst
  obtain ⟨g, hg, eg⟩ := sim.step.cur_spinner_geom_refines tn fo c s i hinst
  obtain ⟨rate, hr, er⟩ := sim.mods.true_rate_refines c.cfg (alloc.vec.Vec.deref s.speed)
    (fun x hx k hk => by simpa [alloc.vec.Vec.deref] using hd x hx k hk)
  unfold sim.step.spinner_tracker_update s4TrackerF
  simp only [hg, bind_ok, hr, vec_index_mut_eq _ _ ho, uncurry_apply_pair, simM_bind, eg, Except.bind,
    s3a_ostate tn fo c s _ ho]
  have hsm : (ostateS (s.objs.val[i.val]'ho)).spinMouse = (s.objs.val[i.val]'ho).spin_mouse.map abs := rfl
  rw [hsm]
  cases hm : (s.objs.val[i.val]'ho).spin_mouse with
  | none =>
    simp only [Option.map_none]
    refine ⟨.Ok (), _, rfl, ?_, ho, _, rfl, rfl, fun _ => Nat.le_add_right _ _⟩
    simp only [s4KR, s4_set_self]
  | some pos =>
    simp only [Option.map_some, sim_basic_F32_2, float.F32.div, float.F32.sub, float.F32.atan2,
      sim.geometry.radians_to_degrees_eq, float.F32.neg, bind_ok, s4_F32_180C, s3a_step_F32_360, float.F32.lt,
      float.F32.add]
    have hla : (ostateS (s.objs.val[i.val]'ho)).lastAngle = (s.objs.val[i.val]'ho).last_angle := rfl
    have hst : (ostateS (s.objs.val[i.val]'ho)).spinTracking = (s.objs.val[i.val]'ho).spin_tracking := rfl
    rw [hla, hst]
    have hA : ((abs pos : OsuModel.Sim.Vec2).x - (abs g : OsuModel.Sim.SpinnerGeom).trackerSize.x / 2).atan2
        ((abs pos : OsuModel.Sim.Vec2).y - (abs g : OsuModel.Sim.SpinnerGeom).trackerSize.y / 2) =
        F32.atan2 (pos.x - g.tracker_size.x / 2) (pos.y - g.tracker_size.y / 2) := rfl
    rw [hA]
    generalize hθ : -OsuModel.Sim.radiansToDegrees (F32.atan2 (pos.x - g.tracker_size.x / 2)
      (pos.y - g.tracker_size.y / 2)) = θ
    rw [← hm]
    cases hla2 : (s.objs.val[i.val]'ho).last_angle with
    | none =>
      simp only [sim_basic_F32_0, bind_ok, uncurry_apply_pair]
      rw [← hla2]
      s4_trk_wrap (0 : F32)
    | some la =>
      simp only [bind_ok, uncurry_apply_pair]
      rw [← hla2]
      s4_trk_wrap (θ - la)


theorem s4_c101 : float.F64.from_bits 4607227454796291113#u64 = ok (1.01 : F64) := by
  simp [float.F64.from_bits] <;> decide +kernel
theorem s4_c2 : sim.step.F32_2C = ok (2 : F32) := by
  simp [sim.step.F32_2C] <;> decide +kernel
theorem s4_pi : sim.geometry.F32_PI = ok (Float32.ofBits 1078530011) := by
  simp [sim.geometry.F32_PI, float.F32.from_bits] <;> rfl

/-- `spun_out_update` (Rust, called after the `spin_tracking` write) refines `s4SpunR` -/
-- FRAGMENT-OF: OsuModel.Sim.Sim.updateSpinner (s4SpunR, checked = the spec by rfl in s4_updSpinner_eq); CONDITIONAL: hcs (report_delta's premise)
theorem sim.step.spun_out_update_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize)
    (sp : sim.playable.SpinnerData) (spinnable : Bool) (ho : i.val < s.objs.val.length)
    (hstep : s.k.val ≠ 0 → s.k.val - 1 < c.steps.val.length)
    (hd : ∀ x ∈ c.cfg.rate_sources.val, ∀ k, x.val = .Dyn k → k.val < s.speed.val.length)
    (hcs : (s.objs.val[i.val]'ho).completed_spins.val + 1000000 ≤ U64.max)
    (K : Unit → OsuModel.Sim.SimM Unit) :
    ∃ r s', sim.step.spun_out_update c s i sp spinnable = ok (r, s') ∧
      s4KR tn (simCtxS tn fo c) K r
        (s4SpunR i.val (abs sp) s.t spinnable (simCtxS tn fo c) K (simCtxS tn fo c) (simStS tn s)) s' ∧
      ∃ o' : sim.state.OState, s' = { s with objs := s.objs.set i o' } ∧
        s4KeepR o' = s4KeepR (s.objs.val[i.val]'ho) ∧ o'.last_angle = (s.objs.val[i.val]'ho).last_angle ∧
        (r = .Ok () → o'.completed_spins.val ≤ (s.objs.val[i.val]'ho).completed_spins.val + 1000000) := by
  obtain ⟨rate, hr, er⟩ := sim.mods.true_rate_refines c.cfg (alloc.vec.Vec.deref s.speed)
    (fun x hx k hk => by simpa [alloc.vec.Vec.deref] using hd x hx k hk)
  have hspeed : (abs (alloc.vec.Vec.deref s.speed) : _root_.Array F64) = (simStS tn s).speed := by
    simp [abs, simStS, alloc.vec.Vec.deref]
  have er' : (simCtxS tn fo c).cfg.trueRate (simStS tn s).speed = .ok rate := by rw [← hspeed]; exact er
  let e : F64 := if s.k.val = 0 then 0 else s.t - ((c.steps.val[s.k.val - 1]?).map (·.time)).getD 0
  have hE : (if s.k = 0#usize then ok (c, (0 : F64))
      else do let i ← s.k - 1#usize; let s1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice schedule.Step) c.steps i
              let e ← float.F64.sub s.t s1.time; ok (c, e)) = ok (c, e) := by
    by_cases h0 : s.k.val = 0
    · have : s.k = 0#usize := by scalar_tac
      simp [this, h0, e]
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
  obtain ⟨b, hb, eb⟩ := sim.basic.almost_equals_d_refines s.clock_rate 0
  have eb' : OsuModel.Sim.almostEqualsD s.clock_rate 0 = b := eb
  unfold sim.step.spun_out_update s4SpunR
  simp only [sim_step_F64_0, hb, bind_ok, simM_bind, OsuModel.Sim.Sim.st, simM_get, Except.bind]
  have hcr : (simStS tn s).clockRate = s.clock_rate := rfl
  rw [hcr, eb']
  cases b
  · simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
    rw [hE]
    simp only [bind_ok, uncurry_apply_pair, hES, Except.bind, float.F64.div, s4_c101, float.F64.from_i64, float.F64.mul,
      float.F64.to_f32, float.F32.mul, s4_pi, s4_c2, sim.geometry.radians_to_degrees_eq, simM_bind]
    have hsp1 : (abs sp : OsuModel.Sim.SpinnerData).spinsRequired = sp.spins_required.val := rfl
    have hsp2 : (abs sp : OsuModel.Sim.SpinnerData).duration = sp.duration := rfl
    rw [hsp1, hsp2]
    cases spinnable
    · simp only [Bool.false_eq_true, ite_false]
      exact ⟨.Ok (), s, rfl, by simp only [s4KR, s4_set_self], _, (s4_set_self s i ho).symm, rfl, rfl,
        fun _ => Nat.le_add_right _ _⟩
    · simp only [ite_true, float.F32.to_f64, hr, bind_ok, float.F64.abs, vec_index_mut_eq _ _ ho, uncurry_apply_pair,
        er', OsuModel.Sim.Sim.liftExcept, simM_pure, Except.bind, s3a_ostate tn fo c s _ ho]
      obtain ⟨r1, os1, e1, ⟨ta, acc, cm, sp1, lrt, hos1⟩, rel⟩ := sim.step.report_delta_refines
        (s.objs.val[i.val]'ho) s.t _ hcs
      rw [e1]; simp only [bind_ok, uncurry_apply_pair, s3a_abs_os] at rel ⊢
      cases r1 with
      | Err er1 =>
        obtain ⟨m, hm1⟩ := rel
        refine ⟨.Err er1, _, by simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame], ⟨m, ?_⟩,
          os1, rfl, by rw [hos1]; rfl, by rw [hos1], fun h => by cases h⟩
        (simp only [simM_bind, simM_pure, Except.bind, s3a_ostate tn fo c s _ ho, hm1]) <;> rfl
      | Ok u =>
        have hcs1 := s4_report_delta_cs _ s.t _ hcs _ os1 e1 rfl
        have hmo := s3a_modifyObj tn fo c s i ho (fun _ => ostateS os1) os1 rfl
        refine ⟨.Ok (), _, by simp [core.result.Result.Insts.CoreOpsTry.branch], ?_, os1, rfl,
          by rw [hos1]; rfl, by rw [hos1], fun _ => hcs1⟩
        simp only [s3aOR] at rel
        simp only [s4KR, s3a_ostate tn fo c s _ ho, rel, simM_pure, simM_bind, hmo, Except.bind]
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    exact ⟨.Ok (), s, rfl, rfl, _, (s4_set_self s i ho).symm, rfl, rfl, fun _ => Nat.le_add_right _ _⟩


/-! ## spinner ticks -/

theorem s4_getA {α : Type} (a : _root_.Array α) (j : Nat) (w : String) (h : j < a.size) (C : OsuModel.Sim.Ctx)
    (S : OsuModel.Sim.St) : OsuModel.Sim.Sim.getA a j w C S = .ok (a[j], S) := by
  simp [OsuModel.Sim.Sim.getA, h]

theorem s4_setA {α : Type} (a : _root_.Array α) (j : Nat) (x : α) (w : String) (h : j < a.size) (C : OsuModel.Sim.Ctx)
    (S : OsuModel.Sim.St) : OsuModel.Sim.Sim.setA a j x w C S = .ok (a.set j x h, S) := by
  simp [OsuModel.Sim.Sim.setA, h]

theorem s4_judged_eq (s : sim.state.St) (i j : Usize) (hi : i.val < s.objs.val.length)
    (hj : j.val < (s.objs.val[i.val]'hi).nested.val.length) (h63 : j.val < 2 ^ 63) :
    sim.step.judged s ⟨i, UScalar.hcast .I64 j⟩ = ok ((s.objs.val[i.val]'hi).nested.val[j.val]'hj).isSome := by
  have hcj : (UScalar.hcast .I64 j).val = (j.val : Int) := sim_usize_to_i64 j h63
  have hn : ¬ (UScalar.hcast .I64 j : I64) < 0#i64 := by
    intro h; have : (UScalar.hcast .I64 j : I64).val < 0 := h; omega
  have hu : (lift (IScalar.hcast .Usize (UScalar.hcast .I64 j : I64)) : Result Usize) = ok j := by
    simp only [lift]; congr 1; apply UScalar.eq_of_val_eq
    rw [sim_i64_cast_usize _ (by rw [hcj]; omega) (by rw [hcj, Int.toNat_natCast]; scalar_tac), hcj,
      Int.toNat_natCast]
  simp only [sim.step.judged, sim.step.res_of, vec_index_eq _ _ hi, bind_ok, hn, if_false, hu, vec_index_eq _ _ hj,
    core.option.Option.is_some]

theorem s4_tfInv_loaded {P : Nat → sim.transforms.TObj → Prop} (b : Nat) (s : sim.state.St) (k : Usize)
    (hk : k.val < s.insts.val.length) (h : s3b_TfInv P b s) :
    s3b_TfInv P b { s with insts := s.insts.set k { s.insts.val[k.val]'hk with loaded := true } } := by
  intro ins hins
  change ins ∈ (s.insts.set k _).val at hins
  rw [vec_set_val'] at hins
  rcases List.mem_or_eq_of_mem_set hins with h1 | h1
  · exact h ins h1
  · subst h1; exact h (s.insts.val[k.val]'hk) (List.getElem_mem hk)

@[reducible] def s4TUL (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (t : F64) (n : Usize) (start : F64)
    (j : Usize) :=
  sim.step.spinner_ticks_update_loop c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in c.pb.difficulty
    c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks c.pb.objects c.frames c.steps
    c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames c.block_periods
    c.first_obj s i t n start j

@[reducible] def s4TUB (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (t : F64) (n : Usize) (start : F64)
    (j : Usize) :=
  sim.step.spinner_ticks_update_loop.body c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in c.pb.difficulty
    c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks c.pb.objects c.frames c.steps
    c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames c.block_periods
    c.first_obj i t n start s j

theorem s4_tul_step (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (t : F64) (n : Usize) (start : F64)
    (j : Usize) (r) (hb : s4TUB c s i t n start j = ok r) :
    s4TUL c s i t n start j = (match r with
      | .cont (s1, j1) => s4TUL c s1 i t n start j1
      | .done y => ok y) := by
  unfold s4TUL sim.step.spinner_ticks_update_loop
  rw [loop_unfold]; dsimp only; rw [show sim.step.spinner_ticks_update_loop.body _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s j
    = ok r from hb]; simp only [bind_ok]
  rcases r with ⟨s1, j1⟩ | y <;> rfl

set_option maxHeartbeats 1600000 in
/-- the tick-container loop of `updateSpinner` -/
theorem s4_ticks_loop (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (e : Nat) (s1 : sim.state.St) (i : Usize) (t : F64)
    (hi : i.val < c.pb.objects.val.length) (hio : i.val < s1.objs.val.length)
    (htl : (s1.objs.val[i.val]'hio).tick_live.val.length = (c.pb.objects.val[i.val]'hi).nested.val.length)
    (htk : (s1.objs.val[i.val]'hio).tick_insts.val.length = (c.pb.objects.val[i.val]'hi).nested.val.length)
    (hD1 : some i ∈ s1.dict_slots.val) :
    ∀ m (j : Usize) (s : sim.state.St), (c.pb.objects.val[i.val]'hi).nested.val.length - j.val = m →
      j.val ≤ (c.pb.objects.val[i.val]'hi).nested.val.length →
      SimARInv tn fo P b0 n c s e 0 0 →
      (∃ ins th, s = { s1 with insts := ins, theta := th } ∧ ins.val.length = s1.insts.val.length) →
      ∃ s', s4TUL c s i t (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) (c.pb.objects.val[i.val]'hi).h.start j
          = ok s' ∧
        forIn (m := OsuModel.Sim.SimM) (List.range' j.val m) PUnit.unit
          (s4TickF i.val (topS tn (c.pb.objects.val[i.val]'hi)) t) (simCtxS tn fo c) (simStS tn s) =
          .ok (PUnit.unit, simStS tn s') ∧
        SimARInv tn fo P b0 n c s' e 0 0 ∧
          ∃ ins th, s' = { s1 with insts := ins, theta := th } ∧ ins.val.length = s1.insts.val.length := by
  intro m
  induction m with
  | zero =>
    intro j s hm hj hI hS
    refine ⟨s, ?_, rfl, hI, hS⟩
    have hb : s4TUB c s i t (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) (c.pb.objects.val[i.val]'hi).h.start j
        = ok (.done s) := by
      have : ¬ j < alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested := by rw [vec_lt_len_iff]; omega
      simp [sim.step.spinner_ticks_update_loop.body, this]
    rw [s4_tul_step c s i _ _ _ j _ hb]
  | succ m ih =>
    intro j s hm hj hI hS
    obtain ⟨ins0, th0, rfl, hl0⟩ := hS
    have hjl : j.val < (c.pb.objects.val[i.val]'hi).nested.val.length := by omega
    have hsm := hI.inv.nested_small _ (List.getElem_mem hi)
    have hio' : i.val < ({ s1 with insts := ins0, theta := th0 } : sim.state.St).objs.val.length := hio
    have hnl := hI.inv.nested_len _ hio' hi
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := (c.pb.objects.val[i.val]'hi).nested.property; omega)
    have hlt : j < alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested := by rw [vec_lt_len_iff]; exact hjl
    generalize hS : ({ s1 with insts := ins0, theta := th0 } : sim.state.St) = s at hI hio' hnl
    have ho1 : (s.objs.val[i.val]'hio') = (s1.objs.val[i.val]'hio) := by subst hS; rfl
    have htlj : j.val < (s.objs.val[i.val]'hio').tick_live.val.length := by rw [ho1, htl]; exact hjl
    have htkj : j.val < (s.objs.val[i.val]'hio').tick_insts.val.length := by rw [ho1, htk]; exact hjl
    have hnj : j.val < (s.objs.val[i.val]'hio').nested.val.length := by rw [hnl]; exact hjl
    have hjud := s4_judged_eq s i j hio' hnj (by omega)
    have ejud := s3a_judged_obj tn fo c s i.val j.val hio' hnj
    rw [List.range'_succ, List.forIn_cons]
    simp only [s4TickF, simM_bind, s3a_ostate tn fo c s _ hio', Except.bind]
    have htlS : j.val < (ostateS (s.objs.val[i.val]'hio')).tickLive.size := by simpa [ostateS, abs] using htlj
    rw [s4_getA _ _ _ htlS]
    simp only [Except.bind, ejud]
    have hgl : (ostateS (s.objs.val[i.val]'hio')).tickLive[j.val]'htlS =
        ((s.objs.val[i.val]'hio').tick_live.val[j.val]'htlj) := by simp [ostateS, abs]
    have hst0 : (topS tn (c.pb.objects.val[i.val]'hi)).h.start = (c.pb.objects.val[i.val]'hi).h.start := rfl
    rw [hgl, hst0]
    -- does the tick need loading?
    by_cases hc : (((s.objs.val[i.val]'hio').tick_live.val[j.val]'htlj) &&
        decide ((c.pb.objects.val[i.val]'hi).h.start ≤ t) &&
        !((s.objs.val[i.val]'hio').nested.val[j.val]'hnj).isSome) = true
    · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
      obtain ⟨⟨hb1, hb2⟩, hb3⟩ := hc
      have hcT : (((s.objs.val[i.val]'hio').tick_live.val[j.val]'htlj) &&
          decide ((c.pb.objects.val[i.val]'hi).h.start ≤ t) &&
          !((s.objs.val[i.val]'hio').nested.val[j.val]'hnj).isSome) = true := by simp [hb1, hb2, hb3]
      rw [if_pos hcT]
      have htkI := (hI.ik.old (by rw [← hS]; exact hD1) hio').2.2 j.val htkj
      generalize htkd : (s.objs.val[i.val]'hio').tick_insts.val[j.val]'htkj = tk at htkI
      have htkS : j.val < (ostateS (s.objs.val[i.val]'hio')).tickInsts.size := by simpa [ostateS, abs] using htkj
      have hgk : (ostateS (s.objs.val[i.val]'hio')).tickInsts[j.val]'htkS = tk.val := by
        rw [← htkd]; simp [ostateS, abs]
      simp only [simM_bind, s4_getA _ _ _ htkS, Except.bind, hgk, s3a_instOf tn fo c s _ htkI]
      have hld : (abs (s.insts.val[tk.val]'htkI) : OsuModel.Sim.Inst).loaded = (s.insts.val[tk.val]'htkI).loaded := rfl
      rw [hld]
      cases hldv : (s.insts.val[tk.val]'htkI).loaded
      · -- load the fresh tick instance, then tickState
        simp only [Bool.not_false, ite_true]
        let sL : sim.state.St := { s with insts := s.insts.set tk { s.insts.val[tk.val]'htkI with loaded := true } }
        have hLmod : OsuModel.Sim.Sim.modifyInst tk.val (fun ins => { ins with loaded := true }) (simCtxS tn fo c)
            (simStS tn s) = .ok ((), simStS tn sL) := by
          rw [s3b_modifyInst_ok _ _ _ _ (by simpa [simStS, abs] using htkI)]
          congr 2
          exact s3c_modify_insts tn s s.insts tk.val htkI _ _ rfl tk rfl
        have hinvL : SimInv c sL := s3b_inv_of hI.inv rfl rfl
        have hioL : i.val < sL.objs.val.length := hio'
        have htkL : ((sL.objs.val[i.val]'hioL).tick_insts.val[j.val]'htkj).val < sL.insts.val.length := by
          show ((s.objs.val[i.val]'hio').tick_insts.val[j.val]'htkj).val < (s.insts.set tk _).val.length
          rw [vec_set_val', List.length_set, htkd]; exact htkI
        obtain ⟨s2, e2, eS2, ⟨ins2, th2, hs2⟩, il2, inv2, fo2, ob2, fr2⟩ := sim.step.tick_state_refines tn fo c sL i j
          2#u64 .Idle true hinvL hi hjl hioL htkj htkL
        have hIL : SimARInv tn fo P b0 n c sL e 0 0 :=
          sim_ar_inv_hook tn fo P b0 n c s e 0 0 0 hI sL hinvL (s3b_objFrame_of_eq rfl)
            (by show (s.insts.set tk _).val.length = _; rw [vec_set_val', List.length_set])
            (s4_tfInv_loaded _ s tk htkI hI.tf) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        have hI2 : SimARInv tn fo P b0 n c s2 e 0 0 :=
          sim_ar_inv_hook tn fo P b0 n c sL e 0 0 0 hIL s2 inv2 (s3b_objFrame_of_eq ob2) il2
            (sim.step.tick_state_tfinv c sL i j 2#u64 _ true hinvL hi hjl hioL htkj htkL s2 e2 P _ hIL.tf)
            fr2.1 fr2.2.1 fr2.2.2.1 fr2.2.2.2.1 fr2.2.2.2.2.1 fr2.2.2.2.2.2.1
            fr2.2.2.2.2.2.2.1 fr2.2.2.2.2.2.2.2.1 fr2.2.2.2.2.2.2.2.2.1 fr2.2.2.2.2.2.2.2.2.2.2
        have hb : s4TUB c s i t (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) (c.pb.objects.val[i.val]'hi).h.start j
            = ok (.cont (s2, j1)) := by
          simp only [sim.step.spinner_ticks_update_loop.body, hlt, if_true, vec_index_eq _ _ hio', bind_ok,
            vec_index_eq _ _ htlj, hb1, float.F64.le, hb2, decide_true, lift, hjud, hb3, Bool.false_eq_true, ite_false,
            vec_index_eq _ _ htkj, htkd, vec_index_eq _ _ htkI, hldv, vec_index_mut_eq _ _ htkI, uncurry_apply_pair]
          show (do let s3 ← sim.step.tick_state c sL i j 2#u64 .Idle true; let j2 ← j + 1#usize; ok (ControlFlow.cont (s3, j2))) = _
          rw [e2]; simp [hj1]
        rw [s4_tul_step c s i _ _ _ j _ hb]
        simp only [simM_bind, hLmod, Except.bind]
        have eS2' : OsuModel.Sim.Sim.tickState i.val j.val 2 OsuModel.Sim.Armed.idle true (simCtxS tn fo c)
            (simStS tn sL) = .ok ((), simStS tn s2) := eS2
        simp only [simM_bind, eS2', Except.bind, simM_pure]
        rw [show j.val + 1 = j1.val from hj1v.symm]
        refine ih j1 s2 (by omega) (by omega) hI2 ⟨ins2, th2, by rw [hs2]; subst hS; rfl, ?_⟩
        have h := il2
        rw [hs2] at h
        refine h.trans ?_
        show (s.insts.set tk _).val.length = s1.insts.val.length
        rw [vec_set_val', List.length_set, ← hS]; exact hl0
      · simp only [Bool.not_true, Bool.false_eq_true, ite_false, simM_pure]
        have hb : s4TUB c s i t (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) (c.pb.objects.val[i.val]'hi).h.start j
            = ok (.cont (s, j1)) := by
          simp only [sim.step.spinner_ticks_update_loop.body, hlt, if_true, vec_index_eq _ _ hio', bind_ok,
            vec_index_eq _ _ htlj, hb1, float.F64.le, hb2, decide_true, lift, hjud, hb3, Bool.false_eq_true, ite_false,
            vec_index_eq _ _ htkj, htkd, vec_index_eq _ _ htkI, hldv, ite_true, hj1]
        rw [s4_tul_step c s i _ _ _ j _ hb]
        rw [show j.val + 1 = j1.val from hj1v.symm]
        exact ih j1 s (by omega) (by omega) hI ⟨ins0, th0, hS.symm, hl0⟩
    · have hb : s4TUB c s i t (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) (c.pb.objects.val[i.val]'hi).h.start j
          = ok (.cont (s, j1)) := by
        simp only [sim.step.spinner_ticks_update_loop.body, hlt, if_true, vec_index_eq _ _ hio', bind_ok,
          vec_index_eq _ _ htlj]
        cases hv1 : ((s.objs.val[i.val]'hio').tick_live.val[j.val]'htlj)
        · simp [hj1]
        · by_cases hv2 : (c.pb.objects.val[i.val]'hi).h.start ≤ t
          · have hv3 : ((s.objs.val[i.val]'hio').nested.val[j.val]'hnj).isSome = true := by
              exact Option.isSome_iff_ne_none.mpr (by rw [hv1] at hc; simpa [hv2] using hc)
            simp [float.F64.le, hv2, lift, hjud, hv3, hj1]
          · simp [float.F64.le, hv2, hj1]
      rw [s4_tul_step c s i _ _ _ j _ hb, if_neg hc]
      simp only [simM_pure]
      rw [show j.val + 1 = j1.val from hj1v.symm]
      exact ih j1 s (by omega) (by omega) hI ⟨ins0, th0, hS.symm, hl0⟩


/-- `spinner_ticks_update` (Rust) refines the tick fragment `s4TicksF` of `Sim.updateSpinner` for any continuation `K` -/
-- FRAGMENT-OF: OsuModel.Sim.Sim.updateSpinner (s4TicksF, checked = the spec by rfl in s4_updSpinner_eq); htl/htk: tick slots exist (set by spinner_ticks_get, kept by every write)
theorem sim.step.spinner_ticks_update_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (e : Nat)
    (s : sim.state.St) (i : Usize) (hI : SimARInv tn fo P b0 n c s e 0 0) (hD : some i ∈ s.dict_slots.val)
    (hi : i.val < c.pb.objects.val.length)
    (htl : ∀ h : i.val < s.objs.val.length,
      (s.objs.val[i.val]'h).tick_live.val.length = (c.pb.objects.val[i.val]'hi).nested.val.length)
    (htk : ∀ h : i.val < s.objs.val.length,
      (s.objs.val[i.val]'h).tick_insts.val.length = (c.pb.objects.val[i.val]'hi).nested.val.length)
    (K : Unit → OsuModel.Sim.SimM Unit) :
    ∃ s', sim.step.spinner_ticks_update c s i = ok s' ∧
      s4TicksF i.val (topS tn (c.pb.objects.val[i.val]'hi)) s.t K (simCtxS tn fo c) (simStS tn s) =
        K () (simCtxS tn fo c) (simStS tn s') ∧
      SimARInv tn fo P b0 n c s' e 0 0 ∧
      ∃ (ho : i.val < s.objs.val.length) (tl : alloc.vec.Vec Bool) (ins : _) (th : _),
        s' = { s with objs := s.objs.set i { s.objs.val[i.val]'ho with tick_live := tl }, insts := ins, theta := th } ∧
        tl.val.length = (s.objs.val[i.val]'ho).tick_live.val.length ∧ ins.val.length = s.insts.val.length := by
  have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
  have hnl := hI.inv.nested_len _ ho hi
  obtain ⟨fr, hfr, efr⟩ := sim.step.first_unjudged_nested_refines s i ho
  have hsz : (topS tn (c.pb.objects.val[i.val]'hi)).nested.size = (c.pb.objects.val[i.val]'hi).nested.val.length := by
    simp [topS]
  unfold sim.step.spinner_ticks_update s4TicksF
  simp only [hfr, bind_ok, simM_bind, hsz]
  rw [show s4NextF i.val = s3aTickF i.val from rfl, ← hnl, s3a_tick_range tn fo c s i.val ho, hnl]
  simp only [Except.bind, vec_index_eq _ _ hi]
  -- the common tail: the tick loop from a state `s1` with fixed objects
  have tail : ∀ s1 : sim.state.St, SimARInv tn fo P b0 n c s1 e 0 0 → some i ∈ s1.dict_slots.val → (ho1 : i.val < s1.objs.val.length) →
      (s1.objs.val[i.val]'ho1).tick_live.val.length = (c.pb.objects.val[i.val]'hi).nested.val.length →
      (s1.objs.val[i.val]'ho1).tick_insts.val.length = (c.pb.objects.val[i.val]'hi).nested.val.length →
      ∃ s', s4TUL c s1 i s.t (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested)
          (c.pb.objects.val[i.val]'hi).h.start 0#usize = ok s' ∧
        forIn (m := OsuModel.Sim.SimM) [:(c.pb.objects.val[i.val]'hi).nested.val.length] PUnit.unit
          (s4TickF i.val (topS tn (c.pb.objects.val[i.val]'hi)) s.t) (simCtxS tn fo c)
          (simStS tn s1) = .ok (PUnit.unit, simStS tn s') ∧
        SimARInv tn fo P b0 n c s' e 0 0 ∧
          ∃ ins th, s' = { s1 with insts := ins, theta := th } ∧ ins.val.length = s1.insts.val.length := by
    intro s1 hI1 hD1 ho1 htl1 htk1
    obtain ⟨s', e1, e2, hI', hS'⟩ := s4_ticks_loop tn fo E b0 n c e s1 i s.t hi ho1 htl1 htk1 hD1
      (c.pb.objects.val[i.val]'hi).nested.val.length 0#usize s1 (by simp) (by simp) hI1 ⟨s1.insts, s1.theta, rfl, rfl⟩
    refine ⟨s', e1, ?_, hI', hS'⟩
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    simp only [Std.Legacy.Range.size, Nat.div_one, Nat.sub_zero, Nat.add_sub_cancel]
    have h00 : (0#usize).val = 0 := rfl
    rw [h00] at e2
    exact e2
  cases fr with
  | none =>
    simp only [Option.map_none] at efr
    rw [← efr]
    obtain ⟨s', e1, e2, hI', ins, th, hs', hl'⟩ := tail s hI hD ho (htl ho) (htk ho)
    have hv : s.objs.set i { s.objs.val[i.val]'ho with tick_live := (s.objs.val[i.val]'ho).tick_live } = s.objs := by
      apply alloc.vec.Vec.ext; rw [vec_set_val']; exact List.set_getElem_self _
    refine ⟨s', ?_, ?_, hI', ho, _, ins, th, by rw [hs', hv], rfl, hl'⟩
    · simp only [bind_ok]; exact e1
    · simp only [simM_bind, e2, Except.bind]
  | some j =>
    simp only [Option.map_some] at efr
    have hj : j.val < (s.objs.val[i.val]'ho).nested.val.length := s3a_firstNone_lt _ _ efr.symm
    have hjt : j.val < (s.objs.val[i.val]'ho).tick_live.val.length := by rw [htl ho, ← hnl]; exact hj
    rw [← efr]
    simp only [vec_index_mut_eq _ _ ho, uncurry_apply_pair, bind_ok, vec_index_mut_eq _ _ hjt, simM_bind,
      s3a_ostate tn fo c s _ ho, Except.bind]
    have hjS : j.val < (ostateS (s.objs.val[i.val]'ho)).tickLive.size := by simpa [ostateS, abs] using hjt
    rw [s4_setA _ _ _ _ hjS]
    simp only [Except.bind]
    let o' : sim.state.OState := { s.objs.val[i.val]'ho with tick_live := (s.objs.val[i.val]'ho).tick_live.set j true }
    have hm := s3a_modifyObj tn fo c s i ho
      (fun os => { os with tickLive := (ostateS (s.objs.val[i.val]'ho)).tickLive.set j.val true hjS }) o'
      (by simp [o', ostateS, abs, vec_set_val', List.map_set])
    rw [hm]
    simp only [Except.bind]
    have hI1 : SimARInv tn fo P b0 n c { s with objs := s.objs.set i o' } e 0 0 :=
      sim_ar_inv_objw tn fo P b0 n c s e hI i ho o' rfl rfl rfl rfl rfl (s3a_inv_set c s i o' hI.inv ho rfl)
    have ho1 : i.val < ({ s with objs := s.objs.set i o' } : sim.state.St).objs.val.length := by
      simp [vec_set_val', ho]
    have hgo : (({ s with objs := s.objs.set i o' } : sim.state.St).objs.val[i.val]'ho1) = o' := by
      simp [vec_set_val']
    obtain ⟨s', e1, e2, hI', ins, th, hs', hl'⟩ := tail _ hI1 hD ho1
      (by rw [hgo]; simp [o', vec_set_val', htl ho]) (by rw [hgo]; exact htk ho)
    refine ⟨s', e1, ?_, hI', ho, _, ins, th, by rw [hs'], by simp [vec_set_val'], hl'⟩
    simp only [simM_bind, e2, Except.bind]

end OsuProofs
