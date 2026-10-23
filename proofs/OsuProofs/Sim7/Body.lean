/-
sim7: the slider body part of `updateSlider` (`slider_body_update`: LoadComplete with the argon radius, body
transforms, the scheduled `Refresh`) against the spec fragment `s7BodyF` (continuation-passing, `rfl`-checked
against `Sim.updateSlider` in Sim7/Update.lean), plus the `update_transforms` law `s7UT` (discharged for Sim2s
`s2_tfOk` by `s7_ut_s2`).
-/
import OsuProofs.Sim.OnKilled
import OsuProofs.Sim2.Geometry
import OsuProofs.Sim3.SC_Upd
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- the transform-engine law for `update_transforms` on a budget predicate `P` (instantiated for Sim2's
`s2_tfOk` by `s7_ut_s2`) -/
def s7UT (P : Nat → sim.transforms.TObj → Prop) : Prop :=
  ∀ b o t f, P b o → ∃ o', sim.transforms.update_transforms o t f = ok o' ∧
    OsuModel.Sim.updateTransforms (abs o) t f = abs o' ∧ P b o'

theorem s7_ut_s2 : s7UT s2_tfOk := by
  intro b o t f hP
  obtain ⟨o', h, e⟩ := sim.transforms.update_transforms_refines o t f (s2_tfOk_ts b o hP)
  refine ⟨o', h, e, ?_⟩
  show s2_tfOkS b (abs o')
  rw [← e]; exact s2_tfOkS_UT b _ t f hP

/-- Rust `Result<(), SimErr>` + state vs a spec fragment run with continuation `K` -/
def s7KR (tn : Nat → String) (C : OsuModel.Sim.Ctx) (K : Unit → OsuModel.Sim.SimM Unit)
    (r : core.result.Result Unit sim.err.SimErr) (e : Except String (Unit × OsuModel.Sim.St)) (s' : sim.state.St) : Prop :=
  match r with
  | .Ok _ => e = K () C (simStS tn s')
  | .Err _ => ∃ m, e = .error m

/-- the slider body (`slider_body_update`), then `K` -/
def s7BodyF (o : OsuModel.Sim.TopObj) (t : F64) (sd : OsuModel.Sim.SliderData) (k : Nat)
    (K : Unit → OsuModel.Sim.SimM Unit) : OsuModel.Sim.SimM Unit := do
  let c ← OsuModel.Sim.Sim.ctx
  let env := c.env
  let ins ← OsuModel.Sim.Sim.instOf k
  let jp : Unit → OsuModel.Sim.Inst → OsuModel.Sim.SimM Unit := fun _ ins =>
    let ins := { ins with bodyTf := OsuModel.Sim.updateTransforms ins.bodyTf t }
    let jp := fun (_ : Unit) (ins : OsuModel.Sim.Inst) => do
      OsuModel.Sim.Sim.modifyInst k fun _ => ins
      K ()
    if (ins.refreshPending && decide (Float32.ofBits 953267991 < ins.bodyTf.alpha) &&
        !(ins.bodyTf.scale.x == 0) && !(ins.bodyTf.scale.y == 0)) = true then do
      let x ← OsuModel.Sim.Sim.liftExcept (OsuModel.Sim.bodyRefresh sd ins.bodyRadius)
      match x with
      | (sz, off) =>
        let ins := { ins with refreshPending := false, bodySize := sz, bodyOffset := off }
        jp () ins
    else jp () ins
  if (!ins.bodyLoaded) = true then
    let r := env.argonPathRadius * o.h.scale
    let ins := { ins with bodyLoaded := true }
    if (!(ins.bodyRadius == r)) = true then do
      let x ← OsuModel.Sim.Sim.liftExcept (OsuModel.Sim.bodyRefresh sd r)
      match x with
      | (sz, off) =>
        let ins := { ins with bodyRadius := r, bodySize := sz, bodyOffset := off }
        jp () ins
    else jp () ins
  else jp () ins

theorem s7_br (sd : sim.playable.SliderData) (r : F32) :
    ∃ x, sim.geometry.body_refresh sd r = ok x ∧ (match x with
      | .Ok p => OsuModel.Sim.bodyRefresh (abs sd) r = .ok (abs p.1, abs p.2)
      | .Err _ => ∃ m, OsuModel.Sim.bodyRefresh (abs sd) r = .error m) := by
  obtain ⟨x, hx, ex⟩ := sim.geometry.body_refresh_refines sd r
  refine ⟨x, hx, ?_⟩
  cases x with
  | Ok p =>
    cases h : OsuModel.Sim.bodyRefresh (abs sd) r <;> rw [h] at ex <;> simp [s2_rel] at ex
    rw [← ex]; rfl
  | Err er =>
    cases h : OsuModel.Sim.bodyRefresh (abs sd) r <;> rw [h] at ex <;> simp [s2_rel] at ex
    exact ⟨_, rfl⟩

theorem s7_modInst (tn : Nat → String) (C : OsuModel.Sim.Ctx) (s : sim.state.St) (k : Usize)
    (hk : k.val < s.insts.val.length) (Y : sim.state.Inst) (f : OsuModel.Sim.Inst → OsuModel.Sim.Inst)
    (hf : f (abs (s.insts.val[k.val]'hk)) = abs Y) :
    OsuModel.Sim.Sim.modifyInst k.val f C (simStS tn s) = .ok ((), simStS tn { s with insts := s.insts.set k Y }) := by
  rw [s3b_modifyInst_ok _ _ _ _ (by simpa [simStS, abs] using hk)]
  congr 2
  exact s3c_modify_insts tn s s.insts k.val hk Y f hf k rfl

theorem s7_tfInv_set {P : Nat → sim.transforms.TObj → Prop} (b : Nat) (s : sim.state.St) (k : Usize)
    (hk : k.val < s.insts.val.length) (Y : sim.state.Inst) (h : s3b_TfInv P b s)
    (h1 : P b Y.tf) (h2 : P b Y.body_tf) :
    s3b_TfInv P b { s with insts := s.insts.set k Y } := by
  intro ins hins
  change ins ∈ (s.insts.set k Y).val at hins
  rw [vec_set_val'] at hins
  rcases List.mem_or_eq_of_mem_set hins with h0 | h0
  · exact h ins h0
  · subst h0; exact ⟨h1, h2⟩

set_option hygiene false in
macro "s7_okleaf" : tactic => `(tactic| (
  refine ⟨.Ok (), _, rfl, ?_, ?_⟩
  · intro K
    simp only [s7KR, simM_bind, simM_pure, s3b_modifyInst_ok _ _ _ _ hkS, s3b_ebok]
    refine congrArg (fun S => K () (simCtxS tn fo c) S) ?_
    refine s3c_modify_insts tn s s.insts k.val hk _ _ ?_ k rfl
    rfl
  · intro _
    exact ⟨_, rfl, rfl, rfl, s7_tfInv_set b s k hk _ hP hPk.1 pt1⟩))

set_option hygiene false in
macro "s7_errleaf" : tactic => `(tactic| (
  refine ⟨.Err er, ?_, ?_, fun K => ⟨m, ?_⟩, fun h => by cases h⟩
  rotate_left
  · simp [core.convert.FromSame.from, core.convert.FromSame]; exact rfl
  · simp [hm, hfb, OsuModel.Sim.Sim.liftExcept, simM_bind, simM_throw, Except.bind]))

set_option hygiene false in
/-- the refresh-condition tail (after `t1`), given the instance `I0` written before -/
macro "s7_cond" : tactic => `(tactic| (
  cases hrp : ins.refresh_pending <;> simp only [hrp, Bool.false_and, Bool.true_and, Bool.false_eq_true, if_false, if_true]
  · s7_okleaf
  · by_cases ha : (1e-4 : F32) < t1.alpha
    · simp only [ha, decide_true, Bool.true_and, if_true]
      cases hx : (t1.scale.x == 0) <;> simp only [hx, Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and,
        Bool.false_eq_true, if_false, if_true]
      · cases hy : (t1.scale.y == 0) <;> simp only [hy, Bool.not_true, Bool.not_false, Bool.false_eq_true, if_false,
          if_true]
        · obtain ⟨x, hx1, hx2⟩ := s7_br sd ins.body_radius
          cases x with
          | Ok p =>
            obtain ⟨sz, off⟩ := p
            simp only [hx1, bind_ok, hx2, OsuModel.Sim.Sim.liftExcept, simM_bind, simM_pure, s3b_ebok,
              uncurry_apply_pair, Except.bind]
            s7_okleaf
          | Err er =>
            obtain ⟨m, hm⟩ := hx2
            simp only [hx1, bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            s7_errleaf
        · s7_okleaf
      · s7_okleaf
    · simp only [ha, decide_false, Bool.false_and, Bool.and_false, Bool.false_eq_true, if_false]
      s7_okleaf))

set_option hygiene false in
/-- `s7_cond` after a LoadComplete refresh (the second refresh reuses its result `hx2`) -/
macro "s7_cond2" : tactic => `(tactic| (
  cases hrp : ins.refresh_pending <;> simp only [hrp, Bool.false_and, Bool.true_and, Bool.false_eq_true, if_false, if_true]
  · s7_okleaf
  · by_cases ha : (1e-4 : F32) < t1.alpha
    · simp only [ha, decide_true, Bool.true_and, if_true]
      cases hx : (t1.scale.x == 0) <;> simp only [hx, Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and,
        Bool.false_eq_true, if_false, if_true]
      · cases hy : (t1.scale.y == 0) <;> simp only [hy, Bool.not_true, Bool.not_false, Bool.false_eq_true, if_false,
          if_true]
        · simp only [hx2, OsuModel.Sim.Sim.liftExcept, simM_bind, simM_pure, s3b_ebok,
            uncurry_apply_pair, Except.bind]
          s7_okleaf
        · s7_okleaf
      · s7_okleaf
    · simp only [ha, decide_false, Bool.false_and, Bool.and_false, Bool.false_eq_true, if_false]
      s7_okleaf))

-- FRAGMENT-OF: OsuModel.Sim.Sim.updateSlider (its body block = `s7BodyF`, checked by `rfl` in s7_updSlider_eq; bridged in sim.step.update_slider_refines)
theorem sim.step.slider_body_update_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop} (hU : s7UT P) (b : Nat) (c : sim.state.Ctx) (s : sim.state.St)
    (i k : Usize) (t : F64) (sd : sim.playable.SliderData)
    (hi : i.val < c.pb.objects.val.length) (hk : k.val < s.insts.val.length)
    (hsd : sim.step.slider_data c i = ok (.Ok sd)) (hP : s3b_TfInv P b s) :
    ∃ res s', sim.step.slider_body_update c s i k t = ok (res, s') ∧
      (∀ K, s7KR tn (simCtxS tn fo c) K res
        (s7BodyF (topS tn (c.pb.objects.val[i.val]'hi)) t (abs sd) k.val K (simCtxS tn fo c) (simStS tn s)) s') ∧
      (res = .Ok () → ∃ Y, s' = { s with insts := s.insts.set k Y } ∧ Y.tf = (s.insts.val[k.val]'hk).tf ∧
        Y.loaded = (s.insts.val[k.val]'hk).loaded ∧ s3b_TfInv P b s') := by
  have hPk := hP _ (List.getElem_mem hk)
  have hkS : k.val < (simStS tn s).insts.size := by simpa [simStS, abs] using hk
  generalize hins : s.insts.val[k.val]'hk = ins at hPk
  obtain ⟨t1, ht1, et1, pt1⟩ := hU b _ t false hPk.2
  have eins : OsuModel.Sim.Sim.instOf k.val (simCtxS tn fo c) (simStS tn s) = .ok (abs ins, simStS tn s) := by
    rw [s3a_instOf tn fo c s _ hk, hins]
  have a1 : (abs ins : OsuModel.Sim.Inst).bodyLoaded = ins.body_loaded := rfl
  have a2 : (abs ins : OsuModel.Sim.Inst).bodyRadius = ins.body_radius := rfl
  have a3 : (abs ins : OsuModel.Sim.Inst).refreshPending = ins.refresh_pending := rfl
  have a4 : (abs ins : OsuModel.Sim.Inst).bodyTf = abs ins.body_tf := rfl
  have a5 : (abs t1 : OsuModel.Sim.TObj).alpha = t1.alpha := rfl
  have a6 : (abs t1 : OsuModel.Sim.TObj).scale.x = t1.scale.x := rfl
  have a7 : (abs t1 : OsuModel.Sim.TObj).scale.y = t1.scale.y := rfl
  have a8 : (simCtxS tn fo c).env.argonPathRadius = c.env.argon_path_radius := rfl
  have a9 : (topS tn (c.pb.objects.val[i.val]'hi)).h.scale = (c.pb.objects.val[i.val]'hi).h.scale := rfl
  have hfb : Float32.ofBits 953267991 = (0.0001 : F32) := by
    simpa [float.F32.from_bits] using fb32_953267991
  unfold sim.step.slider_body_update s7BodyF
  simp only [hsd, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, vec_index_eq _ _ hi, vec_index_mut_eq _ _ hk,
    hins, ht1, float.F32.mul, float.F32.eq, float.F32.lt, sim.step.ALPHA_PRESENT, fb32_953267991, sim_basic_F32_0,
    simM_bind, OsuModel.Sim.Sim.ctx, eins, Except.bind, uncurry_apply_pair, simM_read, s3b_ebok,
    a1, a2, a3, a4, et1, a5, a6, a7, a8, a9, hfb]
  generalize c.env.argon_path_radius * (c.pb.objects.val[i.val]'hi).h.scale = r
  cases hbl : ins.body_loaded <;> simp only [Bool.not_false, Bool.not_true, if_true, if_false, Bool.false_eq_true]
  · -- first update: LoadComplete
    by_cases hr : (ins.body_radius == r) = true
    · simp only [hr, Bool.not_true, if_true, if_false, Bool.false_eq_true]
      s7_cond
    · have hr' : (ins.body_radius == r) = false := by simpa using hr
      simp only [hr', Bool.not_false, if_true, if_false, Bool.false_eq_true]
      obtain ⟨x, hx1, hx2⟩ := s7_br sd r
      cases x with
      | Ok p =>
        obtain ⟨sz, off⟩ := p
        simp only [hx1, bind_ok, hx2, OsuModel.Sim.Sim.liftExcept, simM_bind, simM_pure, s3b_ebok,
          uncurry_apply_pair, Except.bind, ht1]
        s7_cond2
      | Err er =>
        obtain ⟨m, hm⟩ := hx2
        simp only [hx1, bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        s7_errleaf
  · s7_cond

end OsuProofs
