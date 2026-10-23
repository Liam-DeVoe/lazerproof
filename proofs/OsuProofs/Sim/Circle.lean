/-
Circle / slider-head judgement: `circle_check_for_result`, `circle_update_result` against `OsuModel.Sim.Sim`.
-/
import OsuProofs.Sim.PostHead
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem sim_click_ne_hit (a : sim.step.ClickAction) :
    core.cmp.PartialEq.ne.trait_default sim.step.ClickAction.Insts.CoreCmpPartialEqClickAction a
      sim.step.ClickAction.Hit = ok (clickS a != OsuModel.Sim.Sim.ClickAction.hit) := by
  cases a <;> simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, bne,
    sim.step.ClickAction.Insts.CoreCmpPartialEqClickAction.eq, sim.step.ClickAction.read_discriminant, clickS] <;> decide

set_option hygiene false in
/-- the `if kind == head then post_process_head_judgement` tail of `circle_check_for_result` at state `sX` -/
macro "cc_tail " sX:term:max : tactic => `(tactic| (
  have hoX : r.top.val < ($sX).objs.val.length := by rw [hFX.len]; rw [hI.inv.objs_len]; exact hr.1
  by_cases hkh : (simHobj c r).kind = .Head
  · have hb1 : sim.playable.Kind.Insts.CoreCmpPartialEqKind.eq (simHobj c r).kind .Head = ok true := by
      rw [hkh, kind_eq_ok]; rfl
    have hkS : ((hobjS tn (simHobj c r)).kind == OsuModel.Sim.Kind.head) = true := by
      show (kindS _ == _) = true; rw [hkh]; rfl
    simp only [hb1, hkS, bind_ok, ite_true]
    have hlpX : (($sX).objs.val[r.top.val]'hoX).last_pressed.len.val ≤ 3 := by
      have hoS : r.top.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hr.1
      have h2 : (($sX).objs.val[r.top.val]'hoX).last_pressed = (s.objs.val[r.top.val]'hoS).last_pressed :=
        congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.1) (hFX.ow r.top.val hoS hoX)
      rw [h2]; exact hlp hoS
    have hprX : ($sX).pressed.len.val ≤ 3 := by
      have h2 : ($sX).pressed = s.pressed := congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.1) hFX.keep
      rw [h2]; exact hpr
    obtain ⟨rp, sp, ep, rlp, ilp⟩ := sim.step.post_process_head_judgement_refines h64 tn fo E b0 n c hC hCS hlen $sX
      r.top e hIX hr.1 (Or.inr ⟨r, hr, rfl, hkh⟩) (simInstOk_of_fr hFX hL) hp (simLP_fr hLP hFX)
    rw [ep]; simp only [bind_ok, uncurry_apply_pair]
    exact sim_tjn_br tn rp sp _ (fun s' => SimARInv tn fo P b0 n c s' e 0 0 ∧ simJFr s s' ∧ simLP s') rlp
      (fun h => ⟨(ilp h).1, simJFr_trans (simJFr_of_ar hFX) (ilp h).2.1, (ilp h).2.2⟩)
  · have hb1 : sim.playable.Kind.Insts.CoreCmpPartialEqKind.eq (simHobj c r).kind .Head = ok false := by
      rw [kind_eq_ok]
      cases hk : (simHobj c r).kind <;> simp only [kindS] <;> first | rfl | decide | exact absurd hk hkh
    have hkS : ((hobjS tn (simHobj c r)).kind == OsuModel.Sim.Kind.head) = false := by
      show (kindS _ == _) = false
      cases hk : (simHobj c r).kind <;> simp only [kindS] <;> first | rfl | decide | simp | exact absurd hk hkh
    simp only [hb1, hkS, bind_ok, Bool.false_eq_true, ite_false]
    exact ⟨_, _, rfl, rfl, fun _ => ⟨hIX, simJFr_of_ar hFX, simLP_fr hLP hFX⟩⟩))

set_option hygiene false in
/-- `circle_check_for_result`'s final head post-processing at state `sX` (after the kind test is simplified away) -/
macro "cc_fin " sX:term:max : tactic => `(tactic| (
  first
  | exact ⟨_, _, rfl, rfl, fun _ => ⟨hIX, simJFr_of_ar hFX, simLP_fr hLP hFX⟩⟩
  | (have hoX : r.top.val < ($sX).objs.val.length := by rw [hFX.len]; rw [hI.inv.objs_len]; exact hr.1
     have hoS : r.top.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hr.1
     have h2 : (($sX).objs.val[r.top.val]'hoX).last_pressed = (s.objs.val[r.top.val]'hoS).last_pressed :=
       congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.1) (hFX.ow r.top.val hoS hoX)
     have hlpX : (($sX).objs.val[r.top.val]'hoX).last_pressed.len.val ≤ 3 := by rw [h2]; exact hlp hoS
     have h3 : ($sX).pressed = s.pressed := congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.1) hFX.keep
     have hprX : ($sX).pressed.len.val ≤ 3 := by rw [h3]; exact hpr
     obtain ⟨rp, sp, ep, rlp, ilp⟩ := sim.step.post_process_head_judgement_refines h64 tn fo E b0 n c hC hCS hlen $sX
       r.top e hIX hr.1 (Or.inr ⟨r, hr, rfl, hkh⟩) (simInstOk_of_fr hFX hL) hp (simLP_fr hLP hFX)
     rw [ep]; simp only [bind_ok, uncurry_apply_pair]
     exact sim_tjn_br tn rp sp _ (fun s' => SimARInv tn fo P b0 n c s' e 0 0 ∧ simJFr s s' ∧ simLP s') rlp
       (fun h => ⟨(ilp h).1, simJFr_trans (simJFr_of_ar hFX) (ilp h).2.1, (ilp h).2.2⟩))))

set_option hygiene false in
/-- `circle_check_for_result` from `check_hittable` on, for the Rust result `RES` (spec result `abs RES`) -/
macro "cc_mid " RES:term:max : tactic => `(tactic| (
  obtain ⟨a, ha, ea⟩ := sim.step.check_hittable_refines tn fo c s r s.t $RES hI.inv hr (hI.enum _)
  have ea' : OsuModel.Sim.Sim.checkHittable (abs r) s.t (abs $RES) (simCtxS tn fo c) (simStS tn s) =
    .ok (abs a, simStS tn s) := ea
  simp only [ha, bind_ok, simM_bind, ea', Except.bind, hr_eq_ok, sim_click_ne_hit]
  have hRn : ((abs $RES : OsuModel.Sim.HitResult) == OsuModel.Sim.HitResult.none) = (hrS $RES == hrS .None) := rfl
  have hAc : ((abs a : OsuModel.Sim.Sim.ClickAction) != OsuModel.Sim.Sim.ClickAction.hit) =
    (clickS a != OsuModel.Sim.Sim.ClickAction.hit) := rfl
  rw [hRn, hAc]
  cases hn : (hrS $RES == hrS .None)
  · simp only [Bool.false_or, Bool.false_eq_true, ite_false, bind_ok]
    cases hc : (clickS a != OsuModel.Sim.Sim.ClickAction.hit)
    · simp only [Bool.false_eq_true, ite_false]
      obtain ⟨f, hf, hfS⟩ := sim.step.max_fuel_refines tn fo c hlen (simStS tn s)
      obtain ⟨ra, sa, ear, rar, iar⟩ := sim.step.apply_result_frame tn fo E b0 n c hC hCS (simARFr s) (fun _ => True)
        (fun _ _ _ => trivial) (simARFr_qok c s _) s f r $RES e hI (simARFr_refl s) trivial hr hL hres
      simp only [hf, bind_ok, ear, uncurry_apply_pair, simM_bind, hfS, Except.bind]
      cases ra with
      | Err er =>
        obtain ⟨msg, hmsg⟩ := rar
        refine ⟨.Err er, sa, by simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], ⟨msg, ?_⟩, fun h => by cases h⟩
        simp only [hmsg, Except.bind]
      | Ok u =>
        simp only [simRelM] at rar
        obtain ⟨hIX, hFX⟩ := iar rfl
        simp only [rar, Except.bind, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        cc_fin sa
    · simp only [ite_true]
      have hIX := hI
      have hFX := simARFr_refl s
      cc_fin s
  · simp only [Bool.true_or, ite_true]
    have hIX := hI
    have hFX := simARFr_refl s
    cc_fin s))

/-- `circle_check_for_result` (Rust) refines `Sim.circleCheckForResult` (`DrawableHitCircle.CheckForResult`,
`DrawableSliderHead`) for an unjudged circle / slider head; the head post-processing runs on the state after the
judgement (field frame `simARFr`). -/
-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem sim.step.circle_check_for_result_refines (h64 : System.Platform.numBits = 64) (tn : Nat → String)
    (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (s : sim.state.St) (r : sim.step.Ref) (ut : Bool) (e : Nat) (hI : SimARInv tn fo P b0 n c s e 0 0)
    (hr : simRefOk c r) (hL : simInstOk c s r.top.val) (hp : s3aPathOk c r.top.val)
    (hLP : simLP s) (hres : sim.step.res_of s r = ok none) :
    ∃ res s', sim.step.circle_check_for_result c s r ut = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.circleCheckForResult (abs r) ut (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ simJFr s s' ∧ simLP s') := by
  have hlp : ∀ h : r.top.val < s.objs.val.length, (s.objs.val[r.top.val]'h).last_pressed.len.val ≤ 3 :=
    fun h => hLP.2 _ h
  have hpr := hLP.1
  obtain ⟨hh, hhS⟩ := sim_hobj_of_eq tn fo c r hr
  unfold sim.step.circle_check_for_result OsuModel.Sim.Sim.circleCheckForResult
  simp only [hh, bind_ok, float.F64.sub, simM_bind, hhS, Except.bind, OsuModel.Sim.Sim.st, simM_get]
  have hT : (simStS tn s).t = s.t := rfl
  have hE : (hobjS tn (simHobj c r)).endTime = (simHobj c r).end_time := rfl
  have hW : (hobjS tn (simHobj c r)).hitWindows = (simHobj c r).hit_windows.map abs := rfl
  have h1 : (abs r : Nat × Int).1 = r.top.val := rfl
  simp only [hT, hE, hW, h1]
  cases hw : (simHobj c r).hit_windows with
  | none => exact ⟨_, _, rfl, rfl, fun _ => ⟨hI, simJFr_refl s, hLP⟩⟩
  | some w =>
  simp only [Option.map_some]
  cases ut
  · -- not user-triggered
    obtain ⟨b, hb, eb⟩ := sim.playable.can_be_hit_refines w (s.t - (simHobj c r).end_time)
    have eb' : (abs w : OsuModel.Sim.HitWindows).canBeHit (s.t - (simHobj c r).end_time) = b := eb
    simp only [hb, bind_ok, eb', Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
    cases b
    · simp only [Bool.false_eq_true, ite_false, Bool.not_false, ite_true]
      obtain ⟨rm, sm, em, rlm, ilm⟩ := sim.step.miss_forcefully_frame tn fo E b0 n c hC hCS hlen (simARFr s)
        (fun _ => True) (fun _ _ _ => trivial) (simARFr_qok c s _) s r e hI (simARFr_refl s) trivial hr hL hres
      simp only [em, bind_ok, uncurry_apply_pair, simM_bind]
      cases rm with
      | Err er =>
        obtain ⟨msg, hmsg⟩ := rlm
        refine ⟨.Err er, sm, by simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], ⟨msg, ?_⟩, fun h => by cases h⟩
        simp only [hmsg, Except.bind]
      | Ok u =>
        simp only [simRelM] at rlm
        obtain ⟨hIX, hFX⟩ := ilm rfl
        simp only [rlm, Except.bind, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        cc_tail sm
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
      have hIX := hI
      have hFX := simARFr_refl s
      cc_tail s
  · simp only [ite_true, Bool.not_true, Bool.false_eq_true, ite_false]
    obtain ⟨base, hbase, ebase⟩ := sim.playable.result_for_refines w (s.t - (simHobj c r).end_time)
    have ebase' : (abs w : OsuModel.Sim.HitWindows).resultFor (s.t - (simHobj c r).end_time) = abs base := ebase
    rw [ebase']
    obtain ⟨bh, hbh, ebh⟩ := sim.basic.is_hit_refines base
    have ebh' : (abs base : OsuModel.Sim.HitResult).isHit = bh := ebh
    rw [ebh']
    simp only [hbase, bind_ok]
    by_cases hkh : (simHobj c r).kind = .Head
    · have hb1 : sim.playable.Kind.Insts.CoreCmpPartialEqKind.eq (simHobj c r).kind .Head = ok true := by
        rw [hkh, kind_eq_ok]; rfl
      have hkS : ((hobjS tn (simHobj c r)).kind == OsuModel.Sim.Kind.head) = true := by
        show (kindS _ == _) = true; rw [hkh]; rfl
      simp only [sim.step.is_classic_head, hb1, hkS, bind_ok, ite_true]
      obtain ⟨sr, hsr, esr⟩ := sim.step.slider_data_refines tn fo c r.top hr.1
      have esr' := esr (simStS tn s)
      rw [hsr]
      cases sr with
      | Err er =>
        obtain ⟨msg, hmsg⟩ := esr'
        refine ⟨.Err er, s, by simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], ⟨msg, ?_⟩, fun h => by cases h⟩
        simp only [simM_bind, hmsg, Except.bind]
      | Ok sd =>
        have esr2 : OsuModel.Sim.Sim.sliderData r.top.val (simCtxS tn fo c) (simStS tn s) = .ok (abs sd, simStS tn s) := esr'
        have hcl' : (abs sd : OsuModel.Sim.SliderData).classic = sd.classic := rfl
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, simM_bind, esr2, Except.bind, simM_pure, hcl']
        cases hcl : sd.classic
        · simp only [Bool.false_eq_true, ite_false]
          cc_mid base
        · simp only [ite_true, hbh, bind_ok]
          cases bh
          · simp only [Bool.false_eq_true, ite_false]
            rw [show OsuModel.Sim.HitResult.largeTickMiss = abs sim.basic.HitResult.LargeTickMiss from rfl]
            cc_mid sim.basic.HitResult.LargeTickMiss
          · simp only [ite_true]
            rw [show OsuModel.Sim.HitResult.largeTickHit = abs sim.basic.HitResult.LargeTickHit from rfl]
            cc_mid sim.basic.HitResult.LargeTickHit
    · have hb1 : sim.playable.Kind.Insts.CoreCmpPartialEqKind.eq (simHobj c r).kind .Head = ok false := by
        rw [kind_eq_ok]
        cases hk : (simHobj c r).kind <;> simp only [kindS] <;> first | rfl | decide | exact absurd hk hkh
      have hkS : ((hobjS tn (simHobj c r)).kind == OsuModel.Sim.Kind.head) = false := by
        show (kindS _ == _) = false
        cases hk : (simHobj c r).kind <;> simp only [kindS] <;> first | rfl | decide | simp | exact absurd hk hkh
      simp only [sim.step.is_classic_head, hb1, hkS, bind_ok, Bool.false_eq_true, ite_false, simM_bind, simM_pure,
        core.result.Result.Insts.CoreOpsTry.branch, Except.bind]
      cc_mid base

-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem sim.step.circle_update_result_refines (h64 : System.Platform.numBits = 64) (tn : Nat → String)
    (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (s : sim.state.St) (r : sim.step.Ref) (ut : Bool) (e : Nat) (hI : SimARInv tn fo P b0 n c s e 0 0)
    (hr : simRefOk c r) (hL : simInstOk c s r.top.val) (hp : s3aPathOk c r.top.val)
    (hLP : simLP s) :
    ∃ res s', sim.step.circle_update_result c s r ut = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.circleUpdateResult (abs r) ut (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ simJFr s s' ∧ simLP s') := by
  have hos := sim_sRefOk_of c s hI.inv r hr
  obtain ⟨ro, hro, ero⟩ := sim.step.res_of_refines tn fo c s r hos
  have hj : sim.step.judged s r = ok ro.isSome := by simp [sim.step.judged, hro, core.option.Option.is_some]
  have ej : OsuModel.Sim.Sim.judged (abs r) (simCtxS tn fo c) (simStS tn s) = .ok (ro.isSome, simStS tn s) := by
    unfold OsuModel.Sim.Sim.judged; simp [ero, Except.bind]
  unfold sim.step.circle_update_result OsuModel.Sim.Sim.circleUpdateResult
  simp only [hj, bind_ok, simM_bind, ej, Except.bind]
  cases hro' : ro with
  | some x =>
    simp only [Option.isSome_some, ite_true]
    exact ⟨_, _, rfl, rfl, fun _ => ⟨hI, simJFr_refl s, hLP⟩⟩
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
    exact sim.step.circle_check_for_result_refines h64 tn fo E b0 n c hC hCS hlen s r ut e hI hr hL hp hLP (hro' ▸ hro)

end OsuProofs
