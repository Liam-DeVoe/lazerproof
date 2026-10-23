/-
sim4 (D62): `update_spinner` (`DrawableSpinner` subtree update) against `OsuModel.Sim.Sim.updateSpinner`, composed from
the fragment lemmas of Sim4/Spinner.lean (spun_out_update, spinner_ticks_update, spinner_tracker_update), sim core's
miss_unjudged_nested / spinner_result (Sim/OnKilled.lean), apply_result_frame, and update_bonus_score (Sim4/Bonus.lean).
-/
import OsuProofs.Sim4.Bonus
import OsuProofs.Sim4.Spinner
import OsuProofs.Sim.OnKilled
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- the spinner fields `update_spinner` never writes (plus the tick-slot count) -/
def s4KeepSp (o : sim.state.OState) :=
  (o.life, o.lifetime_start, o.child_id, o.hit_action, o.hovered, o.head_alive, o.tracking, o.inst, o.head_inst,
   o.tick_insts, o.tick_live.val.length, o.accept_any_after, o.last_pressed, o.slider_mouse, o.spin_mouse)

theorem s4_sp_of_O (o o' : sim.state.OState) (h : simKeepO o = simKeepO o') : s4KeepSp o = s4KeepSp o' := by
  simp only [simKeepO, Prod.mk.injEq] at h; simp only [s4KeepSp, h]
theorem s4_sp_of_B (o o' : sim.state.OState) (h : s4KeepB o = s4KeepB o') : s4KeepSp o = s4KeepSp o' := by
  simp only [s4KeepB, Prod.mk.injEq] at h; simp only [s4KeepSp, h]
theorem s4_sp_of_R (o o' : sim.state.OState) (h : s4KeepR o = s4KeepR o') : s4KeepSp o = s4KeepSp o' := by
  simp only [s4KeepR, Prod.mk.injEq] at h; simp only [s4KeepSp, h]

theorem s4Fr_mono {α β γ : Type} {KO : sim.state.OState → α} {KI : sim.state.OState → β} {KI' : sim.state.OState → γ}
    (hK : ∀ o o', KI o = KI o' → KI' o = KI' o') {i : Nat} {s s' : sim.state.St} (h : s4Fr KO KI i s s') :
    s4Fr KO KI' i s s' :=
  ⟨h.keep, h.len, h.ow, fun hh hh' => hK _ _ (h.oi hh hh'), h.il⟩

/-- writing object `i` (and the instances / theta) -/
theorem s4Fr_set' {α β : Type} {KO : sim.state.OState → α} {KI : sim.state.OState → β} (s : sim.state.St)
    (i : Usize) (hi : i.val < s.objs.val.length) (o' : sim.state.OState) (ins : alloc.vec.Vec sim.state.Inst) th
    (ho : KI o' = KI (s.objs.val[i.val]'hi)) (hins : ins.val.length = s.insts.val.length) :
    s4Fr KO KI i.val s { s with objs := s.objs.set i o', insts := ins, theta := th } := by
  refine ⟨rfl, by simp [alloc.vec.Vec.set], fun j hj hj' hji => ?_, fun hj hj' => ?_, hins⟩
  · show KO ((s.objs.set i o').val[j]'hj') = _
    simp only [vec_set_val', List.getElem_set]
    rw [if_neg (fun e => hji e.symm)]
  · show KI ((s.objs.set i o').val[i.val]'hj') = _
    simp only [vec_set_val', List.getElem_set_self]
    exact ho

theorem s4Fr_set'' {α β : Type} {KO : sim.state.OState → α} {KI : sim.state.OState → β} (s : sim.state.St)
    (i : Usize) (hi : i.val < s.objs.val.length) (o' : sim.state.OState)
    (ho : KI o' = KI (s.objs.val[i.val]'hi)) :
    s4Fr KO KI i.val s { s with objs := s.objs.set i o' } :=
  s4Fr_set' (KO := KO) s i hi o' s.insts s.theta ho rfl

/-- an object-`i` write keeping `s4KeepR` keeps the `apply_result` invariant -/
theorem s4_inv_R (tn fo P b0 n c s e) (hI : SimARInv tn fo P b0 n c s e 0 0) (i : Usize)
    (hi : i.val < s.objs.val.length) (o' : sim.state.OState) (h : s4KeepR o' = s4KeepR (s.objs.val[i.val]'hi)) :
    SimARInv tn fo P b0 n c { s with objs := s.objs.set i o' } e 0 0 := by
  simp only [s4KeepR, Prod.mk.injEq] at h
  obtain ⟨-, -, -, -, h5, h6, -, -, -, -, -, h12, h13, -, -, h16, -⟩ := h
  exact sim_ar_inv_objw tn fo P b0 n c s e hI i hi o' h12 h13 h16 h5 h6 (s3a_inv_set c s i o' hI.inv hi h6)

/-! ## the Rust function split into fragments (checked by `rfl` in `s4_rus_eq`) -/
abbrev s4RR := Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St)

/-- `?` on a `Result<(), SimErr>`, then `K` -/
def s4RBr (r : core.result.Result Unit sim.err.SimErr) (s : sim.state.St) (K : Unit → s4RR) : s4RR := do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue a => K a
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
      (core.convert.FromSame sim.err.SimErr) residual
    ok (r1, s)

theorem s4RBr_ok (s : sim.state.St) (K : Unit → s4RR) : s4RBr (.Ok ()) s K = K () := by
  simp [s4RBr, core.result.Result.Insts.CoreOpsTry.branch]
theorem s4RBr_err (er : sim.err.SimErr) (s : sim.state.St) (K : Unit → s4RR) :
    s4RBr (.Err er) s K = ok (.Err er, s) := by
  simp [s4RBr, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]

/-- CheckForResult + update_bonus_score -/
def s4RTail (c : sim.state.Ctx) (s3 : sim.state.St) (i : Usize) (o1 : sim.playable.TopObj)
    (sp : sim.playable.SpinnerData) (b1 : Bool) (t : F64) : s4RR := do
  let o3 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.state.OState) s3.objs i
  let b2 := core.option.Option.is_none o3.result
  if b2 then
    if b1 then
      let b3 ← float.F64.lt t o1.h.end_time
      if b3 then sim.step.update_bonus_score c s3 i
      else
        let (r2, s4) ← sim.step.miss_unjudged_nested c s3 i
        s4RBr r2 s4 (fun _ => do
          let o4 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.state.OState) s4.objs i
          let ty ← sim.step.spinner_result o1 sp o4
          let i1 ← sim.step.max_fuel c
          let (r3, s5) ← sim.step.apply_result c s4 i1 { top := i, nested := (-1)#i64 } ty
          s4RBr r3 s5 (fun _ => sim.step.update_bonus_score c s5 i))
    else sim.step.update_bonus_score c s3 i
  else sim.step.update_bonus_score c s3 i

/-- ticks, tracker, tail -/
def s4RMid (c : sim.state.Ctx) (s1 : sim.state.St) (i : Usize) (o1 : sim.playable.TopObj)
    (sp : sim.playable.SpinnerData) (b1 : Bool) (t : F64) (spinnable : Bool) : s4RR := do
  let s2 ← sim.step.spinner_ticks_update c s1 i
  let (r1, s3) ← sim.step.spinner_tracker_update c s2 i spinnable
  s4RBr r1 s3 (fun _ => s4RTail c s3 i o1 sp b1 t)

def s4RUS (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) : s4RR := do
  let o ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.state.OState) s.objs i
  let b := core.option.Option.is_some o.result
  if b then ok (core.result.Result.Ok (), s)
  else
    let o1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.playable.TopObj) c.pb.objects i
    match o1.spinner with
    | none => ok (core.result.Result.Ok (), s)
    | some sp =>
      let b1 ← float.F64.le o1.h.start s.t
      let spinnable ← if b1 then float.F64.lt s.t o1.h.end_time else ok false
      if c.cfg.spun_out then
        let (o2, index_mut_back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice sim.state.OState) s.objs i
        let v := index_mut_back { o2 with spin_tracking := spinnable }
        let (r, s1) ← sim.step.spun_out_update c { s with objs := v } i sp spinnable
        s4RBr r s1 (fun _ => s4RMid c s1 i o1 sp b1 s.t spinnable)
      else
        let tracking ← if spinnable then
            let b2 := core.option.Option.is_none o.result
            if b2 then do
              let b3 ← replay.frames.act_contains s.pressed replay.frames.Action.Left
              if b3 then ok true else replay.frames.act_contains s.pressed replay.frames.Action.Right
            else ok false
          else ok false
        let (o2, index_mut_back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice sim.state.OState) s.objs i
        let v := index_mut_back { o2 with spin_tracking := tracking }
        s4RMid c { s with objs := v } i o1 sp b1 s.t spinnable

theorem s4_rus_eq (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) :
    sim.step.update_spinner c s i = s4RUS c s i := by
  unfold sim.step.update_spinner s4RUS s4RMid s4RTail s4RBr
  rfl

/-! ## CheckForResult + bonus -/
set_option pp.proofs false in
theorem s4_tail_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c)
    (hCS : simCSH P n tn fo c) (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (s : sim.state.St) (i : Usize)
    (e : Nat) (hI : SimARInv tn fo P b0 n c s e 0 0) (hD : some i ∈ s.dict_slots.val) (hi : i.val < c.pb.objects.val.length)
    (hsp : (c.pb.objects.val[i.val]'hi).h.kind = .Spinner) (sp : sim.playable.SpinnerData) (b1 : Bool) (t : F64)
    (hb1 : b1 = decide ((c.pb.objects.val[i.val]'hi).h.start ≤ t))
    (hcs : ∀ h : i.val < s.objs.val.length, (s.objs.val[i.val]'h).completed_spins.val * 360 < 2 ^ 63) :
    ∃ res s', s4RTail c s i (c.pb.objects.val[i.val]'hi) sp b1 t = ok (res, s') ∧
      simRelM tn s' res (s4SpinTail i.val (topS tn (c.pb.objects.val[i.val]'hi)) (abs sp) t
        (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ s4Fr simKeepO s4KeepB i.val s s') := by
  have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
  have hr1 : simRefOk c ⟨i, (-1)#i64⟩ := ⟨hi, fun h => by simp at h⟩
  have eabs : (abs (⟨i, (-1)#i64⟩ : sim.step.Ref) : Nat × Int) = (i.val, -1) := by simp [abs]
  have hbon := sim.step.update_bonus_score_refines tn fo E b0 n c hC hCS hlen s i e hI hD hi hcs
  unfold s4RTail s4SpinTail
  simp only [vec_index_eq _ _ ho, bind_ok, simM_bind, s3a_ostate tn fo c s _ ho, Except.bind]
  have hrSo : (ostateS (s.objs.val[i.val]'ho)).result = (s.objs.val[i.val]'ho).result.map abs := rfl
  have hst : (topS tn (c.pb.objects.val[i.val]'hi)).h.start = (c.pb.objects.val[i.val]'hi).h.start := rfl
  have hen : (topS tn (c.pb.objects.val[i.val]'hi)).h.endTime = (c.pb.objects.val[i.val]'hi).h.end_time := rfl
  rw [hrSo, hst, hen]
  subst hb1
  cases hro : (s.objs.val[i.val]'ho).result with
  | some x =>
    simp only [core.option.Option.is_none, Option.map_some, Option.isNone_some, Bool.false_and,
      Bool.false_eq_true, ite_false]
    exact hbon
  | none =>
  simp only [core.option.Option.is_none, Option.map_none, Option.isNone_none, Bool.true_and, ite_true]
  by_cases h1 : (c.pb.objects.val[i.val]'hi).h.start ≤ t
  case neg =>
    simp only [h1, decide_false, Bool.false_and, Bool.false_eq_true, ite_false]
    exact hbon
  by_cases h2 : t < (c.pb.objects.val[i.val]'hi).h.end_time
  case pos =>
    simp only [h1, h2, decide_true, ite_true, float.F64.lt, bind_ok, Bool.not_true, Bool.and_false,
      Bool.false_eq_true, ite_false]
    exact hbon
  simp only [h1, h2, decide_true, decide_false, ite_true, float.F64.lt, bind_ok, Bool.not_false, Bool.and_true,
    Bool.false_eq_true, ite_false]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hsz : (topS tn (c.pb.objects.val[i.val]'hi)).nested.size = (c.pb.objects.val[i.val]'hi).nested.val.length := by
    simp [topS]
  simp only [Std.Legacy.Range.size, Nat.div_one, Nat.sub_zero, Nat.add_sub_cancel, hsz]
  obtain ⟨r1, s1, e1, rr1, i1⟩ := sim.step.miss_unjudged_nested_refines tn fo E b0 n c hC hCS hlen s i e hI hi hsp
    (fun _ => hro) (hI.ik i hD)
  simp only [e1, bind_ok, uncurry_apply_pair]
  cases r1 with
  | Err er =>
    obtain ⟨msg, hmsg⟩ := rr1
    refine ⟨.Err er, s1, s4RBr_err er s1 _, ⟨msg, ?_⟩, fun h => by cases h⟩
    simp only [simM_bind, hmsg, Except.bind]
  | Ok u =>
    cases u
    obtain ⟨hI1, hQ1, hT1⟩ := i1 rfl
    simp only [simRelM] at rr1
    simp only [simM_bind, rr1, Except.bind, s4RBr_ok]
    have ho1 : i.val < s1.objs.val.length := by rw [hQ1.len]; exact ho
    have hcs2 : ∀ (s2 : sim.state.St), simARFr s1 s2 → ∀ h : i.val < s2.objs.val.length,
        (s2.objs.val[i.val]'h).completed_spins.val * 360 < 2 ^ 63 := by
      intro s2 hQ2 h
      have h2 : (s2.objs.val[i.val]'h).completed_spins = (s.objs.val[i.val]'ho).completed_spins :=
        congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) ((simARFr_trans hQ1 hQ2).ow i.val ho h)
      rw [h2]; exact hcs ho
    obtain ⟨ty, ety, hty⟩ := sim.step.spinner_result_refines (c.pb.objects.val[i.val]'hi) sp _
      (hcs2 s1 (simARFr_refl s1) ho1)
    obtain ⟨f, hf, hfS⟩ := sim.step.max_fuel_refines tn fo c hlen (simStS tn s1)
    have hres1 : sim.step.res_of s1 ⟨i, (-1)#i64⟩ = ok none := by
      simp [sim.step.res_of, vec_index_eq _ _ ho1, hT1 ho1]
    obtain ⟨r2, s2, e2, rr2, i2⟩ := sim.step.apply_result_frame tn fo E b0 n c hC hCS (simARFr s1) (fun _ => True)
      (fun _ _ _ => trivial) (simARFr_qok c s1 _) s1 f ⟨i, (-1)#i64⟩ ty e hI1 (simARFr_refl s1) trivial hr1
      (hI1.ik i (by rw [sim_keepS_dict hQ1.keep]; exact hD)) hres1
    have hab : (abs ty : OsuModel.Sim.HitResult) = hrS ty := rfl
    rw [eabs, hab, hty] at rr2
    unfold simSpinTy at rr2
    have hostS : (abs (s1.objs.val[i.val]'ho1) : OsuModel.Sim.OState) = ostateS (s1.objs.val[i.val]'ho1) := rfl
    have hmr : hrS (c.pb.objects.val[i.val]'hi).h.min_result = (topS tn (c.pb.objects.val[i.val]'hi)).h.minResult := rfl
    rw [hostS, hmr] at rr2
    simp only [vec_index_eq _ _ ho1, ety, hf, e2, bind_ok, uncurry_apply_pair,
      s3a_ostate tn fo c s1 i.val ho1, hfS, simM_bind, Except.bind]
    cases r2 with
    | Err er =>
      obtain ⟨msg, hmsg⟩ := rr2
      refine ⟨.Err er, s2, s4RBr_err er s2 _, ⟨msg, ?_⟩, fun h => by cases h⟩
      simp only [hmsg]
    | Ok u2 =>
      cases u2
      obtain ⟨hI2, hQ2⟩ := i2 rfl
      simp only [simRelM] at rr2
      obtain ⟨rb, sb, eb, rrb, ib⟩ := sim.step.update_bonus_score_refines tn fo E b0 n c hC hCS hlen s2 i e hI2
        (by rw [sim_keepS_dict hQ2.keep, sim_keepS_dict hQ1.keep]; exact hD) hi
        (hcs2 s2 hQ2)
      refine ⟨rb, sb, by rw [s4RBr_ok]; exact eb, ?_, fun h => ?_⟩
      · simp only [rr2]; exact rrb
      · obtain ⟨a, b⟩ := ib h
        exact ⟨a, s4Fr_trans (s4Fr_of_ar _ (fun _ _ h => h) s4_keepB_of (simARFr_trans hQ1 hQ2)) b⟩

/-! ## ticks, tracker, tail -/
theorem s4_U64 : (2 : Nat) ^ 54 + 1000000 ≤ U64.max := by
  have : U64.max = 2 ^ 64 - 1 := by first | scalar_tac | simp [U64.max] | (unfold U64.max; rfl)
  rw [this]; norm_num

set_option pp.proofs false in
theorem s4_mid_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c)
    (hCS : simCSH P n tn fo c) (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (s : sim.state.St) (i : Usize)
    (e : Nat) (hI : SimARInv tn fo P b0 n c s e 0 0) (hD : some i ∈ s.dict_slots.val) (hi : i.val < c.pb.objects.val.length)
    (hsp : (c.pb.objects.val[i.val]'hi).h.kind = .Spinner) (sp : sim.playable.SpinnerData) (b1 : Bool)
    (spinnable : Bool) (hb1 : b1 = decide ((c.pb.objects.val[i.val]'hi).h.start ≤ s.t))
    (hd : ∀ x ∈ c.cfg.rate_sources.val, ∀ k, x.val = .Dyn k → k.val < s.speed.val.length)
    (htl : ∀ h : i.val < s.objs.val.length,
      (s.objs.val[i.val]'h).tick_live.val.length = (c.pb.objects.val[i.val]'hi).nested.val.length)
    (htk : ∀ h : i.val < s.objs.val.length,
      (s.objs.val[i.val]'h).tick_insts.val.length = (c.pb.objects.val[i.val]'hi).nested.val.length)
    (hcs : ∀ h : i.val < s.objs.val.length, (s.objs.val[i.val]'h).completed_spins.val + 1000000 ≤ 2 ^ 54) :
    ∃ res s', s4RMid c s i (c.pb.objects.val[i.val]'hi) sp b1 s.t spinnable = ok (res, s') ∧
      simRelM tn s' res (s4TicksF i.val (topS tn (c.pb.objects.val[i.val]'hi)) s.t
        (fun _ => s4TrackerF i.val s.t spinnable
          (fun _ => s4SpinTail i.val (topS tn (c.pb.objects.val[i.val]'hi)) (abs sp) s.t))
        (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ s4Fr simKeepO s4KeepSp i.val s s' ∧
        ∀ (h : i.val < s.objs.val.length) (h' : i.val < s'.objs.val.length),
          (s'.objs.val[i.val]'h').completed_spins.val ≤ (s.objs.val[i.val]'h).completed_spins.val + 1000000) := by
  have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
  obtain ⟨s2, e2, hK2, hI2, ho', tl, ins, th, hs2, htl2, hins2⟩ := sim.step.spinner_ticks_update_refines tn fo E b0 n c e
    s i hI hD hi htl htk (fun _ => s4TrackerF i.val s.t spinnable
      (fun _ => s4SpinTail i.val (topS tn (c.pb.objects.val[i.val]'hi)) (abs sp) s.t))
  subst hs2
  have ho2 : i.val < (s.objs.set i { s.objs.val[i.val]'ho' with tick_live := tl }).val.length := by
    rw [vec_set_val', List.length_set]; exact ho
  have hcs2v : ((s.objs.set i { s.objs.val[i.val]'ho' with tick_live := tl }).val[i.val]'ho2).completed_spins =
      (s.objs.val[i.val]'ho).completed_spins := by
    simp only [vec_set_val', List.getElem_set_self]
  have hinst2 := (⟨ho2, (hI2.ik.old hD ho2).1, (hI2.ik.old hD ho2).2.1⟩ : s3aInstOk _ i.val)
  obtain ⟨r1, s3, e3, hK3, ho3', o', hs3, hkr, hcs3⟩ := sim.step.spinner_tracker_update_refines tn fo c _ i spinnable
    hinst2 hd (fun h => by rw [hcs2v]; have := hcs ho; have := s4_U64; omega)
    (fun _ => s4SpinTail i.val (topS tn (c.pb.objects.val[i.val]'hi)) (abs sp) s.t)
  have hfr2 : s4Fr simKeepO s4KeepSp i.val s
      { s with objs := s.objs.set i { s.objs.val[i.val]'ho' with tick_live := tl }, insts := ins, theta := th } :=
    s4Fr_set' s i ho' _ ins th (by simp only [s4KeepSp, htl2]) hins2
  unfold s4RMid
  simp only [e2, bind_ok, e3, uncurry_apply_pair]
  rw [hK2]
  cases r1 with
  | Err er =>
    obtain ⟨m, hm⟩ := hK3
    exact ⟨.Err er, s3, s4RBr_err er s3 _, ⟨m, hm⟩, fun h => by cases h⟩
  | Ok u =>
    cases u
    simp only [s4KR] at hK3
    subst hs3
    have hI3 := s4_inv_R tn fo P b0 n c _ e hI2 i ho3' o' hkr
    have hc3 := hcs3 rfl
    rw [hcs2v] at hc3
    have ho3 : i.val < (((s.objs.set i { s.objs.val[i.val]'ho' with tick_live := tl })).set i o').val.length := by
      rw [vec_set_val', List.length_set]; exact ho2
    have hcs3v : ((((s.objs.set i { s.objs.val[i.val]'ho' with tick_live := tl })).set i o').val[i.val]'ho3).completed_spins
        = o'.completed_spins := by
      simp only [vec_set_val', List.getElem_set_self]
    obtain ⟨rt, st, et, rrt, it⟩ := s4_tail_refines tn fo E b0 n c hC hCS hlen _ i e hI3 hD hi hsp sp b1 s.t hb1
      (fun h => by rw [hcs3v]; have := hcs ho; omega)
    refine ⟨rt, st, by rw [s4RBr_ok]; exact et, ?_, fun h => ?_⟩
    · beta_reduce at hK3 ⊢
      rw [hK3]; exact rrt
    · obtain ⟨a, b⟩ := it h
      have hfr3 := s4Fr_set'' (KO := simKeepO) _ i ho3' o' (s4_sp_of_R _ _ hkr)
      refine ⟨a, s4Fr_trans hfr2 (s4Fr_trans hfr3 (s4Fr_mono s4_sp_of_B b)), fun h h' => ?_⟩
      have hb := congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (b.oi ho3 h')
      simp only [s4KeepB] at hb
      rw [hb, hcs3v]; exact hc3

/-! ## the spec's `some sp` branch with `st`/`ctx` read once -/
def s4UpdSome (i : Nat) (o : OsuModel.Sim.TopObj) (sp : OsuModel.Sim.SpinnerData) : OsuModel.Sim.SimM Unit := do
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

def s4UpdSpinner2 (i : Nat) : OsuModel.Sim.SimM Unit := do
  let r ← OsuModel.Sim.Sim.ostate i
  if r.result.isSome = true then pure ()
  else do
    let o ← OsuModel.Sim.Sim.topObj i
    match o.spinner with
    | some sp => s4UpdSome i o sp
    | _ => pure ()

theorem s4_upd2 (i : Nat) : s4UpdSpinner i = s4UpdSpinner2 i := by
  unfold s4UpdSpinner s4UpdSpinner2 s4UpdSome
  rfl

def s4SpecBr (i : Nat) (o : OsuModel.Sim.TopObj) (sp : OsuModel.Sim.SpinnerData) (t : F64)
    (pressed : Array OsuModel.Replay.Action) (c : OsuModel.Sim.Ctx) : OsuModel.Sim.SimM Unit :=
  let spinnable : Bool := decide (o.h.start ≤ t) && decide (t < o.h.endTime)
  let jp : Unit → OsuModel.Sim.SimM Unit := fun _ =>
    s4TicksF i o t (fun _ => s4TrackerF i t spinnable (fun _ => s4SpinTail i o sp t))
  if (!c.cfg.spunOut) = true then do
    let r ← OsuModel.Sim.Sim.ostate i
    let tracking : Bool := spinnable && r.result.isNone &&
      (pressed.contains OsuModel.Replay.Action.left || pressed.contains OsuModel.Replay.Action.right)
    let __r ← OsuModel.Sim.Sim.modifyObj i fun os => { os with spinTracking := tracking }
    jp __r
  else s4SpunF i sp t spinnable c jp

theorem s4_some_eq (i : Nat) (o : OsuModel.Sim.TopObj) (sp : OsuModel.Sim.SpinnerData) (C : OsuModel.Sim.Ctx)
    (S : OsuModel.Sim.St) : s4UpdSome i o sp C S = s4SpecBr i o sp S.t S.pressed C C S := by
  unfold s4UpdSome s4SpecBr
  rfl

/-! ## `update_spinner` -/
theorem s4_trk (a x y : Bool) (pl pr : Result Bool) (hl : pl = ok x) (hr : pr = ok y) :
    (if a = true then (do let b3 ← pl; if b3 = true then ok true else pr) else ok false) = ok (a && (x || y)) := by
  subst hl hr; cases a <;> cases x <;> simp

theorem s4_relM_congr {tn : Nat → String} {s : sim.state.St} {r : core.result.Result Unit sim.err.SimErr}
    {X Y : Except String (Unit × OsuModel.Sim.St)} (h : X = Y) (hr : simRelM tn s r Y) : simRelM tn s r X := h ▸ hr

theorem s4_spn (a t b : F64) :
    (if decide (a ≤ t) = true then float.F64.lt t b else ok false) = ok (decide (a ≤ t) && decide (t < b)) := by
  cases decide (a ≤ t) <;> rfl

set_option pp.proofs false in
-- CONDITIONAL: hcs (completed_spins + 2*10^6 ≤ 2^54 for object i: report_delta's U64 premise (<= 10^6 per call, two calls) and spinner_result's completed_spins*360 < 2^63, to be carried by the step invariant); hpr/hstep/hd/htl/htk are state/context well-formedness premises; simCSH via sim_ar_cs
theorem sim.step.update_spinner_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c)
    (hCS : simCSH P n tn fo c) (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (s : sim.state.St) (i : Usize)
    (e : Nat) (hI : SimARInv tn fo P b0 n c s e 0 0) (hD : some i ∈ s.dict_slots.val) (hi : i.val < c.pb.objects.val.length)
    (hsp : (c.pb.objects.val[i.val]'hi).h.kind = .Spinner)
    (hpr : s.pressed.len.val ≤ 3)
    (hstep : s.k.val ≠ 0 → s.k.val - 1 < c.steps.val.length)
    (hd : ∀ x ∈ c.cfg.rate_sources.val, ∀ k, x.val = .Dyn k → k.val < s.speed.val.length)
    (htl : ∀ h : i.val < s.objs.val.length,
      (s.objs.val[i.val]'h).tick_live.val.length = (c.pb.objects.val[i.val]'hi).nested.val.length)
    (htk : ∀ h : i.val < s.objs.val.length,
      (s.objs.val[i.val]'h).tick_insts.val.length = (c.pb.objects.val[i.val]'hi).nested.val.length)
    (hcs : ∀ h : i.val < s.objs.val.length, (s.objs.val[i.val]'h).completed_spins.val + 2000000 ≤ 2 ^ 54) :
    ∃ res s', sim.step.update_spinner c s i = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.updateSpinner i.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ s4Fr simKeepO s4KeepSp i.val s s' ∧
        ∀ (h : i.val < s.objs.val.length) (h' : i.val < s'.objs.val.length),
          (s'.objs.val[i.val]'h').completed_spins.val ≤ (s.objs.val[i.val]'h).completed_spins.val + 2000000) := by
  have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
  rw [s4_updSpinner_eq, s4_upd2, s4_rus_eq]
  unfold s4RUS s4UpdSpinner2
  simp only [vec_index_eq _ _ ho, bind_ok, simM_bind, s3a_ostate tn fo c s _ ho, Except.bind]
  have hrSo : (ostateS (s.objs.val[i.val]'ho)).result = (s.objs.val[i.val]'ho).result.map abs := rfl
  rw [hrSo]
  cases hro : (s.objs.val[i.val]'ho).result with
  | some x =>
    simp only [core.option.Option.is_some, Option.map_some, Option.isSome_some, ite_true, simM_pure]
    exact ⟨.Ok (), s, rfl, rfl, fun _ => ⟨hI, s4Fr_refl _ _ _ s, fun _ _ => Nat.le_add_right _ _⟩⟩
  | none =>
  simp only [core.option.Option.is_some, core.option.Option.is_none, Option.map_none, Option.isSome_none,
    Option.isNone_none, Bool.false_eq_true, ite_false, ite_true, Bool.and_true, vec_index_eq _ _ hi,
    bind_ok, simM_bind, s3b_topObj tn fo c _ i.val hi, Except.bind]
  have hspS : (topS tn (c.pb.objects.val[i.val]'hi)).spinner = (c.pb.objects.val[i.val]'hi).spinner.map abs := rfl
  rw [hspS]
  cases hspo : (c.pb.objects.val[i.val]'hi).spinner with
  | none =>
    simp only [Option.map_none, simM_pure]
    exact ⟨.Ok (), s, rfl, rfl, fun _ => ⟨hI, s4Fr_refl _ _ _ s, fun _ _ => Nat.le_add_right _ _⟩⟩
  | some sp =>
  have hst : (topS tn (c.pb.objects.val[i.val]'hi)).h.start = (c.pb.objects.val[i.val]'hi).h.start := rfl
  have hen : (topS tn (c.pb.objects.val[i.val]'hi)).h.endTime = (c.pb.objects.val[i.val]'hi).h.end_time := rfl
  have hT : (simStS tn s).t = s.t := rfl
  have hSO : (simCtxS tn fo c).cfg.spunOut = c.cfg.spun_out := rfl
  simp only [Option.map_some, float.F64.le, bind_ok, s4_spn]
  rw [s4_some_eq, hT]
  unfold s4SpecBr
  simp only [hst, hen, hSO]
  have hcs1 : ∀ h : i.val < s.objs.val.length, (s.objs.val[i.val]'h).completed_spins.val + 1000000 ≤ U64.max := by
    intro h; have := hcs h; have := s4_U64; omega
  cases hso : c.cfg.spun_out with
  | false =>
    simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false, simM_bind, s3a_ostate tn fo c s _ ho,
      Except.bind, hrSo, hro, Option.map_none, Option.isNone_none, Bool.and_true]
    have hpL : replay.frames.act_contains s.pressed replay.frames.Action.Left =
        ok ((simStS tn s).pressed.contains OsuModel.Replay.Action.left) := by
      rw [replay.frames.act_contains_refines _ _ hpr]; congr 1; simp [simStS, abs, actS]
    have hpR : replay.frames.act_contains s.pressed replay.frames.Action.Right =
        ok ((simStS tn s).pressed.contains OsuModel.Replay.Action.right) := by
      rw [replay.frames.act_contains_refines _ _ hpr]; congr 1; simp [simStS, abs, actS]
    rw [s4_trk _ _ _ _ _ hpL hpR]
    simp only [bind_ok, vec_index_mut_eq _ _ ho, uncurry_apply_pair]
    generalize (decide ((c.pb.objects.val[i.val]'hi).h.start ≤ s.t) &&
      decide (s.t < (c.pb.objects.val[i.val]'hi).h.end_time) &&
      ((simStS tn s).pressed.contains OsuModel.Replay.Action.left ||
        (simStS tn s).pressed.contains OsuModel.Replay.Action.right)) = trk
    have hI1 := sim_ar_inv_objw tn fo P b0 n c s e hI i ho { s.objs.val[i.val]'ho with spin_tracking := trk }
      rfl rfl rfl rfl rfl (s3a_inv_set c s i _ hI.inv ho rfl)
    have ho1 : i.val < (s.objs.set i { s.objs.val[i.val]'ho with spin_tracking := trk }).val.length := by
      rw [vec_set_val', List.length_set]; exact ho
    obtain ⟨r, s', e', rr', ii⟩ := s4_mid_refines tn fo E b0 n c hC hCS hlen _ i e hI1 hD hi hsp sp _
      (decide ((c.pb.objects.val[i.val]'hi).h.start ≤ s.t) && decide (s.t < (c.pb.objects.val[i.val]'hi).h.end_time))
      rfl hd
      (fun h => by simp only [vec_set_val', List.getElem_set_self]; exact htl ho)
      (fun h => by simp only [vec_set_val', List.getElem_set_self]; exact htk ho)
      (fun h => by simp only [vec_set_val', List.getElem_set_self]; have := hcs ho; omega)
    refine ⟨r, s', e', s4_relM_congr (by rw [s3a_modifyObj tn fo c s i ho _
      { s.objs.val[i.val]'ho with spin_tracking := trk } rfl]) rr', fun h => ?_⟩
    obtain ⟨a, b, cc⟩ := ii h
    refine ⟨a, s4Fr_trans (s4Fr_set'' s i ho _ (by simp only [s4KeepSp])) b, fun h0 h' => ?_⟩
    have := cc ho1 h'
    simp only [vec_set_val', List.getElem_set_self] at this
    omega
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true, vec_index_mut_eq _ _ ho, bind_ok,
      uncurry_apply_pair]
    generalize (decide ((c.pb.objects.val[i.val]'hi).h.start ≤ s.t) &&
      decide (s.t < (c.pb.objects.val[i.val]'hi).h.end_time)) = spn
    unfold s4SpunF
    simp only [simM_bind]
    rw [s3a_modifyObj tn fo c s i ho _ { s.objs.val[i.val]'ho with spin_tracking := spn } rfl]
    simp only [Except.bind]
    have hI1 := sim_ar_inv_objw tn fo P b0 n c s e hI i ho { s.objs.val[i.val]'ho with spin_tracking := spn }
      rfl rfl rfl rfl rfl (s3a_inv_set c s i _ hI.inv ho rfl)
    have ho1 : i.val < (s.objs.set i { s.objs.val[i.val]'ho with spin_tracking := spn }).val.length := by
      rw [vec_set_val', List.length_set]; exact ho
    obtain ⟨r, s1, e1, hK, o'', hs1, hkr, hla, hcs'⟩ := sim.step.spun_out_update_refines tn fo c
      { s with objs := s.objs.set i { s.objs.val[i.val]'ho with spin_tracking := spn } } i sp spn ho1
      hstep hd (by simp only [vec_set_val', List.getElem_set_self]; exact hcs1 ho)
      (fun __r => s4TicksF i.val (topS tn (c.pb.objects.val[i.val]'hi)) s.t fun x => s4TrackerF i.val s.t spn
        fun x => s4SpinTail i.val (topS tn (c.pb.objects.val[i.val]'hi)) (abs sp) s.t)
    simp only [e1, bind_ok, uncurry_apply_pair]
    cases r with
    | Err er =>
      obtain ⟨m, hm⟩ := hK
      exact ⟨.Err er, s1, s4RBr_err er s1 _, ⟨m, hm⟩, fun h => by cases h⟩
    | Ok u =>
      cases u
      simp only [s4KR] at hK
      subst hs1
      have hI2 := s4_inv_R tn fo P b0 n c _ e hI1 i ho1 o'' hkr
      have hkr' := hkr
      simp only [s4KeepR, Prod.mk.injEq] at hkr'
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h16, h17, -⟩ := hkr'
      simp only [vec_set_val', List.getElem_set_self] at h16 h17
      have hc'' := hcs' rfl
      simp only [vec_set_val', List.getElem_set_self] at hc''
      have ho2 : i.val < ((s.objs.set i { s.objs.val[i.val]'ho with spin_tracking := spn }).set i o'').val.length := by
        rw [vec_set_val', List.length_set]; exact ho1
      obtain ⟨r2, s2, e2, rr2, ii⟩ := s4_mid_refines tn fo E b0 n c hC hCS hlen _ i e hI2 hD hi hsp sp _ spn rfl hd
        (fun h => by simp only [vec_set_val', List.getElem_set_self]; rw [h17]; exact htl ho)
        (fun h => by simp only [vec_set_val', List.getElem_set_self]; rw [h16]; exact htk ho)
        (fun h => by simp only [vec_set_val', List.getElem_set_self]; have := hcs ho; omega)
      refine ⟨r2, s2, by rw [s4RBr_ok]; exact e2, s4_relM_congr hK rr2, fun h => ?_⟩
      obtain ⟨a, b, cc⟩ := ii h
      refine ⟨a, s4Fr_trans (s4Fr_set'' s i ho _ (by simp only [s4KeepSp]))
        (s4Fr_trans (s4Fr_set'' _ i ho1 o'' (s4_sp_of_R _ _ hkr)) b), fun h0 h' => ?_⟩
      have := cc ho2 h'
      simp only [vec_set_val', List.getElem_set_self] at this
      omega

end OsuProofs
