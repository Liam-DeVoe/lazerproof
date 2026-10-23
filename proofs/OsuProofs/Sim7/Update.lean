import OsuProofs.Sim.OnKilled
import OsuProofs.Sim3.SC_Misc
import OsuProofs.Sim2.Geometry
import OsuProofs.Sim3.SC_Upd
import OsuProofs.Sim7.Loops
import OsuProofs.Sim7.Body
/- sim7: `sim.step.update_slider_refines` (`Sim.updateSlider`). The generated `update_slider` (duplicated tails) is
factored into `s7RUpd`/`s7RRest`/`s7RHead`/`s7RHT`/`s7RAC` (checked by `rfl` in `s7_us_eq`); the spec into
`s7UpdSlider`/`s7Rest`/`s7ChildF`/`s7HeadF`/`s7HTF`/`s7ACF` (checked by `rfl` in `s7_updSlider_eq`).
Budget: the head's first-load `update_state_from_result` costs one slack unit, so the input is
`SimARInv .. (b0 + (n+n+4)) .. e 0 0` and the output `SimARInv .. b0 .. e 0 0`; frame `s7Fr` (+ `simLP`). -/
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- `DrawableSlider.UpdateAfterChildren`: ball position, then `UpdateResult(false)` -/
def s7ACF (i : Nat) (o : OsuModel.Sim.TopObj) (t : F64) (sd : OsuModel.Sim.SliderData) (k : Nat) :
    OsuModel.Sim.SimM Unit :=
  let p0 := (t - o.h.start) / sd.duration
  do
  let prog ← OsuModel.Sim.Sim.liftNet (p0.clamp 0 1)
  let ball ← OsuModel.Sim.Sim.liftExcept (sd.curvePositionAt prog)
  OsuModel.Sim.Sim.modifyInst k fun ins =>
    { ins with size := ins.bodySize, origin := ins.bodyOffset, relAnchor := ins.bodyOffset.cdiv ins.bodySize, ballPos := ball }
  let os ← OsuModel.Sim.Sim.ostate i
  if os.result.isNone = true then OsuModel.Sim.Sim.sliderCheckForResult i else pure ()

/-- Rust `update_slider` after the children: ball position, then `slider_check_for_result` (state `s8`) -/
def s7RAC (c : sim.state.Ctx) (s8 : sim.state.St) (i k : Usize) (t : F64) («to» : sim.playable.TopObj) :
    Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St) := do
  let r6 ← sim.step.slider_data c i
  let cf6 ←
    core.result.Result.Insts.CoreOpsTry.branch r6
  match cf6 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    let f1 ← float.F64.sub t «to».h.start
    let p0 ← float.F64.div f1 val1.duration
    let f2 ← sim.step.F64_0
    let f3 ← sim.step.F64_1
    let r7 ← sim.step.clamp_net p0 f2 f3
    let cf7 ←
      core.result.Result.Insts.CoreOpsTry.branch r7
    match cf7 with
    | core.ops.control_flow.ControlFlow.Continue val2 =>
      let r8 ← sim.geometry.curve_position_at val1 val2
      let cf8 ←
        core.result.Result.Insts.CoreOpsTry.branch r8
      match cf8 with
      | core.ops.control_flow.ControlFlow.Continue val3
        =>
        let (ins, index_mut_back3) ←
          alloc.vec.Vec.index_mut
            (core.slice.index.SliceIndexUsizeSlice
            sim.state.Inst) s8.insts k
        let v3 ←
          sim.basic.Vec2.cdiv ins.body_offset
            ins.body_size
        let o3 ←
          alloc.vec.Vec.index
            (core.slice.index.SliceIndexUsizeSlice
            sim.state.OState) s8.objs i
        let b2 := core.option.Option.is_none o3.result
        if b2
        then
          let v4 :=
            index_mut_back3
              {
                ins
                  with
                  size := ins.body_size,
                  origin := ins.body_offset,
                  rel_anchor := v3,
                  ball_pos := val3
              }
          let (r9, s9) ←
            sim.step.slider_check_for_result c
              { s8 with insts := v4 } i
          let cf9 ←
            core.result.Result.Insts.CoreOpsTry.branch r9
          match cf9 with
          | core.ops.control_flow.ControlFlow.Continue _
            =>
            ok (core.result.Result.Ok (), s9)
          | core.ops.control_flow.ControlFlow.Break
            residual =>
            let r10 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                Unit (core.convert.FromSame
                sim.err.SimErr) residual
            ok (r10, s9)
        else
          let v4 :=
            index_mut_back3
              {
                ins
                  with
                  size := ins.body_size,
                  origin := ins.body_offset,
                  rel_anchor := v3,
                  ball_pos := val3
              }
          ok (core.result.Result.Ok (),
            { s8 with insts := v4 })
      | core.ops.control_flow.ControlFlow.Break residual
        =>
        let r9 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame sim.err.SimErr)
            residual
        ok (r9, s8)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r8 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame sim.err.SimErr)
          residual
      ok (r8, s8)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r7 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame sim.err.SimErr)
        residual
    ok (r7, s8)


theorem s7_tfInv_set' {P : Nat → sim.transforms.TObj → Prop} (b : Nat) (s : sim.state.St) (k : Usize)
    (hk : k.val < s.insts.val.length) (Y : sim.state.Inst) (h : s3b_TfInv P b s)
    (h1 : Y.tf = (s.insts.val[k.val]'hk).tf) (h2 : Y.body_tf = (s.insts.val[k.val]'hk).body_tf) :
    s3b_TfInv P b { s with insts := s.insts.set k Y } := by
  intro ins hins
  change ins ∈ (s.insts.set k Y).val at hins
  rw [vec_set_val'] at hins
  rcases List.mem_or_eq_of_mem_set hins with h0 | h0
  · exact h ins h0
  · subst h0; rw [h1, h2]; exact h _ (List.getElem_mem hk)

/-- an instance write keeping its transformables keeps the `apply_result` invariant -/
theorem s7_inv_inst (tn fo P b0 n c s e) (hI : SimARInv tn fo P b0 n c s e 0 0) (k : Usize)
    (hk : k.val < s.insts.val.length) (Y : sim.state.Inst)
    (h1 : Y.tf = (s.insts.val[k.val]'hk).tf) (h2 : Y.body_tf = (s.insts.val[k.val]'hk).body_tf) :
    SimARInv tn fo P b0 n c { s with insts := s.insts.set k Y } e 0 0 :=
  sim_ar_inv_hook tn fo P b0 n c s e 0 0 0 hI _ (s3b_inv_of hI.inv rfl rfl) (s3b_objFrame_of_eq rfl)
    (by show (s.insts.set k Y).val.length = _; rw [vec_set_val', List.length_set])
    (s7_tfInv_set' _ s k hk Y hI.tf h1 h2) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- `UpdateAfterChildren` (ball position, `slider_check_for_result`) -/
-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem s7_rac (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (s : sim.state.St) (i k : Usize) (e : Nat) (t : F64)
    (sd : sim.playable.SliderData) (hI : SimARInv tn fo P b0 n c s e 0 0) (hD : some i ∈ s.dict_slots.val)
    (hi : i.val < c.pb.objects.val.length) (hk : k.val < s.insts.val.length)
    (hsd : sim.step.slider_data c i = ok (.Ok sd)) (hp : s3aPathOk c i.val)
    (hti : i.val < c.tail_idx.val.length)
    (htl : (c.tail_idx.val[i.val]'hti).val < (c.pb.objects.val[i.val]'hi).nested.val.length) :
    ∃ res s', s7RAC c s i k t (c.pb.objects.val[i.val]'hi) = ok (res, s') ∧
      simRelM tn s' res (s7ACF i.val (topS tn (c.pb.objects.val[i.val]'hi)) t (abs sd) k.val
        (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ simARFr s s') := by
  have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
  have hkS : k.val < (simStS tn s).insts.size := by simpa [simStS, abs] using hk
  have hsdS : (c.pb.objects.val[i.val]'hi).slider = some sd := by
    unfold sim.step.slider_data at hsd
    simp only [vec_index_eq _ _ hi, bind_ok] at hsd
    cases h : (c.pb.objects.val[i.val]'hi).slider <;> simp [h] at hsd; rw [hsd]
  obtain ⟨hpc, hpp⟩ := hp hi sd hsdS
  obtain ⟨pr, hpr, epr⟩ := sim.step.clamp_net_refines ((t - (c.pb.objects.val[i.val]'hi).h.start) / sd.duration) 0 1
  have hst : (topS tn (c.pb.objects.val[i.val]'hi)).h.start = (c.pb.objects.val[i.val]'hi).h.start := rfl
  have hdu : (abs sd : OsuModel.Sim.SliderData).duration = sd.duration := rfl
  unfold s7RAC s7ACF
  simp only [hsd, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, float.F64.sub, float.F64.div, sim_step_F64_0,
    sim_step_F64_1, hpr, hst, hdu, simM_bind]
  have epr' := epr (simCtxS tn fo c) (simStS tn s)
  cases pr with
  | Err er =>
    obtain ⟨m, hm⟩ := epr'
    refine ⟨.Err er, s, ?_, ⟨m, ?_⟩, fun h => by cases h⟩
    · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        core.convert.FromSame]
    · simp only [simM_bind, hm, Except.bind]
  | Ok p =>
    simp only [s3b_rrel, id] at epr'
    simp only [epr', s3b_ebok]
    obtain ⟨ball, hb, eb⟩ := sim.geometry.curve_position_at_refines h64 sd p hpc hpp
    simp only [hb, bind_ok]
    cases ball with
    | Err er =>
      have : ∃ m, (abs sd : OsuModel.Sim.SliderData).curvePositionAt (abs p) = .error m := by
        cases h : (abs sd : OsuModel.Sim.SliderData).curvePositionAt (abs p) <;> rw [h] at eb <;> simp [s2_rel] at eb
        exact ⟨_, rfl⟩
      obtain ⟨m, hm⟩ := this
      refine ⟨.Err er, s, ?_, ⟨m, ?_⟩, fun h => by cases h⟩
      · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
          core.convert.FromSame]
      · simp only [abs_id] at hm
        simp only [hm, OsuModel.Sim.Sim.liftExcept, simM_throw, Except.bind]
    | Ok bv =>
      have hbS : (abs sd : OsuModel.Sim.SliderData).curvePositionAt (abs p) = .ok (abs bv) := by
        cases h : (abs sd : OsuModel.Sim.SliderData).curvePositionAt (abs p) <;> rw [h] at eb <;> simp [s2_rel] at eb
        rw [eb]
      simp only [abs_id] at hbS
      simp only [hbS, OsuModel.Sim.Sim.liftExcept, simM_pure, s3b_ebok, vec_index_mut_eq _ _ hk, uncurry_apply_pair,
        bind_ok]
      obtain ⟨v, hv, ev⟩ := sim.basic.Vec2.cdiv_refines (s.insts.val[k.val]'hk).body_offset (s.insts.val[k.val]'hk).body_size
      simp only [hv, bind_ok, vec_index_eq _ _ ho]
      let I0 := s.insts.val[k.val]'hk
      let Y : sim.state.Inst := { I0 with size := I0.body_size, origin := I0.body_offset, rel_anchor := v, ball_pos := bv }
      have hI1 : SimARInv tn fo P b0 n c { s with insts := s.insts.set k Y } e 0 0 := s7_inv_inst tn fo P b0 n c s e hI k hk Y rfl rfl
      have hF1 : simARFr s { s with insts := s.insts.set k Y } :=
        ⟨rfl, rfl, fun _ _ _ => rfl, by show (s.insts.set k Y).val.length = _; rw [vec_set_val', List.length_set]⟩
      rw [s7_modInst tn _ s k hk Y _ ?hf]
      case hf => simp only [abs] at ev ⊢; rw [ev]
      simp only [s3b_ebok, s3a_ostate tn fo c { s with insts := s.insts.set k Y } i.val ho]
      have hrS : (ostateS (s.objs.val[i.val]'ho)).result = (s.objs.val[i.val]'ho).result.map abs := rfl
      simp only [hrS]
      cases hro : (s.objs.val[i.val]'ho).result with
      | some x =>
        simp only [core.option.Option.is_none, Option.isNone_some, Option.map_some, Bool.false_eq_true, if_false,
          simM_pure]
        exact ⟨_, _, rfl, rfl, fun _ => ⟨hI1, hF1⟩⟩
      | none =>
        have hres : sim.step.res_of { s with insts := s.insts.set k Y } ⟨i, (-1)#i64⟩ = ok none := by
          simp [sim.step.res_of, vec_index_eq _ _ ho, hro]
        obtain ⟨rs, ss, es, rls, ils⟩ := sim.step.slider_check_for_result_frame tn fo E b0 n c hC hCS hlen _ i e hI1 (hI1.ik i hD) hi
          hti htl hres
        simp only [Y, I0] at es
        simp only [core.option.Option.is_none, Option.isNone_none, Option.map_none, if_true, es, bind_ok]
        cases rs with
        | Err er =>
          refine ⟨.Err er, ss, ?_, rls, fun h => by cases h⟩
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
            core.convert.FromSame]
        | Ok u =>
          obtain ⟨hI2, hF2⟩ := ils rfl
          exact ⟨.Ok (), ss, by simp [core.result.Result.Insts.CoreOpsTry.branch], rls,
            fun _ => ⟨hI2, simARFr_trans hF1 hF2⟩⟩

/-- the head instance's transforms and `UpdateResult(false)`, then `K` -/
def s7HTF (i hj hk : Nat) (t : F64) (K : Unit → OsuModel.Sim.SimM Unit) : OsuModel.Sim.SimM Unit := do
  OsuModel.Sim.Sim.modifyInst hk fun ins => { ins with tf := OsuModel.Sim.updateTransforms ins.tf t }
  let pp ← OsuModel.Sim.Sim.partPresent i OsuModel.Sim.Sim.Part.head
  if pp = true then do
    let r ← OsuModel.Sim.Sim.circleUpdateResult (i, (hj : Int)) false
    K r
  else K ()

/-- the head container (lifetime, first load, transforms, `UpdateResult(false)`), then `K` -/
def s7HeadF (i : Nat) (o : OsuModel.Sim.TopObj) (t : F64) (K : Unit → OsuModel.Sim.SimM Unit) :
    OsuModel.Sim.SimM Unit := do
  let hj ← OsuModel.Sim.Sim.headOf i
  let head ← OsuModel.Sim.Sim.nestedOf o hj
  let os ← OsuModel.Sim.Sim.ostate i
  let headAlive : Bool := !decide (t < head.start - head.preempt) && decide (t < os.headLifetimeEnd)
  OsuModel.Sim.Sim.modifyObj i fun os => { os with headAlive := headAlive }
  if headAlive = true then
    let hk := os.headInst
    do
    let ins ← OsuModel.Sim.Sim.instOf hk
    let jp : Unit → OsuModel.Sim.SimM Unit := fun _ => s7HTF i hj hk t K
    if (!ins.loaded) = true then do
      OsuModel.Sim.Sim.modifyInst hk fun ins => { ins with loaded := true }
      let r ← OsuModel.Sim.Sim.updateStateFromResult i OsuModel.Sim.Sim.Part.head 2
      jp r
    else jp ()
  else K ()

/-- Rust `update_slider`: the head instance's transforms and `circle_update_result`, then `s7RAC` -/
def s7RHT (c : sim.state.Ctx) (s7 : sim.state.St) (i k : Usize) (t : F64) (hj : Usize) («to» : sim.playable.TopObj)
    (hk : Usize) : Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St) := do
  let (i4, index_mut_back2) ←
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice sim.state.Inst) s7.insts hk
  let t1 ← sim.transforms.update_transforms i4.tf t false
  let v2 := index_mut_back2 { i4 with tf := t1 }
  let b1 ← sim.step.part_present c { s7 with insts := v2 } i sim.step.Part.Head
  if b1
  then
    let i5 ← lift (UScalar.hcast .I64 hj)
    let (r5, s8) ← sim.step.circle_update_result c { s7 with insts := v2 } { top := i, nested := i5 } false
    let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
    match cf5 with
    | core.ops.control_flow.ControlFlow.Continue _ => s7RAC c s8 i k t «to»
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r6 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame sim.err.SimErr) residual
      ok (r6, s8)
  else s7RAC c { s7 with insts := v2 } i k t «to»

/-- Rust `update_slider`: the head container, then `s7RAC` -/
def s7RHead (c : sim.state.Ctx) (s5 : sim.state.St) (i k : Usize) (t : F64) (gto : (sim.playable.TopObj → Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St)) → Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St)) :
    Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St) := do
  let hj ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.Usize) c.head_idx i
  gto fun «to» => do
    let head ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.playable.HObj) «to».nested hj
    let f ← float.F64.sub head.start head.preempt
    let b ← float.F64.lt t f
    let (s6, head_alive) ←
      if b
      then ok (s5, false)
      else
        do
        let o1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.state.OState) s5.objs i
        let head_alive1 ← float.F64.lt t o1.head_lifetime_end
        ok (s5, head_alive1)
    let (o1, index_mut_back1) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice sim.state.OState) s6.objs i
    if head_alive
    then
      let v1 := index_mut_back1 { o1 with head_alive }
      let o2 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.state.OState) v1 i
      let i3 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.state.Inst) s6.insts o2.head_inst
      let s7 ←
        if i3.loaded
        then ok { s6 with objs := v1 }
        else
          do
          let (i4, index_mut_back2) ←
            alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice sim.state.Inst) s6.insts o2.head_inst
          let v2 := index_mut_back2 { i4 with loaded := true }
          sim.step.update_state_from_result c { s6 with objs := v1, insts := v2 } i sim.step.Part.Head 2#u64
      s7RHT c s7 i k t hj «to» o2.head_inst
    else s7RAC c { s6 with objs := index_mut_back1 { o1 with head_alive } } i k t «to»


/-- the object fields `update_slider` never writes (`simKeepJ` without `head_alive`) -/
def s7KeepI (o : sim.state.OState) :=
  (o.life, o.lifetime_start, o.child_id, o.hit_action, o.hovered, o.inst, o.head_inst,
   o.tick_insts, o.tick_live, o.slider_mouse, o.spin_tracking, o.spin_mouse, o.last_angle, o.total_accumulated,
   o.accumulated_at_last_completion, o.current_spin_max, o.completed_spins, o.last_report_time, o.completed_full_spins)

/-- the frame of `update_slider`: judgement processing (`simJFr`), `head_alive`, instance writes -/
structure s7Fr (s s' : sim.state.St) : Prop where
  keep : simKeepS s' = simKeepS s
  len : s'.objs.val.length = s.objs.val.length
  ow : ∀ j (h : j < s.objs.val.length) (h' : j < s'.objs.val.length), s7KeepI (s'.objs.val[j]'h') = s7KeepI (s.objs.val[j]'h)
  il : s'.insts.val.length = s.insts.val.length

theorem s7Fr_refl (s : sim.state.St) : s7Fr s s := ⟨rfl, rfl, fun _ _ _ => rfl, rfl⟩

theorem s7Fr_trans {s1 s2 s3 : sim.state.St} (h1 : s7Fr s1 s2) (h2 : s7Fr s2 s3) : s7Fr s1 s3 :=
  ⟨h2.keep.trans h1.keep, h2.len.trans h1.len, fun j h h' => (h2.ow j (by rw [h1.len]; exact h) h').trans (h1.ow j h _),
   h2.il.trans h1.il⟩

theorem s7Fr_of_jfr {s s' : sim.state.St} (h : simJFr s s') : s7Fr s s' := by
  refine ⟨h.keep, h.len, fun j hj hj' => ?_, h.il⟩
  have e := h.ow j hj hj'
  simp only [simKeepJ, Prod.mk.injEq] at e
  simp only [s7KeepI, e]

theorem s7Fr_of_ar {s s' : sim.state.St} (h : simARFr s s') : s7Fr s s' := s7Fr_of_jfr (simJFr_of_ar h)

theorem s7_set_len (v : alloc.vec.Vec sim.state.Inst) (k : Usize) (Y : sim.state.Inst) :
    (v.set k Y).val.length = v.val.length := by rw [vec_set_val', List.length_set]

theorem s7Fr_insts (s : sim.state.St) (v : alloc.vec.Vec sim.state.Inst) (hv : v.val.length = s.insts.val.length) :
    s7Fr s { s with insts := v } :=
  ⟨rfl, rfl, fun _ _ _ => rfl, hv⟩

theorem s7Fr_ha (s : sim.state.St) (i : Usize) (hi : i.val < s.objs.val.length) (b : Bool) :
    s7Fr s { s with objs := s.objs.set i { s.objs.val[i.val]'hi with head_alive := b } } := by
  refine ⟨rfl, by simp [vec_set_val'], fun j hj hj' => ?_, rfl⟩
  simp only [vec_set_val', List.getElem_set]
  split
  · subst_vars; rfl
  · rfl

theorem s7_lp_ha {s : sim.state.St} (h : simLP s) (i : Usize) (hi : i.val < s.objs.val.length) (b : Bool) :
    simLP { s with objs := s.objs.set i { s.objs.val[i.val]'hi with head_alive := b } } := by
  refine ⟨h.1, fun j hj => ?_⟩
  have hj0 : j < s.objs.val.length := by simpa [vec_set_val'] using hj
  simp only [vec_set_val', List.getElem_set]
  split
  · subst_vars; exact h.2 _ hi
  · exact h.2 j hj0

theorem s7_inv_weak {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (tn fo b0 d n c s e)
    (hI : SimARInv tn fo P (b0 + d) n c s e 0 0) : SimARInv tn fo P b0 n c s e 0 0 :=
  ⟨hI.inv, sim_tfInv_mono E _ _ s (by omega) hI.tf, hI.ik, hI.em, hI.sp, hI.cnt, hI.seen, hI.enum⟩

theorem s7_inv_ha (tn fo P b0 n c s e) (hI : SimARInv tn fo P b0 n c s e 0 0) (i : Usize)
    (hi : i.val < s.objs.val.length) (b : Bool) :
    SimARInv tn fo P b0 n c { s with objs := s.objs.set i { s.objs.val[i.val]'hi with head_alive := b } } e 0 0 :=
  sim_ar_inv_objw tn fo P b0 n c s e hI i hi _ rfl rfl rfl rfl rfl (s3a_inv_set c s i _ hI.inv hi rfl)

theorem s7_part_inst_head (s : sim.state.St) (i : Usize) (hi : i.val < s.objs.val.length) :
    sim.step.part_inst s i .Head = ok (s.objs.val[i.val]'hi).head_inst := by
  simp [sim.step.part_inst, vec_index_eq _ _ hi, sim.step.Part.Insts.CoreCmpPartialEqPart.eq,
    sim.step.Part.read_discriminant]

theorem s7Fr_inst {s s' : sim.state.St} (hF : s7Fr s s') (i : Nat) (h : i < s.objs.val.length)
    (h' : i < s'.objs.val.length) :
    (s'.objs.val[i]'h').inst = (s.objs.val[i]'h).inst ∧ (s'.objs.val[i]'h').head_inst = (s.objs.val[i]'h).head_inst := by
  have e := hF.ow i h h'
  simp only [s7KeepI, Prod.mk.injEq] at e
  exact ⟨e.2.2.2.2.2.1, e.2.2.2.2.2.2.1⟩

theorem s7_lp_insts {s : sim.state.St} (h : simLP s) (v : alloc.vec.Vec sim.state.Inst) :
    simLP { s with insts := v } := h

/-- the head instance's transforms and `circle_update_result`, then `UpdateAfterChildren` -/
-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem s7_ht (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (hU : s7UT P)
    (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (s : sim.state.St) (i k hkk : Usize) (e : Nat) (t : F64)
    (sd : sim.playable.SliderData) (hI : SimARInv tn fo P b0 n c s e 0 0) (hD : some i ∈ s.dict_slots.val) (hLP : simLP s)
    (hi : i.val < c.pb.objects.val.length) (hhi : i.val < c.head_idx.val.length)
    (hh63 : (c.head_idx.val[i.val]'hhi).val < 2 ^ 63)
    (hhl : (c.head_idx.val[i.val]'hhi).val < (c.pb.objects.val[i.val]'hi).nested.val.length)
    (hk : ∀ h : i.val < s.objs.val.length, (s.objs.val[i.val]'h).inst = k)
    (hhk : ∀ h : i.val < s.objs.val.length, (s.objs.val[i.val]'h).head_inst = hkk)
    (hsd : sim.step.slider_data c i = ok (.Ok sd)) (hp : s3aPathOk c i.val)
    (hti : i.val < c.tail_idx.val.length)
    (htl : (c.tail_idx.val[i.val]'hti).val < (c.pb.objects.val[i.val]'hi).nested.val.length) :
    ∃ res s', s7RHT c s i k t (c.head_idx.val[i.val]'hhi) (c.pb.objects.val[i.val]'hi) hkk = ok (res, s') ∧
      simRelM tn s' res (s7HTF i.val (c.head_idx.val[i.val]'hhi).val hkk.val t
        (fun _ => s7ACF i.val (topS tn (c.pb.objects.val[i.val]'hi)) t (abs sd) k.val) (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ s7Fr s s' ∧ simLP s') := by
  have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
  have hkl : hkk.val < s.insts.val.length := by rw [← hhk ho]; exact (hI.ik.old hD ho).2.1
  have hPk := hI.tf _ (List.getElem_mem hkl)
  obtain ⟨t1, ht1, et1, pt1⟩ := hU _ _ t false hPk.1
  obtain ⟨Y, hY⟩ : ∃ Y : sim.state.Inst, Y = { s.insts.val[hkk.val]'hkl with tf := t1 } := ⟨_, rfl⟩
  have hI8 : SimARInv tn fo P b0 n c { s with insts := s.insts.set hkk Y } e 0 0 :=
    sim_ar_inv_hook tn fo P b0 n c s e 0 0 0 hI _ (s3b_inv_of hI.inv rfl rfl) (s3b_objFrame_of_eq rfl)
      (by show (s.insts.set hkk Y).val.length = _; rw [vec_set_val', List.length_set])
      (s7_tfInv_set _ s hkk hkl Y hI.tf (by rw [hY]; exact pt1) (by rw [hY]; exact hPk.2)) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hF8 : s7Fr s { s with insts := s.insts.set hkk Y } := s7Fr_insts s _ (s7_set_len _ _ _)
  have hL8 : simLP { s with insts := s.insts.set hkk Y } := s7_lp_insts hLP _
  have hch : (UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)).val = ((c.head_idx.val[i.val]'hhi).val : Int) :=
    sim_usize_to_i64 _ hh63
  obtain ⟨b1, hb1, eb1⟩ := sim.step.part_present_refines tn fo c { s with insts := s.insts.set hkk Y } i .Head ho hi
    (fun kk hkk' => by
      rw [s7_part_inst_head { s with insts := s.insts.set hkk Y } i ho] at hkk'
      simp only [Result.ok.injEq] at hkk'; subst hkk'
      show _ < (s.insts.set hkk Y).val.length
      rw [vec_set_val', List.length_set]; exact (hI.ik.old hD ho).2.1)
    (fun _ => ⟨hhi, hhl⟩)
  have hkS : hkk.val < (simStS tn s).insts.size := by simpa [simStS, abs] using hkl
  unfold s7RHT s7HTF
  simp only [vec_index_mut_eq _ _ hkl, ht1, bind_ok, uncurry_apply_pair, simM_bind]
  rw [← hY]
  rw [s7_modInst tn _ s hkk hkl Y _ ?hf]
  case hf => rw [hY]; simp only [abs] at et1 ⊢; rw [et1]
  have eb1' : OsuModel.Sim.Sim.partPresent i.val OsuModel.Sim.Sim.Part.head (simCtxS tn fo c)
      (simStS tn { s with insts := s.insts.set hkk Y }) = .ok (b1, simStS tn { s with insts := s.insts.set hkk Y }) := eb1
  simp only [s3b_ebok, hb1, eb1', bind_ok]
  have hk8 : ∀ s' : sim.state.St, s7Fr s s' → SimARInv tn fo P b0 n c s' e 0 0 → k.val < s'.insts.val.length := by
    intro s' hF hI'
    have ho' : i.val < s'.objs.val.length := by rw [hF.len]; exact ho
    rw [← hk ho, ← (s7Fr_inst hF i.val ho ho').1]; exact (hI'.ik.old (by rw [sim_keepS_dict hF.keep]; exact hD) ho').1
  cases b1
  · simp only [Bool.false_eq_true, if_false]
    obtain ⟨res, s', e1, r1, i1⟩ := s7_rac h64 tn fo E b0 n c hC hCS hlen _ i k e t sd hI8 hD hi (hk8 _ hF8 hI8) hsd hp hti htl
    exact ⟨res, s', e1, r1, fun h => let ⟨a, b⟩ := i1 h; ⟨a, s7Fr_trans hF8 (s7Fr_of_ar b), simLP_fr hL8 b⟩⟩
  · simp only [if_true, lift, bind_ok]
    have hr : simRefOk c ⟨i, UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)⟩ := ⟨hi, fun _ => by
      show (UScalar.hcast .I64 _).val.toNat < _; rw [hch]; simpa using hhl⟩
    have eabs : (abs (⟨i, UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)⟩ : sim.step.Ref) : Nat × Int) =
        (i.val, ((c.head_idx.val[i.val]'hhi).val : Int)) := by simp [abs, hch]
    obtain ⟨res, s9, e1, r1, i1⟩ := sim.step.circle_update_result_refines h64 tn fo E b0 n c hC hCS hlen _ _ false e
      hI8 hr (hI8.ik i hD) hp hL8
    rw [eabs] at r1
    rw [e1]; simp only [bind_ok, uncurry_apply_pair]
    cases res with
    | Err er =>
      obtain ⟨m, hm⟩ := r1
      refine ⟨.Err er, s9, ?_, ⟨m, ?_⟩, fun h => by cases h⟩
      · simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
          core.convert.FromSame]
      · simp only [simM_bind, hm, Except.bind]
    | Ok u =>
      obtain ⟨hI9, hJ9, hL9⟩ := i1 rfl
      simp only [simRelM] at r1
      simp only [simM_bind, r1, s3b_ebok, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have hF9 : s7Fr s s9 := s7Fr_trans hF8 (s7Fr_of_jfr hJ9)
      obtain ⟨res, s', e2, r2, i2⟩ := s7_rac h64 tn fo E b0 n c hC hCS hlen _ i k e t sd hI9 (by rw [sim_keepS_dict hF9.keep]; exact hD) hi (hk8 _ hF9 hI9) hsd hp
        hti htl
      exact ⟨res, s', e2, r2, fun h => let ⟨a, b⟩ := i2 h; ⟨a, s7Fr_trans hF9 (s7Fr_of_ar b), simLP_fr hL9 b⟩⟩


theorem s7_vset_index {α} (v : alloc.vec.Vec α) (i : Usize) (h : i.val < v.val.length) (x : α) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) (v.set i x) i = ok x := by
  rw [vec_index_eq _ _ (by simp [vec_set_val', h])]; simp [vec_set_val']

/-- the head container of `update_slider` (lifetime, first load + `update_state_from_result`, transforms,
`circle_update_result`), then `UpdateAfterChildren` -/
-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem s7_head (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (hU : s7UT P)
    (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (s : sim.state.St) (i k : Usize) (e : Nat) (t : F64)
    (sd : sim.playable.SliderData) (hI : SimARInv tn fo P (b0 + (n + n + 4)) n c s e 0 0) (hD : some i ∈ s.dict_slots.val)
    (hLP : simLP s)
    (hi : i.val < c.pb.objects.val.length) (hsl : (c.pb.objects.val[i.val]'hi).h.kind = .Slider)
    (hk : ∀ h : i.val < s.objs.val.length, (s.objs.val[i.val]'h).inst = k)
    (hsd : sim.step.slider_data c i = ok (.Ok sd)) (hp : s3aPathOk c i.val)
    (hti : i.val < c.tail_idx.val.length)
    (htl : (c.tail_idx.val[i.val]'hti).val < (c.pb.objects.val[i.val]'hi).nested.val.length)
    (gto : (sim.playable.TopObj → Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St)) →
      Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St))
    (hg : ∀ K, gto K = K (c.pb.objects.val[i.val]'hi)) :
    ∃ res s', s7RHead c s i k t gto = ok (res, s') ∧
      simRelM tn s' res (s7HeadF i.val (topS tn (c.pb.objects.val[i.val]'hi)) t
        (fun _ => s7ACF i.val (topS tn (c.pb.objects.val[i.val]'hi)) t (abs sd) k.val) (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ s7Fr s s' ∧ simLP s') := by
  have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
  obtain ⟨hhi, hh63, hhb⟩ := hC.hd i.val hi
  have hhl := hhb (Or.inl hsl)
  have ehead : OsuModel.Sim.Sim.headOf i.val (simCtxS tn fo c) (simStS tn s) =
      .ok ((c.head_idx.val[i.val]'hhi).val, simStS tn s) := by
    have hhi' : i.val < (simCtxS tn fo c).headIdx.size := by simpa [simCtxS, abs] using hhi
    simp [OsuModel.Sim.Sim.headOf, OsuModel.Sim.Sim.headIdxOf, OsuModel.Sim.Sim.getA, OsuModel.Sim.Sim.ctx, hhi',
      Except.bind, simCtxS, abs, hhi]
  have enj : OsuModel.Sim.Sim.nestedOf (topS tn (c.pb.objects.val[i.val]'hi)) (c.head_idx.val[i.val]'hhi).val
      (simCtxS tn fo c) (simStS tn s) =
      .ok (hobjS tn ((c.pb.objects.val[i.val]'hi).nested.val[(c.head_idx.val[i.val]'hhi).val]'hhl), simStS tn s) := by
    simp [OsuModel.Sim.Sim.nestedOf, OsuModel.Sim.Sim.getA, topS, hhl]
  have hI0 : SimARInv tn fo P b0 n c s e 0 0 := s7_inv_weak E tn fo b0 _ n c s e hI
  unfold s7RHead s7HeadF
  simp only [hg, vec_index_eq _ _ hhi, vec_index_eq _ _ hhl, bind_ok, float.F64.sub, float.F64.lt, simM_bind, ehead,
    enj, Except.bind, s3a_ostate tn fo c s _ ho]
  generalize hhd : (c.pb.objects.val[i.val]'hi).nested.val[(c.head_idx.val[i.val]'hhi).val]'hhl = hd at *
  have hS : (hobjS tn hd).start = hd.start := rfl
  have hP' : (hobjS tn hd).preempt = hd.preempt := rfl
  have hle : (ostateS (s.objs.val[i.val]'ho)).headLifetimeEnd = (s.objs.val[i.val]'ho).head_lifetime_end := rfl
  have hhiS : (ostateS (s.objs.val[i.val]'ho)).headInst = (s.objs.val[i.val]'ho).head_inst.val := rfl
  simp only [hS, hP', hle, hhiS]
  -- the `head_alive` write
  have hmod : ∀ b : Bool, OsuModel.Sim.Sim.modifyObj i.val (fun os => { os with headAlive := b }) (simCtxS tn fo c)
      (simStS tn s) = .ok ((), simStS tn { s with objs := s.objs.set i { s.objs.val[i.val]'ho with head_alive := b } }) :=
    fun b => s3a_modifyObj tn fo c s i ho _ _ rfl
  have hdead : ∀ b : Bool, b = false →
      ∃ res s', s7RAC c { s with objs := s.objs.set i { s.objs.val[i.val]'ho with head_alive := b } } i k t
          (c.pb.objects.val[i.val]'hi) = ok (res, s') ∧
        simRelM tn s' res (s7ACF i.val (topS tn (c.pb.objects.val[i.val]'hi)) t (abs sd) k.val (simCtxS tn fo c)
          (simStS tn { s with objs := s.objs.set i { s.objs.val[i.val]'ho with head_alive := b } })) ∧
        (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ s7Fr s s' ∧ simLP s') := by
    intro b _
    have hF6 := s7Fr_ha s i ho b
    have hI6 := s7_inv_ha tn fo P b0 n c s e hI0 i ho b
    have ho6 : i.val < ({ s with objs := s.objs.set i { s.objs.val[i.val]'ho with head_alive := b } } : sim.state.St).objs.val.length := by
      rw [hF6.len]; exact ho
    have hk6 : k.val < s.insts.val.length := by
      rw [← hk ho]; exact (hI0.ik.old hD ho).1
    obtain ⟨res, s', e1, r1, i1⟩ := s7_rac h64 tn fo E b0 n c hC hCS hlen _ i k e t sd hI6 hD hi hk6 hsd hp hti htl
    exact ⟨res, s', e1, r1, fun h => let ⟨a, b⟩ := i1 h; ⟨a, s7Fr_trans hF6 (s7Fr_of_ar b), simLP_fr (s7_lp_ha hLP i ho _) b⟩⟩
  by_cases hb : t < hd.start - hd.preempt
  · simp only [hb, decide_true, if_true, bind_ok, Bool.not_true, Bool.false_and, vec_index_mut_eq _ _ ho,
      uncurry_apply_pair, Bool.false_eq_true, if_false, hmod, s3b_ebok]
    exact hdead false rfl
  · simp only [hb, decide_false, Bool.false_eq_true, if_false, vec_index_eq _ _ ho, bind_ok, Bool.not_false,
      Bool.true_and, vec_index_mut_eq _ _ ho, uncurry_apply_pair, hmod, s3b_ebok]
    by_cases hl : t < (s.objs.val[i.val]'ho).head_lifetime_end
    · simp only [hl, decide_true, if_true]
      have hkl : (s.objs.val[i.val]'ho).head_inst.val < s.insts.val.length := (hI.ik.old hD ho).2.1
      have hF6 := s7Fr_ha s i ho true
      have hI6 := s7_inv_ha tn fo P _ n c s e hI i ho true
      have hL6 := s7_lp_ha hLP i ho true
      have ho6 : i.val < ({ s with objs := s.objs.set i { s.objs.val[i.val]'ho with head_alive := true } } : sim.state.St).objs.val.length := by
        rw [hF6.len]; exact ho
      have hk6 : ∀ h : i.val < ({ s with objs := s.objs.set i { s.objs.val[i.val]'ho with head_alive := true } } : sim.state.St).objs.val.length,
          (({ s with objs := s.objs.set i { s.objs.val[i.val]'ho with head_alive := true } } : sim.state.St).objs.val[i.val]'h).inst = k :=
        fun h => by rw [(s7Fr_inst hF6 i.val ho h).1]; exact hk ho
      have hhk6 : ∀ h : i.val < ({ s with objs := s.objs.set i { s.objs.val[i.val]'ho with head_alive := true } } : sim.state.St).objs.val.length,
          (({ s with objs := s.objs.set i { s.objs.val[i.val]'ho with head_alive := true } } : sim.state.St).objs.val[i.val]'h).head_inst =
            (s.objs.val[i.val]'ho).head_inst :=
        fun h => (s7Fr_inst hF6 i.val ho h).2
      have eI := s3a_instOf tn fo c ({ s with objs := s.objs.set i { s.objs.val[i.val]'ho with head_alive := true } } : sim.state.St)
        _ hkl
      have hla : (abs (s.insts.val[(s.objs.val[i.val]'ho).head_inst.val]'hkl) : OsuModel.Sim.Inst).loaded =
          (s.insts.val[(s.objs.val[i.val]'ho).head_inst.val]'hkl).loaded := rfl
      simp only [s7_vset_index _ _ ho, bind_ok, vec_index_eq _ _ hkl, simM_bind, eI, Except.bind, hla]
      by_cases hld : (s.insts.val[(s.objs.val[i.val]'ho).head_inst.val]'hkl).loaded = true
      · simp only [hld, if_true, bind_ok, Bool.not_true, Bool.false_eq_true, if_false]
        obtain ⟨res, s', e1, r1, i1⟩ := s7_ht h64 tn fo E hU b0 n c hC hCS hlen _ i k _ e t sd
          (s7_inv_weak E tn fo b0 _ n c _ e hI6) hD hL6 hi hhi hh63 hhl hk6 hhk6 hsd hp hti htl
        exact ⟨res, s', e1, r1, fun h => let ⟨a, b, d⟩ := i1 h; ⟨a, s7Fr_trans hF6 b, d⟩⟩
      · simp only [hld, Bool.false_eq_true, if_false, Bool.not_false, if_true, vec_index_mut_eq _ _ hkl,
          uncurry_apply_pair, bind_ok]
        obtain ⟨Y, hY⟩ : ∃ Y : sim.state.Inst, Y = { s.insts.val[(s.objs.val[i.val]'ho).head_inst.val]'hkl with loaded := true } :=
          ⟨_, rfl⟩
        obtain ⟨sL, hsL⟩ : ∃ sL : sim.state.St, sL = { s with objs := s.objs.set i { s.objs.val[i.val]'ho with head_alive := true }, insts := s.insts.set (s.objs.val[i.val]'ho).head_inst Y } := ⟨_, rfl⟩
        have hIL : SimARInv tn fo P (b0 + (n + n + 4)) n c sL e 0 0 := by
          rw [hsL]; exact s7_inv_inst tn fo P _ n c _ e hI6 _ hkl Y (by rw [hY]) (by rw [hY])
        have hFL : s7Fr s sL := by rw [hsL]; exact s7Fr_trans hF6 (s7Fr_insts _ _ (s7_set_len _ _ _))
        have hLL : simLP sL := by rw [hsL]; exact hL6
        have hmi : OsuModel.Sim.Sim.modifyInst (s.objs.val[i.val]'ho).head_inst.val (fun ins => { ins with loaded := true })
            (simCtxS tn fo c) (simStS tn ({ s with objs := s.objs.set i { s.objs.val[i.val]'ho with head_alive := true } } : sim.state.St)) =
            .ok ((), simStS tn sL) := by
          rw [hsL]; exact s7_modInst tn _ ({ s with objs := s.objs.set i { s.objs.val[i.val]'ho with head_alive := true } } : sim.state.St) _ hkl Y (fun ins => { ins with loaded := true }) (by rw [hY]; rfl)
        have hoL : i.val < sL.objs.val.length := by rw [hFL.len]; exact ho
        have hk1 : (sL.objs.val[i.val]'hoL).inst.val < sL.insts.val.length := (hIL.ik.old (by rw [sim_keepS_dict hFL.keep]; exact hD) hoL).1
        have hk2 : (sL.objs.val[i.val]'hoL).head_inst.val < sL.insts.val.length := (hIL.ik.old (by rw [sim_keepS_dict hFL.keep]; exact hD) hoL).2.1
        have hPL : s3b_TfInv P (b0 + (simUnj sL + 0) * (n + n + 4) + n + n + 4) sL := by
          have h0 := hIL.tf
          rwa [show b0 + (n + n + 4) + (simUnj sL + 0) * (n + n + 4) = b0 + (simUnj sL + 0) * (n + n + 4) + n + n + 4 by
            generalize (simUnj sL + 0) * (n + n + 4) = X; omega] at h0
        obtain ⟨s1, eu, su, hinv1, hTf1, hil1, hol1, -, hfr1, hof1, hus1⟩ :=
          s3c_update_state_from_result_strong tn fo E _ n c sL i .Head 2#u64 hIL.inv hPL
            (fun ns => hCS i .Head ns hi hhi hh63 (fun _ => hhl)) hoL hk1 hk2 hhi hh63 (fun _ => hhl)
        have su' : OsuModel.Sim.Sim.updateStateFromResult i.val OsuModel.Sim.Sim.Part.head 2 (simCtxS tn fo c) (simStS tn sL) =
            .ok ((), simStS tn s1) := su
        have eu' := eu
        rw [hsL, hY] at eu'; dsimp only at eu'
        have hmi' := hmi
        dsimp only at hmi'
        rw [eu']
        simp only [bind_ok, simM_bind, hmi', Except.bind, s3b_ebok, su']
        have hA1 : simARFr sL s1 := (simARFr_qok c sL (fun _ => True)).us sL s1 i (simARFr_refl sL) hus1
        have hF1 : s7Fr s s1 := s7Fr_trans hFL (s7Fr_of_ar hA1)
        have hI1 : SimARInv tn fo P b0 n c s1 e 0 0 := by
          obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩ := hfr1
          exact sim_ar_inv_hook tn fo P b0 n c sL e 0 0 0 (s7_inv_weak E tn fo b0 _ n c sL e hIL) s1 hinv1 hof1 hil1 hTf1
            f1 f2 f3 f4 f5 f6 f7 f8 f9 f11
        have ho1 : i.val < s1.objs.val.length := by rw [hF1.len]; exact ho
        obtain ⟨res, s', e1, r1, i1⟩ := s7_ht h64 tn fo E hU b0 n c hC hCS hlen s1 i k _ e t sd hI1 (by rw [sim_keepS_dict hF1.keep]; exact hD) (simLP_fr hLL hA1)
          hi hhi hh63 hhl (fun h => by rw [(s7Fr_inst hF1 i.val ho h).1]; exact hk ho)
          (fun h => (s7Fr_inst hF1 i.val ho h).2) hsd hp hti htl
        exact ⟨res, s', e1, r1, fun h => let ⟨a, b, d⟩ := i1 h; ⟨a, s7Fr_trans hF1 b, d⟩⟩
    · simp only [hl, decide_false, Bool.false_eq_true, if_false]
      exact hdead false rfl


/-- tick, repeat and tail containers, then the head and `UpdateAfterChildren` -/
def s7ChildF (i : Nat) (o : OsuModel.Sim.TopObj) (t : F64) (sd : OsuModel.Sim.SliderData) (k : Nat) :
    OsuModel.Sim.SimM Unit := do
  forIn [OsuModel.Sim.Kind.tick, OsuModel.Sim.Kind.repeat, OsuModel.Sim.Kind.tail] PUnit.unit fun kind _ => do
    forIn [:o.nested.size] PUnit.unit (s7KindF i o kind)
    pure (ForInStep.yield PUnit.unit)
  s7HeadF i o t (fun _ => s7ACF i o t sd k)


/-- after the `drawableTracking` write: tracking, body, children -/
def s7Rest (i : Nat) (o : OsuModel.Sim.TopObj) (t : F64) (sd : OsuModel.Sim.SliderData) (k : Nat) :
    OsuModel.Sim.SimM Unit := do
  let os ← OsuModel.Sim.Sim.ostate i
  let inArea ← OsuModel.Sim.Sim.mouseInFollowArea i os.tracking
  OsuModel.Sim.Sim.updateTracking i inArea
  s7BodyF o t sd k (fun _ => s7ChildF i o t sd k)


/-- Rust `update_slider` after the `drawable_tracking` write (state `s1`, tracking flag `tr`) -/
def s7RRest (c : sim.state.Ctx) (s1 : sim.state.St) (i k : Usize) (t : F64) (tr : Bool) (gto : (sim.playable.TopObj → Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St)) → Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St)) :
    Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St) := do
  let r ← sim.step.mouse_in_follow_area c s1 i tr
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s1' ← sim.step.update_tracking c s1 i val
    let (r1, s2) ← sim.step.slider_body_update c s1' i k t
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let (r2, s3) ← sim.step.update_slider_nested_kind c s2 i sim.playable.Kind.Tick
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let (r3, s4) ← sim.step.update_slider_nested_kind c s3 i sim.playable.Kind.Repeat
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let (r4, s5) ← sim.step.update_slider_nested_kind c s4 i sim.playable.Kind.Tail
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue _ => s7RHead c s5 i k t gto
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r5 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                Unit (core.convert.FromSame sim.err.SimErr) residual
            ok (r5, s5)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r4 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame sim.err.SimErr) residual
          ok (r4, s4)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame sim.err.SimErr) residual
        ok (r3, s3)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame sim.err.SimErr) residual
      ok (r2, s2)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame sim.err.SimErr) residual
    ok (r1, s1)


/-- `Sim.updateSlider` assembled from the fragments -/
def s7UpdSlider (i : Nat) : OsuModel.Sim.SimM Unit := do
  let o ← OsuModel.Sim.Sim.topObj i
  let s1 ← OsuModel.Sim.Sim.st
  let t := s1.t
  let sd ← OsuModel.Sim.Sim.sliderData i
  let os0 ← OsuModel.Sim.Sim.ostate i
  let k := os0.inst
  let os ← OsuModel.Sim.Sim.ostate i
  let ins ← OsuModel.Sim.Sim.instOf k
  let jp : Unit → OsuModel.Sim.SimM Unit := fun _ => s7Rest i o t sd k
  if (os.tracking != ins.drawableTracking) = true then do
    OsuModel.Sim.Sim.modifyInst k fun ins => { ins with drawableTracking := os.tracking }
    let c ← OsuModel.Sim.Sim.ctx
    if (c.cfg.strictTracking && !os.tracking && os.result.isNone && !decide (t < o.h.start)) = true then do
      forIn [:o.nested.size] PUnit.unit (s7StrictF i o)
      jp ()
    else jp ()
  else jp ()

theorem s7_updSlider_eq (i : Nat) : OsuModel.Sim.Sim.updateSlider i = s7UpdSlider i := by
  unfold OsuModel.Sim.Sim.updateSlider s7UpdSlider s7Rest s7BodyF s7ChildF s7HeadF s7HTF s7ACF s7KindF s7StrictF
  rfl


/-- Rust `update_slider` with the shared tails factored out -/
def s7RUpd (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) :
    Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St) := do
  let o ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.state.OState) s.objs i
  let os_unjudged := core.option.Option.is_none o.result
  let i1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.state.Inst) s.insts o.inst
  if o.tracking != i1.drawable_tracking
  then
    let (i2, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice sim.state.Inst) s.insts o.inst
    if c.cfg.strict_tracking
    then
      if o.tracking
      then
        let v := index_mut_back { i2 with drawable_tracking := o.tracking }
        s7RRest c { s with insts := v } i o.inst s.t o.tracking (fun K => do let «to» ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.playable.TopObj) c.pb.objects i; K «to»)
      else
        if os_unjudged
        then
          let «to» ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.playable.TopObj) c.pb.objects i
          let b ← float.F64.lt s.t «to».h.start
          if b
          then
            let v := index_mut_back { i2 with drawable_tracking := o.tracking }
            s7RRest c { s with insts := v } i o.inst s.t o.tracking (fun K => K «to»)
          else
            let v := index_mut_back { i2 with drawable_tracking := o.tracking }
            let (r, s1) ← sim.step.strict_tracking_miss c { s with insts := v } i
            let cf ← core.result.Result.Insts.CoreOpsTry.branch r
            match cf with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let o1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.state.OState) s1.objs i
              s7RRest c s1 i o.inst s.t o1.tracking (fun K => K «to»)
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r1 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame sim.err.SimErr) residual
              ok (r1, s1)
        else
          let v := index_mut_back { i2 with drawable_tracking := o.tracking }
          s7RRest c { s with insts := v } i o.inst s.t o.tracking (fun K => do let «to» ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.playable.TopObj) c.pb.objects i; K «to»)
    else
      let v := index_mut_back { i2 with drawable_tracking := o.tracking }
      s7RRest c { s with insts := v } i o.inst s.t o.tracking (fun K => do let «to» ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.playable.TopObj) c.pb.objects i; K «to»)
  else s7RRest c s i o.inst s.t o.tracking (fun K => do let «to» ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.playable.TopObj) c.pb.objects i; K «to»)

theorem s7_us_eq (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) : sim.step.update_slider c s i = s7RUpd c s i := by
  unfold sim.step.update_slider s7RUpd s7RRest s7RHead s7RHT s7RAC
  rfl


theorem s7_kT : kindS sim.playable.Kind.Tick = OsuModel.Sim.Kind.tick := rfl
theorem s7_kR : kindS sim.playable.Kind.Repeat = OsuModel.Sim.Kind.repeat := rfl
theorem s7_kL : kindS sim.playable.Kind.Tail = OsuModel.Sim.Kind.tail := rfl

/-- mouse tracking, the slider body, the nested `tick/repeat/tail` passes, then the head container -/
-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem s7_rest (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (hU : s7UT P)
    (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (s : sim.state.St) (i k : Usize) (e : Nat) (t : F64)
    (sd : sim.playable.SliderData) (tr : Bool) (hI : SimARInv tn fo P (b0 + (n + n + 4)) n c s e 0 0)
    (hD : some i ∈ s.dict_slots.val) (hLP : simLP s)
    (hi : i.val < c.pb.objects.val.length) (hsl : (c.pb.objects.val[i.val]'hi).h.kind = .Slider)
    (hk : ∀ h : i.val < s.objs.val.length, (s.objs.val[i.val]'h).inst = k)
    (htr : ∀ h : i.val < s.objs.val.length, (s.objs.val[i.val]'h).tracking = tr)
    (hsd : sim.step.slider_data c i = ok (.Ok sd)) (hp : s3aPathOk c i.val)
    (hti : i.val < c.tail_idx.val.length)
    (htl : (c.tail_idx.val[i.val]'hti).val < (c.pb.objects.val[i.val]'hi).nested.val.length)
    (gto : (sim.playable.TopObj → Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St)) →
      Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St))
    (hg : ∀ K, gto K = K (c.pb.objects.val[i.val]'hi)) :
    ∃ res s', s7RRest c s i k t tr gto = ok (res, s') ∧
      simRelM tn s' res (s7Rest i.val (topS tn (c.pb.objects.val[i.val]'hi)) t (abs sd) k.val (simCtxS tn fo c)
        (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ s7Fr s s' ∧ simLP s') := by
  have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
  have hip : s3aInstOk s i.val := ⟨ho, (hI.ik.old hD ho).1, (hI.ik.old hD ho).2.1⟩
  obtain ⟨r0, hr0, er0⟩ := sim.step.mouse_in_follow_area_refines h64 tn fo c s i tr hI.inv hip hp
  have hosT : (ostateS (s.objs.val[i.val]'ho)).tracking = tr := by rw [← htr ho]; rfl
  unfold s7RRest s7Rest
  simp only [hr0, bind_ok, simM_bind, s3a_ostate tn fo c s _ ho, Except.bind, hosT]
  cases r0 with
  | Err er =>
    obtain ⟨msg, hmsg⟩ := er0
    refine ⟨.Err er, s, ?_, ⟨msg, ?_⟩, fun h => by cases h⟩
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        core.convert.FromSame]
    · simp only [hmsg]
  | Ok v =>
  simp only [s3aR, id] at er0
  simp only [er0, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨s1, e1, eS1, ⟨aj, hs1⟩, inv1, -⟩ := sim.step.update_tracking_refines tn fo c s i v hI.inv ho (hLP.2 _ ho) hLP.1
  simp only [e1, bind_ok, eS1, Except.bind]
  have hI1 : SimARInv tn fo P (b0 + (n + n + 4)) n c s1 e 0 0 := by
    rw [hs1]; rw [hs1] at inv1; exact sim_ar_inv_objw tn fo P _ n c s e hI i ho _ rfl rfl rfl rfl rfl inv1
  have hF1 : s7Fr s s1 := by rw [hs1]; exact s7Fr_of_jfr (simJFr_track s i ho _ _ aj _ _)
  have hL1 : simLP s1 := by rw [hs1]; exact simLP_track hLP i _ _ _ aj _
  have ho1 : i.val < s1.objs.val.length := by rw [hF1.len]; exact ho
  have hk1 : k.val < s1.insts.val.length := by
    rw [← hk ho, ← (s7Fr_inst hF1 i.val ho ho1).1]; exact (hI1.ik.old (by rw [sim_keepS_dict hF1.keep]; exact hD) ho1).1
  obtain ⟨r2, s2, e2, rr2, i2⟩ := sim.step.slider_body_update_refines tn fo hU _ c s1 i k t sd hi hk1 hsd hI1.tf
  have rr2' := rr2 (fun _ => s7ChildF i.val (topS tn (c.pb.objects.val[i.val]'hi)) t (abs sd) k.val)
  simp only [e2, bind_ok, uncurry_apply_pair]
  cases r2 with
  | Err er =>
    obtain ⟨m, hm⟩ := rr2'
    refine ⟨.Err er, s2, ?_, ⟨m, hm⟩, fun h => by cases h⟩
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      core.convert.FromSame]
  | Ok u =>
  simp only [s7KR] at rr2'
  rw [rr2']
  obtain ⟨Y, hs2, -, -, hT2⟩ := i2 rfl
  have hI2 : SimARInv tn fo P (b0 + (n + n + 4)) n c s2 e 0 0 := by
    subst hs2
    exact sim_ar_inv_hook tn fo P _ n c s1 e 0 0 0 hI1 _ (s3b_inv_of hI1.inv rfl rfl) (s3b_objFrame_of_eq rfl)
      (by show (s1.insts.set k Y).val.length = _; rw [vec_set_val', List.length_set]) hT2
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hF2 : s7Fr s s2 := by rw [hs2]; exact s7Fr_trans hF1 (s7Fr_insts _ _ (s7_set_len _ _ _))
  have hL2 : simLP s2 := by rw [hs2]; exact s7_lp_insts hL1 _
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hsz : (topS tn (c.pb.objects.val[i.val]'hi)).nested.size = (c.pb.objects.val[i.val]'hi).nested.val.length := by
    simp [topS]
  unfold s7ChildF
  simp only [List.forIn_cons, List.forIn_nil, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.div_one, Nat.sub_zero, Nat.add_sub_cancel, hsz, simM_bind]
  -- tick
  obtain ⟨r3, s3, e3, rr3, i3⟩ :=
    sim.step.update_slider_nested_kind_refines tn fo E _ n c hC hCS hlen s2 i .Tick e hI2 (hI2.ik i (by rw [sim_keepS_dict hF2.keep]; exact hD)) hi hsl
  rw [s7_kT] at rr3
  simp only [e3, bind_ok, uncurry_apply_pair]
  cases r3 with
  | Err er =>
    obtain ⟨m, hm⟩ := rr3
    refine ⟨.Err er, s3, ?_, ⟨m, ?_⟩, fun h => by cases h⟩
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        core.convert.FromSame]
    · simp only [simM_bind, hm, Except.bind]
  | Ok u =>
  simp only [simRelM] at rr3
  obtain ⟨hI3, hA3⟩ := i3 rfl
  have hF3 : s7Fr s s3 := s7Fr_trans hF2 (s7Fr_of_ar hA3)
  have hL3 : simLP s3 := simLP_fr hL2 hA3
  simp only [rr3, Except.bind, simM_pure, simM_bind, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  -- repeat
  obtain ⟨r4, s4, e4, rr4, i4⟩ :=
    sim.step.update_slider_nested_kind_refines tn fo E _ n c hC hCS hlen s3 i .Repeat e hI3 (hI3.ik i (by rw [sim_keepS_dict hF3.keep]; exact hD)) hi hsl
  rw [s7_kR] at rr4
  simp only [e4, bind_ok, uncurry_apply_pair]
  cases r4 with
  | Err er =>
    obtain ⟨m, hm⟩ := rr4
    refine ⟨.Err er, s4, ?_, ⟨m, ?_⟩, fun h => by cases h⟩
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        core.convert.FromSame]
    · simp only [simM_bind, hm, Except.bind]
  | Ok u =>
  simp only [simRelM] at rr4
  obtain ⟨hI4, hA4⟩ := i4 rfl
  have hF4 : s7Fr s s4 := s7Fr_trans hF3 (s7Fr_of_ar hA4)
  have hL4 : simLP s4 := simLP_fr hL3 hA4
  simp only [rr4, Except.bind, simM_pure, simM_bind, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  -- tail
  obtain ⟨r5, s5, e5, rr5, i5⟩ :=
    sim.step.update_slider_nested_kind_refines tn fo E _ n c hC hCS hlen s4 i .Tail e hI4 (hI4.ik i (by rw [sim_keepS_dict hF4.keep]; exact hD)) hi hsl
  rw [s7_kL] at rr5
  simp only [e5, bind_ok, uncurry_apply_pair]
  cases r5 with
  | Err er =>
    obtain ⟨m, hm⟩ := rr5
    refine ⟨.Err er, s5, ?_, ⟨m, ?_⟩, fun h => by cases h⟩
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        core.convert.FromSame]
    · simp only [simM_bind, hm, Except.bind]
  | Ok u =>
  simp only [simRelM] at rr5
  obtain ⟨hI5, hA5⟩ := i5 rfl
  have hF5 : s7Fr s s5 := s7Fr_trans hF4 (s7Fr_of_ar hA5)
  have hL5 : simLP s5 := simLP_fr hL4 hA5
  simp only [rr5, Except.bind, simM_pure, simM_bind, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨res, s', e6, r6, i6⟩ := s7_head h64 tn fo E hU b0 n c hC hCS hlen s5 i k e t sd hI5 (by rw [sim_keepS_dict hF5.keep]; exact hD) hL5 hi hsl
    (fun h => by rw [(s7Fr_inst hF5 i.val ho h).1]; exact hk ho) hsd hp hti htl gto hg
  exact ⟨res, s', e6, r6, fun h => let ⟨a, b, d⟩ := i6 h; ⟨a, s7Fr_trans hF5 b, d⟩⟩


theorem s7_isNone (o : sim.state.OState) : (ostateS o).result.isNone = core.option.Option.is_none o.result := by
  show (o.result.map abs).isNone = _
  cases o.result <;> rfl

theorem s7_resid_simp (er : sim.err.SimErr) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit (core.convert.FromSame sim.err.SimErr)
      (core.result.Result.Err er) = ok (core.result.Result.Err er) := by
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
    core.convert.FromSame]

/-- without slider data `mouse_in_follow_area` fails first -/
theorem s7_rest_err (c : sim.state.Ctx) (s : sim.state.St) (i k : Usize) (t : F64) (tr : Bool)
    (gto : (sim.playable.TopObj → Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St)) →
      Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St))
    (hi : i.val < c.pb.objects.val.length) (hs : (c.pb.objects.val[i.val]'hi).slider = none) :
    ∃ er, s7RRest c s i k t tr gto = ok (.Err er, s) := by
  refine ⟨.Internal .MissingSliderData, ?_⟩
  unfold s7RRest sim.step.mouse_in_follow_area sim.step.slider_data
  simp only [vec_index_eq _ _ hi, bind_ok, hs]
  simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
    core.convert.FromSame]

/-- without slider data the Rust step ends in `Err` (the spec fails in `sliderData`) -/
theorem s7_upd_err (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (s : sim.state.St) (i : Usize) (e : Nat)
    (hI : SimARInv tn fo P b0 n c s e 0 0) (hD : some i ∈ s.dict_slots.val) (hi : i.val < c.pb.objects.val.length)
    (hST : s7StrictOk tn c i.val) (hs : (c.pb.objects.val[i.val]'hi).slider = none) :
    ∃ er s', s7RUpd c s i = ok (.Err er, s') := by
  have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
  have hkl : (s.objs.val[i.val]'ho).inst.val < s.insts.val.length := (hI.ik.old hD ho).1
  unfold s7RUpd
  simp only [vec_index_eq _ _ ho, vec_index_eq _ _ hkl, bind_ok]
  split
  · simp only [vec_index_mut_eq _ _ hkl, uncurry_apply_pair, bind_ok]
    split
    · split
      · exact (s7_rest_err c _ i _ _ _ _ hi hs).elim fun er h => ⟨er, _, h⟩
      · split
        · simp only [vec_index_eq _ _ hi, bind_ok, float.F64.lt]
          split
          · exact (s7_rest_err c _ i _ _ _ _ hi hs).elim fun er h => ⟨er, _, h⟩
          · have hID := s7_inv_inst tn fo P b0 n c s e hI _ hkl
              { s.insts.val[(s.objs.val[i.val]'ho).inst.val]'hkl with drawable_tracking := (s.objs.val[i.val]'ho).tracking }
              rfl rfl
            obtain ⟨r, s1, e1, -, i1⟩ := sim.step.strict_tracking_miss_refines tn fo E b0 n c hC hCS hlen _ i e hID (hID.ik i hD) hi hST
            rw [e1]; simp only [bind_ok, uncurry_apply_pair]
            cases r with
            | Err er =>
              exact ⟨er, s1, by simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, s7_resid_simp]⟩
            | Ok u =>
              obtain ⟨hI1, hA1⟩ := i1 rfl
              have ho1 : i.val < s1.objs.val.length := by rw [hA1.len]; exact ho
              simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, vec_index_eq _ _ ho1]
              exact (s7_rest_err c _ i _ _ _ _ hi hs).elim fun er h => ⟨er, _, h⟩
        · exact (s7_rest_err c _ i _ _ _ _ hi hs).elim fun er h => ⟨er, _, h⟩
    · exact (s7_rest_err c _ i _ _ _ _ hi hs).elim fun er h => ⟨er, _, h⟩
  · exact (s7_rest_err c _ i _ _ _ _ hi hs).elim fun er h => ⟨er, _, h⟩

/-- `DrawableSlider.Update` + `UpdateAfterChildren` for one alive slider (`Sim.updateSlider`) -/
-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00);
-- hU (update_transforms law) is discharged by s7_ut_s2 for s2_tfOk; hST is a context premise (type-name table vs strict_tail)
theorem sim.step.update_slider_refines (h64 : System.Platform.numBits = 64) (tn : Nat → String)
    (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (hU : s7UT P)
    (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (s : sim.state.St) (i : Usize) (e : Nat)
    (hI : SimARInv tn fo P (b0 + (n + n + 4)) n c s e 0 0) (hD : some i ∈ s.dict_slots.val) (hLP : simLP s)
    (hi : i.val < c.pb.objects.val.length) (hsl : (c.pb.objects.val[i.val]'hi).h.kind = .Slider)
    (hp : s3aPathOk c i.val) (hti : i.val < c.tail_idx.val.length)
    (htl : (c.tail_idx.val[i.val]'hti).val < (c.pb.objects.val[i.val]'hi).nested.val.length)
    (hST : s7StrictOk tn c i.val) :
    ∃ res s', sim.step.update_slider c s i = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.updateSlider i.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ s7Fr s s' ∧ simLP s') := by
  have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
  have hkl : (s.objs.val[i.val]'ho).inst.val < s.insts.val.length := (hI.ik.old hD ho).1
  rw [s7_us_eq, s7_updSlider_eq]
  obtain ⟨r, hr, er⟩ := sim.step.slider_data_refines tn fo c i hi
  have er' := er (simStS tn s)
  cases r with
  | Err x =>
    have hs : (c.pb.objects.val[i.val]'hi).slider = none := by
      rcases Option.eq_none_or_eq_some (c.pb.objects.val[i.val]'hi).slider with h | ⟨sd', h⟩
      · exact h
      · exfalso; unfold sim.step.slider_data at hr; simp [vec_index_eq _ _ hi, h] at hr
    obtain ⟨er0, s', hR⟩ := s7_upd_err tn fo E _ n c hC hCS hlen s i e hI hD hi hST hs
    obtain ⟨m, hm⟩ := er'
    refine ⟨.Err er0, s', hR, ⟨m, ?_⟩, fun h => by cases h⟩
    unfold s7UpdSlider
    simp only [simM_bind, s3a_topObj tn fo c _ i.val hi, Except.bind, OsuModel.Sim.Sim.st, simM_get, hm]
  | Ok sd =>
  have hsd : sim.step.slider_data c i = ok (.Ok sd) := hr
  simp only [s3aR] at er'
  have hR : ∀ (s2 : sim.state.St), SimARInv tn fo P (b0 + (n + n + 4)) n c s2 e 0 0 → simLP s2 → s7Fr s s2 →
      ∀ gto : (sim.playable.TopObj → Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St)) →
        Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St),
      (∀ K, gto K = K (c.pb.objects.val[i.val]'hi)) → ∀ tr,
      (∀ h : i.val < s2.objs.val.length, (s2.objs.val[i.val]'h).tracking = tr) →
      ∃ res s', s7RRest c s2 i (s.objs.val[i.val]'ho).inst s.t tr gto = ok (res, s') ∧
        simRelM tn s' res (s7Rest i.val (topS tn (c.pb.objects.val[i.val]'hi)) s.t (abs sd)
          (s.objs.val[i.val]'ho).inst.val (simCtxS tn fo c) (simStS tn s2)) ∧
        (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ s7Fr s s' ∧ simLP s') := by
    intro s2 hI2 hL2 hF2 gto hg tr htr
    obtain ⟨res, s', e1, r1, i1⟩ := s7_rest h64 tn fo E hU b0 n c hC hCS hlen s2 i _ e s.t sd tr hI2 (by rw [sim_keepS_dict hF2.keep]; exact hD) hL2 hi hsl
      (fun h => (s7Fr_inst hF2 i.val ho h).1) htr hsd hp hti htl gto hg
    exact ⟨res, s', e1, r1, fun h => let ⟨a, b, d⟩ := i1 h; ⟨a, s7Fr_trans hF2 b, d⟩⟩
  have hgI : ∀ K : sim.playable.TopObj → Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St),
      (do let «to» ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.playable.TopObj) c.pb.objects i
          K «to») = K (c.pb.objects.val[i.val]'hi) := fun K => by simp only [vec_index_eq _ _ hi, bind_ok]
  have hinS : (ostateS (s.objs.val[i.val]'ho)).inst = (s.objs.val[i.val]'ho).inst.val := rfl
  have htrS : (ostateS (s.objs.val[i.val]'ho)).tracking = (s.objs.val[i.val]'ho).tracking := rfl
  have hdtS : (abs (s.insts.val[(s.objs.val[i.val]'ho).inst.val]'hkl) : OsuModel.Sim.Inst).drawableTracking =
      (s.insts.val[(s.objs.val[i.val]'ho).inst.val]'hkl).drawable_tracking := rfl
  have htS : (simStS tn s).t = s.t := rfl
  have eI := s3a_instOf tn fo c s _ hkl
  unfold s7RUpd s7UpdSlider
  simp only [vec_index_eq _ _ ho, vec_index_eq _ _ hkl, bind_ok, simM_bind, s3a_topObj tn fo c _ i.val hi,
    Except.bind, OsuModel.Sim.Sim.st, simM_get, er', s3a_ostate tn fo c s _ ho, hinS, eI, htrS, hdtS, htS]
  generalize htrv : (s.objs.val[i.val]'ho).tracking = trv at *
  by_cases hdt : (trv != (s.insts.val[(s.objs.val[i.val]'ho).inst.val]'hkl).drawable_tracking) = true
  swap
  · simp only [hdt, if_false]
    exact hR s hI hLP (s7Fr_refl s) _ hgI trv (fun _ => htrv)
  simp only [hdt, if_true, vec_index_mut_eq _ _ hkl, uncurry_apply_pair, bind_ok]
  have hmD := s7_modInst tn (simCtxS tn fo c) s (s.objs.val[i.val]'ho).inst hkl
    { s.insts.val[(s.objs.val[i.val]'ho).inst.val]'hkl with drawable_tracking := trv }
    (fun ins => { ins with drawableTracking := trv }) rfl
  have hID := s7_inv_inst tn fo P _ n c s e hI _ hkl
    { s.insts.val[(s.objs.val[i.val]'ho).inst.val]'hkl with drawable_tracking := trv } rfl rfl
  have hFD := s7Fr_insts s (s.insts.set (s.objs.val[i.val]'ho).inst
    { s.insts.val[(s.objs.val[i.val]'ho).inst.val]'hkl with drawable_tracking := trv }) (s7_set_len _ _ _)
  have hLD := s7_lp_insts hLP (s.insts.set (s.objs.val[i.val]'ho).inst
    { s.insts.val[(s.objs.val[i.val]'ho).inst.val]'hkl with drawable_tracking := trv })
  simp only [simM_bind, hmD, OsuModel.Sim.Sim.ctx, simM_read, simM_read_bind, Except.bind]
  have hsS : (simCtxS tn fo c).cfg.strictTracking = c.cfg.strict_tracking := rfl
  have hnS := s7_isNone (s.objs.val[i.val]'ho)
  have hstS : (topS tn (c.pb.objects.val[i.val]'hi)).h.start = (c.pb.objects.val[i.val]'hi).h.start := rfl
  simp only [hsS, hnS, hstS]
  by_cases hst : c.cfg.strict_tracking = true
  swap
  · simp only [hst, if_false, Bool.false_and, Bool.false_eq_true]
    exact hR _ hID hLD hFD _ hgI trv (fun _ => htrv)
  simp only [hst, if_true, Bool.true_and]
  cases trv with
  | true =>
    simp only [if_true, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]
    exact hR _ hID hLD hFD _ hgI true (fun _ => htrv)
  | false =>
  simp only [Bool.false_eq_true, if_false, Bool.not_false, Bool.true_and]
  by_cases hun : core.option.Option.is_none (s.objs.val[i.val]'ho).result = true
  swap
  · simp only [hun, if_false, Bool.false_and, Bool.false_eq_true]
    exact hR _ hID hLD hFD _ hgI false (fun _ => htrv)
  simp only [hun, if_true, Bool.true_and, vec_index_eq _ _ hi, bind_ok, float.F64.lt]
  by_cases hb : s.t < (c.pb.objects.val[i.val]'hi).h.start
  · simp only [hb, decide_true, if_true, Bool.not_true, Bool.false_eq_true, if_false]
    exact hR _ hID hLD hFD _ (fun K => rfl) false (fun _ => htrv)
  simp only [hb, decide_false, Bool.false_eq_true, if_false, Bool.not_false, if_true]
  obtain ⟨r1, s1, e1, rr1, i1⟩ := sim.step.strict_tracking_miss_refines tn fo E _ n c hC hCS hlen _ i e hID (hID.ik i hD) hi hST
  rw [e1]; simp only [bind_ok, uncurry_apply_pair]
  have hsz : (topS tn (c.pb.objects.val[i.val]'hi)).nested.size = (c.pb.objects.val[i.val]'hi).nested.val.length := by
    simp [topS]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.div_one, Nat.sub_zero,
    Nat.add_sub_cancel, hsz, simM_bind]
  cases r1 with
  | Err er =>
    obtain ⟨m, hm⟩ := rr1
    refine ⟨.Err er, s1, ?_, ⟨m, ?_⟩, fun h => by cases h⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, s7_resid_simp]
    · simp only [hm, Except.bind]
  | Ok u =>
  simp only [simRelM] at rr1
  obtain ⟨hI1, hA1⟩ := i1 rfl
  have ho1 : i.val < s1.objs.val.length := by rw [hA1.len]; exact ho
  simp only [rr1, Except.bind, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, vec_index_eq _ _ ho1]
  exact hR s1 hI1 (simLP_fr hLD hA1) (s7Fr_trans hFD (s7Fr_of_ar hA1)) _ (fun K => rfl) _ (fun _ => rfl)

end OsuProofs
