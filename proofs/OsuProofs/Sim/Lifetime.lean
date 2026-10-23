/-
sim8: the lifetime chain (`became_dead`, `lifetime_first_update`, `lifetime_future_update`, `lifetime_update`) against
`OsuModel.Sim.Sim.becameDead` / `lifetimeUpdate`. Split lemmas copy the generated / spec tails verbatim (`s8_bd_split`,
`s8_bd_splitS`); the tick-return loop is `s8_bdl_loop`; `s8_enum` rebuilds SimARInv.enum from a duplicate-free dictionary.
-/
import OsuProofs.Sim.BecameAlive
import OsuProofs.Sim.OnKilled
import OsuProofs.Sim5.S5_Sort
import OsuProofs.Sim3.SC_Misc
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s8_poolOk_return (s : sim.state.St) (pk k : Usize) (s' : sim.state.St) (hP : simPoolOk s)
    (hpk : pk.val < s.pools.val.length) (h6 : pk.val < 6)
    (hk : k.val < s.insts.val.length) (h : sim.step.pool_return s pk k = ok s') : simPoolOk s' := by
  obtain ⟨m, hm, -, -⟩ := s3b_pool_max pk h6
  unfold sim.step.pool_return at h
  rw [vec_index_eq _ _ hpk] at h
  simp only [bind_ok, hm] at h
  split at h
  · rename_i hlt
    rw [vec_index_mut_eq _ _ hpk] at h
    simp only [bind_ok, uncurry_apply_pair] at h
    have hl : (s.pools.val[pk.val]'hpk).val.length < Usize.max := by
      have h1 : (s.pools.val[pk.val]'hpk).val.length < m.val := by
        have h3 : ((s.pools.val[pk.val]'hpk).len).val < m.val := hlt
        simpa using h3
      have h2 : m.val ≤ Usize.max := by scalar_tac
      omega
    rw [vec_push_ok _ _ hl] at h
    simp only [bind_ok, ok.injEq] at h
    subst h
    intro p hp j hj
    rw [vec_set_val'] at hp
    rcases List.mem_or_eq_of_mem_set hp with hp | hp
    · exact hP p hp j hj
    · subst hp
      simp at hj
      rcases hj with hj | hj
      · exact hP _ (List.getElem_mem hpk) j hj
      · subst hj; exact hk
  · simp only [ok.injEq] at h; subst h; exact hP

/-- the field tuple that `became_dead_loop` returns -/
def s8T (s : sim.state.St) := (s.k, s.t, s.objs, s.first_lifetime_update, s.next_future,
      s.future_order, s.active, s.dict_slots, s.free_list, s.child_counter,
      s.mouse_valid, s.mouse, s.last_replay, s.pressed, s.score, s.health,
      s.score_rp, s.health_rp, s.out, s.speed, s.as_target, s.as_recent,
      s.as_seen, s.clock_rate, s.relax_down, s.relax_was_left, s.relax_last,
      s.ap_frame, s.block_last, s.block_idx, s.insts, s.pools, s.br_rot,
      s.theta, s.cursor_pos)

/-- becameDead's tick-instance return loop body (membership proof dropped) -/
def s8BDG (o : OsuModel.Sim.TopObj) (T : Array Nat) (j : Nat) (_ : PUnit) : OsuModel.Sim.SimM (ForInStep PUnit) := do
  let x ← OsuModel.Sim.Sim.nestedOf o j
  OsuModel.Sim.Sim.poolReturn (if (x.kind == OsuModel.Sim.Kind.spinnerBonusTick) = true then 5 else 4) T[j]!
  pure (ForInStep.yield PUnit.unit)

theorem s8_bdl_loop (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (i : Usize)
    (hi : i.val < c.pb.objects.val.length)
    (TI : alloc.vec.Vec Usize) (hTI : TI.val.length ≤ (c.pb.objects.val[i.val]'hi).nested.val.length) :
    ∀ m (j : Usize) (s : sim.state.St), TI.val.length - j.val = m → j.val ≤ TI.val.length →
      (∃ hio : i.val < s.objs.val.length, (s.objs.val[i.val]'hio).tick_insts = TI) →
      6 ≤ s.pools.val.length → (∀ x ∈ TI.val, x.val < s.insts.val.length) → simPoolOk s →
      ∃ s', sim.step.became_dead_loop c.pb.objects s i j = ok (s8T s') ∧
        forIn (m := OsuModel.Sim.SimM) (List.range' j.val m) PUnit.unit
          (s8BDG (topS tn (c.pb.objects.val[i.val]'hi)) (simTisS TI))
          (simCtxS tn fo c) (simStS tn s) = .ok (PUnit.unit, simStS tn s') ∧
        (∃ pl, s' = { s with pools := pl }) ∧ s'.pools.val.length = s.pools.val.length ∧ simPoolOk s' := by
  intro m
  induction m with
  | zero =>
    intro j s hm hj ⟨ho, hti⟩ hpl htk hP
    have hge : ¬ j < alloc.vec.Vec.len (s.objs.val[i.val]'ho).tick_insts := by rw [vec_lt_len_iff, hti]; omega
    refine ⟨s, ?_, by simp, ⟨_, rfl⟩, rfl, hP⟩
    unfold sim.step.became_dead_loop
    rw [loop_unfold]
    have hge' : ¬ j.val < (s.objs.val[i.val]'ho).tick_insts.val.length := by rw [hti]; omega
    simp [sim.step.became_dead_loop.body, vec_index_eq _ _ ho, hge', s8T]
  | succ m ih =>
    intro j s hm hj ⟨ho, hti⟩ hpl htk hP
    have hjT : j.val < TI.val.length := by omega
    have hjl : j.val < (c.pb.objects.val[i.val]'hi).nested.val.length := by omega
    have hlt : j < alloc.vec.Vec.len (s.objs.val[i.val]'ho).tick_insts := by rw [vec_lt_len_iff, hti]; exact hjT
    have htj : j.val < (s.objs.val[i.val]'ho).tick_insts.val.length := by rw [hti]; exact hjT
    have hnp := TI.property
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by omega)
    have hn : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.playable.HObj)
      (c.pb.objects.val[i.val]'hi).nested j = ok ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl) :=
      vec_index_eq _ _ hjl
    generalize hhd : (c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl = hd at hn
    have enj : OsuModel.Sim.Sim.nestedOf (topS tn (c.pb.objects.val[i.val]'hi)) j.val (simCtxS tn fo c) (simStS tn s) =
        .ok (hobjS tn hd, simStS tn s) := by
      rw [← hhd]; simp [OsuModel.Sim.Sim.nestedOf, OsuModel.Sim.Sim.getA, topS, hjl]
    have hpkS : ∀ b : Bool, (if b = true then (5 : Nat) else 4) = (if b = true then (5#usize : Usize) else 4#usize).val := by
      intro b; cases b <;> rfl
    set pk : Usize := if (kindS hd.kind == OsuModel.Sim.Kind.spinnerBonusTick) = true then 5#usize else 4#usize with hpk
    have hpk6' : pk.val ≤ 5 := by rw [hpk]; split <;> decide
    have hpk6 : pk.val < s.pools.val.length := by omega
    have htv : (s.objs.val[i.val]'ho).tick_insts.val[j.val]'htj = TI.val[j.val]'hjT := by simp [hti]
    have hkx : (TI.val[j.val]'hjT).val < s.insts.val.length := htk _ (List.getElem_mem _)
    obtain ⟨s1, epr, rpr, ⟨pl1, hs1⟩, hpl1⟩ := sim.step.pool_return_refines tn fo c s pk (TI.val[j.val]'hjT) hpk6 (by omega)
    have hP1 : simPoolOk s1 := s8_poolOk_return s pk _ s1 hP hpk6 (by omega) hkx epr
    have hb : sim.step.became_dead_loop.body c.pb.objects i s j = ok (.cont (s1, j1)) := by
      simp only [sim.step.became_dead_loop.body, vec_index_eq _ _ ho, bind_ok, hlt, ite_true, vec_index_eq _ _ hi, hn,
        kind_eq_ok]
      have : (kindS sim.playable.Kind.SpinnerBonusTick) = OsuModel.Sim.Kind.spinnerBonusTick := rfl
      simp only [this]
      rw [show (if (kindS hd.kind == OsuModel.Sim.Kind.spinnerBonusTick) = true then ok 5#usize else ok 4#usize : Result Usize) = ok pk by
        rw [hpk]; split <;> rfl]
      simp only [bind_ok, vec_index_eq _ _ htj, htv, epr, hj1]
    have hstep : sim.step.became_dead_loop c.pb.objects s i j = sim.step.became_dead_loop c.pb.objects s1 i j1 := by
      unfold sim.step.became_dead_loop
      rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]
    have ho1 : i.val < s1.objs.val.length := by rw [hs1]; exact ho
    obtain ⟨s', e', r', ⟨pl', hs'⟩, l', P'⟩ := ih j1 s1 (by omega) (by omega) ⟨ho1, by simp only [hs1]; exact hti⟩
      (by rw [hpl1]; exact hpl) (by rw [hs1]; exact htk) hP1
    refine ⟨s', by rw [hstep]; exact e', ?_, ⟨pl', by rw [hs', hs1]⟩, by rw [l', hpl1], P'⟩
    rw [List.range'_succ, List.forIn_cons]
    simp only [s8BDG, simM_bind, enj, Except.bind]
    have hkS : (hobjS tn hd).kind = kindS hd.kind := rfl
    have hTj : (simTisS TI)[j.val]! = (TI.val[j.val]'hjT).val := by simp [simTisS, hjT]
    rw [hkS, hpkS, ← hpk, hTj, rpr]
    simp only [simM_pure, Except.bind]
    rw [show j.val + 1 = j1.val from hj1v.symm]
    exact r'


/-- `became_dead` after `on_killed` succeeded (verbatim copy of the generated body) -/
def s8BDTailR (c : sim.state.Ctx) (s1 : sim.state.St) (i : Std.Usize) :
    Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St) := do
  let «to» ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      sim.playable.TopObj) c.pb.objects i
  let b ←
    sim.playable.Kind.Insts.CoreCmpPartialEqKind.eq «to».h.kind
      sim.playable.Kind.Slider
  let s2 ←
    if b
    then
      do
      let o2 ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          sim.state.OState) s1.objs i
      let (i1, index_mut_back2) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
          sim.state.Inst) s1.insts o2.head_inst
      let t ← sim.transforms.clear_state i1.tf
      let v3 := index_mut_back2 { i1 with tf := t }
      let (i2, index_mut_back3) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
          sim.state.Inst) v3 o2.head_inst
      let v4 := index_mut_back3 { i2 with armed := o2.head_armed }
      sim.step.pool_return { s1 with insts := v4 } 2#usize o2.head_inst
    else ok s1
  let b1 ←
    sim.playable.Kind.Insts.CoreCmpPartialEqKind.eq «to».h.kind
      sim.playable.Kind.Spinner
  if b1
  then
    let (i1, f, v3, b2, i2, v4, v5, v6, v7, i3, b3, v8, o2, al, ss, hs,
      ss1, hs1, v9, v10, v11, v12, v13, f1, b4, b5, f2, i4, v14, v15, v16,
      v17, f3, f4, v18) ←
      sim.step.became_dead_loop c.pb.objects s2 i 0#usize
    let o3 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        sim.state.OState) v3 i
    let (i5, index_mut_back2) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
        sim.state.Inst) v16 o3.inst
    let t ← sim.transforms.clear_state i5.tf
    let v19 := index_mut_back2 { i5 with tf := t }
    let (i6, index_mut_back3) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
        sim.state.Inst) v19 o3.inst
    let t1 ← sim.transforms.clear_state i6.body_tf
    let v20 := index_mut_back3 { i6 with body_tf := t1 }
    let (i7, index_mut_back4) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
        sim.state.Inst) v20 o3.inst
    let v21 := index_mut_back4 { i7 with armed := o3.armed }
    let i8 ← sim.step.pool_kind «to».h.kind
    let s3 ←
      sim.step.pool_return
        {
          k := i1,
          t := f,
          objs := v3,
          first_lifetime_update := b2,
          next_future := i2,
          future_order := v4,
          active := v5,
          dict_slots := v6,
          free_list := v7,
          child_counter := i3,
          mouse_valid := b3,
          mouse := v8,
          last_replay := o2,
          pressed := al,
          score := ss,
          health := hs,
          score_rp := ss1,
          health_rp := hs1,
          out := v9,
          speed := v10,
          as_target := v11,
          as_recent := v12,
          as_seen := v13,
          clock_rate := f1,
          relax_down := b4,
          relax_was_left := b5,
          relax_last := f2,
          ap_frame := i4,
          block_last := v14,
          block_idx := v15,
          insts := v21,
          pools := v17,
          br_rot := f3,
          theta := f4,
          cursor_pos := v18
        } i8 o3.inst
    ok (core.result.Result.Ok (), s3)
  else
    let o2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        sim.state.OState) s2.objs i
    let (i1, index_mut_back2) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
        sim.state.Inst) s2.insts o2.inst
    let t ← sim.transforms.clear_state i1.tf
    let v3 := index_mut_back2 { i1 with tf := t }
    let (i2, index_mut_back3) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
        sim.state.Inst) v3 o2.inst
    let t1 ← sim.transforms.clear_state i2.body_tf
    let v4 := index_mut_back3 { i2 with body_tf := t1 }
    let (i3, index_mut_back4) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
        sim.state.Inst) v4 o2.inst
    let v5 := index_mut_back4 { i3 with armed := o2.armed }
    let i4 ← sim.step.pool_kind «to».h.kind
    let s3 ← sim.step.pool_return { s2 with insts := v5 } i4 o2.inst
    ok (core.result.Result.Ok (), s3)

theorem s8_bd_split (c s i) : sim.step.became_dead c s i = (do
  let o ← sim.step.dict_slot_of s i
  match o with
  | none =>
    ok (core.result.Result.Err (sim.err.SimErr.Internal
      (sim.err.Internal.DeadNotAlive i)), s)
  | some slot =>
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice (Option
        Std.Usize)) s.dict_slots slot
    let v ← alloc.vec.Vec.push s.free_list slot
    let (o1, index_mut_back1) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
        sim.state.OState) s.objs i
    let v1 := index_mut_back1 { o1 with life := sim.state.Life.Past }
    let v2 := index_mut_back none
    let (r, s1) ←
      sim.step.on_killed c
        { s with objs := v1, dict_slots := v2, free_list := v } i
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ => s8BDTailR c s1 i
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame sim.err.SimErr) residual
      ok (r1, s1)) := rfl

open OsuModel.Net OsuModel.Replay OsuModel.Sim OsuModel.Sim.Sim in
/-- the part of `becameDead` after `onKilled` (verbatim copy of the spec body) -/
def s8BDTailS (i : Nat) : OsuModel.Sim.SimM Unit := do
  let o ← topObj i
  let os ← ostate i
  if o.h.kind == .slider then
    modifyInst os.headInst fun ins => { ins with tf := clearState ins.tf, armed := os.headArmed }
    poolReturn 2 os.headInst
  if o.h.kind == .spinner then
    for h : j in [0:os.tickInsts.size] do
      poolReturn (if (← nestedOf o j).kind == .spinnerBonusTick then 5 else 4) (os.tickInsts[j]'h.upper)
  modifyInst os.inst fun ins => { ins with tf := clearState ins.tf, bodyTf := clearState ins.bodyTf, armed := os.armed }
  poolReturn (poolKind o.h.kind) os.inst

open OsuModel.Net OsuModel.Replay OsuModel.Sim OsuModel.Sim.Sim in
theorem s8_bd_splitS (i : Nat) : OsuModel.Sim.Sim.becameDead i = (do
  let s ← st
  match s.dictSlots.idxOf? (some i) with
  | some slot => set { s with dictSlots := ← setA s.dictSlots slot none "dictionary entries", freeList := slot :: s.freeList }
  | none => throw s!"internal: dead object {i} not in the alive dictionary"
  modifyObj i fun os => { os with life := .past }
  onKilled i
  s8BDTailS i) := rfl

theorem s8_modifyInst_stS (tn) (C : OsuModel.Sim.Ctx) (s : sim.state.St) (k : Usize) (h : k.val < s.insts.val.length)
    (Y : sim.state.Inst) (f : OsuModel.Sim.Inst → OsuModel.Sim.Inst)
    (hf : f (abs (s.insts.val[k.val]'h)) = abs Y) (j : Nat) (hj : j = k.val) :
    OsuModel.Sim.Sim.modifyInst j f C (simStS tn s) = .ok ((), simStS tn { s with insts := s.insts.set k Y }) := by
  subst hj
  rw [s3b_modifyInst_ok _ _ _ _ (by simpa [simStS, abs] using h)]
  have e : (simStS tn s).insts.modify k.val f = (simStS tn { s with insts := s.insts.set k Y }).insts := by
    show (s.insts.val.map (fun x => (abs x : OsuModel.Sim.Inst))).toArray.modify k.val f =
      ((s.insts.set k Y).val.map (fun x => (abs x : OsuModel.Sim.Inst))).toArray
    rw [s3b_arr_modify_toArray _ _ _ h, hf]
    simp [vec_set_val', List.map_set]
  rw [e]; rfl

theorem s8_tf_set {P : Nat → sim.transforms.TObj → Prop} {B : Nat} {s : sim.state.St} {k : Usize}
    (h : s3b_TfInv P B s) (Y : sim.state.Inst) (h1 : P B Y.tf) (h2 : P B Y.body_tf) :
    s3b_TfInv P B { s with insts := s.insts.set k Y } := by
  intro ins hm
  simp only [vec_set_val'] at hm
  rcases List.mem_or_eq_of_mem_set hm with hm | hm
  · exact h ins hm
  · subst hm; exact ⟨h1, h2⟩

theorem s8_poolOk_insts {s : sim.state.St} (h : simPoolOk s) (ins : alloc.vec.Vec sim.state.Inst)
    (hl : s.insts.val.length ≤ ins.val.length) : simPoolOk { s with insts := ins } :=
  fun p hp j hj => Nat.lt_of_lt_of_le (h p hp j hj) hl

theorem s8_bd_fin (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (B : Nat) (c : sim.state.Ctx) (sF : sim.state.St) (i : Usize)
    (hi : i.val < c.pb.objects.val.length) (O : sim.state.OState)
    (hkF : O.inst.val < sF.insts.val.length)
    (hTfF : s3b_TfInv P B sF) (hplF : 6 ≤ sF.pools.val.length) (hPF : simPoolOk sF) :
    ∃ s', (do
      let (i1, index_mut_back2) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice sim.state.Inst) sF.insts O.inst
      let t ← sim.transforms.clear_state i1.tf
      let v3 := index_mut_back2 { i1 with tf := t }
      let (i2, index_mut_back3) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice sim.state.Inst) v3 O.inst
      let t1 ← sim.transforms.clear_state i2.body_tf
      let v4 := index_mut_back3 { i2 with body_tf := t1 }
      let (i3, index_mut_back4) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice sim.state.Inst) v4 O.inst
      let v5 := index_mut_back4 { i3 with armed := O.armed }
      let i4 ← sim.step.pool_kind (c.pb.objects.val[i.val]'hi).h.kind
      let s3 ← sim.step.pool_return { sF with insts := v5 } i4 O.inst
      ok (core.result.Result.Ok (), s3) : Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St)) = ok (.Ok (), s') ∧
    (do
      OsuModel.Sim.Sim.modifyInst (ostateS O).inst fun ins =>
        { ins with tf := OsuModel.Sim.clearState ins.tf, bodyTf := OsuModel.Sim.clearState ins.bodyTf,
                   armed := (ostateS O).armed }
      OsuModel.Sim.Sim.poolReturn (OsuModel.Sim.Sim.poolKind (kindS (c.pb.objects.val[i.val]'hi).h.kind))
        (ostateS O).inst : OsuModel.Sim.SimM Unit) (simCtxS tn fo c) (simStS tn sF) =
      .ok ((), simStS tn s') ∧
    (∃ ins pl, s' = { sF with insts := ins, pools := pl }) ∧ s'.insts.val.length = sF.insts.val.length ∧
    s3b_TfInv P B s' ∧ s'.pools.val.length = sF.pools.val.length ∧ simPoolOk s' := by
  obtain ⟨tF, etF, ctF, PtF⟩ := E.clear B _ (hTfF _ (List.getElem_mem hkF)).1
  obtain ⟨tF1, etF1, ctF1, PtF1⟩ := E.clear B _ (hTfF _ (List.getElem_mem hkF)).2
  set I0 := sF.insts.val[O.inst.val]'hkF with hI0
  set YF : sim.state.Inst := { I0 with tf := tF, body_tf := tF1, armed := O.armed } with hYF
  have hkF2 : O.inst.val < (sF.insts.set O.inst { I0 with tf := tF }).val.length := by
    simpa [vec_set_val'] using hkF
  have hkF3 : O.inst.val < ((sF.insts.set O.inst { I0 with tf := tF }).set O.inst { I0 with tf := tF, body_tf := tF1 }).val.length := by
    simpa [vec_set_val'] using hkF
  obtain ⟨pkF, epkF, spkF⟩ := sim.step.pool_kind_refines (c.pb.objects.val[i.val]'hi).h.kind
  have hpkF : pkF.val < 6 := by
    cases hkd : (c.pb.objects.val[i.val]'hi).h.kind <;> rw [hkd] at epkF <;>
      simp [sim.step.pool_kind] at epkF <;> subst epkF <;> decide
  have hpkS : OsuModel.Sim.Sim.poolKind (kindS (c.pb.objects.val[i.val]'hi).h.kind) = pkF.val := by
    first | exact spkF | simpa [abs] using spkF
  obtain ⟨sF', eprF, rprF, ⟨plF, hsF'⟩, hplF'⟩ := sim.step.pool_return_refines tn fo c
    { sF with insts := sF.insts.set O.inst YF } pkF O.inst (by simp; omega) hpkF
  have hlen : (sF.insts.set O.inst YF).val.length = sF.insts.val.length := by simp [vec_set_val']
  have hP1 : simPoolOk { sF with insts := sF.insts.set O.inst YF } := s8_poolOk_insts hPF _ (by rw [hlen])
  refine ⟨sF', ?_, ?_, ⟨_, plF, by rw [hsF']⟩, by rw [hsF']; exact hlen, ?_, by rw [hplF'], ?_⟩
  · rw [vec_index_mut_eq _ _ hkF]
    simp only [bind_ok, uncurry_apply_pair, ← hI0, etF]
    rw [vec_index_mut_eq _ _ hkF2]
    simp only [bind_ok, uncurry_apply_pair, vec_set_val', List.getElem_set_self]
    rw [etF1]
    simp only [bind_ok, sim_vset_set]
    rw [vec_index_mut_eq _ _ (by simpa [vec_set_val'] using hkF)]
    simp only [bind_ok, uncurry_apply_pair, vec_set_val', List.getElem_set_self, sim_vset_set, epkF]
    first | (erw [eprF]) | (simp only [hYF] at eprF; rw [eprF])
    simp only [bind_ok]
  · simp only [simM_bind]
    rw [s8_modifyInst_stS tn (simCtxS tn fo c) sF O.inst hkF YF _ ?hf (ostateS O).inst rfl]
    · simp only [Except.bind, hpkS]
      exact rprF
    case hf =>
      show ({ (abs I0 : OsuModel.Sim.Inst) with tf := OsuModel.Sim.clearState (abs I0.tf), bodyTf := OsuModel.Sim.clearState (abs I0.body_tf), armed := armedS O.armed } : OsuModel.Sim.Inst) = abs YF
      rw [ctF, ctF1]; rfl
  · rw [hsF']; exact s8_tf_set hTfF YF PtF PtF1
  · exact s8_poolOk_return _ pkF O.inst sF' hP1 (by simp; omega) hpkF (by rw [hlen]; exact hkF) eprF

theorem s8_bd_fin2 (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (B : Nat) (c : sim.state.Ctx) (sF : sim.state.St) (i : Usize)
    (hi : i.val < c.pb.objects.val.length) (hoF : i.val < sF.objs.val.length)
    (hkF : (sF.objs.val[i.val]'hoF).inst.val < sF.insts.val.length)
    (hTfF : s3b_TfInv P B sF) (hplF : 6 ≤ sF.pools.val.length) (hPF : simPoolOk sF) :
    ∃ s', (do
      let o3 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.state.OState) sF.objs i
      let (i1, index_mut_back2) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice sim.state.Inst) sF.insts o3.inst
      let t ← sim.transforms.clear_state i1.tf
      let v3 := index_mut_back2 { i1 with tf := t }
      let (i2, index_mut_back3) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice sim.state.Inst) v3 o3.inst
      let t1 ← sim.transforms.clear_state i2.body_tf
      let v4 := index_mut_back3 { i2 with body_tf := t1 }
      let (i3, index_mut_back4) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice sim.state.Inst) v4 o3.inst
      let v5 := index_mut_back4 { i3 with armed := o3.armed }
      let i4 ← sim.step.pool_kind (c.pb.objects.val[i.val]'hi).h.kind
      let s3 ← sim.step.pool_return { sF with insts := v5 } i4 o3.inst
      ok (core.result.Result.Ok (), s3) : Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St)) = ok (.Ok (), s') ∧
    (do
      OsuModel.Sim.Sim.modifyInst (ostateS (sF.objs.val[i.val]'hoF)).inst fun ins =>
        { ins with tf := OsuModel.Sim.clearState ins.tf, bodyTf := OsuModel.Sim.clearState ins.bodyTf,
                   armed := (ostateS (sF.objs.val[i.val]'hoF)).armed }
      OsuModel.Sim.Sim.poolReturn (OsuModel.Sim.Sim.poolKind (kindS (c.pb.objects.val[i.val]'hi).h.kind))
        (ostateS (sF.objs.val[i.val]'hoF)).inst : OsuModel.Sim.SimM Unit) (simCtxS tn fo c) (simStS tn sF) =
      .ok ((), simStS tn s') ∧
    (∃ ins pl, s' = { sF with insts := ins, pools := pl }) ∧ s'.insts.val.length = sF.insts.val.length ∧
    s3b_TfInv P B s' ∧ s'.pools.val.length = sF.pools.val.length ∧ simPoolOk s' := by
  obtain ⟨s', f1, f2, f3, f4, f5, f6, f7⟩ := s8_bd_fin tn fo E B c sF i hi _ hkF hTfF hplF hPF
  refine ⟨s', ?_, f2, f3, f4, f5, f6, f7⟩
  rw [vec_index_eq _ _ hoF]
  simp only [bind_ok]
  exact f1

theorem s8_bd_hd (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (B : Nat) (c : sim.state.Ctx) (sF : sim.state.St) (O : sim.state.OState)
    (hkF : O.head_inst.val < sF.insts.val.length)
    (hTfF : s3b_TfInv P B sF) (hplF : 6 ≤ sF.pools.val.length) (hPF : simPoolOk sF) :
    ∃ s', (do
      let (i1, index_mut_back2) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice sim.state.Inst) sF.insts O.head_inst
      let t ← sim.transforms.clear_state i1.tf
      let v3 := index_mut_back2 { i1 with tf := t }
      let (i2, index_mut_back3) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice sim.state.Inst) v3 O.head_inst
      let v4 := index_mut_back3 { i2 with armed := O.head_armed }
      sim.step.pool_return { sF with insts := v4 } 2#usize O.head_inst : Result sim.state.St) = ok s' ∧
    (∀ K : OsuModel.Sim.SimM Unit, (do
      OsuModel.Sim.Sim.modifyInst (ostateS O).headInst fun ins =>
        { ins with tf := OsuModel.Sim.clearState ins.tf, armed := (ostateS O).headArmed }
      OsuModel.Sim.Sim.poolReturn 2 (ostateS O).headInst
      K : OsuModel.Sim.SimM Unit) (simCtxS tn fo c) (simStS tn sF) = K (simCtxS tn fo c) (simStS tn s')) ∧
    (∃ ins pl, s' = { sF with insts := ins, pools := pl }) ∧ s'.insts.val.length = sF.insts.val.length ∧
    s3b_TfInv P B s' ∧ s'.pools.val.length = sF.pools.val.length ∧ simPoolOk s' := by
  obtain ⟨tF, etF, ctF, PtF⟩ := E.clear B _ (hTfF _ (List.getElem_mem hkF)).1
  set I0 := sF.insts.val[O.head_inst.val]'hkF with hI0
  set YF : sim.state.Inst := { I0 with tf := tF, armed := O.head_armed } with hYF
  have hkF2 : O.head_inst.val < (sF.insts.set O.head_inst { I0 with tf := tF }).val.length := by
    simpa [vec_set_val'] using hkF
  obtain ⟨sF', eprF, rprF, ⟨plF, hsF'⟩, hplF'⟩ := sim.step.pool_return_refines tn fo c
    { sF with insts := sF.insts.set O.head_inst YF } 2#usize O.head_inst (by simp; omega) (by decide)
  have hlen : (sF.insts.set O.head_inst YF).val.length = sF.insts.val.length := by simp [vec_set_val']
  have hP1 : simPoolOk { sF with insts := sF.insts.set O.head_inst YF } := s8_poolOk_insts hPF _ (by rw [hlen])
  refine ⟨sF', ?_, ?_, ⟨_, plF, by rw [hsF']⟩, by rw [hsF']; exact hlen, ?_, by rw [hplF'], ?_⟩
  · rw [vec_index_mut_eq _ _ hkF]
    simp only [bind_ok, uncurry_apply_pair, ← hI0, etF]
    rw [vec_index_mut_eq _ _ hkF2]
    simp only [bind_ok, uncurry_apply_pair, vec_set_val', List.getElem_set_self, sim_vset_set]
    first | (erw [eprF]) | (simp only [hYF] at eprF; rw [eprF])
  · intro K
    simp only [simM_bind]
    rw [s8_modifyInst_stS tn (simCtxS tn fo c) sF O.head_inst hkF YF _ ?hf (ostateS O).headInst rfl]
    · simp only [Except.bind]
      rw [show ((2#usize : Usize).val) = 2 from rfl] at rprF
      rw [show (ostateS O).headInst = O.head_inst.val from rfl, rprF]
    case hf =>
      show ({ (abs I0 : OsuModel.Sim.Inst) with tf := OsuModel.Sim.clearState (abs I0.tf), armed := armedS O.head_armed } : OsuModel.Sim.Inst) = abs YF
      rw [ctF]; rfl
  · rw [hsF']; exact s8_tf_set hTfF YF PtF (hTfF _ (List.getElem_mem hkF)).2
  · exact s8_poolOk_return _ 2#usize O.head_inst sF' hP1 (by simp; omega) (by decide) (by rw [hlen]; exact hkF) eprF

theorem s8_forIn'_congr {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} (L : List α) (init : β)
    (f : (a : α) → a ∈ L → β → m (ForInStep β)) (g : α → β → m (ForInStep β)) (hfg : ∀ a h b, f a h b = g a b) :
    forIn' L init f = forIn L init g := by
  induction L generalizing init with
  | nil => simp
  | cons x t ih =>
    rw [List.forIn'_cons, List.forIn_cons, hfg]
    congr 1; funext r
    cases r with
    | done b => rfl
    | yield b => exact ih b (fun a h' b => f a (List.mem_cons_of_mem _ h') b) (fun a h' b => hfg _ _ _)

theorem s8_bd_tail (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (B : Nat) (c : sim.state.Ctx) (s1 : sim.state.St) (i : Usize)
    (hi : i.val < c.pb.objects.val.length) (ho : i.val < s1.objs.val.length)
    (hTf : s3b_TfInv P B s1)
    (hik : (s1.objs.val[i.val]'ho).inst.val < s1.insts.val.length ∧
      (s1.objs.val[i.val]'ho).head_inst.val < s1.insts.val.length ∧
      ∀ j (hj : j < (s1.objs.val[i.val]'ho).tick_insts.val.length),
        ((s1.objs.val[i.val]'ho).tick_insts.val[j]'hj).val < s1.insts.val.length)
    (htk : (s1.objs.val[i.val]'ho).tick_insts.val.length ≤ (c.pb.objects.val[i.val]'hi).nested.val.length)
    (hpl : 6 ≤ s1.pools.val.length) (hP : simPoolOk s1) :
    ∃ s', s8BDTailR c s1 i = ok (.Ok (), s') ∧
      s8BDTailS i.val (simCtxS tn fo c) (simStS tn s1) = .ok ((), simStS tn s') ∧
      (∃ ins pl, s' = { s1 with insts := ins, pools := pl }) ∧ s'.insts.val.length = s1.insts.val.length ∧
      s3b_TfInv P B s' ∧ s'.pools.val.length = s1.pools.val.length ∧ simPoolOk s' := by
  unfold s8BDTailR s8BDTailS
  have hkS : (topS tn (c.pb.objects.val[i.val]'hi)).h.kind = kindS (c.pb.objects.val[i.val]'hi).h.kind := rfl
  simp only [simM_bind, s3b_topObj tn fo c _ i.val hi, Except.bind, vec_index_eq _ _ hi, bind_ok,
    s3a_ostate tn fo c s1 _ ho, kind_eq_ok, hkS]
  obtain ⟨hkI, hhI, htI⟩ := hik
  by_cases hsl : (c.pb.objects.val[i.val]'hi).h.kind = .Slider
  · have hb1 : (kindS (c.pb.objects.val[i.val]'hi).h.kind == OsuModel.Sim.Kind.slider) = true := by rw [hsl]; rfl
    have hb2 : (kindS (c.pb.objects.val[i.val]'hi).h.kind == OsuModel.Sim.Kind.spinner) = false := by rw [hsl]; rfl
    have hb1' : (kindS (c.pb.objects.val[i.val]'hi).h.kind == kindS sim.playable.Kind.Slider) = true := hb1
    have hb2' : (kindS (c.pb.objects.val[i.val]'hi).h.kind == kindS sim.playable.Kind.Spinner) = false := hb2
    simp only [hb1, hb2, hb1', hb2', Bool.false_eq_true, if_false, if_true, simM_pure, vec_index_eq _ _ ho]
    obtain ⟨s2, h1, h2, ⟨ins2, pl2, hs2⟩, h4, h5, h6, h7⟩ := s8_bd_hd tn fo E B c s1 _ hhI hTf hpl hP
    dsimp only at h1
    simp only [bind_ok]
    rw [h1]
    simp only [bind_ok]
    subst hs2
    simp only [vec_index_eq _ _ ho, bind_ok]
    obtain ⟨s', e1, e2, ⟨ins3, pl3, e3⟩, e4, e5, e6, e7⟩ := s8_bd_fin tn fo E B c { s1 with insts := ins2, pools := pl2 } i hi
      (s1.objs.val[i.val]'ho) (by simp only at h4 ⊢; omega) h5 (by simp only at h6 ⊢; omega) h7
    refine ⟨s', e1, ?_, ⟨ins3, pl3, by rw [e3]⟩, by rw [e4, h4], e5, by rw [e6, h6], e7⟩
    rw [h2]; exact e2
  by_cases hsp : (c.pb.objects.val[i.val]'hi).h.kind = .Spinner
  · have hb1 : (kindS (c.pb.objects.val[i.val]'hi).h.kind == OsuModel.Sim.Kind.slider) = false := by rw [hsp]; rfl
    have hb2 : (kindS (c.pb.objects.val[i.val]'hi).h.kind == OsuModel.Sim.Kind.spinner) = true := by rw [hsp]; rfl
    have hb1' : (kindS (c.pb.objects.val[i.val]'hi).h.kind == kindS sim.playable.Kind.Slider) = false := hb1
    have hb2' : (kindS (c.pb.objects.val[i.val]'hi).h.kind == kindS sim.playable.Kind.Spinner) = true := hb2
    simp only [hb1, hb2, hb1', hb2', Bool.false_eq_true, if_false, if_true, simM_pure, vec_index_eq _ _ ho, bind_ok]
    obtain ⟨s2, e1, e2, ⟨pl2, hs2⟩, h6, h7⟩ := s8_bdl_loop tn fo c i hi (s1.objs.val[i.val]'ho).tick_insts htk _ 0#usize s1
      rfl (by simp) ⟨ho, rfl⟩ hpl (fun x hx => by
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx; exact htI j hj) hP
    rw [e1]
    simp only [bind_ok, s8T]
    subst hs2
    obtain ⟨s', f1, f2, ⟨ins3, pl3, f3⟩, f4, f5, f6, f7⟩ := s8_bd_fin2 tn fo E B c { s1 with pools := pl2 } i hi
      ho hkI hTf (by simp only at h6 ⊢; omega) h7
    refine ⟨s', ?_, ?_, ⟨ins3, pl3, by rw [f3]⟩, f4, f5, by rw [f6, h6], f7⟩
    · exact f1
    simp only [simM_bind]
    rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
    simp only [Std.Legacy.Range.size, Nat.div_one, Nat.sub_zero, Nat.add_sub_cancel]
    rw [s8_forIn'_congr _ _ _ (s8BDG (topS tn (c.pb.objects.val[i.val]'hi)) (simTisS (s1.objs.val[i.val]'ho).tick_insts)) ?hg]
    · have e2' := e2
      simp only [show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero] at e2'
      rw [show (ostateS (s1.objs.val[i.val]'ho)).tickInsts.size = (s1.objs.val[i.val]'ho).tick_insts.val.length by
        simp [ostateS, abs], e2']
      simp only [Except.bind]
      exact f2
    case hg =>
      intro a ha b
      have ha2 := ha
      simp at ha2
      have ha' : a < (simTisS (s1.objs.val[i.val]'ho).tick_insts).size := by simp [simTisS]; simpa [ostateS, abs] using ha2
      simp only [s8BDG, getElem!_pos (simTisS (s1.objs.val[i.val]'ho).tick_insts) a ha']
      rfl
  have hb1 : (kindS (c.pb.objects.val[i.val]'hi).h.kind == OsuModel.Sim.Kind.slider) = false := by
    revert hsl; cases (c.pb.objects.val[i.val]'hi).h.kind <;> simp [kindS] <;> decide
  have hb2 : (kindS (c.pb.objects.val[i.val]'hi).h.kind == OsuModel.Sim.Kind.spinner) = false := by
    revert hsp; cases (c.pb.objects.val[i.val]'hi).h.kind <;> simp [kindS] <;> decide
  have hb1' : (kindS (c.pb.objects.val[i.val]'hi).h.kind == kindS sim.playable.Kind.Slider) = false := hb1
  have hb2' : (kindS (c.pb.objects.val[i.val]'hi).h.kind == kindS sim.playable.Kind.Spinner) = false := hb2
  simp only [hb1, hb2, hb1', hb2', Bool.false_eq_true, if_false, simM_pure, vec_index_eq _ _ ho]
  simp only [bind_ok, vec_index_eq _ _ ho]
  obtain ⟨s', e1, e2, e3, e4, e5, e6, e7⟩ := s8_bd_fin tn fo E B c s1 i hi _ hkI hTf hpl hP
  exact ⟨s', e1, e2, e3, e4, e5, e6, e7⟩


/-! ## enumerate_up_to capacity from a duplicate-free dictionary -/

theorem s8_sortL_perm {α} (lt : α → α → Bool) (l : List α) : (simSortL lt l).Perm l := by
  unfold simSortL
  suffices h : ∀ acc : List α, (l.foldl (fun out x => out.insertIdx (simInsPos lt out x out.length) x) acc).Perm (acc ++ l) by
    simpa using h []
  induction l with
  | nil => intro acc; simp
  | cons y t ih =>
    intro acc
    simp only [List.foldl_cons]
    refine (ih _).trans ?_
    have hp := sim_simInsPos_le lt acc y acc.length
    have h1 : (acc.insertIdx (simInsPos lt acc y acc.length) y).Perm (y :: acc) := List.perm_insertIdx y acc hp
    have h2 : (acc ++ y :: t).Perm ((y :: acc) ++ t) := by
      simpa using (List.perm_middle (a := y) (l₁ := acc) (l₂ := t))
    exact (h1.append_right t).trans h2.symm

theorem s8_enumL_len (objs : Array OsuModel.Sim.TopObj) (target : F64) (l : List Nat) :
    (simEnumL objs target l).length ≤ (l.map (fun i => 1 + (objs[i]!).nested.size)).sum := by
  induction l with
  | nil => simp [simEnumL]
  | cons i t ih =>
    simp only [simEnumL]
    split
    · simp only [List.length_cons, List.length_append, List.map_cons, List.sum_cons]
      have : (simNestedTW (objs[i]!) i target).length ≤ (objs[i]!).nested.size := by
        unfold simNestedTW
        have h1 := (List.takeWhile_sublist (fun j => decide (((objs[i]!).nested[j]!).start < target))).length_le.trans
          (le_of_eq (List.length_range (n := (objs[i]!).nested.size)))
        first | simpa using h1 | (simp [List.length_flatMap]; exact h1) | (rw [List.length_map]; exact h1)
      omega
    · simp

theorem s8_sum_nodup_le (f : Nat → Nat) (N : Nat) (l : List Nat) (hnd : l.Nodup) (hl : ∀ x ∈ l, x < N) :
    (l.map f).sum ≤ ((List.range N).map f).sum := by
  have hs : l.Subperm (List.range N) := hnd.subperm (fun x hx => List.mem_range.2 (hl x hx))
  obtain ⟨l', hp, hsub⟩ := hs
  rw [← hp.map f |>.sum_eq]
  exact (hsub.map f).sum_le_sum (fun _ _ => Nat.zero_le _)

theorem s8_sum_range_le (f : Nat → Nat) (N K : Nat) (hf : ∀ i < N, f i ≤ K) : ((List.range N).map f).sum ≤ N * K := by
  induction N with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    have := ih (fun i hi => hf i (by omega))
    have := hf m (by omega)
    simp; rw [Nat.succ_mul]; omega

theorem s8_enum (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St)
    (hinv : SimInv c s) (hND : ((s.dict_slots.val.filterMap id).map (·.val)).Nodup)
    (hos : c.pb.objects.val.length < 2 ^ 32) (hns : ∀ o ∈ c.pb.objects.val, o.nested.val.length < 2 ^ 32) :
    ∀ target v, OsuModel.Sim.Sim.enumerateUpTo target (simCtxS tn fo c) (simStS tn s) =
      .ok (v, simStS tn s) → v.size < Usize.max := by
  have hS : ∀ i ∈ ((simStS tn s).dictSlots.filterMap id), i < (simCtxS tn fo c).pb.objects.size := by
    intro i hi
    simp [simStS, abs] at hi
    obtain ⟨a, ha, hai⟩ := hi
    rw [← hai]; simpa using hinv.dict_in _ ha a rfl
  have hL : ((simStS tn s).dictSlots.filterMap id).toList = (s.dict_slots.val.filterMap id).map (·.val) := by
    simp [simStS, abs, List.filterMap_map]
    rw [List.map_filterMap]
  intro target v hv
  rw [simS_enumerateUpTo _ _ _ hS] at hv
  simp only [Except.ok.injEq, Prod.mk.injEq] at hv
  rw [← hv.1, List.size_toArray]
  refine Nat.lt_of_le_of_lt (s8_enumL_len _ target _) ?_
  rw [(s8_sortL_perm _ _).map _ |>.sum_eq, hL]
  have hN : (simCtxS tn fo c).pb.objects.size = c.pb.objects.val.length := by simp [simCtxS, playableS]
  refine Nat.lt_of_le_of_lt (s8_sum_nodup_le _ c.pb.objects.val.length _ hND ?_) ?_
  · intro x hx; rw [← hL] at hx; rw [← hN]; exact hS x (by simpa using hx)
  · refine Nat.lt_of_le_of_lt (s8_sum_range_le _ _ (2 ^ 32) ?_) ?_
    · intro j hj
      have : ((simCtxS tn fo c).pb.objects[j]!).nested.size = (c.pb.objects.val[j]'hj).nested.val.length := by
        simp [simCtxS, playableS, hj, topS]
        done
      have := hns _ (List.getElem_mem hj)
      omega
    · have : c.pb.objects.val.length * 2 ^ 32 < 2 ^ 64 - 1 := by
        have : c.pb.objects.val.length * 2 ^ 32 ≤ (2 ^ 32 - 1) * 2 ^ 32 := Nat.mul_le_mul_right _ (by omega)
        omega
      simpa [Usize.max, Usize.numBits, h64] using this


/-! ## became_dead -/

theorem s8_keepS {s s' : sim.state.St} (h : simKeepS s' = simKeepS s) :
    s'.t = s.t ∧ s'.first_lifetime_update = s.first_lifetime_update ∧ s'.next_future = s.next_future ∧
    s'.future_order = s.future_order ∧ s'.active = s.active ∧ s'.dict_slots = s.dict_slots ∧
    s'.free_list = s.free_list ∧ s'.child_counter = s.child_counter ∧ s'.pressed = s.pressed ∧
    s'.speed = s.speed ∧ s'.pools = s.pools := by
  simp only [simKeepS, Prod.mk.injEq] at h
  obtain ⟨_, a, b, c, d, e, f, g, h', _, _, _, i, j, _, _, _, _, _, _, _, k, _, _⟩ := h
  exact ⟨a, b, c, d, e, f, g, h', i, j, k⟩

/-- `SimARInv` for a state with the same instances/results whose dictionary changed (enum from duplicate-freeness) -/
theorem s8_ar_rebuild (h64 : System.Platform.numBits = 64) (tn fo P b0 n c s E ut us) (hI : SimARInv tn fo P b0 n c s E ut us)
    (s' : sim.state.St) (hinv' : SimInv c s') (hof : s3b_objFrame s s') (hil : s'.insts.val.length = s.insts.val.length)
    (htf : s3b_TfInv P (b0 + (simUnj s + ut) * (n + n + 4)) s')
    (h1 : s'.score = s.score) (h2 : s'.health = s.health) (h3 : s'.score_rp = s.score_rp)
    (h4 : s'.health_rp = s.health_rp) (h5 : s'.out = s.out) (h6 : s'.as_target = s.as_target)
    (h7 : s'.as_recent = s.as_recent) (h8 : s'.as_seen = s.as_seen) (h9 : s'.speed = s.speed)
    (hND : ((s'.dict_slots.val.filterMap id).map (·.val)).Nodup)
    (hds : ∀ x, some x ∈ s'.dict_slots.val → some x ∈ s.dict_slots.val)
    (hos : c.pb.objects.val.length < 2 ^ 32) (hns : ∀ o ∈ c.pb.objects.val, o.nested.val.length < 2 ^ 32) :
    SimARInv tn fo P b0 n c s' E ut us := by
  have hU := sim_unj_objFrame hof
  have hk := sim_keep_of_objFrame hof
  obtain ⟨hinv, htf0, hik, hem, hsp, hcnt, hseen, henum⟩ := hI
  refine ⟨hinv', by rw [hU]; exact htf, fun x hx => sim_instOk_keep hk (by omega) (hik x (hds x hx)), ?_, by rw [h9]; exact hsp,
    by rw [h6, h7, h8]; exact hcnt, by rw [h8, hU]; exact hseen, s8_enum h64 tn fo c s' hinv' hND hos hns⟩
  rw [hU]; exact sim_emitBud_congr c s s' _ h1 h2 h3 h4 h5 hem

theorem s8_stS_bd (tn) (s : sim.state.St) (slot : Usize) (hsl : slot.val < s.dict_slots.val.length)
    (v : alloc.vec.Vec Usize) (hv : v.val = s.free_list.val ++ [slot]) (h' : slot.val < (simStS tn s).dictSlots.size) :
    simStS tn { s with dict_slots := s.dict_slots.set slot none, free_list := v } =
      { simStS tn s with dictSlots := (simStS tn s).dictSlots.set slot.val none h',
                         freeList := slot.val :: (simStS tn s).freeList } := by
  simp only [simStS]
  congr 1
  · simp [abs, vec_set_val', List.map_set]
  · simp [hv]

theorem s8_keepJ {a b : sim.state.OState} (h : simKeepJ a = simKeepJ b) :
    a.life = b.life ∧ a.lifetime_start = b.lifetime_start ∧ a.child_id = b.child_id ∧ a.tick_insts = b.tick_insts ∧
    a.completed_spins = b.completed_spins := by
  simp only [simKeepJ, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, _, _, _, _, _, h9, _, _, _, _, _, _, _, _, h18, _, _⟩ := h
  exact ⟨h1, h2, h3, h9, h18⟩

theorem s8_filterMap_set_none {α} (l : List (Option α)) (k : Nat) :
    ((l.set k none).filterMap id).Sublist (l.filterMap id) := by
  induction l generalizing k with
  | nil => simp
  | cons x t ih =>
    cases k with
    | zero =>
      simp only [List.set_cons_zero, List.filterMap_cons, id]
      cases x
      · simp
      · exact List.sublist_cons_self _ _
    | succ k =>
      simp only [List.set_cons_succ, List.filterMap_cons, id]
      cases x
      · exact ih k
      · exact (ih k).cons_cons _

/-- the state fields the lifetime chain never changes (consumers: simcore3 / proc frames) -/
def s8LuKeep (s : sim.state.St) :=
  (s.k, s.t, s.mouse_valid, s.mouse, s.last_replay, s.pressed, s.speed, s.clock_rate, s.relax_down, s.relax_was_left,
   s.relax_last, s.ap_frame, s.block_last, s.block_idx, s.br_rot, s.cursor_pos, s.health.nearest_index,
   s.health_rp.nearest_index)

theorem s8_luk_of_keepS {s s' : sim.state.St} (h : simKeepS s' = simKeepS s) : s8LuKeep s' = s8LuKeep s := by
  simp only [simKeepS, Prod.mk.injEq] at h
  obtain ⟨h1, h2, _, _, _, _, _, _, _, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, _, h23, h24, h25, h26⟩ := h
  simp only [s8LuKeep, h1, h2, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h23, h24, h25, h26]

/-- what `became_dead` changes (for the lifetime invariant) -/
structure s8DFr (i : Usize) (s s' : sim.state.St) : Prop where
  len : s'.objs.val.length = s.objs.val.length
  ow : ∀ j (h : j < s.objs.val.length) (h' : j < s'.objs.val.length), j ≠ i.val →
    simKeepJ (s'.objs.val[j]'h') = simKeepJ (s.objs.val[j]'h)
  oi : ∀ (h : i.val < s.objs.val.length) (h' : i.val < s'.objs.val.length), (s'.objs.val[i.val]'h').life = .Past ∧
    (s'.objs.val[i.val]'h').child_id = (s.objs.val[i.val]'h).child_id ∧
    (s'.objs.val[i.val]'h').tick_insts = (s.objs.val[i.val]'h).tick_insts ∧
    (s'.objs.val[i.val]'h').completed_spins = (s.objs.val[i.val]'h).completed_spins ∧
    (s'.objs.val[i.val]'h').lifetime_start = (s.objs.val[i.val]'h).lifetime_start
  dict : ∃ (slot : Usize) (hs : slot.val < s.dict_slots.val.length), s.dict_slots.val[slot.val]'hs = some i ∧
    s'.dict_slots = s.dict_slots.set slot none ∧ s'.free_list.val = s.free_list.val ++ [slot]
  keep : s'.t = s.t ∧ s'.first_lifetime_update = s.first_lifetime_update ∧ s'.next_future = s.next_future ∧
    s'.future_order = s.future_order ∧ s'.active = s.active ∧ s'.child_counter = s.child_counter ∧
    s'.pressed = s.pressed ∧ s'.pools.val.length = s.pools.val.length ∧ s'.insts.val.length = s.insts.val.length
  lk : s8LuKeep s' = s8LuKeep s

theorem sim.step.became_dead_refines (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (hos : c.pb.objects.val.length < 2 ^ 32)
    (hns : ∀ o ∈ c.pb.objects.val, o.nested.val.length < 2 ^ 32)
    (s : sim.state.St) (i : Usize)
    (hI : SimARInv tn fo P b0 n c s 0 0 0) (hi : i.val < c.pb.objects.val.length) (hp : s3aPathOk c i.val)
    (hLP : simLP s)
    (htl : (c.pb.objects.val[i.val]'hi).h.kind = .Slider → ∃ hti : i.val < c.tail_idx.val.length,
      (c.tail_idx.val[i.val]'hti).val < (c.pb.objects.val[i.val]'hi).nested.val.length)
    (hcs : ∀ h : i.val < s.objs.val.length, (s.objs.val[i.val]'h).completed_spins.val * 360 < 2 ^ 63)
    (htk : ∀ h : i.val < s.objs.val.length,
      (s.objs.val[i.val]'h).tick_insts.val.length ≤ (c.pb.objects.val[i.val]'hi).nested.val.length)
    (hND : ((s.dict_slots.val.filterMap id).map (·.val)).Nodup) (hfl : s.free_list.val.length < Usize.max)
    (hpl : 6 ≤ s.pools.val.length) (hP : simPoolOk s) :
    ∃ res s', sim.step.became_dead c s i = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.becameDead i.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' 0 0 0 ∧ simLP s' ∧ simPoolOk s' ∧ s8DFr i s s') := by
  have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
  rw [s8_bd_split, s8_bd_splitS]
  obtain ⟨r, er, hr⟩ := sim.step.dict_slot_of_refines tn s i
  have hds : (simStS tn s).dictSlots = (s.dict_slots.val.map (fun o => (abs o : Option Nat))).toArray := rfl
  simp only [er, bind_ok, simM_bind, OsuModel.Sim.Sim.st, simM_get, s3b_ebok]
  cases r with
  | none =>
    have hn : (simStS tn s).dictSlots.idxOf? (some i.val) = none := by rw [← hr]; rfl
    simp only [hn]
    refine ⟨_, _, rfl, ?_, fun h => by cases h⟩
    exact ⟨_, rfl⟩
  | some slot =>
    have hn : (simStS tn s).dictSlots.idxOf? (some i.val) = some slot.val := by rw [← hr]; rfl
    have hL : (s.dict_slots.val.map (fun o => (abs o : Option Nat))).idxOf? (some i.val) = some slot.val := by
      rw [hds, List.idxOf?_toArray] at hn; exact hn
    obtain ⟨hsl0, hsv0, -⟩ := List.idxOf?_eq_some_iff.mp hL
    have hsl : slot.val < s.dict_slots.val.length := by simpa using hsl0
    have hsv : s.dict_slots.val[slot.val]'hsl = some i := by
      have : (abs (s.dict_slots.val[slot.val]'hsl) : Option Nat) = some i.val := by simpa using hsv0
      rcases hx : s.dict_slots.val[slot.val]'hsl with _ | x
      · rw [hx] at this; cases this
      · rw [hx] at this
        have : x.val = i.val := by simpa [abs] using this
        rw [show x = i from by scalar_tac]
    simp only [hn]
    have hsS : slot.val < (simStS tn s).dictSlots.size := by rw [hds]; simpa using hsl
    rw [vec_index_mut_eq _ _ hsl]
    simp only [bind_ok, uncurry_apply_pair]
    obtain ⟨FL, eFL, hFL⟩ : ∃ v, alloc.vec.Vec.push s.free_list slot = ok v ∧ v.val = s.free_list.val ++ [slot] :=
      ⟨_, vec_push_ok _ _ hfl, by simp⟩
    rw [eFL]; simp only [bind_ok]
    rw [vec_index_mut_eq _ _ ho]; simp only [bind_ok, uncurry_apply_pair]
    simp only [OsuModel.Sim.Sim.setA, dif_pos hsS, simM_bind, simM_pure, s3b_ebok, simM_set]
    rw [← s8_stS_bd tn s slot hsl FL hFL hsS]
    set O := s.objs.val[i.val]'ho with hO
    set O' : sim.state.OState := { O with life := .Past } with hO'
    have ho2 : i.val < ({ s with dict_slots := s.dict_slots.set slot none, free_list := FL } : sim.state.St).objs.val.length := ho
    rw [sim_modifyObj_stS tn _ _ i ho2 O' _ rfl _ rfl]
    simp only [s3b_ebok]
    set sm : sim.state.St := { s with objs := s.objs.set i O', dict_slots := s.dict_slots.set slot none, free_list := FL }
      with hsm
    have hgo : ∀ j (h : j < s.objs.val.length) (h' : j < sm.objs.val.length),
        sm.objs.val[j]'h' = if i.val = j then O' else s.objs.val[j]'h := by
      intro j h h'; simp only [hsm, vec_set_val', List.getElem_set]
    have hlo : sm.objs.val.length = s.objs.val.length := by simp [hsm, vec_set_val']
    have hinvO := sim_inv_objs_set hI.inv O' ho rfl
    have hinvm : SimInv c sm := by
      refine ⟨hinvO.objs_len, hinvO.nested_len, hinvO.nested_small, ?_, by simpa [hsm, vec_set_val'] using hI.inv.dict_small⟩
      intro o hm x hx
      simp only [hsm, vec_set_val'] at hm
      rcases List.mem_or_eq_of_mem_set hm with hm | hm
      · exact hI.inv.dict_in o hm x hx
      · subst hm; cases hx
    have hofm : s3b_objFrame s sm := by
      refine ⟨hlo, fun j h h' => ?_⟩
      rw [hgo j h h']
      split
      · rename_i hij; subst hij; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hNDm : ((sm.dict_slots.val.filterMap id).map (·.val)).Nodup := by
      have hsub := s8_filterMap_set_none s.dict_slots.val slot.val
      have : sm.dict_slots.val = s.dict_slots.val.set slot.val none := by simp [hsm, vec_set_val']
      rw [this]; exact hND.sublist (hsub.map _)
    have hIm : SimARInv tn fo P b0 n c sm 0 0 0 :=
      s8_ar_rebuild h64 tn fo P b0 n c s 0 0 0 hI sm hinvm hofm rfl hI.tf rfl rfl rfl rfl rfl rfl rfl rfl rfl hNDm
        (fun x hx => by
          simp only [hsm, vec_set_val'] at hx
          rcases List.mem_or_eq_of_mem_set hx with h | h
          · exact h
          · cases h) hos hns
    have hom : i.val < sm.objs.val.length := by rw [hlo]; exact ho
    have hsmi : sm.objs.val[i.val]'hom = O' := by rw [hgo _ ho hom]; simp
    have hLPm : simLP sm := by
      refine ⟨hLP.1, fun j hj => ?_⟩
      have hj' : j < s.objs.val.length := by rw [← hlo]; exact hj
      rw [hgo j hj' hj]
      split
      · rename_i hij; subst hij; exact hLP.2 _ ho
      · exact hLP.2 _ hj'
    have hcsm : ∀ h : i.val < sm.objs.val.length, (sm.objs.val[i.val]'h).completed_spins.val * 360 < 2 ^ 63 := by
      intro h; rw [hsmi]; exact hcs ho
    have hInm : simInstOk c sm i.val :=
      sim_instOk_keep ⟨hlo, fun j h h' => by
          rw [hgo j h h']
          split
          · rename_i hij; subst hij; exact ⟨rfl, rfl, rfl⟩
          · exact ⟨rfl, rfl, rfl⟩⟩ (le_refl _)
        (hI.ik i (by rw [← hsv]; exact List.getElem_mem hsl))
    obtain ⟨res, s1, eok, rok, iok⟩ := sim.step.on_killed_refines h64 tn fo E b0 n c hC hCS hlen sm i 0 hIm hInm hi hp hLPm htl hcsm
    rw [eok]; simp only [bind_ok, uncurry_apply_pair]
    cases res with
    | Err e =>
      refine ⟨.Err e, s1, by simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], ?_, fun h => by cases h⟩
      obtain ⟨m, hm⟩ := rok
      exact ⟨m, by rw [hm]; rfl⟩
    | Ok u =>
      cases u
      have rok' : OsuModel.Sim.Sim.onKilled i.val (simCtxS tn fo c) (simStS tn sm) = .ok ((), simStS tn s1) := rok
      obtain ⟨hI1, hJ1, hLP1⟩ := iok rfl
      have hil1 : s1.insts.val.length = sm.insts.val.length := hJ1.il
      obtain ⟨kt, kf, knf, kfo, kac, kd, kfl, kcc, kpr, ksp, kpl⟩ := s8_keepS hJ1.keep
      have ho1 : i.val < s1.objs.val.length := by rw [hJ1.len]; exact hom
      obtain ⟨jl, js, jc, jt, jcs⟩ := s8_keepJ (hJ1.ow i.val hom ho1)
      have hpl1 : 6 ≤ s1.pools.val.length := by rw [kpl]; exact hpl
      have hP1 : simPoolOk s1 := by
        intro p hp' j hj
        rw [kpl] at hp'
        rw [hil1]; exact hP p hp' j hj
      have htk1 : (s1.objs.val[i.val]'ho1).tick_insts.val.length ≤ (c.pb.objects.val[i.val]'hi).nested.val.length := by
        rw [jt, hsmi]; exact htk ho
      obtain ⟨s', et, st, ⟨ins', pl', hs'⟩, hil', htf', hpl', hP'⟩ :=
        s8_bd_tail tn fo E (b0 + (simUnj s1 + 0) * (n + n + 4)) c s1 i hi ho1 hI1.tf
          (by obtain ⟨_, a, b, d, -⟩ := simInstOk_of_jfr hJ1 hInm; exact ⟨a, b, d⟩) htk1 hpl1 hP1
      refine ⟨.Ok (), s', by simpa [core.result.Result.Insts.CoreOpsTry.branch] using et, ?_, fun _ => ⟨?_, ?_, hP', ?_⟩⟩
      · show _ = _
        rw [rok']; exact st
      · subst hs'
        exact sim_ar_inv_hook tn fo P b0 n c s1 0 0 0 0 hI1 _ (s3b_inv_of hI1.inv rfl rfl)
          ⟨rfl, fun j h h' => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ hil' htf' rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      · subst hs'; exact hLP1
      · subst hs'
        refine ⟨by simp only; rw [hJ1.len, hlo], fun j h h' hji => ?_, fun h h' => ?_, ⟨slot, hsl, hsv, ?_, ?_⟩, ?_, ?_⟩
        · have hm1 : j < sm.objs.val.length := by rw [hlo]; exact h
          have e1 := hJ1.ow j hm1 h'
          rw [hgo j h hm1, if_neg (Ne.symm hji)] at e1
          exact e1
        · refine ⟨by rw [jl, hsmi], by rw [jc, hsmi], by rw [jt, hsmi], by rw [jcs, hsmi], by rw [js, hsmi]⟩
        · show s1.dict_slots = _; rw [kd]
        · show s1.free_list.val = _; rw [kfl]; exact hFL
        · exact ⟨kt, kf, knf, kfo, kac, kcc, kpr, by simp only; rw [hpl', kpl], by simp only; rw [hil', hil1]⟩
        · have e := s8_luk_of_keepS hJ1.keep; exact e
end OsuProofs
