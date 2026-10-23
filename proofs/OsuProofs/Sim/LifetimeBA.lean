import OsuProofs.Sim.LifetimeLoops
import OsuProofs.Sim.LifetimeInv

/-
  sim8: `became_alive` with the frame the lifetime chain needs (s8_became_alive_fr): the dictionary / free-list step
  (s8DS), active ++ [i], child_counter + 1, and `s8R` (only object i, insts, pools, theta change; key fields of object i
  fixed; insts grow by at most nested + 2). Copies of sim core's tails (BecameAlive.lean) with the frame conjunct added.
-/
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

/-! ## the became_alive frame (sim8: copies of the BecameAlive tails with a frame conjunct) -/

def s8BAKey (o : sim.state.OState) :=
  (o.life, o.child_id, o.completed_spins, o.last_pressed, o.result, o.nested, o.lifetime_start, o.inst)

def s8K (o : sim.state.OState) (cid : U64) (k : Usize) :=
  (sim.state.Life.Alive, cid, 0#u64, replay.frames.ACTLIST_EMPTY, o.result, o.nested, o.lifetime_start, k)

/-- the frame of became_alive's tail from base state `s0`: only insts / pools / theta and object `i` change; object `i`'s
key fields are `K`; its ticks stay in range / bounded by `N` if they were; at most `M` new instances -/
structure s8R (i : Usize) (K : sim.state.Life × U64 × U64 × replay.frames.ActList × Option sim.state.Res ×
    alloc.vec.Vec (Option sim.state.Res) × float.F64 × Usize) (N M T TL : Nat) (s0 s : sim.state.St) : Prop where
  shape : ∃ ins pl th O, s = { s0 with insts := ins, pools := pl, theta := th, objs := s0.objs.set i O }
  key : ∀ h : i.val < s.objs.val.length, s8BAKey (s.objs.val[i.val]'h) = K
  hdv : ∀ h : i.val < s.objs.val.length, (s.objs.val[i.val]'h).head_inst.val < s.insts.val.length
  tkl : (∀ h : i.val < s0.objs.val.length, (s0.objs.val[i.val]'h).tick_insts.val.length ≤ N) →
    ∀ h : i.val < s.objs.val.length, (s.objs.val[i.val]'h).tick_insts.val.length ≤ N
  tkv : (∀ h : i.val < s0.objs.val.length, ∀ x ∈ (s0.objs.val[i.val]'h).tick_insts.val, x.val < s0.insts.val.length) →
    ∀ h : i.val < s.objs.val.length, ∀ x ∈ (s.objs.val[i.val]'h).tick_insts.val, x.val < s.insts.val.length
  ilen : s0.insts.val.length ≤ s.insts.val.length
  iub : s.insts.val.length ≤ s0.insts.val.length + M
  plen : s.pools.val.length = s0.pools.val.length
  pool : simPoolOk s
  inl : ∀ h : i.val < s.objs.val.length, (s.objs.val[i.val]'h).inst.val < s.insts.val.length
  tkn : ∀ h : i.val < s.objs.val.length, (s.objs.val[i.val]'h).tick_insts.val.length = T
  tln : ∀ h : i.val < s.objs.val.length, (s.objs.val[i.val]'h).tick_live.val.length = TL

theorem s8R_ins {i K N M T TL s0 s} (h : s8R i K N M T TL s0 s) (ins : alloc.vec.Vec sim.state.Inst)
    (hl : ins.val.length = s.insts.val.length) (th : float.F32) : s8R i K N M T TL s0 { s with insts := ins, theta := th } := by
  obtain ⟨⟨ins0, pl0, th0, O0, hs⟩, hk, hdv, htl, htv, hil, hiu, hpl, hP, hin, hT, hTL⟩ := h
  refine ⟨⟨ins, pl0, th, O0, by subst hs; rfl⟩, hk, fun h' => ?_, htl, fun h0 h1 x hx => ?_, ?_, ?_, hpl, ?_, fun h' => ?_, hT, hTL⟩
  · have := hdv h'; show _ < ins.val.length; rw [hl]; exact this
  · have := htv h0 h1 x hx; show x.val < ins.val.length; rw [hl]; exact this
  · show s0.insts.val.length ≤ ins.val.length; rw [hl]; exact hil
  · show ins.val.length ≤ _; rw [hl]; exact hiu
  · intro p hp j hj; show j.val < ins.val.length; rw [hl]; exact hP p hp j hj
  · have := hin h'; show _ < ins.val.length; rw [hl]; exact this

theorem s8R_usx {i K N M T TL s0 s} (h : s8R i K N M T TL s0 s) (ins : alloc.vec.Vec sim.state.Inst) (th : float.F32)
    (hio : i.val < s.objs.val.length) (O : sim.state.OState)
    (hO : s8BAKey O = s8BAKey (s.objs.val[i.val]'hio)) (hOt : O.tick_insts = (s.objs.val[i.val]'hio).tick_insts)
    (hOh : O.head_inst = (s.objs.val[i.val]'hio).head_inst)
    (hl : ins.val.length = s.insts.val.length) (hOl : O.tick_live = (s.objs.val[i.val]'hio).tick_live) :
    s8R i K N M T TL s0 { s with insts := ins, theta := th, objs := s.objs.set i O } := by
  obtain ⟨⟨ins0, pl0, th0, O0, hs⟩, hk, hdv, htl, htv, hil, hiu, hpl, hP, hin, hT, hTL⟩ := h
  have hg : ∀ h' : i.val < (s.objs.set i O).val.length, (s.objs.set i O).val[i.val]'h' = O := by
    intro h'; simp only [vec_set_val', List.getElem_set_self]
  have hOi : O.inst = (s.objs.val[i.val]'hio).inst := by
    simp only [s8BAKey, Prod.mk.injEq] at hO; exact hO.2.2.2.2.2.2.2
  refine ⟨⟨ins, pl0, th, O, ?_⟩, fun h' => ?_, fun h' => ?_, fun h0 h' => ?_, fun h0 h' x hx => ?_, ?_, ?_, hpl, ?_,
    fun h' => ?_, fun h' => ?_, fun h' => ?_⟩
  · subst hs; simp only [sim_vset_set]
  · show s8BAKey ((s.objs.set i O).val[i.val]'h') = K; rw [hg, hO]; exact hk hio
  · show ((s.objs.set i O).val[i.val]'h').head_inst.val < ins.val.length; rw [hg, hOh, hl]; exact hdv hio
  · show ((s.objs.set i O).val[i.val]'h').tick_insts.val.length ≤ N; rw [hg, hOt]; exact htl h0 hio
  · change x ∈ ((s.objs.set i O).val[i.val]'h').tick_insts.val at hx
    rw [hg, hOt] at hx; show x.val < ins.val.length; rw [hl]; exact htv h0 hio x hx
  · show s0.insts.val.length ≤ ins.val.length; rw [hl]; exact hil
  · show ins.val.length ≤ _; rw [hl]; exact hiu
  · intro p hp j hj; show j.val < ins.val.length; rw [hl]; exact hP p hp j hj
  · show ((s.objs.set i O).val[i.val]'h').inst.val < ins.val.length; rw [hg, hOi, hl]; exact hin hio
  · show ((s.objs.set i O).val[i.val]'h').tick_insts.val.length = T; rw [hg, hOt]; exact hT hio
  · show ((s.objs.set i O).val[i.val]'h').tick_live.val.length = TL; rw [hg, hOl]; exact hTL hio

theorem s8R_us {i K N M T TL s0 s} (h : s8R i K N M T TL s0 s) (s' : sim.state.St) (hus : s3c_usFrame i s s') :
    s8R i K N M T TL s0 s' := by
  obtain ⟨hio, a, ha, le, hle, hs', hl⟩ := hus
  rw [hs']
  exact s8R_usx h s'.insts s'.theta hio _ rfl rfl rfl hl rfl

theorem s8R_pg {i K N M T TL s0 s} (h : s8R i K N M T TL s0 s) (s' : sim.state.St)
    (hs : ∃ ins pl, s' = { s with insts := ins, pools := pl }) (hl1 : s.insts.val.length ≤ s'.insts.val.length)
    (hl2 : s'.insts.val.length ≤ s.insts.val.length + 1) (hpl' : s'.pools.val.length = s.pools.val.length)
    (hP' : simPoolOk s') : s8R i K N (M + 1) T TL s0 s' := by
  obtain ⟨ins1, pl1, hs1⟩ := hs
  obtain ⟨⟨ins0, pl0, th0, O0, hs⟩, hk, hdv, htl, htv, hil, hiu, hpl, hP, hin, hT, hTL⟩ := h
  rw [hs1] at hl1 hl2 hpl' hP' ⊢
  refine ⟨⟨ins1, pl1, th0, O0, by subst hs; rfl⟩, hk, fun h' => Nat.lt_of_lt_of_le (hdv h') hl1, htl,
    fun h0 h1 x hx => ?_, ?_, ?_, ?_, hP', fun h' => Nat.lt_of_lt_of_le (hin h') hl1, hT, hTL⟩
  · have := htv h0 h1 x hx; show x.val < ins1.val.length; exact Nat.lt_of_lt_of_le this hl1
  · exact Nat.le_trans hil hl1
  · show ins1.val.length ≤ _; have := hiu; change ins1.val.length ≤ s.insts.val.length + 1 at hl2; omega
  · change pl1.val.length = s.pools.val.length at hpl'; show pl1.val.length = _; rw [hpl']; exact hpl

theorem s8R_init (i : Usize) (K) (N M T TL : Nat) (s0 s : sim.state.St) (hs : ∃ ins pl, s = { s0 with insts := ins, pools := pl })
    (ho : i.val < s0.objs.val.length) (O2 : sim.state.OState) (hK : s8BAKey O2 = K)
    (htk : O2.tick_insts = (s0.objs.val[i.val]'ho).tick_insts) (hhd : O2.head_inst.val < s.insts.val.length)
    (hl1 : s0.insts.val.length ≤ s.insts.val.length) (hl2 : s.insts.val.length ≤ s0.insts.val.length + M)
    (hpl : s.pools.val.length = s0.pools.val.length) (hP : simPoolOk s)
    (hT : (s0.objs.val[i.val]'ho).tick_insts.val.length = T) (hin : O2.inst.val < s.insts.val.length)
    (htl2 : O2.tick_live = (s0.objs.val[i.val]'ho).tick_live) (hTL : (s0.objs.val[i.val]'ho).tick_live.val.length = TL) :
    s8R i K N M T TL s0 { s with objs := s.objs.set i O2 } := by
  obtain ⟨ins1, pl1, rfl⟩ := hs
  have hg : ∀ h' : i.val < (s0.objs.set i O2).val.length, (s0.objs.set i O2).val[i.val]'h' = O2 := by
    intro h'; simp only [vec_set_val', List.getElem_set_self]
  refine ⟨⟨ins1, pl1, s0.theta, O2, rfl⟩, fun h' => by simp only; rw [hg]; exact hK,
    fun h' => by simp only at h' ⊢; rw [hg]; exact hhd, fun h0 h' => ?_, fun h0 h' x hx => ?_, hl1, hl2, hpl, hP,
    fun h' => by simp only at h' ⊢; rw [hg]; exact hin, fun h' => by simp only at h' ⊢; rw [hg, htk]; exact hT,
    fun h' => by simp only at h' ⊢; rw [hg, htl2]; exact hTL⟩
  · simp only at h' ⊢; rw [hg, htk]; exact h0 ho
  · simp only at h' hx ⊢; rw [hg, htk] at hx; exact Nat.lt_of_lt_of_le (h0 ho x hx) hl1

set_option hygiene false in
/-- `became_alive` from the Top `apply_bindings` on (state `sT`) -/
macro "s8_ba_top" : tactic => `(tactic| (
  obtain ⟨r2, s6, ea2, sa2, Y2, hY2, fY2⟩ := sim.step.apply_bindings_refines tn fo c sT i .Top k hi hhi hkT
    (fun h => by cases h)
  simp only [ea2, bind_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch]
  cases r2 with
  | Err e =>
    obtain ⟨m, hm⟩ := sa2
    refine ⟨.Err e, s6, by simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual],
      ⟨m, ?_⟩, fun h => by cases h⟩
    have hm' : OsuModel.Sim.Sim.applyBindings i.val .top k.val (simCtxS tn fo c) (simStS tn sT) = .error m := hm
    simp only [hm', simM_bind, Except.bind]
  | Ok u =>
    have sa2' : OsuModel.Sim.Sim.applyBindings i.val .top k.val (simCtxS tn fo c) (simStS tn sT) =
      .ok ((), simStS tn s6) := sa2
    subst hY2
    have hk6 : k.val < (sT.insts.set k Y2).val.length := by simpa [vec_set_val'] using hkT
    have hl6 : ((sT.insts.set k Y2).val[k.val]'hk6).loaded = (sT.insts.val[k.val]'hkT).loaded := by
      simp only [vec_set_val', List.getElem_set_self]; exact fY2.loaded
    simp only [sa2', simM_bind, Except.bind, s3a_instOf tn fo c { sT with insts := sT.insts.set k Y2 } _ hk6, vec_index_eq _ _ hk6, hl6, bind_ok]
    have hlS6 : (abs ((sT.insts.set k Y2).val[k.val]'hk6) : OsuModel.Sim.Inst).loaded =
      (sT.insts.val[k.val]'hkT).loaded := hl6
    rw [hlS6]
    by_cases hl : (sT.insts.val[k.val]'hkT).loaded = true
    · have hTf6 : s3b_TfInv P (b + n + n + 4) { sT with insts := sT.insts.set k Y2 } := sim_tf_ab X hkT hTfT fY2
      obtain ⟨s7, eu, su, hinv7, hTf7, -, -, -, -, -, hus7⟩ := s3c_update_state_from_result_strong tn fo E b n c
        { sT with insts := sT.insts.set k Y2 } i .Top 1#u64
        ⟨hinvT.objs_len, hinvT.nested_len, hinvT.nested_small, hinvT.dict_in, hinvT.dict_small⟩ hTf6
        (fun ns => hCS i .Top ns hi hhi hhb (fun h => by cases h)) hioT
        (by simpa [vec_set_val'] using hk1T) (by simpa [vec_set_val'] using hk2T) hhi hhb hhnT
      have su' : OsuModel.Sim.Sim.updateStateFromResult i.val .top 1 (simCtxS tn fo c)
        (simStS tn { sT with insts := sT.insts.set k Y2 }) = .ok ((), simStS tn s7) := su
      refine ⟨.Ok (), s7, by simp [hl, eu], ?_, fun _ => ⟨hinv7, hTf7,
        fun h => s8R_us (s8R_ins (hRT h) (sT.insts.set k Y2) (by simp [vec_set_val']) sT.theta) s7 hus7⟩⟩
      simp only [hl, if_true, su']
      rfl
    · refine ⟨.Ok (), { sT with insts := sT.insts.set k Y2 }, by simp [hl], ?_, fun _ =>
        ⟨⟨hinvT.objs_len, hinvT.nested_len, hinvT.nested_small, hinvT.dict_in, hinvT.dict_small⟩,
         sim_tf_ab X hkT (sim_tf_mono E hTfT (by omega)) fY2,
         fun h => s8R_ins (hRT h) (sT.insts.set k Y2) (by simp [vec_set_val']) sT.theta⟩⟩
      simp only [hl, Bool.false_eq_true, if_false, simM_pure, simRelM]))


theorem s8_ba_tail_other (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize)
    (hi : i.val < c.pb.objects.val.length) (hinv : SimInv c s) (cid : U64) (k : Usize)
    (hk : k.val < s.insts.val.length) (hpl : 6 ≤ s.pools.val.length) (hP : simPoolOk s)
    (hcap : s.insts.val.length + 1 + (c.pb.objects.val[i.val]'hi).nested.val.length < Usize.max)
    (hns : (c.pb.objects.val[i.val]'hi).h.kind ≠ .Slider) (hnsp : (c.pb.objects.val[i.val]'hi).h.kind ≠ .Spinner)
    (hC : SimARCtx c)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (X : simTfX P) (b n : Nat) (hCS : simCSH P n tn fo c)
    (hTf : s3b_TfInv P (b + n + n + 4) s) (hB : b + n + n + 4 + 1 < Usize.max) :
    ∃ res s', simBATailR c s i (c.pb.objects.val[i.val]'hi) cid k = ok (res, s') ∧
      simRelM tn s' res (simBATailS i.val (topS tn (c.pb.objects.val[i.val]'hi)) cid.val k.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimInv c s' ∧ s3b_TfInv P b s' ∧
        ∀ h : i.val < s.objs.val.length, s8R i (s8K (s.objs.val[i.val]'h) cid k)
          (c.pb.objects.val[i.val]'hi).nested.val.length 0 ((s.objs.val[i.val]'h).tick_insts.val.length) ((s.objs.val[i.val]'h).tick_live.val.length) s s') := by
  have ho : i.val < s.objs.val.length := by rw [hinv.objs_len]; exact hi
  unfold simBATailR simBATailS
  have hkS : (topS tn (c.pb.objects.val[i.val]'hi)).h.kind = kindS (c.pb.objects.val[i.val]'hi).h.kind := rfl
  have hb1 : (kindS (c.pb.objects.val[i.val]'hi).h.kind == OsuModel.Sim.Kind.slider) = false := by
    revert hns; cases (c.pb.objects.val[i.val]'hi).h.kind <;> simp [kindS] <;> decide
  have hb2 : (kindS (c.pb.objects.val[i.val]'hi).h.kind == OsuModel.Sim.Kind.spinner) = false := by
    revert hnsp; cases (c.pb.objects.val[i.val]'hi).h.kind <;> simp [kindS] <;> decide
  have hb1' : (kindS (c.pb.objects.val[i.val]'hi).h.kind == kindS sim.playable.Kind.Slider) = false := hb1
  have hb2' : (kindS (c.pb.objects.val[i.val]'hi).h.kind == kindS sim.playable.Kind.Spinner) = false := hb2
  rw [hkS]
  have hk0 : (0 : Nat) < s.insts.val.length := by omega
  simp only [simM_bind, Except.bind, hb1, hb2, hb1', hb2', kind_eq_ok, bind_ok, simM_pure,
    Bool.false_eq_true, if_false, uncurry_apply_pair,
    vec_index_eq _ _ hk, vec_index_mut_eq _ _ ho, netx_F64_POS_INF, netx_F64_NEG_INF,
    sim_basic_F32_0, s3a_instOf tn fo c s _ hk, s3a_instOf tn fo c s _ hk0]
  generalize hO1 : s.objs.val[i.val]'ho = O1
  set O1' : sim.state.OState := { O1 with
      armed := (s.insts.val[k.val]'hk).armed
      head_armed := .Idle } with hO1'
  rw [sim_modifyObj_stS tn _ s i ho O1' _ (by rw [hO1]; rfl) _ rfl]
  set O2 : sim.state.OState := { O1 with
      life := sim.state.Life.Alive
      child_id := cid
      hit_action := none
      hovered := false
      head_lifetime_end := F64.posInf
      head_alive := false
      tracking := false
      inst := k
      head_inst := 0#usize
      armed := (s.insts.val[k.val]'hk).armed
      head_armed := .Idle
      accept_any_after := none
      last_pressed := replay.frames.ACTLIST_EMPTY
      slider_mouse := none
      spin_tracking := false
      spin_mouse := none
      last_angle := none
      total_accumulated := 0
      accumulated_at_last_completion := 0
      current_spin_max := 0
      completed_spins := 0#u64
      last_report_time := F64.negInf
      completed_full_spins := 0#i64 } with hO2
  have ho' : i.val < (s.objs.set i O1').val.length := by simpa [vec_set_val'] using ho
  have h2m := sim_modifyObj_stS tn (simCtxS tn fo c) { s with objs := s.objs.set i O1' } i ho' O2
    (fun os => { os with
      life := OsuModel.Sim.Life.alive, childId := cid.val, hitAction := none, inst := k.val, headInst := 0
      hovered := false, tracking := false, acceptAnyAfter := none, lastPressed := [], sliderMouse := none
      headAlive := false, headLifetimeEnd := F64.posInf
      spinTracking := false, spinMouse := none, lastAngle := none, totalAccumulated := 0
      accumulatedAtLastCompletion := 0, currentSpinMax := 0, completedSpins := 0, lastReportTime := F64.negInf
      completedFullSpins := 0 })
    (by simp only [vec_set_val', List.getElem_set_self]; first | rfl | (simp [ostateS, hO2, hO1']; exact ⟨rfl, s2_abs_empty⟩) ) _ rfl
  simp only [h2m, sim_vset_set]
  clear h2m hO1' ho'
  clear_value O1' O2
  obtain ⟨hhi, hhb, hhn⟩ := hC.hd i.val hi
  have ho4 : i.val < (s.objs.set i O2).val.length := by simpa [vec_set_val'] using ho
  have hhnT : sim.step.Part.Top = sim.step.Part.Head ∨ (c.pb.objects.val[i.val]'hi).h.kind = .Slider →
      (c.head_idx.val[i.val]'hhi).val < (c.pb.objects.val[i.val]'hi).nested.val.length := by
    rintro (h | h); · cases h
    · exact absurd h hns
  have hinv4 : SimInv c { s with objs := s.objs.set i O2 } := sim_inv_objs_set hinv O2 ho (by rw [hO1, hO2])
  have hTfT : s3b_TfInv P (b + n + n + 4) ({ s with objs := s.objs.set i O2 } : sim.state.St) := hTf
  have hkT : k.val < ({ s with objs := s.objs.set i O2 } : sim.state.St).insts.val.length := hk
  have hioT : i.val < ({ s with objs := s.objs.set i O2 } : sim.state.St).objs.val.length := ho4
  have hk1T : ((({ s with objs := s.objs.set i O2 } : sim.state.St).objs.val[i.val]'hioT).inst.val) <
      ({ s with objs := s.objs.set i O2 } : sim.state.St).insts.val.length := by
    simpa [vec_set_val', hO2] using hk
  have hk2T : ((({ s with objs := s.objs.set i O2 } : sim.state.St).objs.val[i.val]'hioT).head_inst.val) <
      ({ s with objs := s.objs.set i O2 } : sim.state.St).insts.val.length := by
    simpa [vec_set_val', hO2] using hk0
  have hinvT := hinv4
  have hRT : ∀ h : i.val < s.objs.val.length, s8R i (s8K (s.objs.val[i.val]'h) cid k)
      (c.pb.objects.val[i.val]'hi).nested.val.length 0 ((s.objs.val[i.val]'h).tick_insts.val.length) ((s.objs.val[i.val]'h).tick_live.val.length) s { s with objs := s.objs.set i O2 } := by
    intro h
    exact s8R_init i _ _ 0 _ _ s s ⟨s.insts, s.pools, rfl⟩ h O2 (by rw [hO2]; simp only [s8BAKey, s8K]; rw [← hO1]) (by rw [hO2, hO1]) (by rw [hO2]; exact hk0) le_rfl (by omega) rfl hP rfl (by rw [hO2]; exact hk) (by rw [hO2, hO1]) rfl
  generalize hsT : ({ s with objs := s.objs.set i O2 } : sim.state.St) = sT at *
  s8_ba_top


theorem s8_ba_tail_slider (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize)
    (hi : i.val < c.pb.objects.val.length) (hinv : SimInv c s) (cid : U64) (k : Usize)
    (hk : k.val < s.insts.val.length) (hpl : 6 ≤ s.pools.val.length) (hP : simPoolOk s)
    (hcap : s.insts.val.length + 1 + (c.pb.objects.val[i.val]'hi).nested.val.length < Usize.max)
    (hsl : (c.pb.objects.val[i.val]'hi).h.kind = .Slider) (hC : SimARCtx c)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (X : simTfX P) (b n : Nat) (hCS : simCSH P n tn fo c)
    (hTf : s3b_TfInv P (b + n + n + 4 + (n + n + 4)) s) (hB : b + n + n + 4 + (n + n + 4) + 1 < Usize.max) :
    ∃ res s', simBATailR c s i (c.pb.objects.val[i.val]'hi) cid k = ok (res, s') ∧
      simRelM tn s' res (simBATailS i.val (topS tn (c.pb.objects.val[i.val]'hi)) cid.val k.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimInv c s' ∧ s3b_TfInv P b s' ∧
        ∀ h : i.val < s.objs.val.length, s8R i (s8K (s.objs.val[i.val]'h) cid k)
          (c.pb.objects.val[i.val]'hi).nested.val.length 1 ((s.objs.val[i.val]'h).tick_insts.val.length) ((s.objs.val[i.val]'h).tick_live.val.length) s s') := by
  have ho : i.val < s.objs.val.length := by rw [hinv.objs_len]; exact hi
  unfold simBATailR simBATailS
  have hkS : (topS tn (c.pb.objects.val[i.val]'hi)).h.kind = kindS (c.pb.objects.val[i.val]'hi).h.kind := rfl
  rw [hkS, hsl]
  obtain ⟨hk1, s3, e1', ⟨ins3, pl3, hs3⟩, hpl3, hpre3, hk1l, hP3, -⟩ := sim_pool_get_ok s 2#usize (by simp; omega)
    (by omega) hP
  obtain ⟨hk1', s3', e1, s1e, -, -, hins, -⟩ := sim.step.pool_get_refines tn fo c s 2#usize (by simp; omega)
    (by omega)
  rw [e1] at e1'; simp only [ok.injEq, Prod.mk.injEq] at e1'; obtain ⟨h1', h2'⟩ := e1'; subst hk1'; subst s3'
  have s1e' : OsuModel.Sim.Sim.poolGet 2 (simCtxS tn fo c) (simStS tn s) = .ok (hk1.val, simStS tn s3) := s1e
  have hk3 : k.val < s3.insts.val.length := Nat.lt_of_lt_of_le hk hpre3.length_le
  have ho3 : i.val < s3.objs.val.length := by rw [hs3]; exact ho
  simp only [simM_bind, Except.bind, kindS, sim_kb_slider_slider, sim_kb_slider_spinner, kind_eq_ok, bind_ok,
    if_true, if_false, e1, s1e', uncurry_apply_pair, Bool.false_eq_true,
    vec_index_eq _ _ hk3, vec_index_eq _ _ hk1l, vec_index_mut_eq _ _ ho3, netx_F64_POS_INF, netx_F64_NEG_INF,
    sim_basic_F32_0, s3a_instOf tn fo c s3 _ hk3, s3a_instOf tn fo c s3 _ hk1l]
  generalize hO1 : s3.objs.val[i.val]'ho3 = O1
  rw [sim_modifyObj_stS tn _ s3 i ho3 { O1 with
      armed := (s3.insts.val[k.val]'hk3).armed
      head_armed := (s3.insts.val[hk1.val]'hk1l).armed } _ (by rw [hO1]; rfl) _ rfl]
  set O1' : sim.state.OState := { O1 with
      armed := (s3.insts.val[k.val]'hk3).armed
      head_armed := (s3.insts.val[hk1.val]'hk1l).armed } with hO1'
  set O2 : sim.state.OState := { O1 with
      life := sim.state.Life.Alive
      child_id := cid
      hit_action := none
      hovered := false
      head_lifetime_end := F64.posInf
      head_alive := false
      tracking := false
      inst := k
      head_inst := hk1
      armed := (s3.insts.val[k.val]'hk3).armed
      head_armed := (s3.insts.val[hk1.val]'hk1l).armed
      accept_any_after := none
      last_pressed := replay.frames.ACTLIST_EMPTY
      slider_mouse := none
      spin_tracking := false
      spin_mouse := none
      last_angle := none
      total_accumulated := 0
      accumulated_at_last_completion := 0
      current_spin_max := 0
      completed_spins := 0#u64
      last_report_time := F64.negInf
      completed_full_spins := 0#i64 } with hO2
  have ho3' : i.val < (s3.objs.set i O1').val.length := by simpa [vec_set_val'] using ho3
  have h2m := sim_modifyObj_stS tn (simCtxS tn fo c) { s3 with objs := s3.objs.set i O1' } i ho3' O2
    (fun os => { os with
      life := OsuModel.Sim.Life.alive, childId := cid.val, hitAction := none, inst := k.val, headInst := hk1.val
      hovered := false, tracking := false, acceptAnyAfter := none, lastPressed := [], sliderMouse := none
      headAlive := false, headLifetimeEnd := F64.posInf
      spinTracking := false, spinMouse := none, lastAngle := none, totalAccumulated := 0
      accumulatedAtLastCompletion := 0, currentSpinMax := 0, completedSpins := 0, lastReportTime := F64.negInf
      completedFullSpins := 0 })
    (by simp only [vec_set_val', List.getElem_set_self]; first | rfl | (simp [ostateS, hO2, hO1']; exact ⟨rfl, s2_abs_empty⟩) ) _ rfl
  simp only [h2m, sim_vset_set]
  clear h2m hO1' ho3'
  clear_value O1' O2
  obtain ⟨hhi, hhb, hhn⟩ := hC.hd i.val hi
  have hhn' := hhn (Or.inl hsl)
  have hk1l4 : hk1.val < ({ s3 with objs := s3.objs.set i O2 } : sim.state.St).insts.val.length := hk1l
  obtain ⟨r1, s5, ea1, sa1, Y1, hY1, fY1⟩ := sim.step.apply_bindings_refines tn fo c { s3 with objs := s3.objs.set i O2 }
    i .Head hk1 hi hhi hk1l4 (fun _ => hhn')
  have sa1' := sa1
  simp only [ea1, bind_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch]
  cases r1 with
  | Err e =>
    obtain ⟨m, hm⟩ := sa1
    simp only [abs, sim.step.Part.Head] at hm
    refine ⟨.Err e, s5, by simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual],
      ⟨m, ?_⟩, fun h => by cases h⟩
    have hm' : OsuModel.Sim.Sim.applyBindings i.val .head hk1.val (simCtxS tn fo c)
      (simStS tn { s3 with objs := s3.objs.set i O2 }) = .error m := hm
    simp only [hm']
  | Ok u =>
    have sa1' : OsuModel.Sim.Sim.applyBindings i.val .head hk1.val (simCtxS tn fo c)
      (simStS tn { s3 with objs := s3.objs.set i O2 }) = .ok ((), simStS tn s5) := sa1
    subst hY1
    have hk15 : hk1.val < (s3.insts.set hk1 Y1).val.length := by simpa [vec_set_val'] using hk1l
    have hl5 : ((s3.insts.set hk1 Y1).val[hk1.val]'hk15).loaded = (s3.insts.val[hk1.val]'hk1l).loaded := by
      simp only [vec_set_val', List.getElem_set_self]; exact fY1.loaded
    simp only [sa1', simM_bind, Except.bind, s3a_instOf tn fo c { s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } _ hk15,
      vec_index_eq _ _ hk15, hl5, bind_ok]
    have hlS : (abs ((s3.insts.set hk1 Y1).val[hk1.val]'hk15) : OsuModel.Sim.Inst).loaded =
      (s3.insts.val[hk1.val]'hk1l).loaded := hl5
    rw [hlS]
    have hinv3 : SimInv c s3 := by
      rw [hs3]; exact ⟨hinv.objs_len, hinv.nested_len, hinv.nested_small, hinv.dict_in, hinv.dict_small⟩
    have hinv4 : SimInv c { s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } := by
      have := sim_inv_objs_set (s := s3) hinv3 O2 ho3 (by rw [hO1, hO2])
      exact ⟨this.objs_len, this.nested_len, this.nested_small, this.dict_in, this.dict_small⟩
    have hTf3 : s3b_TfInv P (b + n + n + 4 + (n + n + 4)) s3 := sim_tf_pg X hB hTf (by
      rcases hins with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, trivial⟩)
    have hTf4 : s3b_TfInv P (b + n + n + 4 + (n + n + 4))
        { s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } := sim_tf_ab X hk1l hTf3 fY1
    have ho4 : i.val < (s3.objs.set i O2).val.length := by simpa [vec_set_val'] using ho3
    have hO2i : (s3.objs.set i O2).val[i.val]'ho4 = O2 := by simp [vec_set_val']
    have hhnT : sim.step.Part.Top = sim.step.Part.Head ∨ (c.pb.objects.val[i.val]'hi).h.kind = .Slider →
        (c.head_idx.val[i.val]'hhi).val < (c.pb.objects.val[i.val]'hi).nested.val.length := fun _ => hhn'
    have hR4 : ∀ h : i.val < s.objs.val.length, s8R i (s8K (s.objs.val[i.val]'h) cid k)
        (c.pb.objects.val[i.val]'hi).nested.val.length 1 ((s.objs.val[i.val]'h).tick_insts.val.length) ((s.objs.val[i.val]'h).tick_live.val.length) s
        ({ s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } : sim.state.St) := by
      intro h
      have hO1s : O1 = s.objs.val[i.val]'h := by rw [← hO1]; simp only [hs3]
      have hl3 : s3.insts.val.length ≤ s.insts.val.length + 1 := by
        rcases hins with h' | ⟨h', -⟩ <;> rw [h'] <;> simp
      exact s8R_ins (s8R_init i _ _ 1 _ _ s s3 ⟨ins3, pl3, hs3⟩ h O2 (by rw [hO2, hO1s]; rfl) (by rw [hO2, hO1s]) (by rw [hO2]; exact hk1l)
        hpre3.length_le hl3 hpl3 hP3 rfl (by rw [hO2]; exact hk3) (by rw [hO2, hO1s]) rfl) (s3.insts.set hk1 Y1) (by simp [vec_set_val']) s3.theta
    by_cases hl : (s3.insts.val[hk1.val]'hk1l).loaded = true
    · obtain ⟨s5, eu, su, hinv5, hTf5, hil5, hol5, -, -, hof5, hus5⟩ := s3c_update_state_from_result_strong tn fo E
        (b + n + n + 4) n c { s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } i .Head 1#u64 hinv4
        (by simpa [Nat.add_assoc] using hTf4)
        (fun ns => hCS i .Head ns hi hhi hhb (fun _ => hhn')) ho4
        (by simpa [vec_set_val', hO2] using hk3)
        (by simpa [vec_set_val', hO2] using hk1l) hhi hhb (fun _ => hhn')
      have su' : OsuModel.Sim.Sim.updateStateFromResult i.val .head 1 (simCtxS tn fo c)
        (simStS tn { s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 }) = .ok ((), simStS tn s5) := su
      simp only [hl, if_true, eu, bind_ok, su', simM_bind, Except.bind]
      have hioT : i.val < s5.objs.val.length := by rw [hol5]; exact ho4
      have hkT : k.val < s5.insts.val.length := by rw [hil5]; simpa [vec_set_val'] using hk3
      have hk1T : ((s5.objs.val[i.val]'hioT).inst.val) < s5.insts.val.length := by
        rw [(hof5.2 i.val ho4 hioT).1, hil5]; simpa [vec_set_val', hO2] using hk3
      have hk2T : ((s5.objs.val[i.val]'hioT).head_inst.val) < s5.insts.val.length := by
        rw [(hof5.2 i.val ho4 hioT).2.1, hil5]; simpa [vec_set_val', hO2] using hk1l
      have hRT : ∀ h : i.val < s.objs.val.length, s8R i (s8K (s.objs.val[i.val]'h) cid k)
          (c.pb.objects.val[i.val]'hi).nested.val.length 1 ((s.objs.val[i.val]'h).tick_insts.val.length) ((s.objs.val[i.val]'h).tick_live.val.length) s s5 := fun h => s8R_us (hR4 h) s5 hus5
      generalize s5 = sT at *
      have hinvT := hinv5
      have hTfT := hTf5
      s8_ba_top
    · simp only [hl, Bool.false_eq_true, if_false, bind_ok]
      have hTfT : s3b_TfInv P (b + n + n + 4) ({ s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } : sim.state.St) :=
        sim_tf_mono E hTf4 (by omega)
      have hkT : k.val < ({ s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } : sim.state.St).insts.val.length := by simpa [vec_set_val'] using hk3
      have hioT : i.val < ({ s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } : sim.state.St).objs.val.length := ho4
      have hk1T : ((({ s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } : sim.state.St).objs.val[i.val]'hioT).inst.val) < ({ s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } : sim.state.St).insts.val.length := by
        simpa [vec_set_val', hO2] using hk3
      have hk2T : ((({ s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } : sim.state.St).objs.val[i.val]'hioT).head_inst.val) < ({ s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } : sim.state.St).insts.val.length := by
        simpa [vec_set_val', hO2] using hk1l
      have hinvT := hinv4
      have hRT := hR4
      generalize hsT : ({ s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } : sim.state.St) = sT at *
      s8_ba_top


theorem s8_stg0_loop (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (i : Usize)
    (hi : i.val < c.pb.objects.val.length)
    (hsm : (c.pb.objects.val[i.val]'hi).nested.val.length < 2 ^ 63)
    (F : Nat → Array Nat → OsuModel.Sim.SimM (ForInStep (Array Nat)))
    (hF : ∀ j r, F j r = (do
      let x ← OsuModel.Sim.Sim.nestedOf (topS tn (c.pb.objects.val[i.val]'hi)) j
      let tk ← OsuModel.Sim.Sim.poolGet (if (x.kind == OsuModel.Sim.Kind.spinnerBonusTick) = true then 5 else 4)
      pure (ForInStep.yield (r.push tk)))) :
    ∀ m (j : Usize) (s : sim.state.St) (tis : alloc.vec.Vec Usize) (live : alloc.vec.Vec Bool),
      (c.pb.objects.val[i.val]'hi).nested.val.length - j.val = m →
      j.val ≤ (c.pb.objects.val[i.val]'hi).nested.val.length →
      tis.val.length = j.val → live.val = List.replicate j.val false →
      6 ≤ s.pools.val.length → s.insts.val.length + m < Usize.max → simPoolOk s →
      (∀ x ∈ tis.val, x.val < s.insts.val.length) →
      ∃ s' tis' live', simSTG0 c s i tis live j hi = ok (s', tis', live') ∧
        forIn (m := OsuModel.Sim.SimM) (List.range' j.val m) (simTisS tis) F (simCtxS tn fo c) (simStS tn s) =
          .ok (simTisS tis', simStS tn s') ∧
        tis'.val.length = (c.pb.objects.val[i.val]'hi).nested.val.length ∧
        live'.val = List.replicate (c.pb.objects.val[i.val]'hi).nested.val.length false ∧
        (∃ ins pl, s' = { s with insts := ins, pools := pl }) ∧ s'.pools.val.length = s.pools.val.length ∧
        s.insts.val <+: s'.insts.val ∧ simPoolOk s' ∧ (∀ x ∈ tis'.val, x.val < s'.insts.val.length) ∧
        (∀ ins ∈ s'.insts.val, ins ∈ s.insts.val ∨ ins = s3b_instNew) ∧
        s'.insts.val.length ≤ s.insts.val.length + m := by
  intro m
  induction m with
  | zero =>
    intro j s tis live hm hj htl hlv hpl hcap hP htis
    have hge : ¬ j < alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested := by rw [vec_lt_len_iff]; omega
    have hjn : j.val = (c.pb.objects.val[i.val]'hi).nested.val.length := by omega
    refine ⟨s, tis, live, ?_, by simp, by rw [htl, hjn], by rw [hlv, hjn], ⟨_, _, rfl⟩, rfl, List.prefix_refl _, hP, htis,
      fun ins h => Or.inl h, by omega⟩
    unfold simSTG0 sim.step.spinner_ticks_get_loop0
    rw [loop_unfold]
    simp [sim.step.spinner_ticks_get_loop0.body, hge]
  | succ m ih =>
    intro j s tis live hm hj htl hlv hpl hcap hP htis
    have hjl : j.val < (c.pb.objects.val[i.val]'hi).nested.val.length := by omega
    have hlt : j < alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested := by rw [vec_lt_len_iff]; exact hjl
    have hnp := (c.pb.objects.val[i.val]'hi).nested.property
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
    have hpk6 : pk.val < s.pools.val.length := by
      have : pk.val ≤ 5 := by rw [hpk]; split <;> decide
      omega
    obtain ⟨k, s1, epg, rpg⟩ := sim.step.pool_get_refines tn fo c s pk hpk6 (by omega)
    obtain ⟨k', s1', epg', hfr, hpl1, hpre, hkl, hP1, -, hnw⟩ := sim_pool_get_ok s pk hpk6 (by omega) hP
    rw [epg] at epg'
    simp only [ok.injEq, Prod.mk.injEq] at epg'
    obtain ⟨rfl, rfl⟩ := epg'
    obtain ⟨tis1, htis1⟩ : ∃ v, alloc.vec.Vec.push tis k = ok v ∧ v.val = tis.val ++ [k] :=
      ⟨_, vec_push_ok tis k (by omega), by simp⟩
    obtain ⟨live1, hlive1⟩ : ∃ v, alloc.vec.Vec.push live false = ok v ∧ v.val = live.val ++ [false] :=
      ⟨_, vec_push_ok live false (by rw [hlv]; simp; omega), by simp⟩
    have hb : sim.step.spinner_ticks_get_loop0.body c.pb.objects i
        (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) s tis live j = ok (.cont (s1, tis1, live1, j1)) := by
      simp only [sim.step.spinner_ticks_get_loop0.body, hlt, ite_true, vec_index_eq _ _ hi, bind_ok, hn, kind_eq_ok]
      have : (kindS sim.playable.Kind.SpinnerBonusTick) = OsuModel.Sim.Kind.spinnerBonusTick := rfl
      simp only [this]
      rw [show (if (kindS hd.kind == OsuModel.Sim.Kind.spinnerBonusTick) = true then ok 5#usize else ok 4#usize : Result Usize) = ok pk by
        rw [hpk]; split <;> rfl]
      simp only [bind_ok, epg, uncurry_apply_pair, htis1.1, hlive1.1, hj1]
    have hstep : simSTG0 c s i tis live j hi = simSTG0 c s1 i tis1 live1 j1 hi := by
      unfold simSTG0 sim.step.spinner_ticks_get_loop0
      rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]
    obtain ⟨ins1, pl1, hs1⟩ := hfr
    have htis1' : ∀ x ∈ tis1.val, x.val < s1.insts.val.length := by
      intro x hx; rw [htis1.2] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact Nat.lt_of_lt_of_le (htis x hx) hpre.length_le
      · simp at hx; subst hx; exact hkl
    obtain ⟨s', tis', live', e', r', l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := ih j1 s1 tis1 live1 (by omega) (by omega)
      (by rw [htis1.2]; simp; omega) (by rw [hlive1.2, hlv, hj1v, List.replicate_succ']) (by omega)
      (by rcases rpg.2.2.2.1 with h | ⟨h, _⟩ <;> rw [h] <;> (try simp) <;> omega) hP1 htis1'
    refine ⟨s', tis', live', by rw [hstep]; exact e', ?_, l1, l2, ?_, by omega, hpre.trans l5, l6, l7, ?_, ?_⟩
    · rw [List.range'_succ, List.forIn_cons, hF]
      simp only [simM_bind, enj, Except.bind]
      have hkS : (hobjS tn hd).kind = kindS hd.kind := rfl
      rw [hkS, hpkS, ← hpk, rpg.1]
      simp only [simM_pure]
      have : (simTisS tis).push k.val = simTisS tis1 := by simp [simTisS, htis1.2]
      rw [this, show j.val + 1 = j1.val from hj1v.symm]
      exact r'
    · obtain ⟨a, b, hsa⟩ := l3; rw [hsa, hs1]; exact ⟨a, b, rfl⟩
    · intro ins h
      rcases l8 ins h with h | h
      · exact hnw ins h
      · exact Or.inr h
    · have : s1.insts.val.length ≤ s.insts.val.length + 1 := by
        rcases rpg.2.2.2.1 with h | ⟨h, _⟩ <;> rw [h] <;> simp
      omega

theorem s8_stg (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (s : sim.state.St) (i : Usize) (hi : i.val < c.pb.objects.val.length) (hinv : SimInv c s)
    (hpl : 6 ≤ s.pools.val.length)
    (hcap : s.insts.val.length + (c.pb.objects.val[i.val]'hi).nested.val.length < Usize.max) (hP : simPoolOk s) :
    ∃ s', sim.step.spinner_ticks_get c s i = ok s' ∧
      (do
        let tis ← forIn (m := OsuModel.Sim.SimM) [:(topS tn (c.pb.objects.val[i.val]'hi)).nested.size] (#[] : Array Nat)
          (fun j r => do
            let x ← OsuModel.Sim.Sim.nestedOf (topS tn (c.pb.objects.val[i.val]'hi)) j
            let tk ← OsuModel.Sim.Sim.poolGet (if (x.kind == OsuModel.Sim.Kind.spinnerBonusTick) = true then 5 else 4)
            pure (ForInStep.yield (r.push tk)))
        OsuModel.Sim.Sim.modifyObj i.val fun os =>
          { os with tickInsts := tis, tickLive := Array.map (fun _ => false) tis }
        forIn' (m := OsuModel.Sim.SimM) [:tis.size] PUnit.unit fun j h _ => do
          let x ← OsuModel.Sim.Sim.instOf tis[j]
          if x.loaded = true then do
            OsuModel.Sim.Sim.tickState i.val j 1 OsuModel.Sim.Armed.idle true
            pure (ForInStep.yield PUnit.unit)
          else pure (ForInStep.yield PUnit.unit)) (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧
      SimInv c s' ∧ s'.pools.val.length = s.pools.val.length ∧ simPoolOk s' ∧
      s.insts.val.length ≤ s'.insts.val.length ∧
      (∀ (P : Nat → sim.transforms.TObj → Prop), simTfX P → ∀ B, B + 1 < Usize.max → s3b_TfInv P B s → s3b_TfInv P B s') ∧
      (∀ (h : i.val < s.objs.val.length) (h' : i.val < s'.objs.val.length),
        (s'.objs.val[i.val]'h').inst = (s.objs.val[i.val]'h).inst ∧
        (s'.objs.val[i.val]'h').head_inst = (s.objs.val[i.val]'h).head_inst) ∧
      (∀ h : i.val < s.objs.val.length, ∃ (tis : alloc.vec.Vec Usize) (live : alloc.vec.Vec Bool)
          (ins : alloc.vec.Vec sim.state.Inst) (pl : alloc.vec.Vec (alloc.vec.Vec (Option Usize))) (th : float.F32),
          s' = { s with insts := ins, pools := pl, theta := th, objs := s.objs.set i { s.objs.val[i.val]'h with tick_insts := tis, tick_live := live } } ∧
          tis.val.length = (c.pb.objects.val[i.val]'hi).nested.val.length ∧ ∀ x ∈ tis.val, x.val < ins.val.length) ∧
      (∀ (h : i.val < s.objs.val.length) (h' : i.val < s'.objs.val.length),
        (s'.objs.val[i.val]'h').tick_live.val.length = (c.pb.objects.val[i.val]'hi).nested.val.length) ∧
      s'.insts.val.length ≤ s.insts.val.length + (c.pb.objects.val[i.val]'hi).nested.val.length := by
  have hsm := hinv.nested_small _ (List.getElem_mem hi)
  have hsz : (topS tn (c.pb.objects.val[i.val]'hi)).nested.size = (c.pb.objects.val[i.val]'hi).nested.val.length := by
    simp [topS]
  have hnew : simTisS (alloc.vec.Vec.new Usize) = #[] := rfl
  obtain ⟨s1, tis, live, e0, r0, htl, hlv, ⟨ins1, pl1, hs1⟩, hpl1, hpre, hP1, htis, hnw0, hiub⟩ :=
    s8_stg0_loop tn fo c i hi (by omega) _ (fun _ _ => rfl) (c.pb.objects.val[i.val]'hi).nested.val.length 0#usize s (alloc.vec.Vec.new Usize)
      (alloc.vec.Vec.new Bool) (by simp) (by simp) (by simp) (by simp) hpl (by simpa using hcap) hP (by simp)
  have h00 : (0#usize).val = 0 := rfl
  simp only [h00, hnew] at r0
  have ho : i.val < s.objs.val.length := by rw [hinv.objs_len]; exact hi
  have ho1 : i.val < s1.objs.val.length := by rw [hs1]; exact ho
  have hinv1 : SimInv c s1 := by rw [hs1]; exact ⟨hinv.objs_len, hinv.nested_len, hinv.nested_small, hinv.dict_in, hinv.dict_small⟩
  set o := s1.objs.val[i.val]'ho1 with ho_def
  let o' : sim.state.OState := { o with tick_insts := tis, tick_live := live }
  let s2 : sim.state.St := { s1 with objs := s1.objs.set i o' }
  have hinv2 : SimInv c s2 := ⟨by simp [s2, vec_set_val', hinv1.objs_len], fun j h1 h2 => by
      simp only [s2, vec_set_val'] at h1 ⊢
      by_cases e : j = i.val
      · subst e; simp [o', o]; exact hinv1.nested_len _ ho1 h2
      · simp [List.getElem_set, Ne.symm e]; exact hinv1.nested_len _ _ h2, hinv1.nested_small, hinv1.dict_in,
      hinv1.dict_small⟩
  have hti2 : ∀ hio : i.val < s2.objs.val.length, (s2.objs.val[i.val]'hio).tick_insts = tis := by
    intro hio; simp [s2, vec_set_val', o']
  have htk2 : ∀ x ∈ tis.val, x.val < s2.insts.val.length := htis
  have hsimS : ((simTisS tis).size) = (c.pb.objects.val[i.val]'hi).nested.val.length := by simp [simTisS, htl]
  obtain ⟨s', e1, r1, i1, o1', l1, f1, t1⟩ := sim_stg1_loop tn fo c i hi tis htl
    (c.pb.objects.val[i.val]'hi).nested.val.length 0#usize s2 (by simp) (by simp) hinv2 hti2 htk2
    (List.range' 0 (c.pb.objects.val[i.val]'hi).nested.val.length)
    (fun a h u => (do
          let x ← OsuModel.Sim.Sim.instOf ((simTisS tis)[a]'(by simp at h; rw [hsimS]; omega))
          if x.loaded = true then do
            OsuModel.Sim.Sim.tickState i.val a 1 OsuModel.Sim.Armed.idle true
            pure (ForInStep.yield PUnit.unit)
          else pure (ForInStep.yield PUnit.unit) : OsuModel.Sim.SimM (ForInStep PUnit)))
    (by simp) (fun a h u => by
      simp at h
      simp only [simSTG1G, getElem!_pos (simTisS tis) a (by rw [hsimS]; omega)])
  refine ⟨s', ?_, ?_, i1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold sim.step.spinner_ticks_get
    simp only [simSTG0] at e0
    simp only [vec_index_eq _ _ hi, bind_ok, e0, uncurry_apply_pair, vec_index_mut_eq _ _ ho1]
    rw [vec_index_mut_eq _ _ (by simp [vec_set_val']; exact ho1)]
    simp only [bind_ok, uncurry_apply_pair]
    simp only [simSTG1] at e1
    convert e1 using 2
    simp only [s2, o', o]
    congr 1
    apply alloc.vec.Vec.ext
    simp [vec_set_val']
  · rw [Std.Legacy.Range.forIn_eq_forIn_range']
    simp only [Std.Legacy.Range.size, Nat.div_one, Nat.sub_zero, Nat.add_sub_cancel, hsz]
    simp only [simM_bind, r0, Except.bind]
    rw [sim_modifyObj_stS tn _ s1 i ho1 o' _ (by
      simp only [ostateS, o', o]
      congr 1
      all_goals simp [abs, simTisS, hlv, htl]) _ rfl]
    simp only [Except.bind]
    rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
    simp only [Std.Legacy.Range.size, Nat.div_one, Nat.sub_zero, Nat.add_sub_cancel, hsimS]
    exact r1
  · obtain ⟨a, b, hab⟩ := f1; rw [hab]; exact hpl1
  · obtain ⟨a, b, hab⟩ := f1
    intro p hp j hj
    have hp' : p ∈ s1.pools.val := by rw [hab] at hp; exact hp
    rw [l1]; exact hP1 p hp' j hj
  · rw [l1]; exact hpre.length_le
  · intro P X B hB h
    apply t1 P B
    intro ins hm
    rcases hnw0 ins hm with hm | hm
    · exact h ins hm
    · subst hm; exact X.new B hB
  · intro h h'
    have e2 : s'.objs.val = (s1.objs.set i o').val := by rw [o1']
    have hh : (s'.objs.val[i.val]'h') = o' := by simp only [e2, vec_set_val', List.getElem_set_self]
    rw [hh]
    have hs1o : s1.objs = s.objs := by rw [hs1]
    simp only [o', o, hs1o]
    refine ⟨?_, ?_⟩ <;> first | trivial | rfl | simp
  · intro h
    obtain ⟨a, b, hab⟩ := f1
    refine ⟨tis, live, a, pl1, b, ?_, htl, fun x hx => ?_⟩
    · rw [hab]; first | (subst hs1; rfl) | (simp only [s2, o', o]; subst hs1; rfl)
    · have := htk2 x hx; change x.val < s1.insts.val.length at this; have hl1' := l1; rw [hab] at hl1'; change a.val.length = s1.insts.val.length at hl1'; omega
  · intro h h'
    have e2 : s'.objs.val = (s1.objs.set i o').val := by rw [o1']
    have hh : (s'.objs.val[i.val]'h') = o' := by simp only [e2, vec_set_val', List.getElem_set_self]
    rw [hh]; simp [o', hlv]
  · rw [l1]; show s1.insts.val.length ≤ _; simpa using hiub

theorem s8R_ticks {i K N M T TL s0 s} (h : s8R i K N M T TL s0 s) (s' : sim.state.St) (hio : i.val < s.objs.val.length)
    (tis : alloc.vec.Vec Usize) (live : alloc.vec.Vec Bool) (ins : alloc.vec.Vec sim.state.Inst)
    (pl : alloc.vec.Vec (alloc.vec.Vec (Option Usize))) (th : float.F32)
    (hs' : s' = { s with insts := ins, pools := pl, theta := th, objs := s.objs.set i { s.objs.val[i.val]'hio with tick_insts := tis, tick_live := live } })
    (htl : tis.val.length ≤ N) (htv : ∀ x ∈ tis.val, x.val < ins.val.length) (hl1 : s.insts.val.length ≤ ins.val.length)
    (M' : Nat) (hl2 : ins.val.length ≤ s.insts.val.length + M') (hpl : pl.val.length = s.pools.val.length)
    (hP : simPoolOk s') : s8R i K N (M + M') tis.val.length live.val.length s0 s' := by
  obtain ⟨⟨ins0, pl0, th0, O0, hs⟩, hk, hdv, htl0, htv0, hil, hiu, hpl0, hP0, hin, hT, hTL⟩ := h
  subst hs'
  set O : sim.state.OState := { s.objs.val[i.val]'hio with tick_insts := tis, tick_live := live } with hO
  have hg : ∀ h' : i.val < (s.objs.set i O).val.length, (s.objs.set i O).val[i.val]'h' = O := by
    intro h'; simp only [vec_set_val', List.getElem_set_self]
  refine ⟨⟨ins, pl, th, O, ?_⟩, fun h' => ?_, fun h' => ?_, fun _ h' => ?_, fun _ h' x hx => ?_, ?_, ?_, ?_, hP,
    fun h' => ?_, fun h' => ?_, fun h' => ?_⟩
  · subst hs; simp only [sim_vset_set]
  · show s8BAKey ((s.objs.set i O).val[i.val]'h') = K; rw [hg]; exact hk hio
  · show ((s.objs.set i O).val[i.val]'h').head_inst.val < ins.val.length; rw [hg]; exact Nat.lt_of_lt_of_le (hdv hio) hl1
  · show ((s.objs.set i O).val[i.val]'h').tick_insts.val.length ≤ N; rw [hg]; exact htl
  · change x ∈ ((s.objs.set i O).val[i.val]'h').tick_insts.val at hx; rw [hg] at hx; exact htv x hx
  · show s0.insts.val.length ≤ ins.val.length; omega
  · show ins.val.length ≤ _; omega
  · show pl.val.length = _; rw [hpl]; exact hpl0
  · show ((s.objs.set i O).val[i.val]'h').inst.val < ins.val.length; rw [hg]; exact Nat.lt_of_lt_of_le (hin hio) hl1
  · show ((s.objs.set i O).val[i.val]'h').tick_insts.val.length = tis.val.length; rw [hg]
  · show ((s.objs.set i O).val[i.val]'h').tick_live.val.length = live.val.length; rw [hg]

theorem s8_ba_tail_spinner (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize)
    (hi : i.val < c.pb.objects.val.length) (hinv : SimInv c s) (cid : U64) (k : Usize)
    (hk : k.val < s.insts.val.length) (hpl : 6 ≤ s.pools.val.length) (hP : simPoolOk s)
    (hcap : s.insts.val.length + 1 + (c.pb.objects.val[i.val]'hi).nested.val.length < Usize.max)
    (hsp : (c.pb.objects.val[i.val]'hi).h.kind = .Spinner)
    (hC : SimARCtx c)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (X : simTfX P) (b n : Nat) (hCS : simCSH P n tn fo c)
    (hTf : s3b_TfInv P (b + n + n + 4) s) (hB : b + n + n + 4 + 1 < Usize.max) :
    ∃ res s', simBATailR c s i (c.pb.objects.val[i.val]'hi) cid k = ok (res, s') ∧
      simRelM tn s' res (simBATailS i.val (topS tn (c.pb.objects.val[i.val]'hi)) cid.val k.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimInv c s' ∧ s3b_TfInv P b s' ∧
        ∀ h : i.val < s.objs.val.length, s8R i (s8K (s.objs.val[i.val]'h) cid k)
          (c.pb.objects.val[i.val]'hi).nested.val.length (0 + (c.pb.objects.val[i.val]'hi).nested.val.length) (c.pb.objects.val[i.val]'hi).nested.val.length (c.pb.objects.val[i.val]'hi).nested.val.length s s') := by
  have ho : i.val < s.objs.val.length := by rw [hinv.objs_len]; exact hi
  unfold simBATailR simBATailS
  have hkS : (topS tn (c.pb.objects.val[i.val]'hi)).h.kind = kindS (c.pb.objects.val[i.val]'hi).h.kind := rfl
  have hns : (c.pb.objects.val[i.val]'hi).h.kind ≠ .Slider := by rw [hsp]; intro h; cases h
  rw [hkS, hsp]
  have hk0 : (0 : Nat) < s.insts.val.length := by omega
  simp only [simM_bind, Except.bind, kindS, sim_kb_spinner_slider, sim_kb_spinner_spinner, kind_eq_ok, bind_ok, simM_pure,
    if_true,
    Bool.false_eq_true, if_false, uncurry_apply_pair,
    vec_index_eq _ _ hk, vec_index_mut_eq _ _ ho, netx_F64_POS_INF, netx_F64_NEG_INF,
    sim_basic_F32_0, s3a_instOf tn fo c s _ hk, s3a_instOf tn fo c s _ hk0]
  generalize hO1 : s.objs.val[i.val]'ho = O1
  set O1' : sim.state.OState := { O1 with
      armed := (s.insts.val[k.val]'hk).armed
      head_armed := .Idle } with hO1'
  rw [sim_modifyObj_stS tn _ s i ho O1' _ (by rw [hO1]; rfl) _ rfl]
  set O2 : sim.state.OState := { O1 with
      life := sim.state.Life.Alive
      child_id := cid
      hit_action := none
      hovered := false
      head_lifetime_end := F64.posInf
      head_alive := false
      tracking := false
      inst := k
      head_inst := 0#usize
      armed := (s.insts.val[k.val]'hk).armed
      head_armed := .Idle
      accept_any_after := none
      last_pressed := replay.frames.ACTLIST_EMPTY
      slider_mouse := none
      spin_tracking := false
      spin_mouse := none
      last_angle := none
      total_accumulated := 0
      accumulated_at_last_completion := 0
      current_spin_max := 0
      completed_spins := 0#u64
      last_report_time := F64.negInf
      completed_full_spins := 0#i64 } with hO2
  have ho' : i.val < (s.objs.set i O1').val.length := by simpa [vec_set_val'] using ho
  have h2m := sim_modifyObj_stS tn (simCtxS tn fo c) { s with objs := s.objs.set i O1' } i ho' O2
    (fun os => { os with
      life := OsuModel.Sim.Life.alive, childId := cid.val, hitAction := none, inst := k.val, headInst := 0
      hovered := false, tracking := false, acceptAnyAfter := none, lastPressed := [], sliderMouse := none
      headAlive := false, headLifetimeEnd := F64.posInf
      spinTracking := false, spinMouse := none, lastAngle := none, totalAccumulated := 0
      accumulatedAtLastCompletion := 0, currentSpinMax := 0, completedSpins := 0, lastReportTime := F64.negInf
      completedFullSpins := 0 })
    (by simp only [vec_set_val', List.getElem_set_self]; first | rfl | (simp [ostateS, hO2, hO1']; exact ⟨rfl, s2_abs_empty⟩) ) _ rfl
  simp only [h2m, sim_vset_set]
  clear h2m hO1' ho'
  clear_value O1' O2
  obtain ⟨hhi, hhb, hhn⟩ := hC.hd i.val hi
  have ho4 : i.val < (s.objs.set i O2).val.length := by simpa [vec_set_val'] using ho
  have hinv4 : SimInv c { s with objs := s.objs.set i O2 } := sim_inv_objs_set hinv O2 ho (by rw [hO1, hO2])
  obtain ⟨s5, es, rs, hinv5, hpl5, hP5, hil5, htf5, hio5, hsh5, hlv5, hiu5⟩ := s8_stg tn fo c
    { s with objs := s.objs.set i O2 } i hi hinv4 hpl (by simp; omega) hP
  simp only [simM_bind] at rs
  have key := sim_ex_bind3 (δ := Unit × OsuModel.Sim.St) _ _ _ _ rs
  simp only [Except.bind] at key
  rw [key]
  simp only [es, bind_ok]
  have hhnT : sim.step.Part.Top = sim.step.Part.Head ∨ (c.pb.objects.val[i.val]'hi).h.kind = .Slider →
      (c.head_idx.val[i.val]'hhi).val < (c.pb.objects.val[i.val]'hi).nested.val.length := by
    rintro (h | h); · cases h
    · exact absurd h hns
  have hTfT : s3b_TfInv P (b + n + n + 4) s5 := htf5 P X _ (by omega) hTf
  have hkT : k.val < s5.insts.val.length := Nat.lt_of_lt_of_le hk hil5
  have hioT : i.val < s5.objs.val.length := by rw [hinv5.objs_len]; exact hi
  have hio5' := hio5 ho4 hioT
  have hk1T : ((s5.objs.val[i.val]'hioT).inst.val) < s5.insts.val.length := by
    rw [hio5'.1]; simpa [vec_set_val', hO2] using hkT
  have hk2T : ((s5.objs.val[i.val]'hioT).head_inst.val) < s5.insts.val.length := by
    rw [hio5'.2]; simp [vec_set_val', hO2]; omega
  have hinvT := hinv5
  have hRT : ∀ h : i.val < s.objs.val.length, s8R i (s8K (s.objs.val[i.val]'h) cid k)
      (c.pb.objects.val[i.val]'hi).nested.val.length (0 + (c.pb.objects.val[i.val]'hi).nested.val.length) (c.pb.objects.val[i.val]'hi).nested.val.length (c.pb.objects.val[i.val]'hi).nested.val.length s s5 := by
    intro h
    obtain ⟨tis, live, a, pl, th, hs5, htl5, htv5⟩ := hsh5 ho4
    have hR0 := s8R_init i (s8K (s.objs.val[i.val]'h) cid k) (c.pb.objects.val[i.val]'hi).nested.val.length 0 _ _ s s
      ⟨s.insts, s.pools, rfl⟩ h O2 (by rw [hO2, ← hO1]; rfl) (by rw [hO2, hO1]) (by rw [hO2]; exact hk0) le_rfl (by omega) rfl hP
      rfl (by rw [hO2]; exact hk) (by rw [hO2, hO1]) rfl
    have e5 : s5.insts = a := by rw [hs5]
    have ep : s5.pools = pl := by rw [hs5]
    have := s8R_ticks hR0 s5 ho4 tis live a pl th hs5 (by rw [htl5]) htv5 (by rw [← e5]; exact hil5) _
      (by rw [← e5]; exact hiu5) (by rw [← ep]; exact hpl5) hP5
    have hlv' : live.val.length = (c.pb.objects.val[i.val]'hi).nested.val.length := by
      have e := hlv5 ho4 (by rw [hinv5.objs_len]; exact hi)
      have : (s5.objs.val[i.val]'(by rw [hinv5.objs_len]; exact hi)).tick_live = live := by
        subst hs5; simp [vec_set_val']
      rw [← this]; exact e
    rw [htl5, hlv'] at this; exact this
  generalize s5 = sT at *
  s8_ba_top


theorem s8R_mono {i K N M M' T TL s0 s} (h : s8R i K N M T TL s0 s) (hM : M ≤ M') : s8R i K N M' T TL s0 s := by
  obtain ⟨a, b, c, d, e, f, g, p, q, r, t, u⟩ := h
  exact ⟨a, b, c, d, e, f, by omega, p, q, r, t, u⟩

theorem s8R_base {i K N M T TL} (sD s1 : sim.state.St) {s : sim.state.St}
    (hs1 : ∃ ins pl, s1 = { sD with insts := ins, pools := pl }) (hl1 : sD.insts.val.length ≤ s1.insts.val.length)
    (hl2 : s1.insts.val.length ≤ sD.insts.val.length + 1) (hpl : s1.pools.val.length = sD.pools.val.length)
    (h : s8R i K N M T TL s1 s) : s8R i K N (M + 1) T TL sD s := by
  obtain ⟨ins1, pl1, rfl⟩ := hs1
  obtain ⟨⟨ins, pl, th, O, hs⟩, hk, hdv, htl, htv, hil, hiu, hpl0, hP, hin, hT, hTL⟩ := h
  refine ⟨⟨ins, pl, th, O, by rw [hs]⟩, hk, hdv, fun h0 => htl h0, fun h0 => htv (fun h1 x hx => ?_), by omega, by omega,
    by rw [hpl0, hpl], hP, hin, hT, hTL⟩
  exact Nat.lt_of_lt_of_le (h0 h1 x hx) hl1

theorem s8_ba_tail (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize)
    (hi : i.val < c.pb.objects.val.length) (hinv : SimInv c s) (cid : U64) (k : Usize)
    (hk : k.val < s.insts.val.length) (hpl : 6 ≤ s.pools.val.length) (hP : simPoolOk s)
    (hcap : s.insts.val.length + 1 + (c.pb.objects.val[i.val]'hi).nested.val.length < Usize.max) (hC : SimARCtx c)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (X : simTfX P) (b n : Nat) (hCS : simCSH P n tn fo c)
    (hTf : s3b_TfInv P (b + n + n + 4 + (n + n + 4)) s) (hB : b + n + n + 4 + (n + n + 4) + 1 < Usize.max) :
    ∃ res s', simBATailR c s i (c.pb.objects.val[i.val]'hi) cid k = ok (res, s') ∧
      simRelM tn s' res (simBATailS i.val (topS tn (c.pb.objects.val[i.val]'hi)) cid.val k.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimInv c s' ∧ s3b_TfInv P b s' ∧
        ∀ h : i.val < s.objs.val.length, ∃ T TL, ((c.pb.objects.val[i.val]'hi).h.kind = .Spinner → T = (c.pb.objects.val[i.val]'hi).nested.val.length ∧ TL = (c.pb.objects.val[i.val]'hi).nested.val.length) ∧
            s8R i (s8K (s.objs.val[i.val]'h) cid k) (c.pb.objects.val[i.val]'hi).nested.val.length ((c.pb.objects.val[i.val]'hi).nested.val.length + 1) T TL s s') := by
  by_cases hsl : (c.pb.objects.val[i.val]'hi).h.kind = .Slider
  · obtain ⟨res, s', e, r, h⟩ := s8_ba_tail_slider tn fo c s i hi hinv cid k hk hpl hP hcap hsl hC E X b n hCS hTf hB
    exact ⟨res, s', e, r, fun hr => ⟨(h hr).1, (h hr).2.1, fun h' => ⟨_, _, (fun e => by rw [hsl] at e; cases e),
      s8R_mono ((h hr).2.2 h') (by omega)⟩⟩⟩
  by_cases hsp : (c.pb.objects.val[i.val]'hi).h.kind = .Spinner
  · obtain ⟨res, s', e, r, h⟩ := s8_ba_tail_spinner tn fo c s i hi hinv cid k hk hpl hP (by omega) hsp hC E X b n hCS
      (sim_tf_mono E hTf (by omega)) (by omega)
    exact ⟨res, s', e, r, fun hr => ⟨(h hr).1, (h hr).2.1, fun h' => ⟨_, _, fun _ => ⟨rfl, rfl⟩,
      s8R_mono ((h hr).2.2 h') (by omega)⟩⟩⟩
  · obtain ⟨res, s', e, r, h⟩ := s8_ba_tail_other tn fo c s i hi hinv cid k hk hpl hP (by omega) hsl hsp hC E X b n hCS
      (sim_tf_mono E hTf (by omega)) (by omega)
    exact ⟨res, s', e, r, fun hr => ⟨(h hr).1, (h hr).2.1, fun h' => ⟨_, _, fun e => absurd e hsp,
      s8R_mono ((h hr).2.2 h') (by omega)⟩⟩⟩

/-- the dictionary / free-list step of `became_alive` -/
def s8DS (s : sim.state.St) (i : Usize) (v1 : alloc.vec.Vec (Option Usize)) (FL : alloc.vec.Vec Usize) : Prop :=
  (s.free_list.val = [] → v1.val = s.dict_slots.val ++ [some i] ∧ FL.val = []) ∧
  (∀ L x, s.free_list.val = L ++ [x] → ∃ hx : x.val < s.dict_slots.val.length,
    v1 = s.dict_slots.set x (some i) ∧ FL.val = L)

theorem s8_ds (s : sim.state.St) (i : Usize) (v1 : alloc.vec.Vec (Option Usize))
    (hsmall : s.dict_slots.val.length < Usize.max) (hfree : ∀ x ∈ s.free_list.val, x.val < s.dict_slots.val.length)
    (ev1 : (match s.free_list.val.getLast? with
        | none => alloc.vec.Vec.push s.dict_slots (some i)
        | some slot => do
          let (_, index_mut_back) ←
            alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice (Option Usize)) s.dict_slots slot
          ok (index_mut_back (some i))) = ok v1)
    (FL : alloc.vec.Vec Usize) (hFL : FL.val = s.free_list.val.dropLast) : s8DS s i v1 FL := by
  constructor
  · intro h
    simp only [h, List.getLast?_nil] at ev1
    rw [vec_push_ok _ _ hsmall] at ev1
    simp only [ok.injEq] at ev1
    refine ⟨by rw [← ev1]; simp, by rw [hFL, h]; rfl⟩
  · intro L x h
    have hx : x.val < s.dict_slots.val.length := hfree x (by rw [h]; simp)
    simp only [h, List.getLast?_append, List.getLast?_singleton, Option.some_or] at ev1
    rw [vec_index_mut_eq _ _ hx] at ev1
    simp only [bind_ok, uncurry_apply_pair, ok.injEq] at ev1
    exact ⟨hx, ev1.symm, by rw [hFL, h]; simp⟩

-- CONDITIONAL: step-invariant premises (free list in range, capacities, 6 pools, simPoolOk, simTfX + transformable budget for the two updateStateFromResult calls); hC/hCS are context premises (ev_ctxWF / sim_ar_cs)
theorem s8_became_alive_fr (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (s : sim.state.St) (i : Usize)
    (hi : i.val < c.pb.objects.val.length) (hinv : SimInv c s)
    (hfree : ∀ x ∈ s.free_list.val, x.val < s.dict_slots.val.length)
    (hds : s.dict_slots.val.length + 1 < Usize.max)
    (hact : s.active.val.length < Usize.max) (hcc : s.child_counter.val + 1 ≤ U64.max)
    (hpl : 6 ≤ s.pools.val.length) (hcap : s.insts.val.length + 2 + (c.pb.objects.val[i.val]'hi).nested.val.length < Usize.max)
    (hP : simPoolOk s) (hC : SimARCtx c)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (X : simTfX P) (b n : Nat) (hCS : simCSH P n tn fo c)
    (hTf : s3b_TfInv P (b + n + n + 4 + (n + n + 4)) s) (hB : b + n + n + 4 + (n + n + 4) + 1 < Usize.max) :
    ∃ res s', sim.step.became_alive c s i = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.becameAlive i.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimInv c s' ∧ s3b_TfInv P b s' ∧
        ∃ (k : Usize) (v1 : alloc.vec.Vec (Option Usize)) (FL v2 : alloc.vec.Vec Usize) (cid : U64),
          s8DS s i v1 FL ∧ v2.val = s.active.val ++ [i] ∧ cid.val = s.child_counter.val + 1 ∧
          ∀ h : i.val < s.objs.val.length, ∃ T TL, ((c.pb.objects.val[i.val]'hi).h.kind = .Spinner → T = (c.pb.objects.val[i.val]'hi).nested.val.length ∧ TL = (c.pb.objects.val[i.val]'hi).nested.val.length) ∧
            s8R i (s8K (s.objs.val[i.val]'h) cid k) (c.pb.objects.val[i.val]'hi).nested.val.length ((c.pb.objects.val[i.val]'hi).nested.val.length + 2) T TL
            { s with active := v2, dict_slots := v1, free_list := FL, child_counter := cid } s') := by
  rw [sim_ba_split, sim_ba_splitS]
  obtain ⟨v1, ev1, snil, scons, mv1⟩ := sim_ba_dict2 tn s i hinv.dict_small hfree
  obtain ⟨FL, epop, hFL⟩ : ∃ FL, alloc.vec.Vec.pop alloc.alloc.Global s.free_list =
      ok (s.free_list.val.getLast?, FL) ∧ FL.val = s.free_list.val.dropLast :=
    ⟨_, rfl, by simp [alloc.vec.Vec.from_val]⟩
  have hDS : s8DS s i v1 FL := s8_ds s i v1 hinv.dict_small hfree ev1 FL hFL
  obtain ⟨cid, ecid, vcid⟩ := sim_u64_add_one s.child_counter hcc
  obtain ⟨v2, ev2, vv2⟩ : ∃ v, alloc.vec.Vec.push s.active i = ok v ∧ v.val = s.active.val ++ [i] :=
    ⟨_, vec_push_ok _ _ hact, by simp⟩
  obtain ⟨pk, epk, spk⟩ := sim.step.pool_kind_refines (c.pb.objects.val[i.val]'hi).h.kind
  simp only [simM_bind, s3b_topObj tn fo c _ i.val hi, Except.bind, OsuModel.Sim.Sim.st, simM_get,
    vec_index_eq _ _ hi, bind_ok, epop, uncurry_apply_pair]
  have hfl : (simStS tn s).freeList = (s.free_list.val.map (·.val)).reverse := rfl
  have hS0 := sim_stS_ba tn s i v1 FL v2 cid vv2 vcid
  rcases hg : s.free_list.val.getLast? with _ | x
  on_goal 1 =>
    rw [List.getLast?_eq_none_iff] at hg
    have hfl0 : (simStS tn s).freeList = [] := by rw [hfl, hg]; rfl
    obtain ⟨h1, -⟩ := snil hfl0
    have hFL0 : (FL.val.map (fun x => x.val)).reverse = [] := by simp [hFL, hg]
    rw [hFL0] at hS0
    simp only [hg, List.getLast?_nil] at ev1
    have hv1l : v1.val.length ≤ s.dict_slots.val.length + 1 := by
      have e := ev1; rw [vec_push_ok _ _ hinv.dict_small] at e; simp only [ok.injEq] at e; rw [← e]; simp
    simp only [ev1, ecid, ev2, epk, bind_ok, hfl0, simM_bind, simM_pure, h1, Except.bind, ← hS0, simM_set, simM_get]
  on_goal 2 =>
    have hx : x.val < s.dict_slots.val.length := hfree x (List.mem_of_getLast? hg)
    obtain ⟨L, hL⟩ : ∃ L, s.free_list.val = L ++ [x] := ⟨_, (List.dropLast_append_getLast? _ hg).symm⟩
    have hfl1 : (simStS tn s).freeList = x.val :: (L.map (·.val)).reverse := by rw [hfl, hL]; simp
    obtain ⟨h1, h2⟩ := scons _ _ hfl1
    have hFL1 : (FL.val.map (fun x => x.val)).reverse = (L.map (·.val)).reverse := by simp [hFL, hL]
    rw [hFL1] at hS0
    simp only [hg] at ev1
    have hv1l : v1.val.length ≤ s.dict_slots.val.length + 1 := by
      have e := ev1; simp only [vec_index_mut_eq _ _ hx, bind_ok, uncurry_apply_pair, ok.injEq] at e; rw [← e]; simp [vec_set_val']
    simp only [ev1, ecid, ev2, epk, bind_ok, hfl1, simM_bind, simM_pure, h1, Except.bind, ← hS0, simM_set, simM_get]
  all_goals
    have hpk : pk.val < 6 := by
      cases hkd : (c.pb.objects.val[i.val]'hi).h.kind <;> rw [hkd] at epk <;>
        simp [sim.step.pool_kind] at epk <;> subst epk <;> decide
    obtain ⟨k, s1, ek, sk, hfr, hpl1, hins, hk⟩ := sim.step.pool_get_refines tn fo c
      { s with active := v2, dict_slots := v1, free_list := FL, child_counter := cid } pk (by simp; omega)
      (by simp; omega)
    have hpkS : OsuModel.Sim.Sim.poolKind (topS tn (c.pb.objects.val[i.val]'hi)).h.kind = pk.val := by
      first | exact spk | simpa [abs] using spk
    obtain ⟨k', s1', ek', -, -, -, hkl', hP1, -⟩ := sim_pool_get_ok
      { s with active := v2, dict_slots := v1, free_list := FL, child_counter := cid } pk (by simp; omega)
      (by simp; omega) hP
    rw [ek] at ek'; simp only [ok.injEq, Prod.mk.injEq] at ek'; obtain ⟨hk', hs1'⟩ := ek'; subst hk'; subst hs1'
    simp only [ek, bind_ok, uncurry_apply_pair, hpkS, sk]
    obtain ⟨ins1, pl1, hs1⟩ := hfr
    have hinv1 : SimInv c s1 := by
      rw [hs1]
      refine ⟨hinv.objs_len, hinv.nested_len, hinv.nested_small, ?_, by simp; omega⟩
      intro o ho x hx
      rcases mv1 o ho with ho | ho
      · exact hinv.dict_in o ho x hx
      · subst ho; cases hx; exact hi
    have hTf1 : s3b_TfInv P (b + n + n + 4 + (n + n + 4)) s1 := sim_tf_pg X hB hTf (by
      rcases hins with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, trivial⟩)
    have hcap1 : s1.insts.val.length + 1 + (c.pb.objects.val[i.val]'hi).nested.val.length < Usize.max := by
      rcases hins with h | ⟨h, -⟩ <;> rw [h] <;> simp <;> omega
    obtain ⟨res, s', e', r', h'⟩ := s8_ba_tail tn fo c s1 i hi hinv1 cid k hkl' (by rw [hpl1]; exact hpl) hP1 hcap1 hC E X b n
      hCS hTf1 hB
    refine ⟨res, s', e', r', fun hr => ?_⟩
    obtain ⟨hA, hB', hR⟩ := h' hr
    refine ⟨hA, hB', k, v1, FL, v2, cid, hDS, vv2, vcid, fun h => ?_⟩
    have hl1 : ({ s with active := v2, dict_slots := v1, free_list := FL, child_counter := cid } : sim.state.St).insts.val.length
        ≤ s1.insts.val.length := by rcases hins with h2 | ⟨h2, -⟩ <;> rw [h2] <;> simp
    have hl2 : s1.insts.val.length ≤
        ({ s with active := v2, dict_slots := v1, free_list := FL, child_counter := cid } : sim.state.St).insts.val.length + 1 := by
      rcases hins with h2 | ⟨h2, -⟩ <;> rw [h2] <;> simp
    subst hs1
    obtain ⟨T, TL, hTs, hRh⟩ := hR h
    exact ⟨T, TL, hTs, s8R_mono (s8R_base _ _ ⟨ins1, pl1, rfl⟩ hl1 hl2 hpl1 hRh) (by omega)⟩



/-! ## lifetime invariant transitions -/

end OsuProofs
