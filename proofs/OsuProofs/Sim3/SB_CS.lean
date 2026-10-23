/-
Sim3b part 9 (sim3c: Wiggle handled via Sim3/SC_Wiggle, strong frame `s3c_ito`): `custom_state` (the `ApplyCustomUpdateState` handlers of the visibility mods) refines
`Sim.customState`: loop lockstep `s3b_cs_loop` (Rust `custom_state_loop` vs the spec `for hv : vi in [0:n]`), and the
per-handler steps (`custom_state_one`).
-/
import OsuProofs.Sim3.SC_Wiggle
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

set_option hygiene false in
/-- split `custom_state_one`'s `increased` and the object kind, then close every case with `t` -/
macro "s3b_cs_split " t:tactic : tactic => `(tactic| (
  split
  · rename_i hf; simp only [hf, Option.map_none, s3b_none_beq, bind_ok]
    cases hK : h.kind <;> simp (config := {decide := true}) only [kindS, bind_ok, if_true, if_false,
      Bool.false_eq_true, Bool.true_or, Bool.false_or, Bool.or_false, Bool.or_true, Bool.not_true, Bool.not_false,
      ite_true, ite_false] <;> $t
  · rename_i f hf; simp only [hf, Option.map_some, s3b_some_beq, bind_ok]
    cases decide (f = i) <;> cases hK : h.kind <;> simp (config := {decide := true}) only [kindS, bind_ok, if_true,
      if_false, Bool.false_eq_true, Bool.true_or, Bool.false_or, Bool.or_false, Bool.or_true, Bool.not_true,
      Bool.not_false, ite_true, ite_false] <;> $t))

theorem s3b_cs_loop_step (c : sim.state.Ctx) (s s1 : sim.state.St) (i : Usize) (p : sim.step.Part) (state : sim.state.Armed)
    (fw : Bool) (h : sim.playable.HObj) (k : Usize) (now : F64) (vi vi1 : Usize) (hlt : vi < alloc.vec.Vec.len c.cfg.vis_mods)
    (h1 : sim.step.custom_state_one c s i p k h vi state fw now = ok s1) (h2 : vi + 1#usize = ok vi1) :
    sim.step.custom_state_loop c s i p state fw h k now vi = sim.step.custom_state_loop c s1 i p state fw h k now vi1 := by
  unfold sim.step.custom_state_loop; rw [loop_unfold]
  simp [sim.step.custom_state_loop.body, hlt, h1, h2]
theorem s3b_cs_loop_end (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (p : sim.step.Part) (state : sim.state.Armed)
    (fw : Bool) (h : sim.playable.HObj) (k : Usize) (now : F64) (vi : Usize) (hlt : ¬ vi < alloc.vec.Vec.len c.cfg.vis_mods) :
    sim.step.custom_state_loop c s i p state fw h k now vi = ok s := by
  unfold sim.step.custom_state_loop; rw [loop_unfold]
  simp [sim.step.custom_state_loop.body, hlt]

/-- loop lockstep of `custom_state` -/
theorem s3b_cs_loop (tn) (c : sim.state.Ctx) (i : Usize) (p : sim.step.Part) (state : sim.state.Armed) (fw : Bool)
    (h : sim.playable.HObj) (k : Usize) (now : F64) (C : OsuModel.Sim.Ctx) (Inv : Nat → sim.state.St → Prop)
    (n : Nat) (hn : n = c.cfg.vis_mods.val.length)
    (F : (j : Nat) → j ∈ [:n] → PUnit → OsuModel.Sim.SimM (ForInStep PUnit))
    (hstep : ∀ (vi : Usize) (hm : vi.val ∈ [:n]) s, Inv vi.val s →
      ∃ s', sim.step.custom_state_one c s i p k h vi state fw now = ok s' ∧
        F vi.val hm PUnit.unit C (simStS tn s) = .ok (.yield PUnit.unit, simStS tn s') ∧ Inv (vi.val + 1) s') :
    ∀ s, Inv 0 s → ∃ s', sim.step.custom_state_loop c s i p state fw h k now 0#usize = ok s' ∧
      forIn' [:n] PUnit.unit F C (simStS tn s) = .ok (PUnit.unit, simStS tn s') ∧
      Inv c.cfg.vis_mods.val.length s' := by
  subst hn
  have hmax := c.cfg.vis_mods.property
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  suffices H : ∀ m (vi : Usize) (hvi : vi.val + m = c.cfg.vis_mods.val.length), ∀ s, Inv vi.val s → ∃ s',
      sim.step.custom_state_loop c s i p state fw h k now vi = ok s' ∧
      forIn' (List.range' vi.val m) PUnit.unit (fun a ha => F a (by
        exact ⟨Nat.zero_le _, by simp [List.mem_range'] at ha; show a < c.cfg.vis_mods.val.length; omega, Nat.mod_one _⟩)) C (simStS tn s) = .ok (PUnit.unit, simStS tn s') ∧ Inv c.cfg.vis_mods.val.length s' by
    intro s hs
    obtain ⟨s', h1, h2, h3⟩ := H c.cfg.vis_mods.val.length 0#usize (by simp) s hs
    exact ⟨s', h1, h2, h3⟩
  intro m
  induction m with
  | zero =>
    intro vi hvi s hs
    have : ¬ vi < alloc.vec.Vec.len c.cfg.vis_mods := by rw [vec_lt_len_iff]; omega
    exact ⟨s, s3b_cs_loop_end c s i p state fw h k now vi this, rfl, by rw [← hvi]; simpa using hs⟩
  | succ m ih =>
    intro vi hvi s hs
    have hlt : vi < alloc.vec.Vec.len c.cfg.vis_mods := by rw [vec_lt_len_iff]; omega
    obtain ⟨vi1, hvi1, hvi1v⟩ := usize_add_one vi (by omega)
    have hm : vi.val ∈ [:c.cfg.vis_mods.val.length] := ⟨Nat.zero_le _, by show vi.val < c.cfg.vis_mods.val.length; omega, Nat.mod_one _⟩
    obtain ⟨s1, hs1, es1, is1⟩ := hstep vi hm s hs
    obtain ⟨s', h1, h2, h3⟩ := ih vi1 (by omega) s1 (by rw [hvi1v]; exact is1)
    refine ⟨s', by rw [s3b_cs_loop_step c s s1 i p state fw h k now vi vi1 hlt hs1 hvi1]; exact h1, ?_, h3⟩
    simp only [List.range'_succ, List.forIn'_cons, simM_bind]
    rw [es1]
    simp only [s3b_ebok]
    simp only [hvi1v] at h2
    exact h2

theorem s3b_bind_unit (x : OsuModel.Sim.SimM PUnit) (C : OsuModel.Sim.Ctx) (S S' : OsuModel.Sim.St)
    (h : x C S = .ok (PUnit.unit, S')) : (x >>= fun _ => pure ()) C S = .ok ((), S') := by
  rw [simM_bind, h]; rfl

theorem s3b_cs_loop' (tn) (c : sim.state.Ctx) (i : Usize) (p : sim.step.Part) (state : sim.state.Armed) (fw : Bool)
    (h : sim.playable.HObj) (k : Usize) (now : F64) (C : OsuModel.Sim.Ctx) (Inv : Nat → sim.state.St → Prop)
    (n : Nat) (hn : n = c.cfg.vis_mods.val.length)
    (F : (j : Nat) → j ∈ [:n] → PUnit → OsuModel.Sim.SimM (ForInStep PUnit))
    (hstep : ∀ (vi : Usize) (hm : vi.val ∈ [:n]) s, Inv vi.val s →
      ∃ s', sim.step.custom_state_one c s i p k h vi state fw now = ok s' ∧
        F vi.val hm PUnit.unit C (simStS tn s) = .ok (.yield PUnit.unit, simStS tn s') ∧ Inv (vi.val + 1) s')
    (s : sim.state.St) (hs : Inv 0 s) (Q : sim.state.St → Prop) (hQ : ∀ s', Inv c.cfg.vis_mods.val.length s' → Q s') :
    ∃ s', sim.step.custom_state_loop c s i p state fw h k now 0#usize = ok s' ∧
      (forIn' [:n] PUnit.unit F >>= fun _ => pure ()) C (simStS tn s) = .ok ((), simStS tn s') ∧ Q s' := by
  obtain ⟨s', h1, h2, h3⟩ := s3b_cs_loop tn c i p state fw h k now C Inv n hn F hstep s hs
  exact ⟨s', h1, s3b_bind_unit _ _ _ _ h2, hQ s' h3⟩

@[simp] theorem s3b_F32_1C : sim.step.F32_1C = ok (1 : F32) := by unfold sim.step.F32_1C; simp; decide +kernel
@[simp] theorem s3b_F32_0_5C : sim.step.F32_0_5C = ok (0.5 : F32) := by unfold sim.step.F32_0_5C; simp <;> decide +kernel
@[simp] theorem s3b_F32_360C : sim.step.F32_360C = ok (360 : F32) := by unfold sim.step.F32_360C; simp; decide +kernel
@[simp] theorem s3b_F32_2C : sim.step.F32_2C = ok (2 : F32) := by unfold sim.step.F32_2C; simp; decide +kernel
@[simp] theorem s3b_v_xy (x y : F32) : sim.step.v_xy x y = ok ⟨x, y⟩ := rfl

/-- `ScaleTween`'s block (`OsuModScaleTween`): 2 transforms -/
theorem s3b_cs_scale (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b : Nat) (c : sim.state.Ctx)
    (s : sim.state.St) (k : Usize) (hk : k.val < s.insts.val.length) (now t pre : F64) (sc : F32)
    (hinv : SimInv c s) (hP : s3b_TfInv P (b + 2) s) :
    ∃ s', (do
          let (saved, s1) ← sim.step.with_abs_begin s k now t
          let (i1, index_mut_back) ←
            alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice sim.state.Inst) s1.insts k
          let v ← sim.step.v_xy sc sc
          let f ← sim.step.F64_0
          let (sq, tf) ←
            sim.transforms.transform_to i1.tf now sim.transforms.Member.Scale v f net.framework.Easing.None none
          let s2 ← sim.transforms.seq_then sq
          let f1 ← sim.step.F32_1C
          let v1 ← sim.step.v_xy f1 f1
          let (_, tf1) ←
            sim.transforms.seq_append s2 tf now sim.transforms.Member.Scale v1 pre net.framework.Easing.OutSine none
          sim.step.with_abs_end { s1 with insts := index_mut_back { i1 with tf := tf1 } } k saved) = ok s' ∧
      OsuModel.Sim.Sim.withAbs k.val now t (fun tf =>
        ((OsuModel.Sim.transformTo tf now .scale ⟨sc, sc⟩ 0).2.then_.append
          (OsuModel.Sim.transformTo tf now .scale ⟨sc, sc⟩ 0).1 now .scale ⟨1, 1⟩ pre .outSine).1)
        (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧ s3b_csPost P b c s s' := by
  have hT0 : P (b + 2) { (s.insts.val[k.val]'hk).tf with delay := t - now } :=
    E.delay _ _ _ (hP _ (List.getElem_mem hk)).1
  dsimp only at hT0
  obtain ⟨sq, tf, h1, e1, p1⟩ := E.tto (b + 1) _ now .Scale ⟨sc, sc⟩ 0 .None none hT0
  obtain ⟨s2, h2, e2⟩ := sim.transforms.seq_then_refines sq
  obtain ⟨sq', tf1, h3, e3, p3⟩ := E.app b s2 tf now .Scale ⟨1, 1⟩ pre .OutSine none p1
  refine ⟨s3b_waSt s k hk tf1, ?_, ?_⟩
  · simp only [sim.step.with_abs_begin_eq _ _ _ _ hk, bind_ok, s3b_index_mut_set _ _ _ hk,
      s3b_v_xy, sim_step_F64_0, h1, h2, s3b_F32_1C, h3, uncurry_apply_pair]
    exact s3b_waR_end s k hk _ tf1
  · refine s3b_wa tn fo E b (b + 2) (by omega) c s k hk now t _ tf1 hinv hP ?_ p3
    have e1c : OsuModel.Sim.transformTo (abs { (s.insts.val[k.val]'hk).tf with delay := t - now }) now .scale ⟨sc, sc⟩ 0 =
      (abs tf, abs sq) := e1
    rw [e1c]; dsimp only; rw [e2]; exact congrArg Prod.fst e3

/-- `TargetPractice`'s block (`OsuModTargetPractice`): 2 transforms -/
theorem s3b_cs_tp (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b : Nat) (c : sim.state.Ctx)
    (s : sim.state.St) (k : Usize) (hk : k.val < s.insts.val.length) (now t pre : F64)
    (hinv : SimInv c s) (hP : s3b_TfInv P (b + 2) s) :
    ∃ s', (do
          let (saved, s1) ← sim.step.with_abs_begin s k now t
          let (i1, index_mut_back) ←
            alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice sim.state.Inst) s1.insts k
          let f ← sim.step.F32_0_5C
          let v ← sim.step.v_xy f f
          let f1 ← sim.step.F64_0
          let (_, tf) ← sim.transforms.transform_to i1.tf now sim.transforms.Member.Scale v f1 net.framework.Easing.None none
          let f2 ← sim.step.F32_1C
          let v1 ← sim.step.v_xy f2 f2
          let (_, tf1) ← sim.transforms.transform_to tf now sim.transforms.Member.Scale v1 pre net.framework.Easing.None none
          sim.step.with_abs_end { s1 with insts := index_mut_back { i1 with tf := tf1 } } k saved) = ok s' ∧
      OsuModel.Sim.Sim.withAbs k.val now t (fun tf =>
        let tf := (OsuModel.Sim.transformTo tf now .scale ⟨0.5, 0.5⟩ 0).1
        (OsuModel.Sim.transformTo tf now .scale ⟨1, 1⟩ pre).1)
        (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧ s3b_csPost P b c s s' := by
  have hT0 : P (b + 2) { (s.insts.val[k.val]'hk).tf with delay := t - now } :=
    E.delay _ _ _ (hP _ (List.getElem_mem hk)).1
  dsimp only at hT0
  obtain ⟨sq, tf, h1, e1, p1⟩ := E.tto (b + 1) _ now .Scale ⟨0.5, 0.5⟩ 0 .None none hT0
  obtain ⟨sq', tf1, h3, e3, p3⟩ := E.tto b tf now .Scale ⟨1, 1⟩ pre .None none p1
  refine ⟨s3b_waSt s k hk tf1, ?_, ?_⟩
  · simp only [sim.step.with_abs_begin_eq _ _ _ _ hk, bind_ok, s3b_index_mut_set _ _ _ hk,
      s3b_v_xy, sim_step_F64_0, h1, s3b_F32_0_5C, s3b_F32_1C, h3, uncurry_apply_pair]
    exact s3b_waR_end s k hk _ tf1
  · refine s3b_wa tn fo E b (b + 2) (by omega) c s k hk now t _ tf1 hinv hP ?_ p3
    have e1c : OsuModel.Sim.transformTo (abs { (s.insts.val[k.val]'hk).tf with delay := t - now }) now .scale ⟨0.5, 0.5⟩ 0 =
      (abs tf, abs sq) := e1
    dsimp only; rw [e1c]; exact congrArg Prod.fst e3

/-- `ClassicEarlyFade`'s block (`OsuModClassic`): 1 transform -/
theorem s3b_cs_cef (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b : Nat) (c : sim.state.Ctx)
    (s : sim.state.St) (k : Usize) (hk : k.val < s.insts.val.length) (now t okv mehv : F64)
    (hinv : SimInv c s) (hP : s3b_TfInv P (b + 1) s) :
    ∃ s', (do
          let (saved, s1) ← sim.step.with_abs_begin s k now t
          let (i1, index_mut_back) ←
            alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice sim.state.Inst) s1.insts k
          let d ← sim.transforms.delay_seq i1.tf now okv
          let f ← sim.basic.F32_0
          let v ← sim.transforms.vs f
          let (_, tf) ← sim.transforms.seq_append d i1.tf now sim.transforms.Member.Alpha v (mehv - okv) net.framework.Easing.None none
          sim.step.with_abs_end { s1 with insts := index_mut_back { i1 with tf } } k saved) = ok s' ∧
      OsuModel.Sim.Sim.withAbs k.val now t (fun tf =>
        ((OsuModel.Sim.delaySeq tf now okv).append tf now .alpha (OsuModel.Sim.vs 0) (mehv - okv)).1)
        (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧ s3b_csPost P b c s s' := by
  have hT0 : P (b + 1) { (s.insts.val[k.val]'hk).tf with delay := t - now } :=
    E.delay _ _ _ (hP _ (List.getElem_mem hk)).1
  dsimp only at hT0
  obtain ⟨d, hd, ed⟩ := sim.transforms.delay_seq_refines { (s.insts.val[k.val]'hk).tf with delay := t - now } now okv
  obtain ⟨sq', tf1, h3, e3, p3⟩ := E.app b d _ now .Alpha ⟨0, 0⟩ (mehv - okv) .None none hT0
  refine ⟨s3b_waSt s k hk tf1, ?_, ?_⟩
  · simp only [sim.step.with_abs_begin_eq _ _ _ _ hk, bind_ok, s3b_index_mut_set _ _ _ hk, hd, sim_basic_F32_0, s3b_vs,
      float.F64.sub, h3, uncurry_apply_pair]
    exact s3b_waR_end s k hk _ tf1
  · refine s3b_wa tn fo E b (b + 1) (by omega) c s k hk now t _ tf1 hinv hP ?_ p3
    dsimp only; rw [ed]; exact congrArg Prod.fst e3

/-- one `transformTo alpha 0` block (`OsuModHidden` circles/heads/spinners): 1 transform -/
theorem s3b_cs_fade (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b : Nat) (c : sim.state.Ctx)
    (s : sim.state.St) (k : Usize) (hk : k.val < s.insts.val.length) (now t fd : F64)
    (hinv : SimInv c s) (hP : s3b_TfInv P (b + 1) s) :
    ∃ s', (do
          let (saved, s1) ← sim.step.with_abs_begin s k now t
          let (i, index_mut_back) ←
            alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice sim.state.Inst) s1.insts k
          let f2 ← sim.basic.F32_0
          let v ← sim.transforms.vs f2
          let (_, t1) ← sim.transforms.transform_to i.tf now sim.transforms.Member.Alpha v fd net.framework.Easing.None none
          sim.step.with_abs_end { s1 with insts := index_mut_back { i with tf := t1 } } k saved) = ok s' ∧
      OsuModel.Sim.Sim.withAbs k.val now t (fun tf => (OsuModel.Sim.transformTo tf now .alpha (OsuModel.Sim.vs 0) fd).1)
        (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧ s3b_csPost P b c s s' := by
  have hT0 : P (b + 1) { (s.insts.val[k.val]'hk).tf with delay := t - now } :=
    E.delay _ _ _ (hP _ (List.getElem_mem hk)).1
  dsimp only at hT0
  obtain ⟨sq', tf1, h3, e3, p3⟩ := E.tto b _ now .Alpha ⟨0, 0⟩ fd .None none hT0
  refine ⟨s3b_waSt s k hk tf1, ?_, ?_⟩
  · simp only [sim.step.with_abs_begin_eq _ _ _ _ hk, bind_ok, s3b_index_mut_set _ _ _ hk, sim_basic_F32_0, s3b_vs,
      h3, uncurry_apply_pair]
    exact s3b_waR_end s k hk _ tf1
  · refine s3b_wa tn fo E b (b + 1) (by omega) c s k hk now t _ tf1 hinv hP ?_ p3
    exact congrArg Prod.fst e3

/-- `Hidden` on a slider: fades the body (`OsuModHidden`, `modifyInst` on `bodyTf`): 1 transform -/
theorem s3b_cs_hidsl (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b : Nat) (c : sim.state.Ctx)
    (s : sim.state.St) (k : Usize) (hk : k.val < s.insts.val.length) (now fs ld : F64)
    (hinv : SimInv c s) (hP : s3b_TfInv P (b + 1) s) :
    ∃ s', (do
          let i ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.state.Inst) s.insts k
          let (i1, index_mut_back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice sim.state.Inst) s.insts k
          let t ← sim.transforms.abs_seq i1.body_tf now fs
          let (i2, index_mut_back1) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice sim.state.Inst)
            (index_mut_back { i1 with body_tf := t }) k
          let f2 ← sim.basic.F32_0
          let v1 ← sim.transforms.vs f2
          let (_, t1) ← sim.transforms.transform_to i2.body_tf now sim.transforms.Member.Alpha v1 ld net.framework.Easing.Out none
          let (i3, index_mut_back2) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice sim.state.Inst)
            (index_mut_back1 { i2 with body_tf := t1 }) k
          ok { s with insts := index_mut_back2 { i3 with body_tf := { i3.body_tf with delay := i.body_tf.delay } } }) = ok s' ∧
      OsuModel.Sim.Sim.modifyInst k.val (fun ins =>
          let b := OsuModel.Sim.absSeq ins.bodyTf now fs
          { ins with bodyTf := { (OsuModel.Sim.transformTo b now .alpha (OsuModel.Sim.vs 0) ld .out).1 with delay := ins.bodyTf.delay } })
        (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧ s3b_csPost P b c s s' := by
  have hB : P (b + 1) { (s.insts.val[k.val]'hk).body_tf with delay := fs - now } :=
    E.delay _ _ _ (hP _ (List.getElem_mem hk)).2
  dsimp only at hB
  have hr : sim.transforms.abs_seq (s.insts.val[k.val]'hk).body_tf now fs =
      ok { (s.insts.val[k.val]'hk).body_tf with delay := fs - now } := by
    simp [sim.transforms.abs_seq, float.F64.sub]
  obtain ⟨sq, t1, h1, e1, p1⟩ := E.tto b _ now .Alpha ⟨0, 0⟩ ld .Out none hB
  let B : sim.state.Inst := { s.insts.val[k.val]'hk with
    body_tf := { t1 with delay := (s.insts.val[k.val]'hk).body_tf.delay } }
  have hk' : k.val < (simStS tn s).insts.size := by simpa [s3b_stS_insts] using hk
  refine ⟨{ s with insts := s.insts.set k B }, ?_, ?_, s3b_inv_objs hinv rfl (fun _ _ _ => rfl) rfl, ?_,
    by simp [vec_set_val'], rfl, rfl⟩
  · simp only [vec_index_eq _ _ hk, vec_index_mut_eq _ _ hk, hr, bind_ok, s3b_index_mut_set _ _ _ hk, sim_basic_F32_0,
      s3b_vs, h1, uncurry_apply_pair, s3b_index_mut_set2 _ _ _ _ hk]
    congr 2
    refine alloc.vec.Vec.ext _ _ ?_
    simp [vec_set_val', B]
  · rw [s3b_modifyInst_ok _ _ _ _ hk']
    have hS : simStS tn { s with insts := s.insts.set k B } =
        { simStS tn s with insts := ((s.insts.set k B).val.map (fun x => (abs x : OsuModel.Sim.Inst))).toArray } := rfl
    rw [hS]
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and]
    congr 1
    rw [s3b_stS_insts, s3b_arr_modify_toArray _ _ _ hk, vec_set_val', List.map_set]
    congr 2
    have e2 : ∀ X, X = (abs (s.insts.val[k.val]'hk) : OsuModel.Sim.Inst) →
        (OsuModel.Sim.transformTo (OsuModel.Sim.absSeq X.bodyTf now fs) now .alpha (OsuModel.Sim.vs 0) ld .out).1 = abs t1 := by
      rintro X rfl; exact congrArg Prod.fst e1
    rw [e2 _ rfl]; rfl
  · exact s3b_tfinv_set2 E (by omega : b ≤ b + 1) hP k B (by simp only [vec_set_val'])
      ⟨E.mono _ _ _ (by omega) (hP _ (List.getElem_mem hk)).1, E.delay _ _ _ p1⟩

/-- the spec's `SpinIn` circle/head block -/
def s3b_spinC (now pre : F64) (st : OsuModel.Sim.Armed) (tf : OsuModel.Sim.TObj) : OsuModel.Sim.TObj :=
  let A := OsuModel.Sim.transformTo tf now .rotation (OsuModel.Sim.vs 360) 0
  let B := (A.2.then_.append A.1 now .rotation (OsuModel.Sim.vs 0) pre .inOutSine).1
  let C := OsuModel.Sim.transformTo B now .scale ⟨2, 0⟩ 0
  let D := (C.2.then_.append C.1 now .scale ⟨1, 1⟩ pre .inOutSine).1
  if (st == .idle) = true then (OsuModel.Sim.transformTo D now .alpha (OsuModel.Sim.vs 1) 0).1 else D

/-- `SpinIn` on a circle/head (`OsuModSpinIn`): 5 transforms -/
theorem s3b_cs_spinC (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b : Nat) (c : sim.state.Ctx)
    (s : sim.state.St) (k : Usize) (hk : k.val < s.insts.val.length) (h : sim.playable.HObj) (K : sim.playable.Kind)
    (state : sim.state.Armed) (now : F64)
    (hinv : SimInv c s) (hP : s3b_TfInv P (b + 5) s) (hK : (kindS K == .circle || kindS K == .head) = true)
    (Q : sim.state.St → Prop) (hQ : ∀ s', s3b_csPost P b c s s' → Q s') :
    ∃ s', sim.step.spin_in_state s k h K state now = ok s' ∧
      (OsuModel.Sim.Sim.withAbs k.val now (h.start - h.preempt) (s3b_spinC now h.preempt (abs state)) >>=
        fun _ => pure (ForInStep.yield PUnit.unit) : OsuModel.Sim.SimM (ForInStep PUnit))
        (simCtxS tn fo c) (simStS tn s) = .ok (ForInStep.yield PUnit.unit, simStS tn s') ∧ Q s' := by
  have hT0 : P (b + 5) { (s.insts.val[k.val]'hk).tf with delay := h.start - h.preempt - now } :=
    E.delay _ _ _ (hP _ (List.getElem_mem hk)).1
  dsimp only at hT0
  obtain ⟨sq, tf, h1, e1, p1⟩ := E.tto (b + 4) _ now .Rotation ⟨360, 0⟩ 0 .None none hT0
  obtain ⟨s2, h2, e2⟩ := sim.transforms.seq_then_refines sq
  obtain ⟨sq', tf1, h3, e3, p3⟩ := E.app (b + 3) s2 tf now .Rotation ⟨0, 0⟩ h.preempt .InOutSine none p1
  obtain ⟨sq2, tf2, h4, e4, p4⟩ := E.tto (b + 2) tf1 now .Scale ⟨2, 0⟩ 0 .None none p3
  obtain ⟨s3, h5, e5⟩ := sim.transforms.seq_then_refines sq2
  obtain ⟨sq3, tf3, h6, e6, p6⟩ := E.app (b + 1) s3 tf2 now .Scale ⟨1, 1⟩ h.preempt .InOutSine none p4
  obtain ⟨sq4, tf5, h7, e7, p7⟩ := E.tto b tf3 now .Alpha ⟨1, 0⟩ 0 .None none p6
  have e1c : OsuModel.Sim.transformTo (abs { (s.insts.val[k.val]'hk).tf with delay := h.start - h.preempt - now }) now
    .rotation (OsuModel.Sim.vs 360) 0 = (abs tf, abs sq) := e1
  have e3c : ((abs s2 : OsuModel.Sim.Seq).append (abs tf) now .rotation (OsuModel.Sim.vs 0) h.preempt .inOutSine) =
    (abs tf1, abs sq') := e3
  have e4c : OsuModel.Sim.transformTo (abs tf1) now .scale ⟨2, 0⟩ 0 = (abs tf2, abs sq2) := e4
  have e6c : ((abs s3 : OsuModel.Sim.Seq).append (abs tf2) now .scale ⟨1, 1⟩ h.preempt .inOutSine) = (abs tf3, abs sq3) := e6
  have e7c : OsuModel.Sim.transformTo (abs tf3) now .alpha (OsuModel.Sim.vs 1) 0 = (abs tf5, abs sq4) := e7
  have hspec : s3b_spinC now h.preempt (abs state) (abs { (s.insts.val[k.val]'hk).tf with delay := h.start - h.preempt - now }) =
      abs (if (armedS state == .idle) = true then tf5 else tf3) := by
    unfold s3b_spinC; dsimp only
    rw [e1c]; dsimp only; rw [e2, e3c]; dsimp only; rw [e4c]; dsimp only; rw [e5, e6c]; dsimp only; rw [e7c]
    show (if (armedS state == .idle) = true then _ else _) = _
    split <;> rfl
  have pF : P b (if (armedS state == .idle) = true then tf5 else tf3) := by
    split
    · exact p7
    · exact E.mono _ _ _ (by omega) p6
  obtain ⟨hw, hpost⟩ := s3b_wa tn fo E b (b + 5) (by omega) c s k hk now (h.start - h.preempt) _ _ hinv hP hspec pF
  refine ⟨s3b_waSt s k hk (if (armedS state == .idle) = true then tf5 else tf3), ?_, s3b_cs_yield _ _ _ _ hw, hQ _ hpost⟩
  cases K <;> simp (config := {decide := true}) [kindS] at hK <;> (
    unfold sim.step.spin_in_state
    simp only [float.F64.sub, kind_eq_ok, kindS, bind_ok, sim.step.with_abs_begin_eq _ _ _ _ hk, s3b_index_mut_set _ _ _ hk,
      s3b_F32_360C, s3b_vs, sim_step_F64_0, h1, h2, sim_basic_F32_0, h3, sim_basic_F32_2, s3b_v_xy, h4, h5, s3b_F32_1C, h6,
      armed_eq_ok, uncurry_apply_pair]
    simp (config := {decide := true}) only [if_true, if_false, Bool.false_eq_true, bind_ok]
    cases state <;> simp (config := {decide := true}) only [armedS, if_true, if_false, Bool.false_eq_true, bind_ok,
      s3b_vs, h7, uncurry_apply_pair] <;> exact s3b_waR_end s k hk _ _)

theorem s3b_tfinv_mono {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) {b b' : Nat} (hb : b' ≤ b)
    {s : sim.state.St} (h : s3b_TfInv P b s) : s3b_TfInv P b' s :=
  fun ins hins => ⟨E.mono _ _ _ hb (h ins hins).1, E.mono _ _ _ hb (h ins hins).2⟩
theorem s3b_none_beq (x : Nat) : ((none : Option Nat) == some x) = false := rfl
theorem s3b_some_beq (f i : Usize) : (some f.val == some i.val) = decide (f = i) := by
  by_cases e : f.val = i.val <;> simp [e, UScalar.eq_equiv]

/-- the spec's `SpinIn` slider block -/
def s3b_spinS (now pre : F64) (st : OsuModel.Sim.Armed) (tf : OsuModel.Sim.TObj) : OsuModel.Sim.TObj :=
  let C := OsuModel.Sim.transformTo tf now .scale ⟨0, 0⟩ 0
  let D := (C.2.then_.append C.1 now .scale ⟨1, 1⟩ pre .inOutSine).1
  if (st == .idle) = true then (OsuModel.Sim.transformTo D now .alpha (OsuModel.Sim.vs 1) 0).1 else D

/-- `SpinIn` on a slider: 3 transforms -/
theorem s3b_cs_spinS (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b : Nat) (c : sim.state.Ctx)
    (s : sim.state.St) (k : Usize) (hk : k.val < s.insts.val.length) (h : sim.playable.HObj)
    (state : sim.state.Armed) (now : F64)
    (hinv : SimInv c s) (hP : s3b_TfInv P (b + 3) s)
    (Q : sim.state.St → Prop) (hQ : ∀ s', s3b_csPost P b c s s' → Q s') :
    ∃ s', sim.step.spin_in_state s k h .Slider state now = ok s' ∧
      (OsuModel.Sim.Sim.withAbs k.val now (h.start - h.preempt) (s3b_spinS now h.preempt (abs state)) >>=
        fun _ => pure (ForInStep.yield PUnit.unit) : OsuModel.Sim.SimM (ForInStep PUnit))
        (simCtxS tn fo c) (simStS tn s) = .ok (ForInStep.yield PUnit.unit, simStS tn s') ∧ Q s' := by
  have hT0 : P (b + 3) { (s.insts.val[k.val]'hk).tf with delay := h.start - h.preempt - now } :=
    E.delay _ _ _ (hP _ (List.getElem_mem hk)).1
  dsimp only at hT0
  obtain ⟨sq2, tf2, h4, e4, p4⟩ := E.tto (b + 2) _ now .Scale ⟨0, 0⟩ 0 .None none hT0
  obtain ⟨s3, h5, e5⟩ := sim.transforms.seq_then_refines sq2
  obtain ⟨sq3, tf3, h6, e6, p6⟩ := E.app (b + 1) s3 tf2 now .Scale ⟨1, 1⟩ h.preempt .InOutSine none p4
  obtain ⟨sq4, tf5, h7, e7, p7⟩ := E.tto b tf3 now .Alpha ⟨1, 0⟩ 0 .None none (E.mono _ _ _ (by omega) p6)
  have e4c : OsuModel.Sim.transformTo (abs { (s.insts.val[k.val]'hk).tf with delay := h.start - h.preempt - now }) now
    .scale ⟨0, 0⟩ 0 = (abs tf2, abs sq2) := e4
  have e6c : ((abs s3 : OsuModel.Sim.Seq).append (abs tf2) now .scale ⟨1, 1⟩ h.preempt .inOutSine) = (abs tf3, abs sq3) := e6
  have e7c : OsuModel.Sim.transformTo (abs tf3) now .alpha (OsuModel.Sim.vs 1) 0 = (abs tf5, abs sq4) := e7
  have hspec : s3b_spinS now h.preempt (abs state) (abs { (s.insts.val[k.val]'hk).tf with delay := h.start - h.preempt - now }) =
      abs (if (armedS state == .idle) = true then tf5 else tf3) := by
    unfold s3b_spinS; dsimp only
    rw [e4c]; dsimp only; rw [e5, e6c]; dsimp only; rw [e7c]
    show (if (armedS state == .idle) = true then _ else _) = _
    split <;> rfl
  have pF : P b (if (armedS state == .idle) = true then tf5 else tf3) := by
    split
    · exact p7
    · exact E.mono _ _ _ (by omega) p6
  obtain ⟨hw, hpost⟩ := s3b_wa tn fo E b (b + 3) (by omega) c s k hk now (h.start - h.preempt) _ _ hinv hP hspec pF
  refine ⟨s3b_waSt s k hk (if (armedS state == .idle) = true then tf5 else tf3), ?_, s3b_cs_yield _ _ _ _ hw, hQ _ hpost⟩
  unfold sim.step.spin_in_state
  simp only [float.F64.sub, kind_eq_ok, kindS, bind_ok, sim.step.with_abs_begin_eq _ _ _ _ hk, s3b_index_mut_set _ _ _ hk,
    s3b_vs, sim_step_F64_0, sim_basic_F32_0, s3b_v_xy, h4, h5, s3b_F32_1C, h6, armed_eq_ok, uncurry_apply_pair]
  simp (config := {decide := true}) only [if_true, if_false, Bool.false_eq_true, bind_ok]
  cases state <;> simp (config := {decide := true}) only [armedS, if_true, if_false, Bool.false_eq_true, bind_ok,
    s3b_vs, h7, uncurry_apply_pair] <;> exact s3b_waR_end s k hk _ _

theorem s3b_cs_spinO (s : sim.state.St) (k : Usize) (h : sim.playable.HObj) (K : sim.playable.Kind)
    (state : sim.state.Armed) (now : F64)
    (hK : (kindS K == .circle || kindS K == .head || kindS K == .slider) = false) :
    sim.step.spin_in_state s k h K state now = ok s := by
  cases K <;> simp (config := {decide := true}) [kindS] at hK <;>
    simp (config := {decide := true}) [sim.step.spin_in_state, kindS, float.F64.sub]

theorem s3b_waR_end' (s : sim.state.St) (k : Usize) (hk : k.val < s.insts.val.length) (tf1 : sim.transforms.TObj)
    (V : alloc.vec.Vec sim.state.Inst)
    (hV : V.val = s.insts.val.set k.val { s.insts.val[k.val]'hk with tf := tf1 }) :
    sim.step.with_abs_end { s with insts := V } k (s.insts.val[k.val]'hk).tf.delay = ok (s3b_waSt s k hk tf1) := by
  have hl : k.val < V.val.length := by rw [hV]; simpa using hk
  rw [sim.step.with_abs_end_eq _ _ _ hl]
  unfold s3b_waSt
  congr 2
  refine alloc.vec.Vec.ext _ _ ?_
  simp only [vec_set_val', hV, List.set_set, List.getElem_set_self]

/-- `Transform` (`OsuModTransform.applyTransform`): 2 transforms, then `theta` advances -/
theorem s3b_cs_tfm (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b : Nat) (c : sim.state.Ctx)
    (s : sim.state.St) (k : Usize) (hk : k.val < s.insts.val.length) (h : sim.playable.HObj) (now : F64)
    (hinv : SimInv c s) (hP : s3b_TfInv P (b + 2) s) (htr : (simCtxS tn fo c).cfg.traceObj = none)
    (T : OsuModel.Sim.SimM (ForInStep PUnit)) (Q : sim.state.St → Prop) (hQ : ∀ s', s3b_csPost P b c s s' → Q s')
    (K : OsuModel.Sim.Kind) (hK : (!(K == .circle || K == .slider || K == .spinner)) = false) :
    ∃ s', sim.step.transform_state s k h now = ok s' ∧
      (if (!(K == .circle || K == .slider || K == .spinner)) = true then pure (ForInStep.yield PUnit.unit) else do
        let __do_lift ← get
        let __do_lift_1 ← OsuModel.Sim.Sim.instOf k.val
        OsuModel.Sim.Sim.withAbs k.val now ((hobjS tn h).start - (hobjS tn h).preempt - 1) fun tf =>
          ((OsuModel.Sim.transformTo tf now .position OsuModel.Sim.Vec2.zero 0 .none
              (some ((⟨__do_lift.theta.cos, __do_lift.theta.sin⟩ : OsuModel.Sim.Vec2).scale
                (((hobjS tn h).preempt - (hobjS tn h).fadeIn).toF32 / 2)))).2.append
            (OsuModel.Sim.transformTo tf now .position OsuModel.Sim.Vec2.zero 0 .none
              (some ((⟨__do_lift.theta.cos, __do_lift.theta.sin⟩ : OsuModel.Sim.Vec2).scale
                (((hobjS tn h).preempt - (hobjS tn h).fadeIn).toF32 / 2)))).1
            now .position __do_lift_1.tf.pos ((hobjS tn h).preempt + 1) .inOutSine).1
        modify fun (S : OsuModel.Sim.St) => { S with theta := S.theta + (hobjS tn h).fadeIn.toF32 / 1000 }
        if (simCtxS tn fo c).cfg.traceObj.isSome = true then T else pure (ForInStep.yield PUnit.unit) :
        OsuModel.Sim.SimM (ForInStep PUnit)) (simCtxS tn fo c) (simStS tn s) =
        .ok (ForInStep.yield PUnit.unit, simStS tn s') ∧ Q s' := by
  have hT0 : P (b + 2) { (s.insts.val[k.val]'hk).tf with delay := h.start - h.preempt - 1 - now } :=
    E.delay _ _ _ (hP _ (List.getElem_mem hk)).1
  dsimp only at hT0
  obtain ⟨off, hoff, eoff⟩ := sim.basic.Vec2.scale_refines ⟨OsuModel.Net.F32.cos s.theta, OsuModel.Net.F32.sin s.theta⟩
    ((h.preempt - h.fade_in).toF32 / 2)
  obtain ⟨sq, tf, h1, e1, p1⟩ := E.tto (b + 1) _ now .Position ⟨0, 0⟩ 0 .None (some off) hT0
  obtain ⟨sq', tf1, h3, e3, p3⟩ := E.app b sq tf now .Position (s.insts.val[k.val]'hk).tf.pos (h.preempt + 1)
    .InOutSine none p1
  let G : OsuModel.Sim.TObj → OsuModel.Sim.TObj := fun tf =>
      ((OsuModel.Sim.transformTo tf now .position OsuModel.Sim.Vec2.zero 0 .none
          (some ((⟨(simStS tn s).theta.cos, (simStS tn s).theta.sin⟩ : OsuModel.Sim.Vec2).scale
            (((hobjS tn h).preempt - (hobjS tn h).fadeIn).toF32 / 2)))).2.append
        (OsuModel.Sim.transformTo tf now .position OsuModel.Sim.Vec2.zero 0 .none
          (some ((⟨(simStS tn s).theta.cos, (simStS tn s).theta.sin⟩ : OsuModel.Sim.Vec2).scale
            (((hobjS tn h).preempt - (hobjS tn h).fadeIn).toF32 / 2)))).1
        now .position ((abs (s.insts.val[k.val]'hk) : OsuModel.Sim.Inst)).tf.pos ((hobjS tn h).preempt + 1) .inOutSine).1
  have hspec : G (abs { (s.insts.val[k.val]'hk).tf with delay := h.start - h.preempt - 1 - now }) = abs tf1 := by
    have e1c : OsuModel.Sim.transformTo (abs { (s.insts.val[k.val]'hk).tf with delay := h.start - h.preempt - 1 - now }) now
        .position OsuModel.Sim.Vec2.zero 0 .none (some (abs off)) = (abs tf, abs sq) := e1
    have hoff' : ((⟨(simStS tn s).theta.cos, (simStS tn s).theta.sin⟩ : OsuModel.Sim.Vec2).scale
        (((hobjS tn h).preempt - (hobjS tn h).fadeIn).toF32 / 2)) = abs off := eoff
    simp only [G]; rw [hoff', e1c]; exact congrArg Prod.fst e3
  obtain ⟨hw, hpost⟩ := s3b_wa tn fo E b (b + 2) (by omega) c s k hk now (h.start - h.preempt - 1) G _ hinv hP hspec p3
  let s' : sim.state.St := { s3b_waSt s k hk tf1 with theta := s.theta + h.fade_in.toF32 / 1000 }
  obtain ⟨q1, q2, q3, q4, q5⟩ := hpost
  refine ⟨s', ?_, ?_, hQ s' ⟨s3b_inv_objs q1 rfl (fun _ _ _ => rfl) rfl, fun ins hins => q2 ins hins, q3, q4, ?_⟩⟩
  · unfold sim.step.transform_state
    simp only [float.F64.sub, float.F64.to_f32, sim_basic_F32_2, float.F32.div, bind_ok, vec_index_eq _ _ hk,
      float.F32.cos, float.F32.sin, hoff, sim_step_F64_1, float.F64.add, sim.step.with_abs_begin_eq _ _ _ _ hk,
      s3b_index_mut_set _ _ _ hk, sim_basic_VEC2_ZERO, sim_step_F64_0, h1, s3b_index_mut_set2 _ _ _ _ hk, h3,
      uncurry_apply_pair]
    rw [s3b_waR_end' s k hk tf1 _ (by simp [vec_set_val'])]
    simp only [bind_ok, s3b_F32_1000, float.F32.div, float.F32.add]
    rfl
  · have hk' : k.val < (simStS tn s).insts.size := by simpa [s3b_stS_insts] using hk
    rw [if_neg (by simp [hK])]
    have hI : OsuModel.Sim.Sim.instOf k.val (simCtxS tn fo c) (simStS tn s) =
        .ok (abs (s.insts.val[k.val]'hk), simStS tn s) := by
      simp only [OsuModel.Sim.Sim.instOf, simM_bind, OsuModel.Sim.Sim.st, simM_get, s3b_ebok, OsuModel.Sim.Sim.getA,
        dif_pos hk', simM_pure]
      simp [s3b_stS_insts]
    refine (s3b_bind_ok' _ _ _ _ _ _ (simM_get _ _)).trans ?_
    try dsimp only
    refine (s3b_bind_ok' _ _ _ _ _ _ hI).trans ?_
    try dsimp only
    refine (s3b_bind_ok' _ _ _ _ _ _ hw).trans ?_
    simp only [simM_bind, simM_modify, s3b_ebok, htr, Option.isSome_none, Bool.false_eq_true, if_false]
    rfl
  · rfl

/-- transforms added by one handler (at most; `Wiggle`: `s3c_W`, see Sim3/SC_Wiggle) -/
def s3b_vmCost : sim.mods.VisMod → Nat
  | .ClassicEarlyFade => 1 | .ScaleTween _ => 2 | .SpinIn => 5 | .TargetPractice => 2 | .Hidden _ => 1
  | .Transform => 2 | .Wiggle _ => 2 ^ 31 + 2 ^ 25 | .Inert => 0

/-- transforms added by the handlers from `vi` on -/
def s3b_csCostFrom (l : List sim.mods.VisMod) (vi : Nat) : Nat := ((l.drop vi).map s3b_vmCost).sum

theorem s3b_csCostFrom_succ (l : List sim.mods.VisMod) (vi : Nat) (h : vi < l.length) :
    s3b_csCostFrom l vi = s3b_vmCost (l[vi]'h) + s3b_csCostFrom l (vi + 1) := by
  unfold s3b_csCostFrom; rw [List.drop_eq_getElem_cons h, List.map_cons, List.sum_cons]

section
attribute [local irreducible] sim.step.spin_in_state sim.step.transform_state sim.step.wiggle_state

set_option maxHeartbeats 1600000 in
theorem sim.step.custom_state_refines (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b : Nat)
    (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (p : sim.step.Part) (ns : sim.state.Armed) (fw : Bool)
    (hinv : SimInv c s) (hP : s3b_TfInv P (b + s3b_csCostFrom c.cfg.vis_mods.val 0) s) (hio : i.val < s.objs.val.length)
    (hk1 : (s.objs.val[i.val]'hio).inst.val < s.insts.val.length)
    (hk2 : (s.objs.val[i.val]'hio).head_inst.val < s.insts.val.length)
    (hhi : i.val < c.head_idx.val.length) (hhb : (c.head_idx.val[i.val]'hhi).val < 2 ^ 63)
    (hhn : p = .Head → (c.head_idx.val[i.val]'hhi).val <
      (c.pb.objects.val[i.val]'(by rw [← hinv.objs_len]; exact hio)).nested.val.length)
    (hfo : c.cfg.vis_mods.val.length ≤ c.first_obj.val.length) :
    ∃ s', sim.step.custom_state c s i p ns fw = ok s' ∧
      OsuModel.Sim.Sim.customState i.val (abs p) (abs ns) fw (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧
      SimInv c s' ∧ s3b_TfInv P b s' ∧ s'.insts.val.length = s.insts.val.length ∧ s'.objs = s.objs ∧
      s'.future_order = s.future_order ∧ s3c_ito s s' := by
  have hi : i.val < c.pb.objects.val.length := by rw [← hinv.objs_len]; exact hio
  obtain ⟨r, hr, er⟩ := sim.step.part_ref_refines tn fo c (simStS tn s) i p hhi hhb
  obtain ⟨k, hkk, ek⟩ := sim.step.part_inst_refines tn fo c s i p hio
  have hrok : simRefOk c r := by
    cases p
    · simp [sim.step.part_ref, part_eq_ok, sim.step.Part.read_discriminant] at hr
      rw [← hr]; exact ⟨hi, fun h0 => by simp at h0⟩
    · simp [sim.step.part_ref, part_eq_ok, sim.step.Part.read_discriminant, vec_index_eq _ _ hhi, lift] at hr
      rw [← hr]
      have hc : (UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)).val = ((c.head_idx.val[i.val]'hhi).val : Int) := by
        rw [UScalar.hcast_val_eq]; simp; rw [Int.bmod_eq_of_le] <;> omega
      exact ⟨hi, fun _ => by simp only [hc, Int.toNat_natCast]; exact hhn rfl⟩
  obtain ⟨h, hh, eh⟩ := sim.step.hobj_of_refines tn fo c r hrok
  have hkv : k.val < s.insts.val.length := by
    cases p <;> simp [sim.step.part_inst, part_eq_ok, sim.step.Part.read_discriminant, vec_index_eq _ _ hio] at hkk <;>
      rw [← hkk] <;> assumption
  unfold sim.step.custom_state OsuModel.Sim.Sim.customState
  rw [hr, bind_ok, hh, bind_ok, hkk, bind_ok]
  rw [simM_bind, OsuModel.Sim.Sim.ctx, simM_read, s3b_ebok]; dsimp (config := {zeta := false}) only
  rw [simM_bind, s3b_topObj tn fo c _ _ hi, s3b_ebok]; dsimp (config := {zeta := false}) only
  rw [simM_bind, er, s3b_ebok]; dsimp (config := {zeta := false}) only
  rw [simM_bind, eh, s3b_ebok]; dsimp (config := {zeta := false}) only
  rw [simM_bind, ek, s3b_ebok]; dsimp (config := {zeta := false}) only
  rw [simM_bind, OsuModel.Sim.Sim.st, simM_get, s3b_ebok]; dsimp (config := {zeta := false}) only
  have hvm : (simCtxS tn fo c).cfg.visMods.size = c.cfg.vis_mods.val.length := by simp [simCtxS, abs, configS]
  refine s3b_cs_loop' tn c i p ns fw h k s.t (simCtxS tn fo c)
    (fun vi s1 => SimInv c s1 ∧ s3b_TfInv P (b + s3b_csCostFrom c.cfg.vis_mods.val vi) s1 ∧
      s1.insts.val.length = s.insts.val.length ∧ s1.objs = s.objs ∧ s3c_ito s s1) _ hvm _ ?step s
      ⟨hinv, hP, rfl, rfl, s3c_ito_refl s⟩ _ ?fin
  case fin =>
    intro s' ⟨i3, i4, i5, i6, i7⟩
    refine ⟨i3, ?_, i5, i6, (s3c_ito_frame i7).2.2.2.2.2.2.2.2.2.1, i7⟩
    have : s3b_csCostFrom c.cfg.vis_mods.val c.cfg.vis_mods.val.length = 0 := by simp [s3b_csCostFrom]
    rw [this] at i4; simpa using i4
  case step =>
    intro vi hm s1 ⟨j1, j2, j3, j4, j5⟩
    have hvi : vi.val < c.cfg.vis_mods.val.length := by have := hm.2.1; rw [hvm] at this; exact this
    rw [s3b_csCostFrom_succ _ _ hvi] at j2
    have hfi : vi.val < c.first_obj.val.length := by omega
    have hgf : OsuModel.Sim.Sim.getA (simCtxS tn fo c).firstObj vi.val "firstObj" (simCtxS tn fo c) (simStS tn s1) =
        .ok (((c.first_obj.val[vi.val]'hfi).map (·.val)), simStS tn s1) := by
      have : vi.val < (simCtxS tn fo c).firstObj.size := by simpa [simCtxS, abs] using hfi
      simp only [OsuModel.Sim.Sim.getA, dif_pos this, simM_pure]; simp [simCtxS, abs]
    have hgv : (simCtxS tn fo c).cfg.visMods[vi.val]'hm.2.1 = abs (c.cfg.vis_mods.val[vi.val]'hvi) := by
      simp [simCtxS, abs, configS]
    simp only [hgv]
    unfold sim.step.custom_state_one
    simp only [vec_index_eq _ _ hfi, vec_index_eq _ _ hvi, bind_ok, float.F64.sub, kind_eq_ok]
    simp only [simM_bind, hgf, s3b_ebok]
    obtain ⟨vm, hvv⟩ : ∃ vm, (c.cfg.vis_mods.val[vi.val]'hvi) = vm := ⟨_, rfl⟩
    simp only [hvv] at j2 ⊢
    have hcd : (if (kindS h.kind == kindS sim.playable.Kind.Circle) = true then ok true
        else ok (kindS h.kind == kindS sim.playable.Kind.Head) : Result Bool) =
        ok (kindS h.kind == kindS sim.playable.Kind.Circle || kindS h.kind == kindS sim.playable.Kind.Head) := by
      cases (kindS h.kind == kindS sim.playable.Kind.Circle) <;> rfl
    rw [hcd, bind_ok]
    have hP1 : s3b_TfInv P (b + s3b_csCostFrom c.cfg.vis_mods.val (vi.val + 1)) s1 := fun ins hins =>
      ⟨E.mono _ _ _ (by omega) (j2 ins hins).1, E.mono _ _ _ (by omega) (j2 ins hins).2⟩
    have hk : k.val < s1.insts.val.length := by omega
    have hmono : ∀ n, s3b_vmCost vm = n → s3b_TfInv P (b + s3b_csCostFrom c.cfg.vis_mods.val (vi.val + 1) + n) s1 :=
      fun n hn ins hins => by rw [← hn]; exact ⟨E.mono _ _ _ (by omega) (j2 ins hins).1, E.mono _ _ _ (by omega) (j2 ins hins).2⟩
    rw [show (hobjS tn h).kind = kindS h.kind from rfl]
    cases vm
    case Inert =>
      split <;> exact ⟨s1, by simp only [bind_ok], rfl, j1, hP1, j3, j4, j5⟩
    case ScaleTween sc =>
      rw [show (abs (sim.mods.VisMod.ScaleTween sc) : OsuModel.Sim.VisMod) = .scaleTween sc from rfl]
      obtain ⟨s', hR, hW, q1, q2, q3, q4, q5⟩ := s3b_cs_scale tn fo E _ c s1 k hk s.t (h.start - h.preempt) h.preempt sc j1
        (hmono 2 rfl)
      have Y := s3b_cs_yield _ _ _ _ hW
      s3b_cs_split (first
        | exact ⟨s1, rfl, rfl, j1, hP1, j3, j4, j5⟩
        | exact ⟨s', hR, Y, q1, q2, q3.trans j3, q4.trans j4, s3c_ito_trans j5 q5⟩)
    case TargetPractice =>
      rw [show (abs sim.mods.VisMod.TargetPractice : OsuModel.Sim.VisMod) = .targetPractice from rfl]
      obtain ⟨s', hR, hW, q1, q2, q3, q4, q5⟩ := s3b_cs_tp tn fo E _ c s1 k hk s.t (h.start - h.preempt) h.preempt j1
        (hmono 2 rfl)
      have Y := s3b_cs_yield _ _ _ _ hW
      s3b_cs_split (first
        | exact ⟨s1, rfl, rfl, j1, hP1, j3, j4, j5⟩
        | exact ⟨s', hR, Y, q1, q2, q3.trans j3, q4.trans j4, s3c_ito_trans j5 q5⟩)
    case ClassicEarlyFade =>
      rw [show (abs sim.mods.VisMod.ClassicEarlyFade : OsuModel.Sim.VisMod) = .classicEarlyFade from rfl,
        show (hobjS tn h).hitWindows = h.hit_windows.map abs from rfl, show (abs ns : OsuModel.Sim.Armed) = armedS ns from rfl]
      simp only [armed_eq_ok]
      cases hhw : h.hit_windows with
      | none =>
        simp only [Option.map_none]
        s3b_cs_split (cases fw <;> cases ns <;> (try simp (config := {decide := true}) only [armedS, bind_ok, if_true,
          if_false, Bool.false_eq_true, Bool.true_or, Bool.false_or, Bool.or_false, Bool.or_true, Bool.not_true,
          Bool.not_false, ite_true, ite_false]) <;> exact ⟨s1, rfl, rfl, j1, hP1, j3, j4, j5⟩)
      | some hw =>
        simp only [Option.map_some]
        obtain ⟨s', hR, hW, q1, q2, q3, q4, q5⟩ := s3b_cs_cef tn fo E _ c s1 k hk s.t h.start hw.ok_ hw.meh j1
          (hmono 1 rfl)
        have Y := s3b_cs_yield _ _ _ _ hW
        s3b_cs_split (cases fw <;> cases ns <;> (try simp (config := {decide := true}) only [armedS, bind_ok, if_true,
          if_false, Bool.false_eq_true, Bool.true_or, Bool.false_or, Bool.or_false, Bool.or_true, Bool.not_true,
          Bool.not_false, ite_true, ite_false]) <;> first
          | exact ⟨s1, rfl, rfl, j1, hP1, j3, j4, j5⟩
          | exact ⟨s', hR, Y, q1, q2, q3.trans j3, q4.trans j4, s3c_ito_trans j5 q5⟩)
    case Hidden oa =>
      rw [show (abs (sim.mods.VisMod.Hidden oa) : OsuModel.Sim.VisMod) = .hidden oa from rfl]
      cases oa
      case true => s3b_cs_split (exact ⟨s1, rfl, rfl, j1, hP1, j3, j4, j5⟩)
      case false =>
        unfold sim.step.hidden_state
        simp only [float.F64.sub, float.F64.add, float.F64.mul, fb64_4599075939470750515, bind_ok, kind_eq_ok]
        obtain ⟨s', hR, hW, q1, q2, q3, q4, q5⟩ := s3b_cs_fade tn fo E _ c s1 k hk s.t (h.start - h.preempt + h.fade_in)
          (h.preempt * 0.3) j1 (hmono 1 rfl)
        have Y := s3b_cs_yield _ _ _ _ hW
        obtain ⟨s'', hR', hW', q1', q2', q3', q4', q5'⟩ := s3b_cs_fade tn fo E _ c s1 k hk s.t
          (h.start - h.preempt + h.fade_in + (h.end_time - (h.start - h.preempt + h.fade_in))) (h.preempt * 0.3) j1 (hmono 1 rfl)
        have Y' := s3b_cs_yield _ _ _ _ hW'
        obtain ⟨s3, hR3, hW3, r1, r2, r3, r4, r5⟩ := s3b_cs_hidsl tn fo E _ c s1 k hk s.t (h.start - h.preempt + h.fade_in)
          (h.end_time - (h.start - h.preempt + h.fade_in)) j1 (hmono 1 rfl)
        have Y3 := s3b_cs_yield _ _ _ _ hW3
        s3b_cs_split (first
          | exact ⟨s1, rfl, rfl, j1, hP1, j3, j4, j5⟩
          | exact ⟨s', hR, Y, q1, q2, q3.trans j3, q4.trans j4, s3c_ito_trans j5 q5⟩
          | exact ⟨s'', hR', Y', q1', q2', q3'.trans j3, q4'.trans j4, s3c_ito_trans j5 q5'⟩
          | exact ⟨s3, hR3, Y3, r1, r2, r3.trans j3, r4.trans j4, s3c_ito_trans j5 r5⟩)
    case SpinIn =>
      rw [show (abs sim.mods.VisMod.SpinIn : OsuModel.Sim.VisMod) = .spinIn from rfl]
      s3b_cs_split (first
        | exact ⟨s1, rfl, rfl, j1, hP1, j3, j4, j5⟩
        | (have hd : (kindS h.kind == .circle || kindS h.kind == .head || kindS h.kind == .slider) = false := by
              rw [hK]; decide
           rw [hK] at hd
           exact ⟨s1, s3b_cs_spinO _ _ _ _ _ _ hd, rfl, j1, hP1, j3, j4, j5⟩)
        | (have hd : (kindS h.kind == .circle || kindS h.kind == .head) = true := by rw [hK]; decide
           rw [hK] at hd
           exact s3b_cs_spinC tn fo E _ c s1 k hk h _ ns s.t j1 (hmono 5 rfl) hd _
            (fun s' q => ⟨q.1, q.2.1, q.2.2.1.trans j3, q.2.2.2.1.trans j4, s3c_ito_trans j5 q.2.2.2.2⟩))
        | (have hd : (kindS h.kind == .slider) = true := by rw [hK]; decide
           exact s3b_cs_spinS tn fo E _ c s1 k hk h ns s.t j1 (s3b_tfinv_mono E (by omega) (hmono 5 rfl)) _
            (fun s' q => ⟨q.1, q.2.1, q.2.2.1.trans j3, q.2.2.2.1.trans j4, s3c_ito_trans j5 q.2.2.2.2⟩)))
    case Transform =>
      rw [show (abs sim.mods.VisMod.Transform : OsuModel.Sim.VisMod) = .transform from rfl]
      s3b_cs_split (first
        | exact ⟨s1, rfl, rfl, j1, hP1, j3, j4, j5⟩
        | exact s3b_cs_tfm tn fo E _ c s1 k hk h s.t j1 (hmono 2 rfl) rfl _ _
            (fun s' q => ⟨q.1, q.2.1, q.2.2.1.trans j3, q.2.2.2.1.trans j4, s3c_ito_trans j5 q.2.2.2.2⟩) _ (by decide))
    case Wiggle st =>
      rw [show (abs (sim.mods.VisMod.Wiggle st) : OsuModel.Sim.VisMod) = .wiggle st from rfl]
      obtain ⟨s', hR, hS, q⟩ := sim.step.wiggle_state_refines tn fo E (b + s3b_csCostFrom c.cfg.vis_mods.val (vi.val + 1))
        c s1 i p k h st s.t j1 (hmono _ rfl) hk hi
      refine ⟨s', ?_, hS, q.1, q.2.1, q.2.2.1.trans j3, q.2.2.2.1.trans j4, s3c_ito_trans j5 q.2.2.2.2⟩
      split <;> simp only [bind_ok] <;> exact hR

end

/-- `s3b_CSOk` (the custom-state hypothesis of `update_state_refines`) from `custom_state_refines` -/
theorem s3c_csOk_of (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (c : sim.state.Ctx) (i : Usize)
    (p : sim.step.Part) (ns : sim.state.Armed) (hi : i.val < c.pb.objects.val.length)
    (hhi : i.val < c.head_idx.val.length) (hhb : (c.head_idx.val[i.val]'hhi).val < 2 ^ 63)
    (hhn : p = sim.step.Part.Head → (c.head_idx.val[i.val]'hhi).val < (c.pb.objects.val[i.val]'hi).nested.val.length)
    (hfo : c.cfg.vis_mods.val.length ≤ c.first_obj.val.length) :
    s3b_CSOk P (s3b_csCostFrom c.cfg.vis_mods.val 0) tn fo c i p ns := by
  intro b s fw hinv hP hio hk1 hk2
  exact sim.step.custom_state_refines tn fo E b c s i p ns fw hinv hP hio hk1 hk2 hhi hhb hhn hfo

/-- compatibility form of `s3c_csOk_of` (the `hnw` argument is no longer needed and ignored; Wiggle is handled) -/
theorem s3b_csOk_of (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (c : sim.state.Ctx) (i : Usize)
    (p : sim.step.Part) (ns : sim.state.Armed) (hi : i.val < c.pb.objects.val.length)
    (hhi : i.val < c.head_idx.val.length) (hhb : (c.head_idx.val[i.val]'hhi).val < 2 ^ 63)
    (hhn : p = sim.step.Part.Head → (c.head_idx.val[i.val]'hhi).val < (c.pb.objects.val[i.val]'hi).nested.val.length)
    (hfo : c.cfg.vis_mods.val.length ≤ c.first_obj.val.length)
    (_hnw : ∀ vm ∈ c.cfg.vis_mods.val, ∀ st, vm ≠ .Wiggle st) :
    s3b_CSOk P (s3b_csCostFrom c.cfg.vis_mods.val 0) tn fo c i p ns :=
  s3c_csOk_of tn fo E c i p ns hi hhi hhb hhn hfo

end OsuProofs
