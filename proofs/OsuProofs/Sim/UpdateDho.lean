/-
`update_dho` (`DrawableHitObject.Update` driver) against `OsuModel.Sim.Sim.updateDho`: split lemmas, the
first-load/transform-update prefix (re-establishing `SimARInv` from one spare budget unit) and the per-kind tail.
-/
import OsuProofs.Sim.OnKilled
import OsuProofs.Sim.Bindings
import OsuProofs.Sim3.SC_Misc
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- `update_dho` after the transform update (verbatim generated tail, the state `{ s1 with insts := v }` as `s2`) -/
def simDhoTailR (c : sim.state.Ctx) (s2 : sim.state.St) (i : Std.Usize) :
    Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St) := do
  let b ← sim.step.part_present c s2 i sim.step.Part.Top
  if b
  then
    let «to» ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        sim.playable.TopObj) c.pb.objects i
    match «to».h.kind with
    | sim.playable.Kind.Circle =>
      sim.step.circle_update_result c s2
        { top := i, nested := (-1)#i64 } false
    | sim.playable.Kind.Slider =>
      sim.step.update_slider c s2 i
    | sim.playable.Kind.Spinner =>
      sim.step.update_spinner c s2 i
    | sim.playable.Kind.Head =>
      ok (core.result.Result.Ok (), s2)
    | sim.playable.Kind.Tick =>
      ok (core.result.Result.Ok (), s2)
    | sim.playable.Kind.Repeat =>
      ok (core.result.Result.Ok (), s2)
    | sim.playable.Kind.Tail =>
      ok (core.result.Result.Ok (), s2)
    | sim.playable.Kind.SpinnerTick =>
      ok (core.result.Result.Ok (), s2)
    | sim.playable.Kind.SpinnerBonusTick =>
      ok (core.result.Result.Ok (), s2)
  else ok (core.result.Result.Ok (), s2)


theorem sim_dho_split (c s i) : sim.step.update_dho c s i = (do
  let o ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      sim.state.OState) s.objs i
  let i1 ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.state.Inst)
      s.insts o.inst
  let s1 ←
    if i1.loaded
    then ok s
    else
      do
      let (i2, index_mut_back) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
          sim.state.Inst) s.insts o.inst
      let v := index_mut_back { i2 with loaded := true }
      sim.step.update_state_from_result c { s with insts := v } i
        sim.step.Part.Top 1#u64
  let (i2, index_mut_back) ←
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
      sim.state.Inst) s1.insts o.inst
  let t ← sim.transforms.update_transforms i2.tf s1.t false
  let v := index_mut_back { i2 with tf := t }
  simDhoTailR c { s1 with insts := v } i) := rfl

open OsuModel.Net OsuModel.Replay OsuModel.Sim OsuModel.Sim.Sim in
/-- `updateDho` after the transform update (verbatim spec tail) -/
def simDhoTailS (i : Nat) (o : OsuModel.Sim.TopObj) : OsuModel.Sim.SimM Unit := do
  if !(← partPresent i .top) then return
  match o.h.kind with
  | .circle => circleUpdateResult (i, -1) false
  | .slider => updateSlider i
  | .spinner => updateSpinner i
  | _ => pure ()

open OsuModel.Net OsuModel.Replay OsuModel.Sim OsuModel.Sim.Sim in
theorem sim_dho_splitS (i : Nat) : OsuModel.Sim.Sim.updateDho i = (do
  let o ← topObj i
  let k := (← ostate i).inst
  if !(← instOf k).loaded then
    modifyInst k fun ins => { ins with loaded := true }
    updateStateFromResult i .top 1
  let t := (← st).t
  modifyInst k fun ins => { ins with tf := updateTransforms ins.tf t }
  simDhoTailS i o) := rfl

theorem sim_modifyInst_stS (tn) (C : OsuModel.Sim.Ctx) (s : sim.state.St) (k : Usize) (h : k.val < s.insts.val.length)
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

theorem sim_tf_setsame {P : Nat → sim.transforms.TObj → Prop} {B : Nat} {s : sim.state.St} {k : Usize}
    (hk : k.val < s.insts.val.length) {Y : sim.state.Inst} (h : s3b_TfInv P B s)
    (h1 : P B Y.tf) (h2 : Y.body_tf = (s.insts.val[k.val]'hk).body_tf) :
    s3b_TfInv P B { s with insts := s.insts.set k Y } := by
  intro ins hm
  simp only [vec_set_val'] at hm
  rcases List.mem_or_eq_of_mem_set hm with hm | hm
  · exact h ins hm
  · subst hm
    exact ⟨h1, h2 ▸ (h _ (List.getElem_mem hk)).2⟩

theorem sim_objFrame_refl (s : sim.state.St) : s3b_objFrame s s :=
  ⟨rfl, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- the transformable predicate survives `update_transforms` -/
structure simTfU (P : Nat → sim.transforms.TObj → Prop) : Prop where
  ut : ∀ b o time, P b o → ∃ o', sim.transforms.update_transforms o time false = ok o' ∧
    OsuModel.Sim.updateTransforms (abs o) time false = abs o' ∧ P b o'

theorem sim_dho_prefix (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (U : simTfU P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (s : sim.state.St) (i : Usize) (e : Nat) (hI : SimARInv tn fo P b0 n c s e 1 0) (hIn : simInstOk c s i.val)
    (hi : i.val < c.pb.objects.val.length) :
    ∃ s2, sim.step.update_dho c s i = simDhoTailR c s2 i ∧
      OsuModel.Sim.Sim.updateDho i.val (simCtxS tn fo c) (simStS tn s) =
        simDhoTailS i.val (topS tn (c.pb.objects.val[i.val]'hi)) (simCtxS tn fo c) (simStS tn s2) ∧
      SimARInv tn fo P b0 n c s2 e 0 0 ∧ s3b_frame s s2 ∧ s3b_objFrame s s2 ∧
      s2.insts.val.length = s.insts.val.length ∧ simARFr s s2 := by
  have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
  have hik : (s.objs.val[i.val]'ho).inst.val < s.insts.val.length ∧ (s.objs.val[i.val]'ho).head_inst.val < s.insts.val.length ∧ True := by
    obtain ⟨_, a, b, _⟩ := hIn; exact ⟨a, b, trivial⟩
  rw [sim_dho_split, sim_dho_splitS]
  simp only [vec_index_eq _ _ ho, vec_index_eq _ _ hik.1, bind_ok, simM_bind, s3b_topObj tn fo c _ i.val hi,
    s3a_ostate tn fo c s _ ho, Except.bind, s3a_ostateS_inst, s3a_instOf tn fo c s _ hik.1]
  generalize hk : (s.objs.val[i.val]'ho).inst = k at hik ⊢
  have hkl : k.val < s.insts.val.length := hik.1
  generalize hins : s.insts.val[k.val]'hkl = ins
  have hlS : (abs ins : OsuModel.Sim.Inst).loaded = ins.loaded := rfl
  rw [hlS]
  have hK : b0 + (simUnj s + 1) * (n + n + 4) = b0 + simUnj s * (n + n + 4) + (n + n + 4) := by ring
  have hTf0 : s3b_TfInv P (b0 + simUnj s * (n + n + 4) + (n + n + 4)) s := by rw [← hK]; exact hI.tf
  have hTfm : s3b_TfInv P (b0 + simUnj s * (n + n + 4)) s := sim_tfInv_mono E _ _ s (by omega) hTf0
  by_cases hl : ins.loaded = true
  · have hPi : P (b0 + simUnj s * (n + n + 4)) ins.tf := (hTfm ins (by rw [← hins]; exact List.getElem_mem _)).1
    obtain ⟨o', eo, ao, Po⟩ := U.ut _ ins.tf s.t hPi
    rw [if_pos hl, if_neg (by simp [hl])]
    simp only [bind_ok, vec_index_mut_eq _ _ hkl, hins, uncurry_apply_pair, eo, simM_bind, OsuModel.Sim.Sim.st,
      simM_get, Except.bind]
    have hY : (fun (x : OsuModel.Sim.Inst) => { x with tf := OsuModel.Sim.updateTransforms x.tf (simStS tn s).t })
        (abs (s.insts.val[k.val]'hkl)) = abs { ins with tf := o' } := by
      rw [hins]; simp only [s3a_inst_tf]; rw [show (simStS tn s).t = s.t from rfl, ao]; rfl
    rw [sim_modifyInst_stS tn _ s k hkl { ins with tf := o' }
      (fun (x : OsuModel.Sim.Inst) => { x with tf := OsuModel.Sim.updateTransforms x.tf (simStS tn s).t }) hY _ rfl]
    refine ⟨{ s with insts := s.insts.set k { ins with tf := o' } }, rfl, rfl, ?_, s3b_frame_refl s,
      sim_objFrame_refl s, by simp [vec_set_val'], ⟨rfl, rfl, fun _ _ _ => rfl, by simp [vec_set_val']⟩⟩
    refine sim_ar_inv_hook tn fo P b0 n c s e 1 0 0 hI _
      ⟨hI.inv.objs_len, hI.inv.nested_len, hI.inv.nested_small, hI.inv.dict_in, hI.inv.dict_small⟩
      (sim_objFrame_refl s) (by simp [vec_set_val']) ?_ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    simp only [Nat.add_zero]
    exact sim_tf_setsame hkl hTfm Po (by rw [hins])
  · rw [if_neg hl, if_pos (by simp [hl])]
    simp only [bind_ok, vec_index_mut_eq _ _ hkl, hins, uncurry_apply_pair]
    obtain ⟨hhi, hhb, hhn⟩ := hC.hd i.val hi
    set sA : sim.state.St := { s with insts := s.insts.set k { ins with loaded := true } } with hsA
    have hkA : k.val < sA.insts.val.length := by simp [sA, vec_set_val', hkl]
    have hTfA : s3b_TfInv P (b0 + simUnj s * (n + n + 4) + (n + n + 4)) sA :=
      sim_tf_setsame hkl hTf0 (by rw [← hins]; exact (hTf0 _ (List.getElem_mem _)).1) (by rw [hins])
    have hinvA : SimInv c sA := ⟨hI.inv.objs_len, hI.inv.nested_len, hI.inv.nested_small, hI.inv.dict_in, hI.inv.dict_small⟩
    have hoA : i.val < sA.objs.val.length := ho
    obtain ⟨s1, eu, su, hinv1, hTf1, hil1, hol1, -, hfr1, hof1, hus1⟩ := s3c_update_state_from_result_strong tn fo E
      (b0 + simUnj s * (n + n + 4)) n c sA i .Top 1#u64 hinvA (by simpa [Nat.add_assoc] using hTfA)
      (fun ns => hCS i .Top ns hi hhi hhb (fun h => by cases h)) hoA
      (by show (s.objs.val[i.val]'ho).inst.val < _; rw [hk]; exact hkA)
      (by show (s.objs.val[i.val]'ho).head_inst.val < _; simp [sA, vec_set_val']; exact hik.2.1) hhi hhb
      (fun h => hhn (by rcases h with h | h; · cases h
                        · exact Or.inl h))
    simp only [eu, bind_ok]
    have hk1 : k.val < s1.insts.val.length := by rw [hil1]; exact hkA
    generalize hins1 : s1.insts.val[k.val]'hk1 = ins1
    have hPi : P (b0 + simUnj s * (n + n + 4)) ins1.tf := (hTf1 ins1 (by rw [← hins1]; exact List.getElem_mem _)).1
    obtain ⟨o', eo, ao, Po⟩ := U.ut _ ins1.tf s1.t hPi
    simp only [vec_index_mut_eq _ _ hk1, hins1, uncurry_apply_pair, eo, bind_ok]
    have hlA : (fun (x : OsuModel.Sim.Inst) => { x with loaded := true }) (abs (s.insts.val[k.val]'hkl)) =
        abs { ins with loaded := true } := by rw [hins]; rfl
    have su' : OsuModel.Sim.Sim.updateStateFromResult i.val .top 1 (simCtxS tn fo c) (simStS tn sA) =
        .ok ((), simStS tn s1) := su
    have hY : (fun (x : OsuModel.Sim.Inst) => { x with tf := OsuModel.Sim.updateTransforms x.tf (simStS tn s1).t })
        (abs (s1.insts.val[k.val]'hk1)) = abs { ins1 with tf := o' } := by
      rw [hins1]; simp only [s3a_inst_tf]; rw [show (simStS tn s1).t = s1.t from rfl, ao]; rfl
    simp only [simM_bind, Except.bind, OsuModel.Sim.Sim.st, simM_get]
    rw [sim_modifyInst_stS tn _ s k hkl { ins with loaded := true } (fun x => { x with loaded := true }) hlA _ rfl,
      ← hsA]
    simp only [Except.bind, su']
    rw [sim_modifyInst_stS tn _ s1 k hk1 { ins1 with tf := o' }
      (fun (x : OsuModel.Sim.Inst) => { x with tf := OsuModel.Sim.updateTransforms x.tf (simStS tn s1).t }) hY _ rfl]
    have hofs : s3b_objFrame s { s1 with insts := s1.insts.set k { ins1 with tf := o' } } := by
      have h2 : s3b_objFrame s1 { s1 with insts := s1.insts.set k { ins1 with tf := o' } } := sim_objFrame_refl s1
      exact s3b_objFrame_trans (s2 := sA) (sim_objFrame_refl s) (s3b_objFrame_trans hof1 h2)
    have hfrs : s3b_frame s { s1 with insts := s1.insts.set k { ins1 with tf := o' } } :=
      s3b_frame_trans (s2 := sA) (s3b_frame_refl s) (s3b_frame_trans hfr1 (s3b_frame_refl s1))
    have hils : ({ s1 with insts := s1.insts.set k { ins1 with tf := o' } } : sim.state.St).insts.val.length =
        s.insts.val.length := by simp [vec_set_val', hil1, sA]
    have hA1 : simARFr sA s1 := (simARFr_qok c sA (fun _ => True)).us sA s1 i (simARFr_refl sA) hus1
    have hAs : simARFr s { s1 with insts := s1.insts.set k { ins1 with tf := o' } } :=
      simARFr_trans (simARFr_trans (⟨rfl, rfl, fun _ _ _ => rfl, by simp [sA, vec_set_val']⟩ : simARFr s sA) hA1)
        ⟨rfl, rfl, fun _ _ _ => rfl, by simp [vec_set_val']⟩
    refine ⟨{ s1 with insts := s1.insts.set k { ins1 with tf := o' } }, rfl, rfl, ?_, hfrs, hofs, hils, hAs⟩
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩ := hfrs
    refine sim_ar_inv_hook tn fo P b0 n c s e 1 0 0 hI _
      ⟨hinv1.objs_len, hinv1.nested_len, hinv1.nested_small, hinv1.dict_in, hinv1.dict_small⟩
      hofs hils ?_ f1 f2 f3 f4 f5 f6 f7 f8 f9 f11
    simp only [Nat.add_zero]
    exact sim_tf_setsame hk1 hTf1 Po (by rw [hins1])
/-- weakening the transform budget of the `apply_result` invariant -/
theorem sim_ar_weak {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) {tn fo b0 b1 n c s e} (hb : b1 ≤ b0)
    (hI : SimARInv tn fo P b0 n c s e 0 0) : SimARInv tn fo P b1 n c s e 0 0 :=
  ⟨hI.inv, sim_tfInv_mono E _ _ s (by omega) hI.tf, hI.ik, hI.em, hI.sp, hI.cnt, hI.seen, hI.enum⟩

theorem sim_dho_tail (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c)
    (hCS : simCSH P n tn fo c) (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (s : sim.state.St) (i : Usize) (e : Nat) (hI : SimARInv tn fo P b0 n c s e 0 0) (hIn : simInstOk c s i.val)
    (hi : i.val < c.pb.objects.val.length) (hp : s3aPathOk c i.val) (hLP : simLP s)
    (Q : sim.state.St → Prop) (hQ0 : Q s)
    (hQc : ∀ s', SimARInv tn fo P b0 n c s' e 0 0 → simJFr s s' → simLP s' → Q s')
    (hSl : (c.pb.objects.val[i.val]'hi).h.kind = .Slider → ∃ res s', sim.step.update_slider c s i = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.updateSlider i.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → Q s'))
    (hSp : (c.pb.objects.val[i.val]'hi).h.kind = .Spinner → ∃ res s', sim.step.update_spinner c s i = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.updateSpinner i.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → Q s')) :
    ∃ res s', simDhoTailR c s i = ok (res, s') ∧
      simRelM tn s' res (simDhoTailS i.val (topS tn (c.pb.objects.val[i.val]'hi)) (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → Q s') := by
  have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
  obtain ⟨b, eb, sb⟩ := sim.step.part_present_refines tn fo c s i .Top ho hi (by
    intro k hk
    simp [sim.step.part_inst, vec_index_eq _ _ ho] at hk
    subst hk; obtain ⟨_, a, _⟩ := hIn; exact a) (fun h => by cases h)
  have sb' : OsuModel.Sim.Sim.partPresent i.val .top (simCtxS tn fo c) (simStS tn s) = .ok (b, simStS tn s) := sb
  unfold simDhoTailR simDhoTailS
  simp only [eb, bind_ok, simM_bind, sb', Except.bind]
  cases b with
  | false => exact ⟨.Ok (), s, by simp, by simp [simRelM], fun _ => hQ0⟩
  | true =>
  simp only [ite_true, Bool.not_true, Bool.false_eq_true, ite_false, vec_index_eq _ _ hi, bind_ok]
  have hkS : (topS tn (c.pb.objects.val[i.val]'hi)).h.kind = kindS (c.pb.objects.val[i.val]'hi).h.kind := rfl
  rw [hkS]
  have hr1 : simRefOk c ⟨i, (-1)#i64⟩ := ⟨hi, fun h => by simp at h⟩
  have eabs : (abs (⟨i, (-1)#i64⟩ : sim.step.Ref) : Nat × Int) = (i.val, -1) := by simp [abs]
  cases hk : (c.pb.objects.val[i.val]'hi).h.kind <;> simp only [kindS]
  case Circle =>
    obtain ⟨res, s1, e1, r1, i1⟩ := sim.step.circle_update_result_refines h64 tn fo E b0 n c hC hCS hlen s
      ⟨i, (-1)#i64⟩ false e hI hr1 hIn hp hLP
    rw [eabs] at r1
    exact ⟨res, s1, e1, r1, fun h => let ⟨a, b, d⟩ := i1 h; hQc s1 a b d⟩
  case Slider => exact hSl hk
  case Spinner => exact hSp hk
  all_goals exact ⟨.Ok (), s, rfl, by simp [simRelM], fun _ => hQ0⟩

-- CONDITIONAL: hR (on the post-prefix state: Q there and after circle judgement, and the update_slider / update_spinner results; slider: sim7, spinner: sim4); hI carries one spare transform unit (ut = 1) for the first-load updateStateFromResult; hC/hCS context premises
theorem sim.step.update_dho_refines (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (U : simTfU P) (b0 n : Nat) (c : sim.state.Ctx)
    (hC : SimARCtx c) (hCS : simCSH P n tn fo c) (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (s : sim.state.St) (i : Usize) (e : Nat) (hI : SimARInv tn fo P b0 n c s e 1 0) (hIn : simInstOk c s i.val)
    (hi : i.val < c.pb.objects.val.length) (hp : s3aPathOk c i.val) (Q : sim.state.St → Prop)
    (hR : ∀ s2, SimARInv tn fo P b0 n c s2 e 0 0 → s3b_frame s s2 → s3b_objFrame s s2 →
      s2.insts.val.length = s.insts.val.length → simInstOk c s2 i.val → simARFr s s2 → simLP s2 ∧ Q s2 ∧
      (∀ s', SimARInv tn fo P b0 n c s' e 0 0 → simJFr s2 s' → simLP s' → Q s') ∧
      ((c.pb.objects.val[i.val]'hi).h.kind = .Slider → ∃ res s', sim.step.update_slider c s2 i = ok (res, s') ∧
        simRelM tn s' res (OsuModel.Sim.Sim.updateSlider i.val (simCtxS tn fo c) (simStS tn s2)) ∧
        (res = .Ok () → Q s')) ∧
      ((c.pb.objects.val[i.val]'hi).h.kind = .Spinner → ∃ res s', sim.step.update_spinner c s2 i = ok (res, s') ∧
        simRelM tn s' res (OsuModel.Sim.Sim.updateSpinner i.val (simCtxS tn fo c) (simStS tn s2)) ∧
        (res = .Ok () → Q s'))) :
    ∃ res s', sim.step.update_dho c s i = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.updateDho i.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → Q s') := by
  obtain ⟨s2, e1, e2, hI2, hfr, hof, hil, hA2⟩ := sim_dho_prefix tn fo E U b0 n c hC hCS s i e hI hIn hi
  have hIn2 : simInstOk c s2 i.val := sim_instOk_keep (sim_keep_of_objFrame hof) (by rw [hil]) hIn
  obtain ⟨hLP, hQ0, hQc, hSl, hSp⟩ := hR s2 hI2 hfr hof hil hIn2 hA2
  rw [e1, e2]
  exact sim_dho_tail h64 tn fo E b0 n c hC hCS hlen s2 i e hI2 hIn2 hi hp hLP Q hQ0 hQc hSl hSp

end OsuProofs
