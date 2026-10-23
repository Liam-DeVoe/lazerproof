/-
Sim3b part 4: DHO state updates of `sim::step`: `tick_state` (`Sim.tickState`: spinner tick state + the
OsuModTransform `theta` advance per pass), `update_state` / `update_state_from_result` (`Sim.updateState`).
-/
import OsuProofs.Sim3.SB_Basic
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

/-! ## Frame conditions (what a hook leaves untouched) -/
/-- scoring/health/judgement output, AS state, rate state, the future order and the dictionary slots are untouched -/
def s3b_frame (s s' : sim.state.St) : Prop :=
  s'.score = s.score ∧ s'.health = s.health ∧ s'.score_rp = s.score_rp ∧ s'.health_rp = s.health_rp ∧
  s'.out = s.out ∧ s'.as_target = s.as_target ∧ s'.as_recent = s.as_recent ∧ s'.as_seen = s.as_seen ∧
  s'.speed = s.speed ∧ s'.future_order = s.future_order ∧ s'.dict_slots = s.dict_slots

/-- the transformables of every instance are untouched -/
def s3b_tfSame (s s' : sim.state.St) : Prop :=
  s'.insts.val.length = s.insts.val.length ∧ ∀ k (h : k < s.insts.val.length) (h' : k < s'.insts.val.length),
    (s'.insts.val[k]'h').tf = (s.insts.val[k]'h).tf ∧ (s'.insts.val[k]'h').body_tf = (s.insts.val[k]'h).body_tf

/-- the per-object instance indices, results and nested results are untouched -/
def s3b_objFrame (s s' : sim.state.St) : Prop :=
  s'.objs.val.length = s.objs.val.length ∧ ∀ j (h : j < s.objs.val.length) (h' : j < s'.objs.val.length),
    (s'.objs.val[j]'h').inst = (s.objs.val[j]'h).inst ∧ (s'.objs.val[j]'h').head_inst = (s.objs.val[j]'h).head_inst ∧
    (s'.objs.val[j]'h').tick_insts = (s.objs.val[j]'h).tick_insts ∧ (s'.objs.val[j]'h').result = (s.objs.val[j]'h).result ∧
    (s'.objs.val[j]'h').nested = (s.objs.val[j]'h).nested

theorem s3b_frame_refl (s : sim.state.St) : s3b_frame s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem s3b_frame_trans {s1 s2 s3 : sim.state.St} (h1 : s3b_frame s1 s2) (h2 : s3b_frame s2 s3) : s3b_frame s1 s3 := by
  obtain ⟨a1, b1, c1, d1, e1, f1, g1, h1', i1, j1, k1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2, f2, g2, h2', i2, j2, k2⟩ := h2
  exact ⟨a2.trans a1, b2.trans b1, c2.trans c1, d2.trans d1, e2.trans e1, f2.trans f1, g2.trans g1, h2'.trans h1',
    i2.trans i1, j2.trans j1, k2.trans k1⟩
theorem s3b_objFrame_of_eq {s s' : sim.state.St} (h : s'.objs = s.objs) : s3b_objFrame s s' := by
  refine ⟨by rw [h], fun j h1 h2 => ?_⟩
  have : s'.objs.val[j]'h2 = s.objs.val[j]'h1 := by simp only [h]
  rw [this]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem s3b_objFrame_trans {s1 s2 s3 : sim.state.St} (h1 : s3b_objFrame s1 s2) (h2 : s3b_objFrame s2 s3) :
    s3b_objFrame s1 s3 := by
  refine ⟨h2.1.trans h1.1, fun j ha hb => ?_⟩
  have hm : j < s2.objs.val.length := by rw [h1.1]; exact ha
  obtain ⟨a1, b1, c1, d1, e1⟩ := h1.2 j ha hm
  obtain ⟨a2, b2, c2, d2, e2⟩ := h2.2 j hm hb
  exact ⟨a2.trans a1, b2.trans b1, c2.trans c1, d2.trans d1, e2.trans e1⟩

/-! ## `tickState` -/
/-- one pass of `tickState`'s handler loop on `theta` (Transform adds `d` per occurrence) -/
def s3b_thetaStep (vms : List OsuModel.Sim.VisMod) (d : F32) (θ : F32) : F32 :=
  vms.foldl (fun θ vm => match vm with | .transform => θ + d | _ => θ) θ

theorem s3b_forIn_list_st {α : Type} (l : List α) (F : α → PUnit → OsuModel.Sim.SimM (ForInStep PUnit))
    (g : α → OsuModel.Sim.St → OsuModel.Sim.St) (C : OsuModel.Sim.Ctx)
    (hF : ∀ x ∈ l, ∀ S, F x PUnit.unit C S = .ok (.yield PUnit.unit, g x S)) :
    ∀ S, forIn l PUnit.unit F C S = .ok (PUnit.unit, l.foldl (fun S x => g x S) S) := by
  induction l with
  | nil => intro S; rfl
  | cons x t ih =>
    intro S
    rw [List.forIn_cons]
    simp only [simM_bind, hF x List.mem_cons_self, Except.bind, List.foldl_cons]
    exact ih (fun y hy S => hF y (List.mem_cons_of_mem _ hy) S) _

theorem s3b_foldl_theta (vms : List OsuModel.Sim.VisMod) (d : F32) :
    ∀ S : OsuModel.Sim.St, vms.foldl (fun S vm => match vm with
        | .transform => { S with theta := S.theta + d } | _ => S) S =
      { S with theta := s3b_thetaStep vms d S.theta } := by
  induction vms with
  | nil => intro S; rfl
  | cons vm t ih =>
    intro S
    simp only [List.foldl_cons, s3b_thetaStep]
    cases vm <;> (rw [ih]; rfl)

theorem s3b_iter_theta (f : F32 → F32) :
    ∀ n (S : OsuModel.Sim.St), (List.range' 0 n).foldl (fun S _ => { S with theta := f S.theta }) S =
      { S with theta := f^[n] S.theta } := by
  intro n
  induction n with
  | zero => intro S; rfl
  | succ n ih =>
    intro S
    rw [List.range'_concat, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, Function.iterate_succ_apply']

/-- spec `tickState` on in-range indices (no debug trace) -/
theorem s3b_tickState_spec (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) (i j passes : Nat) (ns : OsuModel.Sim.Armed)
    (force : Bool) (hi : i < C.pb.objects.size) (hj : j < C.pb.objects[i].nested.size) (hio : i < S.objs.size)
    (htj : j < S.objs[i].tickInsts.size) (htk : S.objs[i].tickInsts[j] < S.insts.size)
    (htr : C.cfg.traceObj = none) :
    OsuModel.Sim.Sim.tickState i j passes ns force C S =
      if (S.insts[S.objs[i].tickInsts[j]].armed == ns && !force) = true then .ok ((), S)
      else .ok ((), { S with insts := S.insts.set (S.objs[i].tickInsts[j]) { S.insts[S.objs[i].tickInsts[j]] with armed := ns },
                             theta := (s3b_thetaStep C.cfg.visMods.toList (F64.toF32 C.pb.objects[i].nested[j].fadeIn / 1000))^[passes] S.theta }) := by
  unfold OsuModel.Sim.Sim.tickState
  simp only [simM_bind, OsuModel.Sim.Sim.ctx, simM_read, Except.bind, OsuModel.Sim.Sim.topObj, OsuModel.Sim.Sim.getA,
    dif_pos hi, simM_pure, OsuModel.Sim.Sim.nestedOf, dif_pos hj, OsuModel.Sim.Sim.ostate, OsuModel.Sim.Sim.st,
    simM_get, dif_pos hio, dif_pos htj, OsuModel.Sim.Sim.instOf, dif_pos htk]
  split
  · rfl
  · simp only [OsuModel.Sim.Sim.modifyInst, simM_bind, OsuModel.Sim.Sim.checkIdx, simM_get, OsuModel.Sim.Sim.st,
      if_pos htk, simM_pure, Except.bind, simM_modify, s3b_arr_modify _ _ htk]
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    generalize hd : F64.toF32 C.pb.objects[i].nested[j].fadeIn / 1000 = d
    rw [s3b_forIn_list_st _ _ (fun _ S => { S with theta := s3b_thetaStep C.cfg.visMods.toList d S.theta }) _ ?hF]
    case hF =>
      intro x _ S'
      simp only [simM_bind]
      rw [← Array.forIn_toList, s3b_forIn_list_st _ _ (fun vm S => match vm with
        | .transform => { S with theta := S.theta + d } | _ => S) _ ?hG, s3b_foldl_theta]
      · rfl
      case hG =>
        intro vm _ S''
        cases vm <;> simp [htr, hd, Except.bind]
    simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    rw [s3b_iter_theta]

@[simp] theorem s3b_F32_1000 : sim.step.F32_1000 = ok (1000 : F32) := by
  unfold sim.step.F32_1000; simp; decide +kernel

theorem s3b_tick_inner01 : @sim.step.tick_state_loop0_loop0 = @sim.step.tick_state_loop1_loop0 := by
  funext a b c d
  unfold sim.step.tick_state_loop0_loop0 sim.step.tick_state_loop1_loop0
    sim.step.tick_state_loop0_loop0.body sim.step.tick_state_loop1_loop0.body
  rfl
theorem s3b_tick_outer01 : @sim.step.tick_state_loop0 = @sim.step.tick_state_loop1 := by
  funext a b c d e
  unfold sim.step.tick_state_loop0 sim.step.tick_state_loop1 sim.step.tick_state_loop0.body sim.step.tick_state_loop1.body
  rw [s3b_tick_inner01]

/-- the Rust handler loop of one pass (`tick_state_loop1_loop0`) -/
theorem s3b_tick_inner (c : sim.mods.Config) (fi : F64) (f : F32) :
    sim.step.tick_state_loop1_loop0 c f fi 0#usize = ok (c.policy, c.classic_head_block, c.legacy_health,
      c.fail_overrides, c.easy_retries, c.fail_conds, c.acc_challenges, c.rank_adjust, c.rate_sources, c.dyn_rates,
      c.score_multiplier, c.updatables, c.input_blockers, c.spun_out, c.strict_tracking, c.lazer_replay, c.rate_mods,
      c.vis_mods, c.depth_max, c.magnet_strength, c.repel_strength, c.barrel_roll,
      s3b_thetaStep (c.vis_mods.val.map (fun v => (abs v : OsuModel.Sim.VisMod))) (F64.toF32 fi / 1000) f) := by
  have hmax := c.vis_mods.property
  let L := c.vis_mods.val.map (fun v => (abs v : OsuModel.Sim.VisMod))
  obtain ⟨y, hl, hy⟩ := loop_fold_gen' (fun x => sim.step.tick_state_loop1_loop0.body c fi x.1 x.2) (·.2)
    c.vis_mods.val.length (by omega) (fun _ => True) (fun x => x.1)
    (fun k θ => match L[k]! with | .transform => θ + F64.toF32 fi / 1000 | _ => θ)
    (fun y θ => y = (c.policy, c.classic_head_block, c.legacy_health,
      c.fail_overrides, c.easy_retries, c.fail_conds, c.acc_challenges, c.rank_adjust, c.rate_sources, c.dyn_rates,
      c.score_multiplier, c.updatables, c.input_blockers, c.spun_out, c.strict_tracking, c.lazer_replay, c.rate_mods,
      c.vis_mods, c.depth_max, c.magnet_strength, c.repel_strength, c.barrel_roll, θ))
    (by
      rintro ⟨θ, k⟩ _ hk j1 hj1 hj1v
      simp only at hk hj1 hj1v ⊢
      have hkl : k < alloc.vec.Vec.len c.vis_mods := by rw [vec_lt_len_iff]; exact hk
      have hL : L[k.val]! = abs (c.vis_mods.val[k.val]'hk) := by simp [L, getElem!_def, hk]
      refine ⟨(match (abs (c.vis_mods.val[k.val]'hk) : OsuModel.Sim.VisMod) with
        | .transform => θ + F64.toF32 fi / 1000 | _ => θ, j1), ?_, rfl, by simp only [hL], trivial⟩
      cases hv : c.vis_mods.val[k.val]'hk <;>
        simp [sim.step.tick_state_loop1_loop0.body, hkl, vec_index_eq _ _ hk, hv, hj1, float.F64.to_f32,
          float.F32.div, float.F32.add, abs])
    (by
      rintro ⟨θ, k⟩ _ hge
      simp only at hge
      have : ¬ k < alloc.vec.Vec.len c.vis_mods := by rw [vec_lt_len_iff]; omega
      exact ⟨_, by simp only [sim.step.tick_state_loop1_loop0.body, this, ite_false], rfl⟩)
    (f, 0#usize) trivial (by simp)
  unfold sim.step.tick_state_loop1_loop0
  rw [hl, hy]
  simp only [show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero]
  have hlen : L.length = c.vis_mods.val.length := by simp [L]
  rw [← hlen, ← foldl_iterR L (fun θ vm => match vm with | .transform => θ + F64.toF32 fi / 1000 | _ => θ) f]
  rfl

/-- the Rust pass loop (`tick_state_loop1`, `q` from its start to `passes`) -/
theorem s3b_tick_outer (c : sim.mods.Config) (fi : F64) (passes : U64) :
    ∀ n (q : U64) (f : F32), passes.val - q.val = n → q.val ≤ passes.val →
      sim.step.tick_state_loop1 c f passes fi q =
        ok ((s3b_thetaStep (c.vis_mods.val.map (fun v => (abs v : OsuModel.Sim.VisMod))) (F64.toF32 fi / 1000))^[n] f) := by
  intro n
  induction n with
  | zero =>
    intro q f hn hq
    have : ¬ q < passes := by intro h; have : q.val < passes.val := h; omega
    unfold sim.step.tick_state_loop1; rw [loop_unfold]
    simp [sim.step.tick_state_loop1.body, this]
  | succ n ih =>
    intro q f hn hq
    have hlt : q < passes := by show q.val < passes.val; omega
    obtain ⟨q1, hq1, hq1v⟩ := eq_ok_of_spec (UScalar.add_spec (x := q) (y := 1#u64) (by scalar_tac))
    have hb : sim.step.tick_state_loop1.body passes fi c f q = ok (.cont (c,
        s3b_thetaStep (c.vis_mods.val.map (fun v => (abs v : OsuModel.Sim.VisMod))) (F64.toF32 fi / 1000) f, q1)) := by
      simp only [sim.step.tick_state_loop1.body, hlt, if_true, s3b_tick_inner, bind_ok, hq1]
      rfl
    have e : sim.step.tick_state_loop1 c f passes fi q = sim.step.tick_state_loop1 c
        (s3b_thetaStep (c.vis_mods.val.map (fun v => (abs v : OsuModel.Sim.VisMod))) (F64.toF32 fi / 1000) f) passes fi q1 := by
      unfold sim.step.tick_state_loop1; rw [loop_unfold]; simp only [hb, bind_ok]
    rw [e, ih q1 _ (by simp at hq1v; omega) (by simp at hq1v; omega), Function.iterate_succ_apply]

def s3b_tickSt (s : sim.state.St) (tk : Usize) (h : tk.val < s.insts.val.length) (ns : sim.state.Armed) (th : F32) :
    sim.state.St :=
  { s with insts := s.insts.set tk ({ s.insts.val[tk.val]'h with armed := ns }), theta := th }

theorem s3b_tickSt_tfSame (s : sim.state.St) (tk : Usize) (h : tk.val < s.insts.val.length) (ns : sim.state.Armed)
    (th : F32) : s3b_tfSame s (s3b_tickSt s tk h ns th) := by
  refine ⟨by simp [s3b_tickSt, vec_set_val'], fun k h1 h2 => ?_⟩
  simp only [s3b_tickSt, vec_set_val', List.getElem_set]
  split
  · subst_vars; exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem s3b_tick_core (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (i j : Usize) (passes : U64)
    (ns : sim.state.Armed) (force : Bool) (hinv : SimInv c s)
    (hi : i.val < c.pb.objects.val.length) (hj : j.val < (c.pb.objects.val[i.val]'hi).nested.val.length)
    (hio : i.val < s.objs.val.length) (htj : j.val < (s.objs.val[i.val]'hio).tick_insts.val.length)
    (htk : ((s.objs.val[i.val]'hio).tick_insts.val[j.val]'htj).val < s.insts.val.length) :
    ∃ s', sim.step.tick_state c s i j passes ns force = ok s' ∧
      OsuModel.Sim.Sim.tickState i.val j.val passes.val (abs ns) force (simCtxS tn fo c) (simStS tn s) =
        .ok ((), simStS tn s') ∧
      (∃ ins th, s' = { s with insts := ins, theta := th }) ∧ s'.insts.val.length = s.insts.val.length ∧
      SimInv c s' ∧ s'.future_order = s.future_order ∧ s'.objs = s.objs ∧ s3b_frame s s' ∧ s3b_tfSame s s' := by
  have hiC : i.val < (simCtxS tn fo c).pb.objects.size := by simpa using hi
  have hjC : j.val < ((simCtxS tn fo c).pb.objects[i.val]'hiC).nested.size := by
    rw [sim_ctxS_object]; simpa [topS] using hj
  have hioS : i.val < (simStS tn s).objs.size := by simpa using hio
  have htjS : j.val < ((simStS tn s).objs[i.val]'hioS).tickInsts.size := by
    rw [sim_stS_obj]; simpa [ostateS, abs] using htj
  have etk : ((simStS tn s).objs[i.val]'hioS).tickInsts[j.val]'htjS =
      ((s.objs.val[i.val]'hio).tick_insts.val[j.val]'htj).val := by
    simp only [sim_stS_obj]; simp [ostateS, abs]
  have htkS : ((simStS tn s).objs[i.val]'hioS).tickInsts[j.val]'htjS < (simStS tn s).insts.size := by
    rw [etk]; simpa [s3b_stS_insts] using htk
  have htr : (simCtxS tn fo c).cfg.traceObj = none := rfl
  rw [s3b_tickState_spec _ _ _ _ _ _ _ hiC hjC hioS htjS htkS htr]
  generalize htkv : (s.objs.val[i.val]'hio).tick_insts.val[j.val]'htj = tk at htk etk
  have eins : (simStS tn s).insts[((simStS tn s).objs[i.val]'hioS).tickInsts[j.val]'htjS]'htkS =
      abs (s.insts.val[tk.val]'htk) := by simp only [etk]; simp [s3b_stS_insts]
  have efi : ((simCtxS tn fo c).pb.objects[i.val]'hiC).nested[j.val]'hjC =
      hobjS tn ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hj) := by
    simp only [sim_ctxS_object]; simp [topS]
  have evm : (simCtxS tn fo c).cfg.visMods.toList = c.cfg.vis_mods.val.map (fun v => (abs v : OsuModel.Sim.VisMod)) := by
    simp [simCtxS, abs, configS]
  simp only [eins, efi, evm]
  unfold sim.step.tick_state
  simp only [vec_index_eq _ _ hi, vec_index_eq _ _ hj, vec_index_eq _ _ hio, vec_index_eq _ _ htj, bind_ok, htkv,
    vec_index_eq _ _ htk, armed_eq_ok]
  have hloop := s3b_tick_outer c.cfg ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hj).fade_in passes
    passes.val 0#u64 s.theta (by simp) (by simp)
  rw [← s3b_tick_outer01] at hloop
  have hloop1 := s3b_tick_outer c.cfg ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hj).fade_in passes
    passes.val 0#u64 s.theta (by simp) (by simp)
  have hfi : (hobjS tn ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hj)).fadeIn =
      ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hj).fade_in := by simp [hobjS]
  rw [hfi]
  have hupd : ∀ th, simStS tn { s with insts := s.insts.set tk { s.insts.val[tk.val]'htk with armed := ns }, theta := th } =
      { simStS tn s with insts := (simStS tn s).insts.set tk.val { (abs (s.insts.val[tk.val]'htk) : OsuModel.Sim.Inst) with armed := abs ns } (by simpa [s3b_stS_insts] using htk),
                         theta := th } := by
    intro th
    have : ((s.insts.set tk { s.insts.val[tk.val]'htk with armed := ns }).val.map (fun x => (abs x : OsuModel.Sim.Inst))).toArray =
        (simStS tn s).insts.set tk.val { (abs (s.insts.val[tk.val]'htk) : OsuModel.Sim.Inst) with armed := abs ns } (by simpa [s3b_stS_insts] using htk) := by
      simp [s3b_stS_insts, alloc.vec.Vec.set, List.map_set]; rfl
    rw [← this]; rfl
  have hlen : ∀ x, (s.insts.set tk x).val.length = s.insts.val.length := by intro x; simp [alloc.vec.Vec.set]
  have habs : ((abs (s.insts.val[tk.val]'htk) : OsuModel.Sim.Inst).armed == abs ns) =
      (armedS (s.insts.val[tk.val]'htk).armed == armedS ns) := rfl
  rw [habs]
  have hspec : ∀ th, (Except.ok ((), { simStS tn s with
      insts := (simStS tn s).insts.set (((simStS tn s).objs[i.val]'hioS).tickInsts[j.val]'htjS)
        { (abs (s.insts.val[tk.val]'htk) : OsuModel.Sim.Inst) with armed := abs ns } htkS, theta := th }) :
        Except String (Unit × OsuModel.Sim.St)) =
      .ok ((), simStS tn (s3b_tickSt s tk htk ns th)) := by
    intro th; unfold s3b_tickSt; rw [hupd]; simp only [etk]
  by_cases ha : (armedS (s.insts.val[tk.val]'htk).armed == armedS ns) = true
  · cases force
    · exact ⟨s, by simp [ha], by simp [ha], ⟨s.insts, s.theta, rfl⟩, rfl, hinv, rfl, rfl, s3b_frame_refl s,
        rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩
    · refine ⟨s3b_tickSt s tk htk ns ((s3b_thetaStep (c.cfg.vis_mods.val.map (fun v => (abs v : OsuModel.Sim.VisMod)))
            (F64.toF32 ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hj).fade_in / 1000))^[passes.val] s.theta),
        by simp only [ha, if_true, vec_index_mut_eq _ _ htk, bind_ok, hloop, uncurry_apply_pair]; rfl, ?_,
        ⟨_, _, rfl⟩, hlen _, s3b_inv_of hinv rfl rfl, rfl, rfl, s3b_frame_refl s, s3b_tickSt_tfSame _ _ _ _ _⟩
      simp only [ha, Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false]
      exact hspec _
  · refine ⟨s3b_tickSt s tk htk ns ((s3b_thetaStep (c.cfg.vis_mods.val.map (fun v => (abs v : OsuModel.Sim.VisMod)))
            (F64.toF32 ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hj).fade_in / 1000))^[passes.val] s.theta),
      by simp only [ha, Bool.false_eq_true, if_false, vec_index_mut_eq _ _ htk, bind_ok, hloop1, uncurry_apply_pair]; rfl,
      ?_, ⟨_, _, rfl⟩, hlen _, s3b_inv_of hinv rfl rfl, rfl, rfl, s3b_frame_refl s, s3b_tickSt_tfSame _ _ _ _ _⟩
    simp only [ha, Bool.false_and, Bool.false_eq_true, if_false]
    exact hspec _

theorem sim.step.tick_state_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (i j : Usize) (passes : U64)
    (ns : sim.state.Armed) (force : Bool) (hinv : SimInv c s)
    (hi : i.val < c.pb.objects.val.length) (hj : j.val < (c.pb.objects.val[i.val]'hi).nested.val.length)
    (hio : i.val < s.objs.val.length) (htj : j.val < (s.objs.val[i.val]'hio).tick_insts.val.length)
    (htk : ((s.objs.val[i.val]'hio).tick_insts.val[j.val]'htj).val < s.insts.val.length) :
    ∃ s', sim.step.tick_state c s i j passes ns force = ok s' ∧
      OsuModel.Sim.Sim.tickState i.val j.val passes.val (abs ns) force (simCtxS tn fo c) (simStS tn s) =
        .ok ((), simStS tn s') ∧
      (∃ ins th, s' = { s with insts := ins, theta := th }) ∧ s'.insts.val.length = s.insts.val.length ∧
      SimInv c s' ∧ s'.future_order = s.future_order ∧ s'.objs = s.objs ∧ s3b_frame s s' := by
  obtain ⟨s', h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := s3b_tick_core tn fo c s i j passes ns force hinv hi hj hio htj htk
  exact ⟨s', h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- `tick_state` leaves every instance's transformables untouched (Rust side) -/
theorem sim.step.tick_state_tfSame (c : sim.state.Ctx) (s : sim.state.St) (i j : Usize) (passes : U64)
    (ns : sim.state.Armed) (force : Bool) (hinv : SimInv c s)
    (hi : i.val < c.pb.objects.val.length) (hj : j.val < (c.pb.objects.val[i.val]'hi).nested.val.length)
    (hio : i.val < s.objs.val.length) (htj : j.val < (s.objs.val[i.val]'hio).tick_insts.val.length)
    (htk : ((s.objs.val[i.val]'hio).tick_insts.val[j.val]'htj).val < s.insts.val.length)
    (s' : sim.state.St) (h : sim.step.tick_state c s i j passes ns force = ok s') : s3b_tfSame s s' := by
  obtain ⟨s'', h1, -, -, -, -, -, -, -, h9⟩ :=
    s3b_tick_core (fun _ => "") (alloc.vec.Vec.new Usize) c s i j passes ns force hinv hi hj hio htj htk
  rw [h] at h1; cases Result.ok_injective h1; exact h9

end OsuProofs
