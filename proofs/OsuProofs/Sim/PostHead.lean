/-
Slider head post-processing: `judge_started_nested` (loop `sim_jsn_loop`) and `post_process_head_judgement` against
`OsuModel.Sim.Sim.postProcessHeadJudgement`.
-/
import OsuProofs.Sim.ApplyFrame
import OsuProofs.Sim.Judge
import OsuProofs.Sim3.SA_PostHead
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- `judge_started_nested`'s loop on the context `c` -/
@[reducible] def simJSN (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (allIn : Bool) (nn j : Usize) (stop : Bool) :=
  sim.step.judge_started_nested_loop c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in c.pb.difficulty
    c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks c.pb.objects c.frames c.steps
    c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames c.block_periods
    c.first_obj s i allIn nn j stop

theorem sim_jsn_stop (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (allIn : Bool) (nn j : Usize) :
    simJSN c s i allIn nn j true = ok (.Ok (), s) := by
  unfold simJSN sim.step.judge_started_nested_loop
  rw [loop_unfold]
  by_cases h : j < nn <;> simp [sim.step.judge_started_nested_loop.body, h]

theorem sim_jsn_loop (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (e : Nat) (s0 : sim.state.St)
    (i : Usize) (hi : i.val < c.pb.objects.val.length) (allIn : Bool)
    (F : Nat → PUnit → OsuModel.Sim.SimM (ForInStep PUnit))
    (hF : ∀ j u, F j u = (do
      let b ← OsuModel.Sim.Sim.judged (i.val, (j : Int))
      if b = true then pure (ForInStep.yield PUnit.unit)
      else do
        let nh ← OsuModel.Sim.Sim.nestedOf (topS tn (c.pb.objects.val[i.val]'hi)) j
        if s0.t < nh.start then pure (ForInStep.done PUnit.unit)
        else if allIn = true then do
          OsuModel.Sim.Sim.hitForcefully (i.val, (j : Int))
          pure (ForInStep.yield PUnit.unit)
        else do
          OsuModel.Sim.Sim.missForcefully (i.val, (j : Int))
          pure (ForInStep.yield PUnit.unit))) (hL0 : simInstOk c s0 i.val) :
    ∀ m (j : Usize) (s : sim.state.St), (c.pb.objects.val[i.val]'hi).nested.val.length - j.val = m →
      j.val ≤ (c.pb.objects.val[i.val]'hi).nested.val.length →
      SimARInv tn fo P b0 n c s e 0 0 → simARFr s0 s →
      ∃ res s', simJSN c s i allIn (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) j false = ok (res, s') ∧
        simRelM tn s' res (forIn (m := OsuModel.Sim.SimM) (List.range' j.val m) PUnit.unit F (simCtxS tn fo c) (simStS tn s)) ∧
        (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ simARFr s0 s') := by
  have hsmall := fun h => (show (c.pb.objects.val[i.val]'hi).nested.val.length < 2 ^ 63 from h)
  intro m
  induction m with
  | zero =>
    intro j s hm hj hI hQ
    refine ⟨.Ok (), s, ?_, rfl, fun _ => ⟨hI, hQ⟩⟩
    unfold simJSN sim.step.judge_started_nested_loop
    rw [loop_unfold]
    have : ¬ j < alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested := by rw [vec_lt_len_iff]; omega
    simp [sim.step.judge_started_nested_loop.body, this]
  | succ m ih =>
    intro j s hm hj hI hQ
    have hjl : j.val < (c.pb.objects.val[i.val]'hi).nested.val.length := by omega
    have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
    have hsm := hI.inv.nested_small _ (List.getElem_mem hi)
    have hnl := hI.inv.nested_len _ ho hi
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := (c.pb.objects.val[i.val]'hi).nested.property; omega)
    have hlt : j < alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested := by rw [vec_lt_len_iff]; exact hjl
    have hcj : (UScalar.hcast .I64 j).val = (j.val : Int) := sim_usize_to_i64 j (by omega)
    have hrj : simRefOk c ⟨i, UScalar.hcast .I64 j⟩ := ⟨hi, fun _ => by
      show (UScalar.hcast .I64 j).val.toNat < _; rw [hcj]; simpa using hjl⟩
    have hsj : simSRefOk s ⟨i, UScalar.hcast .I64 j⟩ := ⟨ho, fun _ => by
      show (UScalar.hcast .I64 j).val.toNat < _; rw [hcj, hnl]; simpa using hjl⟩
    obtain ⟨ro, hrof, ero⟩ := sim.step.res_of_refines tn fo c s _ hsj
    have hjud : sim.step.judged s ⟨i, UScalar.hcast .I64 j⟩ = ok ro.isSome := by
      simp [sim.step.judged, hrof, core.option.Option.is_some]
    have ejud : OsuModel.Sim.Sim.judged (i.val, (j.val : Int)) (simCtxS tn fo c) (simStS tn s) =
        .ok (ro.isSome, simStS tn s) := by
      have e2 := ero
      have eabs : (abs (⟨i, UScalar.hcast .I64 j⟩ : sim.step.Ref) : Nat × Int) = (i.val, (j.val : Int)) := by
        simp [abs, hcj]
      rw [eabs] at e2
      unfold OsuModel.Sim.Sim.judged; simp [e2, Except.bind]
    have enj : OsuModel.Sim.Sim.nestedOf (topS tn (c.pb.objects.val[i.val]'hi)) j.val (simCtxS tn fo c) (simStS tn s) =
        .ok (hobjS tn ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl), simStS tn s) := by
      simp [OsuModel.Sim.Sim.nestedOf, OsuModel.Sim.Sim.getA, topS, hjl]
    have hts : s.t = s0.t := congrArg (fun x => x.2.1) hQ.keep
    have hc : (⟨c.env, c.cfg, ⟨c.pb.beatmap_version, c.pb.audio_lead_in, c.pb.difficulty, c.pb.base_difficulty,
        c.pb.slider_multiplier, c.pb.slider_tick_rate, c.pb.breaks, c.pb.objects⟩, c.frames, c.steps, c.head_idx,
        c.tail_idx, c.smax, c.hcfg, c.last_frame_time, c.corner_pow, c.prec_end, c.ap_frames, c.block_periods,
        c.first_obj⟩ : sim.state.Ctx) = c := rfl
    have hk : m = (c.pb.objects.val[i.val]'hi).nested.val.length - j1.val := by omega
    rw [List.range'_succ, List.forIn_cons, hF]
    simp only [simM_bind, ejud, Except.bind]
    have hstep : ∀ r, sim.step.judge_started_nested_loop.body c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in
              c.pb.difficulty c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks
              c.pb.objects c.frames c.steps c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow
              c.prec_end c.ap_frames c.block_periods c.first_obj i allIn
              (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) s j false = ok r →
        simJSN c s i allIn (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) j false =
          (match r with
            | .cont (s1, j1, st1) => simJSN c s1 i allIn (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) j1 st1
            | .done y => ok y) := by
      intro r hb
      unfold simJSN sim.step.judge_started_nested_loop
      rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]
      rcases r with ⟨s1, j1, st1⟩ | y <;> rfl
    cases hro : ro with
    | some x =>
      simp only [Option.isSome_some, if_true, simM_pure]
      have hb : sim.step.judge_started_nested_loop.body c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in
              c.pb.difficulty c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks
              c.pb.objects c.frames c.steps c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow
              c.prec_end c.ap_frames c.block_periods c.first_obj i allIn
              (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) s j false = ok (.cont (s, j1, false)) := by
        simp [sim.step.judge_started_nested_loop.body, hlt, lift, hjud, hro, hj1]
      rw [hstep _ hb]
      rw [show j.val + 1 = j1.val from hj1v.symm]
      exact ih j1 s (by omega) (by omega) hI hQ
    | none =>
      have hres : sim.step.res_of s ⟨i, UScalar.hcast .I64 j⟩ = ok none := hro ▸ hrof
      simp only [Option.isSome_none, Bool.false_eq_true, if_false, simM_bind, enj, Except.bind]
      have hst : (hobjS tn ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl)).start =
        ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl).start := rfl
      rw [hst]
      by_cases hlt2 : s0.t < ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl).start
      · have hb : sim.step.judge_started_nested_loop.body c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in
              c.pb.difficulty c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks
              c.pb.objects c.frames c.steps c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow
              c.prec_end c.ap_frames c.block_periods c.first_obj i allIn
              (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) s j false = ok (.cont (s, j1, true)) := by
          simp [sim.step.judge_started_nested_loop.body, hlt, lift, hjud, hro, hj1, vec_index_eq _ _ hi,
            vec_index_eq _ _ hjl, vec_index_usize_eq _ _ hjl, float.F64.lt, hts, hlt2]
        rw [hstep _ hb]
        simp only [hlt2, if_true, simM_pure]
        exact ⟨.Ok (), s, sim_jsn_stop c s i allIn _ j1, rfl, fun _ => ⟨hI, hQ⟩⟩
      · simp only [hlt2, if_false]
        by_cases hall : allIn = true
        · obtain ⟨res, s1, e1, r1, i1⟩ := sim.step.hit_forcefully_frame tn fo E b0 n c hC hCS hlen (simARFr s0)
            (fun _ => True) (fun _ _ _ => trivial) (simARFr_qok c s0 _) s _ e hI hQ trivial hrj (simInstOk_of_fr hQ hL0) hres
          have eabs : (abs (⟨i, UScalar.hcast .I64 j⟩ : sim.step.Ref) : Nat × Int) = (i.val, (j.val : Int)) := by
            simp [abs, hcj]
          rw [eabs] at r1
          rw [if_pos hall]
          cases res with
          | Err er =>
            obtain ⟨msg, hmsg⟩ := r1
            have hb : sim.step.judge_started_nested_loop.body c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in
                c.pb.difficulty c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks
                c.pb.objects c.frames c.steps c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow
                c.prec_end c.ap_frames c.block_periods c.first_obj i allIn
                (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) s j false = ok (.done (.Err er, s1)) := by
              simp only [sim.step.judge_started_nested_loop.body, hlt, if_true, lift, bind_ok, hjud, hro,
                vec_index_eq _ _ hi, vec_index_eq _ _ hjl, vec_index_usize_eq _ _ hjl, float.F64.lt, hts, hlt2, decide_false, Option.isSome_none,
                Bool.false_eq_true, if_false, hc, e1, uncurry_apply_pair, hall, ite_true, ite_false]
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]
            rw [hstep _ hb]
            refine ⟨.Err er, s1, rfl, ⟨msg, ?_⟩, fun h => by cases h⟩
            simp only [simM_bind, hmsg, Except.bind]
          | Ok u =>
            obtain ⟨hI1, hQ1⟩ := i1 rfl
            have hb : sim.step.judge_started_nested_loop.body c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in
                c.pb.difficulty c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks
                c.pb.objects c.frames c.steps c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow
                c.prec_end c.ap_frames c.block_periods c.first_obj i allIn
                (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) s j false = ok (.cont (s1, j1, false)) := by
              simp only [sim.step.judge_started_nested_loop.body, hlt, if_true, lift, bind_ok, hjud, hro,
                vec_index_eq _ _ hi, vec_index_eq _ _ hjl, vec_index_usize_eq _ _ hjl, float.F64.lt, hts, hlt2, decide_false, Option.isSome_none,
                Bool.false_eq_true, if_false, hc, e1, uncurry_apply_pair, hall, ite_true, ite_false]
              simp [core.result.Result.Insts.CoreOpsTry.branch, hj1]
            rw [hstep _ hb]
            simp only [simRelM] at r1
            simp only [simM_bind, r1, Except.bind, simM_pure]
            rw [show j.val + 1 = j1.val from hj1v.symm]
            exact ih j1 s1 (by omega) (by omega) hI1 hQ1
        · obtain ⟨res, s1, e1, r1, i1⟩ := sim.step.miss_forcefully_frame tn fo E b0 n c hC hCS hlen (simARFr s0)
            (fun _ => True) (fun _ _ _ => trivial) (simARFr_qok c s0 _) s _ e hI hQ trivial hrj (simInstOk_of_fr hQ hL0) hres
          have eabs : (abs (⟨i, UScalar.hcast .I64 j⟩ : sim.step.Ref) : Nat × Int) = (i.val, (j.val : Int)) := by
            simp [abs, hcj]
          rw [eabs] at r1
          rw [if_neg hall]
          cases res with
          | Err er =>
            obtain ⟨msg, hmsg⟩ := r1
            have hb : sim.step.judge_started_nested_loop.body c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in
                c.pb.difficulty c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks
                c.pb.objects c.frames c.steps c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow
                c.prec_end c.ap_frames c.block_periods c.first_obj i allIn
                (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) s j false = ok (.done (.Err er, s1)) := by
              simp only [sim.step.judge_started_nested_loop.body, hlt, if_true, lift, bind_ok, hjud, hro,
                vec_index_eq _ _ hi, vec_index_eq _ _ hjl, vec_index_usize_eq _ _ hjl, float.F64.lt, hts, hlt2, decide_false, Option.isSome_none,
                Bool.false_eq_true, if_false, hc, e1, uncurry_apply_pair, hall, ite_true, ite_false]
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]
            rw [hstep _ hb]
            refine ⟨.Err er, s1, rfl, ⟨msg, ?_⟩, fun h => by cases h⟩
            simp only [simM_bind, hmsg, Except.bind]
          | Ok u =>
            obtain ⟨hI1, hQ1⟩ := i1 rfl
            have hb : sim.step.judge_started_nested_loop.body c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in
                c.pb.difficulty c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks
                c.pb.objects c.frames c.steps c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow
                c.prec_end c.ap_frames c.block_periods c.first_obj i allIn
                (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) s j false = ok (.cont (s1, j1, false)) := by
              simp only [sim.step.judge_started_nested_loop.body, hlt, if_true, lift, bind_ok, hjud, hro,
                vec_index_eq _ _ hi, vec_index_eq _ _ hjl, vec_index_usize_eq _ _ hjl, float.F64.lt, hts, hlt2, decide_false, Option.isSome_none,
                Bool.false_eq_true, if_false, hc, e1, uncurry_apply_pair, hall, ite_true, ite_false]
              simp [core.result.Result.Insts.CoreOpsTry.branch, hj1]
            rw [hstep _ hb]
            simp only [simRelM] at r1
            simp only [simM_bind, r1, Except.bind, simM_pure]
            rw [show j.val + 1 = j1.val from hj1v.symm]
            exact ih j1 s1 (by omega) (by omega) hI1 hQ1

/-- the body of the second loop of `Sim.postProcessHeadJudgement` (judge the started nested objects) -/
def simJSNF (tn : Nat → String) (c : sim.state.Ctx) (i : Usize) (hi : i.val < c.pb.objects.val.length) (t : F64)
    (allIn : Bool) : Nat → PUnit → OsuModel.Sim.SimM (ForInStep PUnit) := fun j _ => do
  let b ← OsuModel.Sim.Sim.judged (i.val, (j : Int))
  if b = true then pure (ForInStep.yield PUnit.unit)
  else do
    let nh ← OsuModel.Sim.Sim.nestedOf (topS tn (c.pb.objects.val[i.val]'hi)) j
    if t < nh.start then pure (ForInStep.done PUnit.unit)
    else if allIn = true then do
      OsuModel.Sim.Sim.hitForcefully (i.val, (j : Int))
      pure (ForInStep.yield PUnit.unit)
    else do
      OsuModel.Sim.Sim.missForcefully (i.val, (j : Int))
      pure (ForInStep.yield PUnit.unit)

theorem sim_forIn_congrF {α β : Type} (l : List α) (b : β) (F G : α → β → OsuModel.Sim.SimM (ForInStep β))
    (h : ∀ a x, G a x = F a x) : forIn l b G = forIn l b F := by
  rw [show G = F from funext fun a => funext fun x => h a x]

theorem sim_forIn_congrR {β : Type} (r : Std.Legacy.Range) (b : β) (F G : Nat → β → OsuModel.Sim.SimM (ForInStep β))
    (h : ∀ a x, G a x = F a x) : forIn r b G = forIn r b F := by
  rw [show G = F from funext fun a => funext fun x => h a x]

/-- an object write that keeps the result slots and instance indices keeps the `apply_result` invariant -/
theorem sim_ar_inv_objw (tn fo P b0 n c s e) (hI : SimARInv tn fo P b0 n c s e 0 0) (i : Usize)
    (hi : i.val < s.objs.val.length) (o' : sim.state.OState)
    (h1 : o'.inst = (s.objs.val[i.val]'hi).inst) (h2 : o'.head_inst = (s.objs.val[i.val]'hi).head_inst)
    (h3 : o'.tick_insts = (s.objs.val[i.val]'hi).tick_insts) (h4 : o'.result = (s.objs.val[i.val]'hi).result)
    (h5 : o'.nested = (s.objs.val[i.val]'hi).nested)
    (hinv' : SimInv c { s with objs := s.objs.set i o' }) :
    SimARInv tn fo P b0 n c { s with objs := s.objs.set i o' } e 0 0 := by
  have hof : s3b_objFrame s { s with objs := s.objs.set i o' } := by
    refine ⟨by simp [vec_set_val'], fun j h h' => ?_⟩
    simp only [vec_set_val', List.getElem_set]
    split
    · subst_vars; exact ⟨h1, h2, h3, h4, h5⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hU := sim_unj_objFrame hof
  exact sim_ar_inv_hook tn fo P b0 n c s e 0 0 0 hI _ hinv' hof rfl hI.tf
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- the pressed-action lists stay small (`update_tracking` copies `pressed` into `last_pressed`) -/
def simLP (s : sim.state.St) : Prop :=
  s.pressed.len.val ≤ 3 ∧ ∀ j (h : j < s.objs.val.length), (s.objs.val[j]'h).last_pressed.len.val ≤ 3

theorem simLP_fr {s s' : sim.state.St} (h : simLP s) (hF : simARFr s s') : simLP s' := by
  refine ⟨?_, fun j hj => ?_⟩
  · have h3 : s'.pressed = s.pressed := congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.1) hF.keep
    rw [h3]; exact h.1
  · have hj0 : j < s.objs.val.length := by rw [← hF.len]; exact hj
    have h2 : (s'.objs.val[j]'hj).last_pressed = (s.objs.val[j]'hj0).last_pressed :=
      congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.1) (hF.ow j hj0 hj)
    rw [h2]; exact h.2 j hj0

theorem simLP_track {s : sim.state.St} (h : simLP s) (i : Usize) (o : sim.state.OState) (t endT : F64) (aj vp : Bool) :
    simLP { s with objs := s.objs.set i (s3aTracked o t endT aj vp s.pressed) } := by
  refine ⟨h.1, fun j hj => ?_⟩
  have hj0 : j < s.objs.val.length := by simpa [vec_set_val'] using hj
  simp only [vec_set_val', List.getElem_set]
  split
  · exact h.1
  · exact h.2 j hj0

/-- the object fields judgement processing (`apply_result` chain, `update_tracking`) never writes -/
def simKeepJ (o : sim.state.OState) :=
  (o.life, o.lifetime_start, o.child_id, o.hit_action, o.hovered, o.head_alive, o.inst, o.head_inst,
   o.tick_insts, o.tick_live, o.slider_mouse, o.spin_tracking, o.spin_mouse, o.last_angle, o.total_accumulated,
   o.accumulated_at_last_completion, o.current_spin_max, o.completed_spins, o.last_report_time, o.completed_full_spins)

/-- the frame of judgement processing -/
structure simJFr (s s' : sim.state.St) : Prop where
  keep : simKeepS s' = simKeepS s
  len : s'.objs.val.length = s.objs.val.length
  ow : ∀ j (h : j < s.objs.val.length) (h' : j < s'.objs.val.length), simKeepJ (s'.objs.val[j]'h') = simKeepJ (s.objs.val[j]'h)
  il : s'.insts.val.length = s.insts.val.length

theorem simJFr_refl (s : sim.state.St) : simJFr s s := ⟨rfl, rfl, fun _ _ _ => rfl, rfl⟩

theorem simJFr_trans {s1 s2 s3 : sim.state.St} (h1 : simJFr s1 s2) (h2 : simJFr s2 s3) : simJFr s1 s3 :=
  ⟨h2.keep.trans h1.keep, h2.len.trans h1.len, fun j h h' => (h2.ow j (by rw [h1.len]; exact h) h').trans (h1.ow j h _),
    h2.il.trans h1.il⟩

/-- the instances of an object survive judgement processing -/
theorem simInstOk_of_jfr {c : sim.state.Ctx} {s s' : sim.state.St} (h : simJFr s s') {i : Nat}
    (hL : simInstOk c s i) : simInstOk c s' i := by
  refine sim_instOk_keep ⟨h.len, fun j hj hj' => ?_⟩ (by rw [h.il]) hL
  have e := h.ow j hj hj'
  simp only [simKeepJ, Prod.mk.injEq] at e
  exact ⟨e.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2.2.1⟩

theorem simJFr_of_ar {s s' : sim.state.St} (h : simARFr s s') : simJFr s s' := by
  refine ⟨h.keep, h.len, fun j hj hj' => ?_, h.il⟩
  have e := h.ow j hj hj'
  simp only [simKeepO, Prod.mk.injEq] at e
  simp only [simKeepJ, e]

theorem simJFr_track (s : sim.state.St) (i : Usize) (hi : i.val < s.objs.val.length) (t endT : F64) (aj vp : Bool)
    (pr : replay.frames.ActList) :
    simJFr s { s with objs := s.objs.set i (s3aTracked (s.objs.val[i.val]'hi) t endT aj vp pr) } := by
  refine ⟨rfl, by simp [vec_set_val'], fun j hj hj' => ?_, rfl⟩
  simp only [vec_set_val', List.getElem_set]
  split
  · subst_vars; rfl
  · rfl

/-- `post_process_head_judgement` (Rust) refines `Sim.postProcessHeadJudgement` (`SliderInputManager.PostProcessHeadJudgement`)
for a slider; the `judge_started_nested` loop is `sim_jsn_loop` (carrying the `apply_result` field frame `simARFr`, which
keeps `t`, the slider mouse, `last_pressed`, `pressed` and the instance indices across the forced judgements). -/
-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem sim.step.post_process_head_judgement_refines (h64 : System.Platform.numBits = 64) (tn : Nat → String)
    (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (s : sim.state.St) (i : Usize) (e : Nat) (hI : SimARInv tn fo P b0 n c s e 0 0)
    (hi : i.val < c.pb.objects.val.length)
    (hsl : (c.pb.objects.val[i.val]'hi).h.kind = .Slider ∨
      ∃ r, simRefOk c r ∧ r.top.val = i.val ∧ (simHobj c r).kind = .Head)
    (hL : simInstOk c s i.val) (hp : s3aPathOk c i.val)
    (hLP : simLP s) :
    ∃ res s', sim.step.post_process_head_judgement c s i = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.postProcessHeadJudgement i.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ simJFr s s' ∧ simLP s') := by
  have hip : s3aInstOk s i.val := by obtain ⟨h1, h2, h3, _⟩ := hL; exact ⟨h1, h2, h3⟩
  have hlp : ∀ h : i.val < s.objs.val.length, (s.objs.val[i.val]'h).last_pressed.len.val ≤ 3 := fun h => hLP.2 _ h
  have hpr := hLP.1
  have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
  have hnl := hI.inv.nested_len _ ho hi
  obtain ⟨hhi, hh63, hhb⟩ := hC.hd i.val hi
  have hhl := hhb hsl
  have hch : (UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)).val = ((c.head_idx.val[i.val]'hhi).val : Int) :=
    sim_usize_to_i64 _ hh63
  have hsh : simSRefOk s ⟨i, UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)⟩ := ⟨ho, fun _ => by
    show (UScalar.hcast .I64 _).val.toNat < _; rw [hch, hnl]; simpa using hhl⟩
  have eabsh : (abs (⟨i, UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)⟩ : sim.step.Ref) : Nat × Int) =
      (i.val, ((c.head_idx.val[i.val]'hhi).val : Int)) := by simp [abs, hch]
  obtain ⟨bh, hbh, ebh⟩ := sim.step.judged_refines tn fo c s _ hsh
  obtain ⟨bk, hbk, ebk⟩ := sim.step.is_hit_ref_refines tn fo c s _ hsh
  rw [eabsh] at ebh ebk
  have ehead : OsuModel.Sim.Sim.headOf i.val (simCtxS tn fo c) (simStS tn s) =
      .ok ((c.head_idx.val[i.val]'hhi).val, simStS tn s) := by
    have hhi' : i.val < (simCtxS tn fo c).headIdx.size := by simpa [simCtxS, abs] using hhi
    simp [OsuModel.Sim.Sim.headOf, OsuModel.Sim.Sim.headIdxOf, OsuModel.Sim.Sim.getA, OsuModel.Sim.Sim.ctx,
      Except.bind, simCtxS, abs, hhi]
  rw [OsuModel.Sim.Sim.postProcessHeadJudgement.eq_1]
  unfold sim.step.post_process_head_judgement
  simp only [simM_bind, ehead, Except.bind, ebh, ebk, vec_index_eq _ _ hhi, lift, bind_ok, hbh]
  cases bh
  · simp only [Bool.not_false, Bool.true_or, ite_true, Bool.false_eq_true, ite_false]
    exact ⟨_, _, rfl, rfl, fun _ => ⟨hI, simJFr_refl s, hLP⟩⟩
  simp only [hbk, bind_ok, Bool.not_true, Bool.false_or, ite_true]
  cases bk
  · simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
    exact ⟨_, _, rfl, rfl, fun _ => ⟨hI, simJFr_refl s, hLP⟩⟩
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
  have hinv := hI.inv
  obtain ⟨r0, hr0, er0⟩ := sim.step.mouse_in_follow_area_refines h64 tn fo c s i true hinv hip hp
  simp only [hr0, bind_ok, simM_bind]
  cases r0 with
  | Err er =>
    obtain ⟨m, hm⟩ := er0
    refine ⟨.Err er, s, by simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], ⟨m, ?_⟩, fun h => by cases h⟩
    simp only [hm, Except.bind]
  | Ok v =>
    simp only [s3aR, id] at er0
    simp only [er0, Except.bind, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    cases v
    · simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
      exact ⟨_, _, rfl, rfl, fun _ => ⟨hI, simJFr_refl s, hLP⟩⟩
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    obtain ⟨g, hg, eg⟩ := sim.step.cur_slider_geom_refines tn fo c s i hinv hip
    obtain ⟨sr, hsr, esr⟩ := sim.step.slider_data_refines tn fo c i hi
    have esr' := esr (simStS tn s)
    simp only [hg, bind_ok, vec_index_eq _ _ ho, s3b_topObj tn fo c _ i.val hi, Except.bind]
    cases sr with
    | Err er =>
      -- impossible: `mouse_in_follow_area` succeeded, so the slider data exist
      exfalso
      obtain ⟨m, hm⟩ := esr'
      have : OsuModel.Sim.Sim.mouseInFollowArea i.val true (simCtxS tn fo c) (simStS tn s) = .error m := by
        unfold OsuModel.Sim.Sim.mouseInFollowArea
        simp only [simM_bind, s3b_topObj tn fo c _ i.val hi, Except.bind, hm]
      rw [this] at er0; cases er0
    | Ok sd =>
    have esr2 : OsuModel.Sim.Sim.sliderData i.val (simCtxS tn fo c) (simStS tn s) = .ok (abs sd, simStS tn s) := esr'
    have eos := s3a_ostate tn fo c s i.val ho
    simp only [simM_bind, s3b_topObj tn fo c _ i.val hi, esr2, eg, OsuModel.Sim.Sim.st, simM_get, eos, Except.bind,
      s3a_ostateS_sliderMouse]
    have hs : (c.pb.objects.val[i.val]'hi).slider = some sd := by
      unfold sim.step.slider_data at hsr
      simp only [vec_index_eq _ _ hi, bind_ok] at hsr
      split at hsr
      · simp at hsr
      · rename_i sd' h; simp at hsr; rw [h, hsr]
    cases hm : (s.objs.val[i.val]'ho).slider_mouse with
    | none => exact ⟨_, _, rfl, rfl, fun _ => ⟨hI, simJFr_refl s, hLP⟩⟩
    | some m =>
    simp only [Option.map_some]
    obtain ⟨m1, hm1, em1⟩ := sim.geometry.mouse_in_slider_refines g m
    rw [em1]
    obtain ⟨r1, hr1, er1⟩ := sim.step.all_nested_in_follow_area_refines h64 tn fo c s i m1 hinv ho hp
    have er1' := (er1 hi).2 sd hs
    rw [sim_forIn_congrR _ true (s3aAllInF i.val (topS tn (c.pb.objects.val[i.val]'hi)) (abs sd) s.t (abs m1)) _ ?hF1]
    case hF1 => intro j b; rfl
    simp only [hm1, bind_ok, hr1, simM_bind]
    cases r1 with
    | Err er =>
      obtain ⟨msg, hmsg⟩ := er1'
      refine ⟨.Err er, s, by simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual],
        ⟨msg, ?_⟩, fun h => by cases h⟩
      simp only [hmsg, Except.bind]
    | Ok allIn =>
    simp only [s3aR, id] at er1'
    simp only [er1', Except.bind]
    rw [sim_forIn_congrR _ PUnit.unit (simJSNF tn c i hi s.t allIn) _ ?hF2]
    case hF2 => intro j b; rfl
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    have hsz : (topS tn (c.pb.objects.val[i.val]'hi)).nested.size = (c.pb.objects.val[i.val]'hi).nested.val.length := by
      simp [topS]
    simp only [Std.Legacy.Range.size, Nat.div_one, Nat.sub_zero, Nat.add_sub_cancel, hsz]
    obtain ⟨res2, s1, e2, r2, i2⟩ := sim_jsn_loop tn fo E b0 n c hC hCS hlen e s i hi allIn
      (simJSNF tn c i hi s.t allIn) (fun _ _ => rfl) hL (c.pb.objects.val[i.val]'hi).nested.val.length 0#usize s
      (by simp) (by simp) hI (simARFr_refl s)
    have e2' : sim.step.judge_started_nested c s i allIn = ok (res2, s1) := by
      unfold sim.step.judge_started_nested; simp only [vec_index_eq _ _ hi, bind_ok]; exact e2
    simp only [bind_ok, e2', uncurry_apply_pair]
    have h00 : (0#usize).val = 0 := rfl
    simp only [h00, Nat.sub_zero] at r2
    cases res2 with
    | Err er =>
      obtain ⟨msg, hmsg⟩ := r2
      refine ⟨.Err er, s1, by simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual],
        ⟨msg, ?_⟩, fun h => by cases h⟩
      simp only [hmsg]
    | Ok u =>
    simp only [simRelM] at r2
    obtain ⟨hI1, hF1⟩ := i2 rfl
    simp only [r2, bind_ok]
    have ho1 : i.val < s1.objs.val.length := by rw [hF1.len]; exact ho
    have hip1 : s3aInstOk s1 i.val := by
      obtain ⟨h1, h2, h3, _⟩ := simInstOk_of_fr hF1 hL; exact ⟨h1, h2, h3⟩
    obtain ⟨r3, hr3, er3⟩ := sim.step.mouse_in_follow_area_refines h64 tn fo c s1 i false hI1.inv hip1 hp
    simp only [hr3, bind_ok]
    cases r3 with
    | Err er =>
      obtain ⟨msg, hmsg⟩ := er3
      refine ⟨.Err er, s1, by simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual],
        ⟨msg, ?_⟩, fun h => by cases h⟩
      simp only [hmsg]
    | Ok v2 =>
    simp only [s3aR, id] at er3
    simp only [er3]
    have hlp1 : (s1.objs.val[i.val]'ho1).last_pressed.len.val ≤ 3 := by
      have := congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.1) (hF1.ow i.val ho ho1)
      simp only [simKeepO] at this
      rw [this]; exact hlp ho
    have hpr1 : s1.pressed.len.val ≤ 3 := by
      have := congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.1) hF1.keep
      simp only [simKeepS] at this
      rw [this]; exact hpr
    obtain ⟨s2, e3, eS3, ⟨aj, hs2⟩, inv2, -⟩ := sim.step.update_tracking_refines tn fo c s1 i (allIn || v2) hI1.inv ho1
      hlp1 hpr1
    refine ⟨.Ok (), s2, ?_, eS3, fun _ => ⟨?_, ?_, ?_⟩⟩
    · cases allIn <;> simp only [Bool.false_or, Bool.true_or] at e3 <;> simp [e3]
    · rw [hs2]; rw [hs2] at inv2
      exact sim_ar_inv_objw tn fo P b0 n c s1 e hI1 i ho1 _ rfl rfl rfl rfl rfl inv2
    · rw [hs2]; exact simJFr_trans (simJFr_of_ar hF1) (simJFr_track s1 i ho1 _ _ aj _ _)
    · rw [hs2]; exact simLP_track (simLP_fr hLP hF1) i _ _ _ aj _

end OsuProofs
