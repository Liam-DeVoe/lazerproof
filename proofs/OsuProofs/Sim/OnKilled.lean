/-
`on_killed` (DrawableHitObject kill → `UpdateResult(false)`) against `OsuModel.Sim.Sim.onKilled`: the slider loop
(circle_update_result / try_judge_nested per unjudged nested, then slider_check_for_result), the spinner's
`miss_unjudged_nested` + `spinner_result` + `apply_result`, and the frame versions of try_judge_nested /
slider_check_for_result used by the loop.
-/
import OsuProofs.Sim.Circle
import OsuProofs.Sim3.SA_Spin
import OsuProofs.Sim3.SA_Geom
import OsuProofs.Sim3.SB_US2
import OsuProofs.Sim.MkHealthCfg
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

set_option hygiene false in
macro "tjn_jpF" : tactic => `(tactic| (
  simp only [vec_index_eq _ _ hhi, lift, bind_ok, hbh, simM_bind, ehead, ebh', Except.bind]
  cases bh
  · exact ⟨_, _, rfl, rfl, fun _ => ⟨hI, simARFr_refl s⟩⟩
  · simp only [vec_index_eq _ _ ho, bind_ok, simM_bind, eos, Except.bind, htrS, Bool.not_true, Bool.false_eq_true,
      ite_false, ite_true]
    cases htr : (s.objs.val[i.val]'ho).tracking
    · simp only [hf0, float.F64.le, bind_ok, ite_false, Bool.false_eq_true]
      by_cases h0 : (0 : F64) ≤ x
      · simp only [h0, decide_true, ite_true, emf, bind_ok, uncurry_apply_pair]
        exact sim_tjn_br tn _ _ _ (fun s' => SimARInv tn fo P b0 n c s' e 0 0 ∧ simARFr s s') rmf imf
      · simp only [h0, decide_false, ite_false, Bool.false_eq_true]
        exact ⟨_, _, rfl, rfl, fun _ => ⟨hI, simARFr_refl s⟩⟩
    · simp only [ite_true, ehf, bind_ok, uncurry_apply_pair]
      exact sim_tjn_br tn _ _ _ (fun s' => SimARInv tn fo P b0 n c s' e 0 0 ∧ simARFr s s') rhf ihf))

-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem sim.step.try_judge_nested_frame (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (s : sim.state.St) (i j : Usize) (e : Nat) (hI : SimARInv tn fo P b0 n c s e 0 0) (hIn : simInstOk c s i.val)
    (hi : i.val < c.pb.objects.val.length) (hj : j.val < (c.pb.objects.val[i.val]'hi).nested.val.length)
    (hsl : (c.pb.objects.val[i.val]'hi).h.kind = .Slider)
    (hres : sim.step.res_of s ⟨i, UScalar.hcast .I64 j⟩ = ok none) :
    ∃ res s', sim.step.try_judge_nested c s i j = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.tryJudgeNested i.val j.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ simARFr s s') := by
  have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
  have hsmall := hI.inv.nested_small _ (List.getElem_mem hi)
  have hnl := hI.inv.nested_len _ ho hi
  obtain ⟨hhi, hh63, hhb⟩ := hC.hd i.val hi
  have hhl := hhb (Or.inl hsl)
  have hcj : (UScalar.hcast .I64 j).val = (j.val : Int) := sim_usize_to_i64 j (by omega)
  have hch : (UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)).val = ((c.head_idx.val[i.val]'hhi).val : Int) :=
    sim_usize_to_i64 _ hh63
  have hrj : simRefOk c ⟨i, UScalar.hcast .I64 j⟩ := ⟨hi, fun _ => by
    show (UScalar.hcast .I64 j).val.toNat < _; rw [hcj]; simpa using hj⟩
  have hsh : simSRefOk s ⟨i, UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)⟩ := ⟨ho, fun _ => by
    show (UScalar.hcast .I64 _).val.toNat < _; rw [hch, hnl]; simpa using hhl⟩
  obtain ⟨bh, hbh, ebh⟩ := sim.step.judged_refines tn fo c s _ hsh
  have ebh' : OsuModel.Sim.Sim.judged (i.val, ((c.head_idx.val[i.val]'hhi).val : Int)) (simCtxS tn fo c) (simStS tn s) =
      .ok (bh, simStS tn s) := by
    rw [← ebh]; congr 2; simp [abs, hch]
  have ehead : OsuModel.Sim.Sim.headOf i.val (simCtxS tn fo c) (simStS tn s) =
      .ok ((c.head_idx.val[i.val]'hhi).val, simStS tn s) := by
    have hhi' : i.val < (simCtxS tn fo c).headIdx.size := by simpa [simCtxS, abs] using hhi
    simp [OsuModel.Sim.Sim.headOf, OsuModel.Sim.Sim.headIdxOf, OsuModel.Sim.Sim.getA, OsuModel.Sim.Sim.ctx, hhi',
      Except.bind, simCtxS, abs, hhi]
  have eabsj : (abs (⟨i, UScalar.hcast .I64 j⟩ : sim.step.Ref) : Nat × Int) = (i.val, (j.val : Int)) := by
    simp [abs, hcj]
  obtain ⟨rh, sh, ehf, rhf, ihf⟩ := sim.step.hit_forcefully_frame tn fo E b0 n c hC hCS hlen (simARFr s) (fun _ => True) (fun _ _ _ => trivial)
    (simARFr_qok c s _) s _ e hI (simARFr_refl s) trivial hrj hIn hres
  obtain ⟨rm, sm, emf, rmf, imf⟩ := sim.step.miss_forcefully_frame tn fo E b0 n c hC hCS hlen (simARFr s) (fun _ => True) (fun _ _ _ => trivial)
    (simARFr_qok c s _) s _ e hI (simARFr_refl s) trivial hrj hIn hres
  rw [eabsj] at rhf rmf
  have eos : OsuModel.Sim.Sim.ostate i.val (simCtxS tn fo c) (simStS tn s) = .ok (ostateS (s.objs.val[i.val]'ho), simStS tn s) := by
    rw [simS_ostate _ _ _ (by simpa using ho), sim_stS_obj]
  have hf0 : sim.step.F64_0 = ok (0 : F64) := by simp [sim.step.F64_0]
  have enj : OsuModel.Sim.Sim.nestedOf (topS tn (c.pb.objects.val[i.val]'hi)) j.val (simCtxS tn fo c) (simStS tn s) =
      .ok (hobjS tn ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hj), simStS tn s) := by
    simp [OsuModel.Sim.Sim.nestedOf, OsuModel.Sim.Sim.getA, topS, hj]
  have htrS : (ostateS (s.objs.val[i.val]'ho)).tracking = (s.objs.val[i.val]'ho).tracking := rfl
  rw [OsuModel.Sim.Sim.tryJudgeNested.eq_1]
  simp only [simM_bind, s3b_topObj tn fo c _ i.val hi, enj, Except.bind, OsuModel.Sim.Sim.st, simM_get]
  unfold sim.step.try_judge_nested
  simp only [vec_index_eq _ _ hi, vec_index_eq _ _ hj, bind_ok, float.F64.sub]
  have hT : (simStS tn s).t = s.t := rfl
  have hE : (hobjS tn ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hj)).endTime =
    ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hj).end_time := rfl
  have hK : (hobjS tn ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hj)).kind =
    kindS ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hj).kind := rfl
  simp only [hT, hE, hK]
  generalize s.t - ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hj).end_time = x
  cases hk : ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hj).kind <;>
    simp only [kindS, bind_ok, ite_false, Bool.false_eq_true]
  all_goals first | exact ⟨_, _, rfl, rfl, fun _ => ⟨hI, simARFr_refl s⟩⟩ | skip
  · -- tick
    simp only [hf0, float.F64.lt, bind_ok]
    by_cases hx0 : x < 0
    · simp only [hx0, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, decide_false]
      exact ⟨_, _, rfl, rfl, fun _ => ⟨hI, simARFr_refl s⟩⟩
    · have hb0 : decide (x < 0) = false := decide_eq_false hx0
      simp only [hb0, if_neg hx0, Bool.false_eq_true, not_false_eq_true, decide_true, ite_true]
      tjn_jpF
  · -- repeat
    simp only [hf0, float.F64.lt, bind_ok]
    by_cases hx0 : x < 0
    · simp only [hx0, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, decide_false]
      exact ⟨_, _, rfl, rfl, fun _ => ⟨hI, simARFr_refl s⟩⟩
    · have hb0 : decide (x < 0) = false := decide_eq_false hx0
      simp only [hb0, if_neg hx0, Bool.false_eq_true, not_false_eq_true, decide_true, ite_true]
      tjn_jpF
  · -- tail
    simp only [sim.step.TAIL_LENIENCY, fb64_13853635403745067008, float.F64.lt, bind_ok]
    by_cases hx0 : x < -36
    · simp only [hx0, decide_true, ite_true, bind_ok, Bool.false_eq_true, ite_false]
      exact ⟨_, _, rfl, rfl, fun _ => ⟨hI, simARFr_refl s⟩⟩
    · have hb0 : decide (x < -36) = false := decide_eq_false hx0
      simp only [hb0, if_neg hx0, Bool.false_eq_true, ite_false]
      obtain ⟨lt, hlt, elt⟩ := sim.step.last_tick_index_refines (c.pb.objects.val[i.val]'hi)
      rw [hlt]; simp only [bind_ok]
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      simp only [Std.Legacy.Range.size, Nat.div_one, Nat.sub_zero, Nat.add_sub_cancel, simM_bind]
      rw [sim_tjn_last_loop tn _ _ (c.pb.objects.val[i.val]'hi) _ (fun _ _ => rfl) _ 0 none (by simp [topS])]
      simp only [List.drop_zero, ← elt, Except.bind]
      cases lt with
      | none =>
        simp only [Option.map_none]
        tjn_jpF
      | some k =>
        simp only [Option.map_some]
        have hkl : k.val < (c.pb.objects.val[i.val]'hi).nested.val.length := by
          rcases sim_simLastP_lt simIsTR _ 0 none k.val elt.symm with h | h
          · simpa using h
          · cases h
        have hck : (UScalar.hcast .I64 k).val = (k.val : Int) := sim_usize_to_i64 k (by omega)
        have hsk : simSRefOk s ⟨i, UScalar.hcast .I64 k⟩ := ⟨ho, fun _ => by
          show (UScalar.hcast .I64 k).val.toNat < _; rw [hck, hnl]; simpa using hkl⟩
        obtain ⟨bk, hbk, ebk⟩ := sim.step.judged_refines tn fo c s _ hsk
        have ebk' : OsuModel.Sim.Sim.judged (i.val, (k.val : Int)) (simCtxS tn fo c) (simStS tn s) =
            .ok (bk, simStS tn s) := by
          rw [← ebk]; congr 2; simp [abs, hck]
        simp only [lift, bind_ok, hbk, simM_bind, ebk', Except.bind]
        cases bk
        · simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
          exact ⟨_, _, rfl, rfl, fun _ => ⟨hI, simARFr_refl s⟩⟩
        · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
          tjn_jpF

-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem sim.step.slider_check_for_result_frame (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (s : sim.state.St) (i : Usize) (e : Nat) (hI : SimARInv tn fo P b0 n c s e 0 0) (hIn : simInstOk c s i.val)
    (hi : i.val < c.pb.objects.val.length)
    (hti : i.val < c.tail_idx.val.length)
    (htl : (c.tail_idx.val[i.val]'hti).val < (c.pb.objects.val[i.val]'hi).nested.val.length)
    (hres : sim.step.res_of s ⟨i, (-1)#i64⟩ = ok none) :
    ∃ res s', sim.step.slider_check_for_result c s i = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.sliderCheckForResult i.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ simARFr s s') := by
  have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
  have hsmall := hI.inv.nested_small _ (List.getElem_mem hi)
  have hnl := hI.inv.nested_len _ ho hi
  have hct : (UScalar.hcast .I64 (c.tail_idx.val[i.val]'hti)).val = ((c.tail_idx.val[i.val]'hti).val : Int) :=
    sim_usize_to_i64 _ (by omega)
  have hst : simSRefOk s ⟨i, UScalar.hcast .I64 (c.tail_idx.val[i.val]'hti)⟩ := ⟨ho, fun _ => by
    show (UScalar.hcast .I64 _).val.toNat < _; rw [hct, hnl]; simpa using htl⟩
  obtain ⟨bt, hbt, ebt⟩ := sim.step.judged_refines tn fo c s _ hst
  have ebt' : OsuModel.Sim.Sim.judged (i.val, ((c.tail_idx.val[i.val]'hti).val : Int)) (simCtxS tn fo c) (simStS tn s) =
      .ok (bt, simStS tn s) := by
    rw [← ebt]; congr 2; simp [abs, hct]
  have etail : OsuModel.Sim.Sim.tailOf i.val (simCtxS tn fo c) (simStS tn s) =
      .ok ((c.tail_idx.val[i.val]'hti).val, simStS tn s) := by
    have hti' : i.val < (simCtxS tn fo c).tailIdx.size := by simpa [simCtxS, abs] using hti
    simp [OsuModel.Sim.Sim.tailOf, OsuModel.Sim.Sim.getA, OsuModel.Sim.Sim.ctx, Except.bind, simCtxS, abs, hti]
  have hr1 : simRefOk c ⟨i, (-1)#i64⟩ := ⟨hi, fun h => by simp at h⟩
  have eabs1 : (abs (⟨i, (-1)#i64⟩ : sim.step.Ref) : Nat × Int) = (i.val, -1) := by simp [abs]
  have eos := s3a_ostate tn fo c s i.val ho
  have hT : (simStS tn s).t = s.t := rfl
  have hE : (hobjS tn (c.pb.objects.val[i.val]'hi).h).endTime = (c.pb.objects.val[i.val]'hi).h.end_time := rfl
  rw [OsuModel.Sim.Sim.sliderCheckForResult.eq_1]
  unfold sim.step.slider_check_for_result
  simp only [simM_bind, s3b_topObj tn fo c _ i.val hi, Except.bind, OsuModel.Sim.Sim.st, simM_get, etail, ebt',
    vec_index_eq _ _ hi, vec_index_eq _ _ hti, lift, bind_ok, hbt, hT, hE]
  have hE' : (topS tn (c.pb.objects.val[i.val]'hi)).h.endTime = (c.pb.objects.val[i.val]'hi).h.end_time := rfl
  rw [hE']
  cases bt
  · simp only [Bool.false_eq_true, ite_false, Bool.not_false, Bool.true_or, ite_true]
    exact ⟨_, _, rfl, rfl, fun _ => ⟨hI, simARFr_refl s⟩⟩
  · by_cases hlt : s.t < (c.pb.objects.val[i.val]'hi).h.end_time
    · simp only [ite_true, float.F64.lt, hlt, decide_true, bind_ok, Bool.not_true, Bool.false_or]
      exact ⟨_, _, rfl, rfl, fun _ => ⟨hI, simARFr_refl s⟩⟩
    · simp only [ite_true, float.F64.lt, hlt, decide_false, bind_ok, Bool.not_true, Bool.false_or,
        Bool.false_eq_true, ite_false]
      obtain ⟨sr, hsr, esr⟩ := sim.step.slider_data_refines tn fo c i hi
      have esr' := esr (simStS tn s)
      rw [hsr]; simp only [bind_ok]
      cases sr with
      | Err er =>
        obtain ⟨m, hm⟩ := esr'
        refine ⟨.Err er, s, by simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], ⟨m, ?_⟩, fun h => by cases h⟩
        simp only [simM_bind, hm, Except.bind]
      | Ok sd =>
        have esr2 : OsuModel.Sim.Sim.sliderData i.val (simCtxS tn fo c) (simStS tn s) = .ok (abs sd, simStS tn s) := esr'
        obtain ⟨hits, hh, hhv⟩ := sim.step.count_nested_hits_refines (s.objs.val[i.val]'ho) (by omega)
        obtain ⟨f, hf, hfS⟩ := sim.step.max_fuel_refines tn fo c hlen (simStS tn s)
        have htot : (UScalar.cast .U64 (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested)).val =
            (topS tn (c.pb.objects.val[i.val]'hi)).nested.size := by
          simp [topS]
        obtain ⟨ty, hty, ety⟩ := sim.step.slider_result_refines sd.classic hits
          (UScalar.cast .U64 (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested))
          (c.pb.objects.val[i.val]'hi).h.max_result (c.pb.objects.val[i.val]'hi).h.min_result
        obtain ⟨res, s', ear, rar, iar⟩ := sim.step.apply_result_frame tn fo E b0 n c hC hCS (simARFr s) (fun _ => True) (fun _ _ _ => trivial)
          (simARFr_qok c s _) s f _ ty e hI (simARFr_refl s) trivial hr1 hIn hres
        refine ⟨res, s', ?_, ?_, iar⟩
        · simp [core.result.Result.Insts.CoreOpsTry.branch, vec_index_eq _ _ ho, hh, hty, hf, ear]
        · rw [eabs1, show (abs ty : OsuModel.Sim.HitResult) = hrS ty from rfl, ety, hhv, htot] at rar
          simp only [simM_bind, esr2, eos, hfS, Except.bind]
          exact rar

@[reducible] def simOKL (c : sim.state.Ctx) (s : sim.state.St) (i j : Usize) :=
  sim.step.on_killed_loop c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in c.pb.difficulty
    c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks c.pb.objects c.frames c.steps
    c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames c.block_periods
    c.first_obj s i j

@[reducible] def simOKB (c : sim.state.Ctx) (s : sim.state.St) (i j : Usize) :=
  sim.step.on_killed_loop.body c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in c.pb.difficulty
    c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks c.pb.objects c.frames c.steps
    c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames c.block_periods
    c.first_obj i s j

theorem sim_okl_step (c : sim.state.Ctx) (s : sim.state.St) (i j : Usize) (r) (hb : simOKB c s i j = ok r) :
    simOKL c s i j = (match r with
      | .cont (s1, j1) => simOKL c s1 i j1
      | .done y => ok y) := by
  unfold simOKL sim.step.on_killed_loop
  rw [loop_unfold]; dsimp only; rw [show sim.step.on_killed_loop.body _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s j
    = ok r from hb]; simp only [bind_ok]
  rcases r with ⟨s1, j1⟩ | y <;> rfl

theorem sim_okl_loop (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (e : Nat) (s0 : sim.state.St)
    (i : Usize) (hi : i.val < c.pb.objects.val.length) (hsl : (c.pb.objects.val[i.val]'hi).h.kind = .Slider)
    (hp : s3aPathOk c i.val) (hti : i.val < c.tail_idx.val.length)
    (htl : (c.tail_idx.val[i.val]'hti).val < (c.pb.objects.val[i.val]'hi).nested.val.length)
    (F : Nat → PUnit → OsuModel.Sim.SimM (ForInStep PUnit))
    (hF : ∀ j u, F j u = (do
      let b ← OsuModel.Sim.Sim.judged (i.val, (j : Int))
      if b = true then pure (ForInStep.yield PUnit.unit)
      else do
        let nh ← OsuModel.Sim.Sim.nestedOf (topS tn (c.pb.objects.val[i.val]'hi)) j
        if (nh.kind == OsuModel.Sim.Kind.head) = true then do
          OsuModel.Sim.Sim.circleUpdateResult (i.val, (j : Int)) false
          pure (ForInStep.yield PUnit.unit)
        else do
          OsuModel.Sim.Sim.tryJudgeNested i.val j
          pure (ForInStep.yield PUnit.unit)))
    (K : PUnit → OsuModel.Sim.SimM Unit)
    (hK : ∀ u, K u = (do
      let os ← OsuModel.Sim.Sim.ostate i.val
      if os.result.isNone = true then OsuModel.Sim.Sim.sliderCheckForResult i.val else pure ()))
    (hIn0 : simInstOk c s0 i.val) :
    ∀ m (j : Usize) (s : sim.state.St), (c.pb.objects.val[i.val]'hi).nested.val.length - j.val = m →
      j.val ≤ (c.pb.objects.val[i.val]'hi).nested.val.length →
      SimARInv tn fo P b0 n c s e 0 0 → simJFr s0 s → simLP s →
      ∃ res s', simOKL c s i j = ok (res, s') ∧
        simRelM tn s' res ((forIn (m := OsuModel.Sim.SimM) (List.range' j.val m) PUnit.unit F >>= K)
          (simCtxS tn fo c) (simStS tn s)) ∧
        (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ simJFr s0 s' ∧ simLP s') := by
  have hc : (⟨c.env, c.cfg, ⟨c.pb.beatmap_version, c.pb.audio_lead_in, c.pb.difficulty, c.pb.base_difficulty,
      c.pb.slider_multiplier, c.pb.slider_tick_rate, c.pb.breaks, c.pb.objects⟩, c.frames, c.steps, c.head_idx,
      c.tail_idx, c.smax, c.hcfg, c.last_frame_time, c.corner_pow, c.prec_end, c.ap_frames, c.block_periods,
      c.first_obj⟩ : sim.state.Ctx) = c := rfl
  intro m
  induction m with
  | zero =>
    intro j s hm hj hI hQ hL
    have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
    have hge : ¬ j < alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested := by rw [vec_lt_len_iff]; omega
    have hge' : ¬ (j.val < (c.pb.objects.val[i.val]'hi).nested.val.length) := by omega
    simp only [List.range'_zero, List.forIn_nil, simM_bind, simM_pure, Except.bind, hK,
      s3a_ostate tn fo c s i.val ho]
    have hrS : (ostateS (s.objs.val[i.val]'ho)).result = (s.objs.val[i.val]'ho).result.map abs := rfl
    rw [hrS]
    cases hro : (s.objs.val[i.val]'ho).result with
    | some x =>
      have hb : simOKB c s i j = ok (.done (.Ok (), s)) := by
        simp [sim.step.on_killed_loop.body, hge, hge', vec_index_eq _ _ hi, vec_index_eq _ _ ho, hro,
          core.option.Option.is_none]
      rw [sim_okl_step c s i j _ hb]
      exact ⟨_, _, rfl, rfl, fun _ => ⟨hI, hQ, hL⟩⟩
    | none =>
      have hres : sim.step.res_of s ⟨i, (-1)#i64⟩ = ok none := by
        simp [sim.step.res_of, vec_index_eq _ _ ho, hro]
      obtain ⟨rs, ss, es, rls, ils⟩ := sim.step.slider_check_for_result_frame tn fo E b0 n c hC hCS hlen s i e hI (simInstOk_of_jfr hQ hIn0) hi hti
        htl hres
      simp only [Option.map_none, Option.isNone_none, ite_true]
      cases rs with
      | Err er =>
        have hb : simOKB c s i j = ok (.done (.Err er, ss)) := by
          simp only [sim.step.on_killed_loop.body, hge, hge', alloc.vec.Vec.len, if_false, vec_index_eq _ _ hi, vec_index_eq _ _ ho, bind_ok,
            hro, core.option.Option.is_none, ite_true, hc, es, uncurry_apply_pair]
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        rw [sim_okl_step c s i j _ hb]
        exact ⟨_, _, rfl, rls, fun h => by cases h⟩
      | Ok u =>
        have hb : simOKB c s i j = ok (.done (.Ok (), ss)) := by
          simp only [sim.step.on_killed_loop.body, hge, hge', alloc.vec.Vec.len, if_false, vec_index_eq _ _ hi, vec_index_eq _ _ ho, bind_ok,
            hro, core.option.Option.is_none, ite_true, hc, es, uncurry_apply_pair]
          simp [core.result.Result.Insts.CoreOpsTry.branch]
        rw [sim_okl_step c s i j _ hb]
        obtain ⟨hI1, hF1⟩ := ils rfl
        exact ⟨_, _, rfl, rls, fun _ => ⟨hI1, simJFr_trans hQ (simJFr_of_ar hF1), simLP_fr hL hF1⟩⟩
  | succ m ih =>
    intro j s hm hj hI hQ hL
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
    have eabs : (abs (⟨i, UScalar.hcast .I64 j⟩ : sim.step.Ref) : Nat × Int) = (i.val, (j.val : Int)) := by
      simp [abs, hcj]
    have ejud : OsuModel.Sim.Sim.judged (i.val, (j.val : Int)) (simCtxS tn fo c) (simStS tn s) =
        .ok (ro.isSome, simStS tn s) := by
      have e2 := ero
      rw [eabs] at e2
      unfold OsuModel.Sim.Sim.judged; simp [e2, Except.bind]
    have enj : OsuModel.Sim.Sim.nestedOf (topS tn (c.pb.objects.val[i.val]'hi)) j.val (simCtxS tn fo c) (simStS tn s) =
        .ok (hobjS tn ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl), simStS tn s) := by
      simp [OsuModel.Sim.Sim.nestedOf, OsuModel.Sim.Sim.getA, topS, hjl]
    have hk : m = (c.pb.objects.val[i.val]'hi).nested.val.length - j1.val := by omega
    have hoi : c.pb.objects.index_usize i = ok (c.pb.objects.val[i.val]'hi) := vec_index_usize_eq _ _ hi
    have hnj : (c.pb.objects.val[i.val]'hi).nested.index_usize j =
      ok ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl) := vec_index_usize_eq _ _ hjl
    have hKH : kindS sim.playable.Kind.Head = OsuModel.Sim.Kind.head := rfl
    rw [List.range'_succ, List.forIn_cons, hF]
    simp only [simM_bind, ejud, Except.bind]
    cases hro : ro with
    | some x =>
      simp only [Option.isSome_some, if_true, simM_pure]
      have hb : simOKB c s i j = ok (.cont (s, j1)) := by
        simp [sim.step.on_killed_loop.body, hlt, hjl, hoi, hnj, hKH, lift, hjud, hro, hj1]
      rw [sim_okl_step c s i j _ hb]
      rw [show j.val + 1 = j1.val from hj1v.symm]
      exact ih j1 s (by omega) (by omega) hI hQ hL
    | none =>
      have hres : sim.step.res_of s ⟨i, UScalar.hcast .I64 j⟩ = ok none := hro ▸ hrof
      simp only [Option.isSome_none, Bool.false_eq_true, if_false, simM_bind, enj, Except.bind]
      have hkd : (hobjS tn ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl)).kind =
        kindS ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl).kind := rfl
      rw [hkd]
      by_cases hkh : (kindS ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl).kind == OsuModel.Sim.Kind.head) = true
      · rw [if_pos hkh]
        obtain ⟨res, s1, e1, r1, i1⟩ := sim.step.circle_update_result_refines h64 tn fo E b0 n c hC hCS hlen s
          ⟨i, UScalar.hcast .I64 j⟩ false e hI hrj (simInstOk_of_jfr hQ hIn0) hp hL
        rw [eabs] at r1
        cases res with
        | Err er =>
          obtain ⟨msg, hmsg⟩ := r1
          have hb : simOKB c s i j = ok (.done (.Err er, s1)) := by
            simp only [sim.step.on_killed_loop.body, hlt, hjl, hoi, hnj, hKH, if_true, lift, bind_ok, hjud, hro,
              vec_index_eq _ _ hi, vec_index_usize_eq _ _ hjl, Option.isSome_none,
              Bool.false_eq_true, if_false, hc, e1, uncurry_apply_pair]
            simp [hnj, hKH, hkh, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]
          rw [sim_okl_step c s i j _ hb]
          refine ⟨.Err er, s1, rfl, ⟨msg, ?_⟩, fun h => by cases h⟩
          simp only [simM_bind, hmsg, Except.bind]
        | Ok u =>
          obtain ⟨hI1, hQ1, hL1⟩ := i1 rfl
          have hb : simOKB c s i j = ok (.cont (s1, j1)) := by
            simp only [sim.step.on_killed_loop.body, hlt, hjl, hoi, hnj, hKH, if_true, lift, bind_ok, hjud, hro,
              vec_index_eq _ _ hi, vec_index_usize_eq _ _ hjl, Option.isSome_none,
              Bool.false_eq_true, if_false, hc, e1, uncurry_apply_pair]
            simp [hnj, hKH, hkh, core.result.Result.Insts.CoreOpsTry.branch, hj1]
          rw [sim_okl_step c s i j _ hb]
          simp only [simRelM] at r1
          simp only [simM_bind, r1, Except.bind, simM_pure]
          rw [show j.val + 1 = j1.val from hj1v.symm]
          exact ih j1 s1 (by omega) (by omega) hI1 (simJFr_trans hQ hQ1) hL1
      · rw [if_neg hkh]
        obtain ⟨res, s1, e1, r1, i1⟩ := sim.step.try_judge_nested_frame tn fo E b0 n c hC hCS hlen s i j e hI (simInstOk_of_jfr hQ hIn0) hi hjl
          hsl hres
        cases res with
        | Err er =>
          obtain ⟨msg, hmsg⟩ := r1
          have hb : simOKB c s i j = ok (.done (.Err er, s1)) := by
            simp only [sim.step.on_killed_loop.body, hlt, hjl, hoi, hnj, hKH, if_true, lift, bind_ok, hjud, hro,
              vec_index_eq _ _ hi, vec_index_usize_eq _ _ hjl, Option.isSome_none,
              Bool.false_eq_true, if_false, hc, e1, uncurry_apply_pair]
            simp [hnj, hKH, hkh, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]
          rw [sim_okl_step c s i j _ hb]
          refine ⟨.Err er, s1, rfl, ⟨msg, ?_⟩, fun h => by cases h⟩
          simp only [simM_bind, hmsg, Except.bind]
        | Ok u =>
          obtain ⟨hI1, hQ1⟩ := i1 rfl
          have hb : simOKB c s i j = ok (.cont (s1, j1)) := by
            simp only [sim.step.on_killed_loop.body, hlt, hjl, hoi, hnj, hKH, if_true, lift, bind_ok, hjud, hro,
              vec_index_eq _ _ hi, vec_index_usize_eq _ _ hjl, Option.isSome_none,
              Bool.false_eq_true, if_false, hc, e1, uncurry_apply_pair]
            simp [hnj, hKH, hkh, core.result.Result.Insts.CoreOpsTry.branch, hj1]
          rw [sim_okl_step c s i j _ hb]
          simp only [simRelM] at r1
          simp only [simM_bind, r1, Except.bind, simM_pure]
          rw [show j.val + 1 = j1.val from hj1v.symm]
          exact ih j1 s1 (by omega) (by omega) hI1 (simJFr_trans hQ (simJFr_of_ar hQ1)) (simLP_fr hL hQ1)

/-- the spec's spinner judgement (`onKilled`/`updateSpinner`): progress → result -/
def simSpinTy (p : F32) (mr : OsuModel.Sim.HitResult) : OsuModel.Sim.HitResult :=
  if (1 : F32) ≤ p then .great
  else if 0.9 < F32.toF64 p then .ok
  else if 0.75 < F32.toF64 p then .meh
  else mr

-- CONDITIONAL: h (completed_spins * 360 < 2^63, from spinner_progress_refines; overflow-free spin count)
theorem sim.step.spinner_result_refines (o : sim.playable.TopObj) (sp : sim.playable.SpinnerData) (os : sim.state.OState)
    (h : os.completed_spins.val * 360 < 2 ^ 63) :
    ∃ ty, sim.step.spinner_result o sp os = ok ty ∧
      hrS ty = simSpinTy (OsuModel.Sim.Sim.spinnerProgress (abs sp) (abs os)) (hrS o.h.min_result) := by
  unfold sim.step.spinner_result simSpinTy
  simp only [sim.step.spinner_progress_refines sp os h, bind_ok, sim_basic_F32_1, float.F32.le, sim_hp_to_f64,
    fb64_4606281698874543309, fb64_4604930618986332160, float.F64.lt]
  generalize OsuModel.Sim.Sim.spinnerProgress (abs sp) (abs os) = p
  by_cases h1 : (1 : F32) ≤ p <;> simp [h1] <;>
  by_cases h2 : (0.9 : F64) < p.toF64 <;> simp [h2, hrS] <;>
  by_cases h3 : (0.75 : F64) < p.toF64 <;> simp [h3, hrS]

theorem sim_spin_hA (c : sim.state.Ctx) (i : Usize) (hi : i.val < c.pb.objects.val.length)
    (hsp : (c.pb.objects.val[i.val]'hi).h.kind = .Spinner) :
    ∀ r, simRefOk c r → sim.step.circle_like c r = ok true → ¬ (r.top.val = i.val ∧ r.nested.val < 0) := by
  intro r hr hcl ⟨ht, hn⟩
  rw [sim_circle_like_eq c r hr] at hcl
  have : (c.pb.objects.val[r.top.val]!) = c.pb.objects.val[i.val]'hi := by
    rw [ht]; exact getElem!_pos _ _ _
  simp [simHobj, hn, this, hsp, kindS, OsuModel.Sim.Kind.isCircleLike] at hcl

@[reducible] def simMUN (c : sim.state.Ctx) (s : sim.state.St) (i n j : Usize) :=
  sim.step.miss_unjudged_nested_loop c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in c.pb.difficulty
    c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks c.pb.objects c.frames c.steps
    c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames c.block_periods
    c.first_obj s i n j

@[reducible] def simMUB (c : sim.state.Ctx) (s : sim.state.St) (i n j : Usize) :=
  sim.step.miss_unjudged_nested_loop.body c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in c.pb.difficulty
    c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks c.pb.objects c.frames c.steps
    c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames c.block_periods
    c.first_obj i n s j

theorem sim_mun_step (c : sim.state.Ctx) (s : sim.state.St) (i n j : Usize) (r) (hb : simMUB c s i n j = ok r) :
    simMUN c s i n j = (match r with
      | .cont (s1, j1) => simMUN c s1 i n j1
      | .done y => ok y) := by
  unfold simMUN sim.step.miss_unjudged_nested_loop
  rw [loop_unfold]; dsimp only; rw [show sim.step.miss_unjudged_nested_loop.body _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s j
    = ok r from hb]; simp only [bind_ok]
  rcases r with ⟨s1, j1⟩ | y <;> rfl

/-- the spinner's `miss_unjudged_nested` loop: keeps the apply_result frame and the (unset) top result -/
theorem sim_mun_loop (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (e : Nat) (s0 : sim.state.St)
    (i : Usize) (hi : i.val < c.pb.objects.val.length) (hsp : (c.pb.objects.val[i.val]'hi).h.kind = .Spinner)
    (F : Nat → PUnit → OsuModel.Sim.SimM (ForInStep PUnit))
    (hF : ∀ j u, F j u = (do
      let b ← OsuModel.Sim.Sim.judged (i.val, (j : Int))
      if (!b) = true then do
        OsuModel.Sim.Sim.missForcefully (i.val, (j : Int))
        pure (ForInStep.yield PUnit.unit)
      else pure (ForInStep.yield PUnit.unit))) (hIn0 : simInstOk c s0 i.val) :
    ∀ m (j : Usize) (s : sim.state.St), (c.pb.objects.val[i.val]'hi).nested.val.length - j.val = m →
      j.val ≤ (c.pb.objects.val[i.val]'hi).nested.val.length →
      SimARInv tn fo P b0 n c s e 0 0 → simARFr s0 s → simTopRes i.val none s →
      ∃ res s', simMUN c s i (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) j = ok (res, s') ∧
        simRelM tn s' res (forIn (m := OsuModel.Sim.SimM) (List.range' j.val m) PUnit.unit F (simCtxS tn fo c) (simStS tn s)) ∧
        (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ simARFr s0 s' ∧ simTopRes i.val none s') := by
  have hc : (⟨c.env, c.cfg, ⟨c.pb.beatmap_version, c.pb.audio_lead_in, c.pb.difficulty, c.pb.base_difficulty,
      c.pb.slider_multiplier, c.pb.slider_tick_rate, c.pb.breaks, c.pb.objects⟩, c.frames, c.steps, c.head_idx,
      c.tail_idx, c.smax, c.hcfg, c.last_frame_time, c.corner_pow, c.prec_end, c.ap_frames, c.block_periods,
      c.first_obj⟩ : sim.state.Ctx) = c := rfl
  have hQ := SimQOk.and (simARFr_qok c s0 (fun _ => True)) (simTopRes_qok c i.val none)
  have hA : ∀ r, simRefOk c r → sim.step.circle_like c r = ok true →
      (True ∧ ¬ (r.top.val = i.val ∧ r.nested.val < 0)) :=
    fun r hr hcl => ⟨trivial, sim_spin_hA c i hi hsp r hr hcl⟩
  intro m
  induction m with
  | zero =>
    intro j s hm hj hI hQ0 hT
    refine ⟨.Ok (), s, ?_, rfl, fun _ => ⟨hI, hQ0, hT⟩⟩
    have hb : simMUB c s i (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) j = ok (.done (.Ok (), s)) := by
      have : ¬ j < alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested := by rw [vec_lt_len_iff]; omega
      simp [sim.step.miss_unjudged_nested_loop.body, this]
    rw [sim_mun_step c s i _ j _ hb]
  | succ m ih =>
    intro j s hm hj hI hQ0 hT
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
    have eabs : (abs (⟨i, UScalar.hcast .I64 j⟩ : sim.step.Ref) : Nat × Int) = (i.val, (j.val : Int)) := by
      simp [abs, hcj]
    have ejud : OsuModel.Sim.Sim.judged (i.val, (j.val : Int)) (simCtxS tn fo c) (simStS tn s) =
        .ok (ro.isSome, simStS tn s) := by
      have e2 := ero
      rw [eabs] at e2
      unfold OsuModel.Sim.Sim.judged; simp [e2, Except.bind]
    rw [List.range'_succ, List.forIn_cons, hF]
    simp only [simM_bind, ejud, Except.bind]
    cases hro : ro with
    | some x =>
      simp only [Option.isSome_some, Bool.not_true, Bool.false_eq_true, if_false, simM_pure]
      have hb : simMUB c s i (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) j = ok (.cont (s, j1)) := by
        simp [sim.step.miss_unjudged_nested_loop.body, hlt, lift, hjud, hro, hj1]
      rw [sim_mun_step c s i _ j _ hb]
      rw [show j.val + 1 = j1.val from hj1v.symm]
      exact ih j1 s (by omega) (by omega) hI hQ0 hT
    | none =>
      have hres : sim.step.res_of s ⟨i, UScalar.hcast .I64 j⟩ = ok none := hro ▸ hrof
      simp only [Option.isSome_none, Bool.not_false, if_true]
      have hAr : True ∧ ¬ ((⟨i, UScalar.hcast .I64 j⟩ : sim.step.Ref).top.val = i.val ∧
          (⟨i, UScalar.hcast .I64 j⟩ : sim.step.Ref).nested.val < 0) :=
        ⟨trivial, fun ⟨_, hn⟩ => by simp only [hcj] at hn; omega⟩
      obtain ⟨res, s1, e1, r1, i1⟩ := sim.step.miss_forcefully_frame tn fo E b0 n c hC hCS hlen _ _ hA hQ
        s _ e hI ⟨hQ0, hT⟩ hAr hrj (simInstOk_of_fr hQ0 hIn0) hres
      rw [eabs] at r1
      cases res with
      | Err er =>
        obtain ⟨msg, hmsg⟩ := r1
        have hb : simMUB c s i (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) j = ok (.done (.Err er, s1)) := by
          simp only [sim.step.miss_unjudged_nested_loop.body, hlt, if_true, lift, bind_ok, hjud, hro,
            Option.isSome_none, Bool.false_eq_true, if_false, hc, e1, uncurry_apply_pair]
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]
        rw [sim_mun_step c s i _ j _ hb]
        refine ⟨.Err er, s1, rfl, ⟨msg, ?_⟩, fun h => by cases h⟩
        simp only [simM_bind, hmsg, Except.bind]
      | Ok u =>
        obtain ⟨hI1, hQ1, hT1⟩ := i1 rfl
        have hb : simMUB c s i (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) j = ok (.cont (s1, j1)) := by
          simp only [sim.step.miss_unjudged_nested_loop.body, hlt, if_true, lift, bind_ok, hjud, hro,
            Option.isSome_none, Bool.false_eq_true, if_false, hc, e1, uncurry_apply_pair]
          simp [core.result.Result.Insts.CoreOpsTry.branch, hj1]
        rw [sim_mun_step c s i _ j _ hb]
        simp only [simRelM] at r1
        simp only [simM_bind, r1, Except.bind, simM_pure]
        rw [show j.val + 1 = j1.val from hj1v.symm]
        exact ih j1 s1 (by omega) (by omega) hI1 hQ1 hT1

-- FRAGMENT-OF: OsuModel.Sim.Sim.onKilled / updateSpinner (the inline `for j in [0:o.nested.size] do if !(← judged (i, j)) then missForcefully (i, j)`; bridged in on_killed_refines); simCSH via sim_ar_cs
theorem sim.step.miss_unjudged_nested_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (s : sim.state.St) (i : Usize) (e : Nat)
    (hI : SimARInv tn fo P b0 n c s e 0 0) (hi : i.val < c.pb.objects.val.length)
    (hsp : (c.pb.objects.val[i.val]'hi).h.kind = .Spinner) (hT : simTopRes i.val none s) (hIn : simInstOk c s i.val) :
    ∃ res s', sim.step.miss_unjudged_nested c s i = ok (res, s') ∧
      simRelM tn s' res (forIn (m := OsuModel.Sim.SimM) (List.range' 0 (c.pb.objects.val[i.val]'hi).nested.val.length) PUnit.unit
        (fun (j : Nat) _ => do
          let b ← OsuModel.Sim.Sim.judged (i.val, (j : Int))
          if (!b) = true then do
            OsuModel.Sim.Sim.missForcefully (i.val, (j : Int))
            pure (ForInStep.yield PUnit.unit)
          else pure (ForInStep.yield PUnit.unit)) (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ simARFr s s' ∧ simTopRes i.val none s') := by
  obtain ⟨r1, s1, e1, rr1, i1⟩ := sim_mun_loop tn fo E b0 n c hC hCS hlen e s i hi hsp _ (fun _ _ => rfl) hIn
    (c.pb.objects.val[i.val]'hi).nested.val.length 0#usize s (by simp) (by simp) hI (simARFr_refl s) hT
  have h00 : (0#usize).val = 0 := rfl
  simp only [h00] at rr1
  refine ⟨r1, s1, ?_, rr1, i1⟩
  unfold sim.step.miss_unjudged_nested; simp only [vec_index_eq _ _ hi, bind_ok]; exact e1

-- CONDITIONAL: hcs (completed_spins * 360 < 2^63 for object i, needed by spinner_result; to be discharged by the step invariant); htl/hp are context (ev_ctxWF) premises, simCSH via sim_ar_cs
theorem sim.step.on_killed_refines (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (s : sim.state.St) (i : Usize) (e : Nat)
    (hI : SimARInv tn fo P b0 n c s e 0 0) (hIn : simInstOk c s i.val) (hi : i.val < c.pb.objects.val.length)
    (hp : s3aPathOk c i.val) (hLP : simLP s)
    (htl : (c.pb.objects.val[i.val]'hi).h.kind = .Slider → ∃ hti : i.val < c.tail_idx.val.length,
      (c.tail_idx.val[i.val]'hti).val < (c.pb.objects.val[i.val]'hi).nested.val.length)
    (hcs : ∀ h : i.val < s.objs.val.length, (s.objs.val[i.val]'h).completed_spins.val * 360 < 2 ^ 63) :
    ∃ res s', sim.step.on_killed c s i = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.onKilled i.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ simJFr s s' ∧ simLP s') := by
  have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
  unfold sim.step.on_killed OsuModel.Sim.Sim.onKilled
  simp only [simM_bind, s3b_topObj tn fo c _ i.val hi, Except.bind, vec_index_eq _ _ hi, bind_ok]
  have hkS : (topS tn (c.pb.objects.val[i.val]'hi)).h.kind = kindS (c.pb.objects.val[i.val]'hi).h.kind := rfl
  rw [hkS]
  have hr1 : simRefOk c ⟨i, (-1)#i64⟩ := ⟨hi, fun h => by simp at h⟩
  have eabs : (abs (⟨i, (-1)#i64⟩ : sim.step.Ref) : Nat × Int) = (i.val, -1) := by simp [abs]
  cases hk : (c.pb.objects.val[i.val]'hi).h.kind <;> simp only [kindS]
  case Circle =>
    obtain ⟨res, s1, e1, r1, i1⟩ := sim.step.circle_update_result_refines h64 tn fo E b0 n c hC hCS hlen s
      ⟨i, (-1)#i64⟩ false e hI hr1 hIn hp hLP
    rw [eabs] at r1
    cases res with
    | Err er =>
      refine ⟨.Err er, s1, ?_, r1, fun h => by cases h⟩
      simp [e1, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]
    | Ok u =>
      cases u
      exact ⟨.Ok (), s1, by simp [e1, core.result.Result.Insts.CoreOpsTry.branch], r1, i1⟩
  case Slider =>
    obtain ⟨hti, htl'⟩ := htl hk
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    have hsz : (topS tn (c.pb.objects.val[i.val]'hi)).nested.size = (c.pb.objects.val[i.val]'hi).nested.val.length := by
      simp [topS]
    simp only [Std.Legacy.Range.size, Nat.div_one, Nat.sub_zero, Nat.add_sub_cancel, hsz]
    obtain ⟨res, s1, e1, r1, i1⟩ := sim_okl_loop h64 tn fo E b0 n c hC hCS hlen e s i hi hk hp hti htl' _
      (fun _ _ => rfl) _ (fun _ => rfl) hIn (c.pb.objects.val[i.val]'hi).nested.val.length 0#usize s (by simp) (by simp) hI (simJFr_refl s) hLP
    have h00 : (0#usize).val = 0 := rfl
    simp only [h00] at r1
    exact ⟨res, s1, e1, r1, i1⟩
  case Spinner =>
    simp only [vec_index_eq _ _ ho, bind_ok, OsuModel.Sim.Sim.st, simM_bind, simM_get, Except.bind,
      s3a_ostate tn fo c s i.val ho]
    have hrSo : (ostateS (s.objs.val[i.val]'ho)).result = (s.objs.val[i.val]'ho).result.map abs := rfl
    have hT : (simStS tn s).t = s.t := rfl
    have hst : (topS tn (c.pb.objects.val[i.val]'hi)).h.start = (c.pb.objects.val[i.val]'hi).h.start := rfl
    have hen : (topS tn (c.pb.objects.val[i.val]'hi)).h.endTime = (c.pb.objects.val[i.val]'hi).h.end_time := rfl
    rw [hrSo, hT, hst, hen]
    cases hro : (s.objs.val[i.val]'ho).result with
    | some x =>
      exact ⟨.Ok (), s, by simp [core.option.Option.is_none], by simp [simRelM], fun _ => ⟨hI, simJFr_refl s, hLP⟩⟩
    | none =>
    simp only [core.option.Option.is_none, Option.map_none, Option.isNone_none, ite_true, Bool.true_and]
    by_cases h1 : (c.pb.objects.val[i.val]'hi).h.start ≤ s.t
    case neg =>
      exact ⟨.Ok (), s, by simp [float.F64.le, h1], by simp [h1, simRelM], fun _ => ⟨hI, simJFr_refl s, hLP⟩⟩
    by_cases h2 : s.t < (c.pb.objects.val[i.val]'hi).h.end_time
    case pos =>
      exact ⟨.Ok (), s, by simp [float.F64.le, h1, float.F64.lt, h2], by simp [h1, h2, simRelM],
        fun _ => ⟨hI, simJFr_refl s, hLP⟩⟩
    simp only [float.F64.le, float.F64.lt, h1, h2, decide_true, decide_false, Bool.not_false, Bool.and_true,
      ite_true, ite_false, bind_ok, Bool.false_eq_true]
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    have hsz : (topS tn (c.pb.objects.val[i.val]'hi)).nested.size = (c.pb.objects.val[i.val]'hi).nested.val.length := by
      simp [topS]
    simp only [Std.Legacy.Range.size, Nat.div_one, Nat.sub_zero, Nat.add_sub_cancel, hsz]
    obtain ⟨r1, s1, e1, rr1, i1⟩ := sim_mun_loop tn fo E b0 n c hC hCS hlen e s i hi hk _ (fun _ _ => rfl) hIn
      (c.pb.objects.val[i.val]'hi).nested.val.length 0#usize s (by simp) (by simp) hI (simARFr_refl s) (fun _ => hro)
    have h00 : (0#usize).val = 0 := rfl
    simp only [h00] at rr1
    have e1' : sim.step.miss_unjudged_nested c s i = ok (r1, s1) := by
      unfold sim.step.miss_unjudged_nested; simp only [vec_index_eq _ _ hi, bind_ok]; exact e1
    simp only [e1', bind_ok, uncurry_apply_pair]
    cases r1 with
    | Err er =>
      obtain ⟨msg, hmsg⟩ := rr1
      refine ⟨.Err er, s1, ?_, ⟨msg, ?_⟩, fun h => by cases h⟩
      · simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]
      · simp only [simM_bind, hmsg, Except.bind]
    | Ok u =>
      obtain ⟨hI1, hQ1, hT1⟩ := i1 rfl
      simp only [simRelM] at rr1
      simp only [simM_bind, rr1, Except.bind, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have hspS : (topS tn (c.pb.objects.val[i.val]'hi)).spinner = (c.pb.objects.val[i.val]'hi).spinner.map abs := rfl
      rw [hspS]
      cases hsp : (c.pb.objects.val[i.val]'hi).spinner with
      | none =>
        exact ⟨.Ok (), s1, by simp [core.result.Result.Insts.CoreOpsTry.branch], by simp [simRelM], fun _ => ⟨hI1, simJFr_of_ar hQ1, simLP_fr hLP hQ1⟩⟩
      | some sp =>
        have ho1 : i.val < s1.objs.val.length := by rw [hQ1.len]; exact ho
        have hcs1 : (s1.objs.val[i.val]'ho1).completed_spins.val * 360 < 2 ^ 63 := by
          have h2 : (s1.objs.val[i.val]'ho1).completed_spins = (s.objs.val[i.val]'ho).completed_spins :=
            congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hQ1.ow i.val ho ho1)
          rw [h2]; exact hcs ho
        obtain ⟨ty, ety, hty⟩ := sim.step.spinner_result_refines (c.pb.objects.val[i.val]'hi) sp _ hcs1
        obtain ⟨f, hf, hfS⟩ := sim.step.max_fuel_refines tn fo c hlen (simStS tn s1)
        have hres1 : sim.step.res_of s1 ⟨i, (-1)#i64⟩ = ok none := by
          simp [sim.step.res_of, vec_index_eq _ _ ho1, hT1 ho1]
        obtain ⟨r2, s2, e2, rr2, i2⟩ := sim.step.apply_result_frame tn fo E b0 n c hC hCS (simARFr s1) (fun _ => True)
          (fun _ _ _ => trivial) (simARFr_qok c s1 _) s1 f ⟨i, (-1)#i64⟩ ty e hI1 (simARFr_refl s1) trivial hr1 (simInstOk_of_fr hQ1 hIn) hres1
        have hab : (abs ty : OsuModel.Sim.HitResult) = hrS ty := rfl
        rw [eabs, hab, hty] at rr2
        unfold simSpinTy at rr2
        simp only [vec_index_eq _ _ ho1, ety, hf, e2, bind_ok, uncurry_apply_pair, Option.map_some,
          s3a_ostate tn fo c s1 i.val ho1, hfS, simM_bind, Except.bind]
        cases r2 with
        | Err er =>
          obtain ⟨msg, hmsg⟩ := rr2
          refine ⟨.Err er, s2, ?_, ⟨msg, ?_⟩, fun h => by cases h⟩
          · simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]
          · exact hmsg
        | Ok u2 =>
          obtain ⟨hI2, hQ2⟩ := i2 rfl
          cases u2
          exact ⟨.Ok (), s2, by simp [core.result.Result.Insts.CoreOpsTry.branch], rr2, fun _ => ⟨hI2, simJFr_trans (simJFr_of_ar hQ1) (simJFr_of_ar hQ2),
            simLP_fr (simLP_fr hLP hQ1) hQ2⟩⟩
  all_goals exact ⟨.Ok (), s, rfl, rfl, fun _ => ⟨hI, simJFr_refl s, hLP⟩⟩

-- FRAGMENT-OF: OsuModel.Sim.Sim.postProcessHeadJudgement (its inline nested loop = simJSNF; bridged in post_process_head_judgement_refines); simCSH via sim_ar_cs
theorem sim.step.judge_started_nested_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (s : sim.state.St) (i : Usize) (e : Nat)
    (hI : SimARInv tn fo P b0 n c s e 0 0) (hIn : simInstOk c s i.val) (hi : i.val < c.pb.objects.val.length)
    (allIn : Bool) :
    ∃ res s', sim.step.judge_started_nested c s i allIn = ok (res, s') ∧
      simRelM tn s' res (forIn (m := OsuModel.Sim.SimM) (List.range' 0 (c.pb.objects.val[i.val]'hi).nested.val.length)
        PUnit.unit (simJSNF tn c i hi s.t allIn) (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ simARFr s s') := by
  obtain ⟨res2, s1, e2, r2, i2⟩ := sim_jsn_loop tn fo E b0 n c hC hCS hlen e s i hi allIn
    (simJSNF tn c i hi s.t allIn) (fun _ _ => rfl) hIn (c.pb.objects.val[i.val]'hi).nested.val.length 0#usize s
    (by simp) (by simp) hI (simARFr_refl s)
  have h00 : (0#usize).val = 0 := rfl
  simp only [h00] at r2
  refine ⟨res2, s1, ?_, r2, i2⟩
  unfold sim.step.judge_started_nested; simp only [vec_index_eq _ _ hi, bind_ok]; exact e2

end OsuProofs
