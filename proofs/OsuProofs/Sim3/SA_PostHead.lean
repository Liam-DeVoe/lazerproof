/-
sim3a (D37): the first loop of `SliderInputManager.PostProcessHeadJudgement` (Rust `all_nested_in_follow_area` /
`nested_in_follow_area_loop`, read-only): "is every started, unjudged nested object within the follow radius".
Spec side: the loop body of `Sim.postProcessHeadJudgement`'s first `for` is (definitionally) `s3aAllInF`; the sim
core agent uses `sim.step.all_nested_in_follow_area_refines` for `forIn [:n] true F` with `F` ≡ `s3aAllInF` (`rfl`).
-/
import OsuProofs.Sim3.SA_Track
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

/-- the body of the first `for` loop of `Sim.postProcessHeadJudgement` (as elaborated; `allIn` is the loop state) -/
def s3aAllInF (i : Nat) (o : OsuModel.Sim.TopObj) (sd : OsuModel.Sim.SliderData) (t : F64) (m : OsuModel.Sim.Vec2) :
    Nat → Bool → OsuModel.Sim.SimM (ForInStep Bool) := fun j __s => do
  let allIn := __s
  let jd ← OsuModel.Sim.Sim.judged (i, (j : Int))
  if jd = true then pure (ForInStep.yield allIn)
  else do
    let n ← OsuModel.Sim.Sim.nestedOf o j
    if t < n.start then pure (ForInStep.done allIn)
    else
      let radius := OsuModel.Sim.followRadius o.h true
      let p0 := (n.start - o.h.start) / sd.duration
      let progress := OsuModel.Sim.clampK p0 0 1
      let pos ← OsuModel.Sim.Sim.liftExcept (sd.curvePositionAt progress)
      if radius * radius < (pos - m).lengthSquared then pure (ForInStep.done false)
      else pure (ForInStep.yield allIn)

theorem s3a_st_lit (s : sim.state.St) : ({ k := s.k, t := s.t, objs := s.objs, first_lifetime_update := s.first_lifetime_update, next_future := s.next_future, future_order := s.future_order, active := s.active, dict_slots := s.dict_slots, free_list := s.free_list, child_counter := s.child_counter, mouse_valid := s.mouse_valid, mouse := s.mouse, last_replay := s.last_replay, pressed := s.pressed, score := s.score, health := s.health, score_rp := s.score_rp, health_rp := s.health_rp, out := s.out, speed := s.speed, as_target := s.as_target, as_recent := s.as_recent, as_seen := s.as_seen, clock_rate := s.clock_rate, relax_down := s.relax_down, relax_was_left := s.relax_was_left, relax_last := s.relax_last, ap_frame := s.ap_frame, block_last := s.block_last, block_idx := s.block_idx, insts := s.insts, pools := s.pools, br_rot := s.br_rot, theta := s.theta, cursor_pos := s.cursor_pos } : sim.state.St) = s := rfl

@[simp] theorem s3a_step_F64_0 : sim.step.F64_0 = ok (0 : F64) := by simp [sim.step.F64_0]
@[simp] theorem s3a_step_F64_1 : sim.step.F64_1 = ok (1 : F64) := by simp [sim.step.F64_1]

theorem s3a_clampOr01 (x : F64) : simClampOrD x 0 1 = OsuModel.Sim.clampK x 0 1 := by
  unfold simClampOrD OsuModel.Sim.clampK F64.clamp
  rw [if_neg (by decide +kernel)]
  by_cases h1 : x < 0 <;> by_cases h2 : 1 < x <;> simp [h1, h2]

section
variable (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (h3 : i.val < c.pb.objects.val.length)
  (sd : sim.playable.SliderData) (m : sim.basic.Vec2)

/-- the Rust loop body with the destructured state, as a function of `(all_in, j, stop)` -/
def s3aNB := fun x : Bool × Usize × Bool => sim.step.nested_in_follow_area_loop_loop.body s.k s.t s.objs s.first_lifetime_update s.next_future s.future_order s.active s.dict_slots s.free_list s.child_counter s.mouse_valid s.mouse s.last_replay s.pressed s.score s.health s.score_rp s.health_rp s.out s.speed s.as_target s.as_recent s.as_seen s.clock_rate s.relax_down s.relax_was_left s.relax_last s.ap_frame s.block_last s.block_idx s.insts s.pools s.br_rot s.theta s.cursor_pos i (c.pb.objects.val[i.val]'h3) sd m s.t x.1 x.2.1 x.2.2

theorem s3a_nb_stop (b : Bool) (j : Usize) : s3aNB c s i h3 sd m (b, j, true) = ok (.done (.Ok b)) := by
  unfold s3aNB sim.step.nested_in_follow_area_loop_loop.body
  by_cases hj : j < alloc.vec.Vec.len (c.pb.objects.val[i.val]'h3).nested
  · rw [if_pos hj]; rfl
  · rw [if_neg hj]

theorem s3a_nb_loop (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    (hinv : SimInv c s) (hi : i.val < s.objs.val.length)
    (hc : sd.cum_len.val.length < 2 ^ 62) (hp : sd.path.val.length < 2 ^ 62) :
    ∀ k (j : Usize), (c.pb.objects.val[i.val]'h3).nested.val.length - j.val = k →
      j.val ≤ (c.pb.objects.val[i.val]'h3).nested.val.length →
      ∃ r, loop (s3aNB c s i h3 sd m) (true, j, false) = ok r ∧
        s3aR id (simStS tn s) r (forIn (m := OsuModel.Sim.SimM)
          (List.range' j.val ((c.pb.objects.val[i.val]'h3).nested.val.length - j.val)) true
          (s3aAllInF i.val (topS tn (c.pb.objects.val[i.val]'h3)) (abs sd) s.t (abs m)) (simCtxS tn fo c) (simStS tn s)) := by
  intro k
  induction k with
  | zero =>
    intro j hk hj
    have hge : ¬ j < alloc.vec.Vec.len (c.pb.objects.val[i.val]'h3).nested := by rw [vec_lt_len_iff]; omega
    refine ⟨.Ok true, ?_, ?_⟩
    · rw [loop_unfold]
      simp only [s3aNB, sim.step.nested_in_follow_area_loop_loop.body, hge, if_false, bind_ok]
    · rw [hk]; rfl
  | succ k ih =>
    intro j hk hj
    have hjl : j.val < (c.pb.objects.val[i.val]'h3).nested.val.length := by omega
    have hsmall := hinv.nested_small _ (List.getElem_mem h3)
    have hcast : (UScalar.hcast .I64 j).val = (j.val : Int) := sim_usize_to_i64 j (by omega)
    have hnl : (s.objs.val[i.val]'hi).nested.val.length = (c.pb.objects.val[i.val]'h3).nested.val.length :=
      hinv.nested_len _ hi h3
    have href : simSRefOk s ⟨i, UScalar.hcast .I64 j⟩ := ⟨hi, fun _ => by
      show (UScalar.hcast .I64 j).val.toNat < _
      rw [hcast, hnl]; simpa using hjl⟩
    obtain ⟨b, hb, eb⟩ := sim.step.judged_refines tn fo c s ⟨i, UScalar.hcast .I64 j⟩ href
    have eb' : OsuModel.Sim.Sim.judged (i.val, (j.val : Int)) (simCtxS tn fo c) (simStS tn s) = .ok (b, simStS tn s) := by
      rw [← eb]; congr 2; simp [abs, hcast]
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := (c.pb.objects.val[i.val]'h3).nested.property; omega)
    have hlt : j < alloc.vec.Vec.len (c.pb.objects.val[i.val]'h3).nested := by rw [vec_lt_len_iff]; exact hjl
    rw [show (c.pb.objects.val[i.val]'h3).nested.val.length - j.val = (k + 1) by omega, List.range'_succ, List.forIn_cons]
    have hk1 : k = (c.pb.objects.val[i.val]'h3).nested.val.length - j1.val := by omega
    have hjv : j.val + 1 = j1.val := hj1v.symm
    cases b
    · -- unjudged
      have hnest : OsuModel.Sim.Sim.nestedOf (topS tn (c.pb.objects.val[i.val]'h3)) j.val (simCtxS tn fo c) (simStS tn s) =
          .ok (hobjS tn ((c.pb.objects.val[i.val]'h3).nested.val[j.val]'hjl), simStS tn s) := by
        simp [OsuModel.Sim.Sim.nestedOf, OsuModel.Sim.Sim.getA, topS, hjl]
      have hji : j.val < (c.pb.objects.val[i.val]'h3).nested.val.length := hjl
      by_cases hts : s.t < ((c.pb.objects.val[i.val]'h3).nested.val[j.val]'hjl).start
      · have hstep : s3aNB c s i h3 sd m (true, j, false) = ok (.cont (true, j1, true)) := by
          simp only [s3aNB, sim.step.nested_in_follow_area_loop_loop.body, if_pos hlt, Bool.false_eq_true, if_false,
              lift, bind_ok]
          rw [s3a_st_lit s, hb]
          simp [hj1, vec_index_eq _ _ hji, float.F64.lt, hts]
        refine ⟨.Ok true, by rw [loop_unfold, hstep]; simp only [bind_ok]; rw [loop_unfold, s3a_nb_stop]; simp only [bind_ok], ?_⟩
        have hts' : s.t < (hobjS tn ((c.pb.objects.val[i.val]'h3).nested.val[j.val]'hjl)).start := hts
        simp only [simM_bind, s3aAllInF, eb', Except.bind, Bool.false_eq_true, if_false, hnest, hts', if_true, simM_pure]
        rfl
      · have hts' : ¬ s.t < (hobjS tn ((c.pb.objects.val[i.val]'h3).nested.val[j.val]'hjl)).start := hts
        obtain ⟨rad, hrad, erad⟩ := sim.geometry.follow_radius_refines (c.pb.objects.val[i.val]'h3).h true
        have erad' : OsuModel.Sim.followRadius (hobjS tn (c.pb.objects.val[i.val]'h3).h) true = rad := erad
        obtain ⟨x, hx, ex⟩ := sim.geometry.curve_position_at_refines h64 sd
          (OsuModel.Sim.clampK ((((c.pb.objects.val[i.val]'h3).nested.val[j.val]'hjl).start - (c.pb.objects.val[i.val]'h3).h.start)
            / sd.duration) 0 1) hc hp
        have hsdd : (abs sd : OsuModel.Sim.SliderData).duration = sd.duration := rfl
        have hns : (hobjS tn ((c.pb.objects.val[i.val]'h3).nested.val[j.val]'hjl)).start =
            ((c.pb.objects.val[i.val]'h3).nested.val[j.val]'hjl).start := rfl
        have hos : (hobjS tn (c.pb.objects.val[i.val]'h3).h).start = (c.pb.objects.val[i.val]'h3).h.start := rfl
        cases x with
        | Err e =>
          have hE : ∃ msg, OsuModel.Sim.SliderData.curvePositionAt (abs sd) (OsuModel.Sim.clampK
              ((((c.pb.objects.val[i.val]'h3).nested.val[j.val]'hjl).start - (c.pb.objects.val[i.val]'h3).h.start)
                / sd.duration) 0 1) = .error msg := by
            simp only [abs_id] at ex
            revert ex
            cases OsuModel.Sim.SliderData.curvePositionAt (abs sd) (OsuModel.Sim.clampK
              ((((c.pb.objects.val[i.val]'h3).nested.val[j.val]'hjl).start - (c.pb.objects.val[i.val]'h3).h.start)
                / sd.duration) 0 1) <;> simp [s2_rel]
          obtain ⟨msg, hmsg⟩ := hE
          have hstep : s3aNB c s i h3 sd m (true, j, false) = ok (.done (.Err e)) := by
            simp only [s3aNB, sim.step.nested_in_follow_area_loop_loop.body, if_pos hlt, Bool.false_eq_true, if_false,
              lift, bind_ok]
            rw [s3a_st_lit s, hb]
            simp only [Bool.false_eq_true, if_false, vec_index_eq _ _ hji, bind_ok, float.F64.lt, hts, decide_false, hrad,
              float.F64.sub, float.F64.div, s3a_step_F64_0, s3a_step_F64_1, sim.netx.f64_clamp_or_refines, s3a_clampOr01, hx,
              core.result.Result.Insts.CoreOpsTry.branch]
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          refine ⟨.Err e, by rw [loop_unfold, hstep]; simp only [bind_ok], ⟨msg, ?_⟩⟩
          simp only [simM_bind, s3aAllInF, eb', Except.bind, Bool.false_eq_true, if_false, hnest, hts', erad', hsdd, hns,
            hos, s3a_topS_h, simM_ite, hts, if_false, simM_bind, hmsg, OsuModel.Sim.Sim.liftExcept, simM_throw]
        | Ok pos =>
          have hE : OsuModel.Sim.SliderData.curvePositionAt (abs sd) (OsuModel.Sim.clampK
              ((((c.pb.objects.val[i.val]'h3).nested.val[j.val]'hjl).start - (c.pb.objects.val[i.val]'h3).h.start)
                / sd.duration) 0 1) = .ok (abs pos) := by
            simp only [abs_id] at ex
            revert ex
            cases OsuModel.Sim.SliderData.curvePositionAt (abs sd) (OsuModel.Sim.clampK
              ((((c.pb.objects.val[i.val]'h3).nested.val[j.val]'hjl).start - (c.pb.objects.val[i.val]'h3).h.start)
                / sd.duration) 0 1) <;> simp [s2_rel, eq_comm]
          by_cases hq : rad * rad < ((abs pos : OsuModel.Sim.Vec2) - abs m).lengthSquared
          · have hq' : rad * rad < (pos.x - m.x) * (pos.x - m.x) + (pos.y - m.y) * (pos.y - m.y) := hq
            have hstep : s3aNB c s i h3 sd m (true, j, false) = ok (.cont (false, j1, true)) := by
              simp only [s3aNB, sim.step.nested_in_follow_area_loop_loop.body, if_pos hlt, Bool.false_eq_true, if_false,
                lift, bind_ok]
              rw [s3a_st_lit s, hb]
              simp only [Bool.false_eq_true, if_false, vec_index_eq _ _ hji, bind_ok, float.F64.lt, hts, decide_false, hrad,
                float.F64.sub, float.F64.div, s3a_step_F64_0, s3a_step_F64_1, sim.netx.f64_clamp_or_refines, s3a_clampOr01, hx,
                core.result.Result.Insts.CoreOpsTry.branch]
              simp [sim.basic.Vec2.sub, sim.basic.Vec2.length_squared, float.F32.mul, float.F32.sub, float.F32.add,
                float.F32.lt, hq', hj1]
            refine ⟨.Ok false, by rw [loop_unfold, hstep]; simp only [bind_ok]; rw [loop_unfold, s3a_nb_stop]; simp only [bind_ok], ?_⟩
            simp only [simM_bind, s3aAllInF, eb', Except.bind, Bool.false_eq_true, if_false, hnest, hts', erad', hsdd, hns,
              hos, s3a_topS_h, simM_ite, hts, if_false, simM_bind, hE, OsuModel.Sim.Sim.liftExcept, simM_pure, hq, if_true]
            rfl
          · have hq' : ¬ rad * rad < (pos.x - m.x) * (pos.x - m.x) + (pos.y - m.y) * (pos.y - m.y) := hq
            have hstep : s3aNB c s i h3 sd m (true, j, false) = ok (.cont (true, j1, false)) := by
              simp only [s3aNB, sim.step.nested_in_follow_area_loop_loop.body, if_pos hlt, Bool.false_eq_true, if_false,
                lift, bind_ok]
              rw [s3a_st_lit s, hb]
              simp only [Bool.false_eq_true, if_false, vec_index_eq _ _ hji, bind_ok, float.F64.lt, hts, decide_false, hrad,
                float.F64.sub, float.F64.div, s3a_step_F64_0, s3a_step_F64_1, sim.netx.f64_clamp_or_refines, s3a_clampOr01, hx,
                core.result.Result.Insts.CoreOpsTry.branch]
              simp [sim.basic.Vec2.sub, sim.basic.Vec2.length_squared, float.F32.mul, float.F32.sub, float.F32.add,
                float.F32.lt, hq', hj1]
            obtain ⟨r, hr, er⟩ := ih j1 (by omega) (by omega)
            refine ⟨r, by rw [loop_unfold, hstep]; simpa using hr, ?_⟩
            simp only [simM_bind, s3aAllInF, eb', Except.bind, Bool.false_eq_true, if_false, hnest, hts', erad', hsdd, hns,
              hos, s3a_topS_h, simM_ite, hts, if_false, simM_bind, hE, OsuModel.Sim.Sim.liftExcept, simM_pure, hq]
            rw [hk1, hjv]
            exact er
    · -- judged: skip
      have hstep : s3aNB c s i h3 sd m (true, j, false) = ok (.cont (true, j1, false)) := by
        simp only [s3aNB, sim.step.nested_in_follow_area_loop_loop.body, if_pos hlt, Bool.false_eq_true, if_false,
            lift, bind_ok]
        rw [s3a_st_lit s, hb]
        simp [hj1]
      obtain ⟨r, hr, er⟩ := ih j1 (by omega) (by omega)
      refine ⟨r, by rw [loop_unfold, hstep]; simpa using hr, ?_⟩
      simp only [simM_bind, s3aAllInF, eb', Except.bind, if_true, simM_pure]
      rw [hk1, hjv]
      exact er

end

theorem sim.step.all_nested_in_follow_area_refines (h64 : System.Platform.numBits = 64) (tn : Nat → String)
    (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (m : sim.basic.Vec2)
    (hinv : SimInv c s) (hi : i.val < s.objs.val.length) (hp : s3aPathOk c i.val) :
    ∃ r, sim.step.all_nested_in_follow_area c s i m = ok r ∧
      ∀ (h3 : i.val < c.pb.objects.val.length),
      ((c.pb.objects.val[i.val]'h3).slider = none → ∃ e, r = .Err e) ∧
      ∀ sd, (c.pb.objects.val[i.val]'h3).slider = some sd →
        s3aR id (simStS tn s) r (forIn (m := OsuModel.Sim.SimM) [:(topS tn (c.pb.objects.val[i.val]'h3)).nested.size] true
          (s3aAllInF i.val (topS tn (c.pb.objects.val[i.val]'h3)) (abs sd) s.t (abs m)) (simCtxS tn fo c) (simStS tn s)) := by
  have h3 : i.val < c.pb.objects.val.length := by rw [← hinv.objs_len]; exact hi
  unfold sim.step.all_nested_in_follow_area sim.step.slider_data
  simp only [vec_index_eq _ _ h3, bind_ok]
  rcases Option.eq_none_or_eq_some (c.pb.objects.val[i.val]'h3).slider with hs | ⟨sd, hs⟩
  · refine ⟨.Err (.Internal .MissingSliderData), ?_, fun _ => ⟨fun _ => ⟨_, rfl⟩, fun sd h => by simp [hs] at h⟩⟩
    simp [hs, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · obtain ⟨hc, hpp⟩ := hp h3 sd hs
    obtain ⟨r, hr, er⟩ := s3a_nb_loop c s i h3 sd m h64 tn fo hinv hi hc hpp
      (c.pb.objects.val[i.val]'h3).nested.val.length 0#usize (by simp) (by simp)
    refine ⟨r, ?_, fun _ => ⟨fun h => by simp [hs] at h, fun sd' h => ?_⟩⟩
    · simp only [hs, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      unfold sim.step.nested_in_follow_area_loop sim.step.nested_in_follow_area_loop_loop
      exact hr
    · simp only [hs, Option.some.injEq] at h; subst h
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      simp only [Std.Legacy.Range.size, Nat.div_one, Nat.sub_zero, Nat.add_sub_cancel]
      have hsz : (topS tn (c.pb.objects.val[i.val]'h3)).nested.size = (c.pb.objects.val[i.val]'h3).nested.val.length := by
        simp [topS]
      rw [hsz]
      simpa using er

end OsuProofs
