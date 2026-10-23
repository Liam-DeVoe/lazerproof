/-
sim7: the nested-object loops of `updateSlider` (`DrawableSlider` tick/repeat/tail containers and the
OsuModStrictTracking tail miss) against named copies of the spec loop bodies (`s7KindF`, `s7StrictF`; `rfl`-checked
against `Sim.updateSlider` in Sim7/Update.lean `s7_updSlider_eq`).
-/
import OsuProofs.Sim.OnKilled
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

/-- the `for j` loop body of `updateSlider` for one nested kind (`update_slider_nested_kind`) -/
def s7KindF (i : Nat) (o : OsuModel.Sim.TopObj) (kind : OsuModel.Sim.Kind) :
    Nat → PUnit → OsuModel.Sim.SimM (ForInStep PUnit) := fun j __s => do
  let h ← OsuModel.Sim.Sim.nestedOf o j
  let b ← OsuModel.Sim.Sim.judged (i, (j : Int))
  if (h.kind == kind && !b) = true then do
    OsuModel.Sim.Sim.tryJudgeNested i j
    pure (ForInStep.yield PUnit.unit)
  else pure (ForInStep.yield PUnit.unit)

/-- the StrictTracking loop body of `updateSlider` (`strict_tracking_miss`) -/
def s7StrictF (i : Nat) (o : OsuModel.Sim.TopObj) : Nat → PUnit → OsuModel.Sim.SimM (ForInStep PUnit) :=
  fun j __s => do
  let h ← OsuModel.Sim.Sim.nestedOf o j
  if (h.typeName == "StrictTrackingSliderTailCircle") = true then do
    let b ← OsuModel.Sim.Sim.judged (i, (j : Int))
    let jp : Unit → OsuModel.Sim.SimM (ForInStep PUnit) := fun _ => pure (ForInStep.done PUnit.unit)
    if (!b) = true then do
      let r ← OsuModel.Sim.Sim.missForcefully (i, (j : Int))
      jp r
    else jp ()
  else pure (ForInStep.yield PUnit.unit)

/-- the shell's type-name table marks exactly the `strict_tail` nested objects of slider `i` as
`StrictTrackingSliderTailCircle` (context premise: `eval.adapter` sets `strict_tail := type_id = T_STRICT_..`) -/
def s7StrictOk (tn : Nat → String) (c : sim.state.Ctx) (i : Nat) : Prop :=
  ∀ (hi : i < c.pb.objects.val.length) j (hj : j < (c.pb.objects.val[i]'hi).nested.val.length),
    ((c.pb.objects.val[i]'hi).nested.val[j]'hj).strict_tail =
      (tn ((c.pb.objects.val[i]'hi).nested.val[j]'hj).type_id.val == "StrictTrackingSliderTailCircle")

@[reducible] def s7NKL (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (kind : sim.playable.Kind) (nn j : Usize) :=
  sim.step.update_slider_nested_kind_loop c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in c.pb.difficulty
    c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks c.pb.objects c.frames c.steps
    c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames c.block_periods
    c.first_obj s i kind nn j

@[reducible] def s7NKB (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (kind : sim.playable.Kind) (nn j : Usize) :=
  sim.step.update_slider_nested_kind_loop.body c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in c.pb.difficulty
    c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks c.pb.objects c.frames c.steps
    c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames c.block_periods
    c.first_obj i kind nn s j

theorem s7_nk_step (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (kind : sim.playable.Kind) (nn j : Usize) (r)
    (hb : s7NKB c s i kind nn j = ok r) :
    s7NKL c s i kind nn j = (match r with
      | .cont (s1, j1) => s7NKL c s1 i kind nn j1
      | .done y => ok y) := by
  unfold s7NKL sim.step.update_slider_nested_kind_loop
  rw [loop_unfold]; dsimp only
  rw [show sim.step.update_slider_nested_kind_loop.body _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s j
    = ok r from hb]; simp only [bind_ok]
  rcases r with ⟨s1, j1⟩ | y <;> rfl

theorem s7_nk_loop (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (e : Nat) (s0 : sim.state.St)
    (i : Usize) (hi : i.val < c.pb.objects.val.length) (hsl : (c.pb.objects.val[i.val]'hi).h.kind = .Slider)
    (kind : sim.playable.Kind) (hIn0 : simInstOk c s0 i.val) :
    ∀ m (j : Usize) (s : sim.state.St), (c.pb.objects.val[i.val]'hi).nested.val.length - j.val = m →
      j.val ≤ (c.pb.objects.val[i.val]'hi).nested.val.length →
      SimARInv tn fo P b0 n c s e 0 0 → simARFr s0 s →
      ∃ res s', s7NKL c s i kind (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) j = ok (res, s') ∧
        simRelM tn s' res (forIn (m := OsuModel.Sim.SimM) (List.range' j.val m) PUnit.unit
          (s7KindF i.val (topS tn (c.pb.objects.val[i.val]'hi)) (kindS kind)) (simCtxS tn fo c) (simStS tn s)) ∧
        (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ simARFr s0 s') := by
  have hc : (⟨c.env, c.cfg, ⟨c.pb.beatmap_version, c.pb.audio_lead_in, c.pb.difficulty, c.pb.base_difficulty,
      c.pb.slider_multiplier, c.pb.slider_tick_rate, c.pb.breaks, c.pb.objects⟩, c.frames, c.steps, c.head_idx,
      c.tail_idx, c.smax, c.hcfg, c.last_frame_time, c.corner_pow, c.prec_end, c.ap_frames, c.block_periods,
      c.first_obj⟩ : sim.state.Ctx) = c := rfl
  intro m
  induction m with
  | zero =>
    intro j s hm hj hI hQ0
    refine ⟨.Ok (), s, ?_, rfl, fun _ => ⟨hI, hQ0⟩⟩
    have hb : s7NKB c s i kind (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) j = ok (.done (.Ok (), s)) := by
      have : ¬ j < alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested := by rw [vec_lt_len_iff]; omega
      simp [sim.step.update_slider_nested_kind_loop.body, this]
    rw [s7_nk_step c s i kind _ j _ hb]
  | succ m ih =>
    intro j s hm hj hI hQ0
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
    have hoi : c.pb.objects.index_usize i = ok (c.pb.objects.val[i.val]'hi) := vec_index_usize_eq _ _ hi
    have hnj : (c.pb.objects.val[i.val]'hi).nested.index_usize j =
      ok ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl) := vec_index_usize_eq _ _ hjl
    have hkd : (hobjS tn ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl)).kind =
      kindS ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl).kind := rfl
    rw [List.range'_succ, List.forIn_cons]
    simp only [s7KindF, simM_bind, enj, ejud, Except.bind, hkd]
    by_cases hk : (kindS ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl).kind == kindS kind) = true
    · cases hro : ro with
      | some x =>
        simp only [hk, Option.isSome_some, Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false, simM_pure]
        have hb : s7NKB c s i kind (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) j = ok (.cont (s, j1)) := by
          simp [sim.step.update_slider_nested_kind_loop.body, hlt, hoi, hnj, kind_eq_ok, hk, lift, hjud, hro, hj1]
        rw [s7_nk_step c s i kind _ j _ hb]
        rw [show j.val + 1 = j1.val from hj1v.symm]
        exact ih j1 s (by omega) (by omega) hI hQ0
      | none =>
        have hres : sim.step.res_of s ⟨i, UScalar.hcast .I64 j⟩ = ok none := hro ▸ hrof
        simp only [hk, Option.isSome_none, Bool.not_false, Bool.and_true, if_true]
        obtain ⟨res, s1, e1, r1, i1⟩ := sim.step.try_judge_nested_frame tn fo E b0 n c hC hCS hlen s i j e hI (simInstOk_of_fr hQ0 hIn0) hi hjl
          hsl hres
        cases res with
        | Err er =>
          obtain ⟨msg, hmsg⟩ := r1
          have hb : s7NKB c s i kind (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) j = ok (.done (.Err er, s1)) := by
            simp only [sim.step.update_slider_nested_kind_loop.body, hlt, if_true, hoi, hnj, bind_ok, kind_eq_ok, hk,
              lift, hjud, hro, Option.isSome_none, Bool.false_eq_true, if_false, hc, e1, uncurry_apply_pair,
              vec_index_eq _ _ hi, vec_index_usize_eq _ _ hjl]
            simp [hnj, hk, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]
          rw [s7_nk_step c s i kind _ j _ hb]
          refine ⟨.Err er, s1, rfl, ⟨msg, ?_⟩, fun h => by cases h⟩
          simp only [simM_bind, hmsg, Except.bind]
        | Ok u =>
          obtain ⟨hI1, hQ1⟩ := i1 rfl
          have hb : s7NKB c s i kind (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) j = ok (.cont (s1, j1)) := by
            simp only [sim.step.update_slider_nested_kind_loop.body, hlt, if_true, hoi, hnj, bind_ok, kind_eq_ok, hk,
              lift, hjud, hro, Option.isSome_none, Bool.false_eq_true, if_false, hc, e1, uncurry_apply_pair,
              vec_index_eq _ _ hi, vec_index_usize_eq _ _ hjl]
            simp [hnj, hk, core.result.Result.Insts.CoreOpsTry.branch, hj1]
          rw [s7_nk_step c s i kind _ j _ hb]
          simp only [simRelM] at r1
          simp only [simM_bind, r1, Except.bind, simM_pure]
          rw [show j.val + 1 = j1.val from hj1v.symm]
          exact ih j1 s1 (by omega) (by omega) hI1 (simARFr_trans hQ0 hQ1)
    · have hk' : (kindS ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl).kind == kindS kind) = false := by
        simpa using hk
      simp only [hk', Bool.false_and, Bool.false_eq_true, if_false, simM_pure]
      have hb : s7NKB c s i kind (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) j = ok (.cont (s, j1)) := by
        simp [sim.step.update_slider_nested_kind_loop.body, hlt, hoi, hnj, kind_eq_ok, hk', hj1]
      rw [s7_nk_step c s i kind _ j _ hb]
      rw [show j.val + 1 = j1.val from hj1v.symm]
      exact ih j1 s (by omega) (by omega) hI hQ0

@[reducible] def s7STL (c : sim.state.Ctx) (s : sim.state.St) (i nn j : Usize) (d : Bool) :=
  sim.step.strict_tracking_miss_loop c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in c.pb.difficulty
    c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks c.pb.objects c.frames c.steps
    c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames c.block_periods
    c.first_obj s i nn j d

@[reducible] def s7STB (c : sim.state.Ctx) (s : sim.state.St) (i nn j : Usize) (d : Bool) :=
  sim.step.strict_tracking_miss_loop.body c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in c.pb.difficulty
    c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks c.pb.objects c.frames c.steps
    c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames c.block_periods
    c.first_obj i nn s j d

theorem s7_st_step (c : sim.state.Ctx) (s : sim.state.St) (i nn j : Usize) (d : Bool) (r)
    (hb : s7STB c s i nn j d = ok r) :
    s7STL c s i nn j d = (match r with
      | .cont (s1, j1, d1) => s7STL c s1 i nn j1 d1
      | .done y => ok y) := by
  unfold s7STL sim.step.strict_tracking_miss_loop
  rw [loop_unfold]; dsimp only
  rw [show sim.step.strict_tracking_miss_loop.body _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s j d
    = ok r from hb]; simp only [bind_ok]
  rcases r with ⟨s1, j1, d1⟩ | y <;> rfl

theorem s7_st_done (c : sim.state.Ctx) (s : sim.state.St) (i nn j : Usize) :
    s7STL c s i nn j true = ok (.Ok (), s) := by
  have hb : s7STB c s i nn j true = ok (.done (.Ok (), s)) := by
    by_cases h : j < nn <;> simp [sim.step.strict_tracking_miss_loop.body, h]
  rw [s7_st_step c s i nn j true _ hb]

theorem s7_st_loop (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (e : Nat) (s0 : sim.state.St)
    (i : Usize) (hi : i.val < c.pb.objects.val.length) (hST : s7StrictOk tn c i.val)
    (hIn0 : simInstOk c s0 i.val) :
    ∀ m (j : Usize) (s : sim.state.St), (c.pb.objects.val[i.val]'hi).nested.val.length - j.val = m →
      j.val ≤ (c.pb.objects.val[i.val]'hi).nested.val.length →
      SimARInv tn fo P b0 n c s e 0 0 → simARFr s0 s →
      ∃ res s', s7STL c s i (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) j false = ok (res, s') ∧
        simRelM tn s' res (forIn (m := OsuModel.Sim.SimM) (List.range' j.val m) PUnit.unit
          (s7StrictF i.val (topS tn (c.pb.objects.val[i.val]'hi))) (simCtxS tn fo c) (simStS tn s)) ∧
        (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ simARFr s0 s') := by
  have hc : (⟨c.env, c.cfg, ⟨c.pb.beatmap_version, c.pb.audio_lead_in, c.pb.difficulty, c.pb.base_difficulty,
      c.pb.slider_multiplier, c.pb.slider_tick_rate, c.pb.breaks, c.pb.objects⟩, c.frames, c.steps, c.head_idx,
      c.tail_idx, c.smax, c.hcfg, c.last_frame_time, c.corner_pow, c.prec_end, c.ap_frames, c.block_periods,
      c.first_obj⟩ : sim.state.Ctx) = c := rfl
  intro m
  induction m with
  | zero =>
    intro j s hm hj hI hQ0
    refine ⟨.Ok (), s, ?_, rfl, fun _ => ⟨hI, hQ0⟩⟩
    have hb : s7STB c s i (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) j false = ok (.done (.Ok (), s)) := by
      have : ¬ j < alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested := by rw [vec_lt_len_iff]; omega
      simp [sim.step.strict_tracking_miss_loop.body, this]
    rw [s7_st_step c s i _ j false _ hb]
  | succ m ih =>
    intro j s hm hj hI hQ0
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
    have hoi : c.pb.objects.index_usize i = ok (c.pb.objects.val[i.val]'hi) := vec_index_usize_eq _ _ hi
    have hnj : (c.pb.objects.val[i.val]'hi).nested.index_usize j =
      ok ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl) := vec_index_usize_eq _ _ hjl
    have htn : (hobjS tn ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl)).typeName =
      tn ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl).type_id.val := rfl
    have hst := hST hi j.val hjl
    rw [List.range'_succ, List.forIn_cons]
    simp only [s7StrictF, simM_bind, enj, Except.bind, htn]
    cases hsd : ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl).strict_tail
    · rw [hsd] at hst
      have hn : (tn ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl).type_id.val ==
          "StrictTrackingSliderTailCircle") = false := hst.symm
      simp only [hn, Bool.false_eq_true, if_false, simM_pure]
      have hb : s7STB c s i (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) j false = ok (.cont (s, j1, false)) := by
        simp [sim.step.strict_tracking_miss_loop.body, hlt, hoi, hnj, hsd, hj1]
      rw [s7_st_step c s i _ j false _ hb]
      rw [show j.val + 1 = j1.val from hj1v.symm]
      exact ih j1 s (by omega) (by omega) hI hQ0
    · rw [hsd] at hst
      have hn : (tn ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl).type_id.val ==
          "StrictTrackingSliderTailCircle") = true := hst.symm
      simp only [hn, if_true, simM_bind, ejud, Except.bind]
      cases hro : ro with
      | some x =>
        simp only [Option.isSome_some, Bool.not_true, Bool.false_eq_true, if_false, simM_pure]
        have hb : s7STB c s i (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) j false = ok (.cont (s, j1, true)) := by
          simp [sim.step.strict_tracking_miss_loop.body, hlt, hoi, hnj, hsd, lift, hjud, hro, hj1]
        rw [s7_st_step c s i _ j false _ hb]; dsimp only; rw [s7_st_done]
        exact ⟨_, _, rfl, rfl, fun _ => ⟨hI, hQ0⟩⟩
      | none =>
        have hres : sim.step.res_of s ⟨i, UScalar.hcast .I64 j⟩ = ok none := hro ▸ hrof
        simp only [Option.isSome_none, Bool.not_false, if_true]
        obtain ⟨res, s1, e1, r1, i1⟩ := sim.step.miss_forcefully_frame tn fo E b0 n c hC hCS hlen (simARFr s0)
          (fun _ => True) (fun _ _ _ => trivial) (simARFr_qok c s0 _) s _ e hI hQ0 trivial hrj (simInstOk_of_fr hQ0 hIn0) hres
        rw [eabs] at r1
        cases res with
        | Err er =>
          obtain ⟨msg, hmsg⟩ := r1
          have hb : s7STB c s i (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) j false = ok (.done (.Err er, s1)) := by
            simp only [sim.step.strict_tracking_miss_loop.body, hlt, if_true, hoi, hnj, bind_ok, hsd, lift, hjud, hro,
              Option.isSome_none, Bool.false_eq_true, if_false, hc, e1, uncurry_apply_pair,
              vec_index_eq _ _ hi, vec_index_usize_eq _ _ hjl]
            simp [hnj, hsd, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]
          rw [s7_st_step c s i _ j false _ hb]
          refine ⟨.Err er, s1, rfl, ⟨msg, ?_⟩, fun h => by cases h⟩
          simp only [simM_bind, hmsg, Except.bind]
        | Ok u =>
          obtain ⟨hI1, hQ1⟩ := i1 rfl
          have hb : s7STB c s i (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) j false = ok (.cont (s1, j1, true)) := by
            simp only [sim.step.strict_tracking_miss_loop.body, hlt, if_true, hoi, hnj, bind_ok, hsd, lift, hjud, hro,
              Option.isSome_none, Bool.false_eq_true, if_false, hc, e1, uncurry_apply_pair,
              vec_index_eq _ _ hi, vec_index_usize_eq _ _ hjl]
            simp [hnj, hsd, core.result.Result.Insts.CoreOpsTry.branch, hj1]
          rw [s7_st_step c s i _ j false _ hb]; dsimp only; rw [s7_st_done]
          simp only [simRelM] at r1
          simp only [simM_bind, r1, Except.bind, simM_pure]
          exact ⟨_, _, rfl, rfl, fun _ => ⟨hI1, hQ1⟩⟩

-- FRAGMENT-OF: OsuModel.Sim.Sim.updateSlider (the tick/repeat/tail `for j` loop = `s7KindF`, checked by `rfl` in s7_updSlider_eq; bridged in sim.step.update_slider_refines); simCSH via sim_ar_cs
theorem sim.step.update_slider_nested_kind_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (s : sim.state.St) (i : Usize) (kind : sim.playable.Kind) (e : Nat)
    (hI : SimARInv tn fo P b0 n c s e 0 0) (hIn : simInstOk c s i.val) (hi : i.val < c.pb.objects.val.length)
    (hsl : (c.pb.objects.val[i.val]'hi).h.kind = .Slider) :
    ∃ res s', sim.step.update_slider_nested_kind c s i kind = ok (res, s') ∧
      simRelM tn s' res (forIn (m := OsuModel.Sim.SimM) (List.range' 0 (c.pb.objects.val[i.val]'hi).nested.val.length)
        PUnit.unit (s7KindF i.val (topS tn (c.pb.objects.val[i.val]'hi)) (kindS kind)) (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ simARFr s s') := by
  obtain ⟨r1, s1, e1, rr1, i1⟩ := s7_nk_loop tn fo E b0 n c hC hCS hlen e s i hi hsl kind hIn
    (c.pb.objects.val[i.val]'hi).nested.val.length 0#usize s (by simp) (by simp) hI (simARFr_refl s)
  have h00 : (0#usize).val = 0 := rfl
  simp only [h00] at rr1
  refine ⟨r1, s1, ?_, rr1, i1⟩
  unfold sim.step.update_slider_nested_kind; simp only [vec_index_eq _ _ hi, bind_ok]; exact e1

-- FRAGMENT-OF: OsuModel.Sim.Sim.updateSlider (the StrictTracking `for j` loop = `s7StrictF`, checked by `rfl` in s7_updSlider_eq; bridged in sim.step.update_slider_refines); hST is a context premise (type-name table vs `strict_tail`), simCSH via sim_ar_cs
theorem sim.step.strict_tracking_miss_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (s : sim.state.St) (i : Usize) (e : Nat)
    (hI : SimARInv tn fo P b0 n c s e 0 0) (hIn : simInstOk c s i.val) (hi : i.val < c.pb.objects.val.length)
    (hST : s7StrictOk tn c i.val) :
    ∃ res s', sim.step.strict_tracking_miss c s i = ok (res, s') ∧
      simRelM tn s' res (forIn (m := OsuModel.Sim.SimM) (List.range' 0 (c.pb.objects.val[i.val]'hi).nested.val.length)
        PUnit.unit (s7StrictF i.val (topS tn (c.pb.objects.val[i.val]'hi))) (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ simARFr s s') := by
  obtain ⟨r1, s1, e1, rr1, i1⟩ := s7_st_loop tn fo E b0 n c hC hCS hlen e s i hi hST hIn
    (c.pb.objects.val[i.val]'hi).nested.val.length 0#usize s (by simp) (by simp) hI (simARFr_refl s)
  have h00 : (0#usize).val = 0 := rfl
  simp only [h00] at rr1
  refine ⟨r1, s1, ?_, rr1, i1⟩
  unfold sim.step.strict_tracking_miss; simp only [vec_index_eq _ _ hi, bind_ok]; exact e1

end OsuProofs
