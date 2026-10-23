/-
`sim::step` context initialisation helpers (Rust) refine `OsuModel.Sim` Step (`mkCtx` pieces):
`input_block_periods` (`inputBlockPeriods`: `block_vt`, `first_object_after`, `block_period`, `break_block_period`,
the push loop with `?` and the insertion sort = `stableSortBy`), with `simRel` for `Result<_, SimErr>`.
-/
import OsuProofs.Sim.HealthCfg
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl OsuModel.Net

def simVT (h : OsuModel.Sim.HObj) : F64 := h.start - (match h.hitWindows with | some hw => hw.meh | none => 0)
def simPer (a b : F64) : Except String (F64 × F64) :=
  if a < b then pure (a, b) else throw "InputBlockingMod: invalid period (start >= end), lazer throws"
def simBBP (objs : _root_.Array OsuModel.Sim.TopObj) (b : F64 × F64) : Except String (F64 × F64) :=
  match objs.find? (fun o => b.2 ≤ o.h.start) with
  | some o => simPer b.1 (simVT o.h - 1)
  | none => throw "InputBlockingMod: break without a following object, lazer throws"

theorem sim_foa_loop (pb : sim.playable.Playable) (be : F64) :
    ∀ n (i : Usize), pb.objects.val.length - i.val = n → i.val ≤ pb.objects.val.length →
      ∃ o, sim.step.first_object_after_loop pb be i none = ok o ∧ (∀ j, o = some j → j.val < pb.objects.val.length) ∧
        o.map (fun j => pb.objects.val[j.val]!) = (pb.objects.val.drop i.val).find? (fun o => decide (be ≤ o.h.start)) := by
  intro n
  induction n with
  | zero =>
    intro i hn hi
    have hdn : pb.objects.val.drop i.val = [] := List.drop_of_length_le (by omega)
    refine ⟨none, ?_, by simp, by simp [hdn]⟩
    unfold sim.step.first_object_after_loop; rw [loop_unfold]
    have : ¬ (i < alloc.vec.Vec.len pb.objects) := by rw [vec_lt_len_iff]; omega
    simp [sim.step.first_object_after_loop.body, this]
  | succ n ih =>
    intro i hn hi
    have hlt : i.val < pb.objects.val.length := by omega
    have hlt' : i < alloc.vec.Vec.len pb.objects := by rw [vec_lt_len_iff]; exact hlt
    obtain ⟨i1, hi1, ei1⟩ := usize_add_one i (by have := pb.objects.property; omega)
    rw [List.drop_eq_getElem_cons hlt, List.find?_cons]
    by_cases hc : be ≤ (pb.objects.val[i.val]'hlt).h.start
    · refine ⟨some i, ?_, by intro j hj; cases hj; exact hlt, by simp [hc, List.getElem?_eq_getElem hlt]⟩
      unfold sim.step.first_object_after_loop; rw [loop_unfold]; dsimp only
      rw [show sim.step.first_object_after_loop.body pb be i none = ok (.cont (i1, some i)) by
        simp [sim.step.first_object_after_loop.body, hlt', core.option.Option.is_none, vec_index_usize_ok _ _ hlt,
          float.F64.le, hc, hi1]]
      simp only [bind_ok]
      rw [loop_unfold]
      by_cases h2 : i1 < alloc.vec.Vec.len pb.objects <;>
        simp [sim.step.first_object_after_loop.body, h2, core.option.Option.is_none]
    · obtain ⟨o, ho, hob, eo⟩ := ih i1 (by omega) (by omega)
      refine ⟨o, ?_, hob, by rw [eo, ei1]; simp [hc]⟩
      unfold sim.step.first_object_after_loop; rw [loop_unfold]; dsimp only
      rw [show sim.step.first_object_after_loop.body pb be i none = ok (.cont (i1, none)) by
        simp [sim.step.first_object_after_loop.body, hlt', core.option.Option.is_none, vec_index_usize_ok _ _ hlt,
          float.F64.le, hc, hi1]]
      simp only [bind_ok]
      unfold sim.step.first_object_after_loop at ho; exact ho

-- NOTE: duplicate of sim3b's Sim3/SB_Upd theorem (same fn); kept under a distinct name for InitCtx.
theorem sim.step.first_object_after_refines_ic (pb : sim.playable.Playable) (be : F64) :
    ∃ o, sim.step.first_object_after pb be = ok o ∧ (∀ j, o = some j → j.val < pb.objects.val.length) ∧
      o.map (fun j => pb.objects.val[j.val]!) = pb.objects.val.find? (fun o => decide (be ≤ o.h.start)) := by
  obtain ⟨o, ho, hb, eo⟩ := sim_foa_loop pb be _ 0#usize rfl (by simp)
  exact ⟨o, ho, hb, by simpa using eo⟩

-- NOTE: duplicate of sim3b's Sim3/SB_Upd theorem (same fn); kept under a distinct name for InitCtx.
theorem sim.step.block_vt_refines_ic (tn) (h : sim.playable.HObj) :
    sim.step.block_vt h = ok (simVT (hobjS tn h)) := by
  cases hw : h.hit_windows <;> simp [sim.step.block_vt, hw, simVT, hobjS, abs, sim_step_F64_0]

-- NOTE: duplicate of sim3b's Sim3/SB_Upd theorem (same fn); kept under a distinct name for InitCtx.
theorem sim.step.block_period_refines_ic (a b : F64) :
    ∃ r, sim.step.block_period a b = ok r ∧ simRel simPP r (simPer a b) := by
  by_cases h : a < b
  · exact ⟨.Ok ⟨a, b⟩, by simp [sim.step.block_period, float.F64.lt, h], by simp [simRel, simPer, h, simPP]⟩
  · exact ⟨.Err .PeriodInvalid, by simp [sim.step.block_period, float.F64.lt, h],
      ⟨_, by simp [simPer, h]; rfl⟩⟩

-- NOTE: duplicate of sim3b's Sim3/SB_Upd theorem (same fn); kept under a distinct name for InitCtx.
theorem sim.step.break_block_period_refines_ic (tn) (pb : sim.playable.Playable) (b : Usize)
    (hb : b.val < pb.breaks.val.length) :
    ∃ r, sim.step.break_block_period pb b = ok r ∧
      simRel simPP r (simBBP (playableS tn pb).objects (simPP (pb.breaks.val[b.val]'hb))) := by
  obtain ⟨o, ho, hob, eo⟩ := sim.step.first_object_after_refines_ic pb (pb.breaks.val[b.val]'hb).«end»
  have hf : (playableS tn pb).objects.find? (fun o => decide ((simPP (pb.breaks.val[b.val]'hb)).2 ≤ o.h.start)) =
      o.map (fun j => topS tn (pb.objects.val[j.val]!)) := by
    simp only [playableS, List.find?_toArray, List.find?_map, Function.comp_def]
    rw [show List.find? (fun x => decide ((simPP (pb.breaks.val[b.val]'hb)).2 ≤ (topS tn x).h.start)) pb.objects.val =
      List.find? (fun o => decide ((pb.breaks.val[b.val]'hb).«end» ≤ o.h.start)) pb.objects.val from rfl, ← eo,
      Option.map_map]
    rfl
  unfold simBBP
  rw [hf]
  cases o with
  | none =>
    refine ⟨.Err .PeriodNoFollowing, by simp [sim.step.break_block_period, vec_index_usize_ok _ _ hb, ho], ⟨_, rfl⟩⟩
  | some j =>
    have hj := hob j rfl
    obtain ⟨r, hr, er⟩ := sim.step.block_period_refines_ic (pb.breaks.val[b.val]'hb).start
      (simVT (hobjS tn (pb.objects.val[j.val]'hj).h) - 1)
    refine ⟨r, ?_, ?_⟩
    · simp [sim.step.break_block_period, vec_index_usize_ok _ _ hb, ho, vec_index_usize_ok _ _ hj,
        sim.step.block_vt_refines_ic tn, sim_step_F64_1, float.F64.sub, hr]
    · simp only [Option.map_some, getElem!_pos pb.objects.val j.val hj, topS]; exact er

theorem sim_ibp_sort_loop (ps : alloc.vec.Vec sim.playable.Period) :
    ∀ n (out : alloc.vec.Vec sim.playable.Period) (k : Usize), ps.val.length - k.val = n →
      k.val ≤ ps.val.length → out.val.length = k.val →
      ∃ w, sim.step.input_block_periods_loop0_loop0 ps out k = ok w ∧
        w.val.map simPP = ((ps.val.drop k.val).map simPP).foldl simNDStep (out.val.map simPP) := by
  intro n
  induction n with
  | zero =>
    intro out k hn hk ho
    have hdn : ps.val.drop k.val = [] := List.drop_of_length_le (by omega)
    refine ⟨out, ?_, by simp [hdn]⟩
    unfold sim.step.input_block_periods_loop0_loop0; rw [loop_unfold]
    have : ¬ (k < alloc.vec.Vec.len ps) := by rw [vec_lt_len_iff]; omega
    simp [sim.step.input_block_periods_loop0_loop0.body, this]
  | succ n ih =>
    intro out k hn hk ho
    have hlt : k.val < ps.val.length := by omega
    have hlt' : k < alloc.vec.Vec.len ps := by rw [vec_lt_len_iff]; exact hlt
    have hmax := ps.property
    obtain ⟨k1, hk1, ek1⟩ := usize_add_one k (by omega)
    obtain ⟨w1, hw1, ew1⟩ := sim.scoring.insert_period_sorted_refines out (ps.val[k.val]'hlt) (by omega)
    have hw1l : w1.val.length = k1.val := by
      have := congrArg List.length ew1; simp only [List.length_map, List.length_insertIdx] at this
      have hle := sim_simInsPos_le simPLt (out.val.map simPP) (simPP (ps.val[k.val]'hlt)) out.val.length
      rw [ek1, ← ho]; split at this <;> omega
    obtain ⟨w, hw, ew⟩ := ih w1 k1 (by omega) (by omega) hw1l
    refine ⟨w, ?_, ?_⟩
    · unfold sim.step.input_block_periods_loop0_loop0; rw [loop_unfold]; dsimp only
      rw [show sim.step.input_block_periods_loop0_loop0.body ps out k = ok (.cont (w1, k1)) by
        simp [sim.step.input_block_periods_loop0_loop0.body, hlt', vec_index_usize_ok _ _ hlt, hw1, hk1]]
      simp only [bind_ok]
      unfold sim.step.input_block_periods_loop0_loop0 at hw; exact hw
    · rw [ew, ew1, ek1, List.drop_eq_getElem_cons hlt, List.map_cons, List.foldl_cons]; rfl

theorem sim_simSortL_foldl (L : List (F64 × F64)) : simSortL simPLt L = L.foldl simNDStep [] := rfl

theorem sim_ibp_loop (tn) (pb : sim.playable.Playable) (hcap : pb.breaks.val.length < Usize.max) :
    ∀ n (ps : alloc.vec.Vec sim.playable.Period) (b : Usize), pb.breaks.val.length - b.val = n →
      b.val ≤ pb.breaks.val.length → ps.val.length = b.val + 1 →
      ∃ r, sim.step.input_block_periods_loop0 pb.beatmap_version pb.audio_lead_in pb.difficulty pb.base_difficulty
          pb.slider_multiplier pb.slider_tick_rate pb.breaks pb.objects ps b = ok r ∧
        simRel (fun w => w.val.map simPP) r
          ((((pb.breaks.val.drop b.val).map simPP).mapM (simBBP (playableS tn pb).objects)).map
            (fun ps' => simSortL simPLt (ps.val.map simPP ++ ps'))) := by
  intro n
  induction n with
  | zero =>
    intro ps b hn hb hps
    have hdn : pb.breaks.val.drop b.val = [] := List.drop_of_length_le (by omega)
    obtain ⟨w, hw, ew⟩ := sim_ibp_sort_loop ps _ (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
    refine ⟨.Ok w, ?_, ?_⟩
    · unfold sim.step.input_block_periods_loop0; rw [loop_unfold]
      have : ¬ (b < alloc.vec.Vec.len pb.breaks) := by rw [vec_lt_len_iff]; omega
      simp [sim.step.input_block_periods_loop0.body, this, hw]
    · simp only [simRel, hdn, List.map_nil, List.mapM_nil, List.append_nil, ew]
      simp [sim_simSortL_foldl, alloc.vec.Vec.new, Except.map]
  | succ n ih =>
    intro ps b hn hb hps
    have hlt : b.val < pb.breaks.val.length := by omega
    have hlt' : b < alloc.vec.Vec.len pb.breaks := by rw [vec_lt_len_iff]; exact hlt
    obtain ⟨b1, hb1, eb1⟩ := usize_add_one b (by omega)
    obtain ⟨r, hr, er⟩ := sim.step.break_block_period_refines_ic tn pb b hlt
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, List.mapM_cons]
    cases r with
    | Err e =>
      obtain ⟨m, hm⟩ := er
      refine ⟨.Err e, ?_, ⟨m, by simp [hm]; rfl⟩⟩
      unfold sim.step.input_block_periods_loop0; rw [loop_unfold]
      simp [sim.step.input_block_periods_loop0.body, hlt', hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
        core.convert.From.from]
    | Ok p =>
      simp only [simRel] at er
      have hpl : ps.val.length < Usize.max := by omega
      obtain ⟨R, hR, eR⟩ := ih (vpush ps p hpl) b1 (by omega) (by omega) (by simp; omega)
      refine ⟨R, ?_, ?_⟩
      · unfold sim.step.input_block_periods_loop0; rw [loop_unfold]; dsimp only
        rw [show sim.step.input_block_periods_loop0.body pb.beatmap_version pb.audio_lead_in pb.difficulty
            pb.base_difficulty pb.slider_multiplier pb.slider_tick_rate pb.breaks pb.objects ps b =
            ok (.cont (vpush ps p hpl, b1)) by
          simp [sim.step.input_block_periods_loop0.body, hlt', hr, core.result.Result.Insts.CoreOpsTry.branch,
            vec_push_ok _ _ hpl, hb1]]
        simp only [bind_ok]
        unfold sim.step.input_block_periods_loop0 at hR; exact hR
      · rw [er, eb1] at *
        have key : ∀ (E : Except String (List (F64 × F64))),
            (Except.map (fun ps' => simSortL simPLt (ps.val.map simPP ++ ps'))
              (do let x ← (Except.ok (simPP p) : Except String _); let y ← E; pure (x :: y))) =
            Except.map (fun ps' => simSortL simPLt ((vpush ps p hpl).val.map simPP ++ ps')) E := by
          intro E; cases E <;> simp [Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure]
        rw [key]; simpa only [Functor.map] using eR

theorem sim_exc_forIn_push {α β : Type} (l : List α) (acc : _root_.Array β)
    (F : α → _root_.Array β → Except String (ForInStep (_root_.Array β))) (g : α → Except String β)
    (hF : ∀ x s, F x s = (do let p ← g x; pure (ForInStep.yield (s.push p)))) :
    forIn l acc F = (l.mapM g).map (fun ps => acc ++ ps.toArray) := by
  induction l generalizing acc with
  | nil => simp [Except.map]
  | cons x t ih =>
    rw [List.forIn_cons, hF, List.mapM_cons]
    cases hg : g x with
    | error e => simp [Bind.bind, Except.bind, Except.map]
    | ok p =>
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
      rw [ih]
      cases t.mapM g <;> simp [Except.map]

theorem simS_inputBlockPeriods (pb : OsuModel.Sim.Playable) (o0 : OsuModel.Sim.TopObj) (h : pb.objects[0]? = some o0) :
    OsuModel.Sim.inputBlockPeriods pb = (do
      let p0 ← simPer (F64.ofInt (-2147483648)) (simVT o0.h - 1)
      let ps ← pb.breaks.toList.mapM (simBBP pb.objects)
      pure ((simSortL simPLt (p0 :: ps)).toArray)) := by
  have hF : ∀ (x : F64 × F64) (s : _root_.Array (F64 × F64)),
      (match Array.find? (fun o => decide (x.2 ≤ o.h.start)) pb.objects with
        | some o => do
          let __do_lift ← if x.1 < (o.h.start - match o.h.hitWindows with | some hw => hw.meh | none => 0) - 1
            then pure (x.1, (o.h.start - match o.h.hitWindows with | some hw => hw.meh | none => 0) - 1)
            else throw "InputBlockingMod: invalid period (start >= end), lazer throws"
          pure (ForInStep.yield (s.push __do_lift))
        | none => throw "InputBlockingMod: break without a following object, lazer throws" : Except String _) =
      (do let p ← simBBP pb.objects x; pure (ForInStep.yield (s.push p))) := by
    intro x s
    unfold simBBP simPer simVT
    cases pb.objects.find? (fun o => decide (x.2 ≤ o.h.start)) with
    | none => rfl
    | some o =>
      by_cases hc : x.1 < (o.h.start - match o.h.hitWindows with | some hw => hw.meh | none => 0) - 1 <;>
        simp [hc] <;> rfl
  unfold OsuModel.Sim.inputBlockPeriods
  simp only [h]
  obtain ⟨m, hm⟩ : ∃ m, (match o0.h.hitWindows with | some hw => hw.meh | none => (0 : F64)) = m ∧ True :=
    ⟨_, rfl, trivial⟩
  have hv : simVT o0.h = o0.h.start - m := by rw [← hm.1]; rfl
  rw [hv]
  cases hw : o0.h.hitWindows <;> simp only [hw] at hm ⊢ <;> rw [← hm.1] <;> simp only [simPer] <;>
  · split
    · rename_i hc
      simp only [hc, if_true, pure_bind]
      rw [← Array.forIn_toList, sim_exc_forIn_push _ _ _ (simBBP pb.objects) ?hF2]
      case hF2 =>
        intro x s
        unfold simBBP simPer simVT
        cases hfo : Array.find? (fun o => decide (x.2 ≤ o.h.start)) pb.objects with
        | none => simp [hfo]
        | some o =>
          simp only [hfo]
          cases hw2 : o.h.hitWindows <;> simp only [hw2] <;> split <;> simp_all
      simp only [Bind.bind, Except.bind]
      cases pb.breaks.toList.mapM (simBBP pb.objects) with
      | error e => rfl
      | ok ps => simp [Except.map, sim_stableSortBy_eq]; rfl
    · rename_i hc
      first | rfl | (simp only [hc, ite_false]; rfl) | simp [hc] | (simp [hc]; rfl)

theorem sim.step.input_block_periods_refines (tn) (pb : sim.playable.Playable)
    (hcap : pb.breaks.val.length < Usize.max) :
    ∃ r, sim.step.input_block_periods pb = ok r ∧
      simRel (fun w => (w.val.map simPP).toArray) r (OsuModel.Sim.inputBlockPeriods (playableS tn pb)) := by
  by_cases h0 : pb.objects.val.length = 0
  · have h0' : alloc.vec.Vec.len pb.objects = 0#usize := by scalar_tac
    refine ⟨.Ok (alloc.vec.Vec.new _), by simp [sim.step.input_block_periods, h0'], ?_⟩
    have : (playableS tn pb).objects[0]? = none := by simp [playableS, h0]
    unfold OsuModel.Sim.inputBlockPeriods
    simp [this, simRel, alloc.vec.Vec.new]
  · have h0' : ¬ alloc.vec.Vec.len pb.objects = 0#usize := fun e => h0 (by simpa using congrArg UScalar.val e)
    have hl0 : 0 < pb.objects.val.length := by omega
    have hS0 : (playableS tn pb).objects[0]? = some (topS tn (pb.objects.val[0]'hl0)) := by
      simp [playableS, List.getElem?_eq_getElem hl0]
    rw [simS_inputBlockPeriods _ _ hS0]
    obtain ⟨r0, hr0, er0⟩ := sim.step.block_period_refines_ic (F64.ofInt (-2147483648))
      (simVT (hobjS tn (pb.objects.val[0]'hl0).h) - 1)
    have hfi : float.F64.from_i64 (-2147483648)#i64 = ok (F64.ofInt (-2147483648)) := by
      simp [float.F64.from_i64]
    have h0l : (0#usize : Usize).val < pb.objects.val.length := by simpa using hl0
    have RS : ∀ (X : core.result.Result sim.playable.Period sim.err.SimErr →
        Result (core.result.Result (alloc.vec.Vec sim.playable.Period) sim.err.SimErr)), (do
        let f ← float.F64.from_i64 (-2147483648)#i64
        let «to» ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.playable.TopObj) pb.objects 0#usize
        let f1 ← sim.step.block_vt «to».h
        let f2 ← sim.step.F64_1
        let f3 ← float.F64.sub f1 f2
        let r ← sim.step.block_period f f3
        X r) = X r0 := by
      intro X
      simp only [hfi, bind_ok, vec_index_eq _ _ h0l, sim.step.block_vt_refines_ic tn, sim_step_F64_1, float.F64.sub]
      simp only [show ((0#usize : Usize).val) = 0 from rfl]
      rw [hr0]; simp only [bind_ok]
    cases r0 with
    | Err e =>
      obtain ⟨m, hm⟩ := er0
      refine ⟨.Err e, ?_, ⟨m, ?_⟩⟩
      · unfold sim.step.input_block_periods; simp only [h0', if_false]; rw [RS]
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
          core.convert.From.from]
      simp only [topS] at hm ⊢
      rw [hm]; rfl
    | Ok p0 =>
      simp only [simRel] at er0
      have hpl : (alloc.vec.Vec.new sim.playable.Period).val.length < Usize.max := by simp; scalar_tac
      obtain ⟨R, hR, eR⟩ := sim_ibp_loop tn pb hcap _ (vpush (alloc.vec.Vec.new _) p0 hpl) 0#usize rfl (by simp)
        (by simp [alloc.vec.Vec.new])
      refine ⟨R, ?_, ?_⟩
      · unfold sim.step.input_block_periods; simp only [h0', if_false]; rw [RS]
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, vec_push_ok _ _ hpl]; exact hR
      simp only [topS] at er0 ⊢
      rw [er0]
      simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, vpush_val, alloc.vec.Vec.new,
        List.nil_append, List.map_cons, List.map_nil, List.singleton_append] at eR
      have hb : (playableS tn pb).breaks.toList = pb.breaks.val.map simPP := by simp [playableS, abs, simPP]
      rw [hb]
      cases hm : (pb.breaks.val.map simPP).mapM (simBBP (playableS tn pb).objects) with
      | error e => rw [hm] at eR; cases R <;> simp_all [simRel, Except.map, Bind.bind, Except.bind]
      | ok ps =>
        rw [hm] at eR
        cases R with
        | Err e => simp [simRel, Except.map] at eR
        | Ok w => simp_all [simRel, Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure]
end OsuProofs
