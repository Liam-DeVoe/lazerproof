/-
Sim3b part 3b (WIP, not root-imported): `break_block_period`, the generic Rust-index-loop / spec-`forIn` lockstep
`s3b_loopR_forIn`, and `input_block_update`.
-/
import OsuProofs.Sim3.SB_Upd
import OsuProofs.Sim.Periods
import OsuProofs.Sim3.SB_US
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

theorem s3b_find_topS (tn) (l : List sim.playable.TopObj) (be : F64) :
    (l.map (topS tn)).find? (fun o => decide (be ≤ o.h.start)) =
      ((l.findIdx? (fun o => decide (be ≤ o.h.start))).bind (fun i => l[i]?)).map (topS tn) := by
  rw [List.find?_map, List.find?_eq_bind_findIdx?_getElem?]
  have : (fun o => decide (be ≤ o.h.start)) ∘ topS tn = (fun o : sim.playable.TopObj => decide (be ≤ o.h.start)) := by
    funext o; rfl
  rw [this]

theorem sim.step.break_block_period_refines (tn) (pb : sim.playable.Playable) (b : Usize)
    (hb : b.val < pb.breaks.val.length) :
    ∃ r, sim.step.break_block_period pb b = ok r ∧
      s3b_erel (fun p => (abs p : F64 × F64)) r
        (s3b_breakPeriodS (playableS tn pb) (pb.breaks.val[b.val]'hb).start (pb.breaks.val[b.val]'hb).«end») := by
  obtain ⟨o, ho, hov⟩ := sim.step.first_object_after_refines pb (pb.breaks.val[b.val]'hb).«end»
  unfold sim.step.break_block_period s3b_breakPeriodS
  simp only [vec_index_eq _ _ hb, bind_ok, ho]
  have hobj : (playableS tn pb).objects = (pb.objects.val.map (topS tn)).toArray := by simp [playableS, abs]
  rw [hobj, List.find?_toArray, s3b_find_topS, ← hov]
  rcases o with _ | oi
  · exact ⟨_, rfl, by simp [s3b_erel, throw, throwThe, MonadExceptOf.throw]⟩
  · have hoi : oi.val < pb.objects.val.length := by
      have := List.findIdx?_eq_some_iff_getElem.mp (hov.symm.trans (by rfl : (some oi).map (·.val) = some oi.val))
      exact this.1
    simp only [Option.map_some, Option.bind_some, List.getElem?_eq_getElem hoi, vec_index_eq _ _ hoi, bind_ok,
      sim.step.block_vt_refines tn, sim_step_F64_1, float.F64.sub]
    obtain ⟨r, hr, er⟩ := sim.step.block_period_refines (pb.breaks.val[b.val]'hb).start
      (s3b_vtS (hobjS tn (pb.objects.val[oi.val]'hoi).h) - 1)
    exact ⟨r, hr, by simpa [topS] using er⟩

/-! ## Generic lockstep: a Rust index loop with early `Err` exit vs a spec `for x in l` in `SimM` -/
theorem s3b_loopR_forIn {T α : Type}
    (body : T × Usize → Result (ControlFlow (T × Usize) (core.result.Result Unit sim.err.SimErr × T)))
    (l : List α) (F : α → PUnit → OsuModel.Sim.SimM (ForInStep PUnit)) (C : OsuModel.Sim.Ctx)
    (A : T → OsuModel.Sim.St) (Inv : T → Prop) (hn : l.length ≤ Usize.max)
    (hstep : ∀ t (q : Usize) (h : q.val < l.length), Inv t → ∀ q1 : Usize, q1.val = q.val + 1 →
      (∃ t', body (t, q) = ok (.cont (t', q1)) ∧ Inv t' ∧ F (l[q.val]'h) PUnit.unit C (A t) = .ok (.yield PUnit.unit, A t')) ∨
      (∃ e t', body (t, q) = ok (.done (.Err e, t')) ∧ ∃ m, F (l[q.val]'h) PUnit.unit C (A t) = .error m))
    (hend : ∀ t (q : Usize), l.length ≤ q.val → body (t, q) = ok (.done (.Ok (), t))) :
    ∀ n (q : Usize) t, l.length - q.val = n → Inv t → q.val ≤ l.length → ∃ res t', loop body (t, q) = ok (res, t') ∧
      s3b_rrel (fun _ => PUnit.unit) (A t') res (forIn (l.drop q.val) PUnit.unit F C (A t)) := by
  intro n
  induction n with
  | zero =>
    intro q t hn0 _ hq
    refine ⟨.Ok (), t, by rw [loop_unfold, hend t q (by omega)]; simp only [bind_ok], ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | succ n ih =>
    intro q t hn0 hI hq
    have hlt : q.val < l.length := by omega
    obtain ⟨q1, hq1, hq1v⟩ := usize_add_one q (by omega)
    rw [List.drop_eq_getElem_cons hlt, List.forIn_cons]
    rcases hstep t q hlt hI q1 hq1v with ⟨t', hb, hI', hF⟩ | ⟨e, t', hb, m, hF⟩
    · obtain ⟨res, t'', hl, hr⟩ := ih q1 t' (by omega) hI' (by omega)
      refine ⟨res, t'', by rw [loop_unfold, hb]; simpa using hl, ?_⟩
      simp only [simM_bind, hF, Except.bind]
      rw [hq1v] at hr; exact hr
    · refine ⟨.Err e, t', by rw [loop_unfold, hb]; simp only [bind_ok], m, ?_⟩
      simp only [simM_bind, hF, Except.bind]

/-! ## `inputBlockUpdate` -/
/-- `InputBlockingMod.Update` (`Sim.inputBlockUpdate`). The callee `period_is_in_any` (sim::scoring, not in this
slice) enters through its refinement statement `hp` at the call's arguments. -/
-- CONDITIONAL: hp (period_is_in_any refinement at the call; discharged by input_block_update_refines')
theorem s3b_input_block_update_hp (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (k : Usize)
    (hinv : SimInv c s) (hk1 : k.val < s.block_last.val.length) (hk2 : k.val < s.block_idx.val.length)
    (hp : (s.block_last.val[k.val]'hk1).isSome → ∃ res : Bool × Usize,
      sim.scoring.period_is_in_any (alloc.vec.Vec.deref c.block_periods) (s.block_idx.val[k.val]'hk2) s.t = ok res ∧
      OsuModel.Sim.periodIsInAny (abs c.block_periods) (s.block_idx.val[k.val]'hk2).val s.t = .ok (res.1, res.2.val)) :
    ∃ s', sim.step.input_block_update c s k = ok s' ∧
      OsuModel.Sim.Sim.inputBlockUpdate k.val (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧
      (∃ bl bi, s' = { s with block_last := bl, block_idx := bi }) ∧ SimInv c s' ∧ s'.future_order = s.future_order := by
  have hk1' : k.val < (simStS tn s).blockLast.size := by simpa [simStS] using hk1
  have hk2' : k.val < (simStS tn s).blockIdx.size := by simpa [simStS, abs] using hk2
  have e1 : (simStS tn s).blockLast[k.val]'hk1' = (s.block_last.val[k.val]'hk1).map actS := by simp [simStS]
  have e2 : (simStS tn s).blockIdx[k.val]'hk2' = (s.block_idx.val[k.val]'hk2).val := by simp [simStS, abs]
  unfold sim.step.input_block_update OsuModel.Sim.Sim.inputBlockUpdate
  simp only [vec_index_eq _ _ hk1, bind_ok, core.option.Option.is_some, simM_bind, OsuModel.Sim.Sim.ctx,
    OsuModel.Sim.Sim.st, simM_read, simM_get, Except.bind, OsuModel.Sim.Sim.getA, dif_pos hk1', simM_pure, e1,
    Option.isSome_map]
  cases hb : (s.block_last.val[k.val]'hk1).isSome with
  | false => exact ⟨s, by simp, by simp, ⟨_, _, rfl⟩, hinv, rfl⟩
  | true =>
    obtain ⟨⟨ia, idx⟩, hr, hs⟩ := hp hb
    have hbp : (simCtxS tn fo c).blockPeriods = abs c.block_periods := rfl
    simp only [if_true, vec_index_eq _ _ hk2, dif_pos hk2', e2, hbp, hs, hr, bind_ok, vec_index_mut_eq _ _ hk2,
      vec_index_mut_eq _ _ hk1, OsuModel.Sim.Sim.liftExcept, simM_pure, OsuModel.Sim.Sim.setA, simM_set]
    have hs' : OsuModel.Sim.periodIsInAny (abs c.block_periods) (s.block_idx.val[k.val]'hk2).val (simStS tn s).t =
        .ok (ia, idx.val) := hs
    simp only [simM_bind, simM_pure, s3b_ebok, hs', simM_set, simM_get, uncurry_apply_pair]
    try dsimp only
    have hk1'' : k.val < ((simStS tn s).blockIdx.set k.val idx.val hk2').size := by simpa using hk2'
    cases ia
    · refine ⟨_, rfl, ?_, ⟨_, _, rfl⟩, s3b_inv_of hinv rfl rfl, rfl⟩
      simp only [Bool.false_eq_true, if_false, simM_pure]
      have hI : (simStS tn s).blockIdx.set k.val idx.val hk2' =
          (simStS tn { s with block_idx := s.block_idx.set k idx }).blockIdx := by
        simp [simStS, abs, alloc.vec.Vec.set, List.map_set]
      rw [hI]; rfl
    · refine ⟨_, rfl, ?_, ⟨_, _, rfl⟩, s3b_inv_of hinv rfl rfl, rfl⟩
      simp only [if_true, simM_bind, simM_get, s3b_ebok, dif_pos hk1', simM_pure, simM_set]
      have hI : (simStS tn s).blockIdx.set k.val idx.val hk2' =
          (simStS tn { s with block_idx := s.block_idx.set k idx }).blockIdx := by
        simp [simStS, abs, alloc.vec.Vec.set, List.map_set]
      have hL : ∀ h, (simStS tn s).blockLast.set k.val none h =
          (simStS tn { s with block_last := s.block_last.set k none }).blockLast := by
        intro h; simp [simStS, abs, alloc.vec.Vec.set, List.map_set]
      rw [hI, hL]; rfl

/-- `InputBlockingMod.Update` (`Sim.inputBlockUpdate`); the `period_is_in_any` side condition is the stored index
being in range of the block periods. -/
theorem sim.step.input_block_update_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (k : Usize)
    (hinv : SimInv c s) (hk1 : k.val < s.block_last.val.length) (hk2 : k.val < s.block_idx.val.length)
    (hidx : c.block_periods.val.length ≠ 0 → (s.block_idx.val[k.val]'hk2).val < c.block_periods.val.length) :
    ∃ s', sim.step.input_block_update c s k = ok s' ∧
      OsuModel.Sim.Sim.inputBlockUpdate k.val (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧
      (∃ bl bi, s' = { s with block_last := bl, block_idx := bi }) ∧ SimInv c s' ∧ s'.future_order = s.future_order := by
  refine s3b_input_block_update_hp tn fo c s k hinv hk1 hk2 (fun _ => ?_)
  obtain ⟨r, hr, er⟩ := sim.scoring.period_is_in_any_refines (alloc.vec.Vec.deref c.block_periods)
    (s.block_idx.val[k.val]'hk2) s.t (by simpa using hidx)
  refine ⟨r, hr, ?_⟩
  have e : (abs c.block_periods : _root_.Array (F64 × F64)) = (simPS (alloc.vec.Vec.deref c.block_periods)).toArray := by
    simp [simPS, abs]
  rw [e]; exact er

end OsuProofs
