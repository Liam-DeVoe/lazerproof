/-
`sim::step` legacy hit policy (Rust) refines `OsuModel.Sim.Sim.checkHittable` (`.legacy hittableRange`):
`idx_of` (= `List.idxOf?`), the "blocked by an earlier object" scan `legacy_blocked_by_earlier` (model
`simLegScan`), and `check_hittable` under the legacy policy.
-/
import OsuProofs.Sim.InputPhase
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl OsuModel.Net
theorem sim_idx_of_loop (v : Slice Usize) (x : Usize) : ∀ n (k : Usize), v.val.length - k.val = n → k.val ≤ v.val.length →
    ∃ o, sim.step.idx_of_loop v x k none = ok o ∧
      Option.map (· + k.val) (((v.val.drop k.val).map (·.val)).idxOf? x.val) = Option.map (·.val) o := by
  intro n
  induction n with
  | zero =>
    intro k hn hk
    have hk' : k.val = v.val.length := by omega
    refine ⟨none, ?_, by simp [hk']⟩
    unfold sim.step.idx_of_loop; rw [loop_unfold]
    have : ¬ (k < Slice.len v) := by rw [slice_lt_len_iff]; omega
    simp [sim.step.idx_of_loop.body, this]
  | succ n ih =>
    intro k hn hk
    have hlt : k.val < v.val.length := by omega
    have hlt' : k < Slice.len v := by rw [slice_lt_len_iff]; exact hlt
    have hks : k.val + 1 ≤ Usize.max := by have := v.property; omega
    obtain ⟨k1, hk1, ek1⟩ := usize_add_one k hks
    have hd : v.val.drop k.val = v.val[k.val] :: v.val.drop (k.val + 1) := List.drop_eq_getElem_cons hlt
    by_cases hx : v.val[k.val] = x
    · refine ⟨some k, ?_, by simp [hd, hx, List.idxOf?_cons]⟩
      unfold sim.step.idx_of_loop; rw [loop_unfold]; dsimp only
      rw [show sim.step.idx_of_loop.body v x k none = ok (.cont (k1, some k)) by
        simp [sim.step.idx_of_loop.body, hlt', core.option.Option.is_none, slice_index_ok v k hlt, hx, hk1]; exact congrArg _ hx]
      simp only [bind_ok]
      rw [loop_unfold]
      by_cases h2 : k1 < Slice.len v <;> simp [sim.step.idx_of_loop.body, h2, core.option.Option.is_none]
    · have hxv : ¬ (v.val[k.val]).val = x.val := fun h => hx (by scalar_tac)
      obtain ⟨o, ho, eo⟩ := ih k1 (by omega) (by omega)
      refine ⟨o, ?_, ?_⟩
      · unfold sim.step.idx_of_loop; rw [loop_unfold]; dsimp only
        rw [show sim.step.idx_of_loop.body v x k none = ok (.cont (k1, none)) by
          simp [sim.step.idx_of_loop.body, hlt', core.option.Option.is_none, slice_index_ok v k hlt, hx, hk1]; intro h; exact hx (UScalar.eq_of_val_eq h)]
        simp only [bind_ok]; unfold sim.step.idx_of_loop at ho; exact ho
      · rw [← eo, hd, ek1]
        have : (v.val[k.val].val == x.val) = false := by
          simp; intro h; exact hx (by scalar_tac)
        simp only [List.map_cons, List.idxOf?_cons, this, Bool.false_eq_true, if_false, Option.map_map]
        congr 1; funext i; simp; omega

theorem sim.step.idx_of_refines (v : Slice Usize) (x : Usize) :
    ∃ o, sim.step.idx_of v x = ok o ∧ (v.val.map (·.val)).idxOf? x.val = Option.map (·.val) o := by
  obtain ⟨o, ho, eo⟩ := sim_idx_of_loop v x _ 0#usize rfl (by simp)
  exact ⟨o, ho, by simpa using eo⟩

@[simp] theorem sim_step_F64_3 : sim.step.F64_3 = ok (3 : F64) := by simp [sim.step.F64_3]

/-- the legacy policy's "blocked by an earlier object" scan (`for p in alive` of `checkHittable .legacy`) -/
def simLegScan (aj : Nat → Bool) (endOf : Nat → F64) (r : Nat × Int) (hs : F64) : List Nat → Bool
  | [] => false
  | p :: t => if aj p then simLegScan aj endOf r hs t
    else if (decide (r.2 < 0) && p == r.1) then false
    else if endOf p + 3 < hs then true else simLegScan aj endOf r hs t

def simEndOf (v : alloc.vec.Vec sim.playable.TopObj) (i : Nat) : F64 := ((v.val[i]?).map (·.h.end_time)).getD 0

theorem sim_leg_stopped (c : sim.state.Ctx) (s : sim.state.St) (alive : Slice Usize) (r : sim.step.Ref)
    (h : sim.playable.HObj) (k : Usize) (sh : Bool) :
    sim.step.legacy_blocked_by_earlier_loop c s alive r h k true sh = ok sh := by
  unfold sim.step.legacy_blocked_by_earlier_loop; rw [loop_unfold]
  by_cases h2 : k < Slice.len alive <;> simp [sim.step.legacy_blocked_by_earlier_loop.body, h2]

theorem sim_leg_loop (c : sim.state.Ctx) (s : sim.state.St) (alive : Slice Usize) (r : sim.step.Ref)
    (h : sim.playable.HObj) (aj : Nat → Bool) (hj : ∀ p ∈ alive.val, sim.step.all_judged s p = ok (aj p.val))
    (hE : ∀ p ∈ alive.val, p.val < c.pb.objects.val.length) :
    ∀ n (k : Usize), alive.val.length - k.val = n → k.val ≤ alive.val.length →
    sim.step.legacy_blocked_by_earlier_loop c s alive r h k false false =
      ok (simLegScan aj (simEndOf c.pb.objects) (r.top.val, r.nested.val) h.start
        ((alive.val.drop k.val).map (·.val))) := by
  intro n
  induction n with
  | zero =>
    intro k hn hk
    have hk' : k.val = alive.val.length := by omega
    have : ¬ (k < Slice.len alive) := by rw [slice_lt_len_iff]; omega
    unfold sim.step.legacy_blocked_by_earlier_loop; rw [loop_unfold]
    simp [sim.step.legacy_blocked_by_earlier_loop.body, this, hk', simLegScan]
  | succ n ih =>
    intro k hn hk
    have hlt : k.val < alive.val.length := by omega
    have hlt' : k < Slice.len alive := by rw [slice_lt_len_iff]; exact hlt
    have hks : k.val + 1 ≤ Usize.max := by have := alive.property; omega
    obtain ⟨k1, hk1, ek1⟩ := usize_add_one k hks
    have hd : alive.val.drop k.val = alive.val[k.val] :: alive.val.drop (k.val + 1) := List.drop_eq_getElem_cons hlt
    have hpm : alive.val[k.val] ∈ alive.val := List.getElem_mem hlt
    generalize hp : alive.val[k.val] = p at hpm hd
    have hpE := hE p hpm
    have hix : Slice.index_usize alive k = ok p := by rw [← hp]; exact slice_index_ok alive k hlt
    have hend : simEndOf c.pb.objects p.val = (c.pb.objects.val[p.val]'hpE).h.end_time := by
      simp [simEndOf, List.getElem?_eq_getElem hpE]
    have IH := ih k1 (by omega) (by omega)
    unfold sim.step.legacy_blocked_by_earlier_loop at IH
    rw [ek1] at IH
    have STP := fun b => sim_leg_stopped c s alive r h k1 b
    unfold sim.step.legacy_blocked_by_earlier_loop at STP
    rw [hd]; simp only [List.map_cons, simLegScan]
    unfold sim.step.legacy_blocked_by_earlier_loop; rw [loop_unfold]; dsimp only
    cases ha : aj p.val
    · simp only [Bool.false_eq_true, if_false]
      by_cases hneg : r.nested < 0#i64
      · have h0 : r.nested.val < 0 := by scalar_tac
        by_cases hpt : p = r.top
        · have hv : (p.val == r.top.val) = true := by simp [hpt]
          subst hpt
          rw [show sim.step.legacy_blocked_by_earlier_loop.body s alive c r h k false false = ok (.cont (c, r, h, k1, true, false)) by simp [sim.step.legacy_blocked_by_earlier_loop.body, hlt', hix, hj _ hpm, ha, hneg,
            hk1]]; simp only [bind_ok]
          simp only [hv, h0, decide_true, Bool.and_true, if_true]; exact STP false
        · have hv : (p.val == r.top.val) = false := by simp; intro e; exact hpt (UScalar.eq_of_val_eq e)
          by_cases hlt3 : (c.pb.objects.val[p.val]'hpE).h.end_time + 3 < h.start
          · rw [show sim.step.legacy_blocked_by_earlier_loop.body s alive c r h k false false = ok (.cont (c, r, h, k1, true, true)) by simp [sim.step.legacy_blocked_by_earlier_loop.body, hlt', hix, hj p hpm, ha, hneg,
              hpt, hk1, vec_index_eq _ _ hpE, vec_index_usize_ok _ _ hpE, hlt3, float.F64.add, float.F64.lt]]; simp only [bind_ok]
            simp only [hv, Bool.and_false, Bool.false_eq_true, if_false, hend, hlt3, if_true]; exact STP true
          · rw [show sim.step.legacy_blocked_by_earlier_loop.body s alive c r h k false false = ok (.cont (c, r, h, k1, false, false)) by simp [sim.step.legacy_blocked_by_earlier_loop.body, hlt', hix, hj p hpm, ha, hneg,
              hpt, hk1, vec_index_eq _ _ hpE, vec_index_usize_ok _ _ hpE, hlt3, float.F64.add, float.F64.lt]]; simp only [bind_ok]
            simp only [hv, Bool.and_false, Bool.false_eq_true, if_false, hend, hlt3]; exact IH
      · have h0 : ¬ r.nested.val < 0 := by scalar_tac
        by_cases hlt3 : (c.pb.objects.val[p.val]'hpE).h.end_time + 3 < h.start
        · rw [show sim.step.legacy_blocked_by_earlier_loop.body s alive c r h k false false = ok (.cont (c, r, h, k1, true, true)) by simp [sim.step.legacy_blocked_by_earlier_loop.body, hlt', hix, hj p hpm, ha, hneg,
            hk1, vec_index_eq _ _ hpE, vec_index_usize_ok _ _ hpE, hlt3, float.F64.add, float.F64.lt]]; simp only [bind_ok]
          simp only [h0, decide_false, Bool.false_and, Bool.false_eq_true, if_false, hend, hlt3, if_true]; exact STP true
        · rw [show sim.step.legacy_blocked_by_earlier_loop.body s alive c r h k false false = ok (.cont (c, r, h, k1, false, false)) by simp [sim.step.legacy_blocked_by_earlier_loop.body, hlt', hix, hj p hpm, ha, hneg,
            hk1, vec_index_eq _ _ hpE, vec_index_usize_ok _ _ hpE, hlt3, float.F64.add, float.F64.lt]]; simp only [bind_ok]
          simp only [h0, decide_false, Bool.false_and, Bool.false_eq_true, if_false, hend, hlt3]; exact IH
    · rw [show sim.step.legacy_blocked_by_earlier_loop.body s alive c r h k false false = ok (.cont (c, r, h, k1, false, false)) by simp [sim.step.legacy_blocked_by_earlier_loop.body, hlt', hix, hj p hpm, ha, hk1]]; simp only [bind_ok]
      simp only [if_true]; exact IH

theorem sim_arr_idxOf (l : List Nat) (a : Nat) : l.toArray.idxOf? a = l.idxOf? a := by
  first | simp | rw [Array.idxOf?_eq_map_finIdxOf?_val]; simp [List.idxOf?, Array.finIdxOf?]

theorem sim_legScan_congr (aj aj' : Nat → Bool) (e e' : Nat → F64) (r : Nat × Int) (hs : F64) (l : List Nat)
    (ha : ∀ p ∈ l, aj p = aj' p) (he : ∀ p ∈ l, e p = e' p) :
    simLegScan aj e r hs l = simLegScan aj' e' r hs l := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    simp only [simLegScan, ha p List.mem_cons_self, he p List.mem_cons_self,
      ih (fun q hq => ha q (List.mem_cons_of_mem _ hq)) (fun q hq => he q (List.mem_cons_of_mem _ hq))]

/-- the spec loop's step function -/
def simLegG (aj : Nat → Bool) (e : Nat → F64) (r : Nat × Int) (hs : F64) (p : Nat)
    (_ : Option OsuModel.Sim.Sim.ClickAction × Unit) : ForInStep (Option OsuModel.Sim.Sim.ClickAction × Unit) :=
  if aj p then .yield (none, ()) else if (decide (r.2 < 0) && p == r.1) then .done (none, ())
  else if e p + 3 < hs then .done (some .shake, ()) else .yield (none, ())

theorem sim_legG_foldr (aj : Nat → Bool) (e : Nat → F64) (r : Nat × Int) (hs : F64) (l : List Nat) :
    l.foldr (simForStep (simLegG aj e r hs)) id (none, ()) =
      (if simLegScan aj e r hs l then some .shake else none, ()) := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    simp only [List.foldr_cons, simForStep, simLegG, simLegScan]
    by_cases h1 : aj p = true
    · simp [h1, ih]
    · by_cases h2 : (decide (r.2 < 0) && p == r.1) = true
      · simp [h1, h2]
      · by_cases h3 : e p + 3 < hs
        · simp [h1, h2, h3]
        · simp only [h1, h2, h3, if_false, Bool.false_eq_true]; exact ih

set_option hygiene false in
macro "sim_leg_tail" : tactic => `(tactic| (
    refine ⟨if (hrS result == .none) = true then .Shake
      else if simLegScan ajF (simEndOf c.pb.objects) (r.top.val, r.nested.val) (simHobj c r).start (v.val.map (·.val))
      then .Shake else if F64.abs ((simHobj c r).start - time) < range then .Hit else .Shake, ?_, ?_⟩
    · try dsimp only
      simp only [hr_eq_ok, bind_ok, show hrS .None = .none from rfl]
      by_cases hn : (hrS result == .none) = true
      · simp [hn]
      · simp [hn]
        rw [hRL']
        simp only [bind_ok, float.F64.sub, float.F64.abs, float.F64.lt]
        all_goals (split_ifs <;> simp)
    · by_cases hn : (hrS result == .none) = true
      · simp [hn, abs, clickS]
      · simp only [hn, if_false, Bool.false_eq_true, simM_bind]
        rw [simM_forIn_array_eval _ _ _ _ _ (hF _ HD)]
        rw [sim_legG_foldr, ← sim_legScan_congr _ _ _ _ _ _ _ (fun _ _ => rfl) hEnd]
        try simp only [List.toList_toArray]
        all_goals (split_ifs <;> (try simp [Except.bind, abs, clickS, hobjS]))
        all_goals (exfalso; rename_i q1 q2; first | exact q1 q2 | exact q2 q1)))

theorem sim_usize_sub_one (x : Usize) (h : 1 ≤ x.val) : ∃ z, x - 1#usize = ok z ∧ z.val = x.val - 1 := by
  obtain ⟨z, hz, hv, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := x) (y := 1#usize) (by simpa using h))
  exact ⟨z, hz, by simpa using hv⟩

theorem sim.step.check_hittable_legacy_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (r : sim.step.Ref)
    (time : F64) (result : sim.basic.HitResult) (range : F64) (hinv : SimInv c s) (hr : simRefOk c r)
    (hpol : c.cfg.policy = .Legacy range) :
    ∃ a, sim.step.check_hittable c s r time result = ok a ∧
      OsuModel.Sim.Sim.checkHittable (abs r) (abs time) (abs result) (simCtxS tn fo c) (simStS tn s) =
        .ok (abs a, simStS tn s) := by
  obtain ⟨hh, eh⟩ := sim_hobj_of_eq tn fo c r hr
  obtain ⟨v, hv, ev⟩ := sim.step.alive_objects_refines tn fo c s hinv.dict_in hinv.dict_small
  have hS : ∀ i ∈ ((simStS tn s).dictSlots.filterMap id), i < (simCtxS tn fo c).pb.objects.size := by
    intro i hi
    simp [simStS, abs] at hi
    obtain ⟨a, ha, hai⟩ := hi
    rw [← hai]; simpa using hinv.dict_in _ ha a rfl
  have hvb : ∀ x ∈ v.val, x.val < c.pb.objects.val.length := by
    intro x hx
    have e2 := ev.symm.trans (simS_aliveObjects _ _ hS)
    have e3 : (abs v : _root_.Array Nat) = _ := (Prod.mk.inj (Except.ok.inj e2)).1
    have hx' : x.val ∈ (abs v : _root_.Array Nat).toList := by simp [abs]; exact ⟨x, hx, rfl⟩
    rw [e3] at hx'
    have := sim_simSortL_mem _ _ _ (by simpa using hx')
    have := hS _ (by simpa using this)
    simpa using this
  let ajF : Nat → Bool := fun i => match OsuModel.Sim.Sim.allJudged i (simCtxS tn fo c) (simStS tn s) with
    | .ok (b, _) => b | .error _ => false
  have hAJ : ∀ x ∈ v.val, sim.step.all_judged s x = ok (ajF x.val) ∧
      OsuModel.Sim.Sim.allJudged x.val (simCtxS tn fo c) (simStS tn s) = .ok (ajF x.val, simStS tn s) := by
    intro x hx
    obtain ⟨b, hb, eb⟩ := sim.step.all_judged_refines tn fo c s x (by rw [hinv.objs_len]; exact hvb x hx)
    have : ajF x.val = b := by simp only [ajF, eb]
    rw [this]; exact ⟨hb, eb⟩
  have hTop : ∀ i, i < c.pb.objects.val.length → OsuModel.Sim.Sim.topObj i (simCtxS tn fo c) (simStS tn s) =
      .ok (topS tn (c.pb.objects.val[i]!), simStS tn s) := by
    intro i hi
    have hi' : i < (simCtxS tn fo c).pb.objects.size := by simpa using hi
    have e1 := sim_ctxS_object tn fo c i hi'
    simp [OsuModel.Sim.Sim.topObj, OsuModel.Sim.Sim.getA, OsuModel.Sim.Sim.ctx, hi', Except.bind, hi, e1,
      getElem!_def, List.getElem?_eq_getElem hi]
  have hRL := sim_leg_loop c s (alloc.vec.Vec.deref v) r (simHobj c r) ajF
    (fun p hp => (hAJ p (by simpa [alloc.vec.Vec.deref] using hp)).1)
    (fun p hp => hvb p (by simpa [alloc.vec.Vec.deref] using hp)) _ 0#usize rfl (by simp)
  have hRL' : sim.step.legacy_blocked_by_earlier c s (alloc.vec.Vec.deref v) r (simHobj c r) =
      ok (simLegScan ajF (simEndOf c.pb.objects) (r.top.val, r.nested.val) (simHobj c r).start (v.val.map (·.val))) := by
    simpa [alloc.vec.Vec.deref] using hRL
  have hpolS : (simCtxS tn fo c).cfg.policy = .legacy range := by simp [simCtxS, abs, configS, hpol]
  unfold OsuModel.Sim.Sim.checkHittable
  simp only [simM_bind, OsuModel.Sim.Sim.ctx, simM_read, Except.bind, eh, hpolS, ev]
  unfold sim.step.check_hittable sim.step.check_hittable_legacy
  simp only [hh, bind_ok, hpol, hv]
  have hEnd : ∀ p ∈ (v.val.map (·.val)), simEndOf c.pb.objects p = (c.pb.objects.val[p]!).h.end_time := by
    intro p hp
    obtain ⟨y, hy, hyp⟩ := List.mem_map.mp hp
    have := hvb y hy; rw [← hyp]
    simp [simEndOf, List.getElem?_eq_getElem this, getElem!_def]
  have hF : ∀ d : Bool, decide (r.nested.val < 0) = d → ∀ x ∈ ((v.val.map (·.val)).toArray).toList, ∀ b : Option OsuModel.Sim.Sim.ClickAction × Unit,
      (do
        let __do_lift ← OsuModel.Sim.Sim.allJudged x
        if __do_lift = true then pure (ForInStep.yield (none, ()))
        else if (d && x == r.top.val) = true then pure (ForInStep.done (none, ()))
        else do
          let __do_lift ← OsuModel.Sim.Sim.topObj x
          if __do_lift.h.endTime + 3 < (hobjS tn (simHobj c r)).start then
            pure (ForInStep.done (some OsuModel.Sim.Sim.ClickAction.shake, ()))
          else pure (ForInStep.yield (none, ())) : OsuModel.Sim.SimM _) (simCtxS tn fo c) (simStS tn s) =
      .ok (simLegG ajF (fun p => (c.pb.objects.val[p]!).h.end_time) (r.top.val, r.nested.val) (simHobj c r).start x b,
        simStS tn s) := by
    intro d hdd x hx b
    subst hdd
    have hx' : x ∈ v.val.map (·.val) := by simpa using hx
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hx'
    subst hyx
    simp only [simM_bind, (hAJ y hy).2, Except.bind, simLegG]
    cases ajF y.val
    · simp only [Bool.false_eq_true, if_false]
      by_cases hd : (decide (r.nested.val < 0) && y.val == r.top.val) = true
      · simp [hd]
      · simp only [hd, ite_false, Bool.false_eq_true, simM_bind, hTop _ (hvb y hy), Except.bind, simM_ite]
        split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; exact h2 h1) | (exfalso; exact h1 h2)
    · rfl
  by_cases hneg : r.nested < 0#i64
  · have h0 : r.nested.val < 0 := by scalar_tac
    obtain ⟨o, ho, eo⟩ := sim.step.idx_of_refines (alloc.vec.Vec.deref v) r.top
    have eo' : (abs v : _root_.Array Nat).idxOf? r.top.val = o.map (·.val) := by
      simp only [abs, sim_arr_idxOf]; simpa [alloc.vec.Vec.deref] using eo
    simp only [hneg, ho, if_true, bind_ok]
    simp only [abs, h0, decide_true, if_true] at eo' ⊢
    rw [eo']
    have HD : decide (r.nested.val < 0) = true := by simp [h0]
    rcases o with _ | idx
    · simp only [Option.map_none, bind_ok]
      sim_leg_tail
    · simp only [Option.map_some]
      have eo2 : (v.val.map (·.val)).idxOf? r.top.val = some idx.val := by simpa [alloc.vec.Vec.deref] using eo
      obtain ⟨hil, -, -⟩ := List.idxOf?_eq_some_iff.mp eo2
      have hil' : idx.val < v.val.length := by simpa using hil
      by_cases hpos : idx > 0#usize
      · have hpos' : 0 < idx.val := by scalar_tac
        obtain ⟨i, hi, ei⟩ := sim_usize_sub_one idx (by omega)
        have hiv : i.val < v.val.length := by omega
        have hpm : v.val[i.val] ∈ v.val := List.getElem_mem hiv
        have hpb := hvb _ hpm
        obtain ⟨hj1, hj2⟩ := hAJ _ hpm
        have hga : OsuModel.Sim.Sim.getA (v.val.map (·.val)).toArray (idx.val - 1) "alive objects" (simCtxS tn fo c)
            (simStS tn s) = .ok ((v.val[i.val]).val, simStS tn s) := by
          have : idx.val - 1 < (v.val.map (·.val)).toArray.size := by simp; omega
          simp [OsuModel.Sim.Sim.getA, this, abs, ← ei, hiv]
        simp only [hpos', if_true, decide_true, hpos, hi, bind_ok, vec_index_eq _ _ hiv, vec_index_eq _ _ hpb]
        simp only [simM_bind, hga, Except.bind, hTop _ hpb, hj2]
        have hsh_eq : (topS tn (c.pb.objects.val[(v.val[i.val]).val]!)).h.stackHeight =
            (c.pb.objects.val[(v.val[i.val]).val]'hpb).h.stack_height.val := by
          simp [topS, hobjS, List.getElem?_eq_getElem hpb]
        rw [hsh_eq]
        by_cases hsh : (c.pb.objects.val[(v.val[i.val]).val]'hpb).h.stack_height > 0#i64
        · have hsh' : (c.pb.objects.val[(v.val[i.val]).val]'hpb).h.stack_height.val > 0 := by scalar_tac
          cases haj : ajF (v.val[i.val]).val
          · refine ⟨.Ignore, by simp [hsh, hj1, haj], by simp [hsh', haj, abs, clickS]⟩
          · simp only [hsh, if_true, hj1, haj, bind_ok, ite_true, hsh', decide_true, Bool.not_true, Bool.and_false,
              Bool.false_eq_true, ite_false]
            sim_leg_tail
        · have hsh' : ¬ (c.pb.objects.val[(v.val[i.val]).val]'hpb).h.stack_height.val > 0 := by scalar_tac
          simp only [hsh, if_false, bind_ok, ite_false, hsh', decide_false, Bool.false_and,
            Bool.false_eq_true]
          sim_leg_tail
      · have hpos' : ¬ 0 < idx.val := by scalar_tac
        simp only [hpos, hpos', if_false, ite_false, bind_ok, gt_iff_lt]
        sim_leg_tail
  · have h0 : ¬ r.nested.val < 0 := by scalar_tac
    have HD : decide (r.nested.val < 0) = false := by simp [h0]
    simp only [hneg, if_false, ite_false, bind_ok]
    simp only [abs, h0, decide_false, ite_false]
    sim_leg_tail

/-- `checkHittable` under both hit policies (`hcap`: the `enumerateUpTo` result fits a `Vec`, start-time-ordered
policy only). -/
theorem sim.step.check_hittable_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (r : sim.step.Ref)
    (time : F64) (result : sim.basic.HitResult) (hinv : SimInv c s) (hr : simRefOk c r)
    (hcap : ∀ v, OsuModel.Sim.Sim.enumerateUpTo (simHobj c r).start (simCtxS tn fo c) (simStS tn s) =
      .ok (v, simStS tn s) → v.size < Usize.max) :
    ∃ a, sim.step.check_hittable c s r time result = ok a ∧
      OsuModel.Sim.Sim.checkHittable (abs r) (abs time) (abs result) (simCtxS tn fo c) (simStS tn s) =
        .ok (abs a, simStS tn s) := by
  cases hp : c.cfg.policy with
  | StartTimeOrdered => exact sim.step.check_hittable_sto_refines tn fo c s r time result hinv hr hp hcap
  | Legacy range => exact sim.step.check_hittable_legacy_refines tn fo c s r time result range hinv hr hp
end OsuProofs
