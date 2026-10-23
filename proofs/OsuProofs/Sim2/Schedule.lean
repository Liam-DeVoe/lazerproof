/-
`sim::schedule` (Rust, total: `Result<_, SimErr>`) refines `OsuModel.Sim` Schedule (Except String).
Error relation (Sim2, DECISIONS D31): `s2_rel` = both succeed with related values, or both reject (the spec's
message is not related to the `SimErr` variant).
-/
import OsuProofs.Sim.Abs
import OsuProofs.Sim.NetX
import OsuProofs.Sim2.SchedSpec
import OsuProofs.Sim2.Abs
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl OsuModel.Sim OsuProofs.SpecSched

/-- Sim2 error relation: spec `Except String β` vs Rust `Result<α, SimErr>`. -/
def s2_rel {α β : Type} (f : α → β) : Except String β → core.result.Result α sim.err.SimErr → Prop
  | .ok b, .Ok a => f a = b
  | .error _, .Err _ => True
  | _, _ => False

@[simp] theorem s2_sched_F64_2000 : sim.schedule.F64_2000 = ok (2000 : F64) := by
  unfold sim.schedule.F64_2000; exact from_bits_lit _ _ (by decide +kernel)
@[simp] theorem s2_sched_F64_1000 : sim.schedule.F64_1000 = ok (1000 : F64) := by
  unfold sim.schedule.F64_1000; exact from_bits_lit _ _ (by decide +kernel)
@[simp] theorem s2_sched_F64_ONE : sim.schedule.F64_ONE = ok (1 : F64) := by
  unfold sim.schedule.F64_ONE; exact from_bits_lit _ _ (by decide +kernel)

theorem s2_referenceEnd_eq (pb : OsuModel.Sim.Playable) : referenceEnd pb =
    pb.objects.foldl (fun m o => o.nested.foldl (fun m n => F64.max m n.endTime) (F64.max m o.h.endTime)) F64.negInf + 1000 := by
  unfold referenceEnd
  simp [Id.run, Array.forIn_pure_yield_eq_foldl]; rfl

theorem s2_objects0 (tn : Nat → String) (pb : sim.playable.Playable) (h : 0 < pb.objects.val.length) :
    (playableS tn pb).objects[0]? = some (topS tn (pb.objects.val[0]'h)) := by
  simp [playableS, List.getElem?_eq_getElem h]

theorem sim.schedule.gameplay_start_time_refines (pb : sim.playable.Playable) :
    ∃ r, sim.schedule.gameplay_start_time pb = ok r ∧ OsuModel.Sim.gameplayStartTime (abs pb) = abs r := by
  unfold sim.schedule.gameplay_start_time OsuModel.Sim.gameplayStartTime
  by_cases h : 0 < pb.objects.val.length
  · have h' : alloc.vec.Vec.len pb.objects > 0#usize := by
      show (0#usize).val < (alloc.vec.Vec.len pb.objects).val; simpa using h
    have h0 : (0#usize).val < pb.objects.val.length := by simpa using h
    simp only [h', ite_true, s2_sched_F64_2000, net.max_refines, float.F64.sub, bind_ok]
    simp [vec_index_usize_ok _ _ h0, abs, s2_objects0 _ pb h, topS, hobjS]
  · have h' : ¬ (alloc.vec.Vec.len pb.objects > 0#usize) := by
      show ¬ ((0#usize).val < (alloc.vec.Vec.len pb.objects).val); simpa using h
    have e : pb.objects.val = [] := by simpa using h
    simp [h', abs, playableS, e]

theorem sim.schedule.reference_start_refines (pb : sim.playable.Playable) :
    ∃ r, sim.schedule.reference_start pb = ok r ∧ OsuModel.Sim.referenceStart (abs pb) = abs r := by
  obtain ⟨g, hg, eg⟩ := sim.schedule.gameplay_start_time_refines pb
  unfold sim.schedule.reference_start OsuModel.Sim.referenceStart
  rw [eg]
  by_cases h : 0 < pb.objects.val.length
  · have h' : alloc.vec.Vec.len pb.objects > 0#usize := by
      show (0#usize).val < (alloc.vec.Vec.len pb.objects).val; simpa using h
    have h0 : (0#usize).val < pb.objects.val.length := by simpa using h
    simp only [hg, h', ite_true, netx_F64_ZERO, net.min_refines, float.F64.sub, float.F64.lt, bind_ok]
    simp [vec_index_usize_ok _ _ h0, abs, playableS, List.getElem?_eq_getElem h, topS, hobjS]
    by_cases hc : (0:F64) < pb.audio_lead_in <;> simp [hc]
  · have h' : ¬ (alloc.vec.Vec.len pb.objects > 0#usize) := by
      show ¬ ((0#usize).val < (alloc.vec.Vec.len pb.objects).val); simpa using h
    have e : pb.objects.val = [] := by simpa using h
    simp [hg, h', abs, playableS, e, netx_F64_ZERO, net.min_refines]

theorem s2_getElem!_map {X Y : Type} [Inhabited Y] (l : List X) (f : X → Y) (k : Nat) (h : k < l.length) :
    (l.map f)[k]! = f l[k] := by
  rw [getElem!_pos (l.map f) k (by simpa using h)]; simp

theorem sim.schedule.max_end_time_refines (m0 : F64) (o : sim.playable.TopObj) :
    sim.schedule.max_end_time m0 o =
      ok (o.nested.val.foldl (fun m n => F64.max m n.end_time) (F64.max m0 o.h.end_time)) := by
  obtain ⟨y, hl, hv⟩ := loop_fold_gen' (fun x => sim.schedule.max_end_time_loop.body o.nested x.1 x.2) (·.2)
    o.nested.val.length (by have := o.nested.property; omega)
    (fun _ => True) (fun x => x.1) (fun k m => F64.max m ((o.nested.val.map (·.end_time))[k]!)) (fun y m => y = m)
    (by loop_step [sim.schedule.max_end_time_loop.body, net.max_refines, s2_getElem!_map])
    (by loop_end [sim.schedule.max_end_time_loop.body])
    (F64.max m0 o.h.end_time, 0#usize) trivial (by simp)
  unfold sim.schedule.max_end_time
  simp only [net.max_refines, bind_ok]
  rw [show sim.schedule.max_end_time_loop o.nested (F64.max m0 o.h.end_time) 0#usize = ok y by
    unfold sim.schedule.max_end_time_loop; exact hl]
  rw [hv, ← List.foldl_map, foldl_iterR]; simp

/-- one object's contribution to `referenceEnd` (end time, nested end times) -/
def s2_endTimes (o : sim.playable.TopObj) : F64 × List F64 := (o.h.end_time, o.nested.val.map (·.end_time))
def s2_maxEnd (m : F64) (e : F64 × List F64) : F64 := e.2.foldl F64.max (F64.max m e.1)

theorem sim.schedule.reference_end_refines (pb : sim.playable.Playable) :
    ∃ r, sim.schedule.reference_end pb = ok r ∧ OsuModel.Sim.referenceEnd (abs pb) = abs r := by
  obtain ⟨y, hl, hv⟩ := loop_fold_gen' (fun x => sim.schedule.reference_end_loop.body pb x.1 x.2) (·.2)
    pb.objects.val.length (by have := pb.objects.property; omega)
    (fun _ => True) (fun x => x.1) (fun k m => s2_maxEnd m ((pb.objects.val.map s2_endTimes)[k]!)) (fun y m => y = m)
    (by loop_step [sim.schedule.reference_end_loop.body, sim.schedule.max_end_time_refines, s2_getElem!_map,
          s2_maxEnd, s2_endTimes, List.foldl_map])
    (by loop_end [sim.schedule.reference_end_loop.body])
    (F64.negInf, 0#usize) trivial (by simp)
  refine ⟨y + 1000, ?_, ?_⟩
  · unfold sim.schedule.reference_end
    simp only [netx_F64_NEG_INF, s2_sched_F64_1000, float.F64.add, bind_ok]
    rw [show sim.schedule.reference_end_loop pb F64.negInf 0#usize = ok y by
      unfold sim.schedule.reference_end_loop; exact hl]
    simp only [bind_ok]
  · have e : y = (pb.objects.val.map s2_endTimes).foldl s2_maxEnd F64.negInf := by
      rw [hv, foldl_iterR]; simp
    rw [s2_referenceEnd_eq, e]
    simp [abs, playableS, topS, hobjS, List.foldl_map, s2_maxEnd, s2_endTimes]

theorem s2_range_map_getElem! {X : Type} [Inhabited X] (l : List X) :
    (List.range' 0 l.length).map (fun i => l[i]!) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem?_eq_getElem h2]

theorem sim.schedule.frame_times_refines (frames : Slice replay.frames.Frame) :
    ∃ r, sim.schedule.frame_times frames = ok r ∧
      (abs frames : _root_.Array OsuModel.Replay.Frame).map (·.time) = abs r := by
  have hmax := frames.property
  obtain ⟨r, hl, hr⟩ := loop_push_map (fun x => sim.schedule.frame_times_loop.body frames x.1 x.2)
    frames.val.length (fun i => (frames.val.map (·.time))[i]!)
    (by
      intro ts i hi hb
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
      refine ⟨vpush ts (frames.val[i.val]'hi).time (by omega), i1, ?_, by simp [s2_getElem!_map _ _ _ hi], hi1v⟩
      simp [sim.schedule.frame_times_loop.body, slice_lt_len_iff, hi, slice_index_ok _ _ hi, vec_push_ok _ _ (by omega : ts.val.length < Usize.max), hi1])
    (by intro ts i hi; simp [sim.schedule.frame_times_loop.body, slice_lt_len_iff, Nat.not_lt.mpr hi])
    (alloc.vec.Vec.new _) 0#usize (by simp) (by simpa using hmax)
  refine ⟨r, ?_, ?_⟩
  · unfold sim.schedule.frame_times sim.schedule.frame_times_loop; exact hl
  · have e := s2_range_map_getElem! (frames.val.map (·.time))
    simp only [List.length_map] at e
    simp only [show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero, e] at hr
    simp [abs, hr, s2_frameS, Function.comp_def]

def s2_pfStep (s : _root_.Array F64 × F64) (f : F64) : _root_.Array F64 × F64 :=
  if s.2 < f then (s.1.push f, f) else s
def s2_perframe (r0 endT : F64) (ft : _root_.Array F64) : _root_.Array F64 :=
  let p := ft.foldl s2_pfStep (#[r0], r0)
  if p.2 < endT then p.1.push endT else p.1

theorem s2_references_perframe (r0 endT : F64) (ft : _root_.Array F64) :
    OsuModel.Sim.references .perframe r0 endT ft = .ok (s2_perframe r0 endT ft) := by
  unfold OsuModel.Sim.references s2_perframe
  dsimp only
  rw [SpecSched.forIn_yield (fun r s => s2_pfStep s r) (by intro r s; unfold s2_pfStep; split <;> rfl)]
  rw [Id.run_bind]
  by_cases h : (Array.foldl s2_pfStep (#[r0], r0) ft).2 < endT
  · rw [if_pos h]; exact if_pos h
  · rw [if_neg h]; exact if_neg h

def s2_pfStepL (s : List F64 × F64) (f : F64) : List F64 × F64 :=
  if s.2 < f then (s.1 ++ [f], f) else s

theorem s2_pf_foldl (l : List F64) : ∀ (A : _root_.Array F64) (x : F64),
    (fun p => (p.1.toList, p.2)) (l.foldl s2_pfStep (A, x)) = l.foldl s2_pfStepL (A.toList, x) := by
  induction l with
  | nil => intro A x; rfl
  | cons f t ih =>
    intro A x
    simp only [List.foldl_cons]
    by_cases h : x < f
    · have e1 : s2_pfStep (A, x) f = (A.push f, f) := if_pos h
      have e2 : s2_pfStepL (A.toList, x) f = (A.toList ++ [f], f) := if_pos h
      rw [e1, e2]; simpa using ih (A.push f) f
    · have e1 : s2_pfStep (A, x) f = (A, x) := if_neg h
      have e2 : s2_pfStepL (A.toList, x) f = (A.toList, x) := if_neg h
      rw [e1, e2]; exact ih A x

theorem s2_pfL_len (l : List F64) : ∀ (L : List F64) (x : F64),
    (l.foldl s2_pfStepL (L, x)).1.length ≤ L.length + l.length := by
  induction l with
  | nil => intro L x; simp
  | cons f t ih =>
    intro L x
    simp only [List.foldl_cons, s2_pfStepL]
    split
    · have := ih (L ++ [f]) f; simp at this ⊢; omega
    · have := ih L x; simp at this ⊢; omega

theorem sim.schedule.references_perframe_refines (r0 end_t : F64) (ft : Slice F64)
    (hn : ft.val.length + 2 ≤ Usize.max) :
    ∃ r, sim.schedule.references_perframe r0 end_t ft = ok r ∧
      s2_perframe r0 end_t (abs ft) = abs r := by
  obtain ⟨y, hl, hv⟩ := loop_fold_gen' (fun x => sim.schedule.references_perframe_loop.body ft x.1 x.2.1 x.2.2)
    (·.2.2) ft.val.length (by omega)
    (fun t => t.1.val.length ≤ t.2.2.val + 1) (fun t => (t.1.val, t.2.1))
    (fun k s => s2_pfStepL s (ft.val[k]!)) (fun y s => (y.1.val, y.2) = s)
    (by
      intro t hI hlt j1 hj1 hj1v
      obtain ⟨l, last, i⟩ := t
      simp only at hI hlt hj1 hj1v ⊢
      have hp : l.val.length < Usize.max := by omega
      by_cases hc : last < ft.val[i.val]
      · refine ⟨(vpush l ft.val[i.val] hp, ft.val[i.val], j1), ?_, rfl, ?_, ?_⟩
        · simp [sim.schedule.references_perframe_loop.body, slice_lt_len_iff, hlt, slice_index_ok _ _ hlt,
            float.F64.lt, hc, vec_push_ok _ _ hp, hj1]
        · simp [s2_pfStepL, getElem!_pos ft.val i.val hlt, hc]
        · simp; omega
      · refine ⟨(l, last, j1), ?_, rfl, ?_, ?_⟩
        · simp [sim.schedule.references_perframe_loop.body, slice_lt_len_iff, hlt, slice_index_ok _ _ hlt,
            float.F64.lt, hc, hj1]
        · simp [s2_pfStepL, getElem!_pos ft.val i.val hlt, hc]
        · simp; omega)
    (by
      intro t hI hge
      obtain ⟨l, last, i⟩ := t
      refine ⟨(l, last), ?_, rfl⟩
      simp [sim.schedule.references_perframe_loop.body, slice_lt_len_iff, Nat.not_lt.mpr hge])
    (vpush (alloc.vec.Vec.new F64) r0 (by simp; omega), r0, 0#usize) (by simp) (by simp)
  obtain ⟨l1, last⟩ := y
  have hfold := s2_pf_foldl ft.val #[r0] r0
  have e : (l1.val, last) = ft.val.foldl s2_pfStepL ([r0], r0) := by
    rw [hv, foldl_iterR]; simp
  have hlen : l1.val.length ≤ ft.val.length + 1 := by
    have := s2_pfL_len ft.val [r0] r0
    rw [← e] at this; simpa [Nat.add_comm] using this
  have hp : l1.val.length < Usize.max := by omega
  unfold sim.schedule.references_perframe
  rw [vec_push_ok _ _ (by simp; omega)]
  simp only [bind_ok]
  rw [show sim.schedule.references_perframe_loop ft (vpush (alloc.vec.Vec.new F64) r0 (by simp; omega)) r0 0#usize
      = ok (l1, last) by unfold sim.schedule.references_perframe_loop; exact hl]
  simp only [float.F64.lt, bind_ok]
  unfold s2_perframe
  have e2 : (abs ft : _root_.Array F64) = ft.val.toArray := by simp [abs]
  have e3 : (abs ft : _root_.Array F64).foldl s2_pfStep (#[r0], r0) = ft.val.foldl s2_pfStep (#[r0], r0) := by
    simp [abs]
  rw [e3]
  simp only at hfold
  rw [← e] at hfold
  simp only [Prod.mk.injEq] at hfold
  obtain ⟨h1, h2⟩ := hfold
  dsimp only
  rw [h2]
  by_cases hc : last < end_t
  · refine ⟨vpush l1 end_t hp, by simp [hc, vec_push_ok _ _ hp], ?_⟩
    simp only [hc, ite_true]
    apply _root_.Array.toList_inj.mp; simp [abs, h1]
  · refine ⟨l1, by simp [hc], ?_⟩
    simp only [hc, ite_false]
    apply _root_.Array.toList_inj.mp; simp [abs, h1]

/-- the `.dense1ms` `while cur < end && fuel > 0` loop (structural on the fuel; state `(l, cur, fuel)`) -/
def s2_dense (endT : F64) : Nat → _root_.Array F64 → F64 → _root_.Array F64 × F64 × Nat
  | 0, l, cur => (l, cur, 0)
  | n + 1, l, cur => if cur < endT then s2_dense endT n (l.push (F64.floor cur + 1)) (F64.floor cur + 1) else (l, cur, n + 1)

theorem s2_dense_loop (endT : F64) (F : Unit → _root_.Array F64 × F64 × Nat → Except String (ForInStep (_root_.Array F64 × F64 × Nat)))
    (hF : ∀ l cur n, F () (l, cur, n) = if (decide (cur < endT) && decide (n > 0)) = true then
              pure (ForInStep.yield (l.push (cur.floor + 1), cur.floor + 1, n - 1))
            else pure (ForInStep.done (l, cur, n))) :
    ∀ n l cur, (forIn Lean.Loop.mk (l, cur, n) F : Except String _) = .ok (s2_dense endT n l cur) := by
  intro n
  induction n with
  | zero =>
    intro l cur
    show Lean.Loop.forIn _ _ _ = _
    rw [Lean.Loop.forIn_eq_of_monadTail, hF]
    simp [s2_dense, pure, Except.pure, Bind.bind, Except.bind]
  | succ n ih =>
    intro l cur
    show Lean.Loop.forIn _ _ _ = _
    rw [Lean.Loop.forIn_eq_of_monadTail, hF]
    by_cases h : cur < endT
    · simp only [h, decide_true, gt_iff_lt, Nat.zero_lt_succ, Bool.and_self, ite_true, Nat.add_sub_cancel, s2_dense]
      exact ih _ _
    · simp [h, s2_dense, pure, Except.pure, Bind.bind, Except.bind]

theorem s2_references_dense (r0 endT : F64) (ft : _root_.Array F64) :
    OsuModel.Sim.references .dense1ms r0 endT ft =
      (let p := s2_dense endT 100000000 #[r0] r0
       if p.2.1 < endT then .error "schedule: dense reference list exceeds 1e8 entries" else .ok p.1) := by
  unfold OsuModel.Sim.references
  dsimp only
  rw [s2_dense_loop endT _ (fun l cur n => rfl)]
  simp only [Bind.bind, Except.bind]
  by_cases h : (s2_dense endT 100000000 #[r0] r0).2.1 < endT
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]; rfl

theorem s2_dense_rust (end_t : F64) : ∀ (n : Nat) (fuel : U32) (l : alloc.vec.Vec F64) (cur : F64),
    fuel.val = n → l.val.length + n < Usize.max →
    ∃ l', loop (fun x => sim.schedule.references_dense1ms_loop.body end_t x.1 x.2.1 x.2.2) (l, cur, fuel) =
      ok (l', (s2_dense end_t n l.val.toArray cur).2.1) ∧
      l'.val.toArray = (s2_dense end_t n l.val.toArray cur).1 := by
  intro n
  induction n with
  | zero =>
    intro fuel l cur hf hb
    refine ⟨l, ?_, by simp [s2_dense]⟩
    rw [loop_unfold]
    have : ¬ (fuel > 0#u32) := by simp [hf]
    by_cases h : cur < end_t <;> simp [sim.schedule.references_dense1ms_loop.body, float.F64.lt, h, this, s2_dense]
  | succ n ih =>
    intro fuel l cur hf hb
    by_cases h : cur < end_t
    · have hp : fuel > 0#u32 := by simp [hf]
      obtain ⟨f1, hf1, hf1v⟩ := u32_sub_one fuel (by omega)
      have hl : l.val.length < Usize.max := by omega
      obtain ⟨l', hl', he⟩ := ih f1 (vpush l (F64.floor cur + 1) hl) (F64.floor cur + 1) (by omega) (by simp; omega)
      refine ⟨l', ?_, ?_⟩
      · have hb : sim.schedule.references_dense1ms_loop.body end_t l cur fuel =
            ok (.cont (vpush l (F64.floor cur + 1) hl, F64.floor cur + 1, f1)) := by
          simp only [sim.schedule.references_dense1ms_loop.body, float.F64.lt, h, decide_true, ite_true, hp, hf1,
            float.F64.floor, s2_sched_F64_ONE, float.F64.add, vec_push_ok _ _ hl, bind_ok]
        rw [loop_unfold]
        simp only [hb, bind_ok]
        simp only [s2_dense, h, ite_true]
        rw [hl']; simp
      · simp only [s2_dense, h, ite_true]; simpa using he
    · refine ⟨l, ?_, by simp [s2_dense, h]⟩
      rw [loop_unfold]
      simp [sim.schedule.references_dense1ms_loop.body, float.F64.lt, h, s2_dense]

theorem sim.schedule.references_dense1ms_refines (h64 : System.Platform.numBits = 64) (r0 end_t : F64) (ft : _root_.Array F64) :
    ∃ r, sim.schedule.references_dense1ms r0 end_t = ok r ∧
      s2_rel abs (OsuModel.Sim.references .dense1ms r0 end_t ft) r := by
  have hU := usize_max_64 h64
  have h0 : (alloc.vec.Vec.new F64).val.length < Usize.max := by simp; omega
  obtain ⟨l', hl, he⟩ := s2_dense_rust end_t 100000000 100000000#u32 (vpush (alloc.vec.Vec.new F64) r0 h0) r0 rfl
    (by simp; omega)
  unfold sim.schedule.references_dense1ms
  rw [vec_push_ok _ _ h0]
  simp only [bind_ok]
  rw [show sim.schedule.references_dense1ms_loop end_t (vpush (alloc.vec.Vec.new F64) r0 h0) r0 100000000#u32 = _ by
    unfold sim.schedule.references_dense1ms_loop; exact hl]
  rw [s2_references_dense]
  have e : (vpush (alloc.vec.Vec.new F64) r0 h0).val.toArray = #[r0] := by simp
  rw [e] at he
  simp only [e, float.F64.lt, bind_ok]
  by_cases hc : (s2_dense end_t 100000000 #[r0] r0).2.1 < end_t
  · simp [hc, s2_rel]
  · simp [hc, s2_rel, abs, ← he]

def s2_kindS : sim.schedule.ScheduleKind → OsuModel.Sim.ScheduleKind
  | .Catchup => .catchup | .Perframe => .perframe | .Dense1ms => .dense1ms
instance s2_absSchedKind : AbsTo sim.schedule.ScheduleKind OsuModel.Sim.ScheduleKind := ⟨s2_kindS⟩

theorem sim.schedule.references_refines (h64 : System.Platform.numBits = 64) (kind : sim.schedule.ScheduleKind)
    (r0 end_t : F64) (ft : Slice F64) (hn : ft.val.length + 2 ≤ Usize.max) :
    ∃ r, sim.schedule.references kind r0 end_t ft = ok r ∧
      s2_rel abs (OsuModel.Sim.references (abs kind) r0 end_t (abs ft)) r := by
  have hU := usize_max_64 h64
  cases kind
  · have h0 : (alloc.vec.Vec.new F64).val.length < Usize.max := by simp; omega
    have h1 : (vpush (alloc.vec.Vec.new F64) r0 h0).val.length < Usize.max := by simp; omega
    refine ⟨.Ok (vpush (vpush (alloc.vec.Vec.new F64) r0 h0) (F64.max r0 end_t) h1), ?_, ?_⟩
    · simp only [sim.schedule.references, vec_push_ok _ _ h0, net.max_refines, vec_push_ok _ _ h1, bind_ok]
    · simp [s2_rel, abs, s2_kindS, OsuModel.Sim.references, pure, Except.pure]
  · obtain ⟨r, hr, er⟩ := sim.schedule.references_perframe_refines r0 end_t ft hn
    refine ⟨.Ok r, by simp only [sim.schedule.references, hr, bind_ok], ?_⟩
    simp [s2_rel, abs, s2_kindS, s2_references_perframe]
    simpa [abs] using er.symm
  · obtain ⟨r, hr, er⟩ := sim.schedule.references_dense1ms_refines h64 r0 end_t (abs ft)
    exact ⟨r, by simpa [sim.schedule.references] using hr, er⟩

def s2_fscRel (frames : Slice F64) (gst r : F64) (st : schedule.SimState) :
    core.result.Result schedule.SimState sim.err.SimErr → Prop
  | .Ok st' => s2_stepOk frames.val.toArray gst r (toT st) = true ∧ toT st' = stepT frames.val.toArray gst r (toT st)
  | .Err _ => s2_stepOk frames.val.toArray gst r (toT st) = false

set_option maxHeartbeats 4000000 in
theorem sim.schedule.fsc_step_refines (h64 : System.Platform.numBits = 64) (st : schedule.SimState) (r : F64)
    (frames : Slice F64) (gst : F64) (hidx : -2^61 ≤ st.idx.val ∧ st.idx.val ≤ 2^61) :
    ∃ res, sim.schedule.fsc_step st r frames gst = ok res ∧ s2_fscRel frames gst r st res := by
  obtain ⟨i1, hi1, hi1v⟩ := i64_add_one st.idx (by omega) (by omega)
  obtain ⟨i2, hi2, hi2v⟩ := i64_add_one i1 (by omega) (by omega)
  obtain ⟨d, hd, hdv⟩ := i64_sub_one st.idx (by omega) (by omega)
  obtain ⟨d1, hd1, hd1v⟩ := i64_add_one d (by omega) (by omega)
  have f0 := schedule.frame_time_refines h64 frames st.idx (by omega)
  have f1 := schedule.frame_time_refines h64 frames i1 (by omega)
  have f2 := schedule.frame_time_refines h64 frames i2 (by omega)
  have f3 := schedule.frame_time_refines h64 frames d (by omega)
  have f4 := schedule.frame_time_refines h64 frames d1 (by omega)
  rw [hi2v] at f2; rw [hi1v] at f1 f2; rw [hd1v] at f4; rw [hdv] at f3 f4
  unfold sim.schedule.fsc_step
  simp only [hi1, hi2, hd, hd1, f0, f1, f2, f3, f4, CATCHUP_eq, SIXTY_eq, net.min_refines, net.max_refines,
    net.mathops.f64_clamp_refines, float.F64.lt, float.F64.le, float.F64.eq, float.F64.sub, float.F64.add,
    float.F64.abs, bind_tc_ok, bind_ok, s2_fscRel, toT, stepT, s2_stepOk, propose]
  have hlen : (Slice.len frames = 0#usize) ↔ frames.val.length = 0 := by
    rw [UScalar.eq_equiv]; simp
  by_cases hfirst : st.first = true
  swap
  · simp only [hfirst, Bool.false_eq_true, ite_false, decide_eq_true_eq]
    by_cases h1 : st.manual < gst
    · simp only [h1, ite_true, decide_true, bind_tc_ok, bind_ok]
      repeat' split
      all_goals simp_all [exceptI]
    · simp only [h1, ite_false, decide_false, Bool.false_eq_true]
      by_cases h2 : catchupThreshold < F64.abs (st.manual - r)
      · simp only [h2, ite_true, decide_true]
        by_cases h3 : st.manual < r
        · simp only [h3, ite_true, decide_true, bind_tc_ok, bind_ok]
          repeat' split
          all_goals simp_all [exceptI]
        · simp only [h3, ite_false, decide_false, Bool.false_eq_true, bind_tc_ok, bind_ok]
          repeat' split
          all_goals simp_all [exceptI]
      · simp only [h2, ite_false, decide_false, Bool.false_eq_true, bind_tc_ok, bind_ok]
        repeat' split
        all_goals simp_all [exceptI]
  · simp only [hfirst, ite_true, bind_tc_ok, bind_ok]
    repeat' split
    all_goals simp_all [exceptI]

/-- `s2_refO` with an arbitrary fuel `n` -/
def s2_refN (frames : _root_.Array F64) (gst r : F64) (n : Nat) (s : S2St) : Option S2St :=
  match s2_innerO frames gst r n s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2 with
  | none => none
  | some o => if o.2.2.2.2.2 == 0 then none else some (o.1, o.2.1, o.2.2.1, o.2.2.2.1, o.2.2.2.2.1)

def s2_stS (steps : alloc.vec.Vec schedule.Step) (st : schedule.SimState) : S2St :=
  ((steps.val.map stepSpec).toArray, toT st)

def s2_idxOk (steps : alloc.vec.Vec schedule.Step) (st : schedule.SimState) : Prop :=
  (if st.idx.val < 0 then -st.idx.val else st.idx.val) ≤ 1 + steps.val.length

/-- relation of `simulate_ref`'s result to the spec model -/
def s2_refRel (o : Option S2St) (n0 : Nat)
    (x : core.result.Result schedule.SimState sim.err.SimErr × alloc.vec.Vec schedule.Step) : Prop :=
  match o with
  | none => ∃ e, x.1 = .Err e
  | some s => ∃ st', x.1 = .Ok st' ∧ s2_stS x.2 st' = s ∧ s2_idxOk x.2 st' ∧ x.2.val.length ≤ n0

theorem s2_refN_succ (frames : _root_.Array F64) (gst r : F64) (n : Nat) (S : _root_.Array Step)
    (s : Bool × F64 × Int × F64) :
    s2_refN frames gst r (n + 1) (S, s) =
      if s2_stepOk frames gst r s = true then
        (let s' := stepT frames gst r s
         let S' := S.push (Step.mk s'.2.1 s'.2.2.1)
         if (s'.2.2.2 == r) = true then (if n = 0 then none else some (S', s'))
         else s2_refN frames gst r n (S', s'))
      else none := by
  obtain ⟨a, b, c, d⟩ := s
  unfold s2_refN
  simp only [s2_innerO]
  by_cases h1 : s2_stepOk frames gst r (a, b, c, d) = true
  · rw [if_pos h1, if_pos h1]
    by_cases h2 : ((stepT frames gst r (a, b, c, d)).2.2.2 == r) = true
    · rw [if_pos h2, if_pos h2]; by_cases hn : n = 0 <;> simp [hn]
    · rw [if_neg h2, if_neg h2]
  · rw [if_neg h1, if_neg h1]

theorem s2_simulate_ref_loop (h64 : System.Platform.numBits = 64) (frames : Slice F64) (gst r : F64) :
    ∀ (n : Nat) (fuel : U32) (steps : alloc.vec.Vec schedule.Step) (st : schedule.SimState),
      fuel.val = n → s2_idxOk steps st → steps.val.length + n + 2 < 2^61 →
      ∃ x, sim.schedule.simulate_ref_loop steps r frames gst st fuel false = ok x ∧
        s2_refRel (s2_refN frames.val.toArray gst r n (s2_stS steps st)) (steps.val.length + n) x := by
  have hU := usize_max_64 h64
  intro n
  induction n with
  | zero =>
    intro fuel steps st hf hinv hb
    have : ¬ (fuel > 0#u32) := by simp [hf]
    have h0 : fuel = 0#u32 := by scalar_tac
    refine ⟨(.Err sim.err.SimErr.StepFuel, steps), ?_, ?_⟩
    · unfold sim.schedule.simulate_ref_loop; rw [loop_unfold]
      simp [sim.schedule.simulate_ref_loop.body, this, h0]
    · simp [s2_refRel, s2_refN, s2_innerO]
  | succ n ih =>
    intro fuel steps st hf hinv hb
    have hpos : fuel > 0#u32 := by simp [hf]
    obtain ⟨fuel1, hf1, hf1v⟩ := u32_sub_one fuel (by omega)
    obtain ⟨res, hres, hrel⟩ := sim.schedule.fsc_step_refines h64 st r frames gst
      (by unfold s2_idxOk at hinv; split at hinv <;> omega)
    have hst : toT st = (s2_stS steps st).2 := rfl
    cases res with
    | Err e =>
      simp only [s2_fscRel] at hrel
      refine ⟨(.Err e, steps), ?_, ?_⟩
      · unfold sim.schedule.simulate_ref_loop; rw [loop_unfold]
        simp [sim.schedule.simulate_ref_loop.body, hpos, hf1, hres, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · simp [s2_refRel, s2_refN, s2_innerO, s2_stS, hrel]
    | Ok st' =>
      simp only [s2_fscRel] at hrel
      obtain ⟨hok, ht⟩ := hrel
      have hp : steps.val.length < Usize.max := by omega
      let stp : schedule.Step := { time := st'.manual, frame_index := st'.idx }
      have hidx := stepT_idx frames.val.toArray gst r (toT st)
      rw [← ht] at hidx
      simp only [toT] at hidx
      have hinv' : s2_idxOk (vpush steps stp hp) st' := by
        unfold s2_idxOk at hinv ⊢; simp only [vpush_val, List.length_append, List.length_singleton]
        split at hinv <;> split <;> omega
      have hpushS : ((steps.val.map stepSpec).toArray).push (Step.mk (stepT frames.val.toArray gst r (toT st)).2.1
          (stepT frames.val.toArray gst r (toT st)).2.2.1) = ((vpush steps stp hp).val.map stepSpec).toArray := by
        rw [← ht]; simp [stepSpec, stp, toT]
      have hok' : s2_stepOk frames.val.toArray gst r (st.first, st.manual, st.idx.val, st.handler_time) = true := hok
      have hS : stepT frames.val.toArray gst r (st.first, st.manual, st.idx.val, st.handler_time) =
          (st'.first, st'.manual, st'.idx.val, st'.handler_time) := ht.symm
      have hpushS' : ((steps.val.map stepSpec).toArray).push (Step.mk st'.manual st'.idx.val) =
          ((vpush steps stp hp).val.map stepSpec).toArray := by simp [stepSpec, stp]
      have hspec : s2_refN frames.val.toArray gst r (n + 1) (s2_stS steps st) =
          if (st'.handler_time == r) = true then
            (if n = 0 then none else some (s2_stS (vpush steps stp hp) st'))
          else s2_refN frames.val.toArray gst r n (s2_stS (vpush steps stp hp) st') := by
        rw [s2_refN_succ]
        simp only [s2_stS, toT] at hok' ⊢
        simp only [hok', ite_true, hS, hpushS']
      have hb1 : sim.schedule.simulate_ref_loop.body r frames gst steps st fuel false =
          ok (.cont (vpush steps stp hp, st', fuel1, (st'.handler_time == r))) := by
        simp only [sim.schedule.simulate_ref_loop.body, hpos, ite_true, Bool.false_eq_true, ite_false, hf1, hres,
          core.result.Result.Insts.CoreOpsTry.branch, bind_ok, vec_push_ok _ _ hp, float.F64.eq]
        cases (st'.handler_time == r) <;> rfl
      by_cases hbrk : (st'.handler_time == r) = true
      · rw [hspec, if_pos hbrk]
        by_cases hn0 : n = 0
        · subst hn0
          have hz : fuel1 = 0#u32 := by scalar_tac
          refine ⟨(.Err sim.err.SimErr.StepFuel, vpush steps stp hp), ?_, ?_⟩
          · unfold sim.schedule.simulate_ref_loop; rw [loop_unfold]; dsimp only; rw [hb1, hbrk]
            simp only [bind_ok]; rw [loop_unfold]
            simp [sim.schedule.simulate_ref_loop.body, hz]
          · simp [s2_refRel]
        · have hpos1 : fuel1 > 0#u32 := by scalar_tac
          have hnz : ¬ (fuel1 = 0#u32) := by scalar_tac
          refine ⟨(.Ok st', vpush steps stp hp), ?_, ?_⟩
          · unfold sim.schedule.simulate_ref_loop; rw [loop_unfold]; dsimp only; rw [hb1, hbrk]
            simp only [bind_ok]; rw [loop_unfold]
            simp [sim.schedule.simulate_ref_loop.body, hpos1, hnz]
          · simp only [hn0, ite_false, s2_refRel]
            exact ⟨st', rfl, rfl, hinv', by simp only [vpush_val, List.length_append, List.length_singleton]; omega⟩
      · have hbrk' : (st'.handler_time == r) = false := by cases h : (st'.handler_time == r) <;> simp_all
        rw [hspec, if_neg hbrk]
        obtain ⟨x, hx, hxr⟩ := ih fuel1 (vpush steps stp hp) st' (by omega) hinv' (by simp; omega)
        refine ⟨x, ?_, ?_⟩
        · unfold sim.schedule.simulate_ref_loop; rw [loop_unfold]; dsimp only; rw [hb1, hbrk']
          simp only [bind_ok]
          unfold sim.schedule.simulate_ref_loop at hx; exact hx
        · simp only [vpush_val, List.length_append, List.length_singleton] at hxr
          rw [show steps.val.length + (n + 1) = steps.val.length + 1 + n by omega]; exact hxr

def s2_outRel (o : Option S2St) (x : core.result.Result (alloc.vec.Vec schedule.Step) sim.err.SimErr) : Prop :=
  match o, x with
  | none, .Err _ => True
  | some s, .Ok v => (v.val.map stepSpec).toArray = s.1
  | _, _ => False

theorem s2_refO_eq (frames : _root_.Array F64) (gst : F64) (s : S2St) (r : F64) :
    s2_refO frames gst s r = s2_refN frames gst r FUEL s := rfl

theorem s2_simulate_steps_loop (h64 : System.Platform.numBits = 64) (refs frames : Slice F64) (gst : F64) :
    ∀ (k : Nat) (ri : Usize) (steps : alloc.vec.Vec schedule.Step) (st : schedule.SimState),
      refs.val.length - ri.val = k → ri.val ≤ refs.val.length → s2_idxOk steps st →
      steps.val.length + (refs.val.length - ri.val) * FUEL + 4 < 2^61 →
      ∃ x, sim.schedule.simulate_steps_loop refs frames gst steps st ri = ok x ∧
        s2_outRel (s2_outerO frames.val.toArray gst (refs.val.drop ri.val) (s2_stS steps st)) x := by
  intro k
  induction k with
  | zero =>
    intro ri steps st hk hri hinv hb
    have hge : ¬ (ri < Slice.len refs) := by simp only [UScalar.lt_equiv, Slice.len_val, Slice.length]; omega
    refine ⟨.Ok steps, ?_, ?_⟩
    · unfold sim.schedule.simulate_steps_loop; rw [loop_unfold]
      simp [sim.schedule.simulate_steps_loop.body, hge]
    · have : refs.val.drop ri.val = [] := by simp; omega
      simp [this, s2_outerO, s2_outRel, s2_stS]
  | succ k ih =>
    intro ri steps st hk hri hinv hb
    have hlt : ri.val < refs.val.length := by omega
    have hlt' : ri < Slice.len refs := by simp only [UScalar.lt_equiv, Slice.len_val, Slice.length]; omega
    obtain ⟨x, hx, hxr⟩ := s2_simulate_ref_loop h64 frames gst (refs.val[ri.val]'hlt) FUEL schedule.FUEL steps st
      FUEL_val hinv (by rw [FUEL_lit] at *; have : 1 ≤ refs.val.length - ri.val := by omega
                        have : steps.val.length + 100000000 ≤ steps.val.length + (refs.val.length - ri.val) * 100000000 := by
                          have := Nat.mul_le_mul_right 100000000 this; omega
                        omega)
    have hU := usize_max_64 h64
    obtain ⟨ri1, hri1, hri1v⟩ := usize_add_one ri (by have := Slice.length_ineq refs; omega)
    have hdrop : refs.val.drop ri.val = (refs.val[ri.val]'hlt) :: refs.val.drop ri1.val := by
      rw [hri1v]; exact List.drop_eq_getElem_cons hlt
    rw [hdrop]
    simp only [s2_outerO, s2_refO_eq]
    obtain ⟨res, steps'⟩ := x
    cases ho : s2_refN frames.val.toArray gst (refs.val[ri.val]'hlt) FUEL (s2_stS steps st) with
    | none =>
      simp only [ho] at hxr
      obtain ⟨e, he⟩ := hxr
      simp only at he; subst he
      refine ⟨.Err e, ?_, by simp [s2_outRel]⟩
      unfold sim.schedule.simulate_steps_loop; rw [loop_unfold]
      simp [sim.schedule.simulate_steps_loop.body, hlt', slice_index_ok _ _ hlt, hx,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | some s' =>
      simp only [ho] at hxr
      obtain ⟨st', he, hs, hinv', hlen⟩ := hxr
      simp only at he hs hinv' hlen; subst he
      obtain ⟨v, hv, hvr⟩ := ih ri1 steps' st' (by omega) (by omega) hinv'
        (by rw [FUEL_lit] at *
            have e : refs.val.length - ri.val = (refs.val.length - ri1.val) + 1 := by omega
            rw [e] at hb; rw [Nat.add_mul] at hb; omega)
      refine ⟨v, ?_, ?_⟩
      · have hb1 : sim.schedule.simulate_steps_loop.body refs frames gst steps st ri = ok (.cont (steps', st', ri1)) := by
          simp [sim.schedule.simulate_steps_loop.body, hlt', slice_index_ok _ _ hlt, hx, hri1,
            core.result.Result.Insts.CoreOpsTry.branch]
        unfold sim.schedule.simulate_steps_loop; rw [loop_unfold]; dsimp only; rw [hb1]; simp only [bind_ok]
        unfold sim.schedule.simulate_steps_loop at hv; exact hv
      · simp only; rw [← hs]; exact hvr

theorem sim.schedule.simulate_steps_refines (h64 : System.Platform.numBits = 64) (refs frames : Slice F64) (gst : F64)
    (hsz : refs.val.length * 100000000 + 4 < 2^61) :
    ∃ r, sim.schedule.simulate_steps refs frames gst = ok r ∧
      s2_rel abs (simulateSteps (abs refs) (abs frames) gst) r := by
  obtain ⟨x, hx, hxr⟩ := s2_simulate_steps_loop h64 refs frames gst refs.val.length 0#usize
    (alloc.vec.Vec.new schedule.Step) { first := true, manual := 0, idx := (-1)#i64, handler_time := F64.negInf }
    (by simp) (by simp) (by simp [s2_idxOk]) (by rw [FUEL_lit]; simp; omega)
  refine ⟨x, ?_, ?_⟩
  · simp only [sim.schedule.simulate_steps, K0_sched_eq, NEG_INF_eq, bind_ok]; exact hx
  · have e := s2_simulateSteps_eo refs.val.toArray frames.val.toArray gst
    have ea : (abs refs : _root_.Array F64) = refs.val.toArray := by simp [abs]
    have eb : (abs frames : _root_.Array F64) = frames.val.toArray := by simp [abs]
    rw [ea, eb]
    have ei : s2_stS (alloc.vec.Vec.new schedule.Step)
        { first := true, manual := 0, idx := (-1)#i64, handler_time := F64.negInf } = (#[], true, 0, -1, F64.negInf) := by
      simp [s2_stS, toT]
    simp only [ei, show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at hxr
    revert e hxr
    cases simulateSteps refs.val.toArray frames.val.toArray gst with
    | error m =>
      intro e hxr
      simp only [s2_eo] at e
      cases ho : s2_outerO frames.val.toArray gst refs.val (#[], true, 0, -1, F64.negInf) with
      | none => rw [ho] at hxr; cases x <;> simp_all [s2_outRel, s2_rel]
      | some s => rw [ho] at e; simp at e
    | ok s =>
      intro e hxr
      simp only [s2_eo] at e
      cases ho : s2_outerO frames.val.toArray gst refs.val (#[], true, 0, -1, F64.negInf) with
      | none => rw [ho] at e; simp at e
      | some s' =>
        rw [ho] at e hxr; simp at e
        cases x with
        | Err _ => simp [s2_outRel] at hxr
        | Ok a => simp only [s2_outRel] at hxr; simp only [s2_rel]; rw [e, ← hxr]; rfl

theorem s2_dense_size (e : F64) : ∀ n (l : _root_.Array F64) c, (s2_dense e n l c).1.size ≤ l.size + n := by
  intro n
  induction n with
  | zero => intro l c; simp [s2_dense]
  | succ n ih =>
    intro l c
    simp only [s2_dense]
    split
    · have := ih (l.push (F64.floor c + 1)) (F64.floor c + 1); simp at this; omega
    · simp

theorem s2_references_size (k : ScheduleKind) (r0 e : F64) (ft a : _root_.Array F64)
    (h : references k r0 e ft = .ok a) : a.size ≤ ft.size + 100000002 := by
  cases k
  · simp [references, pure, Except.pure] at h; subst h; simp
  · rw [s2_references_perframe] at h; cases h
    unfold s2_perframe
    have h1 := s2_pf_foldl ft.toList #[r0] r0
    have h2 := s2_pfL_len ft.toList [r0] r0
    have e3 : ft.foldl s2_pfStep (#[r0], r0) = ft.toList.foldl s2_pfStep (#[r0], r0) := by simp
    rw [e3]
    simp only at h1
    have hsz : (List.foldl s2_pfStep (#[r0], r0) ft.toList).1.size = (List.foldl s2_pfStepL ([r0], r0) ft.toList).1.length := by
      rw [← Array.length_toList]; exact congrArg (fun p => p.1.length) h1
    have h2' : (List.foldl s2_pfStepL ([r0], r0) ft.toList).1.length ≤ 1 + ft.size := by
      have := h2; simp only [List.length_singleton, Array.length_toList] at this; omega
    dsimp only; split
    · simp only [Array.size_push]; omega
    · omega
  · rw [s2_references_dense] at h
    have := s2_dense_size e 100000000 #[r0] r0
    simp only at h; split at h
    · cases h
    · cases h; simp at this; omega

theorem sim.schedule.steps_refines (h64 : System.Platform.numBits = 64) (kind : sim.schedule.ScheduleKind)
    (pb : sim.playable.Playable) (frames : Slice replay.frames.Frame) (hf : frames.val.length < 2^32) :
    ∃ r, sim.schedule.steps kind pb frames = ok r ∧
      s2_rel abs (OsuModel.Sim.steps (abs kind) (abs pb) (abs frames)) r := by
  have hU := usize_max_64 h64
  obtain ⟨ft, hft, eft⟩ := sim.schedule.frame_times_refines frames
  obtain ⟨rs, hrs, ers⟩ := sim.schedule.reference_start_refines pb
  obtain ⟨re, hre, ere⟩ := sim.schedule.reference_end_refines pb
  obtain ⟨gs, hgs, egs⟩ := sim.schedule.gameplay_start_time_refines pb
  have hftl : ft.val.length = frames.val.length := by
    have := congrArg _root_.Array.size eft; simp [abs] at this; omega
  obtain ⟨rr, hrr, err⟩ := sim.schedule.references_refines h64 kind rs re (alloc.vec.Vec.deref ft)
    (by simp [alloc.vec.Vec.deref, hftl]; omega)
  have eft' : (abs (alloc.vec.Vec.deref ft) : _root_.Array F64) = (abs frames : _root_.Array OsuModel.Replay.Frame).map (·.time) := by
    rw [eft]; simp [abs, alloc.vec.Vec.deref]
  rw [eft'] at err
  unfold OsuModel.Sim.steps
  simp only [ers, ere, egs] at err ⊢
  unfold sim.schedule.steps
  simp only [hft, hrs, hre, hrr, bind_ok]
  cases hR : references (abs kind) rs re ((abs frames : _root_.Array OsuModel.Replay.Frame).map (·.time)) with
  | error m =>
    rw [hR] at err
    cases rr with
    | Ok v => exact absurd err (by simp [s2_rel])
    | Err e =>
      refine ⟨.Err e, ?_, ?_⟩
      · simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · simp [s2_rel, Bind.bind, Except.bind, hR]
  | ok a =>
    rw [hR] at err
    cases rr with
    | Err e => exact absurd err (by simp [s2_rel])
    | Ok v =>
      simp only [s2_rel] at err
      have hsz := s2_references_size _ _ _ _ _ hR
      have hvl : v.val.length = a.size := by rw [← err]; simp [abs]
      have hal : ((abs frames : _root_.Array OsuModel.Replay.Frame).map (·.time)).size = frames.val.length := by simp [abs]
      obtain ⟨w, hw, ew⟩ := sim.schedule.simulate_steps_refines h64 (alloc.vec.Vec.deref v) (alloc.vec.Vec.deref ft) gs
        (by simp [alloc.vec.Vec.deref]; omega)
      refine ⟨w, ?_, ?_⟩
      · simp [core.result.Result.Insts.CoreOpsTry.branch, hgs, hw]
      · have ea : (abs (alloc.vec.Vec.deref v) : _root_.Array F64) = a := by rw [← err]; simp [abs, alloc.vec.Vec.deref]
        rw [ea, eft'] at ew
        simpa [Bind.bind, Except.bind, hR] using ew

/-- one reference of `simulateSteps` (the spec's inner `while` + fuel check, `s2_refO`) -/
theorem sim.schedule.simulate_ref_refines (h64 : System.Platform.numBits = 64) (steps : alloc.vec.Vec schedule.Step)
    (st0 : schedule.SimState) (r : F64) (frames : Slice F64) (gst : F64) (hinv : s2_idxOk steps st0)
    (hb : steps.val.length + FUEL + 2 < 2^61) :
    ∃ x, sim.schedule.simulate_ref steps st0 r frames gst = ok x ∧
      s2_refRel (s2_refO frames.val.toArray gst (s2_stS steps st0) r) (steps.val.length + FUEL) x :=
  s2_simulate_ref_loop h64 frames gst r FUEL schedule.FUEL steps st0 FUEL_val hinv hb

@[step] theorem sim.schedule.gameplay_start_time_step (pb : sim.playable.Playable) :
    sim.schedule.gameplay_start_time pb ⦃ r => OsuModel.Sim.gameplayStartTime (abs pb) = abs r ⦄ :=
  spec_of_ex (sim.schedule.gameplay_start_time_refines pb)
@[step] theorem sim.schedule.reference_start_step (pb : sim.playable.Playable) :
    sim.schedule.reference_start pb ⦃ r => OsuModel.Sim.referenceStart (abs pb) = abs r ⦄ :=
  spec_of_ex (sim.schedule.reference_start_refines pb)
@[step] theorem sim.schedule.reference_end_step (pb : sim.playable.Playable) :
    sim.schedule.reference_end pb ⦃ r => OsuModel.Sim.referenceEnd (abs pb) = abs r ⦄ :=
  spec_of_ex (sim.schedule.reference_end_refines pb)
@[step] theorem sim.schedule.frame_times_step (frames : Slice replay.frames.Frame) :
    sim.schedule.frame_times frames ⦃ r => (abs frames : _root_.Array OsuModel.Replay.Frame).map (·.time) = abs r ⦄ :=
  spec_of_ex (sim.schedule.frame_times_refines frames)
@[step] theorem sim.schedule.references_step (h64 : System.Platform.numBits = 64) (kind : sim.schedule.ScheduleKind)
    (r0 end_t : F64) (ft : Slice F64) (hn : ft.val.length + 2 ≤ Usize.max) :
    sim.schedule.references kind r0 end_t ft ⦃ r => s2_rel abs (OsuModel.Sim.references (abs kind) r0 end_t (abs ft)) r ⦄ :=
  spec_of_ex (sim.schedule.references_refines h64 kind r0 end_t ft hn)
@[step] theorem sim.schedule.simulate_steps_step (h64 : System.Platform.numBits = 64) (refs frames : Slice F64) (gst : F64)
    (hsz : refs.val.length * 100000000 + 4 < 2^61) :
    sim.schedule.simulate_steps refs frames gst ⦃ r => s2_rel abs (simulateSteps (abs refs) (abs frames) gst) r ⦄ :=
  spec_of_ex (sim.schedule.simulate_steps_refines h64 refs frames gst hsz)
@[step] theorem sim.schedule.steps_step (h64 : System.Platform.numBits = 64) (kind : sim.schedule.ScheduleKind)
    (pb : sim.playable.Playable) (frames : Slice replay.frames.Frame) (hf : frames.val.length < 2^32) :
    sim.schedule.steps kind pb frames ⦃ r => s2_rel abs (OsuModel.Sim.steps (abs kind) (abs pb) (abs frames)) r ⦄ :=
  spec_of_ex (sim.schedule.steps_refines h64 kind pb frames hf)

end OsuProofs
