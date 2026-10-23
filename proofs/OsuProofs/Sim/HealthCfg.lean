/-
`sim::scoring` health configuration (Rust) refines `OsuModel.Sim` Scoring: `no_drain_period` (the two scans of
`noDrainPeriods`: last end time ≤ break start / first start time ≥ break end), `no_drain_periods` (insertion via
`insert_period_sorted` = the spec's `stableSortBy … (·.1 < ·.1)`, `simSortL`).
-/
import OsuProofs.Sim.Periods
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem sim_id_forIn_last {α β} (l : List α) (init : β) (p : α → Prop) [DecidablePred p] (f : α → β) :
    forIn (m := Id) l init (fun o s => if p o then pure (ForInStep.yield (f o)) else pure (ForInStep.yield s)) =
      l.foldl (fun s o => if p o then f o else s) init := by
  induction l generalizing init with
  | nil => rfl
  | cons x t ih => simp only [List.forIn_cons, List.foldl_cons]; by_cases h : p x <;> simp [h, ih]

theorem sim_id_forIn_first {α β} (l : List α) (init : β) (p : α → Prop) [DecidablePred p] (f : α → β) :
    forIn (m := Id) l init (fun o s => if p o then pure (ForInStep.done (f o)) else pure (ForInStep.yield s)) =
      ((l.find? (fun o => decide (p o))).map f).getD init := by
  induction l generalizing init with
  | nil => rfl
  | cons x t ih => simp only [List.forIn_cons, List.find?_cons]; by_cases h : p x <;> simp [h, ih] <;> rfl

def simDMax : F64 := Float.ofBits 9218868437227405311
def simNDS (objs : _root_.Array OsuModel.Sim.TopObj) (bs : F64) : F64 :=
  objs.foldl (fun s o => if o.h.endTime ≤ bs then o.h.endTime else s) (-simDMax)
def simNDE (objs : _root_.Array OsuModel.Sim.TopObj) (be : F64) : F64 :=
  ((objs.find? (fun o => decide (be ≤ o.h.start))).map (·.h.start)).getD simDMax

theorem simS_noDrainPeriods (pb : OsuModel.Sim.Playable) :
    OsuModel.Sim.noDrainPeriods pb = OsuModel.Sim.stableSortBy
      (pb.breaks.toList.map (fun x => (simNDS pb.objects x.1, simNDE pb.objects x.2))).toArray
      (fun a b => decide (a.1 < b.1)) := by
  unfold OsuModel.Sim.noDrainPeriods
  simp only [Id.run, pure_bind, bind_pure_comp]
  simp only [← Array.forIn_toList, sim_id_forIn_last, sim_id_forIn_first, Array.foldl_toList, Array.find?_toList]
  have key : ∀ (L : List (F64 × F64)) (acc : _root_.Array (F64 × F64)),
      forIn (m := Id) L acc (fun x s => do
        let a ← (simNDS pb.objects x.1 : Id F64)
        (fun b => ForInStep.yield (s.push (a, b))) <$> (simNDE pb.objects x.2 : Id F64)) =
      acc ++ (L.map (fun x => (simNDS pb.objects x.1, simNDE pb.objects x.2))).toArray := by
    intro L; induction L with
    | nil => intro acc; simp; rfl
    | cons x t ih =>
      intro acc
      rw [List.forIn_cons]
      show forIn (m := Id) t (acc.push (simNDS pb.objects x.1, simNDE pb.objects x.2)) _ = _
      rw [ih]
      apply Array.toList_inj.mp
      simp only [Array.toList_append, Array.toList_push, List.toList_toArray, List.map_cons, List.append_assoc,
        List.singleton_append]
  have hS : ∀ bs, Array.foldl (fun s (o : OsuModel.Sim.TopObj) => if o.h.endTime ≤ bs then o.h.endTime else s)
      (-Float.ofBits 9218868437227405311) pb.objects = simNDS pb.objects bs := fun _ => rfl
  have hE : ∀ be, (Option.map (fun (o : OsuModel.Sim.TopObj) => o.h.start)
      (Array.find? (fun o => decide (be ≤ o.h.start)) pb.objects)).getD (Float.ofBits 9218868437227405311) =
      simNDE pb.objects be := fun _ => rfl
  simp only [hS, hE]
  have := key pb.breaks.toList #[]
  simp only [Array.empty_append] at this
  rw [key]
  simp only [Array.empty_append]
  rfl

theorem sim_scoring_F64_DMAX : sim.scoring.F64_DMAX = ok simDMax := by
  simp [sim.scoring.F64_DMAX, float.F64.from_bits, simDMax]

theorem sim_ndp_loop0 (pb : sim.playable.Playable) (bs : F64) :
    ∀ n (s : F64) (i : Usize), pb.objects.val.length - i.val = n → i.val ≤ pb.objects.val.length →
      sim.scoring.no_drain_period_loop0 pb bs s i = ok (pb.objects,
        (pb.objects.val.drop i.val).foldl (fun s o => if o.h.end_time ≤ bs then o.h.end_time else s) s) := by
  intro n
  induction n with
  | zero =>
    intro s i hn hi
    have hdn : pb.objects.val.drop i.val = [] := List.drop_of_length_le (by omega)
    unfold sim.scoring.no_drain_period_loop0; rw [loop_unfold]
    have : ¬ (i < alloc.vec.Vec.len pb.objects) := by rw [vec_lt_len_iff]; omega
    simp [sim.scoring.no_drain_period_loop0.body, this, hdn]
  | succ n ih =>
    intro s i hn hi
    have hlt : i.val < pb.objects.val.length := by omega
    have hlt' : i < alloc.vec.Vec.len pb.objects := by rw [vec_lt_len_iff]; exact hlt
    obtain ⟨i1, hi1, ei1⟩ := usize_add_one i (by have := pb.objects.property; omega)
    have IH := ih (if (pb.objects.val[i.val]'hlt).h.end_time ≤ bs then (pb.objects.val[i.val]'hlt).h.end_time else s)
      i1 (by omega) (by omega)
    unfold sim.scoring.no_drain_period_loop0; rw [loop_unfold]; dsimp only
    rw [show sim.scoring.no_drain_period_loop0.body pb bs s i = ok (.cont
        (if (pb.objects.val[i.val]'hlt).h.end_time ≤ bs then (pb.objects.val[i.val]'hlt).h.end_time else s, i1)) by
      by_cases hc : (pb.objects.val[i.val]'hlt).h.end_time ≤ bs <;>
        simp [sim.scoring.no_drain_period_loop0.body, hlt', vec_index_usize_ok _ _ hlt, float.F64.le, hc, hi1]]
    simp only [bind_ok]
    unfold sim.scoring.no_drain_period_loop0 at IH
    rw [IH, ei1, List.drop_eq_getElem_cons hlt, List.foldl_cons]

theorem sim_ndp_loop1 (v : alloc.vec.Vec sim.playable.TopObj) (be : F64) :
    ∀ n (e : F64) (k : Usize), v.val.length - k.val = n → k.val ≤ v.val.length →
      sim.scoring.no_drain_period_loop1 v be e k false =
        ok (((v.val.drop k.val).find? (fun o => decide (be ≤ o.h.start))).map (·.h.start) |>.getD e) := by
  intro n
  induction n with
  | zero =>
    intro e k hn hk
    have hdn : v.val.drop k.val = [] := List.drop_of_length_le (by omega)
    unfold sim.scoring.no_drain_period_loop1; rw [loop_unfold]
    have : ¬ (k < alloc.vec.Vec.len v) := by rw [vec_lt_len_iff]; omega
    simp [sim.scoring.no_drain_period_loop1.body, this, hdn]
  | succ n ih =>
    intro e k hn hk
    have hlt : k.val < v.val.length := by omega
    have hlt' : k < alloc.vec.Vec.len v := by rw [vec_lt_len_iff]; exact hlt
    obtain ⟨k1, hk1, ek1⟩ := usize_add_one k (by have := v.property; omega)
    unfold sim.scoring.no_drain_period_loop1; rw [loop_unfold]; dsimp only
    rw [List.drop_eq_getElem_cons hlt, List.find?_cons]
    by_cases hc : be ≤ (v.val[k.val]'hlt).h.start
    · rw [show sim.scoring.no_drain_period_loop1.body v be e k false = ok (.cont ((v.val[k.val]'hlt).h.start, k1, true)) by
        simp [sim.scoring.no_drain_period_loop1.body, hlt', vec_index_usize_ok _ _ hlt, float.F64.le, hc, hk1]]
      simp only [bind_ok, hc, decide_true]
      rw [loop_unfold]
      by_cases h2 : k1 < alloc.vec.Vec.len v <;> simp [sim.scoring.no_drain_period_loop1.body, h2]
    · rw [show sim.scoring.no_drain_period_loop1.body v be e k false = ok (.cont (e, k1, false)) by
        simp [sim.scoring.no_drain_period_loop1.body, hlt', vec_index_usize_ok _ _ hlt, float.F64.le, hc, hk1]]
      simp only [bind_ok, hc, decide_false]
      have IH := ih e k1 (by omega) (by omega)
      unfold sim.scoring.no_drain_period_loop1 at IH
      rw [IH, ek1]

theorem sim.scoring.no_drain_period_refines (tn) (pb : sim.playable.Playable) (bs be : F64) :
    ∃ p, sim.scoring.no_drain_period pb bs be = ok p ∧
      (simNDS (playableS tn pb).objects bs, simNDE (playableS tn pb).objects be) = simPP p := by
  refine ⟨⟨(pb.objects.val).foldl (fun s o => if o.h.end_time ≤ bs then o.h.end_time else s) (-simDMax),
    ((pb.objects.val.find? (fun o => decide (be ≤ o.h.start))).map (·.h.start)).getD simDMax⟩, ?_, ?_⟩
  · have h0 := sim_ndp_loop0 pb bs _ (-simDMax) 0#usize rfl (by simp)
    have h1 := sim_ndp_loop1 pb.objects be _ simDMax 0#usize rfl (by simp)
    simp only [List.drop_zero, show (0#usize : Usize).val = 0 from rfl] at h0 h1
    simp [sim.scoring.no_drain_period, sim_scoring_F64_DMAX, float.F64.neg, h0, h1]
  · simp only [simNDS, simNDE, playableS, simPP]
    simp [List.foldl_map, List.find?_map, Function.comp_def, topS, hobjS]; exact ⟨rfl, rfl⟩

def simNDStep (out : List (F64 × F64)) (x : F64 × F64) : List (F64 × F64) :=
  out.insertIdx (simInsPos simPLt out x out.length) x

theorem sim_ndps_loop (tn) (pb : sim.playable.Playable) :
    ∀ n (out : alloc.vec.Vec sim.playable.Period) (i : Usize), pb.breaks.val.length - i.val = n →
      i.val ≤ pb.breaks.val.length → out.val.length = i.val →
      ∃ w, sim.scoring.no_drain_periods_loop pb out i = ok w ∧
        w.val.map simPP = ((pb.breaks.val.drop i.val).map (fun b =>
          (simNDS (playableS tn pb).objects b.start, simNDE (playableS tn pb).objects b.«end»))).foldl simNDStep
          (out.val.map simPP) := by
  intro n
  induction n with
  | zero =>
    intro out i hn hi ho
    have hdn : pb.breaks.val.drop i.val = [] := List.drop_of_length_le (by omega)
    refine ⟨out, ?_, by simp [hdn]⟩
    unfold sim.scoring.no_drain_periods_loop; rw [loop_unfold]
    have : ¬ (i < alloc.vec.Vec.len pb.breaks) := by rw [vec_lt_len_iff]; omega
    simp [sim.scoring.no_drain_periods_loop.body, this]
  | succ n ih =>
    intro out i hn hi ho
    have hlt : i.val < pb.breaks.val.length := by omega
    have hlt' : i < alloc.vec.Vec.len pb.breaks := by rw [vec_lt_len_iff]; exact hlt
    have hmax := pb.breaks.property
    obtain ⟨i1, hi1, ei1⟩ := usize_add_one i (by omega)
    obtain ⟨p, hp, ep⟩ := sim.scoring.no_drain_period_refines tn pb (pb.breaks.val[i.val]'hlt).start
      (pb.breaks.val[i.val]'hlt).«end»
    obtain ⟨w1, hw1, ew1⟩ := sim.scoring.insert_period_sorted_refines out p (by omega)
    have hw1l : w1.val.length = i1.val := by
      have := congrArg List.length ew1; simp only [List.length_map, List.length_insertIdx] at this
      have hle := sim_simInsPos_le simPLt (out.val.map simPP) (simPP p) out.val.length
      rw [ei1, ← ho]; split at this <;> omega
    obtain ⟨w, hw, ew⟩ := ih w1 i1 (by omega) (by omega) hw1l
    refine ⟨w, ?_, ?_⟩
    · unfold sim.scoring.no_drain_periods_loop; rw [loop_unfold]; dsimp only
      rw [show sim.scoring.no_drain_periods_loop.body pb out i = ok (.cont (w1, i1)) by
        simp [sim.scoring.no_drain_periods_loop.body, hlt', vec_index_usize_ok _ _ hlt, hp, hw1, hi1]]
      simp only [bind_ok]
      unfold sim.scoring.no_drain_periods_loop at hw; exact hw
    · rw [ew, ew1, ei1, List.drop_eq_getElem_cons hlt, List.map_cons, List.foldl_cons, ep]
      rfl

theorem sim.scoring.no_drain_periods_refines (tn) (pb : sim.playable.Playable) :
    ∃ w, sim.scoring.no_drain_periods pb = ok w ∧
      OsuModel.Sim.noDrainPeriods (playableS tn pb) = (w.val.map simPP).toArray := by
  obtain ⟨w, hw, ew⟩ := sim_ndps_loop tn pb _ (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
  refine ⟨w, hw, ?_⟩
  rw [simS_noDrainPeriods, sim_stableSortBy_eq, ew]
  simp only [List.toList_toArray, show (0#usize : Usize).val = 0 from rfl, List.drop_zero, alloc.vec.Vec.new,
    List.map_nil]
  congr 1
  unfold simSortL
  simp only [playableS, List.map_map]
  have hb : (abs pb.breaks : _root_.Array (F64 × F64)).toList = pb.breaks.val.map (fun b => (b.start, b.«end»)) := by
    simp [abs]
  rw [hb, List.map_map]
  have h0 : (alloc.vec.Vec.new sim.playable.Period).val = [] := rfl
  simp only [h0, List.map_nil]
  rfl
end OsuProofs
