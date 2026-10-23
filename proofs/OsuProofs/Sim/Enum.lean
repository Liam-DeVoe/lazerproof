/-
`enumerateUpTo` (StartTimeOrderedHitPolicy.enumerateHitObjectsUpTo): spec evaluation as a list function of the alive
order (`simEnumL`), plus generic lemmas for `forIn`/`forIn'` loops in `SimM` whose bodies are state-preserving
(`simM_forIn_list_eval`, `simM_forIn'_range_pure`; steps unrolled with the shared `simForStep`).
-/
import OsuProofs.Sim.AliveSort
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result

namespace OsuProofs

section
open OsuModel.Net OsuModel.Sim

/-- one step of a `forIn` loop unrolled as a `foldr` (one shared matcher for all the loop lemmas) -/
def simForStep {α β} (g : α → β → ForInStep β) (x : α) (k : β → β) (acc : β) : β :=
  match g x acc with | .done c => c | .yield c => k c

/-- a `forIn'` over a list in `SimM` whose body is `pure`: evaluates like the `iterR` index loop. -/
theorem simM_forIn'_list_pure {β} (l : List Nat) (F : (j : Nat) → j ∈ l → β → SimM (ForInStep β))
    (g : Nat → β → ForInStep β) (hF : ∀ j h b, F j h b = pure (g j b)) (b : β) (C : Ctx) (S : St) :
    forIn' l b F C S = .ok (l.foldr (simForStep g) id b, S) := by
  induction l generalizing b with
  | nil => rfl
  | cons j t ih =>
    rw [List.forIn'_cons, hF]
    simp only [simM_bind, simM_pure, Except.bind, List.foldr_cons, simForStep]
    cases g j b with
    | done c => rfl
    | yield c => exact ih (fun a' m b => F a' (List.mem_cons_of_mem _ m) b) (fun j h b => hF j _ b) c

theorem sim_foldr_range'_iterR {β} (g : Nat → β → ForInStep β) :
    ∀ n k b, (List.range' k n).foldr (simForStep g) id b =
      iterR g k n b := by
  intro n; induction n with
  | zero => intro k b; rfl
  | succ n ih =>
    intro k b
    simp only [List.range'_succ, List.foldr_cons, iterR, simForStep]
    cases g k b with
    | done c => rfl
    | yield c => exact ih (k + 1) c

theorem simM_forIn'_range_pure {β} (n : Nat) (F : (j : Nat) → j ∈ [:n] → β → SimM (ForInStep β))
    (g : Nat → β → ForInStep β) (hF : ∀ j h b, F j h b = pure (g j b)) (b : β) (C : Ctx) (S : St) :
    forIn' [:n] b F C S = .ok (iterR g 0 n b, S) := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  rw [simM_forIn'_list_pure _ _ g (fun j h b => hF j _ b)]
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  exact congrArg (fun x => Except.ok (x, S)) (sim_foldr_range'_iterR g n 0 b)

end
section
open OsuModel.Net OsuModel.Sim

theorem simM_forIn_list_eval {α β} (l : List α) (F : α → β → SimM (ForInStep β)) (g : α → β → ForInStep β)
    (C : Ctx) (S : St) (hF : ∀ a ∈ l, ∀ b, F a b C S = .ok (g a b, S)) (b : β) :
    forIn l b F C S = .ok (l.foldr (simForStep g) id b, S) := by
  induction l generalizing b with
  | nil => rfl
  | cons a t ih =>
    rw [List.forIn_cons]
    simp only [simM_bind, hF a List.mem_cons_self, Except.bind, List.foldr_cons, simForStep]
    cases g a b with
    | done c => rfl
    | yield c => exact ih (fun a h b => hF a (List.mem_cons_of_mem _ h) b) c

/-- nested objects of top-level object `o` (index `i`) starting before `target`, in order -/
def simNestedTW (o : TopObj) (i : Nat) (target : F64) : List Ref :=
  ((List.range o.nested.size).takeWhile (fun j => decide ((o.nested[j]!).start < target))).map (fun j => (i, (j : Int)))

/-- `enumerateUpTo` as a list function of the alive order -/
def simEnumL (objs : Array TopObj) (target : F64) : List Nat → List Ref
  | [] => []
  | i :: t => if decide ((objs[i]!).h.start < target) then (i, -1) :: simNestedTW (objs[i]!) i target ++ simEnumL objs target t
      else []

theorem sim_inner_iterR (o : TopObj) (i : Nat) (target : F64) :
    ∀ k (out : Array Ref), k ≤ o.nested.size →
      iterR (fun j out => if (!decide ((o.nested[j]!).start < target)) = true then ForInStep.done out
        else ForInStep.yield (out.push (i, (j : Int)))) k (o.nested.size - k) out =
      out ++ (((List.range' k (o.nested.size - k)).takeWhile (fun j => decide ((o.nested[j]!).start < target))).map
        (fun j => (i, (j : Int)))).toArray := by
  intro k out hk
  induction h : o.nested.size - k generalizing k out with
  | zero => simp [iterR]
  | succ m ih =>
    rw [List.range'_succ]
    simp only [iterR, List.takeWhile_cons]
    by_cases hs : (o.nested[k]!).start < target
    · simp only [hs, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [ih (k + 1) _ (by omega) (by omega)]
      simp
    · simp [hs]

end
section
open OsuModel.Net OsuModel.Sim

def simEnumInner (o : TopObj) (i : Nat) (target : F64) (j : Nat) (out : Array Ref) : ForInStep (Array Ref) :=
  if (!decide ((o.nested[j]!).start < target)) = true then ForInStep.done out else ForInStep.yield (out.push (i, (j : Int)))

def simEnumOuter (objs : Array TopObj) (target : F64) (i : Nat) (s : Option (Array Ref) × Array Ref) :
    ForInStep (Option (Array Ref) × Array Ref) :=
  if (!decide ((objs[i]!).h.start < target)) = true then ForInStep.done (some s.2, s.2)
  else ForInStep.yield (none, iterR (simEnumInner (objs[i]!) i target) 0 (objs[i]!).nested.size (s.2.push (i, -1)))

theorem sim_enum_fold (objs : Array TopObj) (target : F64) :
    ∀ (l : List Nat) (out : Array Ref),
      let r := l.foldr (simForStep (simEnumOuter objs target)) id
        (none, out)
      r.2 = out ++ (simEnumL objs target l).toArray ∧ (r.1 = none ∨ r.1 = some r.2) := by
  intro l
  induction l with
  | nil => intro out; simp [simEnumL]
  | cons i t ih =>
    intro out
    simp only [List.foldr_cons, simForStep]
    by_cases hs : (objs[i]!).h.start < target
    · have e : simEnumOuter objs target i (none, out) =
          .yield (none, iterR (simEnumInner (objs[i]!) i target) 0 (objs[i]!).nested.size (out.push (i, -1))) := by
        simp [simEnumOuter, hs]
      rw [e]; dsimp only
      have hin := sim_inner_iterR (objs[i]!) i target 0 ((out.push (i, -1))) (Nat.zero_le _)
      simp only [Nat.sub_zero] at hin
      obtain ⟨h1, h2⟩ := ih (iterR (simEnumInner (objs[i]!) i target) 0 (objs[i]!).nested.size (out.push (i, -1)))
      refine ⟨?_, h2⟩
      rw [h1, show simEnumInner (objs[i]!) i target = (fun j out => if (!decide ((objs[i]!).nested[j]!.start < target)) = true
        then ForInStep.done out else ForInStep.yield (out.push (i, (j : Int)))) from rfl, hin]
      simp [simEnumL, hs, simNestedTW, List.range_eq_range']
    · have e : simEnumOuter objs target i (none, out) = .done (some out, out) := by simp [simEnumOuter, hs]
      rw [e]; simp [hs, simEnumL]

end
section
open OsuModel.Net OsuModel.Sim

theorem simM_forIn_array_eval {α β} (a : Array α) (F : α → β → SimM (ForInStep β)) (g : α → β → ForInStep β)
    (C : Ctx) (S : St) (hF : ∀ x ∈ a.toList, ∀ b, F x b C S = .ok (g x b, S)) (b : β) :
    forIn a b F C S = .ok (a.toList.foldr (simForStep g) id b, S) := by
  rw [← Array.forIn_toList]; exact simM_forIn_list_eval _ F g C S hF b

theorem sim_simSortL_mem {α} (lt : α → α → Bool) (l : List α) (x : α) (hx : x ∈ simSortL lt l) : x ∈ l := by
  unfold simSortL at hx
  suffices ∀ acc : List α, x ∈ l.foldl (fun out x => out.insertIdx (simInsPos lt out x out.length) x) acc →
      x ∈ acc ∨ x ∈ l by
    rcases this [] hx with h | h
    · simp at h
    · exact h
  clear hx
  induction l with
  | nil => intro acc h; exact Or.inl h
  | cons y t ih =>
    intro acc h
    simp only [List.foldl_cons] at h
    rcases ih _ h with h' | h'
    · rcases (List.mem_insertIdx (sim_simInsPos_le lt acc y acc.length)).mp h' with e | e
      · exact Or.inr (e ▸ List.mem_cons_self)
      · exact Or.inl e
    · exact Or.inr (List.mem_cons_of_mem _ h')

theorem simS_enumerateUpTo (C : Ctx) (S : St) (target : F64)
    (h : ∀ i ∈ (S.dictSlots.filterMap id), i < C.pb.objects.size) :
    Sim.enumerateUpTo target C S = .ok ((simEnumL C.pb.objects target
      (simSortL (fun a b => decide (simKeyS C a < simKeyS C b)) (S.dictSlots.filterMap id).toList)).toArray, S) := by
  unfold Sim.enumerateUpTo
  simp only [simM_bind, simS_aliveObjects C S h, Except.bind, Sim.ctx, simM_read]
  rw [simM_forIn_array_eval _ _ (simEnumOuter C.pb.objects target) C S ?hF]
  · obtain ⟨h1, h2⟩ := sim_enum_fold C.pb.objects target
      (simSortL (fun a b => decide (simKeyS C a < simKeyS C b)) (S.dictSlots.filterMap id).toList) #[]
    simp only [List.toList_toArray]
    rcases h2 with h2 | h2 <;> simp only [h2, simM_pure, h1] <;> simp
  case hF =>
    intro x hx b
    have hxl : x < C.pb.objects.size := by
      simp only [List.toList_toArray] at hx
      exact h x (by simpa using sim_simSortL_mem _ _ _ hx)
    have e : C.pb.objects[x]! = C.pb.objects[x]'hxl := by simp [getElem!_def, hxl]
    simp only [simM_bind, Sim.topObj, Sim.getA, Sim.ctx, simM_read, Except.bind, simM_dite, dif_pos hxl, simM_pure]
    by_cases hs : (C.pb.objects[x]'hxl).h.start < target
    · simp only [hs, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, simM_ite, simM_bind]
      rw [simM_forIn'_range_pure _ _ (simEnumInner (C.pb.objects[x]'hxl) x target)
        (fun j hj b => by
          have e2 : (C.pb.objects[x]'hxl).nested[j]! = (C.pb.objects[x]'hxl).nested[j]'hj.upper := by
            simp [getElem!_def, hj.upper]
          by_cases hs2 : ((C.pb.objects[x]'hxl).nested[j]'hj.upper).start < target <;>
            simp [simEnumInner, e2, hs2])]
      simp [Except.bind, simEnumOuter, hs, e]
    · simp [hs, simEnumOuter, e]

end

section
open OsuImpl OsuModel.Net

theorem sim_usize_to_i64 (j : Usize) (h : j.val < 2 ^ 63) : (UScalar.hcast .I64 j).val = (j.val : Int) := by
  rw [UScalar.hcast_val_eq]; simp; rw [Int.bmod_eq_of_le] <;> omega

/-- `push_nested_up_to`'s loop from index `j`: appends `(i, j')` for the nested objects `j' ≥ j` that start before
`target`, up to the first one that does not. -/
theorem sim_push_nested_loop (o : sim.playable.TopObj) (i : Usize) (target : F64)
    (hn : o.nested.val.length < 2 ^ 63) :
    ∀ m (j : Usize) (out : alloc.vec.Vec sim.step.Ref), o.nested.val.length - j.val = m → j.val ≤ o.nested.val.length →
      out.val.length + ((List.range' j.val m).takeWhile (fun k => decide ((o.nested.val[k]!).start < target))).length
        < Usize.max →
      ∃ w, sim.step.push_nested_up_to_loop out o i target j false = ok w ∧
        w.val.map (fun r => (abs r : Nat × Int)) = out.val.map (fun r => (abs r : Nat × Int)) ++
          ((List.range' j.val m).takeWhile (fun k => decide ((o.nested.val[k]!).start < target))).map
            (fun k => (i.val, (k : Int))) := by
  intro m
  induction m with
  | zero =>
    intro j out hm hj hcap
    refine ⟨out, ?_, by simp⟩
    unfold sim.step.push_nested_up_to_loop; rw [loop_unfold]
    have : ¬ j < alloc.vec.Vec.len o.nested := by rw [vec_lt_len_iff]; omega
    simp [sim.step.push_nested_up_to_loop.body, this]
  | succ m ih =>
    intro j out hm hj hcap
    have hjl : j.val < o.nested.val.length := by omega
    have hjv : j < alloc.vec.Vec.len o.nested := by rw [vec_lt_len_iff]; exact hjl
    have e! : o.nested.val[j.val]! = o.nested.val[j.val]'hjl := by simp [getElem!_def, hjl]
    rw [List.range'_succ] at hcap ⊢
    by_cases hs : (o.nested.val[j.val]'hjl).start < target
    · obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := o.nested.property; omega)
      rw [List.takeWhile_cons_of_pos (by simp [e!, hs])] at hcap
      simp only [List.length_cons] at hcap
      have hpl : out.val.length < Usize.max := by omega
      have hc := sim_usize_to_i64 j (by omega)
      obtain ⟨w, hw, hwv⟩ := ih j1 (vpush out ⟨i, UScalar.hcast .I64 j⟩ hpl) (by omega) (by omega)
        (by rw [vpush_val, List.length_append, List.length_singleton, hj1v]; omega)
      refine ⟨w, ?_, ?_⟩
      · unfold sim.step.push_nested_up_to_loop; rw [loop_unfold]; dsimp only
        rw [show sim.step.push_nested_up_to_loop.body o i target out j false =
            ok (.cont (vpush out ⟨i, UScalar.hcast .I64 j⟩ hpl, j1, false)) by
          simp [sim.step.push_nested_up_to_loop.body, hjv, vec_index_usize_ok _ _ hjl, hs, lift, vec_push_ok out _ hpl, hj1]]
        simp only [bind_ok]
        unfold sim.step.push_nested_up_to_loop at hw; exact hw
      · rw [hwv, hj1v, List.takeWhile_cons_of_pos (by simp [e!, hs])]
        simp [abs, hc]
    · refine ⟨out, ?_, by rw [List.takeWhile_cons_of_neg (by simp [e!, hs])]; simp⟩
      unfold sim.step.push_nested_up_to_loop; rw [loop_unfold]; dsimp only
      rw [show sim.step.push_nested_up_to_loop.body o i target out j false = ok (.cont (out, j, true)) by
          simp [sim.step.push_nested_up_to_loop.body, hjv, vec_index_usize_ok _ _ hjl, hs]]
      simp only [bind_ok]
      rw [loop_unfold]
      simp [sim.step.push_nested_up_to_loop.body, hjv]

end
section
open OsuImpl OsuModel.Net

theorem sim_nestedTW_topS (tn) (o : sim.playable.TopObj) (i : Nat) (target : F64) :
    simNestedTW (topS tn o) i target =
      ((List.range' 0 o.nested.val.length).takeWhile (fun k => decide ((o.nested.val[k]!).start < target))).map
        (fun k => (i, (k : Int))) := by
  unfold simNestedTW
  have hs : (topS tn o).nested.size = o.nested.val.length := by simp [topS]
  rw [hs, List.range_eq_range']
  have hp : (fun j : Nat => decide ((((topS tn o).nested[j]! : OsuModel.Sim.HObj)).start < target)) =
      (fun k : Nat => decide (((o.nested.val[k]! : sim.playable.HObj)).start < target)) := by
    funext k
    by_cases hk : k < o.nested.val.length
    · simp [getElem!_def, hk, hobjS, topS]
    · simp [getElem!_def, hk, topS]; rfl
  rw [hp]

/-- `enumerate_up_to`'s loop from position `k` of the alive list. -/
theorem sim_enum_loop (tn fo) (c : sim.state.Ctx) (target : F64) (alive : alloc.vec.Vec Usize)
    (ha : ∀ x ∈ alive.val, x.val < c.pb.objects.val.length)
    (hn : ∀ o ∈ c.pb.objects.val, o.nested.val.length < 2 ^ 63) :
    ∀ m (k : Usize) (out : alloc.vec.Vec sim.step.Ref), alive.val.length - k.val = m → k.val ≤ alive.val.length →
      out.val.length + (simEnumL (simCtxS tn fo c).pb.objects target ((alive.val.drop k.val).map (·.val))).length
        < Usize.max →
      ∃ w, sim.step.enumerate_up_to_loop c target alive out k false = ok w ∧
        w.val.map (fun r => (abs r : Nat × Int)) = out.val.map (fun r => (abs r : Nat × Int)) ++
          simEnumL (simCtxS tn fo c).pb.objects target ((alive.val.drop k.val).map (·.val)) := by
  intro m
  induction m with
  | zero =>
    intro k out hm hk hcap
    have hd : alive.val.drop k.val = [] := List.drop_eq_nil_of_le (by omega)
    refine ⟨out, ?_, by simp [hd, simEnumL]⟩
    unfold sim.step.enumerate_up_to_loop; rw [loop_unfold]
    have : ¬ k < alloc.vec.Vec.len alive := by rw [vec_lt_len_iff]; omega
    simp [sim.step.enumerate_up_to_loop.body, this]
  | succ m ih =>
    intro k out hm hk hcap
    have hkl : k.val < alive.val.length := by omega
    have hkv : k < alloc.vec.Vec.len alive := by rw [vec_lt_len_iff]; exact hkl
    have hd : alive.val.drop k.val = (alive.val[k.val]'hkl) :: alive.val.drop (k.val + 1) := List.drop_eq_getElem_cons hkl
    set x := alive.val[k.val]'hkl with hx
    have hxl : x.val < c.pb.objects.val.length := ha x (List.getElem_mem hkl)
    have hobj : ((simCtxS tn fo c).pb.objects[x.val]!) = topS tn (c.pb.objects.val[x.val]'hxl) := by
      simp [simCtxS, playableS, getElem!_def, hxl]
    rw [hd] at hcap ⊢
    simp only [List.map_cons, simEnumL, hobj] at hcap ⊢
    by_cases hs : (c.pb.objects.val[x.val]'hxl).h.start < target
    · have hs' : (topS tn (c.pb.objects.val[x.val]'hxl)).h.start < target := by simpa [topS, hobjS] using hs
      simp only [hs', decide_true, ite_true, List.length_cons, List.length_append] at hcap ⊢
      rw [sim_nestedTW_topS] at hcap ⊢
      simp only [List.length_map] at hcap
      set o := c.pb.objects.val[x.val]'hxl with ho
      have hon : o.nested.val.length < 2 ^ 63 := hn o (List.getElem_mem hxl)
      have hpl : out.val.length < Usize.max := by omega
      set out1 := vpush out ⟨x, (-1)#i64⟩ hpl with hout1
      obtain ⟨out2, hp2, hp2v⟩ := sim_push_nested_loop o x target hon o.nested.val.length 0#usize out1 (by simp) (by simp)
        (by simp only [hout1, vpush_val, List.length_append, List.length_singleton]; simp at hcap ⊢; omega)
      obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := alive.property; omega)
      obtain ⟨w, hw, hwv⟩ := ih k1 out2 (by omega) (by omega) (by
        have := congrArg List.length hp2v
        simp only [List.length_map, List.length_append] at this
        rw [hk1v, this, hout1, vpush_val]; simp at hcap ⊢; omega)
      refine ⟨w, ?_, ?_⟩
      · unfold sim.step.enumerate_up_to_loop; rw [loop_unfold]; dsimp only
        rw [show sim.step.enumerate_up_to_loop.body c target alive out k false = ok (.cont (out2, k1, false)) by
          simp [sim.step.enumerate_up_to_loop.body, hkv, vec_index_usize_ok _ _ hkl, ← hx, vec_index_usize_ok _ _ hxl,
            ← ho, hs, vec_push_ok out _ hpl, ← hout1, sim.step.push_nested_up_to, hp2, hk1]]
        simp only [bind_ok]
        unfold sim.step.enumerate_up_to_loop at hw; exact hw
      · rw [hwv, hp2v, hk1v]
        simp [hout1, abs]
    · have hs' : ¬ (topS tn (c.pb.objects.val[x.val]'hxl)).h.start < target := by simpa [topS, hobjS] using hs
      simp only [hs', decide_false, Bool.false_eq_true, ite_false, List.append_nil]
      refine ⟨out, ?_, rfl⟩
      unfold sim.step.enumerate_up_to_loop; rw [loop_unfold]; dsimp only
      rw [show sim.step.enumerate_up_to_loop.body c target alive out k false = ok (.cont (out, k, true)) by
          simp [sim.step.enumerate_up_to_loop.body, hkv, vec_index_usize_ok _ _ hkl, vec_index_usize_ok _ _ hxl, hs, ← hx]]
      simp only [bind_ok]
      rw [loop_unfold]
      simp [sim.step.enumerate_up_to_loop.body, hkv]

end
section
open OsuImpl OsuModel.Net

theorem sim.step.enumerate_up_to_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (target : F64)
    (hd : ∀ o ∈ s.dict_slots.val, ∀ x, o = some x → x.val < c.pb.objects.val.length)
    (hd2 : s.dict_slots.val.length < Usize.max)
    (hn : ∀ o ∈ c.pb.objects.val, o.nested.val.length < 2 ^ 63)
    (hcap : ∀ v, OsuModel.Sim.Sim.enumerateUpTo target (simCtxS tn fo c) (simStS tn s) = .ok (v, simStS tn s) →
      v.size < Usize.max) :
    ∃ v, sim.step.enumerate_up_to c s target = ok v ∧
      OsuModel.Sim.Sim.enumerateUpTo target (simCtxS tn fo c) (simStS tn s) = .ok (abs v, simStS tn s) := by
  obtain ⟨al, hal, eal⟩ := sim.step.alive_objects_refines tn fo c s hd hd2
  have hS : ∀ i ∈ ((simStS tn s).dictSlots.filterMap id), i < (simCtxS tn fo c).pb.objects.size := by
    intro i hi
    simp [simStS, abs] at hi
    obtain ⟨a, ha, hai⟩ := hi
    rw [← hai]; simpa using hd _ ha a rfl
  have espec := simS_enumerateUpTo (simCtxS tn fo c) (simStS tn s) target hS
  rw [simS_aliveObjects _ _ hS] at eal
  have hal' : (simSortL (fun a b => decide (simKeyS (simCtxS tn fo c) a < simKeyS (simCtxS tn fo c) b))
      ((simStS tn s).dictSlots.filterMap id).toList) = al.val.map (·.val) := by
    have := congrArg (fun e => match e with | .ok p => p.1.toList | .error _ => []) eal
    simpa [abs] using this
  rw [hal'] at espec
  have hcap' := hcap _ espec
  simp only [List.size_toArray] at hcap'
  have ha : ∀ x ∈ al.val, x.val < c.pb.objects.val.length := by
    intro x hx
    have : x.val ∈ al.val.map (·.val) := List.mem_map_of_mem hx
    rw [← hal'] at this
    have := sim_simSortL_mem _ _ _ this
    simp [simStS, abs] at this
    obtain ⟨a, ha, hai⟩ := this
    rw [← hai]; exact hd _ ha a rfl
  obtain ⟨w, hw, hwv⟩ := sim_enum_loop tn fo c target al ha hn al.val.length 0#usize (alloc.vec.Vec.new _) (by simp) (by simp)
    (by simpa using hcap')
  refine ⟨w, by simp [sim.step.enumerate_up_to, hal, hw], ?_⟩
  rw [espec]
  simp only [List.drop_zero, show (0#usize : Usize).val = 0 from rfl] at hwv
  simp only [abs] at hwv
  simp [abs, hwv]

end

end OsuProofs
