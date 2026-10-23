/-
`sim::step` alive-object order: `insert_idx` (`Array.insertIdx`), `stable_sort_by_start` and `alive_objects` refine
`stableSortBy` / `Sim.aliveObjects` (`AliveEntries.Values.OrderBy(StartTime)`: dictionary order, stable insertion sort).
Both sides are related to the list model `simSortL` (insertion sort as a fold, `simInsPos` = `insPos`).
-/
import OsuProofs.Sim.StepBasic
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

theorem sim_insert_idx_loop (v : List Usize) (k : Usize) :
    ∀ (w : alloc.vec.Vec Usize) (i : Usize), k.val ≤ i.val → i.val ≤ v.length →
      (∃ d, w.val = v.take i.val ++ d :: v.drop i.val) →
      ∃ w', sim.step.insert_idx_loop w k i = ok w' ∧ ∃ d, w'.val = v.take k.val ++ d :: v.drop k.val := by
  intro w i hki hiv hw
  unfold sim.step.insert_idx_loop
  refine loop_ok _ (fun (x : alloc.vec.Vec Usize × Usize) => x.2.val)
    (fun (x : alloc.vec.Vec Usize × Usize) => k.val ≤ x.2.val ∧ x.2.val ≤ v.length ∧
      ∃ d, x.1.val = v.take x.2.val ++ d :: v.drop x.2.val)
    (fun (w' : alloc.vec.Vec Usize) => ∃ d, w'.val = v.take k.val ++ d :: v.drop k.val) ?_ (w, i) ⟨hki, hiv, hw⟩
  rintro ⟨w, i⟩ ⟨hki, hiv, d, hw⟩
  dsimp only at hki hiv hw ⊢
  by_cases hik : k.val < i.val
  · right
    have hik' : i > k := hik
    obtain ⟨i1, hi1, hi1v0, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := i) (y := 1#usize) (by simp; omega))
    have hi1v : i1.val = i.val - 1 := by rw [hi1v0]; simp
    have hwl : w.val.length = v.length + 1 := by rw [hw]; simp; omega
    have hl1 : i1.val < w.val.length := by omega
    have hl2 : i.val < w.val.length := by omega
    have hget : w.val[i1.val]'hl1 = v[i.val - 1]'(by omega) := by
      simp only [hw, hi1v]
      rw [List.getElem_append_left (by simp; omega)]
      simp
    refine ⟨(alloc.vec.Vec.set w i (v[i.val - 1]'(by omega)), i1), ?_, ⟨by dsimp only; omega, by dsimp only; omega, ?_⟩,
      by dsimp only; omega⟩
    · simp [sim.step.insert_idx_loop.body, hik', hi1, vec_index_eq w i1 hl1, vec_index_usize_ok w i1 hl1, hget, vec_index_mut_eq w i hl2]
    · refine ⟨v[i.val - 1]'(by omega), ?_⟩
      dsimp only
      rw [alloc.vec.Vec.set_val_eq, hw, hi1v]
      have e1 : v.take i.val = v.take (i.val - 1) ++ [v[i.val - 1]'(by omega)] := by
        have e : i.val = (i.val - 1) + 1 := by omega
        conv_lhs => rw [e]
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; simp
      have e2 : v.drop (i.val - 1) = v[i.val - 1]'(by omega) :: v.drop i.val := by
        rw [List.drop_eq_getElem_cons (by omega)]; congr 2; omega
      rw [e2, e1]; simp only [List.append_assoc, List.singleton_append]
      rw [List.set_append_right _ _ (by simp)]
      have hl : (v.take (i.val - 1)).length = i.val - 1 := by simp; try omega
      rw [hl]
      have h1 : i.val - (i.val - 1) = 1 := by omega
      rw [h1]; rfl
  · left
    have hik' : ¬ i > k := hik
    refine ⟨w, by simp [sim.step.insert_idx_loop.body, hik'], ⟨d, ?_⟩⟩
    have : i.val = k.val := by omega
    rw [← this]; exact hw

theorem sim.step.insert_idx_refines (v : alloc.vec.Vec Usize) (k : Usize) (x : Usize) (hk : k.val ≤ v.val.length) (hl : v.val.length < Usize.max) :
    ∃ w, sim.step.insert_idx v k x = ok w ∧ w.val = v.val.insertIdx k.val x := by
  obtain ⟨v1, hv1, hv1v⟩ := push_eq v x hl
  have hlen : (alloc.vec.Vec.len v1).val = v.val.length + 1 := by simp [hv1v]
  obtain ⟨i1, hi1, hi1v0, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := alloc.vec.Vec.len v1) (y := 1#usize) (by simp [hlen]))
  have hi1v : i1.val = v.val.length := by rw [hi1v0]; simp [hlen]
  obtain ⟨w2, hw2, d, hw2v⟩ := sim_insert_idx_loop v.val k v1 i1 (by omega) (by omega) ⟨x, by rw [hv1v, hi1v]; simp⟩
  have hw2l : k.val < w2.val.length := by rw [hw2v]; simp; omega
  refine ⟨alloc.vec.Vec.set w2 k x, ?_, ?_⟩
  · simp only [sim.step.insert_idx, hv1, hi1, hw2, bind_ok, vec_index_mut_eq w2 k hw2l]; rfl
  · rw [alloc.vec.Vec.set_val_eq, hw2v, insertIdx_take_drop x _ _ hk]
    rw [List.set_append_right _ _ (by simp)]
    have hl2 : (v.val.take k.val).length = k.val := by simp; omega
    rw [hl2, Nat.sub_self]; rfl


/-- `insPos` on a list. -/
def simInsPos {α} (lt : α → α → Bool) (out : List α) (x : α) : Nat → Nat
  | 0 => 0
  | i + 1 => if (out[i]?.map (lt x)).getD false then simInsPos lt out x i else i + 1

theorem sim_insPos_eq {α} (lt : α → α → Bool) (out : Array α) (x : α) :
    ∀ i (h : i ≤ out.size), OsuModel.Sim.insPos lt out x i h = simInsPos lt out.toList x i := by
  intro i
  induction i with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    simp only [OsuModel.Sim.insPos, simInsPos]
    have : n < out.toList.length := by simpa using h
    simp [List.getElem?_eq_getElem this, ih]

/-- The insertion sort as a fold. -/
def simSortL {α} (lt : α → α → Bool) (xs : List α) : List α :=
  xs.foldl (fun out x => out.insertIdx (simInsPos lt out x out.length) x) []

theorem sim_simInsPos_le {α} (lt : α → α → Bool) (out : List α) (x : α) : ∀ i, simInsPos lt out x i ≤ i := by
  intro i; induction i with
  | zero => simp [simInsPos]
  | succ n ih => simp only [simInsPos]; split <;> omega

theorem sim_stableSortBy_eq {α} (xs : Array α) (lt : α → α → Bool) :
    OsuModel.Sim.stableSortBy xs lt = (simSortL lt xs.toList).toArray := by
  unfold OsuModel.Sim.stableSortBy simSortL
  simp only [Id.run]
  rw [← Array.forIn_toList]
  simp only [List.forIn_pure_yield_eq_foldl, Id.run_pure]
  generalize xs.toList = l
  suffices h : ∀ (acc : Array α), l.foldl (fun b a =>
      (b.extract 0 (OsuModel.Sim.insPos lt b a b.size (Nat.le_refl _))).push a ++
        b.extract (OsuModel.Sim.insPos lt b a b.size (Nat.le_refl _)) b.size) acc =
      (l.foldl (fun out x => out.insertIdx (simInsPos lt out x out.length) x) acc.toList).toArray by
    exact h #[]
  induction l with
  | nil => intro acc; simp
  | cons y t ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih]
    congr 2
    rw [sim_insPos_eq]
    have hp := sim_simInsPos_le lt acc.toList y acc.toList.length
    rw [insertIdx_take_drop _ _ _ (by simpa using hp)]
    simp [Array.toList_extract, List.extract]


theorem sim_simInsPos_map {α β} (lt : β → β → Bool) (lt' : α → α → Bool) (g : α → β)
    (hg : ∀ a b, lt (g a) (g b) = lt' a b) (L : List α) (x : α) :
    ∀ n, simInsPos lt (L.map g) (g x) n = simInsPos lt' L x n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih =>
    simp only [simInsPos, List.getElem?_map, ih]
    cases L[n]? <;> simp [hg]

theorem sim_simSortL_map {α β} (lt : β → β → Bool) (lt' : α → α → Bool) (g : α → β)
    (hg : ∀ a b, lt (g a) (g b) = lt' a b) (l : List α) :
    simSortL lt (l.map g) = (simSortL lt' l).map g := by
  unfold simSortL
  suffices ∀ acc : List α, (l.map g).foldl (fun (out : List β) x => out.insertIdx (simInsPos lt out x out.length) x) (acc.map g) =
      (l.foldl (fun (out : List α) x => out.insertIdx (simInsPos lt' out x out.length) x) acc).map g by
    simpa using this []
  induction l with
  | nil => intro acc; simp
  | cons y t ih =>
    intro acc
    simp only [List.map_cons, List.foldl_cons]
    rw [← ih]
    congr 1
    have e := sim_simInsPos_map lt lt' g hg acc y acc.length
    rw [List.length_map, e, List.map_insertIdx]

/-- the start-time key of top-level object `i` -/
def simKey (v : alloc.vec.Vec sim.playable.TopObj) (i : Nat) : F64 := ((v.val[i]?).map (·.h.start)).getD 0
def simLtKey (v : alloc.vec.Vec sim.playable.TopObj) (a b : Nat) : Bool := decide (simKey v a < simKey v b)

theorem sim_sort_inner (v : alloc.vec.Vec sim.playable.TopObj) (out : alloc.vec.Vec Usize) (x : Nat)
    (hin : ∀ e ∈ out.val, e.val < v.val.length) :
    ∀ (n : Nat) (i : Usize), i.val = n → i.val ≤ out.val.length →
      ∃ r, sim.step.stable_sort_by_start_loop0_loop0 v out (simKey v x) i = ok r ∧
        r.val = simInsPos (simLtKey v) (out.val.map (·.val)) x n := by
  intro n
  induction n with
  | zero =>
    intro i hi _
    refine ⟨i, ?_, by simp [hi, simInsPos]⟩
    unfold sim.step.stable_sort_by_start_loop0_loop0; rw [loop_unfold]
    have : ¬ i > 0#usize := by scalar_tac
    simp [sim.step.stable_sort_by_start_loop0_loop0.body, this]
  | succ n ih =>
    intro i hi hle
    have hpos : i > 0#usize := by scalar_tac
    obtain ⟨i1, hi1, hi1v0, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := i) (y := 1#usize) (by simp; omega))
    have hi1v : i1.val = n := by rw [hi1v0]; simp; omega
    have hl1 : i1.val < out.val.length := by omega
    have hmem : out.val[i1.val]'hl1 ∈ out.val := List.getElem_mem hl1
    have hl2 := hin _ hmem
    have hkey : (v.val[(out.val[i1.val]'hl1).val]'hl2).h.start = simKey v (out.val[i1.val]'hl1).val := by
      simp [simKey, List.getElem?_eq_getElem hl2]
    have hget : (out.val.map (·.val))[n]? = some (out.val[i1.val]'hl1).val := by
      rw [← hi1v]; simp [List.getElem?_eq_getElem hl1]
    by_cases hlt : simKey v x < simKey v (out.val[i1.val]'hl1).val
    · obtain ⟨r, hr, hrv⟩ := ih i1 hi1v (by omega)
      refine ⟨r, ?_, by rw [hrv]; simp [simInsPos, hget, simLtKey, hlt]⟩
      unfold sim.step.stable_sort_by_start_loop0_loop0; rw [loop_unfold]
      unfold sim.step.stable_sort_by_start_loop0_loop0 at hr
      rw [show sim.step.stable_sort_by_start_loop0_loop0.body v out (simKey v x) i = ok (.cont i1) by
        simp [sim.step.stable_sort_by_start_loop0_loop0.body, hpos, hi1, vec_index_usize_ok _ _ hl1, vec_index_usize_ok _ _ hl2,
          hkey, hlt]]
      simpa only [bind_ok] using hr
    · refine ⟨i, ?_, by simp [simInsPos, hget, simLtKey, hlt, hi]⟩
      unfold sim.step.stable_sort_by_start_loop0_loop0; rw [loop_unfold]
      rw [show sim.step.stable_sort_by_start_loop0_loop0.body v out (simKey v x) i = ok (.done i) by
        simp [sim.step.stable_sort_by_start_loop0_loop0.body, hpos, hi1, vec_index_usize_ok _ _ hl1, vec_index_usize_ok _ _ hl2,
          hkey, hlt]]
      simp only [bind_ok]

theorem sim.step.stable_sort_by_start_refines (c : sim.state.Ctx) (xs : Slice Usize)
    (hx : ∀ e ∈ xs.val, e.val < c.pb.objects.val.length) (hl : xs.val.length < Usize.max) :
    ∃ out, sim.step.stable_sort_by_start c xs = ok out ∧
      out.val.map (·.val) = simSortL (simLtKey c.pb.objects) (xs.val.map (·.val)) := by
  let G : Nat → List Nat → List Nat := fun k L =>
    L.insertIdx (simInsPos (simLtKey c.pb.objects) L (xs.val[k]!).val L.length) (xs.val[k]!).val
  obtain ⟨v, hv, hvr⟩ := loop_fold_gen' (fun x => sim.step.stable_sort_by_start_loop0.body c xs x.1 x.2) (·.2)
    xs.val.length (by omega)
    (fun x => (∀ e ∈ x.1.val, e.val < c.pb.objects.val.length) ∧ x.1.val.length = x.2.val) (fun x => x.1.val.map (·.val))
    G (fun y L => y.val.map (·.val) = L)
    (by
      rintro ⟨out, k⟩ ⟨hin, hlen⟩ hk j1 hj1 hj1v
      simp only at hin hlen hk hj1 hj1v ⊢
      have hxk : (xs.val[k.val]'hk).val < c.pb.objects.val.length := hx _ (List.getElem_mem hk)
      obtain ⟨r, hr, hrv⟩ := sim_sort_inner c.pb.objects out (xs.val[k.val]'hk).val hin out.val.length
        (alloc.vec.Vec.len out) (by simp) (by simp)
      have hkey : (c.pb.objects.val[(xs.val[k.val]'hk).val]'hxk).h.start = simKey c.pb.objects (xs.val[k.val]'hk).val := by
        simp [simKey, List.getElem?_eq_getElem hxk]
      have hrl : r.val ≤ out.val.length := by rw [hrv]; exact sim_simInsPos_le _ _ _ _
      obtain ⟨w, hw, hwv⟩ := sim.step.insert_idx_refines out r (xs.val[k.val]'hk) hrl (by omega)
      refine ⟨(w, j1), ?_, rfl, ?_, ?_, ?_⟩
      · simp [vec_index_usize_ok _ _ hxk, hkey] at hr
        simp [sim.step.stable_sort_by_start_loop0.body, slice_lt_len_iff, hk, slice_index_ok _ _ hk,
          vec_index_usize_ok _ _ hxk, hkey, hr, hw, hj1]
      · simp only [hwv, G, getElem!_pos xs.val k.val hk, hrv, List.map_insertIdx]
        simp
      · intro e he; rw [hwv] at he
        rcases (List.mem_insertIdx hrl).mp he with h | h
        · exact h ▸ hxk
        · exact hin e h
      · rw [hwv]; simp [List.length_insertIdx, hrl, hj1v, hlen]; omega)
    (by
      rintro ⟨out, k⟩ ⟨hin, hlen⟩ hge
      have : ¬ k < Slice.len xs := by rw [slice_lt_len_iff]; simp at hge; omega
      refine ⟨out, by simp only [sim.step.stable_sort_by_start_loop0.body, this, ite_false], rfl⟩)
    (alloc.vec.Vec.new Usize, 0#usize) ⟨by simp, by simp⟩ (by simp)
  refine ⟨v, by unfold sim.step.stable_sort_by_start sim.step.stable_sort_by_start_loop0; exact hv, ?_⟩
  rw [hvr]
  simp only [show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero]
  unfold simSortL
  rw [List.foldl_map, foldl_iterR]
  simp [G]

section
open OsuImpl OsuModel.Net

theorem sim_filterMap_foldl (l : List (Option Usize)) :
    ∀ acc : List Nat, acc ++ (l.filterMap id).map (·.val) =
      l.foldl (fun acc o => match o with | some x => acc ++ [x.val] | none => acc) acc := by
  induction l with
  | nil => intro acc; simp
  | cons o t ih => intro acc; cases o <;> simp [← ih]

/-- the dictionary enumeration of `aliveObjects` (`dictSlots.filterMap id`) -/
theorem sim_alive_enum (s : sim.state.St) :
    ∃ v, sim.step.alive_objects_loop s (alloc.vec.Vec.new Usize) 0#usize = ok v ∧
      v.val.map (·.val) = (s.dict_slots.val.filterMap id).map (·.val) := by
  obtain ⟨v, hv, hvr⟩ := loop_fold_gen' (fun x => sim.step.alive_objects_loop.body s x.1 x.2) (·.2)
    s.dict_slots.val.length (by have := s.dict_slots.property; omega)
    (fun x => x.1.val.length ≤ x.2.val) (fun x => x.1.val.map (·.val))
    (fun k L => match s.dict_slots.val[k]! with | some x => L ++ [x.val] | none => L) (fun y L => y.val.map (·.val) = L)
    (by
      rintro ⟨out, k⟩ hI hk j1 hj1 hj1v
      simp only at hI hk hj1 hj1v ⊢
      have hkd : k.val < s.dict_slots.val.length := hk
      cases ho : s.dict_slots.val[k.val]'hkd with
      | none =>
        refine ⟨(out, j1), ?_, rfl, ?_, ?_⟩
        · simp [sim.step.alive_objects_loop.body, vec_lt_len_iff, hkd, vec_index_usize_ok _ _ hkd, ho, hj1]
        · simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hkd, ho]
        · simp only; omega
      | some x =>
        have hpl : out.val.length < Usize.max := by have := s.dict_slots.property; omega
        refine ⟨(vpush out x hpl, j1), ?_, rfl, ?_, ?_⟩
        · simp [sim.step.alive_objects_loop.body, vec_lt_len_iff, hkd, vec_index_usize_ok _ _ hkd, ho, hj1,
            vec_push_ok out x hpl]
        · simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hkd, ho]
        · simp only [vpush_val, List.length_append]; simp; omega)
    (by
      rintro ⟨out, k⟩ hI hge
      have : ¬ k < alloc.vec.Vec.len s.dict_slots := by rw [vec_lt_len_iff]; simp at hge; omega
      exact ⟨out, by simp only [sim.step.alive_objects_loop.body, this, ite_false], rfl⟩)
    (alloc.vec.Vec.new Usize, 0#usize) (by simp) (by simp)
  refine ⟨v, by unfold sim.step.alive_objects_loop; exact hv, ?_⟩
  rw [hvr]
  simp only [show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero]
  have := sim_filterMap_foldl s.dict_slots.val []
  rw [foldl_iterR] at this
  simp at this ⊢
  rw [this]

end
section
open OsuImpl OsuModel.Net OsuModel.Sim

/-- spec key of a top-level object -/
def simKeyS (C : Ctx) (i : Nat) : F64 := ((C.pb.objects[i]?).map (·.h.start)).getD 0

theorem simS_startOf (C : Ctx) (S : St) (i : Nat) (h : i < C.pb.objects.size) :
    Sim.startOf i C S = .ok (simKeyS C i, S) := by
  simp [Sim.startOf, Sim.topObj, Sim.getA, Sim.ctx, h, Except.bind, Except.map, simKeyS]

theorem simS_mapM_start (C : Ctx) (S : St) (l : List Nat) (h : ∀ i ∈ l, i < C.pb.objects.size) :
    (l.mapM (fun i => Prod.mk i <$> Sim.startOf i)) C S = .ok (l.map (fun i => (i, simKeyS C i)), S) := by
  induction l with
  | nil => rfl
  | cons i t ih =>
    simp only [List.mapM_cons, simM_bind, simM_pure, simM_map]
    rw [simS_startOf _ _ _ (h i List.mem_cons_self)]
    simp [Except.bind, Except.map, ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]

theorem simS_aliveObjects (C : Ctx) (S : St) (h : ∀ i ∈ (S.dictSlots.filterMap id), i < C.pb.objects.size) :
    Sim.aliveObjects C S = .ok ((simSortL (fun a b => decide (simKeyS C a < simKeyS C b))
      (S.dictSlots.filterMap id).toList).toArray, S) := by
  unfold Sim.aliveObjects
  simp only [simM_bind, Sim.st, simM_get, Except.bind]
  simp only [Array.mapM_eq_mapM_toList, simM_map]
  have hl : ∀ i ∈ (S.dictSlots.filterMap id).toList, i < C.pb.objects.size := fun i hi => h i (by simpa using hi)
  simp only [bind_pure_comp, simS_mapM_start _ _ _ hl, Except.map, simM_pure]
  rw [sim_stableSortBy_eq]
  simp only [List.toList_toArray]
  rw [sim_simSortL_map (fun a b => decide (a.2 < b.2)) (fun a b => decide (simKeyS C a < simKeyS C b))
    (fun i => (i, simKeyS C i)) (fun a b => rfl)]
  simp [Function.comp_def]

end
section
open OsuImpl OsuModel.Net

theorem sim_keyS_ctx (tn fo) (c : sim.state.Ctx) (i : Nat) : simKeyS (simCtxS tn fo c) i = simKey c.pb.objects i := by
  simp only [simKeyS, simKey, simCtxS, playableS]
  by_cases h : i < c.pb.objects.val.length
  · simp [h, List.getElem?_eq_getElem h, topS, hobjS]
  · simp [h]

theorem sim.step.alive_objects_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St)
    (hd : ∀ o ∈ s.dict_slots.val, ∀ x, o = some x → x.val < c.pb.objects.val.length)
    (hd2 : s.dict_slots.val.length < Usize.max) :
    ∃ v, sim.step.alive_objects c s = ok v ∧
      OsuModel.Sim.Sim.aliveObjects (simCtxS tn fo c) (simStS tn s) = .ok (abs v, simStS tn s) := by
  obtain ⟨e, he, hev⟩ := sim_alive_enum s
  have hel : e.val.length ≤ s.dict_slots.val.length := by
    have := congrArg List.length hev; simp at this; rw [this]; exact List.length_filterMap_le _ _
  have hx : ∀ x ∈ (alloc.vec.Vec.deref e).val, x.val < c.pb.objects.val.length := by
    intro x hxm
    have hxm' : x ∈ e.val := by simpa [alloc.vec.Vec.deref] using hxm
    have : x.val ∈ e.val.map (·.val) := List.mem_map_of_mem hxm'
    rw [hev] at this
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp this
    obtain ⟨o, ho, hoy⟩ := List.mem_filterMap.mp hy
    rw [← hyx]; exact hd o ho y hoy
  obtain ⟨out, hout, houtv⟩ := sim.step.stable_sort_by_start_refines c (alloc.vec.Vec.deref e) hx
    (by simp [alloc.vec.Vec.deref]; omega)
  refine ⟨out, by simp [sim.step.alive_objects, he, hout], ?_⟩
  have hS : ∀ i ∈ ((simStS tn s).dictSlots.filterMap id), i < (simCtxS tn fo c).pb.objects.size := by
    intro i hi
    simp [simStS, abs] at hi
    obtain ⟨a, ha, hai⟩ := hi
    rw [← hai]; simpa using hd _ ha a rfl
  rw [simS_aliveObjects _ _ hS]
  simp only [Except.ok.injEq, Prod.mk.injEq, and_true]
  have hk : (fun a b => decide (simKeyS (simCtxS tn fo c) a < simKeyS (simCtxS tn fo c) b)) = simLtKey c.pb.objects := by
    funext a b; simp [sim_keyS_ctx, simLtKey]
  rw [hk]
  have hids : (Array.filterMap id (simStS tn s).dictSlots).toList = (alloc.vec.Vec.deref e).val.map (·.val) := by
    rw [show (alloc.vec.Vec.deref e).val = e.val by simp [alloc.vec.Vec.deref, Slice.from_val], hev]
    simp [simStS, abs, List.filterMap_map, Function.comp_def]
    rw [List.map_filterMap]
  rw [hids, ← houtv]
  simp [abs]

end

end OsuProofs
