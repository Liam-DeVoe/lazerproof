/-
sim5: `sim::step::sort_by_lifetime_start` (the `stableSortBy fut (lifetimeStart <)` of `lifetimeUpdate`'s first
update) refines the spec's `fut.mapM (i, lifetimeStart)` + `stableSortBy` + `map (·.1)`. Same scheme as
Sim/AliveSort (`stable_sort_by_start`): both sides are related to the list model `simSortL`.
-/
import OsuProofs.Sim.AliveSort
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

/-- the lifetime-start key of object state `i` -/
def s5_key (v : alloc.vec.Vec sim.state.OState) (i : Nat) : F64 := ((v.val[i]?).map (·.lifetime_start)).getD 0
def s5_ltKey (v : alloc.vec.Vec sim.state.OState) (a b : Nat) : Bool := decide (s5_key v a < s5_key v b)

theorem s5_sort_inner (v : alloc.vec.Vec sim.state.OState) (out : alloc.vec.Vec Usize) (x : Nat)
    (hin : ∀ e ∈ out.val, e.val < v.val.length) :
    ∀ (n : Nat) (i : Usize), i.val = n → i.val ≤ out.val.length →
      ∃ r, sim.step.sort_by_lifetime_start_loop0_loop0 v out (s5_key v x) i = ok r ∧
        r.val = simInsPos (s5_ltKey v) (out.val.map (·.val)) x n := by
  intro n
  induction n with
  | zero =>
    intro i hi _
    refine ⟨i, ?_, by simp [hi, simInsPos]⟩
    unfold sim.step.sort_by_lifetime_start_loop0_loop0; rw [loop_unfold]
    have : ¬ i > 0#usize := by scalar_tac
    simp [sim.step.sort_by_lifetime_start_loop0_loop0.body, this]
  | succ n ih =>
    intro i hi hle
    have hpos : i > 0#usize := by scalar_tac
    obtain ⟨i1, hi1, hi1v0, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := i) (y := 1#usize) (by simp; omega))
    have hi1v : i1.val = n := by rw [hi1v0]; simp; omega
    have hl1 : i1.val < out.val.length := by omega
    have hmem : out.val[i1.val]'hl1 ∈ out.val := List.getElem_mem hl1
    have hl2 := hin _ hmem
    have hkey : (v.val[(out.val[i1.val]'hl1).val]'hl2).lifetime_start = s5_key v (out.val[i1.val]'hl1).val := by
      simp [s5_key, List.getElem?_eq_getElem hl2]
    have hget : (out.val.map (·.val))[n]? = some (out.val[i1.val]'hl1).val := by
      rw [← hi1v]; simp [List.getElem?_eq_getElem hl1]
    by_cases hlt : s5_key v x < s5_key v (out.val[i1.val]'hl1).val
    · obtain ⟨r, hr, hrv⟩ := ih i1 hi1v (by omega)
      refine ⟨r, ?_, by rw [hrv]; simp [simInsPos, hget, s5_ltKey, hlt]⟩
      unfold sim.step.sort_by_lifetime_start_loop0_loop0; rw [loop_unfold]
      unfold sim.step.sort_by_lifetime_start_loop0_loop0 at hr
      rw [show sim.step.sort_by_lifetime_start_loop0_loop0.body v out (s5_key v x) i = ok (.cont i1) by
        simp [sim.step.sort_by_lifetime_start_loop0_loop0.body, hpos, hi1, vec_index_usize_ok _ _ hl1,
          vec_index_usize_ok _ _ hl2, hkey, hlt]]
      simpa only [bind_ok] using hr
    · refine ⟨i, ?_, by simp [simInsPos, hget, s5_ltKey, hlt, hi]⟩
      unfold sim.step.sort_by_lifetime_start_loop0_loop0; rw [loop_unfold]
      rw [show sim.step.sort_by_lifetime_start_loop0_loop0.body v out (s5_key v x) i = ok (.done i) by
        simp [sim.step.sort_by_lifetime_start_loop0_loop0.body, hpos, hi1, vec_index_usize_ok _ _ hl1,
          vec_index_usize_ok _ _ hl2, hkey, hlt]]
      simp only [bind_ok]

/-- list-model form -/
theorem s5_sort_model (s : sim.state.St) (xs : Slice Usize)
    (hx : ∀ e ∈ xs.val, e.val < s.objs.val.length) (hl : xs.val.length < Usize.max) :
    ∃ out, sim.step.sort_by_lifetime_start s xs = ok out ∧
      out.val.map (·.val) = simSortL (s5_ltKey s.objs) (xs.val.map (·.val)) := by
  let G : Nat → List Nat → List Nat := fun k L =>
    L.insertIdx (simInsPos (s5_ltKey s.objs) L (xs.val[k]!).val L.length) (xs.val[k]!).val
  obtain ⟨v, hv, hvr⟩ := loop_fold_gen' (fun x => sim.step.sort_by_lifetime_start_loop0.body s xs x.1 x.2) (·.2)
    xs.val.length (by omega)
    (fun x => (∀ e ∈ x.1.val, e.val < s.objs.val.length) ∧ x.1.val.length = x.2.val) (fun x => x.1.val.map (·.val))
    G (fun y L => y.val.map (·.val) = L)
    (by
      rintro ⟨out, k⟩ ⟨hin, hlen⟩ hk j1 hj1 hj1v
      simp only at hin hlen hk hj1 hj1v ⊢
      have hxk : (xs.val[k.val]'hk).val < s.objs.val.length := hx _ (List.getElem_mem hk)
      obtain ⟨r, hr, hrv⟩ := s5_sort_inner s.objs out (xs.val[k.val]'hk).val hin out.val.length
        (alloc.vec.Vec.len out) (by simp) (by simp)
      have hkey : (s.objs.val[(xs.val[k.val]'hk).val]'hxk).lifetime_start = s5_key s.objs (xs.val[k.val]'hk).val := by
        simp [s5_key, List.getElem?_eq_getElem hxk]
      have hrl : r.val ≤ out.val.length := by rw [hrv]; exact sim_simInsPos_le _ _ _ _
      obtain ⟨w, hw, hwv⟩ := sim.step.insert_idx_refines out r (xs.val[k.val]'hk) hrl (by omega)
      refine ⟨(w, j1), ?_, rfl, ?_, ?_, ?_⟩
      · simp [vec_index_usize_ok _ _ hxk, hkey] at hr
        simp [sim.step.sort_by_lifetime_start_loop0.body, slice_lt_len_iff, hk, slice_index_ok _ _ hk,
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
      refine ⟨out, by simp only [sim.step.sort_by_lifetime_start_loop0.body, this, ite_false], rfl⟩)
    (alloc.vec.Vec.new Usize, 0#usize) ⟨by simp, by simp⟩ (by simp)
  refine ⟨v, by unfold sim.step.sort_by_lifetime_start sim.step.sort_by_lifetime_start_loop0; exact hv, ?_⟩
  rw [hvr]
  simp only [show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero]
  unfold simSortL
  rw [List.foldl_map, foldl_iterR]
  simp [G]

section
open OsuImpl OsuModel.Net OsuModel.Sim

/-- spec key: lifetime start of object state `i` -/
def s5_keyS (S : St) (i : Nat) : F64 := ((S.objs[i]?).map (·.lifetimeStart)).getD 0

theorem s5S_mapM_ls (C : Ctx) (S : St) (l : List Nat) (h : ∀ i ∈ l, i < S.objs.size) :
    (l.mapM (fun i => do return (i, (← Sim.ostate i).lifetimeStart))) C S =
      .ok (l.map (fun i => (i, s5_keyS S i)), S) := by
  induction l with
  | nil => rfl
  | cons i t ih =>
    have hi := h i List.mem_cons_self
    have ih' := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    simp only [List.mapM_cons, simM_bind, simM_pure, simS_ostate _ _ _ hi, Except.bind]
    rw [ih']
    simp [s5_keyS, hi]

theorem s5_keyS_st (tn) (s : sim.state.St) (i : Nat) : s5_keyS (simStS tn s) i = s5_key s.objs i := by
  simp only [s5_keyS, s5_key, simStS, abs]
  by_cases h : i < s.objs.val.length
  · simp [h, List.getElem?_eq_getElem h, ostateS]
  · simp [h]

end

/-- `sort_by_lifetime_start s xs` = the spec's `lifetimeUpdate` sort of the future list `fut = xs`:
`(stableSortBy (← fut.mapM fun i => do return (i, (← ostate i).lifetimeStart)) (·.2 < ·.2)).map (·.1)`,
in any spec context and without changing the state. -/
theorem sim.step.sort_by_lifetime_start_refines (tn) (s : sim.state.St) (xs : Slice Usize)
    (hx : ∀ e ∈ xs.val, e.val < s.objs.val.length) (hl : xs.val.length < Usize.max) :
    ∃ out, sim.step.sort_by_lifetime_start s xs = ok out ∧ ∀ C,
      (do
        let keyed ← (xs.val.map (·.val)).toArray.mapM fun i => do return (i, (← OsuModel.Sim.Sim.ostate i).lifetimeStart)
        pure ((OsuModel.Sim.stableSortBy keyed fun a b => a.2 < b.2).map (·.1)) : OsuModel.Sim.SimM (Array Nat))
        C (simStS tn s) = .ok ((out.val.map (·.val)).toArray, simStS tn s) := by
  obtain ⟨out, hout, hv⟩ := s5_sort_model s xs hx hl
  refine ⟨out, hout, fun C => ?_⟩
  have hS : ∀ i ∈ xs.val.map (·.val), i < (simStS tn s).objs.size := by
    intro i hi
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    simpa [simStS, abs] using hx e he
  simp only [simM_bind, Array.mapM_eq_mapM_toList, List.toList_toArray, simM_map]
  rw [s5S_mapM_ls _ _ _ hS]
  simp only [Except.bind, Except.map, simM_pure]
  rw [sim_stableSortBy_eq]
  simp only [List.toList_toArray]
  rw [sim_simSortL_map (fun a b => decide (a.2 < b.2)) (fun a b => decide (s5_keyS (simStS tn s) a < s5_keyS (simStS tn s) b))
    (fun i => (i, s5_keyS (simStS tn s) i)) (fun a b => rfl)]
  have hk : (fun a b => decide (s5_keyS (simStS tn s) a < s5_keyS (simStS tn s) b)) = s5_ltKey s.objs := by
    funext a b; simp [s5_keyS_st, s5_ltKey]
  rw [hk, ← hv]
  simp [Function.comp_def]

end OsuProofs
