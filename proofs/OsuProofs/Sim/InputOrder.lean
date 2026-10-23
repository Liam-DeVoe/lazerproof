/-
Input / update order of the alive DHOs (`Sim.inputOrder`: start time, ties by ChildID, stable; `Sim.updateOrder`:
its reverse): `input_lt`, `input_order`, `update_order`.
-/
import OsuProofs.Sim.Hit
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result

namespace OsuProofs

section
open OsuImpl OsuModel.Net

def simCid (s : sim.state.St) (i : Nat) : Nat := ((s.objs.val[i]?).map (·.child_id.val)).getD 0
def simInLt (c : sim.state.Ctx) (s : sim.state.St) (a b : Nat) : Bool :=
  decide (simKey c.pb.objects a < simKey c.pb.objects b) ||
    (simKey c.pb.objects a == simKey c.pb.objects b && decide (simCid s a < simCid s b))

theorem sim_input_lt_eq (c : sim.state.Ctx) (s : sim.state.St) (a b : Usize) (hinv : SimInv c s)
    (ha : a.val < c.pb.objects.val.length) (hb : b.val < c.pb.objects.val.length) :
    sim.step.input_lt c s a b = ok (simInLt c s a.val b.val) := by
  have ha' : a.val < s.objs.val.length := by rw [hinv.objs_len]; exact ha
  have hb' : b.val < s.objs.val.length := by rw [hinv.objs_len]; exact hb
  have k1 : (c.pb.objects.val[a.val]'ha).h.start = simKey c.pb.objects a.val := by simp [simKey, List.getElem?_eq_getElem ha]
  have k2 : (c.pb.objects.val[b.val]'hb).h.start = simKey c.pb.objects b.val := by simp [simKey, List.getElem?_eq_getElem hb]
  have c1 : (s.objs.val[a.val]'ha').child_id.val = simCid s a.val := by simp [simCid, List.getElem?_eq_getElem ha']
  have c2 : (s.objs.val[b.val]'hb').child_id.val = simCid s b.val := by simp [simCid, List.getElem?_eq_getElem hb']
  unfold sim.step.input_lt simInLt
  simp only [vec_index_eq _ _ ha, vec_index_eq _ _ hb, vec_index_eq _ _ ha', vec_index_eq _ _ hb', bind_ok,
    float.F64.lt, float.F64.eq, k1, k2]
  by_cases h1 : simKey c.pb.objects a.val < simKey c.pb.objects b.val
  · simp [h1]
  · by_cases h2 : (simKey c.pb.objects a.val == simKey c.pb.objects b.val) = true
    · simp [h1, h2]
      rw [← c1, ← c2]
    · simp [h1, h2]

theorem sim_input_inner (c : sim.state.Ctx) (s : sim.state.St) (hinv : SimInv c s) (out : alloc.vec.Vec Usize)
    (x : Usize) (hx : x.val < c.pb.objects.val.length) (hin : ∀ e ∈ out.val, e.val < c.pb.objects.val.length) :
    ∀ (n : Nat) (i : Usize), i.val = n → i.val ≤ out.val.length →
      ∃ r, sim.step.input_order_loop0_loop0 c s.k s.t s.objs s.first_lifetime_update s.next_future s.future_order s.active s.dict_slots s.free_list s.child_counter s.mouse_valid s.mouse s.last_replay s.pressed s.score s.health s.score_rp s.health_rp s.out s.speed s.as_target s.as_recent s.as_seen s.clock_rate s.relax_down s.relax_was_left s.relax_last s.ap_frame s.block_last s.block_idx s.insts s.pools s.br_rot s.theta s.cursor_pos out x i = ok r ∧
        r.val = simInsPos (simInLt c s) (out.val.map (·.val)) x.val n := by
  intro n
  induction n with
  | zero =>
    intro i hi _
    refine ⟨i, ?_, by simp [hi, simInsPos]⟩
    unfold sim.step.input_order_loop0_loop0; rw [loop_unfold]
    have : ¬ i > 0#usize := by scalar_tac
    simp [sim.step.input_order_loop0_loop0.body, this]
  | succ n ih =>
    intro i hi hle
    have hpos : i > 0#usize := by scalar_tac
    obtain ⟨i1, hi1, hi1v0, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := i) (y := 1#usize) (by simp; omega))
    have hi1v : i1.val = n := by rw [hi1v0]; simp; omega
    have hl1 : i1.val < out.val.length := by omega
    have hl2 := hin _ (List.getElem_mem hl1)
    have hlt := sim_input_lt_eq c s x (out.val[i1.val]'hl1) hinv hx hl2
    have hlt' : sim.step.input_lt c ⟨s.k, s.t, s.objs, s.first_lifetime_update, s.next_future, s.future_order, s.active,
        s.dict_slots, s.free_list, s.child_counter, s.mouse_valid, s.mouse, s.last_replay, s.pressed, s.score, s.health,
        s.score_rp, s.health_rp, s.out, s.speed, s.as_target, s.as_recent, s.as_seen, s.clock_rate, s.relax_down,
        s.relax_was_left, s.relax_last, s.ap_frame, s.block_last, s.block_idx, s.insts, s.pools, s.br_rot, s.theta,
        s.cursor_pos⟩ x (out.val[i1.val]'hl1) = ok (simInLt c s x.val (out.val[i1.val]'hl1).val) := hlt
    have hget : (out.val.map (·.val))[n]? = some (out.val[i1.val]'hl1).val := by
      rw [← hi1v]; simp [List.getElem?_eq_getElem hl1]
    by_cases hc : simInLt c s x.val (out.val[i1.val]'hl1).val = true
    · obtain ⟨r, hr, hrv⟩ := ih i1 hi1v (by omega)
      refine ⟨r, ?_, by rw [hrv]; simp [simInsPos, hget, hc]⟩
      unfold sim.step.input_order_loop0_loop0; rw [loop_unfold]
      unfold sim.step.input_order_loop0_loop0 at hr
      rw [show sim.step.input_order_loop0_loop0.body c s.k s.t s.objs s.first_lifetime_update s.next_future s.future_order s.active s.dict_slots s.free_list s.child_counter s.mouse_valid s.mouse s.last_replay s.pressed s.score s.health s.score_rp s.health_rp s.out s.speed s.as_target s.as_recent s.as_seen s.clock_rate s.relax_down s.relax_was_left s.relax_last s.ap_frame s.block_last s.block_idx s.insts s.pools s.br_rot s.theta s.cursor_pos out x i = ok (.cont i1) by
        simp [sim.step.input_order_loop0_loop0.body, hpos, hi1, vec_index_usize_ok _ _ hl1]
        rw [hlt']
        simp [hc]]
      simpa only [bind_ok] using hr
    · refine ⟨i, ?_, by simp [simInsPos, hget, hc, hi]⟩
      unfold sim.step.input_order_loop0_loop0; rw [loop_unfold]
      rw [show sim.step.input_order_loop0_loop0.body c s.k s.t s.objs s.first_lifetime_update s.next_future s.future_order s.active s.dict_slots s.free_list s.child_counter s.mouse_valid s.mouse s.last_replay s.pressed s.score s.health s.score_rp s.health_rp s.out s.speed s.as_target s.as_recent s.as_seen s.clock_rate s.relax_down s.relax_was_left s.relax_last s.ap_frame s.block_last s.block_idx s.insts s.pools s.br_rot s.theta s.cursor_pos out x i = ok (.done i) by
        simp [sim.step.input_order_loop0_loop0.body, hpos, hi1, vec_index_usize_ok _ _ hl1]
        rw [hlt']
        simp [hc]]
      simp only [bind_ok]

theorem sim.step.input_order_refines_list (c : sim.state.Ctx) (s : sim.state.St) (hinv : SimInv c s)
    (hx : ∀ e ∈ s.active.val, e.val < c.pb.objects.val.length) (hl : s.active.val.length < Usize.max) :
    ∃ out, sim.step.input_order c s = ok out ∧
      out.val.map (·.val) = simSortL (simInLt c s) (s.active.val.map (·.val)) := by
  let G : Nat → List Nat → List Nat := fun k L =>
    L.insertIdx (simInsPos (simInLt c s) L (s.active.val[k]!).val L.length) (s.active.val[k]!).val
  obtain ⟨v, hv, hvr⟩ := loop_fold_gen' (fun x => sim.step.input_order_loop0.body c s x.1 x.2) (·.2)
    s.active.val.length (by omega)
    (fun x => (∀ e ∈ x.1.val, e.val < c.pb.objects.val.length) ∧ x.1.val.length = x.2.val) (fun x => x.1.val.map (·.val))
    G (fun y L => y.val.map (·.val) = L)
    (by
      rintro ⟨out, k⟩ ⟨hin, hlen⟩ hk j1 hj1 hj1v
      simp only at hin hlen hk hj1 hj1v ⊢
      have hxk : (s.active.val[k.val]'hk).val < c.pb.objects.val.length := hx _ (List.getElem_mem hk)
      obtain ⟨r, hr, hrv⟩ := sim_input_inner c s hinv out (s.active.val[k.val]'hk) hxk hin out.val.length
        (alloc.vec.Vec.len out) (by simp) (by simp)
      have hrl : r.val ≤ out.val.length := by rw [hrv]; exact sim_simInsPos_le _ _ _ _
      obtain ⟨w, hw, hwv⟩ := sim.step.insert_idx_refines out r (s.active.val[k.val]'hk) hrl (by omega)
      refine ⟨(w, j1), ?_, rfl, ?_, ?_, ?_⟩
      · simp at hr
        simp [sim.step.input_order_loop0.body, vec_lt_len_iff, hk, vec_index_usize_ok _ _ hk, hr, hw, hj1]
      · simp only [hwv, G, getElem!_pos s.active.val k.val hk, hrv, List.map_insertIdx]
        simp
      · intro e he; rw [hwv] at he
        rcases (List.mem_insertIdx hrl).mp he with h | h
        · exact h ▸ hxk
        · exact hin e h
      · rw [hwv]; simp [List.length_insertIdx, hrl, hj1v, hlen]; omega)
    (by
      rintro ⟨out, k⟩ ⟨hin, hlen⟩ hge
      have : ¬ k < alloc.vec.Vec.len s.active := by rw [vec_lt_len_iff]; simp at hge; omega
      refine ⟨out, by simp only [sim.step.input_order_loop0.body, this, ite_false], rfl⟩)
    (alloc.vec.Vec.new Usize, 0#usize) ⟨by simp, by simp⟩ (by simp)
  refine ⟨v, by unfold sim.step.input_order sim.step.input_order_loop0; exact hv, ?_⟩
  rw [hvr]
  simp only [show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero]
  unfold simSortL
  rw [List.foldl_map, foldl_iterR]
  simp [G]

end
section
open OsuImpl OsuModel.Net OsuModel.Sim

def simCidS (S : St) (i : Nat) : Nat := ((S.objs[i]?).map (·.childId)).getD 0

theorem simS_inputOrder (C : Ctx) (S : St) (h : ∀ i ∈ S.active, i < C.pb.objects.size ∧ i < S.objs.size) :
    Sim.inputOrder C S = .ok ((simSortL (fun a b => decide (simKeyS C a < simKeyS C b) ||
      (simKeyS C a == simKeyS C b && decide (simCidS S a < simCidS S b))) S.active.toList).toArray, S) := by
  unfold Sim.inputOrder
  simp only [simM_bind, Sim.st, simM_get, Except.bind]
  simp only [Array.mapM_eq_mapM_toList, simM_map]
  have hl : ∀ i ∈ S.active.toList, i < C.pb.objects.size ∧ i < S.objs.size := fun i hi => h i (by simpa using hi)
  have hmap : ∀ (l : List Nat), (∀ i ∈ l, i < C.pb.objects.size ∧ i < S.objs.size) →
      (l.mapM (fun i => (do let a ← Sim.startOf i; (fun b => (i, a, b.childId)) <$> Sim.ostate i : SimM (Nat × F64 × Nat)))) C S =
        .ok (l.map (fun i => (i, simKeyS C i, simCidS S i)), S) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons i t ih =>
      intro hl'
      have ⟨h1, h2⟩ := hl' i List.mem_cons_self
      simp only [List.mapM_cons, simM_bind, simM_pure]
      rw [simS_startOf _ _ _ h1]
      simp only [simM_map, simS_ostate _ _ _ h2, Except.bind, Except.map]
      rw [ih (fun j hj => hl' j (List.mem_cons_of_mem _ hj))]
      simp [simCidS, h2]
  simp only [bind_pure_comp]
  rw [hmap _ hl]
  simp only [Except.map, simM_pure]
  rw [sim_stableSortBy_eq]
  simp only [List.toList_toArray]
  rw [sim_simSortL_map (fun a b => decide (a.2.1 < b.2.1) || (a.2.1 == b.2.1 && decide (a.2.2 < b.2.2)))
    (fun a b => decide (simKeyS C a < simKeyS C b) || (simKeyS C a == simKeyS C b && decide (simCidS S a < simCidS S b)))
    (fun i => (i, simKeyS C i, simCidS S i)) (fun a b => rfl)]
  simp [Function.comp_def]

end
section
open OsuImpl OsuModel.Net

theorem sim_cidS_st (tn) (s : sim.state.St) (i : Nat) : simCidS (simStS tn s) i = simCid s i := by
  simp only [simCidS, simCid, simStS, abs]
  by_cases h : i < s.objs.val.length
  · simp [h, List.getElem?_eq_getElem h, ostateS]
  · simp [h]

theorem sim.step.input_order_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (hinv : SimInv c s)
    (hx : ∀ e ∈ s.active.val, e.val < c.pb.objects.val.length) (hl : s.active.val.length < Usize.max) :
    ∃ v, sim.step.input_order c s = ok v ∧
      OsuModel.Sim.Sim.inputOrder (simCtxS tn fo c) (simStS tn s) = .ok (abs v, simStS tn s) := by
  obtain ⟨v, hv, hvv⟩ := sim.step.input_order_refines_list c s hinv hx hl
  refine ⟨v, hv, ?_⟩
  have hS : ∀ i ∈ (simStS tn s).active, i < (simCtxS tn fo c).pb.objects.size ∧ i < (simStS tn s).objs.size := by
    intro i hi
    simp [simStS, abs] at hi
    obtain ⟨a, ha, hai⟩ := hi
    have := hx a ha
    rw [← hai]; exact ⟨by simpa using this, by simpa [hinv.objs_len] using this⟩
  rw [simS_inputOrder _ _ hS]
  have hk : (fun a b => decide (simKeyS (simCtxS tn fo c) a < simKeyS (simCtxS tn fo c) b) ||
      (simKeyS (simCtxS tn fo c) a == simKeyS (simCtxS tn fo c) b && decide (simCidS (simStS tn s) a < simCidS (simStS tn s) b)))
      = simInLt c s := by
    funext a b; simp [sim_keyS_ctx, sim_cidS_st, simInLt]
  rw [hk]
  have hids : (simStS tn s).active.toList = s.active.val.map (·.val) := by simp [simStS, abs]
  rw [hids, ← hvv]
  simp [abs]

end
section
open OsuImpl OsuModel.Net

theorem sim_update_order_loop (io : alloc.vec.Vec Usize) :
    ∀ m (k : Usize) (out : alloc.vec.Vec Usize), k.val = m → k.val ≤ io.val.length →
      out.val.length + k.val ≤ io.val.length →
      ∃ w, sim.step.update_order_loop io out k = ok w ∧ w.val = out.val ++ (io.val.take k.val).reverse := by
  intro m
  induction m with
  | zero =>
    intro k out hk _ _
    refine ⟨out, ?_, by simp [hk]⟩
    unfold sim.step.update_order_loop; rw [loop_unfold]
    have : ¬ k > 0#usize := by scalar_tac
    simp [sim.step.update_order_loop.body, this]
  | succ m ih =>
    intro k out hk hle hcap
    have hpos : k > 0#usize := by scalar_tac
    obtain ⟨k1, hk1, hk1v0, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := k) (y := 1#usize) (by simp; omega))
    have hk1v : k1.val = m := by rw [hk1v0]; simp; omega
    have hl1 : k1.val < io.val.length := by omega
    have hpl : out.val.length < Usize.max := by have := io.property; omega
    obtain ⟨w, hw, hwv⟩ := ih k1 (vpush out (io.val[k1.val]'hl1) hpl) hk1v (by omega) (by simp; omega)
    refine ⟨w, ?_, ?_⟩
    · unfold sim.step.update_order_loop; rw [loop_unfold]; dsimp only
      rw [show sim.step.update_order_loop.body io out k = ok (.cont (vpush out (io.val[k1.val]'hl1) hpl, k1)) by
        simp [sim.step.update_order_loop.body, hpos, hk1, vec_index_usize_ok _ _ hl1, vec_push_ok out _ hpl]]
      simp only [bind_ok]
      unfold sim.step.update_order_loop at hw; exact hw
    · rw [hwv]
      simp only [vpush_val, List.append_assoc]
      congr 1
      have e : k.val = k1.val + 1 := by omega
      have key : (io.val.take (k1.val + 1)).reverse = (io.val[k1.val]'hl1) :: (io.val.take k1.val).reverse := by
        rw [List.take_add_one, List.getElem?_eq_getElem hl1]; simp
      rw [e, key]; rfl

theorem sim.step.update_order_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (hinv : SimInv c s)
    (hx : ∀ e ∈ s.active.val, e.val < c.pb.objects.val.length) (hl : s.active.val.length < Usize.max) :
    ∃ v, sim.step.update_order c s = ok v ∧
      OsuModel.Sim.Sim.updateOrder (simCtxS tn fo c) (simStS tn s) = .ok (abs v, simStS tn s) := by
  obtain ⟨io, hio, eio⟩ := sim.step.input_order_refines tn fo c s hinv hx hl
  obtain ⟨w, hw, hwv⟩ := sim_update_order_loop io io.val.length (alloc.vec.Vec.len io) (alloc.vec.Vec.new Usize)
    (by simp) (by simp) (by simp)
  refine ⟨w, by simp only [sim.step.update_order, hio, bind_ok]; exact hw, ?_⟩
  unfold OsuModel.Sim.Sim.updateOrder
  simp only [simM_bind, eio, Except.bind, simM_pure]
  simp [abs, hwv, List.take_of_length_le]

end

end OsuProofs
