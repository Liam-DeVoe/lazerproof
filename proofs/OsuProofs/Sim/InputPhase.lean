/-
`sim::step` input-phase pieces (Rust) refine `OsuModel.Sim.Sim` (Step.lean): `interpolate`, `receptorCanBeHit`,
`replayPosition`.
-/
import OsuProofs.Sim.InputOrder
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net
namespace OsuProofs
open OsuImpl OsuModel.Net

theorem sim.step.interpolate_refines (time : F64) (v1 v2 : sim.basic.Vec2) (t0 t1 : F64) :
    ∃ r, sim.step.interpolate time v1 v2 t0 t1 = ok r ∧
      OsuModel.Sim.Sim.interpolate (abs time) (abs v1) (abs v2) (abs t0) (abs t1) = abs r := by
  unfold sim.step.interpolate OsuModel.Sim.Sim.interpolate
  simp only [float.F64.sub, float.F64.to_f32, sim_basic_F32_0, float.F32.eq, float.F32.div, bind_ok, abs, id]
  have hz : OsuModel.Sim.f32zero = (0 : F32) := rfl
  have ea : ∀ a b : OsuModel.Sim.Vec2, a + b = ⟨a.x + b.x, a.y + b.y⟩ := fun _ _ => rfl
  have es : ∀ a b : OsuModel.Sim.Vec2, a - b = ⟨a.x - b.x, a.y - b.y⟩ := fun _ _ => rfl
  by_cases h1 : (F64.toF32 (t1 - t0) == 0) = true <;> by_cases h2 : (F64.toF32 (time - t0) == 0) = true <;>
    simp [h1, h2, hz, sim.basic.Vec2.add, sim.basic.Vec2.sub, sim.basic.Vec2.scale, OsuModel.Sim.Vec2.scale,
      OsuModel.Sim.Vec2.add, OsuModel.Sim.Vec2.sub, ea, es]

theorem sim.step.receptor_can_be_hit_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (r : sim.step.Ref)
    (hr : simSRefOk s r) :
    ∃ b, sim.step.receptor_can_be_hit c s r = ok b ∧
      OsuModel.Sim.Sim.receptorCanBeHit (abs r) (simCtxS tn fo c) (simStS tn s) = .ok (b, simStS tn s) := by
  obtain ⟨ht, hn⟩ := hr
  obtain ⟨a, ha, ea⟩ := sim.step.all_judged_refines tn fo c s r.top ht
  obtain ⟨j, hj, ej⟩ := sim.step.judged_refines tn fo c s r ⟨ht, hn⟩
  unfold sim.step.receptor_can_be_hit OsuModel.Sim.Sim.receptorCanBeHit
  have hcfg : (simCtxS tn fo c).cfg.classicHeadBlock = c.cfg.classic_head_block := rfl
  by_cases h1 : r.nested < 0#i64
  · have h0 : r.nested.val < 0 := by scalar_tac
    refine ⟨!a, by simp [h1, ha], ?_⟩
    simp [simM_bind, OsuModel.Sim.Sim.ctx, simM_read, Except.bind, Except.map, abs, h0, ea]
  · have h0 : ¬ r.nested.val < 0 := by scalar_tac
    cases hc : c.cfg.classic_head_block
    · refine ⟨!j, by simp [h1, hc, hj], ?_⟩
      simp [simM_bind, OsuModel.Sim.Sim.ctx, simM_read, Except.bind, Except.map, abs, h0, hcfg, hc]
      simp [abs] at ej; simp [ej, Except.map]
    · refine ⟨!a, by simp [h1, hc, ha], ?_⟩
      simp [simM_bind, OsuModel.Sim.Sim.ctx, simM_read, Except.bind, Except.map, abs, h0, hcfg, hc, ea]

theorem sim_slice_index_nat {α} (v : Slice α) (x : Usize) (n : Nat) (e : x.val = n) (h : n < v.val.length) :
    Slice.index_usize v x = ok (v.val[n]'h) := by
  subst e; exact slice_index_ok v x h

/-- `replayPosition` (frame indices are `≥ -1`: `frameIndex` of a schedule step) -/
theorem sim.step.replay_position_refines (frames : Slice replay.frames.Frame) (idx : I64) (t : F64)
    (hne : 0 < frames.val.length) (hlen : frames.val.length < 2 ^ 63) (hi0 : -1 ≤ idx.val) (hi1 : idx.val < (frames.val.length : Int)) :
    ∃ v, sim.step.replay_position frames idx t = ok v ∧
      ∀ C S, OsuModel.Sim.Sim.replayPosition (frames.val.map (fun f => (abs f : OsuModel.Replay.Frame))).toArray
        idx.val (abs t) C S = .ok (abs v, S) := by
  have hlv : (UScalar.hcast .I64 (Slice.len frames)).val = (frames.val.length : Int) := by
    rw [sim_usize_to_i64 _ (by scalar_tac)]; simp
  obtain ⟨last, hl, elast⟩ : ∃ z, UScalar.hcast .I64 (Slice.len frames) - 1#i64 = ok z ∧ z.val = frames.val.length - 1 := by
    have := I64.sub_spec (x := UScalar.hcast .I64 (Slice.len frames)) (y := 1#i64) (by rw [hlv]; scalar_tac)
      (by rw [hlv]; scalar_tac)
    obtain ⟨z, hz, hv⟩ := eq_ok_of_spec this
    exact ⟨z, hz, by simp [hlv] at hv; omega⟩
  obtain ⟨i2, h2, e2⟩ : ∃ z, idx + 1#i64 = ok z ∧ z.val = idx.val + 1 := by
    have := I64.add_spec (x := idx) (y := 1#i64) (by scalar_tac) (by scalar_tac)
    obtain ⟨z, hz, hv⟩ := eq_ok_of_spec this
    exact ⟨z, hz, by simpa using hv⟩
  have hcastU : ∀ x : I64, 0 ≤ x.val → x.val < frames.val.length → (IScalar.hcast .Usize x).val = x.val.toNat := by
    intro x h0 h1
    apply sim_i64_cast_usize x h0
    have := frames.property; omega
  have hna : (max 0 idx.val).toNat < frames.val.length := by omega
  have hnb : (min (idx.val + 1) (frames.val.length - 1 : Int)).toNat < frames.val.length := by omega
  obtain ⟨r, hr, er⟩ := sim.step.interpolate_refines t (frames.val[(max 0 idx.val).toNat]'hna).pos
    (frames.val[(min (idx.val + 1) (frames.val.length - 1 : Int)).toNat]'hnb).pos
    (frames.val[(max 0 idx.val).toNat]'hna).time
    (frames.val[(min (idx.val + 1) (frames.val.length - 1 : Int)).toNat]'hnb).time
  refine ⟨r, ?_, ?_⟩
  · unfold sim.step.replay_position
    simp only [lift, bind_ok, hl, h2]
    by_cases ha : idx < 0#i64
    · have ha' : idx.val < 0 := by scalar_tac
      by_cases hb : i2 < last
      · have hb' : i2.val < last.val := by scalar_tac
        simp only [ha, hb, if_true, bind_ok]
        rw [sim_slice_index_nat frames _ _ (by rw [hcastU _ (by simp) (by simp; omega)]; simp; omega) hna]
        rw [sim_slice_index_nat frames _ _ (by rw [hcastU _ (by omega) (by omega)]; omega) hnb]
        simp only [bind_ok]; exact hr
      · have hb' : ¬ i2.val < last.val := by scalar_tac
        simp only [ha, hb, if_true, if_false, bind_ok]
        rw [sim_slice_index_nat frames _ _ (by rw [hcastU _ (by simp) (by simp; omega)]; simp; omega) hna]
        rw [sim_slice_index_nat frames _ _ (by rw [hcastU _ (by omega) (by omega)]; omega) hnb]
        simp only [bind_ok]; exact hr
    · have ha' : ¬ idx.val < 0 := by scalar_tac
      by_cases hb : i2 < last
      · have hb' : i2.val < last.val := by scalar_tac
        simp only [ha, hb, if_true, if_false, bind_ok]
        rw [sim_slice_index_nat frames _ _ (by rw [hcastU _ (by omega) (by omega)]; omega) hna]
        rw [sim_slice_index_nat frames _ _ (by rw [hcastU _ (by omega) (by omega)]; omega) hnb]
        simp only [bind_ok]; exact hr
      · have hb' : ¬ i2.val < last.val := by scalar_tac
        simp only [ha, hb, if_false, bind_ok]
        rw [sim_slice_index_nat frames _ _ (by rw [hcastU _ (by omega) (by omega)]; omega) hna]
        rw [sim_slice_index_nat frames _ _ (by rw [hcastU _ (by omega) (by omega)]; omega) hnb]
        simp only [bind_ok]; exact hr
  · intro C S
    have hna' : (max 0 idx.val).toNat < (frames.val.map (fun f => (abs f : OsuModel.Replay.Frame))).toArray.size := by
      simpa using hna
    have hnb' : (min (idx.val + 1) ((frames.val.map (fun f => (abs f : OsuModel.Replay.Frame))).toArray.size - 1 : Int)).toNat <
        (frames.val.map (fun f => (abs f : OsuModel.Replay.Frame))).toArray.size := by
      simpa using hnb
    unfold OsuModel.Sim.Sim.replayPosition
    simp only [simM_bind, OsuModel.Sim.Sim.getA, hna', hnb', _root_.dite_true, simM_pure, Except.bind]
    simp only [List.getElem_toArray, List.getElem_map, List.size_toArray, List.length_map]
    rw [← er]; rfl
end OsuProofs
