/-
`sim::step` replay-input pieces (Rust) refine `OsuModel.Sim.Sim`: `replay_state_diff` (`replayStateDiff`),
`trigger_released` (`triggerReleased`); uses the `ActList` lemmas of Sim2/Frames. Lake-only (not in Sim/ORDER).
-/
import OsuProofs.Sim.InitState
import OsuProofs.Sim2.Frames
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem sim_actList_nil_iff (l : replay.frames.ActList) (hl : l.len.val ≤ 3) :
    (abs l : List OsuModel.Replay.Action) = [] ↔ l.len.val = 0 := by
  have h3 := s2_items_len l
  simp only [abs, actListS, List.map_eq_nil_iff, List.take_eq_nil_iff]
  constructor
  · rintro (h | h); exact h; rw [h] at h3; simp at h3
  · intro h; exact Or.inl h

theorem simS_rsd (L C : List OsuModel.Replay.Action) (h : L ≠ []) :
    OsuModel.Sim.Sim.replayStateDiff (some L) C = (if C.isEmpty then (L, []) else if L == C then ([], [])
      else (L.filter (!C.contains ·), C.filter (!L.contains ·))) := by
  cases L with
  | nil => exact absurd rfl h
  | cons x t => rfl

theorem sim.step.replay_state_diff_refines (last : Option replay.frames.ActList) (cur : replay.frames.ActList)
    (hl : ∀ l, last = some l → l.len.val ≤ 3) (hc : cur.len.val ≤ 3) :
    ∃ r, sim.step.replay_state_diff last cur = ok r ∧ r.1.len.val ≤ 3 ∧ r.2.len.val ≤ 3 ∧
      OsuModel.Sim.Sim.replayStateDiff (last.map (fun l => (abs l : List OsuModel.Replay.Action)))
        (abs cur) = ((abs r.1 : List OsuModel.Replay.Action), (abs r.2 : List OsuModel.Replay.Action)) := by
  have he := s2_empty_val
  have hE : (abs replay.frames.ACTLIST_EMPTY : List OsuModel.Replay.Action) = [] := s2_abs_empty
  cases last with
  | none =>
    refine ⟨(replay.frames.ACTLIST_EMPTY, cur), by simp [sim.step.replay_state_diff], by simp [he.2], hc, ?_⟩
    simp [OsuModel.Sim.Sim.replayStateDiff, hE]
  | some l =>
    have hl3 := hl l rfl
    by_cases h0 : l.len.val = 0
    · have h0' : l.len = 0#usize := UScalar.eq_of_val_eq (by simpa using h0)
      refine ⟨(replay.frames.ACTLIST_EMPTY, cur), by simp [sim.step.replay_state_diff, h0'], by simp [he.2], hc, ?_⟩
      have : (abs l : List OsuModel.Replay.Action) = [] := (sim_actList_nil_iff l hl3).mpr h0
      simp [OsuModel.Sim.Sim.replayStateDiff, hE, this]
    · have h0' : ¬ l.len = 0#usize := fun e => h0 (by rw [e]; rfl)
      have hlne : (abs l : List OsuModel.Replay.Action) ≠ [] := fun e => h0 ((sim_actList_nil_iff l hl3).mp e)
      by_cases h1 : cur.len.val = 0
      · have h1' : cur.len = 0#usize := UScalar.eq_of_val_eq (by simpa using h1)
        refine ⟨(l, replay.frames.ACTLIST_EMPTY), by simp [sim.step.replay_state_diff, h0', h1'], hl3, by simp [he.2], ?_⟩
        have : (abs cur : List OsuModel.Replay.Action) = [] := (sim_actList_nil_iff cur hc).mpr h1
        simp only [Option.map_some, simS_rsd _ _ hlne, this, List.isEmpty_nil, if_true, hE]
      · have h1' : ¬ cur.len = 0#usize := fun e => h1 (by rw [e]; rfl)
        have hcne : (abs cur : List OsuModel.Replay.Action) ≠ [] := fun e => h1 ((sim_actList_nil_iff cur hc).mp e)
        have heq := replay.frames.act_eq_refines l cur hl3 hc
        by_cases hq : ((abs l : List OsuModel.Replay.Action) == abs cur) = true
        · refine ⟨(replay.frames.ACTLIST_EMPTY, replay.frames.ACTLIST_EMPTY), by
            simp [sim.step.replay_state_diff, h0', h1', heq, hq], by simp [he.2], by simp [he.2], ?_⟩
          have hce : (abs cur : List OsuModel.Replay.Action).isEmpty = false := by
            cases h : (abs cur : List OsuModel.Replay.Action) <;> simp_all
          simp only [Option.map_some, simS_rsd _ _ hlne, hce, Bool.false_eq_true, if_false, hq, if_true, hE]
        · obtain ⟨m1, hm1, lm1, em1⟩ := replay.frames.act_minus_refines l cur hl3 hc
          obtain ⟨m2, hm2, lm2, em2⟩ := replay.frames.act_minus_refines cur l hc hl3
          refine ⟨(m1, m2), by simp [sim.step.replay_state_diff, h0', h1', heq, hq, hm1, hm2], lm1, lm2, ?_⟩
          have hce : (abs cur : List OsuModel.Replay.Action).isEmpty = false := by
            cases h : (abs cur : List OsuModel.Replay.Action) <;> simp_all
          simp only [Option.map_some, simS_rsd _ _ hlne, hce, Bool.false_eq_true, if_false, hq, em1, em2]
theorem sim.step.trigger_released_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (a : replay.frames.Action)
    (hp : s.pressed.len.val ≤ 3) :
    ∃ s', sim.step.trigger_released s a = ok s' ∧ s'.pressed.len.val ≤ 3 ∧
      OsuModel.Sim.Sim.triggerReleased (abs a) (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') := by
  obtain ⟨r, hr, lr, er⟩ := replay.frames.act_remove_refines s.pressed a hp
  refine ⟨{ s with pressed := r }, by simp [sim.step.trigger_released, hr], lr, ?_⟩
  simp only [OsuModel.Sim.Sim.triggerReleased, simM_modify]
  congr 2
  simp only [simStS]
  congr 1
  have : (abs r : List OsuModel.Replay.Action) = actListS r := rfl
  rw [← this, er]
  simp [abs]
end OsuProofs
