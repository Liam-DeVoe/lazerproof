/-
Wiring of sim-slice `_refines` theorems into `EvalAssumptions` fields (Eval/E2EBase.lean), json agent.
`abs` on playables uses the default type-name table (`simTnDefault`), the field statements use `ev_tn`; the schedule
leaves only read times (`js_sch_congr`).
-/
import OsuProofs.Eval.E2EBase
import OsuProofs.Sim2.Schedule
import OsuProofs.Sim2.Mods
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl
section
open OsuModel.Net OsuModel.Sim
def js_schF (o : TopObj) : F64 × F64 × F64 × List F64 := (o.h.start, o.h.preempt, o.h.endTime, o.nested.toList.map (·.endTime))
def js_refEndF (l : List (F64 × F64 × F64 × List F64)) : F64 :=
  l.foldl (fun m e => e.2.2.2.foldl F64.max (F64.max m e.2.2.1)) F64.negInf + 1000
theorem js_refEnd_eq (P : Playable) : referenceEnd P = js_refEndF (P.objects.toList.map js_schF) := by
  simp [referenceEnd, js_refEndF, js_schF, List.foldl_map, ← Array.foldl_toList]; rfl
theorem js_gst_eq (P : Playable) : gameplayStartTime P =
    match (P.objects.toList.map js_schF).head? with | some e => e.1 - F64.max 2000 e.2.1 | none => 0 := by
  unfold gameplayStartTime; cases h : P.objects.toList <;> simp_all [js_schF, Array.getElem?_toList, ← Array.getElem?_toList]
theorem js_r0_eq (P : Playable) : referenceStart P =
    (let t := F64.min 0 (gameplayStartTime P)
     match (P.objects.toList.map js_schF).head? with
     | some e => if 0 < P.audioLeadIn then F64.min t (e.1 - P.audioLeadIn) else t | none => t) := by
  unfold referenceStart; cases h : P.objects.toList <;> simp_all [js_schF, ← Array.getElem?_toList]
theorem js_sch_congr (P Q : Playable) (h : P.objects.toList.map js_schF = Q.objects.toList.map js_schF)
    (ha : P.audioLeadIn = Q.audioLeadIn) :
    gameplayStartTime P = gameplayStartTime Q ∧ referenceStart P = referenceStart Q ∧ referenceEnd P = referenceEnd Q := by
  have hg : gameplayStartTime P = gameplayStartTime Q := by rw [js_gst_eq, js_gst_eq, h]
  refine ⟨hg, ?_, by rw [js_refEnd_eq, js_refEnd_eq, h]⟩
  rw [js_r0_eq, js_r0_eq, h, hg, ha]
end

theorem js_playable_sch (tn tn' : Nat → String) (pb : sim.playable.Playable) :
    (playableS tn pb).objects.toList.map js_schF = (playableS tn' pb).objects.toList.map js_schF ∧
    (playableS tn pb).audioLeadIn = (playableS tn' pb).audioLeadIn := by
  simp [playableS, topS, hobjS, js_schF, Function.comp_def]

theorem js_sch_tn (pb : sim.playable.Playable) :
    OsuModel.Sim.gameplayStartTime (playableS ev_tn pb) = OsuModel.Sim.gameplayStartTime (abs pb) ∧
    OsuModel.Sim.referenceStart (playableS ev_tn pb) = OsuModel.Sim.referenceStart (abs pb) ∧
    OsuModel.Sim.referenceEnd (playableS ev_tn pb) = OsuModel.Sim.referenceEnd (abs pb) :=
  js_sch_congr _ _ (js_playable_sch ev_tn simTnDefault pb).1 (js_playable_sch ev_tn simTnDefault pb).2

theorem js_ev_gst : ∀ pb, ∃ x, sim.schedule.gameplay_start_time pb = ok x ∧
    OsuModel.Sim.gameplayStartTime (playableS ev_tn pb) = x := by
  intro pb; obtain ⟨r, hr, e⟩ := sim.schedule.gameplay_start_time_refines pb
  exact ⟨r, hr, by rw [(js_sch_tn pb).1, e]; rfl⟩

theorem js_ev_r0 : ∀ pb, ∃ x, sim.schedule.reference_start pb = ok x ∧
    OsuModel.Sim.referenceStart (playableS ev_tn pb) = x := by
  intro pb; obtain ⟨r, hr, e⟩ := sim.schedule.reference_start_refines pb
  exact ⟨r, hr, by rw [(js_sch_tn pb).2.1, e]; rfl⟩

theorem js_ev_endT : ∀ pb, ∃ x, sim.schedule.reference_end pb = ok x ∧
    OsuModel.Sim.referenceEnd (playableS ev_tn pb) = x := by
  intro pb; obtain ⟨r, hr, e⟩ := sim.schedule.reference_end_refines pb
  exact ⟨r, hr, by rw [(js_sch_tn pb).2.2, e]; rfl⟩

theorem js_ev_frameTimes : ∀ fs : Slice replay.frames.Frame, ∃ r, sim.schedule.frame_times fs = ok r ∧
    ((fs.val.map abs).toArray : Array OsuModel.Replay.Frame).map (·.time) = r.val.toArray := by
  intro fs; obtain ⟨r, hr, e⟩ := sim.schedule.frame_times_refines fs
  refine ⟨r, hr, ?_⟩
  have e' := e; simp only [abs, List.map_id'] at e'
  simpa [abs] using e'

theorem js_kindS (k : sim.schedule.ScheduleKind) : ev_kindS k = abs k := by cases k <;> rfl

theorem js_rel_flip {α β} (f : α → β) (x : Except String β) (r : core.result.Result α sim.err.SimErr)
    (h : s2_rel f x r) : ev_eRel f r x := by
  cases x <;> cases r <;> simp_all [s2_rel, ev_eRel]

theorem js_ev_references (h64 : System.Platform.numBits = 64) : ∀ k r0 e (ft : Slice float.F64),
    ft.val.length + 2 ≤ Usize.max → ∃ r, sim.schedule.references k r0 e ft = ok r ∧
    ev_eRel (fun v => v.val.toArray) r (OsuModel.Sim.references (ev_kindS k) r0 e ft.val.toArray) := by
  intro k r0 e ft hn
  obtain ⟨r, hr, e'⟩ := sim.schedule.references_refines h64 k r0 e ft hn
  refine ⟨r, hr, ?_⟩
  have := js_rel_flip _ _ _ e'
  rw [js_kindS]; simpa [abs] using this

theorem js_ev_simulateSteps (h64 : System.Platform.numBits = 64) : ∀ (refs ft : Slice float.F64) gst,
    refs.val.length * 100000000 + 4 < 2^61 → ∃ r, sim.schedule.simulate_steps refs ft gst = ok r ∧
    ev_eRel (fun v => (v.val.map abs).toArray) r (OsuModel.Sim.simulateSteps refs.val.toArray ft.val.toArray gst) := by
  intro refs ft gst hn
  obtain ⟨r, hr, e'⟩ := sim.schedule.simulate_steps_refines h64 refs ft gst hn
  refine ⟨r, hr, ?_⟩
  have := js_rel_flip _ _ _ e'
  simpa [abs] using this

theorem js_ev_dynInit : ∀ d, ∃ r, sim.mods.dyn_rate_initial_speed d = ok r ∧
    ev_eRel id r (abs d : OsuModel.Sim.DynRate).initialSpeed := by
  intro d; refine ⟨_, sim.mods.dyn_rate_initial_speed_refines d, ?_⟩
  cases (abs d : OsuModel.Sim.DynRate).initialSpeed <;> simp [exceptI, ev_eRel]

end OsuProofs
