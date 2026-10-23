/-
`js_mk_ctx_full` (json agent): `sim.step.mk_ctx_refines` with its `hAP` / `hPE` hypotheses discharged by
`sim.step.ap_frames_of_refines` (Eval/JsonApFrames) and `sim.step.preceding_end_times_refines` (Eval/JsonPrecEnd),
under the named size bounds `ev_mkBounds`.
-/
import OsuProofs.Eval.JsonPrecEnd
import OsuProofs.Eval.JsonApFrames
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem js_wR_len (h : sim.playable.HObj) : (js_wR h).length ≤ 1 := by
  unfold js_wR; split <;> simp

theorem js_flat_wR_len : ∀ (l : List sim.playable.HObj), (l.flatMap js_wR).length ≤ l.length := by
  intro l; induction l with
  | nil => simp
  | cons x l ih => have := js_wR_len x; simp only [List.flatMap_cons, List.length_append, List.length_cons]; omega

theorem js_flat_wtsR_len : ∀ (l : List sim.playable.TopObj),
    (l.flatMap js_wtsR).length ≤ (l.map (fun o => o.nested.val.length + 1)).sum := by
  intro l; induction l with
  | nil => simp
  | cons x l ih =>
    have h1 := js_wR_len x.h; have h2 := js_flat_wR_len x.nested.val
    simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons, js_wtsR]; omega

theorem js_mem_le_sum : ∀ (l : List sim.playable.TopObj) o, o ∈ l →
    o.nested.val.length + 1 ≤ (l.map (fun o => o.nested.val.length + 1)).sum := by
  intro l; induction l with
  | nil => simp
  | cons x l ih =>
    intro o ho; simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 ho with rfl | h
    · omega
    · have := ih o h; omega

theorem js_len_le_sum : ∀ (l : List sim.playable.TopObj), l.length ≤ (l.map (fun o => o.nested.val.length + 1)).sum := by
  intro l; induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

/-- `mk_ctx` refines `mkCtx` (relation part of `EvalAssumptions.mkCtx`) under `ev_mkBounds`; no open callees. -/
theorem js_mk_ctx_full (h64 : System.Platform.numBits = 64) (env : sim.geometry.Env) (c : sim.mods.Config)
    (pb : sim.playable.Playable) (fs : alloc.vec.Vec replay.frames.Frame) (k : sim.schedule.ScheduleKind)
    (C : OsuModel.Sim.Config) (hc : ev_cfgRel c C) (hB : ev_mkBounds pb fs) :
    ∃ r, sim.step.mk_ctx env c pb fs k = ok r ∧
    (match r, OsuModel.Sim.mkCtx (abs env) C (playableS ev_tn pb) (fs.val.map abs).toArray (ev_kindS k) with
     | .Ok ctx, .ok CTX => ctx.cfg = c ∧ CTX.cfg = C ∧ ctx.pb = pb ∧ CTX.pb = playableS ev_tn pb ∧ ev_ctxRel ctx CTX
     | .Err _, .error _ => True
     | _, _ => False) := by
  obtain ⟨hfs, hob, hsum, hbr, hsd, -⟩ := hB
  have hmax : (2:Nat)^62 < Usize.max := by simp [Usize.max, h64, Usize.numBits]
  exact sim.step.mk_ctx_refines h64 env c pb fs k C hc hfs (by omega) hbr
    (sim.step.ap_frames_of_refines h64 pb c hob hsd)
    (sim.step.preceding_end_times_refines h64 pb (by have := js_flat_wtsR_len pb.objects.val; omega)
      (fun o ho => by have := js_mem_le_sum _ o ho; omega)
      (by have := js_len_le_sum pb.objects.val; omega))

end OsuProofs
