/-
e2e2: every frame decoded by `replay::frames::decode` has at most 3 actions (input_phase's `frame actions len ≤ 3`
context premise; the abstraction `actListS` truncates, so this is a Rust-side fact).
-/
import OsuProofs.Sim2.FramesParse
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem e2_cf_acts (f : replay.frames.LegacyFrame) : (s2_cf f).actions.len.val ≤ 3 :=
  (replay.frames.convert_frame_refines f).choose_spec.2.2

theorem e2_decode_acts (t : Slice U32) (v : I64) (ht : ValidStr t) (hn : t.val.length < 2^62)
    (fs : alloc.vec.Vec replay.frames.Frame) (h : replay.frames.decode t v = ok (.Ok fs)) :
    ∀ f ∈ fs.val, f.actions.len.val ≤ 3 := by
  have hoff : ∃ off : I64, (if v < 5#i64 then ok 24#i64 else ok 0#i64 : Result I64) = ok off := by
    by_cases h : v.val < 5
    · exact ⟨24#i64, by simp [show v < 5#i64 by scalar_tac]⟩
    · exact ⟨0#i64, by simp [show ¬ v < 5#i64 by scalar_tac]⟩
  obtain ⟨off, hoff1⟩ := hoff
  obtain ⟨r, hr, -, -⟩ := replay.frames.parse_legacy_frames_refines t ht hn off
  cases r with
  | Err e =>
    have h2 : replay.frames.decode t v = ok (.Err e) := by
      unfold replay.frames.decode; rw [hoff1, bind_ok, hr, bind_ok]
    rw [h2] at h; cases Result.ok_injective h
  | Ok fs0 =>
    obtain ⟨fixed, hfx, -, -⟩ := replay.frames.fixup_frames_refines fs0
    obtain ⟨out, hout, eout⟩ := s2_decode_loop fixed _ (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
    have h2 : replay.frames.decode t v = ok (.Ok out) := by
      unfold replay.frames.decode; rw [hoff1, bind_ok, hr, bind_ok]; simp [hfx, hout]
    rw [h2] at h
    have := Result.ok_injective h; cases this
    intro f hf
    rw [eout] at hf
    simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at hf
    rcases List.mem_append.1 hf with hf | hf
    · simp [alloc.vec.Vec.new] at hf
    · obtain ⟨g, -, rfl⟩ := List.mem_map.1 hf
      exact e2_cf_acts g
end OsuProofs
