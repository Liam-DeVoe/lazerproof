/-
Sim2 abstraction maps (OsuProofs/Sim/Abs.lean style) for the replay-frame and schedule types:
`replay.frames.{Action, ActList, Frame, LegacyFrame}`, `schedule.Step`.
`ActList { items, len }` (at most 3 distinct actions) ↦ the spec's `List Action` = the first `len` items.
-/
import OsuProofs.Sim.AbsState
import OsuModel.Replay.Frames
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

/-! The canonical maps for actions, action lists, frames and steps are the sim core's (Sim/AbsState.lean, D37);
the `s2_*` names below are abbreviations of them (kept for the Sim2 proofs), with bridging lemmas. -/
abbrev s2_actS : replay.frames.Action → OsuModel.Replay.Action := actS
/-- `ActList` ↦ its first `len` items. -/
abbrev s2_actListS : replay.frames.ActList → List OsuModel.Replay.Action := actListS
def s2_frameS (f : replay.frames.Frame) : OsuModel.Replay.Frame :=
  { time := f.time, pos := abs f.pos, actions := s2_actListS f.actions }
theorem s2_actS_eq (x : replay.frames.Action) : s2_actS x = (abs x : OsuModel.Replay.Action) := rfl
theorem s2_actListS_eq (l : replay.frames.ActList) : s2_actListS l = (abs l : List OsuModel.Replay.Action) := rfl
theorem s2_frameS_eq (f : replay.frames.Frame) : s2_frameS f = (abs f : OsuModel.Replay.Frame) := rfl
theorem s2_stepSpec_eq (s : schedule.Step) : stepSpec s = (abs s : OsuModel.Sim.Step) := rfl
@[simp] theorem s2_abs_step (s : schedule.Step) : (abs s : OsuModel.Sim.Step) = stepSpec s := rfl
instance s2_absLegacyFrame : AbsTo replay.frames.LegacyFrame OsuModel.Replay.LegacyFrame :=
  ⟨fun f => { time := f.time, mouseX := f.mouse_x, mouseY := f.mouse_y, buttons := i32S f.buttons }⟩

end OsuProofs
