/-
The step invariant for `sim::step::step_once` (simcore2, D67/D70): instances of the transform-law classes for the
concrete transform predicate `s2_tfOk`, and the budget bookkeeping.
-/
import OsuProofs.Sim.StepLoop
import OsuProofs.Sim.UpdateDho
import OsuProofs.Sim.Lifetime
import OsuProofs.Sim7.Update
import OsuProofs.Sim4.SpinnerMain
import OsuProofs.Sim3.SD_Play2
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- `update_transforms` law for `s2_tfOk` (update_dho's `U`) -/
theorem sc2_tfU_s2 : simTfU s2_tfOk := ⟨fun b o time hP => s7_ut_s2 b o time false hP⟩

/-- position/new-instance laws for `s2_tfOk` (became_alive's `X`) -/
theorem sc2_tfX_s2 : simTfX s2_tfOk where
  pos b a a' h hP := by
    have e : (abs a' : OsuModel.Sim.TObj).trackers = (abs a : OsuModel.Sim.TObj).trackers := by
      show (a'.trackers.val.map abs).toArray = (a.trackers.val.map abs).toArray
      rw [h.trackers]
    unfold s2_tfOk s2_tfOkS at *
    rw [e]; exact hP
  new b hb := by
    have e : ∀ t : sim.transforms.TObj, t.trackers = alloc.vec.Vec.new _ → s2_tfOk b t := by
      intro t ht
      have e0 : (abs t : OsuModel.Sim.TObj).trackers = #[] := by
        show (t.trackers.val.map abs).toArray = #[]
        rw [ht]; rfl
      unfold s2_tfOk s2_tfOkS
      rw [e0]
      refine ⟨by simp; omega, fun tk htk => by simp at htk⟩
    exact ⟨e _ rfl, e _ rfl⟩

/-! ## D70: the run budget, stated on spec values (computable; `#eval`-checkable on the corpus)

Per step only `update_dho` consumes transform slack: two units of `n+n+4` per object in `updateOrder` (one for the
first-load `updateStateFromResult`, one more for a slider head), and `completed_spins` grows by ≤ 2·10^6 per update.
`updateOrder` is the active list after the lifetime phase, so the whole run needs `runBudgetNeed C S0` updates. -/

/-- the step prefix before the per-object updates -/
def sc2PreDho : OsuModel.Sim.SimM Unit := do
  OsuModel.Sim.Sim.processorsPhase
  OsuModel.Sim.Sim.inputPhase
  OsuModel.Sim.Sim.playfieldUpdate
  OsuModel.Sim.Sim.lifetimeUpdate

/-- updates needed by the steps `ks` from spec state `S` (the active-list size after each lifetime phase) -/
def sc2UnitsRun (C : OsuModel.Sim.Ctx) : List (Nat × OsuModel.Sim.Step) → OsuModel.Sim.St → Nat
  | [], _ => 0
  | (k, stp) :: rest, S =>
    let S1 := { S with k := k, t := stp.time }
    match sc2PreDho C S1 with
    | .error _ => 0
    | .ok (_, SL) => SL.active.size +
      match OsuModel.Sim.Sim.stepOnce C S1 with
      | .ok (_, S2) => sc2UnitsRun C rest S2
      | .error _ => 0

/-- the number of per-object updates of the whole spec run from `S0` -/
def runBudgetNeed (C : OsuModel.Sim.Ctx) (S0 : OsuModel.Sim.St) : Nat :=
  sc2UnitsRun C ((List.range C.steps.size).zip C.steps.toList) S0

/-- spec-side custom-state cost of the visibility mods (= `s3b_csCostFrom vis_mods 0` under `abs`) -/
def sc2VmCostS : OsuModel.Sim.VisMod → Nat
  | .classicEarlyFade => 1 | .scaleTween _ => 2 | .spinIn => 5 | .targetPractice => 2 | .hidden _ => 1
  | .transform => 2 | .wiggle _ => 2 ^ 31 + 2 ^ 25 | .inert => 0

def sc2CsCostS (cfg : OsuModel.Sim.Config) : Nat := (cfg.visMods.toList.map sc2VmCostS).sum

/-- RunBudget (D67a/c, D70) on spec values: U updates, 2 transform units each, plus the one-time became_alive
charge per object and the unjudged-judgement slack; completed_spins headroom -/
def RunBudgetS (C : OsuModel.Sim.Ctx) (S0 : OsuModel.Sim.St) : Prop :=
  let U := runBudgetNeed C S0
  let n := sc2CsCostS C.cfg
  let objs := C.pb.objects.size
  let unj := (C.pb.objects.toList.map (fun o => o.nested.size + 1)).sum
  (2 * U + unj + 1) * (n + n + 4) + objs * (4 * n + 8) + 1 < 2 ^ 64 - 1 ∧ (U + 1) * 2000000 ≤ 2 ^ 54

/-- the corpus check: `runBudgetOkE env cfg pb frames kind = .ok true` -/
def runBudgetOkE (env : OsuModel.Sim.Env) (cfg : OsuModel.Sim.Config) (pb : OsuModel.Sim.Playable)
    (frames : Array OsuModel.Replay.Frame) (kind : OsuModel.Sim.ScheduleKind) : Except String (Nat × Bool) := do
  let C ← OsuModel.Sim.mkCtx env cfg pb frames kind
  let S0 ← OsuModel.Sim.initState cfg pb C.smax.initWithoutMods
  let U := runBudgetNeed C S0
  let n := sc2CsCostS C.cfg
  let objs := C.pb.objects.size
  let unj := (C.pb.objects.toList.map (fun o => o.nested.size + 1)).sum
  return (U, decide ((2 * U + unj + 1) * (n + n + 4) + objs * (4 * n + 8) + 1 < 2 ^ 64 - 1 ∧ (U + 1) * 2000000 ≤ 2 ^ 54))

end OsuProofs
