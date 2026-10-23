/-
sim5: `sim::scoring::legacy_nested` (the nested-object loop of one `computeLegacyDrainRate` pass) refines the
spec's inner `for n in o.nested do …` over `(currentHp, currentHpUncapped)`, in the form the spec loop takes
inside `computeLegacyDrainRate` (cf. `hN` in Sim/LegacyDrain's `simS_computeLegacyDrainRate`).
-/
import OsuProofs.Sim.LegacyDrain
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem sim.scoring.legacy_nested_refines (tn : Nat → String) (pb : sim.playable.Playable) (i : Usize)
    (hp mult c u : F64) (hi : i.val < pb.objects.val.length) :
    ∃ r, sim.scoring.legacy_nested pb i hp mult c u = ok r ∧
      forIn (m := Except String) (topS tn (pb.objects.val[i.val]'hi)).nested (c, u) (fun n (__s : F64 × F64) =>
        if ((topS tn (pb.objects.val[i.val]'hi)).h.kind == OsuModel.Sim.Kind.spinner &&
            n.kind == OsuModel.Sim.Kind.spinnerBonusTick) = true then
          pure (ForInStep.yield (__s.1, __s.2))
        else if ((topS tn (pb.objects.val[i.val]'hi)).h.kind != OsuModel.Sim.Kind.slider &&
            (topS tn (pb.objects.val[i.val]'hi)).h.kind != OsuModel.Sim.Kind.spinner) = true then
          pure (ForInStep.yield (__s.1, __s.2))
        else pure (ForInStep.yield
          (F64.max 0 (F64.min 1 (__s.1 + OsuModel.Sim.legacyHealthIncrease hp mult n.kind n.maxResult)),
            __s.2 + OsuModel.Sim.legacyHealthIncrease hp mult n.kind n.maxResult))) = .ok r := by
  set o := pb.objects.val[i.val]'hi with ho
  refine ⟨simLNest hp mult o.h.kind o.nested.val (c, u), ?_, simS_lnest hp mult o.h.kind o.nested.val (c, u) tn⟩
  have := sim_lnest_loop o.nested hp mult o.h.kind _ c u 0#usize rfl (by simp)
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at this
  simp [sim.scoring.legacy_nested, sim.scoring.legacy_nested_loop, vec_index_eq _ _ hi, ← ho, this]

end OsuProofs
