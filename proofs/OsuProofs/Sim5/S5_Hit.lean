/-
sim5: `sim::step::handle_hit_sto` (`StartTimeOrderedHitPolicy.HandleHit`, the start-time-ordered arm of
`handleHit`) refines `Sim.handleHit` whenever its caller `handle_hit` would call it (policy StartTimeOrdered and
`circle_like r`). Obtained from the fuel induction of Sim/ApplyResult (`sim_ar_all` via `handle_hit_refines`).
-/
import OsuProofs.Sim.ApplyResult
set_option maxHeartbeats 400000  -- = the shared REPL default
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem sim.step.handle_hit_sto_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c)
    (hCS : simCSH P n tn fo c)
    (s : sim.state.St) (fuel : U64) (r : sim.step.Ref) (e : Nat)
    (hI : SimARInv tn fo P b0 n c s e 0 0) (hr : simRefOk c r)
    (hp : c.cfg.policy = .StartTimeOrdered) (hcl : sim.step.circle_like c r = ok true) :
    ∃ res s', sim.step.handle_hit_sto c s fuel r = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.handleHit fuel.val (abs r) (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0) := by
  have heq : sim.step.handle_hit c s fuel r = sim.step.handle_hit_sto c s fuel r := by
    rw [sim.step.handle_hit.eq_def]
    simp only [hp, hcl, bind_ok, if_true]
  rw [← heq]
  exact sim.step.handle_hit_refines tn fo E b0 n c hC hCS s fuel r e hI hr

end OsuProofs
