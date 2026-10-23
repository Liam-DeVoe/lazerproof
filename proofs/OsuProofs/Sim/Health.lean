/-
`sim::scoring` health processor (Rust) refines `OsuModel.Sim` Scoring (`HealthSt.increaseFor`, drain, periods).
-/
import OsuProofs.Sim.Scoring
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

theorem sim_u64_eq_iff (x y : U64) : x = y ↔ x.val = y.val :=
  ⟨fun e => by rw [e], fun e => UScalar.eq_of_val_eq e⟩

/-- closes the leftover `∃ cr, …` goals of `sim_increase_for_main` (the combo result is 0, 1 or 2 there). -/
macro "sim_cr_close" : tactic => `(tactic| first
  | omega | exact ⟨1#u64, rfl⟩ | exact ⟨0#u64, rfl⟩ | exact ⟨2#u64, rfl⟩
  | (refine ⟨1#u64, ?_, ?_⟩ <;> simp_all <;> omega) | (refine ⟨0#u64, ?_, ?_⟩ <;> simp_all <;> omega)
  | (refine ⟨2#u64, ?_, ?_⟩ <;> simp_all <;> omega))

theorem sim_increase_for_main (h : sim.scoring.HealthSt) (c : sim.scoring.HealthCfg) (k : sim.playable.Kind)
    (mx mn ty : sim.basic.HitResult) (ta et tof : F64) (nc lc : Bool) (hl : c.legacy = false) :
    ∃ cr inc, sim.scoring.increase_for h c ⟨k, mx, mn, ty, ta, et, tof, nc, lc⟩ false = ok (cr, inc) ∧
      OsuModel.Sim.HealthSt.increaseFor (abs h) (abs c) (abs (⟨k, mx, mn, ty, ta, et, tof, nc, lc⟩ : sim.scoring.JInfo)) false =
        ({ (abs h : OsuModel.Sim.HealthSt) with comboResult := cr.val }, inc) := by
  obtain ⟨oi, hoi, eoi⟩ := sim.scoring.osu_health_increase_refines c.hp k ty
  simp only [abs, id] at eoi
  unfold sim.scoring.increase_for OsuModel.Sim.HealthSt.increaseFor
  simp only [hl, Bool.false_eq_true, ite_false, abs]
  cases ty <;>
    simp [hrS, sim.scoring.nat_min, sim.basic.is_hit, OsuModel.Sim.HitResult.isHit, hoi, ← eoi, sim_u64_eq_iff] <;>
    (by_cases hk : k = .Tail <;>
      (try simp [hk, kindS, Nat.min_def]) <;>
      (cases nc <;> cases lc <;> (try simp) <;> (try split_ifs) <;> (try simp_all) <;>
        sim_cr_close))


/-- `increaseFor` returns the new state; the Rust returns only its changed field (`comboResult`) and the increase. -/
theorem sim.scoring.increase_for_refines (h : sim.scoring.HealthSt) (c : sim.scoring.HealthCfg)
    (j : sim.scoring.JInfo) (simulating : Bool) :
    ∃ cr inc, sim.scoring.increase_for h c j simulating = ok (cr, inc) ∧
      OsuModel.Sim.HealthSt.increaseFor (abs h) (abs c) (abs j) simulating =
        ({ (abs h : OsuModel.Sim.HealthSt) with comboResult := cr.val }, inc) := by
  cases hl : c.legacy
  · cases simulating
    · rcases j with ⟨k, mx, mn, ty, ta, et, tof, nc, lc⟩; exact sim_increase_for_main h c k mx mn ty ta et tof nc lc hl
    · obtain ⟨oi, hoi, eoi⟩ := sim.scoring.osu_health_increase_refines c.hp j.kind j.ty
      simp only [abs, id] at eoi
      simp [sim.scoring.increase_for, OsuModel.Sim.HealthSt.increaseFor, hl, hoi, abs, ← eoi]
  · obtain ⟨li, hli, eli⟩ := sim.scoring.legacy_health_increase_refines c.hp c.hp_multiplier_normal j.kind j.ty
    simp only [abs, id] at eli
    simp [sim.scoring.increase_for, OsuModel.Sim.HealthSt.increaseFor, hl, hli, abs, ← eli]

end OsuProofs
