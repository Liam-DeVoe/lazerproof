/- Rust derived `PartialEq` on the sim enums = equality of the spec images (`kindS`, `hrS`, `rankS`). -/
import OsuProofs.Sim.Abs
open Aeneas Aeneas.Std Result
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OsuProofs
open OsuImpl
@[simp] theorem kind_eq_ok (a b : sim.playable.Kind) :
    sim.playable.Kind.Insts.CoreCmpPartialEqKind.eq a b = ok (kindS a == kindS b) := by
  cases a <;> cases b <;> simp [sim.playable.Kind.Insts.CoreCmpPartialEqKind.eq, sim.basic.HitResult.Insts.CoreCmpPartialEqHitResult.eq, sim.scoring.Rank.Insts.CoreCmpPartialEqRank.eq, read_discriminant, sim.playable.Kind.read_discriminant, sim.basic.HitResult.read_discriminant, sim.scoring.Rank.read_discriminant, kindS, hrS, rankS] <;> decide
@[simp] theorem hr_eq_ok (a b : sim.basic.HitResult) :
    sim.basic.HitResult.Insts.CoreCmpPartialEqHitResult.eq a b = ok (hrS a == hrS b) := by
  cases a <;> cases b <;> simp [sim.playable.Kind.Insts.CoreCmpPartialEqKind.eq, sim.basic.HitResult.Insts.CoreCmpPartialEqHitResult.eq, sim.scoring.Rank.Insts.CoreCmpPartialEqRank.eq, read_discriminant, sim.playable.Kind.read_discriminant, sim.basic.HitResult.read_discriminant, sim.scoring.Rank.read_discriminant, kindS, hrS, rankS] <;> decide
@[simp] theorem rank_eq_ok (a b : sim.scoring.Rank) :
    sim.scoring.Rank.Insts.CoreCmpPartialEqRank.eq a b = ok (rankS a == rankS b) := by
  cases a <;> cases b <;> simp [sim.playable.Kind.Insts.CoreCmpPartialEqKind.eq, sim.basic.HitResult.Insts.CoreCmpPartialEqHitResult.eq, sim.scoring.Rank.Insts.CoreCmpPartialEqRank.eq, read_discriminant, sim.playable.Kind.read_discriminant, sim.basic.HitResult.read_discriminant, sim.scoring.Rank.read_discriminant, kindS, hrS, rankS] <;> decide
@[simp] theorem hr_ne_ok (a b : sim.basic.HitResult) :
    core.cmp.PartialEq.ne.trait_default sim.basic.HitResult.Insts.CoreCmpPartialEqHitResult a b = ok (hrS a != hrS b) := by
  simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, bne]
end OsuProofs
