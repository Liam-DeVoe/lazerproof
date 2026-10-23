/-
Equation forms (`f x = ok (spec x)`) of the scoring refinements, for `simp`-driven proofs of their callers.
-/
import OsuProofs.Sim.Fail
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

theorem sim_score_stat_miss (s : sim.scoring.ScoreSt) :
    (abs s : OsuModel.Sim.ScoreSt).stat .miss = (s.stats.val.getD 1 0#u64).val := by
  simp [OsuModel.Sim.ScoreSt.stat, abs, scoreS, statsS, OsuModel.Sim.HitResult.toNat]

theorem sim_clamp01_eq (x : F64) : sim.scoring.clamp01 x = ok (OsuModel.Sim.clamp01 x) := by
  obtain ⟨r, h, e⟩ := sim.scoring.clamp01_refines x; simp only [abs, id] at e; rw [h, e]
/-- The value of `round_nonneg` (mirrors the Rust; its `val` is the spec's, `sim_rnI_val`). -/
def simRnI (x : F64) : I64 :=
  if (F64.toInt64 (F64.round x)).toInt < 0 then 0#i64 else (F64.toInt64 (F64.round x)).toBitVec#iscalar
theorem sim_round_nonneg_eq (x : F64) : sim.scoring.round_nonneg x = ok (simRnI x) := by
  simp [sim.scoring.round_nonneg, sim.netx.f64_round_refines, simRnI]
@[simp] theorem sim_rnI_val (x : F64) : (simRnI x).val = max 0 (F64.toInt64 (F64.round x)).toInt := by
  obtain ⟨r, h, e⟩ := sim.scoring.round_nonneg_refines x
  rw [sim_round_nonneg_eq] at h; rw [Result.ok_injective h]; exact e.symm

def simRankI : OsuModel.Sim.Rank → sim.scoring.Rank
  | .d => .D | .c => .C | .b => .B | .a => .A | .s => .S | .sh => .SH | .x => .X | .xh => .XH | .f => .F
@[simp] theorem sim_rankS_I (r : OsuModel.Sim.Rank) : rankS (simRankI r) = r := by cases r <;> rfl
theorem sim_rank_I_S (r : sim.scoring.Rank) : simRankI (rankS r) = r := by cases r <;> rfl
theorem sim_rank_from_score_eq (acc : F64) (st : Std.Array U64 18#usize) :
    sim.scoring.rank_from_score acc st = ok (simRankI (OsuModel.Sim.rankFromScore acc (st.val.getD 1 0#u64).val)) := by
  obtain ⟨r, h, e⟩ := sim.scoring.rank_from_score_refines acc st
  simp only [abs, id] at e; rw [h, e, sim_rank_I_S]
theorem sim_adjust_rank_eq (adj : Bool) (r : sim.scoring.Rank) :
    sim.scoring.adjust_rank adj r = ok (simRankI (OsuModel.Sim.adjustRank adj (rankS r))) := by
  obtain ⟨q, h, e⟩ := sim.scoring.adjust_rank_refines adj r
  simp only [abs, id] at e; rw [h, e, sim_rank_I_S]

theorem sim_ite_ok {α} (c : Prop) [Decidable c] (a b : α) :
    (if c then ok a else ok b : Result α) = ok (if c then a else b) := by split <;> rfl

theorem sim_default_fail_condition_eq (h : sim.scoring.HealthSt) (j : sim.scoring.JInfo) :
    sim.scoring.default_fail_condition h j = ok (OsuModel.Sim.defaultFailCondition (abs h) (abs j)) := by
  obtain ⟨b, hb, e⟩ := sim.scoring.default_fail_condition_refines h j; rw [hb, e]; rfl
theorem sim_any_fail_condition_eq (c : sim.mods.Config) (j : sim.scoring.JInfo) :
    sim.step.any_fail_condition c j =
      ok ((abs c : OsuModel.Sim.Config).failConds.any (OsuModel.Sim.Sim.failCondition (abs j))) := by
  obtain ⟨b, hb, e⟩ := sim.step.any_fail_condition_refines c j; rw [hb, e]; rfl

end OsuProofs
