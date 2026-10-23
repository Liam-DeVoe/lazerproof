/-
`sim::scoring::{update_score, score_apply}` (Rust) refine `ScoreSt.updateScore` / `ScoreSt.apply`
(ScoreProcessor: accuracy, rank, standardised total score; combo, statistics).
-/
import OsuProofs.Sim.ScoringEq
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

/-- the `rank` of `ScoreSt.updateScore`. -/
def simUpdRank (s : OsuModel.Sim.ScoreSt) (accuracy : F64) (adj : Bool) : OsuModel.Sim.Rank :=
  if Framework.Bindable.equalsD s.accuracy accuracy || s.rank == .f then s.rank
  else OsuModel.Sim.adjustRank adj (OsuModel.Sim.rankFromScore accuracy (s.stat .miss))

theorem sim.scoring.update_rank_refines (s : sim.scoring.ScoreSt) (acc : F64) (adj : Bool) :
    ∃ r, sim.scoring.update_rank s acc adj = ok r ∧ simUpdRank (abs s) (abs acc) (abs adj) = abs r := by
  unfold sim.scoring.update_rank simUpdRank
  rw [sim_score_stat_miss]
  have hF : rankS sim.scoring.Rank.F = .f := rfl
  cases he : Framework.Bindable.equalsD s.accuracy acc <;>
    cases hr : (rankS s.rank == OsuModel.Sim.Rank.f) <;>
    simp [sim.netx.equals_d_refines, he, hr, rank_eq_ok, sim_rank_from_score_eq, sim_adjust_rank_eq, abs, scoreS, hF]
theorem sim_update_rank_eq (s : sim.scoring.ScoreSt) (acc : F64) (adj : Bool) :
    sim.scoring.update_rank s acc adj = ok (simRankI (simUpdRank (abs s) acc adj)) := by
  obtain ⟨r, h, e⟩ := sim.scoring.update_rank_refines s acc adj
  have e' : simUpdRank (abs s) acc adj = abs r := e
  rw [h, e']; simp only [abs]; rw [sim_rank_I_S]

theorem sim_u64_zero_lt (x : U64) : (0#u64 < x) = (0 < x.val) := by
  apply propext; constructor <;> intro h <;> scalar_tac

theorem sim.scoring.update_score_refines (s : sim.scoring.ScoreSt) (m : sim.scoring.ScoreMax) :
    ∃ r, sim.scoring.update_score s m = ok r ∧
      OsuModel.Sim.ScoreSt.updateScore (abs s) (abs m) = abs r := by
  unfold sim.scoring.update_score OsuModel.Sim.ScoreSt.updateScore
  simp only [sim_scoring_F64_0, sim_scoring_F64_1, sim_scoring_F64_5, sim_scoring_F64_500000, float.F64.lt,
    float.F64.div, float.F64.sub, float.F64.add, float.F64.mul, float.F64.pow, float.F64.from_u64,
    float.F64.from_i64, sim_clamp01_eq, sim_update_rank_eq, sim_round_nonneg_eq, bind_ok, sim_ite_ok, gt_iff_lt,
    sim_u64_zero_lt]
  refine ⟨_, rfl, ?_⟩
  simp only [abs, scoreS, id]
  congr 1 <;> simp only [decide_eq_true_eq, sim_rnI_val, gt_iff_lt, sim_rankS_I, simUpdRank] <;> rfl

end OsuProofs
