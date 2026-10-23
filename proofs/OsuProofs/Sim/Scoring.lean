/-
`sim::scoring` (Rust) refines `OsuModel.Sim` Scoring (score and health processors, M4).
Statement form `∃ r, f a = ok r ∧ spec (abs a) = abs r` (Rust fns that return only the changed part of a spec
state say so in their docstring). Counter increments (`u64`) are guarded by "below `U64.max`" hypotheses (a
replay has at most a few 10^5 judgements).
-/
import OsuProofs.Sim.Basic
import OsuProofs.Sim.Consts
import OsuProofs.Sim.Eqs
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

@[simp] theorem sim_scoring_F64_0 : sim.scoring.F64_0 = ok (0 : F64) := by simp [sim.scoring.F64_0]
@[simp] theorem sim_scoring_F64_1 : sim.scoring.F64_1 = ok (1 : F64) := by simp [sim.scoring.F64_1]
@[simp] theorem sim_scoring_F64_5 : sim.scoring.F64_5 = ok (5 : F64) := by simp [sim.scoring.F64_5]
@[simp] theorem sim_scoring_F64_0_5 : sim.scoring.F64_0_5 = ok (0.5 : F64) := by simp [sim.scoring.F64_0_5]
@[simp] theorem sim_scoring_F64_500000 : sim.scoring.F64_500000 = ok (500000 : F64) := by
  simp [sim.scoring.F64_500000]

theorem sim.scoring.difficulty_range_refines (d mn mid mx : F64) :
    ∃ r, sim.scoring.difficulty_range d mn mid mx = ok r ∧
      OsuModel.Sim.difficultyRange (abs d) (abs mn) (abs mid) (abs mx) = abs r := by
  simp only [sim.scoring.difficulty_range, OsuModel.Sim.difficultyRange, abs, id, sim_scoring_F64_5,
    float.F64.lt, float.F64.sub, float.F64.div, float.F64.mul, float.F64.add, bind_tc_ok]
  split_ifs <;> simp_all

theorem sim.scoring.base_score_refines (r : sim.basic.HitResult) :
    ∃ n, sim.scoring.base_score r = ok n ∧ OsuModel.Sim.baseScore (abs r) = abs n := by
  cases r <;> simp [sim.scoring.base_score, OsuModel.Sim.baseScore, abs, hrS]

theorem sim.scoring.clamp01_refines (x : F64) :
    ∃ r, sim.scoring.clamp01 x = ok r ∧ OsuModel.Sim.clamp01 (abs x) = abs r := by
  simp only [sim.scoring.clamp01, sim_scoring_F64_0, sim_scoring_F64_1, sim.netx.f64_clamp_or_refines, bind_tc_ok,
    simClampOrD, OsuModel.Sim.clamp01, OsuModel.Sim.clampK, OsuModel.Sim.zeroD, OsuModel.Sim.oneD, abs, id,
    F64.clamp]
  have : ¬ ((1 : F64) < 0) := by decide
  by_cases h1 : x < 0 <;> by_cases h2 : (1 : F64) < x <;> simp [h1, h2, this]

theorem sim.scoring.rank_from_score_refines (acc : F64) (stats : Std.Array U64 18#usize) :
    ∃ r, sim.scoring.rank_from_score acc stats = ok r ∧
      OsuModel.Sim.rankFromScore (abs acc) (stats.val.getD 1 0#u64).val = abs r := by
  have hl : stats.val.length = 18 := by simp
  have hi : Std.Array.index_usize stats 1#usize = ok (stats.val.getD 1 0#u64) := by
    simp [Std.Array.index_usize, List.getD, hl]
  simp only [sim.scoring.rank_from_score, OsuModel.Sim.rankFromScore, abs, id, sim_scoring_F64_1, float.F64.eq,
    float.F64.le, fb64_4606732058837280358, fb64_4606281698874543309, fb64_4605380978949069210,
    fb64_4604480259023595110, bind_tc_ok]
  split_ifs <;> simp_all [sim.basic.hr_index, hi, rankS, gt_iff_lt] <;> split_ifs <;> simp_all <;> omega

theorem sim.scoring.adjust_rank_refines (adj : Bool) (r : sim.scoring.Rank) :
    ∃ q, sim.scoring.adjust_rank adj r = ok q ∧ OsuModel.Sim.adjustRank (abs adj) (abs r) = abs q := by
  cases adj <;> cases r <;> simp [sim.scoring.adjust_rank, OsuModel.Sim.adjustRank, abs, rankS]

/-- Helper (spec idiom `max 0 (F64.toInt64 (F64.round x)).toInt` in `updateScore`). -/
theorem sim.scoring.round_nonneg_refines (x : F64) :
    ∃ r, sim.scoring.round_nonneg x = ok r ∧ max 0 (F64.toInt64 (F64.round x)).toInt = r.val := by
  simp [sim.scoring.round_nonneg, sim.netx.f64_round_refines]
  split_ifs with h
  · simp; omega
  · have : (x.round.toInt64.toBitVec#iscalar : I64).val = x.round.toInt64.toInt := by
      simp [IScalar.val, BitVec.toInt]; rfl
    rw [this]; omega

theorem sim.scoring.osu_health_increase_refines (hp : F64) (k : sim.playable.Kind) (ty : sim.basic.HitResult) :
    ∃ r, sim.scoring.osu_health_increase hp k ty = ok r ∧
      OsuModel.Sim.osuHealthIncrease (abs hp) (abs k) (abs ty) = abs r := by
  cases ty <;> try cases k
  all_goals simp [sim.scoring.osu_health_increase, OsuModel.Sim.osuHealthIncrease, abs, hrS, kindS]
  all_goals first
    | (obtain ⟨r, h1, h2⟩ := sim.scoring.difficulty_range_refines hp (-0.02) (-0.075) (-0.14)
       simp only [abs, id] at h2; simp [h1, h2])
    | (obtain ⟨r, h1, h2⟩ := sim.scoring.difficulty_range_refines hp (-0.03) (-0.125) (-0.2)
       simp only [abs, id] at h2; simp [h1, h2])
    | skip

theorem sim.scoring.legacy_health_increase_refines (hp mult : F64) (k : sim.playable.Kind) (ty : sim.basic.HitResult) :
    ∃ r, sim.scoring.legacy_health_increase hp mult k ty = ok r ∧
      OsuModel.Sim.legacyHealthIncrease (abs hp) (abs mult) (abs k) (abs ty) = abs r := by
  cases ty <;> try cases k
  all_goals simp [sim.scoring.legacy_health_increase, OsuModel.Sim.legacyHealthIncrease, abs, hrS, kindS]
  all_goals (try simp (config := {decide := true}))
  all_goals first
    | (obtain ⟨r, h1, h2⟩ := sim.scoring.difficulty_range_refines hp (-0.02) (-0.075) (-0.14)
       simp only [abs, id] at h2; simp [h1, h2])
    | (obtain ⟨r, h1, h2⟩ := sim.scoring.difficulty_range_refines hp (-0.03) (-0.125) (-0.2)
       simp only [abs, id] at h2; simp [h1, h2])
    | skip

theorem sim.scoring.nat_min_refines (a b : U64) :
    ∃ r, sim.scoring.nat_min a b = ok r ∧ Nat.min (abs a) (abs b) = abs r := by
  unfold sim.scoring.nat_min
  by_cases h : a < b
  · have : a.val < b.val := h
    simp [h, abs, Nat.min_def]; omega
  · have : ¬ a.val < b.val := h
    simp [h, abs, Nat.min_def]; omega

theorem sim.scoring.health_st_init_refines (rs : alloc.vec.Vec U64) :
    ∃ r, sim.scoring.health_st_init rs = ok r ∧
      ({ retries := abs rs } : OsuModel.Sim.HealthSt) = abs r := by
  simp [sim.scoring.health_st_init, abs]

theorem sim.scoring.default_fail_condition_refines (h : sim.scoring.HealthSt) (j : sim.scoring.JInfo) :
    ∃ b, sim.scoring.default_fail_condition h j = ok b ∧
      OsuModel.Sim.defaultFailCondition (abs h) (abs j) = abs b := by
  unfold sim.scoring.default_fail_condition OsuModel.Sim.defaultFailCondition
  cases hm : j.max_result <;> cases ht : j.ty <;>
    simp [hm, ht, abs, hrS, sim.basic.is_bonus, OsuModel.Sim.HitResult.isBonus, sim_basic_ALMOST_EQUALS_EPS, gt_iff_lt]

/-- Helper (the spec's inline `F64.max 0 (F64.min 1 x)` of `computeLegacyDrainRate`). -/
theorem sim.scoring.cap01_refines (x : F64) :
    ∃ r, sim.scoring.cap01 x = ok r ∧ F64.max 0 (F64.min 1 x) = r := by
  simp [sim.scoring.cap01, net.max_refines, net.min_refines]

end OsuProofs
