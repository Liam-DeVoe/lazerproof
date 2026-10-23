/-
(i) Pure numeric functions: `hit_windows.rs` refines `OsuModel.Beatmap.difficultyRange`,
`OsuModel.Beatmap.osuHitWindows` and `OsuModel.Sim.HitWindows.resultFor`.
-/
import OsuProofs.Prims
import OsuModel.Beatmap.Objects
import OsuModel.Sim.Playable
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

/-! Constants: each `F64::from_bits(K)` is the spec literal (checked by the kernel). -/
theorem K5_eq : hit_windows.K5 = ok (5 : F64) := by unfold hit_windows.K5; exact from_bits_lit _ _ (by decide +kernel)
theorem K0_5_eq : hit_windows.K0_5 = ok (0.5 : F64) := by unfold hit_windows.K0_5; exact from_bits_lit _ _ (by decide +kernel)
theorem K20_eq : hit_windows.K20 = ok (20 : F64) := by unfold hit_windows.K20; exact from_bits_lit _ _ (by decide +kernel)
theorem K50_eq : hit_windows.K50 = ok (50 : F64) := by unfold hit_windows.K50; exact from_bits_lit _ _ (by decide +kernel)
theorem K60_eq : hit_windows.K60 = ok (60 : F64) := by unfold hit_windows.K60; exact from_bits_lit _ _ (by decide +kernel)
theorem K80_eq : hit_windows.K80 = ok (80 : F64) := by unfold hit_windows.K80; exact from_bits_lit _ _ (by decide +kernel)
theorem K100_eq : hit_windows.K100 = ok (100 : F64) := by unfold hit_windows.K100; exact from_bits_lit _ _ (by decide +kernel)
theorem K140_eq : hit_windows.K140 = ok (140 : F64) := by unfold hit_windows.K140; exact from_bits_lit _ _ (by decide +kernel)
theorem K150_eq : hit_windows.K150 = ok (150 : F64) := by unfold hit_windows.K150; exact from_bits_lit _ _ (by decide +kernel)
theorem K200_eq : hit_windows.K200 = ok (200 : F64) := by unfold hit_windows.K200; exact from_bits_lit _ _ (by decide +kernel)
theorem MISS_WINDOW_eq : hit_windows.MISS_WINDOW = ok OsuModel.Beatmap.MISS_WINDOW := by
  unfold hit_windows.MISS_WINDOW; exact from_bits_lit _ _ (by decide +kernel)

theorem hit_windows.difficulty_range1_refines (d : F64) :
    hit_windows.difficulty_range1 d = ok (OsuModel.Beatmap.difficultyRange1 d) := by
  unfold hit_windows.difficulty_range1 OsuModel.Beatmap.difficultyRange1
  simp [K5_eq, float.F64.sub, float.F64.div]

theorem hit_windows.difficulty_range_refines (d mn mid mx : F64) :
    hit_windows.difficulty_range d mn mid mx = ok (OsuModel.Beatmap.difficultyRange d mn mid mx) := by
  unfold hit_windows.difficulty_range OsuModel.Beatmap.difficultyRange
  by_cases h1 : (5 : F64) < d <;> by_cases h2 : d < (5 : F64) <;>
    simp [K5_eq, hit_windows.difficulty_range1_refines, float.F64.lt, float.F64.sub, float.F64.mul, float.F64.add, h1, h2]

/-- Representation map: impl `HitWindows` ↦ spec `Sim.HitWindows` (same four fields). -/
def hwSpec (hw : hit_windows.HitWindows) : OsuModel.Sim.HitWindows :=
  { great := hw.great, ok := hw.ok_, meh := hw.meh, miss := hw.miss }

theorem hit_windows.osu_hit_windows_refines (od : F64) :
    ∃ hw, hit_windows.osu_hit_windows od = ok hw ∧
      OsuModel.Beatmap.osuHitWindows od = .osu hw.great hw.ok_ hw.meh ∧
      hw.miss = OsuModel.Beatmap.MISS_WINDOW := by
  unfold hit_windows.osu_hit_windows OsuModel.Beatmap.osuHitWindows
  simp [K80_eq, K50_eq, K20_eq, K140_eq, K100_eq, K60_eq, K200_eq, K150_eq, K0_5_eq, MISS_WINDOW_eq,
    hit_windows.difficulty_range_refines, float.F64.floor, float.F64.sub]

/-- Representation map for results. -/
def hrSpec : hit_windows.HitResult → OsuModel.Sim.HitResult
  | .None => .none | .Miss => .miss | .Meh => .meh | .Ok => .ok | .Great => .great

theorem hit_windows.result_for_refines (hw : hit_windows.HitWindows) (t : F64) :
    ∃ r, hit_windows.result_for hw t = ok r ∧ hrSpec r = (hwSpec hw).resultFor t := by
  unfold hit_windows.result_for OsuModel.Sim.HitWindows.resultFor hwSpec
  simp only [float.F64.abs, float.F64.le, bind_tc_ok]
  by_cases h1 : F64.abs t ≤ hw.great <;> by_cases h2 : F64.abs t ≤ hw.ok_ <;>
    by_cases h3 : F64.abs t ≤ hw.meh <;> by_cases h4 : F64.abs t ≤ hw.miss <;>
    simp [h1, h2, h3, h4, hrSpec]

end OsuProofs
