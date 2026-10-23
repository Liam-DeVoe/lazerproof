/-
`ev_pbOk` (the `LoadBounds` premise of `EvalAssumptions.playable`) from the decoder sizes (`js_decode_sizes`, derived
from `InputBounds.decLines`) and the trusted `PlayableBounds` rows (slider paths, `GpbBounds`). json agent.
-/
import OsuProofs.Eval.E2EBase
import OsuProofs.Eval.JsonDecSize
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

theorem js_decode_beatmap_sz (bm osr : Slice U8) (hb : InputBounds bm osr) (d : beatmap.types.DecodedBeatmap)
    (h : eval.decode_beatmap bm = ok (.Ok d)) : js_decSz d := by
  obtain ⟨N, hN, hpath, hsize⟩ := hb.decLines
  obtain ⟨r, hr, -, hsz⟩ := js_decode_sizes bm hb.bmLen hb.h64 N hN hpath hsize
  unfold eval.decode_beatmap at h; rw [hr] at h; simp only [bind_ok] at h
  cases r with
  | Ok d' =>
    have hs := hsz d' rfl
    simp only at h
    split at h
    · simp only [eval.reject, bind_ok] at h; cases Result.ok_injective h
    · cases Result.ok_injective h; exact hs
  | Err e => simp only [eval.reject, bind_ok] at h; cases Result.ok_injective h

theorem js_pbOk_of (d : beatmap.types.DecodedBeatmap) (ms : Slice beatmap.mod_settings.ModConfig) (L : List Mod)
    (hsz : js_decSz d)
    (hsl : ∀ o ∈ (dec_dbS d).hitObjects, ∀ cps dd r, o.kind = .slider cps dd r → cps.size < 2^32 ∧
      (SliderPath.calculatePath { controlPoints := cps, expectedDistance := dd, optimiseCatmull := true }).1.size < 2^62)
    (hg : GpbBounds (dec_dbS d) L) (e : L = (ms.val.map mcS).map ModConfig.allHooks) : ev_pbOk d ms := by
  subst e
  obtain ⟨h1, h2, h3, h4⟩ := hsz
  exact { tp := by simpa [dec_dbS, cpS] using h1, dp := by simpa [dec_dbS, cpS] using h2,
          ep := by simpa [dec_dbS, cpS] using h3, n := by simpa [dec_dbS] using h4, sl := hsl, gpb := hg }

end OsuProofs
