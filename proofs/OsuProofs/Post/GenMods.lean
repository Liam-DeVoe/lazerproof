/-
Generator mods, part 10 (gen agent): `mod_random.apply` / `mod_target_practice.apply` with preconditions on the spec
value `abs pb` (for `GpbBounds.atb`, Playable3), and `apply_to_beatmap_refines_gen`: `beatmap::mods::apply_to_beatmap`
refines `allHooks.applyToBeatmap` with the Random / Target Practice generators discharged (size hypotheses only).
-/
import OsuProofs.Post.GenTP3
import OsuProofs.Post.ModsApply
set_option maxHeartbeats 400000
set_option linter.all false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl

/-- `mod_random.apply` with its preconditions stated on the spec value `abs pb` (for `GpbBounds.atb`). -/
theorem beatmap.mod_random.apply_refines_abs (seed : I32) (sh : F32) (pb : beatmap.playable.PlayableBeatmap)
    (hg : ∀ h ∈ (abs pb : PlayableBeatmap).hitObjects, GenOk h)
    (hcp : (abs pb : PlayableBeatmap).controlPoints.timingPoints.size < 2^31)
    (h64 : System.Platform.numBits = 64) :
    ∃ e r, beatmap.mod_random.apply seed sh pb = ok (e, r) ∧
      hRel (fun _ => (abs r : PlayableBeatmap)) e (Mods.RandomMod.apply (i32S seed) sh (abs pb)) := by
  refine beatmap.mod_random.apply_refines seed sh pb (fun h hm => hg _ ?_) (by simpa [abs] using hcp) h64
  show (abs h : OsuHitObject) ∈ (pb.hit_objects.val.map (abs : _ → OsuHitObject)).toArray
  simp only [List.mem_toArray, List.mem_map]; exact ⟨h, hm, rfl⟩

/-- `mod_target_practice.apply` with its preconditions stated on the spec value `abs pb` (for `GpbBounds.atb`). -/
theorem beatmap.mod_target_practice.apply_refines_abs (seed : I32) (idx : Usize) (pb : beatmap.playable.PlayableBeatmap)
    (hN : (abs pb : PlayableBeatmap).hitObjects.size < 2^31)
    (hce : (abs pb : PlayableBeatmap).controlPoints.effectPoints.size < 2^31)
    (hct : (abs pb : PlayableBeatmap).controlPoints.timingPoints.size < 2^31)
    (hm : (abs pb : PlayableBeatmap).modStates.size < 2^63) (hep : (abs pb : PlayableBeatmap).epoch < 2^63)
    (h64 : System.Platform.numBits = 64) :
    ∃ e r, beatmap.mod_target_practice.apply seed idx pb = ok (e, r) ∧
      hRel (fun _ => (abs r : PlayableBeatmap)) e (Mods.TargetPractice.apply (i32S seed) (abs idx) (abs pb)) := by
  have hU := usize_max_64 h64
  refine beatmap.mod_target_practice.apply_refines seed idx pb (by simpa [abs] using hN) (by simpa [abs] using hce)
    (by simpa [abs] using hct) ?_ ?_ h64
  · have : (abs pb : PlayableBeatmap).modStates.size = pb.mod_states.val.length := by simp [abs]
    omega
  · have : (abs pb : PlayableBeatmap).epoch = pb.epoch.val := rfl
    omega

theorem gen_asCnt_len (l : List beatmap.objects.OsuHitObject) : l.length ≤ asCnt l := by
  unfold asCnt
  induction l with
  | nil => simp
  | cons h t ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

/-- `apply_to_beatmap` refines `allHooks.applyToBeatmap` (hRD / hTP of `apply_to_beatmap_refines` discharged by
`mod_random.apply_refines` / `mod_target_practice.apply_refines`); size hypotheses only. -/
theorem beatmap.mods.apply_to_beatmap_refines_gen (m : beatmap.mod_settings.ModConfig) (hv : AcrOk m)
    (hk : KeysOk m.settings.val) (i : Usize) (pb : beatmap.playable.PlayableBeatmap)
    (hm : (abs pb : PlayableBeatmap).modStates.size < 2^63) (hC : asCnt pb.hit_objects.val < 2^31)
    (hg : ∀ h ∈ (abs pb : PlayableBeatmap).hitObjects, GenOk h)
    (hce : (abs pb : PlayableBeatmap).controlPoints.effectPoints.size < 2^31)
    (hct : (abs pb : PlayableBeatmap).controlPoints.timingPoints.size < 2^31)
    (hep : (abs pb : PlayableBeatmap).epoch < 2^63) (h64 : System.Platform.numBits = 64) :
    ∃ e r, beatmap.mods.apply_to_beatmap m i pb = ok (e, r) ∧
      hRel (fun _ => (abs r : PlayableBeatmap)) e
        (((mcS m).allHooks.applyToBeatmap.getD (fun _ pb => pure pb)) (abs i) (abs pb)) := by
  have hU := usize_max_64 h64
  have hm' : pb.mod_states.val.length < Usize.max := by
    have : (abs pb : PlayableBeatmap).modStates.size = pb.mod_states.val.length := by simp [abs]
    omega
  have hN : (abs pb : PlayableBeatmap).hitObjects.size < 2^31 := by
    have : (abs pb : PlayableBeatmap).hitObjects.size = pb.hit_objects.val.length := by simp [abs]
    have := gen_asCnt_len pb.hit_objects.val
    omega
  exact beatmap.mods.apply_to_beatmap_refines m hv hk i pb hm' hC
    (fun s f => beatmap.mod_random.apply_refines_abs s f pb hg hct h64)
    (fun s => beatmap.mod_target_practice.apply_refines_abs s i pb hN hce hct hm hep h64)
end OsuProofs
