/-
`beatmap::playable::{get_playable_beatmap, load}` (Rust) refine `getPlayableBeatmap` / `load` (Playable.lean), using
the loop lemmas and spec normal form of Playable2 and the mods / objects callee theorems. Spec-level size bounds are
bundled in `GpbBounds` / `LoadBounds` (trusted input-size assumptions, docs/proof-pipeline.md §5). The Random /
Target Practice generators are discharged by `apply_to_beatmap_refines_gen` (Post/GenMods.lean, gen agent).
-/
import OsuProofs.Post.Playable2
import OsuProofs.Post.ModsApply
import OsuProofs.Post.ModsReflect
import OsuProofs.Post.ObjectsApply
import OsuProofs.Post.GenMods
set_option maxHeartbeats 400000
set_option linter.all false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Beatmap

theorem gpb_loop0P (ml : Slice beatmap.mod_settings.ModConfig)
    (Pac : PlayableBeatmap → Prop)
    (hAC : ∀ m ∈ ml.val, ∀ bm, Pac (abs bm) → ∃ r, beatmap.mods.apply_after_conversion m bm = ok r ∧
      (abs r : PlayableBeatmap) = gpbAC (abs bm) (mcS m).allHooks)
    (bm : beatmap.playable.PlayableBeatmap)
    (hPac : ∀ k < ml.val.length, Pac (((ml.val.take k).map (fun m => (mcS m).allHooks)).foldl gpbAC (abs bm))) :
    ∃ r, beatmap.playable.get_playable_beatmap_loop0 ml bm 0#usize = ok r ∧
      (abs r : PlayableBeatmap) = (ml.val.map (fun m => (mcS m).allHooks)).foldl gpbAC (abs bm) := by
  have hmax : ml.val.length ≤ Usize.max := by have := ml.property; omega
  unfold beatmap.playable.get_playable_beatmap_loop0
  refine loop_ok _ (fun x => ml.val.length - x.2.val)
    (fun x => x.2.val ≤ ml.val.length ∧ (abs x.1 : PlayableBeatmap) = ((ml.val.take x.2.val).map (fun m => (mcS m).allHooks)).foldl gpbAC (abs bm))
    (fun y => (abs y : PlayableBeatmap) = (ml.val.map (fun m => (mcS m).allHooks)).foldl gpbAC (abs bm)) ?_ (bm, 0#usize) ⟨by simp, by simp⟩
  rintro ⟨b, i⟩ ⟨hi, hb⟩
  by_cases hlt : i.val < ml.val.length
  · right
    obtain ⟨r, hr, hrv⟩ := hAC (ml.val[i.val]'hlt) (List.getElem_mem _) b (by rw [hb]; exact hPac _ hlt)
    have hc : i < Slice.len ml := by rw [slice_lt_len_iff]; exact hlt
    obtain ⟨j1, hj1, hj1v⟩ := usize_succ_ok i (by omega)
    refine ⟨(r, j1), ?_, ⟨by simp only [hj1v]; omega, ?_⟩, by simp only [hj1v]; omega⟩
    · simp [beatmap.playable.get_playable_beatmap_loop0.body, hc, slice_index_ok _ _ hlt, hr, hj1]
    · simp only [hj1v]
      simp only [hrv, hb, List.take_add_one, List.map_append, List.foldl_append, List.getElem?_eq_getElem hlt]
      rfl
  · left
    have hc : ¬ i < Slice.len ml := by rw [slice_lt_len_iff]; exact hlt
    refine ⟨b, by simp [beatmap.playable.get_playable_beatmap_loop0.body, hc], ?_⟩
    have hle : ml.val.length ≤ i.val := by omega
    rw [hb, List.take_of_length_le hle]

/-- `get_playable_beatmap` refines `getPlayableBeatmap`, given the callee obligations of the mod hooks and
`apply_defaults` on the actual intermediate stages (discharged by `get_playable_beatmap_refines` once those callee
theorems exist). -/
theorem gpb_main2 (d : beatmap.types.DecodedBeatmap) (ml : Slice beatmap.mod_settings.ModConfig)
    (h1 : d.control_points.timing_points.val.length < 2^31) (h2 : d.control_points.difficulty_points.val.length < 2^31)
    (h3 : d.control_points.effect_points.val.length < 2^31) (hN : d.hit_objects.val.length < 2^31)
    (h64 : System.Platform.numBits = 64) (hall : ∀ o ∈ d.hit_objects.val, choSlOk o)
    (hv : ∀ m ∈ ml.val, AcrOk m) (hk : ∀ m ∈ ml.val, KeysOk m.settings.val)
    (Pac : PlayableBeatmap → Prop)
    (hPac : ∀ k < ml.val.length, Pac (((ml.val.take k).map (fun m => (mcS m).allHooks)).foldl gpbAC (convertBeatmap (abs d))))
    (hAC : ∀ m ∈ ml.val, ∀ bm, Pac (abs bm) → ∃ r, beatmap.mods.apply_after_conversion m bm = ok r ∧
      (abs r : PlayableBeatmap) = gpbAC (abs bm) (mcS m).allHooks)
    (hAD : ∀ (b2 : beatmap.playable.PlayableBeatmap), (abs b2 : PlayableBeatmap) = gpbB2 (abs d) (ml.val.map (fun m => (mcS m).allHooks)) →
      ∀ hr : beatmap.objects.OsuHitObject, abs hr ∈ (OsuBeatmapProcessor.preProcess (abs b2 : PlayableBeatmap).hitObjects).toList →
      ∃ e r, beatmap.objects.apply_defaults b2.control_points b2.difficulty hr = ok (e, r) ∧
        hRel (fun _ => (abs r : OsuHitObject)) e (applyDefaults (abs b2.control_points) (abs b2.difficulty) (abs hr)))
    (Q : OsuHitObject → Prop)
    (hHO : ∀ m ∈ ml.val, ∀ h, Q (abs h) → ∃ r, beatmap.mods.apply_to_hit_object m h = ok r ∧
      ((mcS m).hooks.applyToHitObject.getD id) (abs h) = abs r)
    (hQ : ∀ hos, (let B2 := gpbB2 (abs d) (ml.val.map (fun m => (mcS m).allHooks))
        (OsuBeatmapProcessor.preProcess B2.hitObjects).toList.mapM (applyDefaults B2.controlPoints B2.difficulty) = .ok hos) →
      ∀ k < ml.val.length, ∀ o ∈ ((ml.val.take k).map (fun m => (mcS m).allHooks)).foldl gpbHO hos, Q o)
    (hS : ∀ hos, (let B2 := gpbB2 (abs d) (ml.val.map (fun m => (mcS m).allHooks))
        (OsuBeatmapProcessor.preProcess B2.hitObjects).toList.mapM (applyDefaults B2.controlPoints B2.difficulty) = .ok hos) →
      ∀ v : alloc.vec.Vec beatmap.objects.OsuHitObject, v.val.map abs = (ml.val.map (fun m => (mcS m).allHooks)).foldl gpbHO hos →
      v.val.length < 2^62 ∧ hosOk v.val)
    (P : Nat → PlayableBeatmap → Prop)
    (hA : ∀ (k : Usize) (hk : k.val < ml.val.length) (b : beatmap.playable.PlayableBeatmap), P k.val (abs b) →
      ∃ e r, beatmap.mods.apply_to_beatmap (ml.val[k.val]'hk) k b = ok (e, r) ∧
        hRel (fun _ => (abs r : PlayableBeatmap)) e
          (((mcS (ml.val[k.val]'hk)).allHooks.applyToBeatmap.getD (fun _ pb => pure pb)) k.val (abs b)))
    (hP : ∀ hos, (let B2 := gpbB2 (abs d) (ml.val.map (fun m => (mcS m).allHooks))
        (OsuBeatmapProcessor.preProcess B2.hitObjects).toList.mapM (applyDefaults B2.controlPoints B2.difficulty) = .ok hos) →
      ∀ k < ml.val.length, ∀ b, gpbATB ((ml.val.take k).map (fun m => (mcS m).allHooks)) 0
        (gpbB5 (gpbB2 (abs d) (ml.val.map (fun m => (mcS m).allHooks))) (ml.val.map (fun m => (mcS m).allHooks)) hos) = .ok b → P k b) :
    ∃ r, beatmap.playable.get_playable_beatmap d ml = ok r ∧
      hRel (fun pb => (abs pb : PlayableBeatmap)) r (getPlayableBeatmap (abs d) (ml.val.map (fun m => (mcS m).allHooks))) := by
  obtain ⟨bm, hbm, hbmv⟩ := beatmap.playable.convert_beatmap_refines d h1 h2 h3 hN h64 hall
  obtain ⟨bm1, hbm1, hbm1v⟩ := gpb_loop0P ml Pac hAC bm (by rw [← hbmv]; exact hPac)
  obtain ⟨bm2, hbm2, hbm2v⟩ := gpb_loop1 ml hv hk bm1
  obtain ⟨v, hvv, hvvv⟩ := beatmap.processor.pre_process_refines bm2.hit_objects
  have hb2 : gpbB2 (abs d) (ml.val.map (fun m => (mcS m).allHooks)) = abs bm2 := by
    rw [gpbB2, hbm2v, hbm1v, hbmv]
  have hpp : (OsuBeatmapProcessor.preProcess (abs bm2 : PlayableBeatmap).hitObjects).toList = v.val.map abs := by
    show (OsuBeatmapProcessor.preProcess (abs bm2.hit_objects)).toList = _
    rw [hvvv]; rfl
  rw [gpb_spec' _ _ _ hb2]
  obtain ⟨v1, err, hl2, hrel2⟩ := gpb_loop2 bm2.difficulty bm2.control_points v (fun h hh => by
    refine hAD bm2 hb2.symm h ?_
    rw [hpp]; exact List.mem_map_of_mem hh)
  rw [hpp]
  unfold beatmap.playable.get_playable_beatmap
  simp only [hbm, hbm1, hbm2, hvv, hl2, bind_ok, uncurry_apply_pair]
  have hAD' : (OsuBeatmapProcessor.preProcess (gpbB2 (abs d) (ml.val.map (fun m => (mcS m).allHooks))).hitObjects).toList.mapM
      (applyDefaults (gpbB2 (abs d) (ml.val.map (fun m => (mcS m).allHooks))).controlPoints
        (gpbB2 (abs d) (ml.val.map (fun m => (mcS m).allHooks))).difficulty) =
      (v.val.map abs).mapM (applyDefaults (abs bm2.control_points) (abs bm2.difficulty)) := by
    rw [hb2, hpp]; rfl
  cases err with
  | some e =>
    refine ⟨_, rfl, ?_⟩
    revert hrel2
    cases (v.val.map abs).mapM (applyDefaults (abs bm2.control_points) (abs bm2.difficulty)) with
    | error s => intro _; trivial
    | ok y => intro h; exact h.elim
  | none =>
    have hys : (v.val.map abs).mapM (applyDefaults (abs bm2.control_points) (abs bm2.difficulty)) = .ok (v1.val.map abs) := by
      revert hrel2
      cases (v.val.map abs).mapM (applyDefaults (abs bm2.control_points) (abs bm2.difficulty)) with
      | error s => intro h; exact h.elim
      | ok y => intro h; simp only [hRel, gpbErr] at h; rw [h]
    have hys' := hAD'.trans hys
    obtain ⟨v2, hl3, hv2⟩ := gpb_loop3 ml Q hv hHO v1 (by intro k hk o ho; exact hQ _ hys' k hk o ho)
    obtain ⟨hSl, hSo⟩ := hS _ hys' v2 hv2
    obtain ⟨v3, hl5, hv3⟩ := beatmap.processor.apply_stacking_all_refines bm2.format_version bm2.stack_leniency v2 hSl hSo h64
    have hB5 : (abs ({ bm2 with hit_objects := v3 } : beatmap.playable.PlayableBeatmap) : PlayableBeatmap) =
        gpbB5 (gpbB2 (abs d) (ml.val.map (fun m => (mcS m).allHooks))) (ml.val.map (fun m => (mcS m).allHooks)) (v1.val.map abs) := by
      rw [hb2, gpbB5, ← hv2]
      show _ = { (abs bm2 : PlayableBeatmap) with hitObjects := OsuBeatmapProcessor.applyStackingAll (abs bm2.format_version) bm2.stack_leniency (abs v2) }
      rw [hv3]; rfl
    obtain ⟨bm3, err1, hl4, hrel4⟩ := gpb_loop4 ml P { bm2 with hit_objects := v3 } hA (by
      intro k hk b hb; rw [hB5] at hb; exact hP _ hys' k hk b hb)

    simp only [hl3, hl5, hl4, bind_ok, uncurry_apply_pair]
    rw [show (abs bm2 : PlayableBeatmap).controlPoints = abs bm2.control_points from rfl,
      show (abs bm2 : PlayableBeatmap).difficulty = abs bm2.difficulty from rfl, hys, gpb_ok_bind]
    show ∃ r, _ ∧ hRel _ r (gpbATB (ml.val.map (fun m => (mcS m).allHooks)) 0
      (gpbB5 (abs bm2) (ml.val.map (fun m => (mcS m).allHooks)) (v1.val.map abs)) >>= gpbFuel)
    rw [← hb2, ← hB5]
    revert hrel4
    generalize gpbATB _ _ _ = X
    exact gpb_tail bm3 err1 X
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Beatmap

/-- the spec `applyDefaults` stage of `getPlayableBeatmap` (its `mapM`) -/
def gpbHos (D : DecodedBeatmap) (MS : List Mod) : Except String (List OsuHitObject) :=
  let B2 := gpbB2 D MS
  (OsuBeatmapProcessor.preProcess B2.hitObjects).toList.mapM (applyDefaults B2.controlPoints B2.difficulty)

/-- Spec-level size bounds along `getPlayableBeatmap D MS` (trusted input-size assumptions, docs/proof-pipeline.md
§5): slider control-point / path sizes, list lengths. -/
structure GpbBounds (D : DecodedBeatmap) (MS : List Mod) : Prop where
  st : ∀ k < MS.length, ∀ h ∈ ((MS.take k).foldl gpbAC (convertBeatmap D)).hitObjects, StOk h
  cpe : (gpbB2 D MS).controlPoints.effectPoints.size < 2^31
  cpt : (gpbB2 D MS).controlPoints.timingPoints.size < 2^31
  pp : ∀ h ∈ OsuBeatmapProcessor.preProcess (gpbB2 D MS).hitObjects, PathsOk h
  nest : ∀ h ∈ OsuBeatmapProcessor.preProcess (gpbB2 D MS).hitObjects, ∀ r,
    applyDefaults (gpbB2 D MS).controlPoints (gpbB2 D MS).difficulty h = .ok r → r.nested.size < 2^31
  refl : ∀ hos, gpbHos D MS = .ok hos → ∀ k < MS.length, ∀ o ∈ (MS.take k).foldl gpbHO hos, ReflOk o
  stk : ∀ hos, gpbHos D MS = .ok hos → (MS.foldl gpbHO hos).length < 2^62 ∧ ∀ o ∈ MS.foldl gpbHO hos, PathsOk o
  atb : ∀ hos, gpbHos D MS = .ok hos → ∀ k < MS.length, ∀ b, gpbATB (MS.take k) 0 (gpbB5 (gpbB2 D MS) MS hos) = .ok b →
    b.modStates.size < 2^63 ∧ (b.hitObjects.toList.map (fun h => h.nested.size + 1)).sum < 2^31 ∧
    (∀ h ∈ b.hitObjects, GenOk h) ∧ b.controlPoints.effectPoints.size < 2^31 ∧
    b.controlPoints.timingPoints.size < 2^31 ∧ b.epoch < 2^63

theorem gpb_asCnt (l : List beatmap.objects.OsuHitObject) :
    asCnt l = ((l.map (abs : _ → OsuHitObject)).map (fun h => h.nested.size + 1)).sum := by
  unfold asCnt; simp only [List.map_map]; congr 1
  apply List.map_congr_left; intro h _; simp [abs]

theorem gpb_mem_abs {α β} [AbsTo α β] (l : List α) (x : α) (h : x ∈ l) : (abs x : β) ∈ (l.map abs).toArray := by
  simp only [List.mem_toArray, List.mem_map]; exact ⟨x, h, rfl⟩

end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Beatmap

/-- `get_playable_beatmap` refines `getPlayableBeatmap` (with the mods' `allHooks`), under the decoded-beatmap size
bounds of `convert_beatmap`, valid mod configs, and the spec-level size bounds `GpbBounds`. -/
theorem beatmap.playable.get_playable_beatmap_refines (d : beatmap.types.DecodedBeatmap) (ml : Slice beatmap.mod_settings.ModConfig)
    (h1 : d.control_points.timing_points.val.length < 2^31) (h2 : d.control_points.difficulty_points.val.length < 2^31)
    (h3 : d.control_points.effect_points.val.length < 2^31) (hN : d.hit_objects.val.length < 2^31)
    (h64 : System.Platform.numBits = 64) (hall : ∀ o ∈ d.hit_objects.val, choSlOk o)
    (hv : ∀ m ∈ ml.val, AcrOk m) (hk : ∀ m ∈ ml.val, KeysOk m.settings.val)
    (hB : GpbBounds (abs d) (ml.val.map (fun m => (mcS m).allHooks))) :
    ∃ r, beatmap.playable.get_playable_beatmap d ml = ok r ∧
      hRel (fun pb => (abs pb : PlayableBeatmap)) r (getPlayableBeatmap (abs d) (ml.val.map (fun m => (mcS m).allHooks))) := by
  have hU := usize_max_64 h64
  refine gpb_main2 d ml h1 h2 h3 hN h64 hall hv hk (fun B => ∀ h ∈ B.hitObjects, StOk h)
    (fun k hk' => by rw [List.map_take]; exact hB.st k (by simpa using hk'))
    (fun m hm bm hbm => by
      obtain ⟨r, hr, hrv⟩ := beatmap.mods.apply_after_conversion_refines m (hv m hm) bm
        (fun h hh => hbm _ (gpb_mem_abs _ _ hh)) h64
      refine ⟨r, hr, ?_⟩
      rw [← hrv]; unfold gpbAC; rw [gpb_allHooks_ac]
      cases (mcS m).hooks.applyAfterConversion <;> rfl)
    ?_ ReflOk
    (fun m hm h hq => beatmap.mods.apply_to_hit_object_refines m (hv m hm) (hk m hm) h hq h64)
    (fun hos hhos k hk' o ho => by rw [List.map_take] at ho; exact hB.refl hos hhos k (by simpa using hk') o ho)
    ?_
    (fun k b => b.modStates.size < 2^63 ∧ (b.hitObjects.toList.map (fun h => h.nested.size + 1)).sum < 2^31 ∧
      (∀ h ∈ b.hitObjects, GenOk h) ∧ b.controlPoints.effectPoints.size < 2^31 ∧
      b.controlPoints.timingPoints.size < 2^31 ∧ b.epoch < 2^63)
    ?_
    (fun hos hhos k hk' b hb => by rw [List.map_take] at hb; exact hB.atb hos hhos k (by simpa using hk') b hb)
  · intro b2 hb2 hr hmem
    have hmem' : abs hr ∈ OsuBeatmapProcessor.preProcess (gpbB2 (abs d) (ml.val.map (fun m => (mcS m).allHooks))).hitObjects := by
      rw [← hb2]; simpa using hmem
    have hce := hB.cpe; have hct := hB.cpt
    rw [← hb2] at hce hct
    have hce' : b2.control_points.effect_points.val.length < 2^31 := by simpa [abs] using hce
    have hct' : b2.control_points.timing_points.val.length < 2^31 := by simpa [abs] using hct
    exact beatmap.objects.apply_defaults_refines b2.control_points b2.difficulty hr hce' hct'
      (msr_paths_ok hr (hB.pp _ hmem')) h64 (fun r hr' => hB.nest _ hmem' r (by rw [← hb2]; exact hr'))
  · intro hos hhos v hv'
    obtain ⟨hl, hp⟩ := hB.stk hos hhos
    refine ⟨?_, ?_⟩
    · have := congrArg List.length hv'; simp only [List.length_map] at this; omega
    · intro h hh s hs
      exact msr_paths_ok h (hp _ (by rw [← hv']; exact List.mem_map_of_mem hh)) s hs
  · intro k hk' b hP
    obtain ⟨hms, hsum, hg, hce, hct, hep⟩ := hP
    exact beatmap.mods.apply_to_beatmap_refines_gen _ (hv _ (List.getElem_mem hk')) (hk _ (List.getElem_mem hk')) k b hms
      (by rw [gpb_asCnt]; exact hsum) hg hce hct hep h64
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Beatmap

/-- Spec-level size bounds of a decoded beatmap for `load` (trusted input-size assumptions, §5): control-point list
and hit-object counts, slider control-point / path sizes, plus `GpbBounds` of the playable pipeline. -/
structure LoadBounds (D : DecodedBeatmap) (MS : List Mod) : Prop where
  tp : D.controlPoints.timingPoints.size < 2^31
  dp : D.controlPoints.difficultyPoints.size < 2^31
  ep : D.controlPoints.effectPoints.size < 2^31
  n : D.hitObjects.size < 2^31
  sl : ∀ o ∈ D.hitObjects, ∀ cps dd r, o.kind = .slider cps dd r → cps.size < 2^32 ∧
    (SliderPath.calculatePath { controlPoints := cps, expectedDistance := dd, optimiseCatmull := true }).1.size < 2^62
  gpb : GpbBounds D MS

theorem gpb_load_bounds (d : beatmap.types.DecodedBeatmap) (MS : List Mod) (hL : LoadBounds (abs d) MS) :
    d.control_points.timing_points.val.length < 2^31 ∧ d.control_points.difficulty_points.val.length < 2^31 ∧
    d.control_points.effect_points.val.length < 2^31 ∧ d.hit_objects.val.length < 2^31 ∧
    ∀ o ∈ d.hit_objects.val, choSlOk o := by
  obtain ⟨tp, dp, ep, n, sl, _⟩ := hL
  refine ⟨by simpa [abs] using tp, by simpa [abs] using dp, by simpa [abs] using ep, by simpa [abs] using n, ?_⟩
  intro o ho cps dd r hk
  have hm : (abs o : ConvertHitObject) ∈ (abs d : DecodedBeatmap).hitObjects := gpb_mem_abs _ _ ho
  have hka : (abs o : ConvertHitObject).kind = .slider (pcpsS cps.val) dd (i32S r) := by
    rw [← gpb_choS]; simp only [choS, ckS, hk]
  have := sl _ hm _ _ _ hka
  simpa [pcpsS] using this
end OsuProofs
namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Beatmap

/-- `load` refines `load` (mods given by their `allHooks`) under the decoder bounds of `decode_refines` and the
spec-level `LoadBounds` of the decoded beatmap. -/
theorem beatmap.playable.load_refines (bytes : Slice U8) (ml : Slice beatmap.mod_settings.ModConfig)
    (hb : bytes.val.length < Usize.max) (h64 : System.Platform.numBits = 64) (N : Nat) (hN : N ≤ 2^61) (hpath : dec_pathOk N)
    (hsize : ∀ cs, streamReaderDecode (bytesS bytes) = some cs →
      (readLines cs).size + 1 < 2^31 ∧ ∀ L ∈ readLines cs, L.length < N)
    (hv : ∀ m ∈ ml.val, AcrOk m) (hk : ∀ m ∈ ml.val, KeysOk m.settings.val)
    (hL : ∀ D, LegacyBeatmapDecoder.decode (bytesS bytes) = .ok D → LoadBounds D (ml.val.map (fun m => (mcS m).allHooks))) :
    ∃ r, beatmap.playable.load bytes ml = ok r ∧
      ldRel r (load (bytesS bytes) (ml.val.map (fun m => (mcS m).allHooks))) :=
  load_main bytes ml hb h64 N hN hpath hsize (fun d hd => by
    have hLd := hL _ hd
    obtain ⟨h1, h2, h3, hN', hall⟩ := gpb_load_bounds d _ hLd
    exact beatmap.playable.get_playable_beatmap_refines d ml h1 h2 h3 hN' h64 hall hv hk hLd.gpb)
end OsuProofs

