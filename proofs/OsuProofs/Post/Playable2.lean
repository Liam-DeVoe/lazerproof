/-
`beatmap::playable::get_playable_beatmap` / `load` (Rust) refine `getPlayableBeatmap` / `load` (`Playable.lean`):
loop lemmas (one per Rust loop, callee obligations as hypotheses where the callee theorem is not proved yet) and the
spec normal form `gpb_spec` (the spec's five `for` loops as folds / `mapM` / `gpbATB`). Infra lead slice (D39).
-/
import OsuProofs.Post.Playable
import OsuProofs.Post.ModsB
set_option maxHeartbeats 400000
set_option linter.all false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Beatmap
theorem gpb_allHooks_diff (m : ModConfig) : m.allHooks.applyToDifficulty = m.hooks.applyToDifficulty := by
  unfold ModConfig.allHooks
  split
  · rfl
  · split
    · rename_i h; simp_all [ModConfig.hooks]
    · rfl
    · rfl
theorem gpb_allHooks_ho (m : ModConfig) : m.allHooks.applyToHitObject = m.hooks.applyToHitObject := by
  unfold ModConfig.allHooks
  split
  · rfl
  · split
    · rename_i h; simp_all [ModConfig.hooks]
    · rfl
    · rfl
theorem gpb_allHooks_ac (m : ModConfig) : m.allHooks.applyAfterConversion = m.hooks.applyAfterConversion := by
  unfold ModConfig.allHooks
  split
  · rfl
  · split
    · rename_i h; simp_all [ModConfig.hooks]
    · rfl
    · rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Beatmap

/-- one step of the spec's `applyAfterConversion` loop -/
def gpbAC (b : PlayableBeatmap) (m : Mod) : PlayableBeatmap :=
  match m.applyAfterConversion with | some f => f b | none => b

theorem gpb_loop0 (ml : Slice beatmap.mod_settings.ModConfig)
    (hAC : ∀ m ∈ ml.val, ∀ bm, ∃ r, beatmap.mods.apply_after_conversion m bm = ok r ∧
      (abs r : PlayableBeatmap) = gpbAC (abs bm) (mcS m).allHooks)
    (bm : beatmap.playable.PlayableBeatmap) :
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
    obtain ⟨r, hr, hrv⟩ := hAC (ml.val[i.val]'hlt) (List.getElem_mem _) b
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
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Beatmap

def gpbDiff (b : PlayableBeatmap) (m : Mod) : PlayableBeatmap :=
  match m.applyToDifficulty with | some f => { b with difficulty := f b.difficulty } | none => b

theorem gpb_loop1 (ml : Slice beatmap.mod_settings.ModConfig)
    (hv : ∀ m ∈ ml.val, AcrOk m) (hk : ∀ m ∈ ml.val, KeysOk m.settings.val)
    (bm : beatmap.playable.PlayableBeatmap) :
    ∃ r, beatmap.playable.get_playable_beatmap_loop1 ml bm 0#usize = ok r ∧
      (abs r : PlayableBeatmap) = (ml.val.map (fun m => (mcS m).allHooks)).foldl gpbDiff (abs bm) := by
  unfold beatmap.playable.get_playable_beatmap_loop1
  refine loop_ok _ (fun x => ml.val.length - x.2.val)
    (fun x => x.2.val ≤ ml.val.length ∧ (abs x.1 : PlayableBeatmap) = ((ml.val.take x.2.val).map (fun m => (mcS m).allHooks)).foldl gpbDiff (abs bm))
    (fun y => (abs y : PlayableBeatmap) = (ml.val.map (fun m => (mcS m).allHooks)).foldl gpbDiff (abs bm)) ?_ (bm, 0#usize) ⟨by simp, by simp⟩
  rintro ⟨b, i⟩ ⟨hi, hb⟩
  by_cases hlt : i.val < ml.val.length
  · right
    have hm := List.getElem_mem hlt
    obtain ⟨r, hr, hrv⟩ := beatmap.mods.apply_to_difficulty_refines _ (hv _ hm) (hk _ hm) b.difficulty
    have hc : i < Slice.len ml := by rw [slice_lt_len_iff]; exact hlt
    obtain ⟨j1, hj1, hj1v⟩ := usize_succ_ok i (by have := ml.property; omega)
    refine ⟨({ b with difficulty := r }, j1), ?_, ⟨by simp only [hj1v]; omega, ?_⟩, by simp only [hj1v]; omega⟩
    · simp [beatmap.playable.get_playable_beatmap_loop1.body, hc, slice_index_ok _ _ hlt, hr, hj1]
    · simp only [hj1v]
      simp only [List.take_add_one, List.map_append, List.foldl_append, List.getElem?_eq_getElem hlt, ← hb]
      simp only [Option.toList, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, gpbDiff, gpb_allHooks_diff]
      have habs : (abs ({ b with difficulty := r } : beatmap.playable.PlayableBeatmap) : PlayableBeatmap) =
          { (abs b : PlayableBeatmap) with difficulty := abs r } := rfl
      rw [habs]
      revert hrv
      cases (mcS ml.val[i.val]).hooks.applyToDifficulty <;> intro hrv <;> simp only [Option.getD, id] at hrv <;> rw [← hrv] <;> rfl
  · left
    have hc : ¬ i < Slice.len ml := by rw [slice_lt_len_iff]; exact hlt
    refine ⟨b, by simp [beatmap.playable.get_playable_beatmap_loop1.body, hc], ?_⟩
    have hle : ml.val.length ≤ i.val := by omega
    rw [hb, List.take_of_length_le hle]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Beatmap

/-- `loop_set_map` without the extra state component -/
theorem gpb_loop_set_map {X : Type}
    (body : alloc.vec.Vec X × Usize → Result (ControlFlow (alloc.vec.Vec X × Usize) (alloc.vec.Vec X)))
    (g : X → X)
    (hstep : ∀ v i (h : i.val < v.val.length), ∃ v' i', body (v, i) = ok (.cont (v', i')) ∧
      v'.val = v.val.set i.val (g v.val[i.val]) ∧ i'.val = i.val + 1)
    (hend : ∀ v i, v.val.length ≤ i.val → body (v, i) = ok (.done v)) :
    ∀ v i, i.val ≤ v.val.length → ∃ r, loop body (v, i) = ok r ∧
      r.val = v.val.take i.val ++ (v.val.drop i.val).map g := by
  intro v i
  induction hk : v.val.length - i.val using Nat.strong_induction_on generalizing v i with
  | _ k ih =>
    intro hle
    by_cases hlt : i.val < v.val.length
    · obtain ⟨v', i', hb, hv, hi⟩ := hstep v i hlt
      have hl : v'.val.length = v.val.length := by simp [hv]
      obtain ⟨r, hlp, hr2⟩ := ih (v'.val.length - i'.val) (by omega) v' i' rfl (by omega)
      refine ⟨r, by rw [loop_unfold, hb]; simpa using hlp, ?_⟩
      rw [hr2, hv, hi, take_set_drop _ _ hlt]
    · refine ⟨v, by rw [loop_unfold, hend v i (by omega)]; simp only [bind_ok], ?_⟩
      simp [List.drop_eq_nil_of_le (show v.val.length ≤ i.val by omega), List.take_of_length_le (show v.val.length ≤ i.val by omega)]

/-- the Rust object after `apply_to_hit_object` (identity if it fails; never used then) -/
noncomputable def gpbHOR (m : beatmap.mod_settings.ModConfig) (h : beatmap.objects.OsuHitObject) : beatmap.objects.OsuHitObject :=
  open Classical in if hh : ∃ r, beatmap.mods.apply_to_hit_object m h = ok r then hh.choose else h

theorem gpbHOR_eq (m : beatmap.mod_settings.ModConfig) (h r : beatmap.objects.OsuHitObject)
    (hr : beatmap.mods.apply_to_hit_object m h = ok r) : gpbHOR m h = r := by
  have he : ∃ r, beatmap.mods.apply_to_hit_object m h = ok r := ⟨r, hr⟩
  unfold gpbHOR; rw [dif_pos he]
  have h2 : ok he.choose = ok r := he.choose_spec.symm.trans hr
  exact Result.ok_injective h2

theorem gpb_loop3_inner (ml : Slice beatmap.mod_settings.ModConfig) (i : Usize) (hi : i.val < ml.val.length)
    (v : alloc.vec.Vec beatmap.objects.OsuHitObject)
    (hok : ∀ h ∈ v.val, ∃ r, beatmap.mods.apply_to_hit_object (ml.val[i.val]'hi) h = ok r) :
    ∃ r, beatmap.playable.get_playable_beatmap_loop3_loop0 ml v i 0#usize = ok r ∧
      r.val = v.val.map (gpbHOR (ml.val[i.val]'hi)) := by
  have hmax : v.val.length ≤ Usize.max := by have := v.property; omega
  -- invariant: untouched suffix still consists of original elements
  have key : ∀ (w : alloc.vec.Vec beatmap.objects.OsuHitObject) (j : Usize), j.val ≤ w.val.length →
      (∀ h ∈ w.val.drop j.val, ∃ r, beatmap.mods.apply_to_hit_object (ml.val[i.val]'hi) h = ok r) →
      ∃ r, beatmap.playable.get_playable_beatmap_loop3_loop0 ml w i j = ok r ∧
        r.val = w.val.take j.val ++ (w.val.drop j.val).map (gpbHOR (ml.val[i.val]'hi)) := by
    intro w j
    induction hk : w.val.length - j.val using Nat.strong_induction_on generalizing w j with
    | _ k ih =>
      intro hle hall
      unfold beatmap.playable.get_playable_beatmap_loop3_loop0
      rw [loop_unfold]
      by_cases hlt : j.val < w.val.length
      · have hmem : w.val[j.val] ∈ w.val.drop j.val := by
          rw [List.drop_eq_getElem_cons hlt]; exact List.mem_cons_self
        obtain ⟨r, hr⟩ := hall _ hmem
        have hc : j < alloc.vec.Vec.len w := by rw [vec_lt_len_iff]; exact hlt
        obtain ⟨j1, hj1, hj1v⟩ := usize_succ_ok j (by have := w.property; omega)
        have hb : beatmap.playable.get_playable_beatmap_loop3_loop0.body ml i w j =
            ok (.cont (alloc.vec.Vec.set w j r, j1)) := by
          simp [beatmap.playable.get_playable_beatmap_loop3_loop0.body, hc, slice_index_ok _ _ hi,
            vec_index_mut_usize_ok _ _ hlt, hr, hj1]
        have hg : gpbHOR (ml.val[i.val]'hi) (w.val[j.val]'hlt) = r := gpbHOR_eq _ _ _ hr
        have hlen : (alloc.vec.Vec.set w j r).val.length = w.val.length := by simp [vec_set_val']
        obtain ⟨y, hy, hyv⟩ := ih ((alloc.vec.Vec.set w j r).val.length - j1.val) (by omega) (alloc.vec.Vec.set w j r) j1 rfl
          (by omega) (by
            intro h hh
            rw [vec_set_val', hj1v, List.drop_set_of_lt (by omega)] at hh
            exact hall h (by rw [List.drop_eq_getElem_cons hlt]; exact List.mem_cons_of_mem _ hh))
        refine ⟨y, by simp only [hb, bind_ok]; unfold beatmap.playable.get_playable_beatmap_loop3_loop0 at hy; exact hy, ?_⟩
        rw [hyv, vec_set_val', hj1v, ← hg]
        exact take_set_drop _ _ hlt _
      · have hc : ¬ j < alloc.vec.Vec.len w := by rw [vec_lt_len_iff]; exact hlt
        refine ⟨w, by simp [beatmap.playable.get_playable_beatmap_loop3_loop0.body, hc], ?_⟩
        simp [List.drop_eq_nil_of_le (show w.val.length ≤ j.val by omega), List.take_of_length_le (show w.val.length ≤ j.val by omega)]
  obtain ⟨r, hr, hrv⟩ := key v 0#usize (by simp) (by simpa using hok)
  exact ⟨r, hr, by simpa using hrv⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Beatmap

/-- one step of the spec's `applyToHitObject` loop, on the object list -/
def gpbHO (l : List OsuHitObject) (m : Mod) : List OsuHitObject :=
  match m.applyToHitObject with | some f => l.map f | none => l

theorem gpb_loop3 (ml : Slice beatmap.mod_settings.ModConfig) (Q : OsuHitObject → Prop)
    (hv : ∀ m ∈ ml.val, AcrOk m)
    (hHO : ∀ m ∈ ml.val, ∀ h, Q (abs h) → ∃ r, beatmap.mods.apply_to_hit_object m h = ok r ∧
      ((mcS m).hooks.applyToHitObject.getD id) (abs h) = abs r)
    (v : alloc.vec.Vec beatmap.objects.OsuHitObject)
    (hQ : ∀ k < ml.val.length, ∀ o ∈ ((ml.val.take k).map (fun m => (mcS m).allHooks)).foldl gpbHO (v.val.map abs), Q o) :
    ∃ r, beatmap.playable.get_playable_beatmap_loop3 ml v 0#usize = ok r ∧
      r.val.map (abs : _ → OsuHitObject) = (ml.val.map (fun m => (mcS m).allHooks)).foldl gpbHO (v.val.map abs) := by
  unfold beatmap.playable.get_playable_beatmap_loop3
  refine loop_ok _ (fun x => ml.val.length - x.2.val)
    (fun (x : alloc.vec.Vec beatmap.objects.OsuHitObject × Usize) => x.2.val ≤ ml.val.length ∧ x.1.val.map (abs : _ → OsuHitObject) = ((ml.val.take x.2.val).map (fun m => (mcS m).allHooks)).foldl gpbHO (v.val.map abs))
    (fun (y : alloc.vec.Vec beatmap.objects.OsuHitObject) => y.val.map (abs : _ → OsuHitObject) = (ml.val.map (fun m => (mcS m).allHooks)).foldl gpbHO (v.val.map abs)) ?_ (v, 0#usize) ⟨by simp, by simp⟩
  rintro ⟨w, i⟩ ⟨hi, hw⟩
  by_cases hlt : i.val < ml.val.length
  · right
    have hm := List.getElem_mem hlt
    have hc : i < Slice.len ml := by rw [slice_lt_len_iff]; exact hlt
    obtain ⟨j1, hj1, hj1v⟩ := usize_succ_ok i (by have := ml.property; omega)
    have hstep : ((ml.val.take (i.val + 1)).map (fun m => (mcS m).allHooks)).foldl gpbHO (v.val.map abs) =
        gpbHO (((ml.val.take i.val).map (fun m => (mcS m).allHooks)).foldl gpbHO (v.val.map abs)) (mcS (ml.val[i.val]'hlt)).allHooks := by
      simp only [List.take_add_one, List.map_append, List.foldl_append, List.getElem?_eq_getElem hlt]; rfl
    cases hs : (mcS (ml.val[i.val]'hlt)).hooks.applyToHitObject with
    | none =>
      have hb : beatmap.mods.has_apply_to_hit_object (ml.val[i.val]'hlt) = ok false := by
        rw [beatmap.mods.has_apply_to_hit_object_refines _ (hv _ hm), hs]; rfl
      refine ⟨(w, j1), ?_, ⟨by simp only [hj1v]; omega, ?_⟩, by simp only [hj1v]; omega⟩
      · simp [beatmap.playable.get_playable_beatmap_loop3.body, hc, slice_index_ok _ _ hlt, hb, hj1]
      · simp only [hj1v, hstep, ← hw, gpbHO, gpb_allHooks_ho, hs]
    | some f =>
      have hb : beatmap.mods.has_apply_to_hit_object (ml.val[i.val]'hlt) = ok true := by
        rw [beatmap.mods.has_apply_to_hit_object_refines _ (hv _ hm), hs]; rfl
      have hok : ∀ h ∈ w.val, Q (abs h) := by
        intro h hh; apply hQ i.val hlt; rw [← hw]; exact List.mem_map_of_mem hh
      obtain ⟨r, hr, hrv⟩ := gpb_loop3_inner ml i hlt w (fun h hh => by
        obtain ⟨r, hr, _⟩ := hHO _ hm h (hok h hh); exact ⟨r, hr⟩)
      refine ⟨(r, j1), ?_, ⟨by simp only [hj1v]; omega, ?_⟩, by simp only [hj1v]; omega⟩
      · simp [beatmap.playable.get_playable_beatmap_loop3.body, hc, slice_index_ok _ _ hlt, hb, hj1, hr]
      · simp only [hj1v, hstep, ← hw, gpbHO, gpb_allHooks_ho, hs, hrv, List.map_map]
        apply List.map_congr_left
        intro h hh
        obtain ⟨r', hr', hrv'⟩ := hHO _ hm h (hok h hh)
        rw [hs] at hrv'
        simp only [Function.comp, gpbHOR_eq _ _ _ hr', ← hrv', Option.getD]
  · left
    have hc : ¬ i < Slice.len ml := by rw [slice_lt_len_iff]; exact hlt
    refine ⟨w, by simp [beatmap.playable.get_playable_beatmap_loop3.body, hc], ?_⟩
    have hle : ml.val.length ≤ i.val := by omega
    rw [hw, List.take_of_length_le hle]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Beatmap

/-- the spec's `applyToBeatmap` loop (mod index from `i`) -/
def gpbATB : List Mod → Nat → PlayableBeatmap → Except String PlayableBeatmap
  | [], _, b => .ok b
  | m :: ms, i, b => do
    let b' ← (m.applyToBeatmap.getD (fun _ pb => pure pb)) i b
    gpbATB ms (i + 1) b'

theorem gpbATB_append (l1 l2 : List Mod) (i : Nat) (b : PlayableBeatmap) :
    gpbATB (l1 ++ l2) i b = (gpbATB l1 i b >>= fun b' => gpbATB l2 (i + l1.length) b') := by
  induction l1 generalizing i b with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.cons_append, gpbATB, List.length_cons]
    cases (m.applyToBeatmap.getD (fun _ pb => pure pb)) i b with
    | error e => rfl
    | ok b' =>
      have h1 := ih (i + 1) b'
      rw [show i + 1 + ms.length = i + (ms.length + 1) by omega] at h1
      exact h1

theorem gpbATB_snoc (l : List Mod) (m : Mod) (b : PlayableBeatmap) :
    gpbATB (l ++ [m]) 0 b = (gpbATB l 0 b >>= fun b' => (m.applyToBeatmap.getD (fun _ pb => pure pb)) l.length b') := by
  rw [gpbATB_append]
  cases gpbATB l 0 b with
  | error e => rfl
  | ok b' =>
    show gpbATB [m] (0 + l.length) b' = (m.applyToBeatmap.getD (fun _ pb => pure pb)) l.length b'
    simp only [gpbATB, Nat.zero_add]
    cases (m.applyToBeatmap.getD (fun _ pb => pure pb)) l.length b' <;> rfl

theorem gpbATB_error (l : List Mod) (i : Nat) (b : PlayableBeatmap) (k : Nat) (s : String)
    (h : gpbATB (l.take k) i b = .error s) : ∃ s', gpbATB l i b = .error s' := by
  rw [← List.take_append_drop k l, gpbATB_append, h]; exact ⟨s, rfl⟩

/-- the Rust error flag as a `core.result.Result` -/
def gpbErr (e : Option beatmap.hit_object_parser.DecodeError) : core.result.Result Unit beatmap.hit_object_parser.DecodeError :=
  match e with | none => .Ok () | some x => .Err x

theorem gpb_loop4 (ml : Slice beatmap.mod_settings.ModConfig) (P : Nat → PlayableBeatmap → Prop)
    (bm0 : beatmap.playable.PlayableBeatmap)
    (hA : ∀ (k : Usize) (hk : k.val < ml.val.length) (b : beatmap.playable.PlayableBeatmap), P k.val (abs b) →
      ∃ e r, beatmap.mods.apply_to_beatmap (ml.val[k.val]'hk) k b = ok (e, r) ∧
        hRel (fun _ => (abs r : PlayableBeatmap)) e
          (((mcS (ml.val[k.val]'hk)).allHooks.applyToBeatmap.getD (fun _ pb => pure pb)) k.val (abs b)))
    (hP : ∀ k < ml.val.length, ∀ b, gpbATB ((ml.val.take k).map (fun m => (mcS m).allHooks)) 0 (abs bm0) = .ok b → P k b) :
    ∃ bm err, beatmap.playable.get_playable_beatmap_loop4 ml bm0 0#usize none = ok (bm, err) ∧
      hRel (fun _ => (abs bm : PlayableBeatmap)) (gpbErr err) (gpbATB (ml.val.map (fun m => (mcS m).allHooks)) 0 (abs bm0)) := by
  unfold beatmap.playable.get_playable_beatmap_loop4
  let S := fun (k : Nat) => gpbATB ((ml.val.take k).map (fun m => (mcS m).allHooks)) 0 (abs bm0)
  refine Exists.elim (loop_ok _ (fun x => ml.val.length - x.2.1.val)
    (fun (x : beatmap.playable.PlayableBeatmap × Usize × Option beatmap.hit_object_parser.DecodeError) =>
      x.2.1.val ≤ ml.val.length ∧
      match x.2.2 with
      | none => S x.2.1.val = .ok (abs x.1)
      | some _ => ∃ s, S x.2.1.val = .error s)
    (fun (y : beatmap.playable.PlayableBeatmap × Option beatmap.hit_object_parser.DecodeError) =>
      hRel (fun _ => (abs y.1 : PlayableBeatmap)) (gpbErr y.2) (gpbATB (ml.val.map (fun m => (mcS m).allHooks)) 0 (abs bm0)))
    ?_ (bm0, 0#usize, none) ⟨by simp, by simp [S, gpbATB]⟩) (fun y hy => ⟨y.1, y.2, hy.1, hy.2⟩)
  rintro ⟨b, i, err⟩ ⟨hi, hb⟩
  simp only at hi hb
  cases err with
  | some e =>
    left
    obtain ⟨s, hs⟩ := hb
    refine ⟨(b, some e), by simp [beatmap.playable.get_playable_beatmap_loop4.body], ?_⟩
    have hs' : gpbATB ((ml.val.map (fun m => (mcS m).allHooks)).take i.val) 0 (abs bm0) = .error s := by
      rw [← List.map_take]; exact hs
    obtain ⟨s', hs''⟩ := gpbATB_error _ 0 _ i.val s hs'
    rw [hs'']; trivial
  | none =>
    by_cases hlt : i.val < ml.val.length
    · right
      have hm := List.getElem_mem hlt
      have hc : i < Slice.len ml := by rw [slice_lt_len_iff]; exact hlt
      obtain ⟨j1, hj1, hj1v⟩ := usize_succ_ok i (by have := ml.property; omega)
      obtain ⟨e, r, hr, hrel⟩ := hA i hlt b (hP i.val hlt _ hb)
      have hS1 : S (i.val + 1) = (S i.val >>= fun b' =>
          ((mcS (ml.val[i.val]'hlt)).allHooks.applyToBeatmap.getD (fun _ pb => pure pb)) i.val b') := by
        simp only [S, List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList, List.map_append, List.map_cons,
          List.map_nil, gpbATB_snoc, List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt)]
      have hS2 : S (i.val + 1) = ((mcS (ml.val[i.val]'hlt)).allHooks.applyToBeatmap.getD (fun _ pb => pure pb)) i.val (abs b) := by
        rw [hS1, hb]; rfl
      generalize ((mcS (ml.val[i.val]'hlt)).allHooks.applyToBeatmap.getD (fun _ pb => pure pb)) i.val (abs b) = Y at hrel hS2
      cases e with
      | Ok u =>
        refine ⟨(r, j1, none), ?_, ⟨by simp only [hj1v]; omega, ?_⟩, by simp only [hj1v]; omega⟩
        · simp [beatmap.playable.get_playable_beatmap_loop4.body, hc, slice_index_ok _ _ hlt, hr, hj1]
        · simp only [hj1v, hS2]
          cases Y with
          | ok x => simp only [hRel] at hrel; rw [← hrel]
          | error x => simp only [hRel] at hrel
      | Err x =>
        refine ⟨(r, j1, some x), ?_, ⟨by simp only [hj1v]; omega, ?_⟩, by simp only [hj1v]; omega⟩
        · simp [beatmap.playable.get_playable_beatmap_loop4.body, hc, slice_index_ok _ _ hlt, hr, hj1]
        · simp only [hj1v, hS2]
          cases Y with
          | ok x => simp only [hRel] at hrel
          | error s => exact ⟨s, rfl⟩
    · left
      have hc : ¬ i < Slice.len ml := by rw [slice_lt_len_iff]; exact hlt
      refine ⟨(b, none), by simp [beatmap.playable.get_playable_beatmap_loop4.body, hc], ?_⟩
      have hle : ml.val.length ≤ i.val := by omega
      have : S i.val = gpbATB (ml.val.map (fun m => (mcS m).allHooks)) 0 (abs bm0) := by
        simp only [S, List.take_of_length_le hle]
      rw [← this, hb]; rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Beatmap

theorem gpb_forIn_pure {α β : Type} (l : List α) (init : β) (g : α → β → Except String (ForInStep β)) (step : β → α → β)
    (hg : ∀ m s, g m s = pure (.yield (step s m))) : forIn l init g = pure (l.foldl step init) := by
  induction l generalizing init with
  | nil => rfl
  | cons m ms ih => simp only [List.forIn_cons, List.foldl_cons, hg, pure_bind]; exact ih _

theorem gpb_forIn_push {α β : Type} (l : List α) (acc : _root_.Array β) (f : α → Except String β)
    (g : α → _root_.Array β → Except String (ForInStep (_root_.Array β)))
    (hg : ∀ h a, g h a = (do let y ← f h; pure (.yield (a.push y)))) :
    forIn l acc g = (l.mapM f).map (fun ys => acc ++ ys.toArray) := by
  induction l generalizing acc with
  | nil => simp [List.mapM_nil]; rfl
  | cons h t ih =>
    simp only [List.forIn_cons, hg, List.mapM_cons]
    cases f h with
    | error e => rfl
    | ok y =>
      show forIn t (acc.push y) g = _
      rw [ih]
      cases List.mapM f t with
      | error e => rfl
      | ok ys => show Except.ok _ = Except.ok _; simp

theorem gpb_forIn_atb (l : List Mod) (b : PlayableBeatmap) (i : Nat)
    (g : Mod → PlayableBeatmap × Nat → Except String (ForInStep (PlayableBeatmap × Nat)))
    (hg : ∀ m b i, g m (b, i) = (do let x ← (m.applyToBeatmap.getD (fun _ pb => pure pb)) i b; pure (.yield (x, i + 1)))) :
    forIn l (b, i) g = (gpbATB l i b).map (fun b' => (b', i + l.length)) := by
  induction l generalizing b i with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.forIn_cons, hg, gpbATB, List.length_cons]
    cases (m.applyToBeatmap.getD (fun _ pb => pure pb)) i b with
    | error e => rfl
    | ok x =>
      show forIn ms (x, i + 1) g = Except.map _ (gpbATB ms (i + 1) x)
      rw [ih, show i + 1 + ms.length = i + (ms.length + 1) by omega]

theorem gpb_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : ((Except.ok a : Except ε α) >>= f) = f a := rfl

def gpbHOb (b : PlayableBeatmap) (m : Mod) : PlayableBeatmap :=
  { b with hitObjects := match m.applyToHitObject with | some f => b.hitObjects.map f | none => b.hitObjects }

theorem gpbHOb_foldl (mods : List Mod) (b : PlayableBeatmap) :
    mods.foldl gpbHOb b = { b with hitObjects := (mods.foldl gpbHO b.hitObjects.toList).toArray } := by
  induction mods generalizing b with
  | nil => simp
  | cons m ms ih =>
    simp only [List.foldl_cons, ih]
    cases h : m.applyToHitObject <;> simp [gpbHOb, gpbHO, h]

/-- the spec's per-object B-spline fuel test at the end of `getPlayableBeatmap` (D72) -/
def gpbFo (h : OsuHitObject) : Bool := match h.kind with | .slider s => s.path.fuelOut | _ => false

/-- the spec's final fuel rejection of `getPlayableBeatmap` (D72) -/
def gpbFuel (b : PlayableBeatmap) : Except String PlayableBeatmap :=
  if b.hitObjects.any gpbFo then throw pathFuelMsg else pure b

theorem gpb_fo_abs (h : beatmap.objects.OsuHitObject) :
    gpbFo (abs h) = (match h.kind with | .Slider s => s.path.fuel_out | _ => false) := by
  have hkd : (abs h : OsuHitObject).kind = abs h.kind := rfl
  unfold gpbFo; rw [hkd]; cases h.kind <;> rfl

theorem gpb_apfo_loop (hos : Slice beatmap.objects.OsuHitObject) :
    ∀ k (i : Usize), hos.val.length - i.val = k → i.val ≤ hos.val.length →
    beatmap.playable.any_path_fuel_out_loop hos i = ok ((hos.val.drop i.val).any (fun h => gpbFo (abs h))) := by
  intro k
  induction k with
  | zero =>
    intro i hk hle
    unfold beatmap.playable.any_path_fuel_out_loop
    rw [loop_unfold]
    have hlt : ¬ i < Slice.len hos := by rw [slice_lt_len_iff]; omega
    rw [List.drop_of_length_le (by omega)]
    simp [beatmap.playable.any_path_fuel_out_loop.body, hlt]
  | succ k ih =>
    intro i hk hle
    have hil : i.val < hos.val.length := by omega
    have hlt : i < Slice.len hos := by rw [slice_lt_len_iff]; exact hil
    rw [List.drop_eq_getElem_cons hil, List.any_cons, gpb_fo_abs]
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := hos.property; scalar_tac)
    have hrec := ih i1 (by omega) (by omega)
    rw [show i1.val = i.val + 1 by omega] at hrec
    unfold beatmap.playable.any_path_fuel_out_loop at hrec ⊢
    rw [loop_unfold]
    have hb0 : beatmap.playable.any_path_fuel_out_loop.body hos i =
        (match (hos.val[i.val]'hil).kind with
          | beatmap.objects.ObjectKind.Circle => ok (ControlFlow.cont i1)
          | beatmap.objects.ObjectKind.Slider s =>
            if s.path.fuel_out = true then ok (ControlFlow.done true) else ok (ControlFlow.cont i1)
          | beatmap.objects.ObjectKind.Spinner _ => ok (ControlFlow.cont i1)) := by
      simp only [beatmap.playable.any_path_fuel_out_loop.body, hlt, ite_true, slice_index_ok hos i hil, bind_ok, hi1]
      cases (hos.val[i.val]'hil).kind <;> simp only [bind_ok, hi1]
    rw [hb0]
    cases hk' : (hos.val[i.val]'hil).kind with
    | Circle => simp only [bind_ok, Bool.false_or]; exact hrec
    | Spinner _ => simp only [bind_ok, Bool.false_or]; exact hrec
    | Slider s =>
      cases hf : s.path.fuel_out
      · simp only [hf, Bool.false_eq_true, ite_false, bind_ok, Bool.false_or]; exact hrec
      · simp only [hf, ite_true, bind_ok, Bool.true_or]

theorem beatmap.playable.any_path_fuel_out_refines (hos : Slice beatmap.objects.OsuHitObject) :
    beatmap.playable.any_path_fuel_out hos = ok ((hos.val.map (abs : beatmap.objects.OsuHitObject → OsuHitObject)).any gpbFo) := by
  have := gpb_apfo_loop hos _ 0#usize rfl (by simp)
  simp only [beatmap.playable.any_path_fuel_out]
  rw [this]; simp [List.any_map]; rfl

theorem gpb_tail (bm3 : beatmap.playable.PlayableBeatmap) (err1 : Option beatmap.hit_object_parser.DecodeError)
    (X : Except String PlayableBeatmap) (h : hRel (fun _ => (abs bm3 : PlayableBeatmap)) (gpbErr err1) X) :
    ∃ r, (match err1 with
      | none => do
        let b ← beatmap.playable.any_path_fuel_out (alloc.vec.Vec.deref bm3.hit_objects)
        if b = true then
          ok (core.result.Result.Err (beatmap.hit_object_parser.DecodeError.Msg beatmap.errors.M_SLIDER_PATH_FUEL_EXHAUSTED))
        else ok (core.result.Result.Ok bm3)
      | some e => ok (core.result.Result.Err e)) = ok r ∧
      hRel (fun pb => (abs pb : PlayableBeatmap)) r (X >>= gpbFuel) := by
  cases err1 with
  | some e =>
    refine ⟨_, rfl, ?_⟩
    cases X with
    | error s => trivial
    | ok y => simp [hRel, gpbErr] at h
  | none =>
    cases X with
    | error s => simp [hRel, gpbErr] at h
    | ok y =>
      simp only [hRel, gpbErr] at h
      subst h
      rw [beatmap.playable.any_path_fuel_out_refines, bind_ok]
      have e : (abs bm3 : PlayableBeatmap).hitObjects.any gpbFo =
          ((alloc.vec.Vec.deref bm3.hit_objects).val.map (abs : beatmap.objects.OsuHitObject → OsuHitObject)).any gpbFo := by
        show ((bm3.hit_objects.val.map abs).toArray).any gpbFo = _
        simp [alloc.vec.Vec.deref]
      show ∃ r, _ ∧ hRel _ r (gpbFuel (abs bm3))
      cases hb : ((alloc.vec.Vec.deref bm3.hit_objects).val.map (abs : beatmap.objects.OsuHitObject → OsuHitObject)).any gpbFo
      · refine ⟨.Ok bm3, by simp only [Bool.false_eq_true, ite_false], ?_⟩
        simp only [gpbFuel, e, hb, Bool.false_eq_true, ite_false]
        rfl
      · refine ⟨.Err (beatmap.hit_object_parser.DecodeError.Msg beatmap.errors.M_SLIDER_PATH_FUEL_EXHAUSTED),
          by simp only [ite_true], ?_⟩
        simp only [gpbFuel, e, hb, ite_true]
        trivial

/-- normal form of the spec `getPlayableBeatmap` -/
theorem gpb_spec (d : DecodedBeatmap) (mods : List Mod) :
    getPlayableBeatmap d mods =
      (let b2 := mods.foldl gpbDiff (mods.foldl gpbAC (convertBeatmap d))
       do
        let hos ← (OsuBeatmapProcessor.preProcess b2.hitObjects).toList.mapM (applyDefaults b2.controlPoints b2.difficulty)
        let b ← gpbATB mods 0 { b2 with hitObjects := OsuBeatmapProcessor.applyStackingAll b2.formatVersion b2.stackLeniency (mods.foldl gpbHO hos).toArray }
        gpbFuel b) := by
  unfold getPlayableBeatmap
  simp only []
  rw [gpb_forIn_pure mods _ _ gpbAC (by intro m s; cases h : m.applyAfterConversion <;> simp only [h, gpbAC] <;> rfl)]
  simp only [pure_bind]
  rw [gpb_forIn_pure mods _ _ gpbDiff (by intro m s; cases h : m.applyToDifficulty <;> simp only [h, gpbDiff] <;> rfl)]
  simp only [pure_bind]
  rw [← Array.forIn_toList, gpb_forIn_push _ _ _ _ (fun h a => rfl)]
  generalize List.foldl gpbDiff (List.foldl gpbAC (convertBeatmap d) mods) mods = b2
  cases List.mapM (applyDefaults b2.controlPoints b2.difficulty) (OsuBeatmapProcessor.preProcess b2.hitObjects).toList with
  | error e => rfl
  | ok ys =>
    simp only [Except.map, gpb_ok_bind, Array.empty_append]
    rw [gpb_forIn_pure mods _ _ gpbHOb (by intro m s; cases h : m.applyToHitObject <;> simp only [h, gpbHOb] <;> rfl)]
    simp only [pure_bind, gpbHOb_foldl]
    rw [gpb_forIn_atb mods _ 0 _ (by intro m b i; cases h : m.applyToBeatmap <;> simp only [h, Option.getD] <;> rfl)]
    generalize gpbATB mods 0 _ = Z
    cases Z <;> rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Beatmap

theorem gpb_mapM_snoc {α β : Type} (f : α → Except String β) (l : List α) (x : α) :
    (l ++ [x]).mapM f = (do let ys ← l.mapM f; let y ← f x; pure (ys ++ [y])) := by
  rw [List.mapM_append]
  cases l.mapM f with
  | error e => rfl
  | ok ys =>
    show (do let b ← [x].mapM f; pure (ys ++ b)) = (do let y ← f x; pure (ys ++ [y]))
    simp only [List.mapM_cons, List.mapM_nil]
    cases f x <;> rfl

theorem gpb_loop2 (d : beatmap.types.Difficulty) (cpi : beatmap.control_points.ControlPointInfo)
    (v0 : alloc.vec.Vec beatmap.objects.OsuHitObject)
    (hAD : ∀ h ∈ v0.val, ∃ e r, beatmap.objects.apply_defaults cpi d h = ok (e, r) ∧
      hRel (fun _ => (abs r : OsuHitObject)) e (applyDefaults (abs cpi) (abs d) (abs h))) :
    ∃ v err, beatmap.playable.get_playable_beatmap_loop2 d cpi v0 none 0#usize = ok (v, err) ∧
      hRel (fun _ => v.val.map (abs : _ → OsuHitObject)) (gpbErr err)
        ((v0.val.map (abs : _ → OsuHitObject)).mapM (applyDefaults (abs cpi) (abs d))) := by
  unfold beatmap.playable.get_playable_beatmap_loop2
  refine Exists.elim (loop_ok _ (fun x => v0.val.length - x.2.2.val)
    (fun (x : alloc.vec.Vec beatmap.objects.OsuHitObject × Option beatmap.hit_object_parser.DecodeError × Usize) =>
      x.2.2.val ≤ v0.val.length ∧ x.1.val.length = v0.val.length ∧ x.1.val.drop x.2.2.val = v0.val.drop x.2.2.val ∧
      match x.2.1 with
      | none => ((v0.val.map (abs : _ → OsuHitObject)).take x.2.2.val).mapM (applyDefaults (abs cpi) (abs d)) = .ok ((x.1.val.take x.2.2.val).map abs)
      | some _ => ∃ s, ((v0.val.map (abs : _ → OsuHitObject)).take x.2.2.val).mapM (applyDefaults (abs cpi) (abs d)) = .error s)
    (fun (y : alloc.vec.Vec beatmap.objects.OsuHitObject × Option beatmap.hit_object_parser.DecodeError) =>
      hRel (fun _ => y.1.val.map (abs : _ → OsuHitObject)) (gpbErr y.2) ((v0.val.map (abs : _ → OsuHitObject)).mapM (applyDefaults (abs cpi) (abs d))))
    ?_ (v0, none, 0#usize) ⟨by simp, rfl, rfl, by simp⟩) (fun y hy => ⟨y.1, y.2, hy.1, hy.2⟩)
  rintro ⟨v, err, k⟩ ⟨hk, hlen, hdrop, hb⟩
  simp only at hk hlen hdrop hb
  cases err with
  | some e =>
    left
    obtain ⟨s, hs⟩ := hb
    refine ⟨(v, some e), by simp [beatmap.playable.get_playable_beatmap_loop2.body], ?_⟩
    have hE : ((v0.val.map (abs : _ → OsuHitObject)).mapM (applyDefaults (abs cpi) (abs d))) = Except.error s := by
      rw [← List.take_append_drop k.val (v0.val.map (abs : _ → OsuHitObject)), List.mapM_append, hs]; rfl
    show hRel _ (.Err e) _
    rw [hE]; trivial
  | none =>
    by_cases hlt : k.val < v0.val.length
    · right
      have hlt' : k.val < v.val.length := by omega
      have hel : v.val[k.val]'hlt' = v0.val[k.val]'hlt := by
        have h1 := congrArg (·.head?) hdrop
        simp only [List.head?_drop, List.getElem?_eq_getElem hlt', List.getElem?_eq_getElem hlt] at h1
        exact Option.some.inj h1
      obtain ⟨e, r, hr, hrel⟩ := hAD _ (List.getElem_mem hlt)
      rw [← hel] at hr hrel
      have hc : k < alloc.vec.Vec.len v := by rw [vec_lt_len_iff]; exact hlt'
      obtain ⟨j1, hj1, hj1v⟩ := usize_succ_ok k (by have := v.property; omega)
      have hT : (v0.val.map (abs : _ → OsuHitObject)).take (k.val + 1) = (v0.val.map (abs : _ → OsuHitObject)).take k.val ++ [abs (v.val[k.val]'hlt')] := by
        simp only [List.take_add_one, List.getElem?_map, List.getElem?_eq_getElem hlt, hel]; rfl
      have hlen' : (alloc.vec.Vec.set v k r).val.length = v0.val.length := by simp [vec_set_val', hlen]
      have hdrop' : (alloc.vec.Vec.set v k r).val.drop (k.val + 1) = v0.val.drop (k.val + 1) := by
        rw [vec_set_val', List.drop_set_of_lt (by omega)]
        have := congrArg (List.drop 1) hdrop; simpa [List.drop_drop, Nat.add_comm] using this
      cases e with
      | Ok u =>
        refine ⟨(alloc.vec.Vec.set v k r, none, j1), ?_, ⟨by simp only [hj1v]; omega, hlen', by rw [hj1v]; exact hdrop', ?_⟩,
          by simp only [hj1v]; omega⟩
        · simp [beatmap.playable.get_playable_beatmap_loop2.body, hc, vec_index_mut_usize_ok _ _ hlt', hr, hj1]
        · show ((v0.val.map (abs : _ → OsuHitObject)).take j1.val).mapM (applyDefaults (abs cpi) (abs d)) = _
          rw [hj1v, hT, gpb_mapM_snoc, hb]
          revert hrel
          cases applyDefaults (abs cpi) (abs d) (abs (v.val[k.val]'hlt')) with
          | error x => intro hrel; simp only [hRel] at hrel
          | ok x =>
            intro hrel; simp only [hRel] at hrel
            show Except.ok _ = _
            rw [vec_set_val', List.take_add_one, List.take_set_of_le (by omega)]
            simp [List.getElem?_set_self hlt', hrel]
      | Err x =>
        refine ⟨(alloc.vec.Vec.set v k r, some x, j1), ?_, ⟨by simp only [hj1v]; omega, hlen', by rw [hj1v]; exact hdrop', ?_⟩,
          by simp only [hj1v]; omega⟩
        · simp [beatmap.playable.get_playable_beatmap_loop2.body, hc, vec_index_mut_usize_ok _ _ hlt', hr, hj1]
        · show ∃ s, ((v0.val.map (abs : _ → OsuHitObject)).take j1.val).mapM (applyDefaults (abs cpi) (abs d)) = _
          rw [hj1v, hT, gpb_mapM_snoc, hb]
          revert hrel
          cases applyDefaults (abs cpi) (abs d) (abs (v.val[k.val]'hlt')) with
          | error s => intro _; exact ⟨s, rfl⟩
          | ok x => intro hrel; simp only [hRel] at hrel
    · left
      have hc : ¬ k < alloc.vec.Vec.len v := by rw [vec_lt_len_iff]; omega
      refine ⟨(v, none), by simp [beatmap.playable.get_playable_beatmap_loop2.body, hc], ?_⟩
      have h1 : (v0.val.map (abs : _ → OsuHitObject)).take k.val = v0.val.map (abs : _ → OsuHitObject) :=
        List.take_of_length_le (by simp; omega)
      have h2 : v.val.take k.val = v.val := List.take_of_length_le (by omega)
      rw [h1, h2] at hb
      show hRel _ (.Ok ()) _
      rw [hb]; rfl
end OsuProofs


namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Beatmap

theorem gpb_spec' (d : DecodedBeatmap) (mods : List Mod) (b2 : PlayableBeatmap)
    (hb2 : mods.foldl gpbDiff (mods.foldl gpbAC (convertBeatmap d)) = b2) :
    getPlayableBeatmap d mods =
      (do
        let hos ← (OsuBeatmapProcessor.preProcess b2.hitObjects).toList.mapM (applyDefaults b2.controlPoints b2.difficulty)
        let b ← gpbATB mods 0 { b2 with hitObjects := OsuBeatmapProcessor.applyStackingAll b2.formatVersion b2.stackLeniency (mods.foldl gpbHO hos).toArray }
        gpbFuel b) := by
  subst hb2; exact gpb_spec d mods

/-- spec stage after the difficulty hooks -/
def gpbB2 (d : DecodedBeatmap) (MS : List Mod) : PlayableBeatmap := MS.foldl gpbDiff (MS.foldl gpbAC (convertBeatmap d))
/-- spec stage before the `applyToBeatmap` hooks -/
def gpbB5 (B2 : PlayableBeatmap) (MS : List Mod) (hos : List OsuHitObject) : PlayableBeatmap :=
  { B2 with hitObjects := OsuBeatmapProcessor.applyStackingAll B2.formatVersion B2.stackLeniency (MS.foldl gpbHO hos).toArray }

/-- `get_playable_beatmap` refines `getPlayableBeatmap`, given the callee obligations of the mod hooks and
`apply_defaults` on the actual intermediate stages (discharged by `get_playable_beatmap_refines` once those callee
theorems exist). -/
theorem gpb_main (d : beatmap.types.DecodedBeatmap) (ml : Slice beatmap.mod_settings.ModConfig)
    (h1 : d.control_points.timing_points.val.length < 2^31) (h2 : d.control_points.difficulty_points.val.length < 2^31)
    (h3 : d.control_points.effect_points.val.length < 2^31) (hN : d.hit_objects.val.length < 2^31)
    (h64 : System.Platform.numBits = 64) (hall : ∀ o ∈ d.hit_objects.val, choSlOk o)
    (hv : ∀ m ∈ ml.val, AcrOk m) (hk : ∀ m ∈ ml.val, KeysOk m.settings.val)
    (hAC : ∀ m ∈ ml.val, ∀ bm, ∃ r, beatmap.mods.apply_after_conversion m bm = ok r ∧
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
  obtain ⟨bm1, hbm1, hbm1v⟩ := gpb_loop0 ml hAC bm
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
theorem gpb_choS (h : beatmap.types.ConvertHitObject) : choS h = (abs h : ConvertHitObject) := by
  unfold choS
  show _ = ({ startTime := _, position := _, newCombo := _, comboOffset := _, kind := _, generateTicks := _, sliderVelocityMultiplier := _ } : ConvertHitObject)
  congr 1
  cases h.kind with
  | Slider cps d r =>
    show ConvertKind.slider (pcpsS cps.val) d (i32S r) = ConvertKind.slider (abs cps) (abs d) (abs r)
    rw [pcps_abs]; congr 1; cases d <;> rfl
  | _ => rfl

theorem gpb_dec_dbS (d : beatmap.types.DecodedBeatmap) : dec_dbS d = (abs d : DecodedBeatmap) := by
  unfold dec_dbS
  show _ = ({ formatVersion := _, rulesetId := _, difficulty := _, stackLeniency := _, audioLeadIn := _, controlPoints := _, breaks := _, hitObjects := _ } : DecodedBeatmap)
  congr 1
  show _ = (d.hit_objects.val.map abs).toArray
  congr 1; exact List.map_congr_left (fun h _ => gpb_choS h)
end OsuProofs
namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Beatmap

/-- relation of the Rust and spec `load` results (error payloads are not compared, as `hRel`) -/
def ldRel : beatmap.playable.LoadResult → LoadResult → Prop
  | .DecodeError _, .decodeError _ => True
  | .OtherRuleset i, .otherRuleset j => i32S i = j
  | .PlayableError _, .playableError _ => True
  | .Ok pb, .ok p => (abs pb : PlayableBeatmap) = p
  | _, _ => False

/-- `load` refines `load`, given the decoder size bounds and the `get_playable_beatmap` refinement for the decoded
beatmap (discharged by `load_refines` once `get_playable_beatmap_refines` exists). -/
theorem load_main (bytes : Slice U8) (ml : Slice beatmap.mod_settings.ModConfig)
    (hb : bytes.val.length < Usize.max) (h64 : System.Platform.numBits = 64) (N : Nat) (hN : N ≤ 2^61) (hpath : dec_pathOk N)
    (hsize : ∀ cs, streamReaderDecode (bytesS bytes) = some cs →
      (readLines cs).size + 1 < 2^31 ∧ ∀ L ∈ readLines cs, L.length < N)
    (hG : ∀ d : beatmap.types.DecodedBeatmap, LegacyBeatmapDecoder.decode (bytesS bytes) = .ok (abs d) →
      ∃ r, beatmap.playable.get_playable_beatmap d ml = ok r ∧
        hRel (fun pb => (abs pb : PlayableBeatmap)) r (getPlayableBeatmap (abs d) (ml.val.map (fun m => (mcS m).allHooks)))) :
    ∃ r, beatmap.playable.load bytes ml = ok r ∧
      ldRel r (load (bytesS bytes) (ml.val.map (fun m => (mcS m).allHooks))) := by
  obtain ⟨r, hr, hrel⟩ := beatmap.decoder.decode_refines bytes hb h64 N hN hpath hsize
  unfold beatmap.playable.load load
  rw [hr, bind_ok]
  cases hD : LegacyBeatmapDecoder.decode (bytesS bytes) with
  | error s =>
    rw [hD] at hrel
    cases r with
    | Err e => exact ⟨_, rfl, trivial⟩
    | Ok d => exact hrel.elim
  | ok x =>
    rw [hD] at hrel
    cases r with
    | Err e => exact hrel.elim
    | Ok d =>
      simp only [hRel, gpb_dec_dbS] at hrel
      subst hrel
      have hrs : (abs d : DecodedBeatmap).rulesetId = i32S d.ruleset_id := rfl
      by_cases h0 : d.ruleset_id = 0#i32
      · have hs0 : ((abs d : DecodedBeatmap).rulesetId != 0) = false := by rw [hrs, h0]; rfl
        obtain ⟨g, hg, hgrel⟩ := hG d hD
        simp only [h0, bne_self_eq_false, Bool.false_eq_true, ite_false, hs0, hg, bind_ok]
        revert hgrel
        generalize getPlayableBeatmap (abs d) _ = G
        cases g <;> cases G <;> intro h <;> first | exact h.elim | exact ⟨_, rfl, trivial⟩ | exact ⟨_, rfl, h⟩
      · have hs0 : ((abs d : DecodedBeatmap).rulesetId != 0) = true := by
          rw [hrs, ← i32S_zero]
          simp only [bne_iff_ne, ne_eq, abs_i32S_inj]; exact h0
        have hr0 : (d.ruleset_id != 0#i32) = true := by simpa using h0
        simp only [hr0, ite_true, hs0]
        exact ⟨_, rfl, rfl⟩
end OsuProofs
