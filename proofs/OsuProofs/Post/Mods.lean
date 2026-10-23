/-
`beatmap::mods` (Rust) refines `OsuModel.Beatmap.Mods` (abs-style; uses the Auto lemmas).
-/
import OsuProofs.Auto.Gen
import OsuProofs.Post.Processor
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

/-- Hidden's nested-object update (Rust representation). -/
def hfiN (n : beatmap.objects.NestedObject) : beatmap.objects.NestedObject :=
  { n with time_fade_in := n.time_preempt * (0.4 : F64) }

theorem hfi_loop (h : beatmap.objects.OsuHitObject) :
    ∀ i : Usize, i.val ≤ h.nested.val.length → ∃ v : alloc.vec.Vec beatmap.objects.NestedObject,
      beatmap.mods.hidden_fade_in_loop h i = ok (h.kind, h.start_time, h.position, h.stack_height, h.scale,
        h.time_preempt, h.time_fade_in, h.new_combo, h.combo_offset, h.combo_index, h.combo_index_with_offsets,
        h.index_in_current_combo, h.last_in_combo, h.kiai, h.hit_windows, v) ∧
      v.val = h.nested.val.take i.val ++ (h.nested.val.drop i.val).map hfiN := by
  intro i
  induction hk : h.nested.val.length - i.val using Nat.strong_induction_on generalizing h i with
  | _ k ih =>
    intro hle
    unfold beatmap.mods.hidden_fade_in_loop
    rw [loop_unfold]
    by_cases hlt : i.val < h.nested.val.length
    · have hl : i < alloc.vec.Vec.len h.nested := by show i.val < (alloc.vec.Vec.len h.nested).val; simpa using hlt
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := h.nested.property; omega)
      let h' : beatmap.objects.OsuHitObject := { h with nested := alloc.vec.Vec.set h.nested i (hfiN (h.nested.val[i.val]'hlt)) }
      have hb : beatmap.mods.hidden_fade_in_loop.body h i = ok (.cont (h', i1)) := by
        simp [beatmap.mods.hidden_fade_in_loop.body, hl, vec_index_eq _ i hlt, vec_index_mut_eq _ i hlt,
          cst_beatmap_mods_FADE_IN_DURATION_MULTIPLIER, float.F64.mul, hi1, h', hfiN]
      have hlen : h'.nested.val.length = h.nested.val.length := by simp [h', vec_set_val]
      obtain ⟨v, hv1, hv2⟩ := ih (h'.nested.val.length - i1.val) (by omega) h' i1 rfl (by omega)
      refine ⟨v, ?_, ?_⟩
      · dsimp only; rw [hb]; simp only [bind_ok]
        unfold beatmap.mods.hidden_fade_in_loop at hv1; exact hv1
      · rw [hv2, hi1v]; simp only [h', vec_set_val]
        exact take_set_drop _ _ hlt hfiN
    · have hl : ¬ i < alloc.vec.Vec.len h.nested := by
        show ¬ i.val < (alloc.vec.Vec.len h.nested).val; simpa using hlt
      refine ⟨h.nested, by dsimp only; simp [beatmap.mods.hidden_fade_in_loop.body, hl], ?_⟩
      simp [List.take_of_length_le (show h.nested.val.length ≤ i.val by omega),
        List.drop_eq_nil_of_le (show h.nested.val.length ≤ i.val by omega)]

theorem is_slider_ok (h : beatmap.objects.OsuHitObject) :
    beatmap.objects.is_slider h = ok (abs h : OsuHitObject).isSlider := by
  unfold beatmap.objects.is_slider OsuHitObject.isSlider
  cases hk : h.kind <;> simp [abs, hk]

theorem beatmap.mods.hidden_fade_in_refines (h : beatmap.objects.OsuHitObject) :
    ∃ r, beatmap.mods.hidden_fade_in h = ok r ∧ Mods.hiddenFadeIn (abs h) = abs r := by
  let h1 : beatmap.objects.OsuHitObject :=
    if (abs h : OsuHitObject).isSlider then h else { h with time_fade_in := h.time_preempt * (0.4 : F64) }
  have hn1 : h1.nested = h.nested := by simp only [h1]; split <;> rfl
  obtain ⟨v, hv, hvv⟩ := hfi_loop h1 0#usize (by simp)
  refine ⟨{ h1 with nested := v }, ?_, ?_⟩
  · unfold beatmap.mods.hidden_fade_in
    have e1 : (if (abs h : OsuHitObject).isSlider = true then ok h else
        (do let f ← beatmap.mods.FADE_IN_DURATION_MULTIPLIER
            let f1 ← float.F64.mul h.time_preempt f
            ok { h with time_fade_in := f1 })) = ok h1 := by
      simp only [h1]; split <;> simp [cst_beatmap_mods_FADE_IN_DURATION_MULTIPLIER, float.F64.mul]
    simp only [is_slider_ok, bind_ok]
    rw [e1]; simp only [bind_ok]; rw [hv]; simp only [bind_ok]; rfl
  · simp [hn1] at hvv
    unfold Mods.hiddenFadeIn
    simp only [h1]
    split <;> rename_i hs <;> simp [hs, abs, hvv, hfiN, Mods.FADE_IN_DURATION_MULTIPLIER, Function.comp_def]

@[step] theorem beatmap.mods.hidden_fade_in_step (h : beatmap.objects.OsuHitObject) :
    beatmap.mods.hidden_fade_in h ⦃ r => Mods.hiddenFadeIn (abs h) = abs r ⦄ :=
  spec_of_ex (beatmap.mods.hidden_fade_in_refines h)

end OsuProofs
