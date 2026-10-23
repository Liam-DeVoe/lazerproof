/-
`js_strict_of` (json agent): the adapter's `strict_tail` flag of every nested object is `type_id == 9`
(`T_STRICT_TRACKING_SLIDER_TAIL_CIRCLE`), i.e. `ev_strictOk` for the playable built by `to_sim_playable`
(feeds `ev_ctxWF.strict`, sim7's `s7StrictOk`).
-/
import OsuProofs.Eval.Adapter
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem js_adN_st (h : beatmap.objects.OsuHitObject) (n : beatmap.objects.NestedObject) :
    (ev_adN h n).strict_tail = ((ev_adN h n).type_id.val == 9) := by
  have hr : eval.adapter.adapt_nested h n = ok (ev_adN h n) := (eval.adapter.adapt_nested_refines h n).choose_spec.1
  obtain ⟨k, hk, ek⟩ := eval.adapter.nested_kind_refines n.kind
  obtain ⟨⟨mx, mn⟩, hj, ej⟩ := eval.adapter.judgement_of_refines k n.classic_slider_behaviour n.strict_tracking_tail
  obtain ⟨t, ht, et⟩ := eval.adapter.nested_type_name_refines n
  obtain ⟨w, hw, ew⟩ := eval.adapter.windows_refines n.hit_windows
  obtain ⟨mj, hmj, emj⟩ := beatmap.objects.nested_maximum_judgement_offset_refines n
  obtain ⟨c1, hc1, ec1⟩ := eval.adapter.nat_clamp_neg_refines h.combo_index
  obtain ⟨c2, hc2, ec2⟩ := eval.adapter.nat_clamp_neg_refines h.index_in_current_combo
  obtain ⟨c3, hc3, ec3⟩ := eval.adapter.nat_clamp_neg_refines n.span_index
  obtain ⟨c4, hc4, ec4⟩ := eval.adapter.nat_clamp_neg_refines n.repeat_index
  have hsp := beatmap.objects.nested_stacked_position_refines n
  have hra := beatmap.objects.nested_radius_refines n
  obtain ⟨r, hr', hst⟩ : ∃ r, eval.adapter.adapt_nested h n = ok r ∧
      r.strict_tail = (r.type_id.val == 9) := ⟨_, by
        simp [eval.adapter.adapt_nested, hk, hj, ht, eval.adapter.vec, hsp, hra, hmj, hw, hc1, hc2, hc3, hc4, lift]; rfl,
      by
        simp only [eval.adapter.T_STRICT_TRACKING_SLIDER_TAIL_CIRCLE]
        rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, beq_iff_eq]
        constructor
        · intro e; rw [e]; rfl
        · intro e; exact UScalar.eq_of_val_eq e⟩
  have := Result.ok_injective (hr.symm.trans hr')
  rw [this]; exact hst

theorem js_adO_nested (h : beatmap.objects.OsuHitObject) : (ev_adO h).nested.val = h.nested.val.map (ev_adN h) := by
  have hO : eval.adapter.adapt_object h = ok (ev_adO h) := (eval.adapter.adapt_object_refines h).choose_spec.1
  obtain ⟨nn, hnn, enn⟩ := eval.adapter.adapt_nested_all_refines h
  obtain ⟨mj, hmj, emj⟩ := beatmap.objects.maximum_judgement_offset_refines h
  obtain ⟨ra, hra, era⟩ := beatmap.objects.radius_refines h
  obtain ⟨c1, hc1, ec1⟩ := eval.adapter.nat_clamp_neg_refines h.combo_index
  obtain ⟨c2, hc2, ec2⟩ := eval.adapter.nat_clamp_neg_refines h.index_in_current_combo
  have het := beatmap.objects.end_time_refines h
  have hsp := beatmap.objects.stacked_position_refines h
  have hz : float.F64.from_bits 0#u64 = ok (0 : F64) := by simp <;> decide
  obtain ⟨o, ho, eo⟩ := eval.adapter.top_windows_refines h.hit_windows
  cases hk : h.kind with
  | Circle =>
    obtain ⟨⟨mx, mn⟩, hj, ej⟩ := eval.adapter.judgement_of_refines .Circle false false
    obtain ⟨r, hr, hrn⟩ : ∃ r, eval.adapter.adapt_object h = ok r ∧ r.nested = nn :=
      ⟨_, by simp [eval.adapter.adapt_object, hk, hj, het, eval.adapter.vec, hsp, hra, hmj, hnn, hc1, hc2, hz, lift, ho]; rfl, rfl⟩
    rw [Result.ok_injective (hO.symm.trans hr), hrn, enn]
  | Slider sd =>
    obtain ⟨⟨mx, mn⟩, hj, ej⟩ := eval.adapter.judgement_of_refines .Slider sd.classic_slider_behaviour false
    obtain ⟨sc, hsc, esc⟩ := beatmap.objects.span_count_refines sd
    obtain ⟨scc, hscc, escc⟩ := eval.adapter.nat_clamp_neg_refines sc
    obtain ⟨pv, hpv, epv⟩ := eval.adapter.path_vec_refines (alloc.vec.Vec.deref sd.path.calculated_path)
    have hdu := beatmap.objects.duration_refines h
    have hsd := beatmap.objects.span_duration_refines h
    have hdi := beatmap.slider_path.distance_refines sd.path
    have hcl : alloc.vec.CloneVec.clone float.F64.Insts.CoreCloneClone sd.path.cumulative_length = ok sd.path.cumulative_length := by
      obtain ⟨s', hs, hss⟩ := eq_ok_of_spec (Slice.clone_spec (clone := float.F64.Insts.CoreCloneClone.clone)
        (s := sd.path.cumulative_length.slice) (by intro x _; rfl))
      rw [alloc.vec.CloneVec.clone, hs, ← hss]; simp
    obtain ⟨r, hr, hrn⟩ : ∃ r, eval.adapter.adapt_object h = ok r ∧ r.nested = nn :=
      ⟨_, by simp [eval.adapter.adapt_object, hk, hj, het, eval.adapter.vec, hsp, hra, hmj, hnn, hc1, hc2, hz, lift, ho,
        hsc, hscc, hpv, hdu, hsd, hdi, hcl]; rfl, rfl⟩
    rw [Result.ok_injective (hO.symm.trans hr), hrn, enn]
  | Spinner sp =>
    obtain ⟨⟨mx, mn⟩, hj, ej⟩ := eval.adapter.judgement_of_refines .Spinner false false
    obtain ⟨r, hr, hrn⟩ : ∃ r, eval.adapter.adapt_object h = ok r ∧ r.nested = nn :=
      ⟨_, by simp [eval.adapter.adapt_object, hk, hj, het, eval.adapter.vec, hsp, hra, hmj, hnn, hc1, hc2, hz, lift, ho]; rfl, rfl⟩
    rw [Result.ok_injective (hO.symm.trans hr), hrn, enn]

/-- the playable built by `to_sim_playable` satisfies `ev_strictOk` -/
theorem js_strict_of (pb : beatmap.playable.PlayableBeatmap) (s : sim.playable.Playable)
    (hs : eval.adapter.to_sim_playable pb = ok s) : ev_strictOk s := by
  obtain ⟨br, hbr, ebr⟩ := eval.adapter.adapt_breaks_refines pb
  obtain ⟨ob, hob, eob⟩ := eval.adapter.adapt_objects_refines pb
  obtain ⟨s', hs', hso⟩ : ∃ s', eval.adapter.to_sim_playable pb = ok s' ∧ s'.objects = ob :=
    ⟨_, by simp [eval.adapter.to_sim_playable, eval.adapter.adapt_difficulty, hbr, hob, lift]; rfl, rfl⟩
  rw [Result.ok_injective (hs.symm.trans hs'), ev_strictOk, hso, eob]
  intro o ho n hn
  obtain ⟨h, -, rfl⟩ := List.mem_map.1 ho
  rw [js_adO_nested] at hn
  obtain ⟨m, -, rfl⟩ := List.mem_map.1 hn
  exact js_adN_st h m

end OsuProofs
