/-
`eval::adapter` (Rust, `impl/osu_eval_core/src/eval/adapter.rs`) refines `OsuModel/Eval/Adapter.lean`:
`to_sim_playable` = `toSimPlayable` (playable beatmap → simulation input), with the shell's type-name table `ev_tn`
(`type_id` ↦ class name). Object geometry/timing callees are the objects slice's theorems (Beatmap/Objects.lean,
Auto/Gen.lean).
-/
import OsuProofs.Eval.E2EBase
import OsuProofs.Beatmap.Objects
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem ev_bo_MISS_WINDOW : beatmap.objects.MISS_WINDOW = ok OsuModel.Beatmap.MISS_WINDOW := by
  unfold beatmap.objects.MISS_WINDOW; exact from_bits_lit _ _ (by decide +kernel)

theorem eval.adapter.vec_refines (v : net.osutk.Vector2) :
    eval.adapter.vec v = ok ⟨v.x, v.y⟩ ∧ (abs (⟨v.x, v.y⟩ : sim.basic.Vec2) : OsuModel.Sim.Vec2) = OsuModel.Eval.vec (bv2S v) :=
  ⟨rfl, rfl⟩

theorem eval.adapter.windows_refines (w : beatmap.objects.HitWindows) :
    ∃ r, eval.adapter.windows w = ok r ∧ r.map abs = OsuModel.Eval.windows (abs w) := by
  cases w with
  | Empty => exact ⟨none, rfl, rfl⟩
  | Osu g o m =>
    refine ⟨some ⟨g, o, m, OsuModel.Beatmap.MISS_WINDOW⟩, by simp [eval.adapter.windows, ev_bo_MISS_WINDOW]; rfl, ?_⟩
    rfl

theorem eval.adapter.default_min_result_refines (r : sim.basic.HitResult) :
    ∃ x, eval.adapter.default_min_result r = ok x ∧ hrS x = OsuModel.Eval.defaultMinResult (hrS r) := by
  cases r <;> exact ⟨_, rfl, rfl⟩

theorem eval.adapter.judgement_of_refines (k : sim.playable.Kind) (c s : Bool) :
    ∃ p, eval.adapter.judgement_of k c s = ok p ∧ (hrS p.1, hrS p.2) = OsuModel.Eval.judgementOf (kindS k) c s := by
  cases k <;> cases c <;> cases s <;> simp [eval.adapter.judgement_of,
    sim.playable.Kind.Insts.CoreCmpPartialEqKind.eq, eval.adapter.default_min_result, sim.playable.Kind.read_discriminant,
    OsuModel.Eval.judgementOf, OsuModel.Eval.defaultMinResult, hrS, kindS] <;> rfl

theorem eval.adapter.nested_kind_refines (k : beatmap.objects.NestedKind) :
    ∃ r, eval.adapter.nested_kind k = ok r ∧ kindS r = OsuModel.Eval.nestedKind (abs k) := by
  cases k <;> exact ⟨_, rfl, rfl⟩

theorem eval.adapter.kind_type_id_refines (k : sim.playable.Kind) :
    ∃ r, eval.adapter.kind_type_id k = ok r ∧ ev_tn r.val = (kindS k).typeName := by
  cases k <;> exact ⟨_, rfl, by simp [eval.adapter.T_HIT_CIRCLE, eval.adapter.T_SLIDER, eval.adapter.T_STRICT_TRACKING_SLIDER, eval.adapter.T_SPINNER, eval.adapter.T_SLIDER_HEAD_CIRCLE, eval.adapter.T_SLIDER_TICK, eval.adapter.T_SLIDER_REPEAT, eval.adapter.T_SLIDER_TAIL_CIRCLE, eval.adapter.T_STRICT_TRACKING_SLIDER_TAIL_CIRCLE, eval.adapter.T_SPINNER_TICK, eval.adapter.T_SPINNER_BONUS_TICK, ev_tn, kindS, OsuModel.Sim.Kind.typeName]⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem eval.adapter.nat_clamp_neg_refines (x : I32) :
    ∃ r, eval.adapter.nat_clamp_neg x = ok r ∧ r.val = (i32S x).toNatClampNeg := by
  unfold eval.adapter.nat_clamp_neg Int32.toNatClampNeg
  rw [i32S_toInt]
  by_cases h : x.val < 0
  · refine ⟨0#u64, by simp [IScalar.lt_equiv, h], by simp; omega⟩
  · refine ⟨IScalar.hcast .U64 x, by simp [IScalar.lt_equiv, h], ?_⟩
    have hb := x.hBounds
    simp [IScalar.hcast_val_eq]
    have h2 : x.val < 2^31 := by have := hb.2; simpa using this
    rw [Int.emod_eq_of_lt (by omega) (by omega)]

theorem eval.adapter.nested_type_name_refines (n : beatmap.objects.NestedObject) :
    ∃ r, eval.adapter.nested_type_name n = ok r ∧ ev_tn r.val = OsuModel.Eval.nestedTypeName (abs n) := by
  unfold eval.adapter.nested_type_name OsuModel.Eval.nestedTypeName
  have ek : (abs n : OsuModel.Beatmap.NestedObject).kind = abs n.kind := rfl
  have es : (abs n : OsuModel.Beatmap.NestedObject).strictTrackingTail = n.strict_tracking_tail := rfl
  rw [ek, es]
  cases hk : n.kind <;> cases hs : n.strict_tracking_tail <;> simp [abs, eval.adapter.nested_kind, eval.adapter.kind_type_id,
    eval.adapter.T_HIT_CIRCLE, eval.adapter.T_SLIDER, eval.adapter.T_STRICT_TRACKING_SLIDER, eval.adapter.T_SPINNER, eval.adapter.T_SLIDER_HEAD_CIRCLE, eval.adapter.T_SLIDER_TICK, eval.adapter.T_SLIDER_REPEAT, eval.adapter.T_SLIDER_TAIL_CIRCLE, eval.adapter.T_STRICT_TRACKING_SLIDER_TAIL_CIRCLE, eval.adapter.T_SPINNER_TICK, eval.adapter.T_SPINNER_BONUS_TICK, ev_tn, OsuModel.Eval.nestedKind, OsuModel.Sim.Kind.typeName] <;> rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem eval.adapter.adapt_nested_refines (h : beatmap.objects.OsuHitObject) (n : beatmap.objects.NestedObject) :
    ∃ r, eval.adapter.adapt_nested h n = ok r ∧ hobjS ev_tn r = OsuModel.Eval.adaptNested (abs h) (abs n) := by
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
  refine ⟨{ kind := k, type_id := t, start := n.start_time, end_time := n.start_time, pos := ⟨n.position.x, n.position.y⟩,
            stacked := ⟨(bv2I (OsuModel.Beatmap.NestedObject.stackedPosition (abs n))).x, (bv2I (OsuModel.Beatmap.NestedObject.stackedPosition (abs n))).y⟩,
            stack_height := IScalar.cast .I64 n.stack_height, scale := n.scale, radius := OsuModel.Beatmap.NestedObject.radius (abs n),
            preempt := n.time_preempt, fade_in := n.time_fade_in, max_judgement_offset := mj, hit_windows := w,
            max_result := mx, min_result := mn, new_combo := false, combo_index := c1, index_in_combo := c2,
            last_in_combo := false, span_index := c3, span_start := n.span_start_time, path_progress := n.path_progress,
            repeat_index := c4, strict_tail := (t = eval.adapter.T_STRICT_TRACKING_SLIDER_TAIL_CIRCLE) }, ?_, ?_⟩
  · simp [eval.adapter.adapt_nested, hk, hj, ht, eval.adapter.vec, hsp, hra, hmj, hw, hc1, hc2, hc3, hc4, lift]
  · unfold OsuModel.Eval.adaptNested
    simp only at ej
    have e1 : (abs n : OsuModel.Beatmap.NestedObject).kind = abs n.kind := rfl
    have e2 : (abs n : OsuModel.Beatmap.NestedObject).classicSliderBehaviour = n.classic_slider_behaviour := rfl
    have e3 : (abs n : OsuModel.Beatmap.NestedObject).strictTrackingTail = n.strict_tracking_tail := rfl
    simp only [e1, e2, e3, ← ek, ← ej, ← et]
    simp only [hobjS, OsuModel.Sim.HObj.mk.injEq]
    repeat' constructor
    all_goals first | rfl | (simp only [ec1, ec2, ec3, ec4]; rfl) | exact ew | (rw [emj]; rfl) |
      (show _ = (i32S n.stack_height).toInt; rw [i32S_toInt]; simp)
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- "push `F l[i]` for each `i`" loops -/
theorem ev_map_loop {X Y : Type} (body : alloc.vec.Vec Y × Usize → Result (ControlFlow (alloc.vec.Vec Y × Usize) (alloc.vec.Vec Y)))
    (l : List X) (F : X → Y)
    (hstep : ∀ out i (h : i.val < l.length), out.val.length < Usize.max →
      ∃ out' i', body (out, i) = ok (.cont (out', i')) ∧ out'.val = out.val ++ [F (l[i.val]'h)] ∧ i'.val = i.val + 1)
    (hend : ∀ out i, l.length ≤ i.val → body (out, i) = ok (.done out)) :
    ∀ out i, i.val ≤ l.length → out.val.length + (l.length - i.val) ≤ Usize.max →
      ∃ r, loop body (out, i) = ok r ∧ r.val = out.val ++ (l.drop i.val).map F := by
  intro out i
  induction hk : l.length - i.val using Nat.strong_induction_on generalizing out i with
  | _ k ih =>
    intro hle hmax
    by_cases hlt : i.val < l.length
    · obtain ⟨out', i', hb, hout, hi⟩ := hstep out i hlt (by omega)
      have hl' : out'.val.length = out.val.length + 1 := by rw [hout]; simp
      obtain ⟨r, hl, hr⟩ := ih (l.length - i'.val) (by omega) out' i' rfl (by omega) (by omega)
      refine ⟨r, by rw [loop_unfold, hb]; simpa using hl, ?_⟩
      rw [hr, hout, hi, List.drop_eq_getElem_cons hlt, List.map_cons, List.append_assoc]; rfl
    · refine ⟨out, by rw [loop_unfold, hend out i (by omega)]; simp only [bind_ok], ?_⟩
      rw [List.drop_eq_nil_of_le (by omega)]; simp

theorem eval.adapter.path_vec_refines (p : Slice net.osutk.Vector2) :
    ∃ r, eval.adapter.path_vec p = ok r ∧ r.val = p.val.map (fun v => (⟨v.x, v.y⟩ : sim.basic.Vec2)) := by
  have hmax := p.property
  unfold eval.adapter.path_vec eval.adapter.path_vec_loop
  obtain ⟨r, hr, hv⟩ := ev_map_loop (fun x => eval.adapter.path_vec_loop.body p x.1 x.2) p.val
    (fun v => (⟨v.x, v.y⟩ : sim.basic.Vec2))
    (by
      intro out i hi hl
      obtain ⟨i1, hi1, hv1⟩ := usize_add_one i (by omega)
      exact ⟨vpush out (⟨(p.val[i.val]'hi).x, (p.val[i.val]'hi).y⟩ : sim.basic.Vec2) hl, i1, by simp [eval.adapter.path_vec_loop.body, (slice_lt_len_iff i p).mpr hi,
        slice_index_ok p i hi, eval.adapter.vec, vec_push_ok out _ hl, hi1], by simp, hv1⟩)
    (by intro out i hi; simp [eval.adapter.path_vec_loop.body, (show ¬ i < Slice.len p by scalar_tac)])
    (alloc.vec.Vec.with_capacity _ (Slice.len p)) 0#usize (by simp) (by simp [alloc.vec.Vec.with_capacity])
  exact ⟨r, hr, by simpa [alloc.vec.Vec.with_capacity] using hv⟩

theorem eval.adapter.adapt_breaks_refines (pb : beatmap.playable.PlayableBeatmap) :
    ∃ r, eval.adapter.adapt_breaks pb = ok r ∧
      r.val = pb.breaks.val.map (fun b => (⟨b.start_time, b.end_time⟩ : sim.playable.Period)) := by
  have hmax := pb.breaks.property
  unfold eval.adapter.adapt_breaks eval.adapter.adapt_breaks_loop
  obtain ⟨r, hr, hv⟩ := ev_map_loop (fun x => eval.adapter.adapt_breaks_loop.body pb.breaks x.1 x.2) pb.breaks.val
    (fun b => (⟨b.start_time, b.end_time⟩ : sim.playable.Period))
    (by
      intro out i hi hl
      obtain ⟨i1, hi1, hv1⟩ := usize_add_one i (by omega)
      exact ⟨vpush out (⟨(pb.breaks.val[i.val]'hi).start_time, (pb.breaks.val[i.val]'hi).end_time⟩ : sim.playable.Period) hl, i1, by simp [eval.adapter.adapt_breaks_loop.body, (vec_lt_len_iff i pb.breaks).mpr hi,
        vec_index_eq _ _ hi, vec_push_ok out _ hl, hi1], by simp, hv1⟩)
    (by intro out i hi; simp [eval.adapter.adapt_breaks_loop.body, (show ¬ i < alloc.vec.Vec.len pb.breaks by scalar_tac)])
    (alloc.vec.Vec.with_capacity _ (alloc.vec.Vec.len pb.breaks)) 0#usize (by simp) (by simp [alloc.vec.Vec.with_capacity])
  exact ⟨r, hr, by simpa [alloc.vec.Vec.with_capacity] using hv⟩

/-- the adapted nested object (as a function) -/
noncomputable def ev_adN (h : beatmap.objects.OsuHitObject) (n : beatmap.objects.NestedObject) : sim.playable.HObj :=
  (eval.adapter.adapt_nested_refines h n).choose

theorem eval.adapter.adapt_nested_all_refines (h : beatmap.objects.OsuHitObject) :
    ∃ r, eval.adapter.adapt_nested_all h = ok r ∧ r.val = h.nested.val.map (ev_adN h) := by
  have hmax := h.nested.property
  have hrec : ({ kind := h.kind, start_time := h.start_time, position := h.position, stack_height := h.stack_height,
                 scale := h.scale, time_preempt := h.time_preempt, time_fade_in := h.time_fade_in, new_combo := h.new_combo,
                 combo_offset := h.combo_offset, combo_index := h.combo_index, combo_index_with_offsets := h.combo_index_with_offsets,
                 index_in_current_combo := h.index_in_current_combo, last_in_combo := h.last_in_combo, kiai := h.kiai,
                 hit_windows := h.hit_windows, nested := h.nested } : beatmap.objects.OsuHitObject) = h := rfl
  unfold eval.adapter.adapt_nested_all eval.adapter.adapt_nested_all_loop
  obtain ⟨r, hr, hv⟩ := ev_map_loop (fun x => eval.adapter.adapt_nested_all_loop.body h.kind h.start_time h.position
      h.stack_height h.scale h.time_preempt h.time_fade_in h.new_combo h.combo_offset h.combo_index
      h.combo_index_with_offsets h.index_in_current_combo h.last_in_combo h.kiai h.hit_windows h.nested x.1 x.2)
    h.nested.val (ev_adN h)
    (by
      intro out i hi hl
      obtain ⟨i1, hi1, hv1⟩ := usize_add_one i (by omega)
      have ha : eval.adapter.adapt_nested h (h.nested.val[i.val]'hi) = ok (ev_adN h (h.nested.val[i.val]'hi)) :=
        (eval.adapter.adapt_nested_refines h (h.nested.val[i.val]'hi)).choose_spec.1
      refine ⟨vpush out (ev_adN h (h.nested.val[i.val]'hi)) hl, i1, ?_, by simp, hv1⟩
      have ha' : eval.adapter.adapt_nested ({ kind := h.kind, start_time := h.start_time, position := h.position, stack_height := h.stack_height, scale := h.scale, time_preempt := h.time_preempt, time_fade_in := h.time_fade_in, new_combo := h.new_combo, combo_offset := h.combo_offset, combo_index := h.combo_index, combo_index_with_offsets := h.combo_index_with_offsets, index_in_current_combo := h.index_in_current_combo, last_in_combo := h.last_in_combo, kiai := h.kiai, hit_windows := h.hit_windows, nested := h.nested }  : beatmap.objects.OsuHitObject)
          (h.nested.val[i.val]'hi) = ok (ev_adN h (h.nested.val[i.val]'hi)) := ha
      unfold eval.adapter.adapt_nested_all_loop.body
      simp [(vec_lt_len_iff i h.nested).mpr hi, vec_index_eq _ _ hi, ha', vec_push_ok out _ hl, hi1])
    (by intro out i hi; simp [eval.adapter.adapt_nested_all_loop.body, (show ¬ i < alloc.vec.Vec.len h.nested by scalar_tac)])
    (alloc.vec.Vec.with_capacity _ (alloc.vec.Vec.len h.nested)) 0#usize (by simp) (by simp [alloc.vec.Vec.with_capacity])
  exact ⟨r, hr, by simpa [alloc.vec.Vec.with_capacity] using hv⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem ev_adN_spec (h : beatmap.objects.OsuHitObject) (n : beatmap.objects.NestedObject) :
    hobjS ev_tn (ev_adN h n) = OsuModel.Eval.adaptNested (abs h) (abs n) :=
  (eval.adapter.adapt_nested_refines h n).choose_spec.2

theorem eval.adapter.top_windows_refines (w : Option beatmap.objects.HitWindows) :
    ∃ r, eval.adapter.top_windows w = ok r ∧
      r.map abs = (match (w.map abs : Option OsuModel.Beatmap.HitWindows) with | some x => OsuModel.Eval.windows x | none => none) := by
  cases w with
  | none => exact ⟨none, rfl, rfl⟩
  | some x =>
    obtain ⟨r, hr, er⟩ := eval.adapter.windows_refines x
    exact ⟨r, by simp [eval.adapter.top_windows, hr], er⟩

theorem ev_nested_eq (h : beatmap.objects.OsuHitObject) (nn : alloc.vec.Vec sim.playable.HObj)
    (enn : nn.val = h.nested.val.map (ev_adN h)) :
    (nn.val.map (hobjS ev_tn)).toArray = (abs h : OsuModel.Beatmap.OsuHitObject).nested.map (OsuModel.Eval.adaptNested (abs h)) := by
  rw [enn]
  have : (abs h : OsuModel.Beatmap.OsuHitObject).nested = (h.nested.val.map abs).toArray := rfl
  rw [this]; simp [ev_adN_spec]

theorem eval.adapter.adapt_object_refines (h : beatmap.objects.OsuHitObject) :
    ∃ r, eval.adapter.adapt_object h = ok r ∧ topS ev_tn r = OsuModel.Eval.adaptObject (abs h) := by
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
    refine ⟨_, by simp [eval.adapter.adapt_object, hk, hj, het, eval.adapter.vec, hsp, hra, hmj, hnn, hc1, hc2, hz, lift, ho]; rfl, ?_⟩
    have ek : (abs h : OsuModel.Beatmap.OsuHitObject).kind = .circle := by simp [abs, hk]
    unfold OsuModel.Eval.adaptObject
    simp only [ek]
    simp only [kindS] at ej
    rw [← ej]
    simp only [topS, OsuModel.Sim.TopObj.mk.injEq, hobjS, OsuModel.Sim.HObj.mk.injEq]
    refine ⟨?_, rfl, rfl, ev_nested_eq h nn enn⟩
    repeat' constructor
    all_goals first | rfl | (simp only [ec1, ec2]; rfl) | exact eo | (rw [emj]; rfl) | (rw [era]; rfl) |
      (show _ = (i32S h.stack_height).toInt; rw [i32S_toInt]; simp) | (simp [eval.adapter.T_HIT_CIRCLE, eval.adapter.T_SLIDER, eval.adapter.T_STRICT_TRACKING_SLIDER, eval.adapter.T_SPINNER, eval.adapter.T_SLIDER_HEAD_CIRCLE, eval.adapter.T_SLIDER_TICK, eval.adapter.T_SLIDER_REPEAT, eval.adapter.T_SLIDER_TAIL_CIRCLE, eval.adapter.T_STRICT_TRACKING_SLIDER_TAIL_CIRCLE, eval.adapter.T_SPINNER_TICK, eval.adapter.T_SPINNER_BONUS_TICK, ev_tn]) | skip
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
    refine ⟨_, by simp [eval.adapter.adapt_object, hk, hj, het, eval.adapter.vec, hsp, hra, hmj, hnn, hc1, hc2, hz, lift, ho,
      hsc, hscc, hpv, hdu, hsd, hdi, hcl]; rfl, ?_⟩
    have ek : (abs h : OsuModel.Beatmap.OsuHitObject).kind = .slider (abs sd) := by simp [abs, hk]
    unfold OsuModel.Eval.adaptObject
    simp only [ek]
    simp only [kindS] at ej
    have ec : (abs sd : OsuModel.Beatmap.SliderData).classicSliderBehaviour = sd.classic_slider_behaviour := rfl
    rw [ec, ← ej]
    simp only [topS, OsuModel.Sim.TopObj.mk.injEq, hobjS, OsuModel.Sim.HObj.mk.injEq]
    refine ⟨?_, ?_, rfl, ev_nested_eq h nn enn⟩
    · repeat' constructor
      all_goals first | rfl | (simp only [ec1, ec2]; rfl) | exact eo | (rw [emj]; rfl) | (rw [era]; rfl) |
        (show _ = (i32S h.stack_height).toInt; rw [i32S_toInt]; simp) |
        (rw [show (abs sd : OsuModel.Beatmap.SliderData).strictTracking = sd.strict_tracking from rfl];
         cases sd.strict_tracking <;> simp [eval.adapter.T_HIT_CIRCLE, eval.adapter.T_SLIDER, eval.adapter.T_STRICT_TRACKING_SLIDER, eval.adapter.T_SPINNER, eval.adapter.T_SLIDER_HEAD_CIRCLE, eval.adapter.T_SLIDER_TICK, eval.adapter.T_SLIDER_REPEAT, eval.adapter.T_SLIDER_TAIL_CIRCLE, eval.adapter.T_STRICT_TRACKING_SLIDER_TAIL_CIRCLE, eval.adapter.T_SPINNER_TICK, eval.adapter.T_SPINNER_BONUS_TICK, ev_tn])
    · simp only [Option.map_some, Option.some.injEq]
      have epath : (abs sd : OsuModel.Beatmap.SliderData).path = spS sd.path := ob_abs_sliderPath sd.path
      simp only [abs] at esc
      simp only [epath]
      simp only [abs, OsuModel.Sim.SliderData.mk.injEq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | (rw [escc]; congr 1; exact esc.symm) |
        (rw [epv]; simp [spS, vS, OsuModel.Eval.vec, bv2S]) | simp [spS]
  | Spinner sp =>
    obtain ⟨⟨mx, mn⟩, hj, ej⟩ := eval.adapter.judgement_of_refines .Spinner false false
    refine ⟨_, by simp [eval.adapter.adapt_object, hk, hj, het, eval.adapter.vec, hsp, hra, hmj, hnn, hc1, hc2, hz, lift, ho]; rfl, ?_⟩
    have ek : (abs h : OsuModel.Beatmap.OsuHitObject).kind = .spinner (abs sp) := by simp [abs, hk]
    unfold OsuModel.Eval.adaptObject
    simp only [ek]
    simp only [kindS] at ej
    rw [← ej]
    simp only [topS, OsuModel.Sim.TopObj.mk.injEq, hobjS, OsuModel.Sim.HObj.mk.injEq]
    refine ⟨?_, rfl, ?_, ev_nested_eq h nn enn⟩
    · repeat' constructor
      all_goals first | rfl | (simp only [ec1, ec2]; rfl) | exact eo | (rw [emj]; rfl) | (rw [era]; rfl) |
        (show _ = (i32S h.stack_height).toInt; rw [i32S_toInt]; simp) | simp [eval.adapter.T_HIT_CIRCLE, eval.adapter.T_SLIDER, eval.adapter.T_STRICT_TRACKING_SLIDER, eval.adapter.T_SPINNER, eval.adapter.T_SLIDER_HEAD_CIRCLE, eval.adapter.T_SLIDER_TICK, eval.adapter.T_SLIDER_REPEAT, eval.adapter.T_SLIDER_TAIL_CIRCLE, eval.adapter.T_STRICT_TRACKING_SLIDER_TAIL_CIRCLE, eval.adapter.T_SPINNER_TICK, eval.adapter.T_SPINNER_BONUS_TICK, ev_tn]
    · simp only [Option.map_some, Option.some.injEq, abs, OsuModel.Sim.SpinnerData.mk.injEq]
      refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl | (simp [i32S_toInt])
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

noncomputable def ev_adO (h : beatmap.objects.OsuHitObject) : sim.playable.TopObj :=
  (eval.adapter.adapt_object_refines h).choose

theorem eval.adapter.adapt_objects_refines (pb : beatmap.playable.PlayableBeatmap) :
    ∃ r, eval.adapter.adapt_objects pb = ok r ∧ r.val = pb.hit_objects.val.map ev_adO := by
  have hmax := pb.hit_objects.property
  unfold eval.adapter.adapt_objects eval.adapter.adapt_objects_loop
  obtain ⟨r, hr, hv⟩ := ev_map_loop (fun x => eval.adapter.adapt_objects_loop.body pb.hit_objects x.1 x.2)
    pb.hit_objects.val ev_adO
    (by
      intro out i hi hl
      obtain ⟨i1, hi1, hv1⟩ := usize_add_one i (by omega)
      have ha : eval.adapter.adapt_object (pb.hit_objects.val[i.val]'hi) = ok (ev_adO (pb.hit_objects.val[i.val]'hi)) :=
        (eval.adapter.adapt_object_refines _).choose_spec.1
      exact ⟨vpush out (ev_adO (pb.hit_objects.val[i.val]'hi)) hl, i1, by simp [eval.adapter.adapt_objects_loop.body,
        (vec_lt_len_iff i pb.hit_objects).mpr hi, vec_index_eq _ _ hi, ha, vec_push_ok out _ hl, hi1], by simp, hv1⟩)
    (by intro out i hi; simp [eval.adapter.adapt_objects_loop.body, (show ¬ i < alloc.vec.Vec.len pb.hit_objects by scalar_tac)])
    (alloc.vec.Vec.with_capacity _ (alloc.vec.Vec.len pb.hit_objects)) 0#usize (by simp) (by simp [alloc.vec.Vec.with_capacity])
  exact ⟨r, hr, by simpa [alloc.vec.Vec.with_capacity] using hv⟩

theorem eval.adapter.to_sim_playable_refines (pb : beatmap.playable.PlayableBeatmap) :
    ∃ s, eval.adapter.to_sim_playable pb = ok s ∧ playableS ev_tn s = OsuModel.Eval.toSimPlayable (abs pb) := by
  obtain ⟨br, hbr, ebr⟩ := eval.adapter.adapt_breaks_refines pb
  obtain ⟨ob, hob, eob⟩ := eval.adapter.adapt_objects_refines pb
  refine ⟨_, by simp [eval.adapter.to_sim_playable, eval.adapter.adapt_difficulty, hbr, hob, lift]; rfl, ?_⟩
  unfold OsuModel.Eval.toSimPlayable
  simp only [playableS, OsuModel.Sim.Playable.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · show _ = (i32S pb.format_version).toInt; rw [i32S_toInt]; simp
  · show (br.val.map abs).toArray = _
    rw [ebr]
    have : (abs pb : OsuModel.Beatmap.PlayableBeatmap).breaks = (pb.breaks.val.map abs).toArray := rfl
    rw [this]; simp [abs]
  · rw [eob]
    have : (abs pb : OsuModel.Beatmap.PlayableBeatmap).hitObjects = (pb.hit_objects.val.map abs).toArray := rfl
    rw [this]
    simp [ev_adO, (eval.adapter.adapt_object_refines _).choose_spec.2]
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem eval.adapter.adapt_difficulty_refines (d : beatmap.types.Difficulty) :
    ∃ r, eval.adapter.adapt_difficulty d = ok r ∧
      (abs r : OsuModel.Sim.Difficulty) = OsuModel.Eval.adaptDifficulty (abs d) := by
  exact ⟨_, rfl, rfl⟩
end OsuProofs
