/-
`eval::mods_json` value layer (json agent, D46): named refinement theorems for `value_f`, `value`,
`array_value`, `array_items(_rec)`, `object_value`, `object_items(_rec)` on top of the eval agent's
Eval/ModsJson.lean (`ev_value_f_main` = induction on the nesting fuel vs `SimJson.valueF`).

Statements: the Rust result is related (`ev_vRel`: same value / remaining input, or the same message) to the
spec parser `SimJson.valueF` run on the remaining input `(strS s).drop p`. The array/object entry points are
called after the opening bracket was consumed, so their spec is `valueF (fuel+1)` on `'[' :: rest` /
`'{' :: rest`. The `_rec` (accumulator) forms are stated against the spec's own `repeat` loop
(`forIn Lean.Loop.mk acc (ev_arrBody f)`; `ev_arrBody`/`ev_objBody` are the loop bodies of `valueF`, bridge
`ev_valueF_arr`/`ev_valueF_obj` proved in Eval/ModsJson.lean, so these are not fragments).
Side conditions as in Eval/ModsJson.lean: valid scalar values, `len + 8 ≤ usize::MAX`, `len < 2^62`.
-/
import OsuProofs.Eval.ModsJson
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

theorem eval.mods_json.value_f_refines (s : Slice U32) (hs : ValidStr s) (hlen : s.val.length + 8 ≤ Usize.max)
    (h62 : s.val.length < 2^62) (p fuel : Usize) (hp : p.val ≤ s.val.length) :
    ∃ r, eval.mods_json.value_f s p fuel = ok r ∧
      ev_vRel s p.val r (SimJson.valueF fuel.val ((strS s).drop p.val)) :=
  ev_value_f_main s hs hlen h62 fuel.val fuel rfl p hp

/-- the spec `value` on a remaining input `L` is `valueF (L.length + 1) L` -/
theorem js_value_run (L : List Char) : (SimJson.value).run L = SimJson.valueF (L.length + 1) L := rfl

theorem eval.mods_json.value_refines (s : Slice U32) (hs : ValidStr s) (hlen : s.val.length + 8 ≤ Usize.max)
    (h62 : s.val.length < 2^62) (p : Usize) (hp : p.val ≤ s.val.length) :
    ∃ r, eval.mods_json.value s p = ok r ∧
      ev_vRel s p.val r ((SimJson.value).run ((strS s).drop p.val)) := by
  rw [js_value_run]
  have hmax := slice_len_lt s
  have hdl : ((strS s).drop p.val).length = s.val.length - p.val := by simp [strS_length]
  obtain ⟨rest, hrest, hrv⟩ : ∃ rest : Usize, (if p < Slice.len s then Slice.len s - p else ok 0#usize) = ok rest ∧
      rest.val = s.val.length - p.val := by
    by_cases hlt : p.val < s.val.length
    · have hlt' : p < Slice.len s := (slice_lt_len_iff p s).mpr hlt
      obtain ⟨z, hz, hzv, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := Slice.len s) (y := p) (by simp; omega))
      exact ⟨z, by simp [hlt', hz], by simp at hzv; omega⟩
    · have hlt' : ¬ p < Slice.len s := by rw [slice_lt_len_iff]; exact hlt
      exact ⟨0#usize, by simp [hlt'], by simp; omega⟩
  obtain ⟨f1, hf1, hf1v⟩ := usize_add_one rest (by omega)
  obtain ⟨r, hr, hrel⟩ := eval.mods_json.value_f_refines s hs hlen h62 p f1 hp
  refine ⟨r, ?_, ?_⟩
  · unfold eval.mods_json.value; simp only [hrest, bind_ok, hf1]; exact hr
  · rw [hdl, ← hrv, ← hf1v]; exact hrel

theorem js_wsL_lbr (L : List Char) : SimJson.wsL ('[' :: L) = '[' :: L := by simp [SimJson.wsL]
theorem js_wsL_lbc (L : List Char) : SimJson.wsL ('{' :: L) = '{' :: L := by simp [SimJson.wsL]

/-- `array_value` (after `[`) = the array branch of `valueF (fuel+1)` -/
theorem eval.mods_json.array_value_refines (s : Slice U32) (hs : ValidStr s) (hlen : s.val.length + 8 ≤ Usize.max)
    (h62 : s.val.length < 2^62) (p fuel : Usize) (hp : p.val ≤ s.val.length) :
    ∃ r, eval.mods_json.array_value s p fuel = ok r ∧
      ev_vRel s p.val r (SimJson.valueF (fuel.val + 1) ('[' :: (strS s).drop p.val)) := by
  rw [ev_valueF_arr fuel.val _ _ (js_wsL_lbr _)]
  exact ev_array_value s hs hlen fuel fuel.val (ev_value_f_main s hs hlen h62 fuel.val fuel rfl) p hp

/-- `object_value` (after `{`) = the object branch of `valueF (fuel+1)` -/
theorem eval.mods_json.object_value_refines (s : Slice U32) (hs : ValidStr s) (hlen : s.val.length + 8 ≤ Usize.max)
    (h62 : s.val.length < 2^62) (p fuel : Usize) (hp : p.val ≤ s.val.length) :
    ∃ r, eval.mods_json.object_value s p fuel = ok r ∧
      ev_vRel s p.val r (SimJson.valueF (fuel.val + 1) ('{' :: (strS s).drop p.val)) := by
  rw [ev_valueF_obj fuel.val _ _ (js_wsL_lbc _)]
  exact ev_object_value s hs hlen h62 fuel fuel.val (ev_value_f_main s hs hlen h62 fuel.val fuel rfl) p hp

/-- `array_items_rec` with accumulator `xs` = the spec's array `repeat` loop from state `xs` -/
theorem eval.mods_json.array_items_rec_refines (s : Slice U32) (hs : ValidStr s)
    (hlen : s.val.length + 8 ≤ Usize.max) (h62 : s.val.length < 2^62)
    (q fuel : Usize) (xs : alloc.vec.Vec eval.mods_json.V) (hq : q.val ≤ s.val.length)
    (hxs : xs.val.length ≤ q.val) (hok : ∀ x ∈ xs.val, ev_vOk x) :
    ∃ r, eval.mods_json.array_items_rec s q fuel xs = ok r ∧
      ev_itRel ev_vS ev_vOk s q.val r
        ((forIn Lean.Loop.mk (xs.val.map ev_vS).toArray (ev_arrBody fuel.val) : EvP _).run ((strS s).drop q.val)) :=
  ev_array_items_rec s hs hlen fuel fuel.val (ev_value_f_main s hs hlen h62 fuel.val fuel rfl) q xs hq hxs hok

/-- `object_items_rec` with accumulator `kvs` = the spec's object `repeat` loop from state `kvs` -/
theorem eval.mods_json.object_items_rec_refines (s : Slice U32) (hs : ValidStr s)
    (hlen : s.val.length + 8 ≤ Usize.max) (h62 : s.val.length < 2^62)
    (q fuel : Usize) (kvs : alloc.vec.Vec (alloc.vec.Vec U32 × eval.mods_json.V)) (hq : q.val ≤ s.val.length)
    (hxs : kvs.val.length ≤ q.val) (hok : ∀ x ∈ kvs.val, ev_VV x.1 ∧ ev_vOk x.2) :
    ∃ r, eval.mods_json.object_items_rec s q fuel kvs = ok r ∧
      ev_itRel (fun kv => (vstrS kv.1, ev_vS kv.2)) (fun kv => ev_VV kv.1 ∧ ev_vOk kv.2) s q.val r
        ((forIn Lean.Loop.mk (kvs.val.map fun kv => (vstrS kv.1, ev_vS kv.2)).toArray (ev_objBody fuel.val) : EvP _).run
          ((strS s).drop q.val)) :=
  ev_object_items_rec s hs hlen h62 fuel fuel.val (ev_value_f_main s hs hlen h62 fuel.val fuel rfl) q kvs hq hxs hok

end OsuProofs

namespace OsuProofs
open OsuImpl
theorem js_wsL_idem : ∀ L, SimJson.wsL (SimJson.wsL L) = SimJson.wsL L
  | [] => rfl
  | c :: cs => by
    by_cases h : (c == ' ' || c == '\n' || c == '\t' || c == '\r') = true
    · rw [show SimJson.wsL (c :: cs) = SimJson.wsL cs from by simp only [SimJson.wsL, if_pos h]]
      exact js_wsL_idem cs
    · rw [show SimJson.wsL (c :: cs) = c :: cs from by simp only [SimJson.wsL, if_neg h]]
      simp only [SimJson.wsL, if_neg h]

theorem js_valueF_wsL (f : Nat) (L : List Char) : SimJson.valueF f (SimJson.wsL L) = SimJson.valueF f L := by
  cases f with
  | zero => rfl
  | succ f =>
    show StateT.run (SimJson.valueF (f+1)) (SimJson.wsL L) = StateT.run (SimJson.valueF (f+1)) L
    unfold SimJson.valueF SimJson.ws
    simp only [StateT.run_bind, StateT.run_modify, pure_bind, js_wsL_idem]

theorem js_expect_wsL (c : Char) (L : List Char) : SimJson.expect c (SimJson.wsL L) = SimJson.expect c L := by
  rw [ev_expect_spec, ev_expect_spec, js_wsL_idem]

theorem js_arr_loop_wsL (f : Nat) (xs : Array SimJson.V) (L : List Char) :
    (forIn Lean.Loop.mk xs (ev_arrBody f) : EvP _).run (SimJson.wsL L) =
      (forIn Lean.Loop.mk xs (ev_arrBody f) : EvP _).run L := by
  rw [ev_arr_loop, ev_arr_loop, js_valueF_wsL]

theorem js_obj_loop_wsL (f : Nat) (xs : Array (String × SimJson.V)) (L : List Char) :
    (forIn Lean.Loop.mk xs (ev_objBody f) : EvP _).run (SimJson.wsL L) =
      (forIn Lean.Loop.mk xs (ev_objBody f) : EvP _).run L := by
  rw [ev_obj_loop, ev_obj_loop, js_expect_wsL]
end OsuProofs

namespace OsuProofs
open OsuImpl
/-- `array_items` (at the first element, after `[` and whitespace) = the array branch of `valueF (fuel+1)` when the
array is not empty -/
theorem eval.mods_json.array_items_refines (s : Slice U32) (hs : ValidStr s)
    (hlen : s.val.length + 8 ≤ Usize.max) (h62 : s.val.length < 2^62) (p fuel : Usize) (hp : p.val ≤ s.val.length)
    (hb : (SimJson.wsL ((strS s).drop p.val)).head? ≠ some ']') :
    ∃ r, eval.mods_json.array_items s p fuel = ok r ∧
      ev_vRel s p.val (ev_wrapR eval.mods_json.V.Arr r) (SimJson.valueF (fuel.val + 1) ('[' :: (strS s).drop p.val)) := by
  rw [ev_valueF_arr fuel.val _ _ (js_wsL_lbr _), if_neg (by simpa using hb), js_arr_loop_wsL]
  obtain ⟨r, hr, hrel⟩ := eval.mods_json.array_items_rec_refines s hs hlen h62 p fuel (alloc.vec.Vec.new _) hp
    (by simp) (by simp)
  rw [show ((alloc.vec.Vec.new eval.mods_json.V).val.map ev_vS).toArray = #[] by simp] at hrel
  refine ⟨r, by unfold eval.mods_json.array_items; exact hr, ?_⟩
  revert hrel
  cases r with
  | Ok xq =>
    obtain ⟨xs, q1⟩ := xq
    cases ((forIn Lean.Loop.mk #[] (ev_arrBody fuel.val) : EvP _).run ((strS s).drop p.val)) with
    | ok AL =>
      obtain ⟨A, L⟩ := AL
      rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨by simp [h1], h2, by omega, h4, (ev_vOk_arr xs).mpr h5⟩
    | error _ => intro h; exact h.elim
  | Err e =>
    cases ((forIn Lean.Loop.mk #[] (ev_arrBody fuel.val) : EvP _).run ((strS s).drop p.val)) with
    | ok _ => intro h; exact h.elim
    | error _ => intro h; exact h

/-- `object_items` (at the first member, after `{` and whitespace) = the object branch of `valueF (fuel+1)` when
the object is not empty -/
theorem eval.mods_json.object_items_refines (s : Slice U32) (hs : ValidStr s)
    (hlen : s.val.length + 8 ≤ Usize.max) (h62 : s.val.length < 2^62) (p fuel : Usize) (hp : p.val ≤ s.val.length)
    (hb : (SimJson.wsL ((strS s).drop p.val)).head? ≠ some '}') :
    ∃ r, eval.mods_json.object_items s p fuel = ok r ∧
      ev_vRel s p.val (ev_wrapR eval.mods_json.V.Obj r) (SimJson.valueF (fuel.val + 1) ('{' :: (strS s).drop p.val)) := by
  rw [ev_valueF_obj fuel.val _ _ (js_wsL_lbc _), if_neg (by simpa using hb), js_obj_loop_wsL]
  obtain ⟨r, hr, hrel⟩ := eval.mods_json.object_items_rec_refines s hs hlen h62 p fuel (alloc.vec.Vec.new _) hp
    (by simp) (by simp)
  rw [show ((alloc.vec.Vec.new (alloc.vec.Vec U32 × eval.mods_json.V)).val.map
    fun kv => (vstrS kv.1, ev_vS kv.2)).toArray = #[] by simp] at hrel
  refine ⟨r, by unfold eval.mods_json.object_items; exact hr, ?_⟩
  revert hrel
  cases r with
  | Ok xq =>
    obtain ⟨xs, q1⟩ := xq
    cases ((forIn Lean.Loop.mk #[] (ev_objBody fuel.val) : EvP _).run ((strS s).drop p.val)) with
    | ok AL =>
      obtain ⟨A, L⟩ := AL
      rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨by simp [h1], h2, by omega, h4, (ev_vOk_obj xs).mpr h5⟩
    | error _ => intro h; exact h.elim
  | Err e =>
    cases ((forIn Lean.Loop.mk #[] (ev_objBody fuel.val) : EvP _).run ((strS s).drop p.val)) with
    | ok _ => intro h; exact h.elim
    | error _ => intro h; exact h
end OsuProofs
