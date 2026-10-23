/-
`sim.step.preceding_end_times_refines` (HANDOFF from sim core, json agent): the `hPE` hypothesis of
`sim.step.mk_ctx_refines` (Eval/JsonMkCtx.lean).
-/
import OsuProofs.Eval.JsonMkCtx
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

section Spec
open OsuModel.Sim

theorem js_forIn_list_ok {α σ ε : Type} (g : α → σ → σ) :
    ∀ (l : List α) (init : σ), forIn (m := Except ε) l init (fun x s => Except.ok (ForInStep.yield (g x s))) =
      .ok (l.foldl (fun s x => g x s) init) := by
  intro l; induction l with
  | nil => intro init; rfl
  | cons x l ih => intro init; simp only [List.forIn_cons, List.foldl_cons]; exact ih _

@[simp] theorem js_forIn_arr_ok {α σ ε : Type} (g : α → σ → σ) (xs : _root_.Array α) (init : σ) :
    forIn (m := Except ε) xs init (fun x s => Except.ok (ForInStep.yield (g x s))) =
      .ok (xs.toList.foldl (fun s x => g x s) init) := by
  rw [← Array.forIn_toList]; exact js_forIn_list_ok g _ _

@[simp] theorem js_ite_ok {ε α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then (Except.ok a : Except ε α) else Except.ok b) = .ok (if c then a else b) := by
  split <;> rfl

@[simp] theorem js_ite_yield {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then ForInStep.yield a else ForInStep.yield b) = ForInStep.yield (if c then a else b) := by
  split <;> rfl

theorem js_mapM_ok {α β ε : Type} (xs : _root_.Array α) (f : α → Except ε β) (h : α → β)
    (hf : ∀ x ∈ xs, f x = .ok (h x)) : xs.mapM f = .ok (xs.map h) := by
  rw [Array.mapM_eq_mapM_toList]
  have : ∀ l : List α, (∀ x ∈ l, f x = .ok (h x)) → l.mapM f = .ok (l.map h) := by
    intro l; induction l with
    | nil => intro _; rfl
    | cons x l ih =>
      intro hl
      simp only [List.mapM_cons, hl x (by simp), ih (fun y hy => hl y (by simp [hy]))]
      rfl
  rw [this _ (fun x hx => hf x (by simpa using hx))]
  simp only [Functor.map, Except.map]
  congr 1
  apply Array.ext'; simp

end Spec

theorem js_bsearch_range {α : Type} (a : _root_.Array α) (cmp : α → Int) :
    ∀ n lo hi (h : hi ≤ a.size), hi - lo ≤ n → lo ≤ hi →
      -(a.size : Int) - 1 ≤ OsuModel.Sim.bsearchBy a cmp lo hi h ∧ OsuModel.Sim.bsearchBy a cmp lo hi h < a.size := by
  intro n; induction n with
  | zero =>
    intro lo hi h hn hle
    rw [OsuModel.Sim.bsearchBy]; rw [dif_neg (by omega)]; omega
  | succ n ih =>
    intro lo hi h hn hle
    rw [OsuModel.Sim.bsearchBy]
    split
    · rename_i hlt
      dsimp only
      split
      · omega
      · split
        · exact ih _ _ _ (by omega) (by omega)
        · exact ih _ _ _ (by omega) (by omega)
    · omega

def js_lookS (E : _root_.Array F64) (hw : Option OsuModel.Sim.HitWindows) (e : F64) : Option F64 :=
  if hw.isNone then none else
  let b := OsuModel.Sim.bsearch E fun x => OsuModel.Sim.compareD x e
  let idx := (if b < 0 then -b - 1 else b) - 1
  if idx < 0 then none else E[idx.toNat]?

def js_entryS (E : _root_.Array F64) (o : OsuModel.Sim.TopObj) : Option F64 × _root_.Array (Option F64) :=
  (js_lookS E o.h.hitWindows o.h.endTime, o.nested.map fun n => js_lookS E n.hitWindows n.endTime)

def js_wtsO (o : OsuModel.Sim.TopObj) : List F64 :=
  (if o.h.hitWindows.isSome then [o.h.endTime] else []) ++
    o.nested.toList.flatMap (fun n => if n.hitWindows.isSome then [n.endTime] else [])

def js_ddStepL (s : List F64) (x : F64) : List F64 :=
  match s.getLast? with
  | none => s ++ [x]
  | some l => if Framework.Bindable.equalsD l x then s else s ++ [x]

def js_ltD (a b : F64) : Bool := decide (OsuModel.Sim.compareD a b < 0)

theorem js_foldl_app {α β : Type} (F : _root_.Array β → α → _root_.Array β) (w : α → List β)
    (hF : ∀ s x, (F s x).toList = s.toList ++ w x) :
    ∀ (l : List α) (init : _root_.Array β), (l.foldl F init).toList = init.toList ++ l.flatMap w := by
  intro l; induction l with
  | nil => intro init; simp
  | cons x l ih => intro init; simp only [List.foldl_cons, ih, hF, List.flatMap_cons, List.append_assoc]

theorem js_foldl_dd (F : _root_.Array F64 → F64 → _root_.Array F64)
    (hF : ∀ s x, (F s x).toList = js_ddStepL s.toList x) :
    ∀ (l : List F64) (init : _root_.Array F64), (l.foldl F init).toList = l.foldl js_ddStepL init.toList := by
  intro l; induction l with
  | nil => intro init; simp
  | cons x l ih => intro init; simp only [List.foldl_cons, ih, hF]

theorem js_precS (P : OsuModel.Sim.Playable) : ∃ E : _root_.Array F64,
    OsuModel.Sim.precedingEndTimes P = .ok (P.objects.map (js_entryS E)) ∧
    E.toList = (OsuModel.Sim.stableSortBy (P.objects.toList.flatMap js_wtsO).toArray js_ltD).toList.foldl js_ddStepL [] := by
  unfold OsuModel.Sim.precedingEndTimes
  simp only [except_bind_ok, except_pure, js_ite_ok, js_ite_yield, js_forIn_arr_ok]
  generalize hT : List.foldl _ #[] P.objects.toList = TS
  generalize hS : OsuModel.Sim.stableSortBy TS _ = SS
  generalize hE : List.foldl _ #[] SS.toList = E
  have hTS : TS = (P.objects.toList.flatMap js_wtsO).toArray := by
    rw [← hT]; apply Array.ext'
    rw [js_foldl_app _ js_wtsO]
    · simp
    · intro s o
      have hn : ∀ (s : _root_.Array F64) (l : List OsuModel.Sim.HObj),
          (l.foldl (fun s x => if x.hitWindows.isSome = true then s.push x.endTime else s) s).toList =
            s.toList ++ l.flatMap (fun n => if n.hitWindows.isSome then [n.endTime] else []) := by
        intro s l
        rw [js_foldl_app _ (fun n => if n.hitWindows.isSome then [n.endTime] else [])]
        intro s n; split <;> simp_all
      split
      · rename_i hc; rw [hn]; simp [js_wtsO, hc]
      · rename_i hc; rw [hn]; simp [js_wtsO, hc]
  have hEE : E.toList = SS.toList.foldl js_ddStepL [] := by
    rw [← hE, js_foldl_dd]
    intro s x
    unfold js_ddStepL
    rw [Array.getLast?_toList]
    cases hb : s.back? with
    | none => simp
    | some l => by_cases h : Framework.Bindable.equalsD l x = true <;> simp [h]
  refine ⟨E, ?_, ?_⟩
  · rw [js_mapM_ok _ _ (js_entryS E) ?hf]
    intro o _
    have hr : ∀ e, -(E.size : Int) - 1 ≤ OsuModel.Sim.bsearch E (fun x => OsuModel.Sim.compareD x e) ∧
        OsuModel.Sim.bsearch E (fun x => OsuModel.Sim.compareD x e) < E.size := fun e =>
      js_bsearch_range E _ E.size 0 E.size (le_refl _) (by omega) (by omega)
    rw [js_mapM_ok _ _ (fun n => js_lookS E n.hitWindows n.endTime) ?hn]
    · simp only [js_entryS, js_lookS]
      have hb := hr o.h.endTime
      generalize OsuModel.Sim.bsearch E (fun x => OsuModel.Sim.compareD x o.h.endTime) = b at hb ⊢
      split_ifs <;> simp only [except_bind_ok] <;> first | rfl | (split <;> rename_i hv <;> simp_all <;> omega)
    · intro n _
      simp only [js_lookS]
      have hb := hr n.endTime
      generalize OsuModel.Sim.bsearch E (fun x => OsuModel.Sim.compareD x n.endTime) = b at hb ⊢
      split_ifs <;> first | rfl | (split <;> rename_i hv <;> simp_all <;> omega)
  · rw [hEE, ← hS, hTS]; rfl

/-! ## Rust side -/

def js_insL (l : List F64) (x : F64) : List F64 :=
  l.insertIdx (OsuModel.Sim.insPos js_ltD l.toArray x l.length (by simp)) x

theorem js_ins_loop (v : alloc.vec.Vec F64) (x : F64) : ∀ n (i : Usize) (hn : i.val = n) (hi : n ≤ v.val.length),
    ∃ p : Usize, sim.step.insert_sorted_f64_loop v x i = ok p ∧
      p.val = OsuModel.Sim.insPos js_ltD v.val.toArray x n (by simpa using hi) := by
  intro n; induction n with
  | zero =>
    intro i hn hi
    refine ⟨i, ?_, by rw [hn]; rfl⟩
    unfold sim.step.insert_sorted_f64_loop
    rw [loop_unfold]
    have : ¬ i > 0#usize := by show ¬ (0#usize).val < i.val; simp [hn]
    simp [sim.step.insert_sorted_f64_loop.body, this]
  | succ n ih =>
    intro i hn hi
    have hgt : i > 0#usize := by show (0#usize).val < i.val; simp [hn]
    obtain ⟨i1, hi1, hi1v⟩ := usize_sub_one i (by omega)
    have hl : i1.val < v.val.length := by omega
    obtain ⟨r, hr, hrv⟩ := sim.geometry.compare_d_refines x (v.val[i1.val]'hl)
    have hins : OsuModel.Sim.insPos js_ltD v.val.toArray x (n + 1) (by simpa using hi) =
        if js_ltD x (v.val[n]'(by omega)) then OsuModel.Sim.insPos js_ltD v.val.toArray x n (by simp; omega) else n + 1 := by
      rw [OsuModel.Sim.insPos]; simp
    have hi1n : i1.val = n := by omega
    by_cases hlt : r < 0#i32
    · obtain ⟨p, hp, hpv⟩ := ih i1 hi1n (by omega)
      refine ⟨p, ?_, ?_⟩
      · unfold sim.step.insert_sorted_f64_loop at hp ⊢
        rw [loop_unfold]
        simp only [sim.step.insert_sorted_f64_loop.body, hgt, if_true, hi1, bind_ok, vec_index_eq' v i1 hl, hr, hlt]
        exact hp
      · rw [hins, hpv]
        have : js_ltD x (v.val[n]'(by omega)) = true := by
          simp only [js_ltD, decide_eq_true_eq]
          have e : (v.val[n]'(by omega)) = v.val[i1.val]'hl := by simp [hi1n]
          rw [e]; show OsuModel.Sim.compareD (abs x) (abs (v.val[i1.val]'hl)) < 0
          rw [hrv]; show r.val < 0; have h' : r.val < (0#i32 : I32).val := hlt; simpa using h'
        simp [this]
    · refine ⟨i, ?_, ?_⟩
      · unfold sim.step.insert_sorted_f64_loop
        rw [loop_unfold]
        simp only [sim.step.insert_sorted_f64_loop.body, hgt, if_true, hi1, bind_ok, vec_index_eq' v i1 hl, hr, hlt,
          if_false]
      · rw [hins]
        have : js_ltD x (v.val[n]'(by omega)) = false := by
          simp only [js_ltD, decide_eq_false_iff_not]
          have e : (v.val[n]'(by omega)) = v.val[i1.val]'hl := by simp [hi1n]
          rw [e]; show ¬ OsuModel.Sim.compareD (abs x) (abs (v.val[i1.val]'hl)) < 0
          rw [hrv]; show ¬ r.val < 0; intro h'; exact hlt (show r.val < (0#i32 : I32).val by simpa using h')
        simp [this, hn]

theorem js_insPos_le {α : Type} (lt : α → α → Bool) (out : _root_.Array α) (x : α) :
    ∀ i (h : i ≤ out.size), OsuModel.Sim.insPos lt out x i h ≤ i := by
  intro i; induction i with
  | zero => intro h; simp [OsuModel.Sim.insPos]
  | succ i ih => intro h; rw [OsuModel.Sim.insPos]; split <;> [have := ih (by omega); skip] <;> omega

theorem js_ins (v : alloc.vec.Vec F64) (x : F64) (hl : v.val.length < Usize.max) :
    ∃ w, sim.step.insert_sorted_f64 v x = ok w ∧ w.val = js_insL v.val x := by
  obtain ⟨p, hp, hpv⟩ := js_ins_loop v x v.val.length (alloc.vec.Vec.len v) (by simp) (le_refl _)
  have hple : p.val ≤ v.val.length := by
    rw [hpv]; have := js_insPos_le js_ltD v.val.toArray x v.val.length (by simp); simpa using this
  obtain ⟨w, hw, hwv⟩ := beatmap.dotnet.insert_at_refines float.F64.Insts.CoreCloneClone (fun _ => rfl) v p x hple hl
  refine ⟨w, ?_, ?_⟩
  · unfold sim.step.insert_sorted_f64; simp only [hp, bind_ok]; exact hw
  · rw [hwv, hpv]; rfl

theorem js_insStep (s : _root_.Array F64) (x : F64) :
    ((s.extract 0 (OsuModel.Sim.insPos js_ltD s x s.size (Nat.le_refl _))).push x ++
      s.extract (OsuModel.Sim.insPos js_ltD s x s.size (Nat.le_refl _)) s.size).toList = js_insL s.toList x := by
  have hle := js_insPos_le js_ltD s x s.size (Nat.le_refl _)
  unfold js_insL
  have e : OsuModel.Sim.insPos js_ltD s.toList.toArray x s.toList.length (by simp) =
      OsuModel.Sim.insPos js_ltD s x s.size (Nat.le_refl _) := by
    congr 1 <;> simp
  rw [e, insertIdx_take_drop _ _ _ (by simpa using hle)]
  simp

theorem js_ssb (l : List F64) : (OsuModel.Sim.stableSortBy l.toArray js_ltD).toList = l.foldl js_insL [] := by
  have key : ∀ (l : List F64) (s : _root_.Array F64), (List.foldl (fun b a =>
      (b.extract 0 (OsuModel.Sim.insPos js_ltD b a b.size (Nat.le_refl _))).push a ++
        b.extract (OsuModel.Sim.insPos js_ltD b a b.size (Nat.le_refl _)) b.size) s l).toList =
      l.foldl js_insL s.toList := by
    intro l; induction l with
    | nil => intro s; rfl
    | cons x l ih => intro s; simp only [List.foldl_cons]; rw [ih, js_insStep]
  unfold OsuModel.Sim.stableSortBy
  simp
  exact key l #[]

theorem js_insL_len (l : List F64) (x : F64) : (js_insL l x).length = l.length + 1 := by
  unfold js_insL
  have := js_insPos_le js_ltD l.toArray x l.length (by simp)
  rw [List.length_insertIdx_of_le_length (by simpa using this)]

theorem js_foldl_ins_len : ∀ (l s : List F64), (l.foldl js_insL s).length = s.length + l.length := by
  intro l; induction l with
  | nil => intro s; simp
  | cons x l ih => intro s; simp only [List.foldl_cons, ih, js_insL_len, List.length_cons]; omega

def js_wR (h : sim.playable.HObj) : List F64 := if h.hit_windows.isSome then [h.end_time] else []

def js_wtsR (o : sim.playable.TopObj) : List F64 := js_wR o.h ++ o.nested.val.flatMap js_wR

theorem js_wtsR_eq (tn : Nat → String) (o : sim.playable.TopObj) : js_wtsO (topS tn o) = js_wtsR o := by
  simp only [js_wtsO, js_wtsR, topS, Array.toList_map, List.flatMap_map]
  congr 1
  · simp [js_wR, hobjS]
  · congr 1; funext n; simp [js_wR, hobjS]

theorem js_ins_opt (ts : alloc.vec.Vec F64) (h : sim.playable.HObj) (hl : ts.val.length + (js_wR h).length < Usize.max) :
    ∃ w, (if core.option.Option.is_some h.hit_windows then sim.step.insert_sorted_f64 ts h.end_time else ok ts) = ok w ∧
      w.val = (js_wR h).foldl js_insL ts.val := by
  by_cases hs : h.hit_windows.isSome = true
  · obtain ⟨w, hw, hwv⟩ := js_ins ts h.end_time (by simp [js_wR, hs] at hl; omega)
    refine ⟨w, ?_, ?_⟩
    · simp only [core.option.Option.is_some, hs, ↓reduceIte]; exact hw
    · simp [js_wR, hs, hwv]
  · refine ⟨ts, ?_, ?_⟩
    · simp only [core.option.Option.is_some, hs, ↓reduceIte, Bool.false_eq_true]
    · simp [js_wR, hs]

theorem js_pwet_loop (v : alloc.vec.Vec sim.playable.HObj) : ∀ n (ts : alloc.vec.Vec F64) (j : Usize),
    v.val.length - j.val = n → j.val ≤ v.val.length →
    ts.val.length + ((v.val.drop j.val).flatMap js_wR).length < Usize.max →
    ∃ w, sim.step.push_windowed_end_times_loop ts v j = ok w ∧
      w.val = ((v.val.drop j.val).flatMap js_wR).foldl js_insL ts.val := by
  intro n; induction n with
  | zero =>
    intro ts j hn hj hl
    refine ⟨ts, ?_, by simp [List.drop_of_length_le (show v.val.length ≤ j.val by omega)]⟩
    unfold sim.step.push_windowed_end_times_loop
    rw [loop_unfold]
    have : ¬ j < alloc.vec.Vec.len v := by rw [vec_lt_len_iff]; omega
    simp [sim.step.push_windowed_end_times_loop.body, this]
  | succ n ih =>
    intro ts j hn hj hl
    have hlt : j.val < v.val.length := by omega
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := v.property; omega)
    have hd : v.val.drop j.val = v.val[j.val]'hlt :: v.val.drop j1.val := by
      rw [hj1v]; exact List.drop_eq_getElem_cons hlt
    rw [hd] at hl ⊢
    simp only [List.flatMap_cons, List.length_append, List.foldl_append] at hl ⊢
    have hw1 : (js_wR (v.val[j.val]'hlt)).length ≤ 1 := by unfold js_wR; split <;> simp
    obtain ⟨t1, ht1, ht1v⟩ := js_ins_opt ts (v.val[j.val]'hlt) (by omega)
    have ht1l : t1.val.length = ts.val.length + (js_wR (v.val[j.val]'hlt)).length := by
      rw [ht1v, js_foldl_ins_len]
    obtain ⟨w, hw, hwv⟩ := ih t1 j1 (by omega) (by omega) (by omega)
    refine ⟨w, ?_, by rw [hwv, ht1v]⟩
    unfold sim.step.push_windowed_end_times_loop at hw ⊢
    rw [loop_unfold]
    have hl' : j < alloc.vec.Vec.len v := by rw [vec_lt_len_iff]; exact hlt
    simp only [sim.step.push_windowed_end_times_loop.body, hl', if_true, vec_index_eq' v j hlt, bind_ok, ht1, hj1]
    exact hw

theorem js_pwet (ts : alloc.vec.Vec F64) (o : sim.playable.TopObj)
    (hl : ts.val.length + (js_wtsR o).length < Usize.max) :
    ∃ w, sim.step.push_windowed_end_times ts o = ok w ∧ w.val = (js_wtsR o).foldl js_insL ts.val := by
  have hw1 : (js_wR o.h).length ≤ 1 := by unfold js_wR; split <;> simp
  simp only [js_wtsR, List.length_append] at hl
  obtain ⟨t1, ht1, ht1v⟩ := js_ins_opt ts o.h (by omega)
  have ht1l : t1.val.length = ts.val.length + (js_wR o.h).length := by rw [ht1v, js_foldl_ins_len]
  obtain ⟨w, hw, hwv⟩ := js_pwet_loop o.nested _ t1 0#usize rfl (by simp)
    (by rw [show (0#usize).val = 0 from rfl, List.drop_zero]; omega)
  refine ⟨w, ?_, ?_⟩
  · unfold sim.step.push_windowed_end_times; simp only [ht1, bind_ok]; exact hw
  · rw [hwv, ht1v]; simp [js_wtsR, List.foldl_append]

theorem js_loop0 (pb : sim.playable.Playable) : ∀ n (sorted : alloc.vec.Vec F64) (i : Usize),
    pb.objects.val.length - i.val = n → i.val ≤ pb.objects.val.length →
    sorted.val.length + ((pb.objects.val.drop i.val).flatMap js_wtsR).length < Usize.max →
    ∃ w, sim.step.preceding_end_times_loop0 pb sorted i = ok (pb.objects, w) ∧
      w.val = ((pb.objects.val.drop i.val).flatMap js_wtsR).foldl js_insL sorted.val := by
  intro n; induction n with
  | zero =>
    intro sorted i hn hi hl
    refine ⟨sorted, ?_, by simp [List.drop_of_length_le (show pb.objects.val.length ≤ i.val by omega)]⟩
    unfold sim.step.preceding_end_times_loop0
    rw [loop_unfold]
    have : ¬ i < alloc.vec.Vec.len pb.objects := by rw [vec_lt_len_iff]; omega
    simp [sim.step.preceding_end_times_loop0.body, this]
  | succ n ih =>
    intro sorted i hn hi hl
    have hlt : i.val < pb.objects.val.length := by omega
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := pb.objects.property; omega)
    have hd : pb.objects.val.drop i.val = pb.objects.val[i.val]'hlt :: pb.objects.val.drop i1.val := by
      rw [hi1v]; exact List.drop_eq_getElem_cons hlt
    rw [hd] at hl ⊢
    simp only [List.flatMap_cons, List.length_append, List.foldl_append] at hl ⊢
    obtain ⟨t1, ht1, ht1v⟩ := js_pwet sorted (pb.objects.val[i.val]'hlt) (by omega)
    have ht1l : t1.val.length = sorted.val.length + (js_wtsR (pb.objects.val[i.val]'hlt)).length := by
      rw [ht1v, js_foldl_ins_len]
    obtain ⟨w, hw, hwv⟩ := ih t1 i1 (by omega) (by omega) (by omega)
    refine ⟨w, ?_, by rw [hwv, ht1v]⟩
    unfold sim.step.preceding_end_times_loop0 at hw ⊢
    rw [loop_unfold]
    have hl' : i < alloc.vec.Vec.len pb.objects := by rw [vec_lt_len_iff]; exact hlt
    simp only [sim.step.preceding_end_times_loop0.body, hl', if_true, vec_index_eq' pb.objects i hlt, bind_ok, ht1, hi1]
    exact hw

theorem js_loop1 (sorted : alloc.vec.Vec F64) : ∀ n (et : alloc.vec.Vec F64) (k : Usize),
    sorted.val.length - k.val = n → k.val ≤ sorted.val.length →
    et.val.length + (sorted.val.length - k.val) < Usize.max →
    ∃ w, sim.step.preceding_end_times_loop1 sorted et k = ok w ∧
      w.val = (sorted.val.drop k.val).foldl js_ddStepL et.val := by
  intro n; induction n with
  | zero =>
    intro et k hn hk hl
    refine ⟨et, ?_, by simp [List.drop_of_length_le (show sorted.val.length ≤ k.val by omega)]⟩
    unfold sim.step.preceding_end_times_loop1
    rw [loop_unfold]
    have : ¬ k < alloc.vec.Vec.len sorted := by rw [vec_lt_len_iff]; omega
    simp [sim.step.preceding_end_times_loop1.body, this]
  | succ n ih =>
    intro et k hn hk hl
    have hlt : k.val < sorted.val.length := by omega
    obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := sorted.property; omega)
    have hd : sorted.val.drop k.val = sorted.val[k.val]'hlt :: sorted.val.drop k1.val := by
      rw [hk1v]; exact List.drop_eq_getElem_cons hlt
    rw [hd]
    simp only [List.foldl_cons]
    have hl' : k < alloc.vec.Vec.len sorted := by rw [vec_lt_len_iff]; exact hlt
    -- one dedup step
    obtain ⟨e1, he1, he1v⟩ : ∃ e1, (if alloc.vec.Vec.len et = 0#usize then alloc.vec.Vec.push et (sorted.val[k.val]'hlt)
        else do
          let i1 ← alloc.vec.Vec.len et - 1#usize
          let f ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice F64) et i1
          let b ← sim.netx.equals_d f (sorted.val[k.val]'hlt)
          if b then ok et else alloc.vec.Vec.push et (sorted.val[k.val]'hlt)) = ok e1 ∧
        e1.val = js_ddStepL et.val (sorted.val[k.val]'hlt) := by
      by_cases h0 : et.val.length = 0
      · have h0' : alloc.vec.Vec.len et = 0#usize := by apply UScalar.eq_of_val_eq; simpa using h0
        have e : et.val = [] := List.eq_nil_of_length_eq_zero h0
        rw [if_pos h0', vec_push_ok et _ (by omega)]
        exact ⟨_, rfl, by simp [js_ddStepL, e]⟩
      · have h0' : ¬ alloc.vec.Vec.len et = 0#usize := by
          intro h; apply h0; have := congrArg UScalar.val h; simpa using this
        rw [if_neg h0']
        obtain ⟨i1, hi1, hi1v⟩ := usize_sub_one (alloc.vec.Vec.len et) (by simp; omega)
        have hi1l : i1.val < et.val.length := by simp at hi1v; omega
        simp only [hi1, bind_ok, vec_index_eq' et i1 hi1l, sim.netx.equals_d_refines]
        have hgl : et.val.getLast? = some (et.val[i1.val]'hi1l) := by
          rw [List.getLast?_eq_getElem?]; simp at hi1v; rw [← hi1v]; simp
        by_cases hq : Framework.Bindable.equalsD (et.val[i1.val]'hi1l) (sorted.val[k.val]'hlt) = true
        · rw [if_pos hq]; exact ⟨_, rfl, by simp [js_ddStepL, hgl, hq]⟩
        · rw [if_neg hq, vec_push_ok et _ (by omega)]; exact ⟨_, rfl, by simp [js_ddStepL, hgl, hq]⟩
    have he1l : e1.val.length ≤ et.val.length + 1 := by
      rw [he1v]; unfold js_ddStepL; split
      · simp
      · split <;> simp
    obtain ⟨w, hw, hwv⟩ := ih e1 k1 (by omega) (by omega) (by omega)
    refine ⟨w, ?_, by rw [hwv, he1v]⟩
    unfold sim.step.preceding_end_times_loop1 at hw ⊢
    rw [loop_unfold]
    simp only [sim.step.preceding_end_times_loop1.body, hl', if_true, vec_index_eq' sorted k hlt, bind_ok]
    rw [he1]; simp only [bind_ok, hk1]
    exact hw

theorem sim.step.prec_look_refines (h64 : System.Platform.numBits = 64) (E : Slice F64) (hn : E.val.length < 2^62)
    (hw : Option sim.playable.HitWindows) (e : F64) :
    sim.step.prec_look E hw e = ok (js_lookS E.val.toArray (hw.map abs) e) := by
  unfold sim.step.prec_look js_lookS
  cases hw with
  | none => simp
  | some w =>
    simp only [Option.map_some, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨b, hb, hbv⟩ := sim.geometry.binary_search_d_refines h64 E e hn
    have hbv' : OsuModel.Sim.bsearch E.val.toArray (fun x => OsuModel.Sim.compareD x e) = b.val := by
      have := hbv; simp only [OsuModel.Sim.binarySearchD] at this
      have ea : (abs E : _root_.Array F64) = E.val.toArray := by simp [abs]
      rw [ea] at this; exact this
    have hr : -(E.val.toArray.size : Int) - 1 ≤ OsuModel.Sim.bsearch E.val.toArray (fun x => OsuModel.Sim.compareD x e) ∧
        OsuModel.Sim.bsearch E.val.toArray (fun x => OsuModel.Sim.compareD x e) < E.val.toArray.size :=
      js_bsearch_range E.val.toArray (fun x => OsuModel.Sim.compareD x e) E.val.toArray.size 0 E.val.toArray.size
        (le_refl _) (by omega) (by omega)
    have hr' : -(E.val.length : Int) - 1 ≤ b.val ∧ b.val < E.val.length := by
      rw [← hbv']; simpa using hr
    simp only [hb, bind_ok]
    rw [hbv']
    -- b1
    obtain ⟨b1, hb1, hb1v⟩ : ∃ b1 : I64, (if b < 0#i64 then (do let i ← -. b; i - 1#i64) else ok b) = ok b1 ∧
        b1.val = (if b.val < 0 then -b.val - 1 else b.val) := by
      by_cases hneg : b.val < 0
      · have hneg' : b < 0#i64 := hneg
        rw [if_pos hneg']
        obtain ⟨q, hq, hqv⟩ := eq_ok_of_spec (IScalar.neg_step b (by simp [IScalar.min, I64.min_eq]; omega))
        obtain ⟨z, hz, hzv⟩ := i64_sub_one q (by rw [hqv]; omega) (by rw [hqv]; omega)
        refine ⟨z, by simp [HNeg.hNeg, hq, hz], ?_⟩
        rw [if_pos hneg, hzv, hqv]
      · have hneg' : ¬ b < 0#i64 := hneg
        rw [if_neg hneg']
        exact ⟨b, rfl, by rw [if_neg hneg]⟩
    simp only [hb1, bind_ok]
    obtain ⟨idx, hidx, hidxv⟩ := i64_sub_one b1 (by rw [hb1v]; split <;> omega) (by rw [hb1v]; split <;> omega)
    simp only [hidx, bind_ok]
    rw [← hb1v, ← hidxv]
    by_cases hge : 0 ≤ idx.val
    · have hge' : idx ≥ 0#i64 := by show (0#i64).val ≤ idx.val; simpa using hge
      have hlt : idx.val.toNat < E.val.length := by
        have := hidxv; rw [hb1v] at this; split at this <;> omega
      rw [if_pos hge', if_neg (by omega)]
      have hc := sim_i64_cast_usize idx hge (by have := hlt; have : E.val.length ≤ Usize.max := E.property; omega)
      have hcl : (IScalar.hcast .Usize idx).val < E.val.length := by rw [hc]; exact hlt
      simp only [lift, bind_ok, slice_index_ok E _ hcl]
      congr 1
      simp [hc, List.getElem?_eq_getElem hlt]
    · have hge' : ¬ idx ≥ 0#i64 := by intro h; apply hge; have : (0#i64).val ≤ idx.val := h; simpa using this
      rw [if_neg hge', if_pos (by omega)]

theorem js_entry_loop (h64 : System.Platform.numBits = 64) (E : Slice F64) (hn : E.val.length < 2^62)
    (o : sim.playable.TopObj) : ∀ n (nested : alloc.vec.Vec (Option F64)) (j : Usize),
    o.nested.val.length - j.val = n → j.val ≤ o.nested.val.length →
    nested.val.length + (o.nested.val.length - j.val) < Usize.max →
    ∃ w, sim.step.prec_end_entry_loop E o nested j = ok (o.h, w) ∧
      w.val = nested.val ++ (o.nested.val.drop j.val).map (fun h => js_lookS E.val.toArray (h.hit_windows.map abs) h.end_time) := by
  intro n; induction n with
  | zero =>
    intro nested j hn' hj hl
    refine ⟨nested, ?_, by simp [List.drop_of_length_le (show o.nested.val.length ≤ j.val by omega)]⟩
    unfold sim.step.prec_end_entry_loop
    rw [loop_unfold]
    have : ¬ j < alloc.vec.Vec.len o.nested := by rw [vec_lt_len_iff]; omega
    simp [sim.step.prec_end_entry_loop.body, this]
  | succ n ih =>
    intro nested j hn' hj hl
    have hlt : j.val < o.nested.val.length := by omega
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := o.nested.property; omega)
    have hd : o.nested.val.drop j.val = o.nested.val[j.val]'hlt :: o.nested.val.drop j1.val := by
      rw [hj1v]; exact List.drop_eq_getElem_cons hlt
    have hpl : nested.val.length < Usize.max := by omega
    obtain ⟨w, hw, hwv⟩ := ih (vpush nested (js_lookS E.val.toArray ((o.nested.val[j.val]'hlt).hit_windows.map abs) (o.nested.val[j.val]'hlt).end_time) hpl) j1 (by omega) (by omega) (by simp; omega)
    refine ⟨w, ?_, by rw [hwv, hd]; simp⟩
    have hl' : j < alloc.vec.Vec.len o.nested := by rw [vec_lt_len_iff]; exact hlt
    have hb : sim.step.prec_end_entry_loop.body E o nested j = ok (.cont (vpush nested (js_lookS E.val.toArray ((o.nested.val[j.val]'hlt).hit_windows.map abs) (o.nested.val[j.val]'hlt).end_time) hpl, j1)) := by
      simp only [sim.step.prec_end_entry_loop.body, hl', if_true, vec_index_eq' o.nested j hlt, bind_ok,
        sim.step.prec_look_refines h64 E hn, vec_push_ok nested (js_lookS E.val.toArray ((o.nested.val[j.val]'hlt).hit_windows.map abs) (o.nested.val[j.val]'hlt).end_time) hpl, hj1]
    unfold sim.step.prec_end_entry_loop at hw ⊢
    rw [loop_unfold]
    dsimp only
    rw [hb]
    simp only [bind_ok]
    exact hw

theorem sim.step.prec_end_entry_refines (h64 : System.Platform.numBits = 64) (E : Slice F64) (hn : E.val.length < 2^62)
    (o : sim.playable.TopObj) (hno : o.nested.val.length < Usize.max) :
    ∃ pe, sim.step.prec_end_entry E o = ok pe ∧
      (pe.top, pe.nested.val.toArray) = js_entryS E.val.toArray (topS ev_tn o) := by
  obtain ⟨w, hw, hwv⟩ := js_entry_loop h64 E hn o _ (alloc.vec.Vec.new _) 0#usize rfl (by simp)
    (by simp; omega)
  refine ⟨{ top := js_lookS E.val.toArray (o.h.hit_windows.map abs) o.h.end_time, nested := w }, ?_, ?_⟩
  · unfold sim.step.prec_end_entry
    simp only [hw, bind_ok, sim.step.prec_look_refines h64 E hn]
    rfl
  · simp [js_entryS, topS, hobjS, hwv, Function.comp_def]

def js_peE (p : sim.state.PrecEnd) : Option F64 × _root_.Array (Option F64) := (p.top, p.nested.val.toArray)

theorem js_loop2 (h64 : System.Platform.numBits = 64) (v : alloc.vec.Vec sim.playable.TopObj) (et : alloc.vec.Vec F64)
    (hn : et.val.length < 2^62) (hno : ∀ o ∈ v.val, o.nested.val.length < Usize.max) :
    ∀ n (out : alloc.vec.Vec sim.state.PrecEnd) (q : Usize),
    v.val.length - q.val = n → q.val ≤ v.val.length →
    out.val.length + (v.val.length - q.val) < Usize.max →
    ∃ w, sim.step.preceding_end_times_loop2 v et out q = ok w ∧
      w.val.map js_peE = out.val.map js_peE ++ (v.val.drop q.val).map (fun o => js_entryS et.val.toArray (topS ev_tn o)) := by
  have hn' : (alloc.vec.Vec.deref et).val.length < 2^62 := by rw [ms_deref_val]; exact hn
  intro n; induction n with
  | zero =>
    intro out q hq hql hl
    refine ⟨out, ?_, by simp [List.drop_of_length_le (show v.val.length ≤ q.val by omega)]⟩
    unfold sim.step.preceding_end_times_loop2
    rw [loop_unfold]
    have : ¬ q < alloc.vec.Vec.len v := by rw [vec_lt_len_iff]; omega
    simp [sim.step.preceding_end_times_loop2.body, this]
  | succ n ih =>
    intro out q hq hql hl
    have hlt : q.val < v.val.length := by omega
    obtain ⟨q1, hq1, hq1v⟩ := usize_add_one q (by have := v.property; omega)
    have hd : v.val.drop q.val = v.val[q.val]'hlt :: v.val.drop q1.val := by
      rw [hq1v]; exact List.drop_eq_getElem_cons hlt
    obtain ⟨pe, hpe, hpev⟩ := sim.step.prec_end_entry_refines h64 (alloc.vec.Vec.deref et) hn' (v.val[q.val]'hlt)
      (hno _ (List.getElem_mem hlt))
    have hpl : out.val.length < Usize.max := by omega
    obtain ⟨w, hw, hwv⟩ := ih (vpush out pe hpl) q1 (by omega) (by omega) (by simp; omega)
    refine ⟨w, ?_, ?_⟩
    · have hl' : q < alloc.vec.Vec.len v := by rw [vec_lt_len_iff]; exact hlt
      have hb : sim.step.preceding_end_times_loop2.body v et out q = ok (.cont (vpush out pe hpl, q1)) := by
        simp only [sim.step.preceding_end_times_loop2.body, hl', if_true, vec_index_eq' v q hlt, bind_ok, hpe,
          vec_push_ok out pe hpl, hq1]
      unfold sim.step.preceding_end_times_loop2 at hw ⊢
      rw [loop_unfold]
      dsimp only
      rw [hb]
      simp only [bind_ok]
      exact hw
    · rw [hwv, hd]
      simp only [ms_deref_val] at hpev
      simp [js_peE, hpev]

theorem js_foldl_dd_len : ∀ (l s : List F64), (l.foldl js_ddStepL s).length ≤ s.length + l.length := by
  intro l; induction l with
  | nil => intro s; simp
  | cons x l ih =>
    intro s; simp only [List.foldl_cons]
    have h1 : (js_ddStepL s x).length ≤ s.length + 1 := by
      unfold js_ddStepL; split
      · simp
      · split <;> simp
    have := ih (js_ddStepL s x); simp only [List.length_cons]; omega

/-- `preceding_end_times` refines `precedingEndTimes` (the `hPE` hypothesis of `sim.step.mk_ctx_refines`).
Size premises: the windowed end-time count is < 2^62, each object's nested count < Usize.max, and the
object count < Usize.max. -/
theorem sim.step.preceding_end_times_refines (h64 : System.Platform.numBits = 64) (pb : sim.playable.Playable)
    (hw : (pb.objects.val.flatMap js_wtsR).length < 2^62)
    (hno : ∀ o ∈ pb.objects.val, o.nested.val.length < Usize.max) (hob : pb.objects.val.length < Usize.max) :
    ∃ v, sim.step.preceding_end_times pb = ok v ∧
      OsuModel.Sim.precedingEndTimes (playableS ev_tn pb) = .ok (js_peS v) := by
  have hmax : (2:Nat)^62 < Usize.max := by simp [Usize.max, h64, Usize.numBits]
  obtain ⟨s, hs, hsv⟩ := js_loop0 pb _ (alloc.vec.Vec.new F64) 0#usize rfl (by simp) (by have := hw; simp at this ⊢; omega)
  have hsl : s.val.length = (pb.objects.val.flatMap js_wtsR).length := by
    rw [hsv, js_foldl_ins_len]; simp
  obtain ⟨et, het, hetv⟩ := js_loop1 s _ (alloc.vec.Vec.new F64) 0#usize rfl (by simp) (by simp; omega)
  have hetl : et.val.length < 2^62 := by
    have := js_foldl_dd_len s.val []; rw [hetv]; simp at this ⊢; omega
  obtain ⟨w, hw2, hwv⟩ := js_loop2 h64 pb.objects et hetl hno _ (alloc.vec.Vec.new _) 0#usize rfl (by simp)
    (by simp; omega)
  refine ⟨w, ?_, ?_⟩
  · unfold sim.step.preceding_end_times
    simp [hs, het, hw2]
  · obtain ⟨E, hE, hEv⟩ := js_precS (playableS ev_tn pb)
    have hfl : (playableS ev_tn pb).objects.toList.flatMap js_wtsO = pb.objects.val.flatMap js_wtsR := by
      simp [playableS, List.flatMap_map, Function.comp_def, js_wtsR_eq]
    rw [hfl, js_ssb] at hEv
    have hEe : E = et.val.toArray := by
      apply Array.ext'; rw [hEv, hetv, hsv]; simp
    rw [hE, hEe]
    congr 1
    simp only [js_peS]
    have h2 : (w.val.map fun p => (p.top, p.nested.val.toArray)) = w.val.map js_peE := rfl
    rw [h2, hwv]; simp [playableS]

-- FRAGMENT-OF: OsuModel.Sim.precedingEndTimes (one insertion step of its stableSortBy, as js_insL; bridged by js_ssb in sim.step.preceding_end_times_refines)
theorem sim.step.insert_sorted_f64_refines (v : alloc.vec.Vec F64) (x : F64) (hl : v.val.length < Usize.max) :
    ∃ w, sim.step.insert_sorted_f64 v x = ok w ∧ w.val = js_insL v.val x := js_ins v x hl

-- FRAGMENT-OF: OsuModel.Sim.precedingEndTimes (one object's windowed end times js_wtsO, inserted; bridged in sim.step.preceding_end_times_refines)
theorem sim.step.push_windowed_end_times_refines (ts : alloc.vec.Vec F64) (o : sim.playable.TopObj)
    (hl : ts.val.length + (js_wtsR o).length < Usize.max) :
    ∃ w, sim.step.push_windowed_end_times ts o = ok w ∧ w.val = (js_wtsR o).foldl js_insL ts.val := js_pwet ts o hl

end OsuProofs
