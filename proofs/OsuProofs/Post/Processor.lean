/-
`beatmap::processor` (Rust) refines `OsuModel.Beatmap` (`Processor.lean`): combo information.
-/
import OsuProofs.Auto.Gen
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

/-- One `UpdateComboInformation` step of `preProcess` (second loop body), on the object list. -/
def uciS (L : List OsuHitObject) (i : Nat) : List OsuHitObject :=
  let last := if i = 0 then none else some L[i - 1]!
  let p := OsuBeatmapProcessor.updateComboInformation last L[i]!
  let L1 := match p.1 with | some l => L.set (i - 1) l | none => L
  L1.set i p.2

theorem is_spinner_ok (h : beatmap.objects.OsuHitObject) :
    beatmap.objects.is_spinner h = ok (abs h : OsuHitObject).isSpinner := by
  unfold beatmap.objects.is_spinner OsuHitObject.isSpinner
  cases hk : h.kind <;> simp [abs, hk]

theorem vec_set_val {α} (v : alloc.vec.Vec α) (i : Usize) (x : α) : (alloc.vec.Vec.set v i x).val = v.val.set i.val x := by
  simp [alloc.vec.Vec.set]

theorem uci_imu_eq {α} (v : alloc.vec.Vec α) (i : Usize) (h : i.val < v.val.length) :
    alloc.vec.Vec.index_mut_usize v i = ok (v.val[i.val]'h, alloc.vec.Vec.set v i) := by
  obtain ⟨⟨a, b⟩, hx, hx1, hx2⟩ := eq_ok_of_spec (alloc.vec.Vec.index_mut_usize_spec v i h)
  rw [hx, hx1, hx2]

theorem uci_imu {α} (v : alloc.vec.Vec α) (i : Usize) (x : α) (h : i.val < v.val.length) :
    alloc.vec.Vec.index_mut_usize (alloc.vec.Vec.set v i x) i = ok (x, alloc.vec.Vec.set (alloc.vec.Vec.set v i x) i) := by
  rw [uci_imu_eq _ _ (by simpa [vec_set_val] using h)]; simp [vec_set_val]

theorem uci_imu0 {α} (v : alloc.vec.Vec α) (i : Usize) (h : i.val < v.val.length) :
    alloc.vec.Vec.index_mut_usize v i = ok (v.val[i.val]'h, alloc.vec.Vec.set v i) := uci_imu_eq v i h

theorem uci_setset {α} (v : alloc.vec.Vec α) (i : Usize) (x y : α) :
    alloc.vec.Vec.set (alloc.vec.Vec.set v i x) i y = alloc.vec.Vec.set v i y := by
  unfold alloc.vec.Vec.set; simp

theorem i32S_wadd (a b : I32) : i32S (core.num.I32.wrapping_add a b) = i32S a + i32S b := rfl

@[simp] theorem uci_nc (h : beatmap.objects.OsuHitObject) : (abs h : OsuHitObject).newCombo = h.new_combo := rfl

theorem uci_set_self (l : List beatmap.objects.OsuHitObject) (k : Nat) (hk : k < l.length) :
    (l.map (abs : _ → OsuHitObject)).set k (abs (l[k]'hk)) = l.map abs := by
  rw [← List.map_set]; simp

theorem i32S_zero : i32S 0#i32 = 0 := by decide
theorem i32S_one : i32S 1#i32 = 1 := by decide

theorem beatmap.processor.update_combo_information_refines (objs : alloc.vec.Vec beatmap.objects.OsuHitObject)
    (i : Usize) (hi : i.val < objs.val.length) :
    ∃ r, beatmap.processor.update_combo_information objs i = ok r ∧
      r.val.map (abs : _ → OsuHitObject) = uciS (objs.val.map abs) i.val := by
  have hget : ∀ k (hk : k < objs.val.length), (objs.val.map (abs : _ → OsuHitObject))[k]! = abs (objs.val[k]'hk) := by
    intro k hk; rw [getElem!_pos _ _ (by simpa using hk)]; simp
  unfold beatmap.processor.update_combo_information uciS OsuBeatmapProcessor.updateComboInformation
  by_cases h0 : i.val = 0
  · have hi0 : ¬ i > 0#usize := by show ¬ (0#usize : Usize).val < i.val; simp [h0]
    simp only [hi0, if_false, bind_ok, vec_index_eq objs i hi, is_spinner_ok, vec_index_mut_eq objs i hi,
      hget i.val hi, if_pos h0, Option.map_none, Option.getD_none, Option.isNone_none]
    cases hs : (abs (objs.val[i.val]'hi) : OsuHitObject).isSpinner <;>
    cases hn : (objs.val[i.val]'hi).new_combo <;>
    simp [hi, uci_imu, uci_imu0, uci_setset, vec_set_val, lift, hs, hn, List.map_set] <;>
    (try congr 1) <;> simp [abs, i32S_wadd, i32S_zero, i32S_one, hn]
  · have hi0 : i > 0#usize := by show (0#usize : Usize).val < i.val; simp; omega
    obtain ⟨i1, hi1, hi1v⟩ := usize_sub_one i (by omega)
    have hi1l : i1.val < objs.val.length := by omega
    have hne : i1.val ≠ i.val := by omega
    simp only [hi0, if_true, bind_ok, hi1, vec_index_eq objs i1 hi1l, vec_index_eq objs i hi, is_spinner_ok,
      vec_index_mut_eq objs i hi, hget i.val hi, if_neg h0, Option.map_some, Option.getD_some, Option.isNone_some,
      show i.val - 1 = i1.val by omega, hget i1.val hi1l]
    cases hs : (abs (objs.val[i.val]'hi) : OsuHitObject).isSpinner <;>
    cases hn : (objs.val[i.val]'hi).new_combo <;>
    cases hl : (abs (objs.val[i1.val]'hi1l) : OsuHitObject).isSpinner <;>
    simp [hi, uci_imu, uci_imu0, uci_setset, vec_set_val, lift, hs, hn, hl, List.map_set, hi0,
      vec_index_mut_eq objs i1 hi1l, uci_set_self _ _ hi1l, vec_index_usize_eq, hne, List.getElem_set_ne hne] <;>
    (try congr 1) <;> (try congr 1) <;> simp [abs, i32S_wadd, i32S_zero, i32S_one, hn]

/-- First `preProcess` loop body (forced new combos), on the object list. -/
def ncS (L : List OsuHitObject) (k : Nat) : List OsuHitObject :=
  if (!L[k]!.isSpinner && (k == 0 || L[k - 1]!.isSpinner)) = true then L.set k { L[k]! with newCombo := true } else L

theorem uciS_length (L : List OsuHitObject) (k : Nat) : (uciS L k).length = L.length := by
  unfold uciS; simp only [List.length_set]; split <;> (try split) <;> simp

theorem ncS_length (L : List OsuHitObject) (k : Nat) : (ncS L k).length = L.length := by
  unfold ncS; split <;> simp

theorem pp_loop0 (n : Nat) (v : alloc.vec.Vec beatmap.objects.OsuHitObject) (j : Usize)
    (hv : v.val.length = n) (hj : j.val < n) :
    ∃ v' j', beatmap.processor.pre_process_loop0.body v j = ok (.cont (v', j')) ∧
      v'.val.map (abs : _ → OsuHitObject) = ncS (v.val.map abs) j.val ∧ v'.val.length = n ∧ j'.val = j.val + 1 := by
  have hi : j.val < v.val.length := by omega
  have hget : ∀ k (hk : k < v.val.length), (v.val.map (abs : _ → OsuHitObject))[k]! = abs (v.val[k]'hk) := by
    intro k hk; rw [getElem!_pos _ _ (by simpa using hk)]; simp
  obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := v.property; omega)
  have hjl : j < alloc.vec.Vec.len v := by show j.val < (alloc.vec.Vec.len v).val; simpa using hi
  unfold beatmap.processor.pre_process_loop0.body ncS
  simp only [hjl, if_true, bind_ok, vec_index_eq v j hi, is_spinner_ok, hget j.val hi]
  by_cases h0 : j.val = 0
  · have hj0 : j = 0#usize := by
      apply UScalar.eq_of_val_eq; simpa using h0
    simp only [show (j = 0#usize) = True from eq_true hj0, if_true, show (j.val == 0) = true by simp [h0],
      Bool.true_or, Bool.and_true]
    cases hs : (abs (v.val[j.val]'hi) : OsuHitObject).isSpinner <;> (try simp only [hs]) <;>
    simp [uci_imu0 v j hi, vec_set_val, hj1, List.map_set, hj1v, hv] <;>
    (try congr 1) <;> simp [abs]
  · have hj0 : ¬ j = 0#usize := by intro h; apply h0; rw [h]; rfl
    obtain ⟨i1, hi1, hi1v⟩ := usize_sub_one j (by omega)
    have hi1l : i1.val < v.val.length := by omega
    simp only [show (j = 0#usize) = False from eq_false hj0, if_false, show (j.val == 0) = false by simp [h0],
      Bool.false_or, hi1, bind_ok, vec_index_eq v i1 hi1l,
      is_spinner_ok, show j.val - 1 = i1.val by omega, hget i1.val hi1l]
    cases hs : (abs (v.val[j.val]'hi) : OsuHitObject).isSpinner <;>
    cases hl : (abs (v.val[i1.val]'hi1l) : OsuHitObject).isSpinner <;> (try simp only [hs, hl]) <;>
    simp [uci_imu0 v j hi, vec_set_val, hj1, List.map_set, hj1v, hv] <;>
    (try congr 1) <;> simp [abs]

theorem pp_loop1 (n : Nat) (v : alloc.vec.Vec beatmap.objects.OsuHitObject) (j : Usize)
    (hv : v.val.length = n) (hj : j.val < n) :
    ∃ v' j', beatmap.processor.pre_process_loop1.body v j = ok (.cont (v', j')) ∧
      v'.val.map (abs : _ → OsuHitObject) = uciS (v.val.map abs) j.val ∧ v'.val.length = n ∧ j'.val = j.val + 1 := by
  have hi : j.val < v.val.length := by omega
  obtain ⟨r, hr, hrv⟩ := beatmap.processor.update_combo_information_refines v j hi
  obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := v.property; omega)
  have hjl : j < alloc.vec.Vec.len v := by show j.val < (alloc.vec.Vec.len v).val; simpa using hi
  refine ⟨r, j1, by simp [beatmap.processor.pre_process_loop1.body, hjl, hr, hj1], hrv, ?_, hj1v⟩
  have := congrArg List.length hrv; simp [uciS_length] at this; omega

/-- Spec loop bodies of `preProcess` as Array functions. -/
def ppG1 (k : Nat) (s : Array OsuHitObject) : Array OsuHitObject :=
  if (!s[k]!.isSpinner && (k == 0 || s[k - 1]!.isSpinner)) = true then s.set! k { s[k]! with newCombo := true } else s

def ppG2 (k : Nat) (s : Array OsuHitObject) : Array OsuHitObject :=
  match (OsuBeatmapProcessor.updateComboInformation (if (k == 0) = true then none else some s[k - 1]!) s[k]!).1 with
  | some l => (s.set! (k - 1) l).set! k (OsuBeatmapProcessor.updateComboInformation (if (k == 0) = true then none else some s[k - 1]!) s[k]!).2
  | _ => s.set! k (OsuBeatmapProcessor.updateComboInformation (if (k == 0) = true then none else some s[k - 1]!) s[k]!).2

def ppG2F (k : Nat) (s : Array OsuHitObject) : Id (ForInStep (Array OsuHitObject)) :=
  match (OsuBeatmapProcessor.updateComboInformation (if (k == 0) = true then none else some s[k - 1]!) s[k]!).1 with
  | some l => pure (ForInStep.yield ((s.set! (k - 1) l).set! k (OsuBeatmapProcessor.updateComboInformation (if (k == 0) = true then none else some s[k - 1]!) s[k]!).2))
  | x => pure (ForInStep.yield (s.set! k (OsuBeatmapProcessor.updateComboInformation (if (k == 0) = true then none else some s[k - 1]!) s[k]!).2))

theorem ppG2F_eq (k : Nat) (s : Array OsuHitObject) : ppG2F k s = .yield (ppG2 k s) := by
  unfold ppG2F ppG2; split <;> rfl

theorem ppG1_toList (k : Nat) (s : Array OsuHitObject) : (ppG1 k s).toList = ncS s.toList k := by
  unfold ppG1 ncS
  simp only [Array.getElem!_eq_toList_getElem!]
  split <;> simp

theorem ppG2_toList (k : Nat) (s : Array OsuHitObject) : (ppG2 k s).toList = uciS s.toList k := by
  unfold ppG2 uciS
  simp only [Array.getElem!_eq_toList_getElem!]
  by_cases hk : k = 0 <;> simp [hk] <;>
    (generalize OsuBeatmapProcessor.updateComboInformation _ _ = p; rcases p with ⟨_ | l, h⟩ <;> simp)

theorem beatmap.processor.pre_process_refines (objs : alloc.vec.Vec beatmap.objects.OsuHitObject) :
    ∃ r, beatmap.processor.pre_process objs = ok r ∧
      OsuBeatmapProcessor.preProcess (abs objs) = abs r := by
  let n := objs.val.length
  have h0 := loop_vec_fold (fun x => beatmap.processor.pre_process_loop0.body x.1 x.2)
    (fun v => v.val.map (abs : _ → OsuHitObject)) (fun k L => ncS L k) n
    (fun v j hv hj => pp_loop0 n v j hv hj)
    (fun v j hv hj => by
      have : ¬ j < alloc.vec.Vec.len v := by show ¬ j.val < (alloc.vec.Vec.len v).val; simp; omega
      simp [beatmap.processor.pre_process_loop0.body, this])
    objs 0#usize rfl (by simp)
  obtain ⟨r1, hl1, hr1⟩ := h0
  have hn1 : r1.val.length = n := by
    have := congrArg List.length hr1
    rw [List.length_map] at this; rw [this]
    have := iterR_inv (fun L : List OsuHitObject => L.length = n) (fun k L => ncS L k)
      (fun k L h => by simp [ncS_length, h]) (n - (0#usize : Usize).val) (0#usize : Usize).val (objs.val.map abs) (by simp [n])
    exact this
  have h1 := loop_vec_fold (fun x => beatmap.processor.pre_process_loop1.body x.1 x.2)
    (fun v => v.val.map (abs : _ → OsuHitObject)) (fun k L => uciS L k) n
    (fun v j hv hj => pp_loop1 n v j hv hj)
    (fun v j hv hj => by
      have : ¬ j < alloc.vec.Vec.len v := by show ¬ j.val < (alloc.vec.Vec.len v).val; simp; omega
      simp [beatmap.processor.pre_process_loop1.body, this])
    r1 0#usize hn1 (by simp)
  obtain ⟨r2, hl2, hr2⟩ := h1
  refine ⟨r2, ?_, ?_⟩
  · unfold beatmap.processor.pre_process beatmap.processor.pre_process_loop0 beatmap.processor.pre_process_loop1
    rw [hl1]; simp only [bind_ok]; exact hl2
  · unfold OsuBeatmapProcessor.preProcess
    simp only [Id.run]
    rw [show (fun (i : Nat) (r : Array OsuHitObject) => (if (!r[i]!.isSpinner && (i == 0 || r[i - 1]!.isSpinner)) = true then
        pure (ForInStep.yield (r.set! i { r[i]! with newCombo := true })) else pure (ForInStep.yield r) : Id _)) =
        fun i r => .yield (ppG1 i r) by funext i r; unfold ppG1; split <;> rfl]
    change (do
      let __s ← forIn [:(abs objs : Array OsuHitObject).size] (abs objs) fun i r => (ForInStep.yield (ppG1 i r) : Id _)
      let __s ← forIn [:__s.size] __s ppG2F
      pure __s : Id _) = (abs r2 : Array OsuHitObject)
    simp only [forIn_range_iterR]
    have e2 : ppG2F = fun k s => .yield (ppG2 k s) := funext fun k => funext fun s => ppG2F_eq k s
    rw [e2]
    have hsz : (abs objs : Array OsuHitObject).size = n := by simp [abs, n]
    have hsz1 : (iterR (fun i r => ForInStep.yield (ppG1 i r)) 0 ((abs objs : Array OsuHitObject).size - 0)
        (abs objs : Array OsuHitObject)).size = n := by
      have := iterR_inv (fun a : Array OsuHitObject => a.size = n) ppG1
        (fun k a h => by rw [← h, ← Array.length_toList, ← Array.length_toList, ppG1_toList, ncS_length])
        ((abs objs : Array OsuHitObject).size - 0) 0 (abs objs) hsz
      exact this
    show iterR _ 0 (_ - 0) _ = _
    rw [hsz1]
    apply Array.toList_inj.mp
    rw [iterR_hom Array.toList ppG2 (fun k L => uciS L k) (fun k s => ppG2_toList k s),
      iterR_hom Array.toList ppG1 (fun k L => ncS L k) (fun k s => ppG1_toList k s), hsz]
    have ha : (abs objs : Array OsuHitObject).toList = objs.val.map abs := by simp [abs]
    have hb : (abs r2 : Array OsuHitObject).toList = r2.val.map abs := by simp [abs]
    rw [ha, hb, hr2, hr1]
    simp


@[step] theorem beatmap.processor.update_combo_information_step (objs : alloc.vec.Vec beatmap.objects.OsuHitObject)
    (i : Usize) (hi : i.val < objs.val.length) :
    beatmap.processor.update_combo_information objs i ⦃ r =>
      r.val.map (abs : _ → OsuHitObject) = uciS (objs.val.map abs) i.val ⦄ :=
  spec_of_ex (beatmap.processor.update_combo_information_refines objs i hi)

@[step] theorem beatmap.processor.pre_process_step (objs : alloc.vec.Vec beatmap.objects.OsuHitObject) :
    beatmap.processor.pre_process objs ⦃ r => OsuBeatmapProcessor.preProcess (abs objs) = abs r ⦄ :=
  spec_of_ex (beatmap.processor.pre_process_refines objs)

/-! ## `objects.set_stack_height` (needed by stacking; uses the `loop_fold_gen'` + `loop_step` automation) -/

theorem beatmap.objects.set_stack_height_refines (h : beatmap.objects.OsuHitObject) (val : I32) :
    ∃ r, beatmap.objects.set_stack_height h val = ok r ∧ OsuHitObject.setStackHeight (abs h) (abs val) = abs r := by
  let g := fun (no : beatmap.objects.NestedObject) => { no with stack_height := val }
  obtain ⟨v, hl, hv⟩ := loop_fold_gen' (fun x => beatmap.objects.set_stack_height_loop.body val x.1 x.2) (·.2)
    h.nested.val.length (by have := h.nested.property; omega)
    (fun x => x.1.val.length = h.nested.val.length) (fun x => x.1.val)
    (fun k L => L.modify k g) (fun y L => y.val = L)
    (by loop_step [beatmap.objects.set_stack_height_loop.body, vec_index_mut_usize_ok, vec_set_val', list_modify_set, g])
    (by loop_end [beatmap.objects.set_stack_height_loop.body])
    (h.nested, 0#usize) rfl (by simp)
  simp only at hl hv
  refine ⟨{ h with stack_height := val, nested := v }, ?_, ?_⟩
  · unfold beatmap.objects.set_stack_height
    rw [show beatmap.objects.set_stack_height_loop h.nested val 0#usize = ok v by
      unfold beatmap.objects.set_stack_height_loop; exact hl]
    simp only [bind_ok]
  · rw [show (0#usize : Usize).val = 0 from rfl, iterR_modify_map] at hv
    simp [OsuHitObject.setStackHeight, abs, hv, g, Function.comp_def]

@[step] theorem beatmap.objects.set_stack_height_step (h : beatmap.objects.OsuHitObject) (val : I32) :
    beatmap.objects.set_stack_height h val ⦃ r => OsuHitObject.setStackHeight (abs h) (abs val) = abs r ⦄ :=
  spec_of_ex (beatmap.objects.set_stack_height_refines h val)

end OsuProofs
