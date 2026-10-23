/-
Generator mods, part 7 (gen agent): Target Practice combo fix-up: `beatmap::mod_target_practice::set_combo`,
`renumber_combo` (one `GroupBy` group, spec `gen_grpS`), `fix_combo_info` (spec normal form `gen_fci_spec`).
-/
import OsuProofs.Post.GenRD5
import OsuProofs.Post.TPB
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl

theorem beatmap.mod_target_practice.set_combo_refines (h : beatmap.objects.OsuHitObject) (g jj : I32) :
    beatmap.mod_target_practice.set_combo h g jj = ok { h with combo_index := g, index_in_current_combo := jj } := rfl

/-- positions `j ≥ k` with `m[j] = key` -/
def gen_idxs (m : List I32) (key : I32) (k : Nat) : List Nat :=
  (List.range' k (m.length - k)).filter (fun j => decide (m[j]! = key))

/-- spec-side group renumbering (`fixComboInfo`'s inner `for k in idxs`) -/
def gen_applyIdx (out : Array OsuHitObject) : List Nat → Int32 → Int32 → Array OsuHitObject
  | [], _, _ => out
  | k :: rest, g, j => gen_applyIdx (out.set! k { out[k]! with comboIndex := g, indexInCurrentCombo := j }) rest g (j + 1)

theorem gen_idxs_ge (m : List I32) (key : I32) (k : Nat) (h : m.length ≤ k) : gen_idxs m key k = [] := by
  simp [gen_idxs, show m.length - k = 0 by omega]

theorem gen_idxs_match (m : List I32) (key : I32) (k : Nat) (hk : k < m.length) (hm : m[k] = key) :
    gen_idxs m key k = k :: gen_idxs m key (k + 1) := by
  unfold gen_idxs
  rw [show m.length - k = (m.length - (k + 1)) + 1 by omega, List.range'_succ]
  simp [List.filter_cons, List.getElem?_eq_getElem hk, hm]

theorem gen_idxs_nomatch (m : List I32) (key : I32) (k : Nat) (hk : k < m.length) (hm : m[k] ≠ key) :
    gen_idxs m key k = gen_idxs m key (k + 1) := by
  unfold gen_idxs
  rw [show m.length - k = (m.length - (k + 1)) + 1 by omega, List.range'_succ]
  simp [List.filter_cons, List.getElem?_eq_getElem hk, hm]

/-- skipping to the next match (`next_match`) does not change the remaining positions -/
theorem gen_idxs_skip (m : List I32) (key : I32) :
    ∀ k, gen_idxs m key k = gen_idxs m key (match (m.drop k).findIdx? (fun x => decide (x = key)) with
        | some j => k + j | none => max k m.length) := by
  intro k
  induction hn : m.length - k using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    by_cases hk : k < m.length
    · rw [List.drop_eq_getElem_cons hk, List.findIdx?_cons]
      by_cases hm : m[k] = key
      · simp [hm]
      · simp only [hm, decide_false, Bool.false_eq_true, if_false]
        rw [gen_idxs_nomatch m key k hk hm, ih (m.length - (k + 1)) (by omega) (k + 1) rfl]
        cases h : List.findIdx? (fun x => decide (x = key)) (List.drop (k + 1) m) with
        | none => simp; congr 1; omega
        | some j => simp; congr 1; omega
    · rw [List.drop_eq_nil_of_le (by omega)]
      simp only [List.findIdx?_nil]
      rw [gen_idxs_ge m key k (by omega), gen_idxs_ge m key _ (Nat.le_max_right _ _)]

theorem gen_rn_loop (mapped : Slice I32) (key g : I32) :
    ∀ (hos : alloc.vec.Vec beatmap.objects.OsuHitObject) (jj : I32) (last k : Usize),
      hos.val.length = mapped.val.length → (∀ hk : k.val < mapped.val.length, mapped.val[k.val] = key) →
      ∃ r, beatmap.mod_target_practice.renumber_combo_loop hos mapped key g jj last k = ok r ∧
        r.1.val.length = hos.val.length ∧
        (abs r.1 : Array OsuHitObject) = gen_applyIdx (abs hos) (gen_idxs mapped.val key k.val) (i32S g) (i32S jj) ∧
        r.2.val = ((gen_idxs mapped.val key k.val).getLast?).getD last.val := by
  intro hos jj last k
  induction hn : mapped.val.length - k.val using Nat.strong_induction_on generalizing hos jj last k with
  | _ n ih =>
    intro hl hm
    unfold beatmap.mod_target_practice.renumber_combo_loop
    rw [loop_unfold]
    by_cases hk : k.val < mapped.val.length
    · have hkh : k.val < hos.val.length := by omega
      obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := mapped.property; omega)
      obtain ⟨k2, hk2, hk2v⟩ := beatmap.mod_target_practice.next_match_refines mapped key k1
      have key_fact : ∀ K (hK : K < mapped.val.length),
          K = (match (mapped.val.drop k1.val).findIdx? (fun x => decide (x = key)) with
            | some j => k1.val + j | none => max k1.val mapped.val.length) → mapped.val[K] = key := by
        intro K hK hKe
        cases h : List.findIdx? (fun x => decide (x = key)) (List.drop k1.val mapped.val) with
        | none =>
          simp only [h] at hKe
          rw [hKe] at hK
          exact absurd hK (Nat.not_lt.mpr (Nat.le_max_right _ _))
        | some j =>
          simp only [h] at hKe
          subst hKe
          obtain ⟨hj, hj2, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
          simp at hj2
          simpa [List.getElem_drop] using hj2
      have hm2 : ∀ hk : k2.val < mapped.val.length, mapped.val[k2.val] = key := fun hk' => key_fact _ hk' hk2v
      have hsk : gen_idxs mapped.val key k.val = k.val :: gen_idxs mapped.val key k2.val := by
        rw [gen_idxs_match _ _ _ hk (hm hk), hk2v, ← hk1v]
        first | rw [← gen_idxs_skip] | exact congrArg _ (gen_idxs_skip _ _ _)
      have hk2ge : k1.val ≤ k2.val := by
        rw [hk2v]
        cases h : List.findIdx? (fun x => decide (x = key)) (List.drop k1.val mapped.val) with
        | none => exact Nat.le_max_left _ _
        | some j => simp only; omega
      obtain ⟨r, hr, hrl, hra, hrlast⟩ := ih (mapped.val.length - k2.val) (by omega)
        (alloc.vec.Vec.set hos k { (hos.val[k.val]'hkh) with combo_index := g, index_in_current_combo := jj })
        (core.num.I32.wrapping_add jj 1#i32) k k2 rfl (by simp [vec_set_val', hl]) hm2
      refine ⟨r, ?_, by rw [hrl]; simp [vec_set_val'], ?_, ?_⟩
      · have hb : beatmap.mod_target_practice.renumber_combo_loop.body mapped key g hos jj last k =
            ok (.cont (alloc.vec.Vec.set hos k { (hos.val[k.val]'hkh) with combo_index := g, index_in_current_combo := jj },
              core.num.I32.wrapping_add jj 1#i32, k, k2)) := by
          simp only [beatmap.mod_target_practice.renumber_combo_loop.body, slice_lt_len_iff, hk, if_true,
            vec_index_mut_eq _ _ hkh, bind_ok, uncurry_apply_pair, beatmap.mod_target_practice.set_combo_refines, lift,
            hk1, hk2]
        dsimp only
        rw [hb]
        simp only [bind_ok]
        unfold beatmap.mod_target_practice.renumber_combo_loop at hr
        exact hr
      · rw [hra, hsk, gen_abs_set]
        simp only [gen_applyIdx, i32S_wadd1, gen_abs_get (β := OsuHitObject) hos k.val hkh]
        rfl
      · rw [hrlast, hsk]
        cases h : (gen_idxs mapped.val key k2.val).getLast? with
        | none => simp [List.getLast?_eq_none_iff.mp h]
        | some l => simp [List.getLast?_cons, h]
    · refine ⟨(hos, last), ?_, rfl, ?_, ?_⟩
      · simp [beatmap.mod_target_practice.renumber_combo_loop.body, slice_lt_len_iff, hk]
      · rw [gen_idxs_ge _ _ _ (by omega)]; rfl
      · rw [gen_idxs_ge _ _ _ (by omega)]; rfl

theorem gen_getLast! {α} [Inhabited α] (a : α) (l : List α) (d : α) :
    (a :: l).getLast! = ((a :: l).getLast?).getD d := by
  simp [List.getLast!, List.getLast?_eq_getLast]

/-- spec: one `GroupBy` group of `fixComboInfo` -/
def gen_grpS (out : Array OsuHitObject) (idxs : List Nat) (g : Int32) : Array OsuHitObject :=
  let out := gen_applyIdx out idxs g 0
  let out := out.set! idxs.head! { out[idxs.head!]! with newCombo := true }
  out.set! idxs.getLast! { out[idxs.getLast!]! with lastInCombo := true }

theorem gen_applyIdx_size (out : Array OsuHitObject) : ∀ (idxs : List Nat) (g j : Int32),
    (gen_applyIdx out idxs g j).size = out.size := by
  intro idxs
  induction idxs generalizing out with
  | nil => intro g j; rfl
  | cons k rest ih => intro g j; simp only [gen_applyIdx]; rw [ih]; simp

theorem beatmap.mod_target_practice.renumber_combo_refines (hos : alloc.vec.Vec beatmap.objects.OsuHitObject)
    (mapped : Slice I32) (key g : I32) (hl : hos.val.length = mapped.val.length) (hex : key ∈ mapped.val) :
    ∃ r, beatmap.mod_target_practice.renumber_combo hos mapped key g = ok r ∧ r.val.length = hos.val.length ∧
      (abs r : Array OsuHitObject) = gen_grpS (abs hos) (gen_idxs mapped.val key 0) (i32S g) := by
  obtain ⟨f, hf, hfv⟩ := beatmap.mod_target_practice.next_match_refines mapped key 0#usize
  obtain ⟨j0, hj0⟩ : ∃ j, (mapped.val.drop 0).findIdx? (fun x => decide (x = key)) = some j := by
    simp only [List.drop_zero]
    cases h : List.findIdx? (fun x => decide (x = key)) mapped.val with
    | none => simp [List.findIdx?_eq_none_iff] at h; exact absurd (h key hex) (by simp)
    | some j => exact ⟨j, rfl⟩
  simp only [show ((0#usize : Usize).val) = 0 from rfl] at hfv
  rw [hj0] at hfv
  simp only [Nat.zero_add] at hfv
  obtain ⟨hjl, hjv, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hj0
  simp only [List.drop_zero, List.length_drop, Nat.sub_zero] at hjl hjv
  have hfl : f.val < mapped.val.length := by omega
  have hfm : ∀ hk : f.val < mapped.val.length, mapped.val[f.val] = key := by
    intro hk; simp only [hfv]; simpa using hjv
  have hidx : gen_idxs mapped.val key 0 = gen_idxs mapped.val key f.val := by
    rw [gen_idxs_skip mapped.val key 0]
    simp only [List.drop_zero] at hj0 ⊢
    rw [hj0, hfv]; simp
  obtain ⟨r, hr, hrl, hra, hrlast⟩ := gen_rn_loop mapped key g hos 0#i32 0#usize f hl hfm
  have hsk := gen_idxs_match mapped.val key f.val hfl (hfm hfl)
  have hlast : r.2.val < mapped.val.length := by
    rw [hrlast, hsk]
    have hmem : ∀ x ∈ (f.val :: gen_idxs mapped.val key (f.val + 1)), x < mapped.val.length := by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with hx | hx
      · omega
      · simp only [gen_idxs, List.mem_filter, List.mem_range'] at hx; omega
    cases h : (f.val :: gen_idxs mapped.val key (f.val + 1)).getLast? with
    | none => simp at h
    | some l => simp only [Option.getD_some]; exact hmem l (List.mem_of_getLast? h)
  have hfr : f.val < r.1.val.length := by omega
  have hlr : r.2.val < r.1.val.length := by omega
  have hlast2 : (gen_idxs mapped.val key f.val).getLast! = r.2.val := by
    rw [hrlast, hsk, gen_getLast! _ _ (0#usize : Usize).val]
  have hlr2 : r.2.val < (r.1.set f { (r.1.val[f.val]'hfr) with new_combo := true }).val.length := by
    simp [vec_set_val']; omega
  refine ⟨alloc.vec.Vec.set (r.1.set f { (r.1.val[f.val]'hfr) with new_combo := true }) r.2
    { ((r.1.set f { (r.1.val[f.val]'hfr) with new_combo := true }).val[r.2.val]'hlr2) with last_in_combo := true },
    ?_, ?_, ?_⟩
  · unfold beatmap.mod_target_practice.renumber_combo
    simp only [hf, bind_ok]
    rw [hr]
    simp only [bind_ok, gen_uncurry_eq, slice_lt_len_iff, hfl, if_true, vec_index_mut_eq _ _ hfr, uncurry_apply_pair]
    rw [vec_index_mut_eq _ _ hlr2]
    simp only [bind_ok, uncurry_apply_pair]
  · simp [vec_set_val', hrl]
  · rw [hidx]
    unfold gen_grpS
    have e0 : (i32S 0#i32) = 0 := rfl
    rw [e0] at hra
    rw [← hra, hlast2, hsk, List.head!_cons, gen_abs_set, gen_abs_set]
    simp only []
    rw [gen_abs_get (β := OsuHitObject) r.1 f.val hfr]
    have hW : ((abs r.1 : Array OsuHitObject).set! f.val
          ({ (abs (r.1.val[f.val]'hfr) : OsuHitObject) with newCombo := true }))[r.2.val]! =
        abs ((r.1.set f { (r.1.val[f.val]'hfr) with new_combo := true }).val[r.2.val]'hlr2) := by
      rw [← gen_abs_get (β := OsuHitObject) _ r.2.val hlr2, gen_abs_set]; rfl
    rw [hW]; rfl
end OsuProofs

open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl

def gen_fciA (orig : Array OsuHitObject) (h : OsuHitObject) : OsuHitObject :=
  { h with comboIndex := ((orig.reverse.find? fun y => Mods.TargetPractice.almostBigger h.startTime y.startTime).map
      (·.comboIndex)).getD 0 }

def gen_keysF (ks : Array Int32) (h : OsuHitObject) : Array Int32 :=
  if !ks.contains h.comboIndex then ks.push h.comboIndex else ks

def gen_grpF (hosA : Array OsuHitObject) (s : Array OsuHitObject × Int32) (key : Int32) : Array OsuHitObject × Int32 :=
  (gen_grpS s.1 ((List.range hosA.size).filter fun j => hosA[j]!.comboIndex == key) s.2, s.2 + 1)

theorem gen_applyIdx_foldl (idxs : List Nat) : ∀ (out : Array OsuHitObject) (g j : Int32),
    (idxs.foldl (fun (s : Array OsuHitObject × Int32) k =>
      (s.1.set! k { s.1[k]! with comboIndex := g, indexInCurrentCombo := s.2 }, s.2 + 1)) (out, j)).1 =
      gen_applyIdx out idxs g j := by
  induction idxs with
  | nil => intro out g j; rfl
  | cons k rest ih => intro out g j; simp only [List.foldl_cons, gen_applyIdx]; exact ih _ _ _

theorem gen_fci_spec (hos orig : Array OsuHitObject) :
    Mods.TargetPractice.fixComboInfo hos orig =
      (((hos.map (gen_fciA orig)).foldl gen_keysF #[]).foldl (gen_grpF (hos.map (gen_fciA orig))) (hos.map (gen_fciA orig), 0)).1 := by
  unfold Mods.TargetPractice.fixComboInfo
  simp only [Id.run]
  rw [← Array.forIn_toList, forIn_yield_foldl _ gen_keysF (by intro x s; unfold gen_keysF; split <;> rfl)]
  generalize hK : List.foldl gen_keysF #[] _ = K
  dsimp only [Bind.bind]
  rw [← Array.forIn_toList]
  rw [forIn_yield_foldl _ (gen_grpF _) ?hG]
  case hG =>
    intro key s
    rw [forIn_yield_foldl _ (fun (t : Array OsuHitObject × Int32) k =>
      (t.1.set! k { t.1[k]! with comboIndex := s.2, indexInCurrentCombo := t.2 }, t.2 + 1)) ?hI]
    case hI => intro k s'; rfl
    rw [gen_applyIdx_foldl]
    rfl
  rw [Array.foldl_toList] at hK
  rw [← hK, Array.foldl_toList]
  rfl
end OsuProofs

open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl

/-- last index `< j` whose element satisfies `p` -/
def gen_lastIdx {α} (l : List α) (p : α → Bool) : Nat → Option Nat
  | 0 => none
  | j + 1 => if (l[j]?.map p).getD false then some j else gen_lastIdx l p j

theorem gen_lastIdx_find {α} (l : List α) (p : α → Bool) :
    ∀ j, j ≤ l.length → ((l.take j).reverse.find? p) = (gen_lastIdx l p j).bind (l[·]?) := by
  intro j
  induction j with
  | zero => intro _; simp [gen_lastIdx]
  | succ j ih =>
    intro hj
    rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.find?_cons, gen_lastIdx, List.getElem?_eq_getElem (show j < l.length by omega), Option.map_some,
      Option.getD_some]
    split
    · next h => simp [h, List.getElem?_eq_getElem (show j < l.length by omega)]
    · next h => simp only [h, Bool.false_eq_true, if_false]; exact ih (by omega)

theorem gen_fc_inner (hos : alloc.vec.Vec beatmap.objects.OsuHitObject) (orig : Slice beatmap.objects.OsuHitObject)
    (i : Usize) (hi : i.val < hos.val.length) :
    ∀ j : Usize, j.val ≤ orig.val.length →
      ∃ r, beatmap.mod_target_practice.fix_combo_info_loop0_loop0 hos orig i none j = ok r ∧
        r.map (·.val) = gen_lastIdx orig.val
          (fun o => Mods.TargetPractice.almostBigger (hos.val[i.val]'hi).start_time o.start_time) j.val := by
  intro j
  induction hj : j.val generalizing j with
  | zero =>
    intro _
    refine ⟨none, ?_, rfl⟩
    unfold beatmap.mod_target_practice.fix_combo_info_loop0_loop0
    rw [loop_unfold]
    have : ¬ j > 0#usize := by scalar_tac
    simp [beatmap.mod_target_practice.fix_combo_info_loop0_loop0.body, this]
  | succ n ih =>
    intro hjl
    have hpos : j > 0#usize := by scalar_tac
    obtain ⟨j1, hj1, hj1v⟩ : ∃ j1 : Usize, j - 1#usize = ok j1 ∧ j1.val = n := by
      obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (Usize.sub_spec (x := j) (y := 1#usize) (by scalar_tac))
      exact ⟨z, hz, by have := hzv; scalar_tac⟩
    have hn : n < orig.val.length := by omega
    unfold beatmap.mod_target_practice.fix_combo_info_loop0_loop0
    rw [loop_unfold]
    simp only [gen_lastIdx, List.getElem?_eq_getElem hn, Option.map_some, Option.getD_some]
    by_cases hp : Mods.TargetPractice.almostBigger (hos.val[i.val]'hi).start_time (orig.val[n]'hn).start_time
    · refine ⟨some j1, ?_, by simp [hp, hj1v]⟩
      have hb1 : beatmap.mod_target_practice.fix_combo_info_loop0_loop0.body hos orig i none j =
          ok (.cont (some j1, j1)) := by
        simp only [beatmap.mod_target_practice.fix_combo_info_loop0_loop0.body, core.option.Option.is_none,
          Option.isNone_none, if_true, hpos, hj1, bind_ok, vec_index_eq _ _ hi, slice_index_ok _ _ (show j1.val < orig.val.length by omega),
          tp_ab]
        simp only [hj1v, hp, if_true]
      simp only [hb1, bind_ok]
      rw [loop_unfold]
      simp [beatmap.mod_target_practice.fix_combo_info_loop0_loop0.body]
    · obtain ⟨r, hr, hrv⟩ := ih j1 hj1v (by omega)
      refine ⟨r, ?_, by simp [hp, hrv]⟩
      have hb1 : beatmap.mod_target_practice.fix_combo_info_loop0_loop0.body hos orig i none j =
          ok (.cont (none, j1)) := by
        simp only [beatmap.mod_target_practice.fix_combo_info_loop0_loop0.body, core.option.Option.is_none,
          Option.isNone_none, if_true, hpos, hj1, bind_ok, vec_index_eq _ _ hi, slice_index_ok _ _ (show j1.val < orig.val.length by omega),
          tp_ab]
        simp only [hj1v, hp, Bool.false_eq_true, if_false]
      simp only [hb1, bind_ok]
      unfold beatmap.mod_target_practice.fix_combo_info_loop0_loop0 at hr
      exact hr

theorem gen_lastIdx_map {α β} (l : List α) (f : α → β) (p : β → Bool) :
    ∀ j, gen_lastIdx (l.map f) p j = gen_lastIdx l (fun x => p (f x)) j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih => simp only [gen_lastIdx, List.getElem?_map, Option.map_map]; rw [ih]; rfl

theorem gen_lastIdx_lt {α} (l : List α) (p : α → Bool) : ∀ j c, gen_lastIdx l p j = some c → c < j := by
  intro j
  induction j with
  | zero => intro c h; simp [gen_lastIdx] at h
  | succ j ih =>
    intro c h
    simp only [gen_lastIdx] at h
    split at h
    · cases h; omega
    · have := ih c h; omega

theorem gen_fciA_eq (origR : Slice beatmap.objects.OsuHitObject) (h : beatmap.objects.OsuHitObject) :
    gen_fciA (abs origR) (abs h) = { (abs h : OsuHitObject) with comboIndex :=
      ((gen_lastIdx origR.val (fun o => Mods.TargetPractice.almostBigger h.start_time o.start_time)
        origR.val.length).bind (fun c => (origR.val.map (abs : _ → OsuHitObject))[c]?) |>.map (·.comboIndex)).getD 0 } := by
  unfold gen_fciA
  congr 2
  have e : (abs origR : Array OsuHitObject).reverse.find? (fun y => Mods.TargetPractice.almostBigger (abs h : OsuHitObject).startTime y.startTime) =
      ((origR.val.map (abs : _ → OsuHitObject)).take (origR.val.map (abs : _ → OsuHitObject)).length).reverse.find?
        (fun y => Mods.TargetPractice.almostBigger (abs h : OsuHitObject).startTime y.startTime) := by
    rw [List.take_length, ← Array.find?_toList, Array.toList_reverse]; rfl
  rw [e, gen_lastIdx_find _ _ _ (le_refl _), gen_lastIdx_map, List.length_map]
  rfl

theorem gen_fc_loop0 (hos : alloc.vec.Vec beatmap.objects.OsuHitObject) (orig : Slice beatmap.objects.OsuHitObject) :
    ∃ v, beatmap.mod_target_practice.fix_combo_info_loop0 hos orig 0#usize = ok v ∧
      v.val.map (abs : _ → OsuHitObject) = (hos.val.map abs).map (gen_fciA (abs orig)) := by
  obtain ⟨y, hl, hv⟩ := loop_fold_gen' (fun x => beatmap.mod_target_practice.fix_combo_info_loop0.body orig x.1 x.2) (·.2)
    hos.val.length (by have := hos.property; omega)
    (fun x => x.1.val.length = hos.val.length)
    (fun x => x.1.val.map (abs : _ → OsuHitObject))
    (fun k L => L.modify k (gen_fciA (abs orig)))
    (fun y L => y.val.map (abs : _ → OsuHitObject) = L)
    (by
      rintro ⟨q, k⟩ hI hlt j1 hj1 hj1v
      simp only at hI hlt hj1 hj1v ⊢
      have hl : k.val < q.val.length := by omega
      obtain ⟨c, hc, hcv⟩ := gen_fc_inner q orig k hl (Slice.len orig) (by simp)
      have hlen : (Slice.len orig).val = orig.val.length := by simp
      rw [hlen] at hcv
      have hci : ∃ ci : I32, (match c with
          | none => ok 0#i32
          | some c => do
                      let oho ← Slice.index_usize orig c
                      ok oho.combo_index) = ok ci ∧
          (gen_fciA (abs orig) (abs (q.val[k.val]'hl)) : OsuHitObject) =
            { (abs (q.val[k.val]'hl) : OsuHitObject) with comboIndex := i32S ci } := by
        rw [gen_fciA_eq]
        cases c with
        | none =>
          refine ⟨0#i32, rfl, ?_⟩
          simp only [Option.map_none] at hcv
          simp [← hcv]; rfl
        | some c =>
          have hcl : c.val < orig.val.length := by
            have := gen_lastIdx_lt _ _ _ _ hcv.symm; simpa using this
          refine ⟨(orig.val[c.val]'hcl).combo_index, by simp [slice_index_ok _ _ hcl], ?_⟩
          simp only [Option.map_some] at hcv
          simp only [← hcv, Option.bind_some, List.getElem?_map, List.getElem?_eq_getElem hcl, Option.map_some,
            Option.getD_some]
          rfl
      obtain ⟨ci, hci1, hci2⟩ := hci
      refine ⟨(alloc.vec.Vec.set q k { (q.val[k.val]'hl) with combo_index := ci }, j1), ?_, rfl, ?_, ?_⟩
      · simp only [beatmap.mod_target_practice.fix_combo_info_loop0.body, vec_lt_len_iff, hl, if_true, bind_ok,
          show Slice.len orig = Slice.len orig from rfl]
        rw [hc]
        simp only [bind_ok]
        cases c with
        | none =>
          have := Result.ok_injective hci1; subst this
          simp only [bind_ok, vec_index_mut_eq _ _ hl, uncurry_apply_pair, hj1]
        | some c =>
          simp only [] at hci1 ⊢
          rw [hci1]
          simp only [bind_ok, vec_index_mut_eq _ _ hl, uncurry_apply_pair, hj1]
      · rw [list_modify_set _ _ (by simpa using hl), vec_set_val', List.map_set, List.getElem_map, hci2]; rfl
      · simp [vec_set_val', hI])
    (by
      rintro ⟨q, k⟩ hI hge
      simp only at hI hge ⊢
      have : ¬ k < alloc.vec.Vec.len q := by rw [vec_lt_len_iff]; omega
      exact ⟨q, by simp [beatmap.mod_target_practice.fix_combo_info_loop0.body, this], rfl⟩)
    (hos, 0#usize) rfl (by simp)
  refine ⟨y, by unfold beatmap.mod_target_practice.fix_combo_info_loop0; exact hl, ?_⟩
  rw [hv]
  have := iterR_modify_map (gen_fciA (abs orig)) (hos.val.map (abs : _ → OsuHitObject))
  simpa using this
end OsuProofs

open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl

theorem gen_seen_loop (keys : alloc.vec.Vec I32) (ci : I32) :
    ∀ (seen : Bool) (k : Usize), ∃ r, beatmap.mod_target_practice.fix_combo_info_loop1_loop0 keys ci seen k = ok r ∧
      r = (seen || (keys.val.drop k.val).any (fun x => decide (x = ci))) := by
  intro seen k
  induction hn : keys.val.length - k.val using Nat.strong_induction_on generalizing seen k with
  | _ n ih =>
    unfold beatmap.mod_target_practice.fix_combo_info_loop1_loop0
    rw [loop_unfold]
    by_cases hk : k.val < keys.val.length
    · obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := keys.property; omega)
      have hs : ∃ s1, (if (keys.val[k.val]'hk) = ci then ok true else ok seen) = ok s1 ∧
          s1 = (seen || decide ((keys.val[k.val]'hk) = ci)) := by
        by_cases h : (keys.val[k.val]'hk) = ci <;> simp [h]
      obtain ⟨s1, hs1, hs1v⟩ := hs
      obtain ⟨r, hr, hrv⟩ := ih (keys.val.length - k1.val) (by omega) s1 k1 rfl
      refine ⟨r, ?_, ?_⟩
      · have hb : beatmap.mod_target_practice.fix_combo_info_loop1_loop0.body keys ci seen k = ok (.cont (s1, k1)) := by
          simp only [beatmap.mod_target_practice.fix_combo_info_loop1_loop0.body, vec_lt_len_iff, hk, if_true,
            vec_index_eq _ _ hk, bind_ok, hs1, hk1]
        dsimp only
        rw [hb]; simp only [bind_ok]
        unfold beatmap.mod_target_practice.fix_combo_info_loop1_loop0 at hr
        exact hr
      · rw [hrv, hs1v, hk1v, List.drop_eq_getElem_cons hk]
        simp only [List.any_cons, Bool.or_assoc]
    · refine ⟨seen, ?_, by rw [List.drop_eq_nil_of_le (by omega)]; simp⟩
      have : ¬ k < alloc.vec.Vec.len keys := by rw [vec_lt_len_iff]; exact hk
      simp [beatmap.mod_target_practice.fix_combo_info_loop1_loop0.body, this]

theorem gen_contains_i32 (keys : List I32) (ci : I32) :
    (keys.map i32S).toArray.contains (i32S ci) = keys.any (fun x => decide (x = ci)) := by
  induction keys with
  | nil => simp
  | cons x t ih =>
    simp only [List.map_cons, List.any_cons] at ih ⊢
    rw [← ih]
    simp [abs_i32S_inj, eq_comm]

theorem gen_fc_keys (hos : alloc.vec.Vec beatmap.objects.OsuHitObject) :
    ∃ keys, beatmap.mod_target_practice.fix_combo_info_loop1 hos 0#usize (alloc.vec.Vec.new I32) = ok keys ∧
      (keys.val.map i32S).toArray = ((abs hos : Array OsuHitObject).toList).foldl gen_keysF #[] ∧
      (∀ x ∈ keys.val, x ∈ hos.val.map (·.combo_index)) := by
  obtain ⟨y, hl, hv⟩ := loop_fold_gen'
    (fun x : Usize × alloc.vec.Vec I32 => beatmap.mod_target_practice.fix_combo_info_loop1.body hos x.1 x.2) (·.1)
    hos.val.length (by have := hos.property; omega)
    (fun x => x.2.val.length ≤ x.1.val ∧ ∀ z ∈ x.2.val, z ∈ hos.val.map (·.combo_index))
    (fun x => (x.2.val.map i32S).toArray)
    (fun k ks => gen_keysF ks ((abs hos : Array OsuHitObject).toList[k]!))
    (fun y ks => (y.val.map i32S).toArray = ks ∧ ∀ z ∈ y.val, z ∈ hos.val.map (·.combo_index))
    (by
      rintro ⟨i, keys⟩ ⟨hI1, hI2⟩ hlt j1 hj1 hj1v
      simp only at hI1 hI2 hlt hj1 hj1v ⊢
      have hi : i.val < hos.val.length := hlt
      obtain ⟨sn, hsn, hsnv⟩ := gen_seen_loop keys (hos.val[i.val]'hi).combo_index false 0#usize
      simp only [Bool.false_or, List.drop_zero, show ((0#usize : Usize).val) = 0 from rfl] at hsnv
      have hga : (abs hos : Array OsuHitObject).toList[i.val]! = abs (hos.val[i.val]'hi) := by
        rw [Array.getElem!_toList]; exact gen_abs_get hos i.val hi
      have hmem : (hos.val[i.val]'hi).combo_index ∈ hos.val.map (·.combo_index) :=
        List.mem_map.mpr ⟨_, List.getElem_mem hi, rfl⟩
      by_cases hs : sn = true
      · refine ⟨(j1, keys), ?_, rfl, ?_, ⟨by simp only; omega, hI2⟩⟩
        · simp only [beatmap.mod_target_practice.fix_combo_info_loop1.body, vec_lt_len_iff, hi, if_true,
            vec_index_eq _ _ hi, bind_ok, hsn, hs, hj1]
        · simp only [hga, gen_keysF]
          have : (keys.val.map i32S).toArray.contains (abs (hos.val[i.val]'hi) : OsuHitObject).comboIndex = true := by
            show (keys.val.map i32S).toArray.contains (i32S (hos.val[i.val]'hi).combo_index) = true
            rw [gen_contains_i32, ← hsnv, hs]
          simp only [this, Bool.not_true, Bool.false_eq_true, if_false]
      · have hpush : keys.val.length < Usize.max := by have := hos.property; omega
        refine ⟨(j1, vpush keys (hos.val[i.val]'hi).combo_index hpush), ?_, rfl, ?_, ⟨by simp; omega, ?_⟩⟩
        · simp only [beatmap.mod_target_practice.fix_combo_info_loop1.body, vec_lt_len_iff, hi, if_true,
            vec_index_eq _ _ hi, bind_ok, hsn, hs, Bool.false_eq_true, if_false, vec_push_ok _ _ hpush, hj1]
        · simp only [hga, gen_keysF]
          have : (keys.val.map i32S).toArray.contains (abs (hos.val[i.val]'hi) : OsuHitObject).comboIndex = false := by
            show (keys.val.map i32S).toArray.contains (i32S (hos.val[i.val]'hi).combo_index) = false
            rw [gen_contains_i32, ← hsnv]; simpa using hs
          simp only [this, Bool.not_false, if_true]
          simp [vpush_val]; rfl
        · intro z hz
          simp only [vpush_val, List.mem_append, List.mem_singleton] at hz
          rcases hz with hz | hz
          · exact hI2 z hz
          · subst hz; exact hmem)
    (by
      rintro ⟨i, keys⟩ ⟨hI1, hI2⟩ hge
      simp only at hI1 hI2 hge ⊢
      have : ¬ i < alloc.vec.Vec.len hos := by rw [vec_lt_len_iff]; omega
      exact ⟨keys, by simp [beatmap.mod_target_practice.fix_combo_info_loop1.body, this], rfl, hI2⟩)
    (0#usize, alloc.vec.Vec.new I32) ⟨by simp [alloc.vec.Vec.new], by simp [alloc.vec.Vec.new]⟩ (by simp)
  refine ⟨y, by unfold beatmap.mod_target_practice.fix_combo_info_loop1; exact hl, ?_, hv.2⟩
  rw [hv.1, foldl_iterR]
  simp [abs, alloc.vec.Vec.new]
end OsuProofs

open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl

theorem gen_fc_mapped (hos : alloc.vec.Vec beatmap.objects.OsuHitObject) :
    ∃ m, beatmap.mod_target_practice.fix_combo_info_loop2 hos
        (alloc.vec.Vec.with_capacity I32 (alloc.vec.Vec.len hos)) 0#usize = ok m ∧
      m.val = hos.val.map (·.combo_index) := by
  obtain ⟨r, hr, hrv⟩ := loop_push_map (fun x => beatmap.mod_target_practice.fix_combo_info_loop2.body hos x.1 x.2)
    hos.val.length (fun i => ((hos.val.map (·.combo_index))[i]?).getD 0#i32)
    (by
      intro ts i hlt hmax
      have hl : i.val < hos.val.length := hlt
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := hos.property; omega)
      have hpush : ts.val.length < Usize.max := by omega
      refine ⟨vpush ts (hos.val[i.val]'hl).combo_index hpush, i1, ?_, by simp [List.getElem?_eq_getElem hl], hi1v⟩
      simp only [beatmap.mod_target_practice.fix_combo_info_loop2.body, vec_lt_len_iff, hl, if_true,
        vec_index_eq _ _ hl, bind_ok, vec_push_ok _ _ hpush, hi1])
    (by
      intro ts i hle
      have : ¬ i < alloc.vec.Vec.len hos := by rw [vec_lt_len_iff]; omega
      simp [beatmap.mod_target_practice.fix_combo_info_loop2.body, this])
    (alloc.vec.Vec.with_capacity I32 (alloc.vec.Vec.len hos)) 0#usize (by simp)
    (by have := hos.property; simp [alloc.vec.Vec.with_capacity]; try omega)
  refine ⟨r, by unfold beatmap.mod_target_practice.fix_combo_info_loop2; exact hr, ?_⟩
  rw [hrv]; simp [alloc.vec.Vec.with_capacity]
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp [List.getElem?_eq_getElem (show n < hos.val.length by simpa using h2)]

theorem gen_idxs_eq (mapped : List I32) (hosA : Array OsuHitObject) (hm : mapped.map i32S = hosA.toList.map (·.comboIndex))
    (key : I32) :
    gen_idxs mapped key 0 = (List.range hosA.size).filter (fun j => hosA[j]!.comboIndex == i32S key) := by
  have hlen : mapped.length = hosA.size := by
    have := congrArg List.length hm; simpa using this
  unfold gen_idxs
  rw [Nat.sub_zero, ← List.range_eq_range', hlen]
  apply List.filter_congr
  intro j hj
  have hj' : j < hosA.size := List.mem_range.mp hj
  have e : hosA[j]!.comboIndex = i32S (mapped[j]'(by omega)) := by
    have := List.getElem_of_eq hm (show j < (mapped.map i32S).length by simp; omega)
    simp only [List.getElem_map, Array.getElem_toList] at this
    rw [getElem!_pos hosA j hj']; exact this.symm
  rw [e, getElem!_pos mapped j (by omega)]
  rw [Bool.eq_iff_iff]
  simp [abs_i32S_inj]

theorem gen_fc_loop3 (keys mapped : alloc.vec.Vec I32) (hosA : Array OsuHitObject)
    (hm : mapped.val.map i32S = hosA.toList.map (·.comboIndex)) (hk : ∀ x ∈ keys.val, x ∈ mapped.val) :
    ∀ (hos : alloc.vec.Vec beatmap.objects.OsuHitObject), hos.val.length = mapped.val.length →
    ∃ r, beatmap.mod_target_practice.fix_combo_info_loop3 hos keys mapped 0#i32 0#usize = ok r ∧
      (abs r : Array OsuHitObject) = ((keys.val.map i32S).toArray.foldl (gen_grpF hosA) ((abs hos : Array OsuHitObject), 0)).1 ∧
      r.val.length = hos.val.length := by
  intro hos hl
  obtain ⟨y, hlp, hv⟩ := loop_fold_gen'
    (fun x : alloc.vec.Vec beatmap.objects.OsuHitObject × I32 × Usize =>
      beatmap.mod_target_practice.fix_combo_info_loop3.body keys mapped x.1 x.2.1 x.2.2) (·.2.2)
    keys.val.length (by have := keys.property; omega)
    (fun x => x.1.val.length = mapped.val.length)
    (fun x => ((abs x.1 : Array OsuHitObject), i32S x.2.1))
    (fun k s => gen_grpF hosA s ((keys.val.map i32S).toArray.toList[k]!))
    (fun y s => (abs y : Array OsuHitObject) = s.1 ∧ y.val.length = mapped.val.length)
    (by
      rintro ⟨h, g, ki⟩ hI hlt j1 hj1 hj1v
      simp only at hI hlt hj1 hj1v ⊢
      have hki : ki.val < keys.val.length := hlt
      obtain ⟨r, hr, hrl, hrv⟩ := beatmap.mod_target_practice.renumber_combo_refines h (alloc.vec.Vec.deref mapped)
        (keys.val[ki.val]'hki) g (by rw [gen_deref_val]; exact hI) (by rw [gen_deref_val]; exact hk _ (List.getElem_mem hki))
      refine ⟨(r, core.num.I32.wrapping_add g 1#i32, j1), ?_, rfl, ?_, by simp only; rw [hrl, hI]⟩
      · simp only [beatmap.mod_target_practice.fix_combo_info_loop3.body, vec_lt_len_iff, hki, if_true,
          vec_index_eq _ _ hki, bind_ok, hr, lift, hj1]
      · simp only [i32S_wadd1]
        rw [hrv]
        unfold gen_grpF
        rw [gen_deref_val, gen_idxs_eq mapped.val hosA hm]
        simp [List.getElem?_eq_getElem hki])
    (by
      rintro ⟨h, g, ki⟩ hI hge
      simp only at hI hge ⊢
      have : ¬ ki < alloc.vec.Vec.len keys := by rw [vec_lt_len_iff]; omega
      exact ⟨h, by simp [beatmap.mod_target_practice.fix_combo_info_loop3.body, this], rfl, hI⟩)
    (hos, 0#i32, 0#usize) hl (by simp)
  refine ⟨y, by unfold beatmap.mod_target_practice.fix_combo_info_loop3; exact hlp, ?_, by rw [hv.2, hl]⟩
  rw [hv.1, ← Array.foldl_toList, foldl_iterR]
  simp
  rfl

theorem beatmap.mod_target_practice.fix_combo_info_refines (hos : alloc.vec.Vec beatmap.objects.OsuHitObject)
    (orig : Slice beatmap.objects.OsuHitObject) :
    ∃ r, beatmap.mod_target_practice.fix_combo_info hos orig = ok r ∧ r.val.length = hos.val.length ∧
      (abs r : Array OsuHitObject) = Mods.TargetPractice.fixComboInfo (abs hos) (abs orig) := by
  obtain ⟨v, hv, hvv⟩ := gen_fc_loop0 hos orig
  have hvl : v.val.length = hos.val.length := by have := congrArg List.length hvv; simpa using this
  have hA : (abs v : Array OsuHitObject) = (abs hos : Array OsuHitObject).map (gen_fciA (abs orig)) := by
    show (v.val.map abs).toArray = _
    rw [hvv]; simp [abs]
  obtain ⟨keys, hk, hkv, hkm⟩ := gen_fc_keys v
  obtain ⟨m, hm, hmv⟩ := gen_fc_mapped v
  have hmA : m.val.map i32S = (abs v : Array OsuHitObject).toList.map (·.comboIndex) := by
    rw [hmv]; simp [abs, List.map_map]
  obtain ⟨r, hr, hrv, hrl⟩ := gen_fc_loop3 keys m (abs v) hmA (by rw [hmv]; exact hkm) v (by rw [hmv]; simp)
  refine ⟨r, ?_, by rw [hrl, hvl], ?_⟩
  · unfold beatmap.mod_target_practice.fix_combo_info
    simp only [hv, bind_ok, hk, hm, hr]
  · rw [hrv, gen_fci_spec, ← hA, hkv, Array.foldl_toList]
end OsuProofs

