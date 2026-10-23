/-
`beatmap::mod_settings`, part 6: the helpers of `Settings.assign` / `Settings.toMod`
(`setValue`, `typeOf`, `dbl`, `le`, the change test, the callback selection, the MU type
adjustment, the last-occurrence key lookup, string copy).

`Settings.assign` is a `partial def` (opaque), so the helpers that only exist as its local `let`s
are stated against copies of those `let`s (`changedS`, `assignRuleS`, `toModTypeS`, …), named here.
-/
import OsuProofs.Beatmap.ModSettings5
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap OsuModel.Net.Framework

namespace OsuProofs
open OsuImpl

/-! ## `setValue` -/

/-- Rust-side `set_value` as a list function -/
def setValR (l : List (U32 × beatmap.mod_settings.SettingValue)) (key : U32) (v : beatmap.mod_settings.SettingValue) :
    List (U32 × beatmap.mod_settings.SettingValue) :=
  l.map fun p => if p.1 = key then (p.1, v) else p

theorem set_value_loop_ok (key : U32) (v : beatmap.mod_settings.SettingValue) :
    ∀ (vals : alloc.vec.Vec (U32 × beatmap.mod_settings.SettingValue)) (i : Usize), i.val ≤ vals.val.length →
      ∃ r, beatmap.mod_settings.set_value_loop vals key v i = ok r ∧
        r.val = vals.val.take i.val ++ setValR (vals.val.drop i.val) key v := by
  intro vals i hi
  unfold beatmap.mod_settings.set_value_loop
  refine loop_ok _ (fun (x : alloc.vec.Vec (U32 × beatmap.mod_settings.SettingValue) × Usize) => x.1.val.length - x.2.val)
    (fun x => x.2.val ≤ x.1.val.length ∧ x.1.val.length = vals.val.length ∧
      x.1.val.take x.2.val ++ setValR (x.1.val.drop x.2.val) key v =
        vals.val.take i.val ++ setValR (vals.val.drop i.val) key v)
    (fun (r : alloc.vec.Vec (U32 × beatmap.mod_settings.SettingValue)) => r.val = vals.val.take i.val ++ setValR (vals.val.drop i.val) key v) ?_ (vals, i) ⟨hi, rfl, rfl⟩
  rintro ⟨w, j⟩ ⟨hj, hlen, heq⟩
  dsimp only at hj hlen heq ⊢
  by_cases hlt : j.val < w.val.length
  · right
    have hlt' : j < alloc.vec.Vec.len w := by show j.val < (alloc.vec.Vec.len w).val; simpa using hlt
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := w.property; omega)
    have e2 : w.val.drop j.val = (w.val[j.val]'hlt) :: w.val.drop (j.val + 1) := List.drop_eq_getElem_cons hlt
    have hidx := vec_index_eq' w j hlt
    generalize hp : w.val[j.val]'hlt = p at e2 hidx
    obtain ⟨pk, pv⟩ := p
    by_cases hk : pk = key
    · refine ⟨(alloc.vec.Vec.set w j (pk, v), j1), ?_, ?_, by simp; omega⟩
      · simp [beatmap.mod_settings.set_value_loop.body, hlt', hidx, hk, vec_index_mut_eq w j hlt, hj1]
        rw [hp]; simp [hk]
      · dsimp only
        rw [← heq, e2]
        have hs : (alloc.vec.Vec.set w j (pk, v)).val = w.val.take j.val ++ (pk, v) :: w.val.drop (j.val + 1) := by
          simp [List.set_eq_take_append_cons_drop, hlt]
        have hl : (w.val.take j.val).length = j.val := by simp; omega
        refine ⟨?_, ?_, ?_⟩
        · rw [hs, hj1v]; simp; omega
        · rw [hs, ← hlen]; simp; omega
        · rw [hs, hj1v]
          simp only [List.take_append, List.drop_append, hl]
          simp [setValR, hk]
    · refine ⟨(w, j1), ?_, ?_, by simp; omega⟩
      · simp [beatmap.mod_settings.set_value_loop.body, hlt', hidx, hk, hj1]
      · dsimp only
        rw [← heq, e2]
        refine ⟨by omega, hlen, ?_⟩
        rw [hj1v, take_succ_get w.val j.val hlt, hp]
        simp [setValR, hk, List.drop_eq_getElem_cons]
  · left
    have hlt' : ¬ j < alloc.vec.Vec.len w := by show ¬ j.val < (alloc.vec.Vec.len w).val; simpa using hlt
    refine ⟨w, by simp [beatmap.mod_settings.set_value_loop.body, hlt'], ?_⟩
    rw [← heq, List.drop_eq_nil_of_le (by omega), List.take_of_length_le (by omega)]; simp [setValR]

theorem keyName_beq (a b : U32) (ha : a.val < 44) : (keyName a.val == keyName b.val) = decide (a = b) := by
  by_cases hkey : b.val < 44
  · rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, decide_eq_true_eq, keyName_inj _ _ ha hkey]
    exact ⟨fun h => UScalar.eq_of_val_eq h, fun h => h ▸ rfl⟩
  · have h1 : keyName b.val = "" := by
      by_contra h; exact hkey ((keyName_ne_empty _).mp h)
    have h2 : keyName a.val ≠ "" := (keyName_ne_empty _).mpr ha
    have h3 : a ≠ b := by intro h; rw [h] at ha; exact hkey ha
    simp [h1, h2, h3]

theorem beatmap.mod_settings.set_value_refines (vals : alloc.vec.Vec (U32 × beatmap.mod_settings.SettingValue))
    (key : U32) (v : beatmap.mod_settings.SettingValue) :
    ∃ r, beatmap.mod_settings.set_value vals key v = ok r ∧ r.val = setValR vals.val key v := by
  obtain ⟨r, hr, hrv⟩ := set_value_loop_ok key v vals 0#usize (by simp)
  exact ⟨r, hr, by simpa using hrv⟩

theorem setValR_keys (l : List (U32 × beatmap.mod_settings.SettingValue)) (key : U32) (v) :
    (setValR l key v).map (·.1) = l.map (·.1) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [setValR, List.map_cons] at ih ⊢; rw [ih]; split <;> simp_all

theorem KeysOk_setValR (l : List (U32 × beatmap.mod_settings.SettingValue)) (h : KeysOk l) (key : U32) (v) :
    KeysOk (setValR l key v) := by
  intro p hp
  simp only [setValR, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  split <;> exact h q hq

theorem setValR_spec (l : List (U32 × beatmap.mod_settings.SettingValue)) (h : KeysOk l) (key : U32) (v) :
    (valsS (setValR l key v)).toArray =
      Settings.setValue (valsS l).toArray (keyName key.val) (svS v) := by
  simp only [Settings.setValue, List.map_toArray, valsS, setValR, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp, keyName_beq p.1 key (h p hp)]
  by_cases hk : p.1 = key <;> simp [hk]

/-! ## `typeOf`, `dbl`, `le` -/

/-- the `typeOf` of `Settings.assign` on the Rust defs -/
def typeOfR (defs : List beatmap.mod_settings.SettingDef) (k : U32) : Option beatmap.mod_settings.SettingType :=
  (defs.find? (fun d => decide (d.key = k))).map (·.stype)

theorem type_of_loop_ok (l : Slice beatmap.mod_settings.SettingDef) (key : U32) :
    ∀ (i : Usize), i.val ≤ l.val.length →
      beatmap.mod_settings.type_of_loop l key i none = ok (typeOfR (l.val.drop i.val) key) := by
  intro i hi
  unfold beatmap.mod_settings.type_of_loop
  have := loop_ok (fun (x : Usize × Option beatmap.mod_settings.SettingType) =>
      beatmap.mod_settings.type_of_loop.body l key x.1 x.2)
    (fun x => l.val.length + 1 - x.1.val - (if x.2.isSome then 1 else 0))
    (fun x => x.1.val ≤ l.val.length ∧
      (x.2 = none → typeOfR (l.val.drop x.1.val) key = typeOfR (l.val.drop i.val) key) ∧
      (x.2.isSome → x.2 = typeOfR (l.val.drop i.val) key))
    (fun r => r = typeOfR (l.val.drop i.val) key)
    (by
      rintro ⟨k, r⟩ ⟨hk, hn, hs⟩
      dsimp only at hk hn hs ⊢
      cases r with
      | some v =>
        left; exact ⟨some v, by simp [beatmap.mod_settings.type_of_loop.body, core.option.Option.is_none], hs rfl⟩
      | none =>
        by_cases hlt : k.val < l.val.length
        · right
          have hlt' : k < Slice.len l := by show k.val < (Slice.len l).val; simpa using hlt
          obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := l.property; omega)
          have hd : typeOfR (l.val.drop k.val) key = if (l.val[k.val]'hlt).key = key then some (l.val[k.val]'hlt).stype
              else typeOfR (l.val.drop (k.val + 1)) key := by
            rw [typeOfR, List.drop_eq_getElem_cons hlt, List.find?_cons]
            by_cases hkey : (l.val[k.val]'hlt).key = key <;> simp [hkey, typeOfR]
          have hn' := hn rfl
          by_cases hkey : (l.val[k.val]'hlt).key = key
          · refine ⟨(k1, some (l.val[k.val]'hlt).stype), ?_, ⟨by dsimp only; omega, by simp, ?_⟩, by simp; omega⟩
            · simp [beatmap.mod_settings.type_of_loop.body, core.option.Option.is_none, hlt', index_eq l k hlt, hk1, hkey]
            · intro _; rw [← hn', hd, if_pos hkey]
          · refine ⟨(k1, none), ?_, ⟨by dsimp only; omega, ?_, by simp⟩, by simp; omega⟩
            · simp [beatmap.mod_settings.type_of_loop.body, core.option.Option.is_none, hlt', index_eq l k hlt, hk1, hkey]
            · intro _; rw [← hn', hd, if_neg hkey, hk1v]
        · left
          have hlt' : ¬ k < Slice.len l := by show ¬ k.val < (Slice.len l).val; simpa using hlt
          refine ⟨none, by simp [beatmap.mod_settings.type_of_loop.body, core.option.Option.is_none, hlt'], ?_⟩
          rw [← hn rfl, show k.val = l.val.length by omega, List.drop_length]; rfl)
    (i, none) ⟨hi, fun _ => rfl, by simp⟩
  obtain ⟨y, hy, rfl⟩ := this
  exact hy

theorem beatmap.mod_settings.type_of_refines (defs : Slice beatmap.mod_settings.SettingDef) (k : U32) :
    beatmap.mod_settings.type_of defs k = ok (typeOfR defs.val k) := by
  unfold beatmap.mod_settings.type_of
  rw [type_of_loop_ok defs k 0#usize (by simp)]; rfl

/-- every key id of a def list is known -/
def DefsOk (l : List beatmap.mod_settings.SettingDef) : Prop := ∀ d ∈ l, d.key.val < 44

theorem typeOfR_spec (l : List beatmap.mod_settings.SettingDef) (h : DefsOk l) (k : U32) :
    ((l.map sdS).find? (·.key == keyName k.val)).map (·.type) = (typeOfR l k).map styS := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    have hd : d.key.val < 44 := h d (by simp)
    have hl : DefsOk l := fun q hq => h q (by simp [hq])
    simp only [typeOfR, List.map_cons, List.find?_cons] at ih ⊢
    rw [show (sdS d).key = keyName d.key.val from rfl, keyName_beq d.key k hd]
    by_cases hk : d.key = k
    · simp [hk, sdS]
    · simp only [hk, decide_false]; exact ih hl

/-- the `dbl` of `Settings.assign` -/
def dblR (l : List (U32 × beatmap.mod_settings.SettingValue)) (k : U32) : F64 :=
  match valsFind l k with | some (.Double x) => x | _ => 0

theorem beatmap.mod_settings.dbl_refines (vals : Slice (U32 × beatmap.mod_settings.SettingValue)) (k : U32) :
    beatmap.mod_settings.dbl vals k = ok (dblR vals.val k) := by
  unfold beatmap.mod_settings.dbl dblR
  rw [beatmap.mod_settings.vals_get_refines, bind_ok]
  cases valsFind vals.val k with
  | none => exact ms_D0
  | some v => cases v <;> first | exact ms_D0 | rfl

theorem dblR_spec (l : List (U32 × beatmap.mod_settings.SettingValue)) (h : KeysOk l) (k : U32) :
    (match ((valsS l).toArray.find? (·.1 == keyName k.val)).map (·.2) with
      | some (SettingValue.double x) => x | _ => 0) = dblR l k := by
  rw [List.find?_toArray, valsS_find l h k, dblR]
  cases valsFind l k with
  | none => rfl
  | some v => cases v <;> rfl

theorem beatmap.mod_settings.le_refines (a b : F64) : beatmap.mod_settings.le a b = ok (a < b || a == b) := by
  unfold beatmap.mod_settings.le
  simp only [float.F64.lt, float.F64.eq, bind_ok]
  by_cases h : a < b <;> simp [h]

/-! ## the change test of `Settings.assign` -/

/-- `changed` of `Settings.assign` (`Bindable.Value`'s `Equals` test per type) -/
def changedS (old : Option SettingValue) (v : SettingValue) : Bool :=
  match old, v with
  | some (.double a), .double b => !Framework.Bindable.equalsD a b
  | some (.float a), .float b => !Framework.Bindable.equalsF a b
  | some (.optFloat (some a)), .optFloat (some b) => !Framework.Bindable.equalsF a b
  | some a, b => !(a == b)
  | none, _ => true

theorem beatmap.mod_settings.assign_changed_refines (old : Option beatmap.mod_settings.SettingValue)
    (v : beatmap.mod_settings.SettingValue) :
    beatmap.mod_settings.assign_changed old v = ok (changedS (old.map svS) (svS v)) := by
  unfold beatmap.mod_settings.assign_changed
  cases old with
  | none => rfl
  | some a =>
    cases v <;> cases a <;>
      simp only [beatmap.mod_settings.setting_value_beq_refines, net.framework.equals_d_refines,
        net.framework.equals_f_refines, bind_ok, Option.map_some, svS, changedS]
    all_goals try rfl
    all_goals rename_i x y; cases x <;> cases y <;> rfl

/-! ## the callback selection of `Settings.assign` -/

/-- which `ValueChanged` callback `Settings.assign` runs (its final `match acr, key`):
1 WU initial, 2 WU final, 3 WD initial, 4 WD final, 5 MU inverse_muting, 0 none -/
def assignRuleS (acr key : String) : Nat :=
  if acr = "WU" then (if key = "initial_rate" then 1 else if key = "final_rate" then 2 else 0)
  else if acr = "WD" then (if key = "initial_rate" then 3 else if key = "final_rate" then 4 else 0)
  else if acr = "MU" then (if key = "inverse_muting" then 5 else 0)
  else 0

theorem key_id_iff (key : U32) (n : Nat) (hn : n < 44) :
    key.val = n ↔ keyName key.val = keyName n := by
  constructor
  · intro h; rw [h]
  · intro h
    have hk : key.val < 44 := by
      by_contra hc
      have : keyName key.val = "" := by by_contra h'; exact hc ((keyName_ne_empty _).mp h')
      rw [this] at h; exact (keyName_ne_empty n).mpr hn h.symm
    exact (keyName_inj _ _ hk hn).mp h

theorem beatmap.mod_settings.assign_rule_refines (acr : Slice U32) (hs : ValidStr acr) (key : U32) :
    ∃ r, beatmap.mod_settings.assign_rule acr key = ok r ∧
      r.val = assignRuleS (String.ofList (strS acr)) (keyName key.val) := by
  unfold beatmap.mod_settings.assign_rule assignRuleS
  simp only [lift, bind_ok, se_WU acr hs, se_WD acr hs, se_MU acr hs, decide_eq_true_eq,
    beatmap.names.K_INITIAL_RATE, beatmap.names.K_FINAL_RATE, beatmap.names.K_INVERSE_MUTING]
  have e1 := key_id_iff key 27 (by omega)
  have e2 := key_id_iff key 28 (by omega)
  have e3 := key_id_iff key 33 (by omega)
  simp only [show keyName 27 = "initial_rate" from rfl, show keyName 28 = "final_rate" from rfl,
    show keyName 33 = "inverse_muting" from rfl] at e1 e2 e3
  have c1 : (key = 27#u32) ↔ key.val = 27 := by rw [names_u32_eq_iff]; rfl
  have c2 : (key = 28#u32) ↔ key.val = 28 := by rw [names_u32_eq_iff]; rfl
  have c3 : (key = 33#u32) ↔ key.val = 33 := by rw [names_u32_eq_iff]; rfl
  simp only [c1, c2, c3]
  generalize String.ofList (strS acr) = A
  generalize keyName key.val = K at e1 e2 e3
  generalize key.val = kv at e1 e2 e3 ⊢
  by_cases a1 : A = "WU" <;> by_cases a2 : A = "WD" <;> by_cases a3 : A = "MU" <;>
    by_cases k1 : K = "initial_rate" <;> by_cases k2 : K = "final_rate" <;> by_cases k3 : K = "inverse_muting" <;>
    simp_all

/-! ## string copy -/

theorem copy_str_loop_ok (s : Slice U32) :
    ∀ (out : alloc.vec.Vec U32) (i : Usize), i.val ≤ s.val.length → out.val.length + (s.val.length - i.val) ≤ s.val.length →
      ∃ v, beatmap.mod_settings.copy_str_loop s out i = ok v ∧ v.val = out.val ++ s.val.drop i.val := by
  intro out i hi0 hlen
  unfold beatmap.mod_settings.copy_str_loop
  refine loop_ok _ (fun (x : alloc.vec.Vec U32 × Usize) => s.val.length - x.2.val)
    (fun (x : alloc.vec.Vec U32 × Usize) => x.2.val ≤ s.val.length ∧ x.1.val.length + (s.val.length - x.2.val) ≤ s.val.length ∧
      x.1.val ++ s.val.drop x.2.val = out.val ++ s.val.drop i.val)
    (fun (v : alloc.vec.Vec U32) => v.val = out.val ++ s.val.drop i.val) ?_ (out, i) ⟨hi0, hlen, rfl⟩
  rintro ⟨o, j⟩ ⟨hj, hol, heq⟩
  dsimp only at hj hol heq ⊢
  by_cases hlt : j.val < s.val.length
  · right
    have hlt' : j < Slice.len s := by show j.val < (Slice.len s).val; simpa using hlt
    obtain ⟨o1, ho1, ho1v⟩ := push_eq o (s.val[j.val]'hlt) (by have := s.property; have := usize_ge_32; omega)
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := s.property; omega)
    refine ⟨(o1, j1), by simp [beatmap.mod_settings.copy_str_loop.body, hlt', index_eq s j hlt, ho1, hj1], ?_, by dsimp only; omega⟩
    refine ⟨by dsimp only; omega, by dsimp only; rw [ho1v]; simp; omega, ?_⟩
    dsimp only
    rw [ho1v, hj1v, ← heq, List.drop_eq_getElem_cons hlt]; simp
  · left
    have hlt' : ¬ j < Slice.len s := by show ¬ j.val < (Slice.len s).val; simpa using hlt
    refine ⟨o, by simp [beatmap.mod_settings.copy_str_loop.body, hlt'], ?_⟩
    rw [← heq, List.drop_eq_nil_of_le (by omega)]; simp

/-- `copy_str` (no spec def): a copy of the string. -/
theorem beatmap.mod_settings.copy_str_refines (s : Slice U32) :
    ∃ v, beatmap.mod_settings.copy_str s = ok v ∧ v.val = s.val := by
  obtain ⟨v, hv, hvv⟩ := copy_str_loop_ok s (alloc.vec.Vec.new U32) 0#usize (by simp) (by simp)
  exact ⟨v, hv, by simpa using hvv⟩

/-! ## the MU type adjustment of `Settings.toMod` -/

/-- `ty` of `Settings.toMod`: MU's `MuteComboCount.MinValue` follows `InverseMuting` -/
def toModTypeS (acronym : String) (vals : Array (String × SettingValue)) (t : SettingType) : SettingType :=
  match acronym, t with
  | "MU", .int _ mx => SettingType.int (if (vals.find? (·.1 == "inverse_muting")).map (·.2) == some (.bool true) then 1 else 0) mx
  | _, t => t

theorem beatmap.mod_settings.to_mod_type_refines (acr : Slice U32) (hs : ValidStr acr)
    (vals : Slice (U32 × beatmap.mod_settings.SettingValue)) (hk : KeysOk vals.val) (d : beatmap.mod_settings.SettingDef) :
    ∃ r, beatmap.mod_settings.to_mod_type acr vals d = ok r ∧
      styS r = toModTypeS (String.ofList (strS acr)) (valsS vals.val).toArray (styS d.stype) := by
  unfold beatmap.mod_settings.to_mod_type toModTypeS
  have hf : ((valsS vals.val).toArray.find? (·.1 == "inverse_muting")).map (·.2) =
      (valsFind vals.val beatmap.names.K_INVERSE_MUTING).map svS := by
    rw [List.find?_toArray, ← valsS_find _ hk]; simp [beatmap.names.K_INVERSE_MUTING, keyName, keyNames]
  cases hd : d.stype with
  | Int mn mx =>
    simp only [lift, bind_ok, se_MU acr hs, beatmap.mod_settings.vals_get_refines, styS]
    by_cases hA : String.ofList (strS acr) = "MU"
    · rw [hA, hf]; simp only [decide_true, ite_true]
      cases valsFind vals.val beatmap.names.K_INVERSE_MUTING with
      | none => simp only [bind_ok, Bool.false_eq_true, ite_false]; refine ⟨_, rfl, ?_⟩; simp [styS]; rfl
      | some x =>
        simp only [beatmap.mod_settings.setting_value_beq_refines, bind_ok]
        have e : svS (beatmap.mod_settings.SettingValue.Bool true) = .bool true := rfl
        rw [e]
        by_cases hb : (svS x == SettingValue.bool true) = true
        · simp only [hb, ite_true]; refine ⟨_, rfl, ?_⟩; simp [styS, opt_beq_some, hb]; rfl
        · simp only [hb, Bool.false_eq_true, ite_false]; refine ⟨_, rfl, ?_⟩; simp [styS, opt_beq_some, hb]; rfl
    · simp only [hA, decide_false, Bool.false_eq_true, ite_false]
      refine ⟨_, rfl, ?_⟩
      simp only [styS]
      split <;> simp_all
  | _ => refine ⟨_, rfl, ?_⟩; simp only [styS]; split <;> simp_all

/-! ## last occurrence of a setting key (`settings.reverse.find?` of `Settings.toMod`) -/

/-- `key_is key` on a JSON entry -/
def keyQ (key : U32) (p : alloc.vec.Vec U32 × beatmap.mod_settings.JsonVal) : Bool :=
  decide (key.val < 44 ∧ strS (alloc.vec.Vec.deref p.1) = (keyName key.val).toList)

theorem take_succ_reverse {α} (l : List α) (k : Nat) (h : k < l.length) :
    (l.take (k + 1)).reverse = l[k] :: (l.take k).reverse := by
  rw [take_succ_get l k h]; simp

theorem beatmap.mod_settings.last_key_index_refines (key : U32)
    (st : Slice (alloc.vec.Vec U32 × beatmap.mod_settings.JsonVal)) (hv : ∀ p ∈ st.val, VValid p.1) :
    ∃ r, beatmap.mod_settings.last_key_index key st = ok r ∧ (∀ i, r = some i → i.val < st.val.length) ∧
      (r.bind fun i => st.val[i.val]?) = st.val.reverse.find? (keyQ key) := by
  unfold beatmap.mod_settings.last_key_index
  have hlen : (Slice.len st).val = st.val.length := by simp
  refine loop_ok _ (fun (x : Option Usize × Usize) => x.2.val + (if x.1.isNone then 1 else 0))
    (fun x => x.2.val ≤ st.val.length ∧
      (x.1 = none → st.val.reverse.find? (keyQ key) = (st.val.take x.2.val).reverse.find? (keyQ key)) ∧
      (∀ i : Usize, x.1 = some i → i.val < st.val.length ∧ st.val[i.val]? = st.val.reverse.find? (keyQ key)))
    (fun (r : Option Usize) => (∀ i : Usize, r = some i → i.val < st.val.length) ∧
      (r.bind fun i => st.val[i.val]?) = st.val.reverse.find? (keyQ key)) ?_ (none, Slice.len st)
    ⟨by rw [hlen], by intro _; rw [hlen, List.take_length], by simp⟩
  rintro ⟨f, k⟩ ⟨hk, hn, hs⟩
  dsimp only at hk hn hs ⊢
  cases f with
  | some i =>
    left
    refine ⟨some i, by simp [beatmap.mod_settings.last_key_index_loop.body, core.option.Option.is_none], ?_, ?_⟩
    · intro j hj; cases hj; exact (hs i rfl).1
    · simp only [Option.bind_some]; exact (hs i rfl).2
  | none =>
    have hn' := hn rfl
    by_cases hgt : 0 < k.val
    · right
      have hgt' : k > 0#usize := by show (0#usize).val < k.val; simpa using hgt
      obtain ⟨k1, hk1, hk1v, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := k) (y := 1#usize) (by simp; omega))
      simp at hk1v
      have hl : k1.val < st.val.length := by omega
      have hidx := index_eq st k1 hl
      have hvp := hv _ (List.getElem_mem hl)
      have hki := beatmap.names.key_is_refines key (alloc.vec.Vec.deref (st.val[k1.val]'hl).1) (vvalid_deref _ hvp)
      have hrev : (st.val.take k.val).reverse = (st.val[k1.val]'hl) :: (st.val.take k1.val).reverse := by
        rw [show k.val = k1.val + 1 by omega]; exact take_succ_reverse _ _ hl
      generalize hp : st.val[k1.val]'hl = p at hidx hvp hki hrev
      obtain ⟨pk, pj⟩ := p
      dsimp only at hki hvp
      by_cases hq : keyQ key (pk, pj) = true
      · refine ⟨(some k1, k1), ?_, ⟨by dsimp only; omega, by simp, ?_⟩, by simp; omega⟩
        · simp only [beatmap.mod_settings.last_key_index_loop.body, core.option.Option.is_none, Option.isNone_none,
            ite_true, hgt', hk1, bind_ok, hidx, hki]
          simp only [keyQ] at hq; simp [hq, hki]
        · intro j hj; cases hj; refine ⟨hl, ?_⟩
          rw [hn', hrev, List.find?_cons, hq, List.getElem?_eq_getElem hl, hp]
      · refine ⟨(none, k1), ?_, ⟨by dsimp only; omega, ?_, by simp⟩, by simp; omega⟩
        · simp only [beatmap.mod_settings.last_key_index_loop.body, core.option.Option.is_none, Option.isNone_none,
            ite_true, hgt', hk1, bind_ok, hidx, hki]
          simp only [keyQ] at hq; simp [hq, hki]
        · intro _; rw [hn', hrev, List.find?_cons]; simp only [Bool.not_eq_true] at hq; rw [hq]
    · left
      have hgt' : ¬ k > 0#usize := by show ¬ (0#usize).val < k.val; simpa using hgt
      refine ⟨none, by simp [beatmap.mod_settings.last_key_index_loop.body, core.option.Option.is_none, hgt'], by simp, ?_⟩
      rw [hn', show k.val = 0 by omega]; rfl

end OsuProofs
