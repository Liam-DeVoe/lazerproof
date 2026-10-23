/-
`beatmap::mod_settings`, part 9 (mods proof agent): `assign_f` / `set_d` (mutual, fuel-indexed) refine
`Settings.assignF` by induction on the fuel (D27/D29); `assign` = `assignF assignFuel`; `to_mod_apply`,
`to_mod_known`, `to_mod` refine `Settings.toMod` (spec normal form `ms_toMod_some`).
Spec-side normal form `ms_assignF_succ` (the callback `match acr, key` as `assignRuleS`).
-/
import OsuProofs.Beatmap.ModSettings8
import OsuProofs.LoopsR
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap OsuModel.Net.Framework

namespace OsuProofs
open OsuImpl

def msDblS (vals : Array (String × SettingValue)) (k : String) : F64 :=
  match (vals.find? (·.1 == k)).map (·.2) with | some (SettingValue.double x) => x | _ => 0

def msSetDS (n : Nat) (acr : String) (defs : List SettingDef) (vals : Array (String × SettingValue)) (k : String)
    (x : F64) : Array (String × SettingValue) :=
  match (defs.find? (·.key == k)).map (·.type) with
  | some (SettingType.double mn mx p) =>
    match Settings.setDouble mn mx p (msDblS vals k) x with
    | some y => Settings.assignF n acr defs vals k (SettingValue.double y)
    | none => vals
  | _ => vals

def msNv (v : SettingValue) : F64 := match v with | SettingValue.double x => x | _ => 0

def msRule (n : Nat) (acr : String) (defs : List SettingDef) (vals : Array (String × SettingValue)) (key : String)
    (v : SettingValue) : Array (String × SettingValue) :=
  match assignRuleS acr key with
  | 1 => if (decide (msDblS vals "final_rate" < msNv v) || msDblS vals "final_rate" == msNv v) = true
      then msSetDS n acr defs vals "final_rate" (msNv v + 0.01) else vals
  | 2 => if (decide (msNv v < msDblS vals "initial_rate") || msNv v == msDblS vals "initial_rate") = true
      then msSetDS n acr defs vals "initial_rate" (msNv v - 0.01) else vals
  | 3 => if (decide (msNv v < msDblS vals "final_rate") || msNv v == msDblS vals "final_rate") = true
      then msSetDS n acr defs vals "final_rate" (msNv v - 0.01) else vals
  | 4 => if (decide (msDblS vals "initial_rate" < msNv v) || msDblS vals "initial_rate" == msNv v) = true
      then msSetDS n acr defs vals "initial_rate" (msNv v + 0.01) else vals
  | 5 =>
    let mn : Int32 := if v == SettingValue.bool true then 1 else 0
    match (vals.find? (·.1 == "mute_combo_count")).map (·.2) with
    | some (SettingValue.int c) => Settings.setValue vals "mute_combo_count" (SettingValue.int (Settings.setInt mn 500 c))
    | _ => vals
  | _ => vals

theorem ms_assignF_succ (n : Nat) (acr : String) (defs : List SettingDef) (vals : Array (String × SettingValue))
    (key : String) (v : SettingValue) :
    Settings.assignF (n + 1) acr defs vals key v =
      if (!changedS ((vals.find? (·.1 == key)).map (·.2)) v) = true then vals
      else msRule n acr defs (Settings.setValue vals key v) key v := by
  simp only [Settings.assignF]
  show (if (!changedS ((vals.find? (·.1 == key)).map (·.2)) v) = true then vals else _) = _
  congr 1
  simp only [msRule, assignRuleS]
  split
  case h_1 | h_2 | h_3 | h_4 | h_5 =>
    simp only [show ("WU" = "WU") = True from eq_self _, show ("WD" = "WD") = True from eq_self _,
      show ("MU" = "MU") = True from eq_self _,
      show ("initial_rate" = "initial_rate") = True from eq_self _,
      show ("final_rate" = "final_rate") = True from eq_self _,
      show ("inverse_muting" = "inverse_muting") = True from eq_self _,
      show ("WD" = "WU") = False by decide, show ("MU" = "WU") = False by decide, show ("MU" = "WD") = False by decide,
      show ("final_rate" = "initial_rate") = False by decide, ite_true, ite_false]
    all_goals rfl
  · split_ifs <;> simp_all


/-- refinement of `assign_f` at fuel `n` -/
def msAssignOK (n : Nat) : Prop :=
  ∀ (fuel : U32), fuel.val = n → ∀ (acr : Slice U32), ValidStr acr →
    ∀ (defs : Slice beatmap.mod_settings.SettingDef), DefsOk defs.val →
    ∀ (vals : alloc.vec.Vec (U32 × beatmap.mod_settings.SettingValue)), KeysOk vals.val →
    ∀ (key : U32), key.val < 44 → ∀ (v : beatmap.mod_settings.SettingValue),
      ∃ r, beatmap.mod_settings.assign_f fuel acr defs vals key v = ok r ∧ KeysOk r.val ∧
        (valsS r.val).toArray = Settings.assignF n (String.ofList (strS acr)) (defs.val.map sdS)
          (valsS vals.val).toArray (keyName key.val) (svS v)

theorem ms_msDblS (l : List (U32 × beatmap.mod_settings.SettingValue)) (h : KeysOk l) (k : U32) :
    msDblS (valsS l).toArray (keyName k.val) = dblR l k := by
  rw [← dblR_spec l h k]; rfl

theorem ms_set_d (n : Nat) (ih : msAssignOK n) (fuel : U32) (hf : fuel.val = n) (acr : Slice U32) (hs : ValidStr acr)
    (defs : Slice beatmap.mod_settings.SettingDef) (hd : DefsOk defs.val)
    (vals : alloc.vec.Vec (U32 × beatmap.mod_settings.SettingValue)) (hk : KeysOk vals.val)
    (k : U32) (hkk : k.val < 44) (x : F64) :
    ∃ r, beatmap.mod_settings.set_d fuel acr defs vals k x = ok r ∧ KeysOk r.val ∧
      (valsS r.val).toArray = msSetDS n (String.ofList (strS acr)) (defs.val.map sdS) (valsS vals.val).toArray
        (keyName k.val) x := by
  unfold beatmap.mod_settings.set_d msSetDS
  rw [beatmap.mod_settings.type_of_refines, typeOfR_spec defs.val hd k]
  simp only [bind_ok]
  cases ht : typeOfR defs.val k with
  | none => exact ⟨vals, rfl, hk, rfl⟩
  | some st =>
    cases st
    case Double mn mx p =>
      simp only [Option.map_some, styS]
      rw [beatmap.mod_settings.dbl_refines, ms_msDblS vals.val hk k, ms_deref_val]
      simp only [bind_ok, beatmap.mod_settings.set_double_refines]
      cases Settings.setDouble mn mx p (dblR vals.val k) x with
      | none => exact ⟨vals, rfl, hk, rfl⟩
      | some y => exact ih fuel hf acr hs defs hd vals hk k hkk (.Double y)
    all_goals exact ⟨vals, rfl, hk, rfl⟩


theorem ms_spec_of_ex {α} {m : Result α} {P : α → Prop} (h : ∃ r, m = ok r ∧ P r) : WP.spec m P := by
  obtain ⟨r, rfl, hr⟩ := h; exact (WP.spec_ok r).mpr hr

theorem ms_kFIN : keyName beatmap.names.K_FINAL_RATE.val = "final_rate" := by
  simp [beatmap.names.K_FINAL_RATE, keyName, keyNames]
theorem ms_kINI : keyName beatmap.names.K_INITIAL_RATE.val = "initial_rate" := by
  simp [beatmap.names.K_INITIAL_RATE, keyName, keyNames]
theorem ms_kMCC : keyName beatmap.names.K_MUTE_COMBO_COUNT.val = "mute_combo_count" := by
  simp [beatmap.names.K_MUTE_COMBO_COUNT, keyName, keyNames]
theorem ms_kFIN_lt : beatmap.names.K_FINAL_RATE.val < 44 := by simp [beatmap.names.K_FINAL_RATE]
theorem ms_kINI_lt : beatmap.names.K_INITIAL_RATE.val < 44 := by simp [beatmap.names.K_INITIAL_RATE]
theorem ms_kMCC_lt : beatmap.names.K_MUTE_COMBO_COUNT.val < 44 := by simp [beatmap.names.K_MUTE_COMBO_COUNT]

theorem ms_nv (v : beatmap.mod_settings.SettingValue) :
    (match v with
      | beatmap.mod_settings.SettingValue.Bool _ => beatmap.mod_settings.D0
      | beatmap.mod_settings.SettingValue.Int _ => beatmap.mod_settings.D0
      | beatmap.mod_settings.SettingValue.Double x => ok x
      | beatmap.mod_settings.SettingValue.Float _ => beatmap.mod_settings.D0
      | beatmap.mod_settings.SettingValue.Enum _ => beatmap.mod_settings.D0
      | beatmap.mod_settings.SettingValue.OptInt _ => beatmap.mod_settings.D0
      | beatmap.mod_settings.SettingValue.OptFloat _ => beatmap.mod_settings.D0) = ok (msNv (svS v)) := by
  cases v <;> first | exact ms_D0 | rfl

set_option maxHeartbeats 1600000 in
theorem ms_assign_ok : ∀ n, msAssignOK n := by
  intro n
  induction n with
  | zero =>
    intro fuel hf acr hs defs hd vals hk key hkey v
    have : fuel = 0#u32 := UScalar.eq_of_val_eq (by rw [hf]; rfl)
    subst this
    exact ⟨vals, by unfold beatmap.mod_settings.assign_f; rw [if_pos rfl], hk, by simp [Settings.assignF]⟩
  | succ n ih =>
    intro fuel hf acr hs defs hd vals hk key hkey v
    have hf0 : fuel ≠ 0#u32 := by intro h; rw [h] at hf; simp at hf
    obtain ⟨f1, hf1, hf1v⟩ := eq_ok_of_spec (UScalar.sub_spec (x := fuel) (y := 1#u32) (by simp; omega))
    have hf1n : f1.val = n := by have := hf1v.1; simp at this; omega
    rw [ms_assignF_succ]
    unfold beatmap.mod_settings.assign_f
    simp only [hf0, if_false, hf1, bind_ok, ms_deref_val, beatmap.mod_settings.vals_get_refines,
      beatmap.mod_settings.assign_changed_refines, ← valsS_find vals.val hk key, List.find?_toArray]
    by_cases hc : changedS (((valsS vals.val).find? (fun p => p.1 == keyName key.val)).map (·.2)) (svS v) = true
    swap
    · simp only [hc, Bool.false_eq_true, if_false, Bool.not_false, if_true]
      exact ⟨vals, rfl, hk, rfl⟩
    simp only [hc, if_true, Bool.not_true, Bool.false_eq_true, if_false]
    obtain ⟨vals1, hv1, hv1v⟩ := beatmap.mod_settings.set_value_refines vals key v
    have hk1 : KeysOk vals1.val := by rw [hv1v]; exact KeysOk_setValR _ hk key v
    have hsv : Settings.setValue (valsS vals.val).toArray (keyName key.val) (svS v) = (valsS vals1.val).toArray := by
      rw [hv1v, setValR_spec _ hk]
    rw [hsv]
    have hstep : float.F64.from_bits 4576918229304087675#u64 = ok (0.01 : F64) := by
      simp only [float.F64.from_bits]; congr 1
    obtain ⟨r, hr, hrv⟩ := beatmap.mod_settings.assign_rule_refines acr hs key
    simp only [hv1, bind_ok, ms_nv, beatmap.mod_settings.dbl_refines, ms_deref_val, hstep, hr]
    rw [← ms_msDblS vals1.val hk1, ← ms_msDblS vals1.val hk1, ms_kFIN, ms_kINI]
    unfold msRule
    rw [← hrv]
    generalize hNV : msNv (svS v) = NV
    apply eq_ok_of_spec
    split
    all_goals
      simp only [svS, msNv] at hNV
      subst hNV
      simp only [ms_D0, bind_ok]
      have hlit : (1#32#uscalar : U32).val = 1 ∧ (2#32#uscalar : U32).val = 2 ∧ (3#32#uscalar : U32).val = 3 ∧
          (4#32#uscalar : U32).val = 4 ∧ (5#32#uscalar : U32).val = 5 := by decide
      obtain ⟨l1, l2, l3, l4, l5⟩ := hlit
      split
      · simp only [l1]
        simp only [beatmap.mod_settings.le_refines, bind_ok, float.F64.add, float.F64.sub, l1]
        split
        · rename_i hb
          try simp only [hb, ite_true]
          first
          | exact ms_spec_of_ex (by
              obtain ⟨r, h1, h2, h3⟩ := ms_set_d n ih f1 hf1n acr hs defs hd vals1 hk1 _ ms_kFIN_lt _
              exact ⟨r, h1, h2, by rw [h3, ms_kFIN]⟩)
          | exact ms_spec_of_ex (by
              obtain ⟨r, h1, h2, h3⟩ := ms_set_d n ih f1 hf1n acr hs defs hd vals1 hk1 _ ms_kINI_lt _
              exact ⟨r, h1, h2, by rw [h3, ms_kINI]⟩)
        · rename_i hb
          try simp only [hb, ite_false, Bool.false_eq_true]
          rw [WP.spec_ok]; exact ⟨hk1, rfl⟩
      · simp only [l2]
        simp only [beatmap.mod_settings.le_refines, bind_ok, float.F64.add, float.F64.sub, l2]
        split
        · rename_i hb
          try simp only [hb, ite_true]
          first
          | exact ms_spec_of_ex (by
              obtain ⟨r, h1, h2, h3⟩ := ms_set_d n ih f1 hf1n acr hs defs hd vals1 hk1 _ ms_kFIN_lt _
              exact ⟨r, h1, h2, by rw [h3, ms_kFIN]⟩)
          | exact ms_spec_of_ex (by
              obtain ⟨r, h1, h2, h3⟩ := ms_set_d n ih f1 hf1n acr hs defs hd vals1 hk1 _ ms_kINI_lt _
              exact ⟨r, h1, h2, by rw [h3, ms_kINI]⟩)
        · rename_i hb
          try simp only [hb, ite_false, Bool.false_eq_true]
          rw [WP.spec_ok]; exact ⟨hk1, rfl⟩
      · simp only [l3]
        simp only [beatmap.mod_settings.le_refines, bind_ok, float.F64.add, float.F64.sub, l3]
        split
        · rename_i hb
          try simp only [hb, ite_true]
          first
          | exact ms_spec_of_ex (by
              obtain ⟨r, h1, h2, h3⟩ := ms_set_d n ih f1 hf1n acr hs defs hd vals1 hk1 _ ms_kFIN_lt _
              exact ⟨r, h1, h2, by rw [h3, ms_kFIN]⟩)
          | exact ms_spec_of_ex (by
              obtain ⟨r, h1, h2, h3⟩ := ms_set_d n ih f1 hf1n acr hs defs hd vals1 hk1 _ ms_kINI_lt _
              exact ⟨r, h1, h2, by rw [h3, ms_kINI]⟩)
        · rename_i hb
          try simp only [hb, ite_false, Bool.false_eq_true]
          rw [WP.spec_ok]; exact ⟨hk1, rfl⟩
      · simp only [l4]
        simp only [beatmap.mod_settings.le_refines, bind_ok, float.F64.add, float.F64.sub, l4]
        split
        · rename_i hb
          try simp only [hb, ite_true]
          first
          | exact ms_spec_of_ex (by
              obtain ⟨r, h1, h2, h3⟩ := ms_set_d n ih f1 hf1n acr hs defs hd vals1 hk1 _ ms_kFIN_lt _
              exact ⟨r, h1, h2, by rw [h3, ms_kFIN]⟩)
          | exact ms_spec_of_ex (by
              obtain ⟨r, h1, h2, h3⟩ := ms_set_d n ih f1 hf1n acr hs defs hd vals1 hk1 _ ms_kINI_lt _
              exact ⟨r, h1, h2, by rw [h3, ms_kINI]⟩)
        · rename_i hb
          try simp only [hb, ite_false, Bool.false_eq_true]
          rw [WP.spec_ok]; exact ⟨hk1, rfl⟩
      · simp only [l5]
        simp only [beatmap.mod_settings.setting_value_beq_refines, bind_ok, List.find?_toArray]
        rw [← ms_kMCC, valsS_find vals1.val hk1 _]
        have h500 : i32S 500#i32 = 500 := by decide
        have h1 : i32S 1#i32 = 1 := by decide
        have h0 : i32S 0#i32 = 0 := by decide
        split
        all_goals
          rename_i hb
          simp only [bind_ok]
          cases hvf : valsFind vals1.val beatmap.names.K_MUTE_COMBO_COUNT with
          | none => rw [WP.spec_ok]; exact ⟨hk1, rfl⟩
          | some sv =>
            cases sv
            case Int c =>
              first
              | (obtain ⟨i1, hi1, hi1v⟩ := beatmap.mod_settings.set_int_refines 1#i32 500#i32 c
                 obtain ⟨w, hw, hwv⟩ := beatmap.mod_settings.set_value_refines vals1 beatmap.names.K_MUTE_COMBO_COUNT
                   (.Int i1)
                 dsimp only; rw [hi1]; simp only [bind_ok]; rw [hw]
                 rw [WP.spec_ok]
                 refine ⟨by rw [hwv]; exact KeysOk_setValR _ hk1 _ _, ?_⟩
                 rw [hwv, setValR_spec _ hk1, ms_kMCC]
                 rw [Option.map_some, show svS (beatmap.mod_settings.SettingValue.Int c) = SettingValue.int (i32S c) from rfl]
                 dsimp only
                 rw [show svS (beatmap.mod_settings.SettingValue.Int i1) = SettingValue.int (i32S i1) from rfl, hi1v, h500, h1]
                 split
                 · first | rfl | (exfalso; rename_i hc; exact hc hb)
                 · first | rfl | (exfalso; rename_i hc; exact hc hb))
              | (obtain ⟨i1, hi1, hi1v⟩ := beatmap.mod_settings.set_int_refines 0#i32 500#i32 c
                 obtain ⟨w, hw, hwv⟩ := beatmap.mod_settings.set_value_refines vals1 beatmap.names.K_MUTE_COMBO_COUNT
                   (.Int i1)
                 dsimp only; rw [hi1]; simp only [bind_ok]; rw [hw]
                 rw [WP.spec_ok]
                 refine ⟨by rw [hwv]; exact KeysOk_setValR _ hk1 _ _, ?_⟩
                 rw [hwv, setValR_spec _ hk1, ms_kMCC]
                 rw [Option.map_some, show svS (beatmap.mod_settings.SettingValue.Int c) = SettingValue.int (i32S c) from rfl]
                 dsimp only
                 rw [show svS (beatmap.mod_settings.SettingValue.Int i1) = SettingValue.int (i32S i1) from rfl, hi1v, h500, h0]
                 split
                 · first | rfl | (exfalso; rename_i hc; exact hb hc)
                 · first | rfl | (exfalso; rename_i hc; exact hb hc))
            all_goals (rw [WP.spec_ok]; exact ⟨hk1, rfl⟩)
      · rename_i h1 h2 h3 h4 h5
        rw [WP.spec_ok]
        refine ⟨hk1, ?_⟩
        split
        all_goals first
          | rfl
          | (exfalso; rename_i hh
             first
             | exact h1 (UScalar.eq_of_val_eq (hh.trans l1.symm))
             | exact h2 (UScalar.eq_of_val_eq (hh.trans l2.symm))
             | exact h3 (UScalar.eq_of_val_eq (hh.trans l3.symm))
             | exact h4 (UScalar.eq_of_val_eq (hh.trans l4.symm))
             | exact h5 (UScalar.eq_of_val_eq (hh.trans l5.symm)))

/-- `Bindable.Value` assignment + `ValueChanged` callbacks with explicit fuel; spec `Settings.assignF`
(valid strings, known keys). -/
theorem beatmap.mod_settings.assign_f_refines (fuel : U32) (acr : Slice U32) (hs : ValidStr acr)
    (defs : Slice beatmap.mod_settings.SettingDef) (hd : DefsOk defs.val)
    (vals : alloc.vec.Vec (U32 × beatmap.mod_settings.SettingValue)) (hk : KeysOk vals.val)
    (key : U32) (hkey : key.val < 44) (v : beatmap.mod_settings.SettingValue) :
    ∃ r, beatmap.mod_settings.assign_f fuel acr defs vals key v = ok r ∧ KeysOk r.val ∧
      (valsS r.val).toArray = Settings.assignF fuel.val (String.ofList (strS acr)) (defs.val.map sdS)
        (valsS vals.val).toArray (keyName key.val) (svS v) :=
  ms_assign_ok fuel.val fuel rfl acr hs defs hd vals hk key hkey v

/-- the `setD` callback of `Settings.assignF` (nested call at fuel `fuel`) -/
theorem beatmap.mod_settings.set_d_refines (fuel : U32) (acr : Slice U32) (hs : ValidStr acr)
    (defs : Slice beatmap.mod_settings.SettingDef) (hd : DefsOk defs.val)
    (vals : alloc.vec.Vec (U32 × beatmap.mod_settings.SettingValue)) (hk : KeysOk vals.val)
    (k : U32) (hkk : k.val < 44) (x : F64) :
    ∃ r, beatmap.mod_settings.set_d fuel acr defs vals k x = ok r ∧ KeysOk r.val ∧
      (valsS r.val).toArray = msSetDS fuel.val (String.ofList (strS acr)) (defs.val.map sdS) (valsS vals.val).toArray
        (keyName k.val) x :=
  ms_set_d fuel.val (ms_assign_ok fuel.val) fuel rfl acr hs defs hd vals hk k hkk x

/-- `Bindable.Value = v` + callbacks; spec `Settings.assign` (= `assignF assignFuel`) -/
theorem beatmap.mod_settings.assign_refines (acr : Slice U32) (hs : ValidStr acr)
    (defs : Slice beatmap.mod_settings.SettingDef) (hd : DefsOk defs.val)
    (vals : alloc.vec.Vec (U32 × beatmap.mod_settings.SettingValue)) (hk : KeysOk vals.val)
    (key : U32) (hkey : key.val < 44) (v : beatmap.mod_settings.SettingValue) :
    ∃ r, beatmap.mod_settings.assign acr defs vals key v = ok r ∧ KeysOk r.val ∧
      (valsS r.val).toArray = Settings.assign (String.ofList (strS acr)) (defs.val.map sdS)
        (valsS vals.val).toArray (keyName key.val) (svS v) := by
  have hf : beatmap.mod_settings.ASSIGN_FUEL.val = Settings.assignFuel := by
    simp [beatmap.mod_settings.ASSIGN_FUEL, Settings.assignFuel]
  obtain ⟨r, h1, h2, h3⟩ := beatmap.mod_settings.assign_f_refines beatmap.mod_settings.ASSIGN_FUEL acr hs defs hd vals hk
    key hkey v
  refine ⟨r, by unfold beatmap.mod_settings.assign; exact h1, h2, ?_⟩
  rw [h3, hf]; rfl


/-! ## `APIMod.ToMod` -/

/-- Rust JSON settings (key, value) ↦ spec list -/
def msSetS (st : List (alloc.vec.Vec U32 × beatmap.mod_settings.JsonVal)) : List (String × JsonVal) :=
  st.map fun p => (vstrS p.1, jvS p.2)

/-- one `for d in defs` step of `Settings.toMod` -/
def msApplyS (acronym : String) (defs : List SettingDef) (settings : List (String × JsonVal))
    (vals : Array (String × SettingValue)) (d : SettingDef) : Array (String × SettingValue) :=
  match (settings.reverse.find? (·.1 == d.key)).map (·.2) with
  | none => vals
  | some j =>
    let old := ((vals.find? (·.1 == d.key)).map (·.2)).getD d.default
    match Settings.parse (toModTypeS acronym vals d.type) old j with
    | some v => Settings.assign acronym defs vals d.key v
    | none => vals

theorem ms_keyQ (key : U32) (hk : key.val < 44) (p : alloc.vec.Vec U32 × beatmap.mod_settings.JsonVal) :
    ((vstrS p.1, jvS p.2).1 == keyName key.val) = keyQ key p := by
  simp only [keyQ, hk, true_and, vstrS, strS, ms_deref_val]
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, decide_eq_true_eq, ofList_eq_lit]

theorem ms_find_settings (key : U32) (hk : key.val < 44) (st : List (alloc.vec.Vec U32 × beatmap.mod_settings.JsonVal)) :
    ((msSetS st).reverse.find? (·.1 == keyName key.val)).map (·.2) =
      (st.reverse.find? (keyQ key)).map (fun p => jvS p.2) := by
  simp only [msSetS, ← List.map_reverse, List.find?_map, Option.map_map]
  congr 1
  · congr 1; funext p; simp only [Function.comp]; exact ms_keyQ key hk p


/-- one setting of `APIMod.ToMod` (the `for d in defs` body of `Settings.toMod`) -/
theorem beatmap.mod_settings.to_mod_apply_refines (acr : Slice U32) (hs : ValidStr acr)
    (defs : Slice beatmap.mod_settings.SettingDef) (hd : DefsOk defs.val)
    (vals : alloc.vec.Vec (U32 × beatmap.mod_settings.SettingValue)) (hk : KeysOk vals.val)
    (d : beatmap.mod_settings.SettingDef) (hdk : d.key.val < 44)
    (st : Slice (alloc.vec.Vec U32 × beatmap.mod_settings.JsonVal)) (hv : ∀ p ∈ st.val, VValid p.1)
    (hj : ∀ p ∈ st.val, JOk' p.2) :
    ∃ r, beatmap.mod_settings.to_mod_apply acr defs vals d st = ok r ∧ KeysOk r.val ∧
      (valsS r.val).toArray = msApplyS (String.ofList (strS acr)) (defs.val.map sdS) (msSetS st.val)
        (valsS vals.val).toArray (sdS d) := by
  obtain ⟨o, ho, hoi, hob⟩ := beatmap.mod_settings.last_key_index_refines d.key st hv
  unfold beatmap.mod_settings.to_mod_apply msApplyS
  rw [show (sdS d).key = keyName d.key.val from rfl, ms_find_settings d.key hdk st.val, ← hob]
  simp only [ho, bind_ok]
  cases o with
  | none => exact ⟨vals, rfl, hk, rfl⟩
  | some si =>
    have hsi := hoi si rfl
    simp only [Option.bind_some, List.getElem?_eq_getElem hsi, Option.map_some]
    have hfind : ((valsS vals.val).toArray.find? (·.1 == keyName d.key.val)).map (·.2) = (valsFind vals.val d.key).map svS := by
      rw [List.find?_toArray, valsS_find _ hk]
    rw [hfind]
    obtain ⟨ty, hty, htyv⟩ := beatmap.mod_settings.to_mod_type_refines acr hs (alloc.vec.Vec.deref vals) (by simpa using hk) d
    simp only [ms_deref_val] at htyv
    simp only [beatmap.mod_settings.vals_get_refines, ms_deref_val, bind_ok, hty, index_eq st si hsi]
    have hjs : JOk' (st.val[si.val]'hsi).2 := hj _ (List.getElem_mem hsi)
    generalize hp : st.val[si.val]'hsi = p at hjs ⊢
    obtain ⟨k0, jv⟩ := p
    rw [show (sdS d).type = styS d.stype from rfl, ← htyv]
    cases hvf : valsFind vals.val d.key with
    | none =>
      simp only [Option.map_none, Option.getD_none, show (sdS d).default = svS d.default from rfl]
      obtain ⟨r, hr, hrv⟩ := beatmap.mod_settings.parse_refines ty d.default jv hjs
      rw [← hrv]
      cases r with
      | none => exact ⟨vals, by simp [hr], hk, rfl⟩
      | some v =>
        obtain ⟨r2, h1, h2, h3⟩ := beatmap.mod_settings.assign_refines acr hs defs hd vals hk d.key hdk v
        exact ⟨r2, by simp [hr, h1], h2, by simpa using h3⟩
    | some x =>
      simp only [Option.map_some, Option.getD_some]
      obtain ⟨r, hr, hrv⟩ := beatmap.mod_settings.parse_refines ty x jv hjs
      rw [← hrv]
      cases r with
      | none => exact ⟨vals, by simp [hr], hk, rfl⟩
      | some v =>
        obtain ⟨r2, h1, h2, h3⟩ := beatmap.mod_settings.assign_refines acr hs defs hd vals hk d.key hdk v
        exact ⟨r2, by simp [hr, h1], h2, by simpa using h3⟩

/-- the known-acronym branch of `Settings.toMod` -/
def msKnownS (acronym : String) (defs : List SettingDef) (settings : List (String × JsonVal)) : ModConfig :=
  let vals := (defs.map fun d => (d.key, d.default)).toArray
  if settings.isEmpty then { acronym, settings := vals }
  else { acronym, settings := defs.foldl (msApplyS acronym defs settings) vals }

instance msInhSD : Inhabited SettingDef := ⟨⟨"", .bool false, .bool false⟩⟩

instance msInhSV : Inhabited beatmap.mod_settings.SettingValue := ⟨.Bool false⟩

theorem ms_tmk_loop0 (defs : alloc.vec.Vec beatmap.mod_settings.SettingDef) :
    ∃ r, beatmap.mod_settings.to_mod_known_loop0 defs (alloc.vec.Vec.new _) 0#usize = ok r ∧
      r.val = defs.val.map (fun d => (d.key, d.default)) := by
  have := loop_push_map (fun (x : alloc.vec.Vec (U32 × beatmap.mod_settings.SettingValue) × Usize) =>
      beatmap.mod_settings.to_mod_known_loop0.body defs x.1 x.2) defs.val.length
    (fun i => ((defs.val.map (fun d => (d.key, d.default)))[i]!))
    (by
      intro ts i hi hmax
      have hil : i < alloc.vec.Vec.len defs := by show i.val < (alloc.vec.Vec.len defs).val; simpa using hi
      obtain ⟨w, hw, hwv⟩ := push_eq ts ((defs.val[i.val]'hi).key, (defs.val[i.val]'hi).default) (by omega)
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := defs.property; omega)
      refine ⟨w, i1, ?_, by rw [hwv, getElem!_pos _ i.val (by simpa using hi)]; simp, hi1v⟩
      simp only [beatmap.mod_settings.to_mod_known_loop0.body, hil, if_true, vec_index_eq defs i hi, bind_ok, hw, hi1])
    (by
      intro ts i hi
      have hil : ¬ i < alloc.vec.Vec.len defs := by show ¬ i.val < (alloc.vec.Vec.len defs).val; simp; omega
      simp [beatmap.mod_settings.to_mod_known_loop0.body, hil])
    (alloc.vec.Vec.new _) 0#usize (by simp) (by simp)
  obtain ⟨r, hl, hr⟩ := this
  refine ⟨r, by unfold beatmap.mod_settings.to_mod_known_loop0; exact hl, ?_⟩
  rw [hr]; simp
  apply List.ext_getElem (by simp)
  intro k h1 h2; simp at h2; simp [List.getElem?_eq_getElem h2]

theorem ms_tmk_loop1 (acr : alloc.vec.Vec U32) (hs : VValid acr) (defs : alloc.vec.Vec beatmap.mod_settings.SettingDef)
    (hd : DefsOk defs.val) (st : Slice (alloc.vec.Vec U32 × beatmap.mod_settings.JsonVal))
    (hv : ∀ p ∈ st.val, VValid p.1) (hj : ∀ p ∈ st.val, JOk' p.2)
    (vals : alloc.vec.Vec (U32 × beatmap.mod_settings.SettingValue)) (hk : KeysOk vals.val) :
    ∃ r, beatmap.mod_settings.to_mod_known_loop1 acr defs st vals 0#usize = ok r ∧ KeysOk r.val ∧
      (valsS r.val).toArray = (defs.val.map sdS).foldl (msApplyS (vstrS acr) (defs.val.map sdS) (msSetS st.val))
        (valsS vals.val).toArray := by
  have hacr : ValidStr (alloc.vec.Vec.deref acr) := vvalid_deref acr hs
  obtain ⟨y, hl, hy⟩ := loop_fold_gen
    (fun (x : alloc.vec.Vec (U32 × beatmap.mod_settings.SettingValue) × Usize) =>
      beatmap.mod_settings.to_mod_known_loop1.body acr defs st x.1 x.2)
    (·.2) defs.val.length (fun x => KeysOk x.1.val) (fun x => (valsS x.1.val).toArray)
    (fun k s => msApplyS (vstrS acr) (defs.val.map sdS) (msSetS st.val) s ((defs.val.map sdS)[k]!))
    (fun y s => (valsS y.val).toArray = s ∧ KeysOk y.val)
    (by
      rintro ⟨v, i⟩ hI hi
      simp only at hI hi ⊢
      have hil : i < alloc.vec.Vec.len defs := by show i.val < (alloc.vec.Vec.len defs).val; simpa using hi
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := defs.property; omega)
      have hdk : (defs.val[i.val]'hi).key.val < 44 := hd _ (List.getElem_mem hi)
      obtain ⟨r, hr, hrk, hrv⟩ := beatmap.mod_settings.to_mod_apply_refines (alloc.vec.Vec.deref acr) hacr
        (alloc.vec.Vec.deref defs) (by simpa using hd) v hI (defs.val[i.val]'hi) hdk st hv hj
      have hil' : i.val < (List.map sdS defs.val).length := by simpa using hi
      refine ⟨(r, i1), ?_, hi1v, ?_, hrk⟩
      · simp only [beatmap.mod_settings.to_mod_known_loop1.body, hil, if_true, vec_index_eq defs i hi, bind_ok, hr, hi1]
      · simp only at hrv ⊢
        rw [hrv, getElem!_pos _ i.val hil']
        simp [vstrS, strS, ms_deref_val])
    (by
      rintro ⟨v, i⟩ hI hi
      simp only at hI hi ⊢
      have hil : ¬ i < alloc.vec.Vec.len defs := by show ¬ i.val < (alloc.vec.Vec.len defs).val; simp; omega
      exact ⟨v, by simp [beatmap.mod_settings.to_mod_known_loop1.body, hil], rfl, hI⟩)
    (vals, 0#usize) hk (by simp)
  refine ⟨y, by unfold beatmap.mod_settings.to_mod_known_loop1; exact hl, hy.2, ?_⟩
  rw [hy.1, foldl_iterR]; simp

/-- the known-acronym part of `APIMod.ToMod` -/
theorem beatmap.mod_settings.to_mod_known_refines (acr : alloc.vec.Vec U32) (hs : VValid acr)
    (defs : alloc.vec.Vec beatmap.mod_settings.SettingDef) (hd : DefsOk defs.val)
    (st : Slice (alloc.vec.Vec U32 × beatmap.mod_settings.JsonVal))
    (hv : ∀ p ∈ st.val, VValid p.1) (hj : ∀ p ∈ st.val, JOk' p.2) :
    ∃ r, beatmap.mod_settings.to_mod_known acr defs st = ok r ∧ KeysOk r.settings.val ∧
      mcS r = msKnownS (vstrS acr) (defs.val.map sdS) (msSetS st.val) := by
  obtain ⟨v0, hv0, hv0v⟩ := ms_tmk_loop0 defs
  have hk0 : KeysOk v0.val := by
    intro p hp; rw [hv0v] at hp; simp only [List.mem_map] at hp
    obtain ⟨d, hd', rfl⟩ := hp; exact hd d hd'
  have hvs : (valsS v0.val).toArray = ((defs.val.map sdS).map fun d => (d.key, d.default)).toArray := by
    rw [hv0v]; simp [valsS, sdS, Function.comp_def]
  unfold beatmap.mod_settings.to_mod_known msKnownS
  simp only [hv0, bind_ok]
  by_cases h0 : st.val.length = 0
  · have h0' : Slice.len st = 0#usize := UScalar.eq_of_val_eq (by simpa using h0)
    have he : (msSetS st.val).isEmpty = true := by simp [msSetS, List.isEmpty_iff, List.length_eq_zero_iff.mp h0]
    refine ⟨{ acronym := acr, known := true, settings := v0 }, by simp only [h0', if_true], hk0, ?_⟩
    simp only [he, if_true, mcS, ← hvs]
  · have h0' : ¬ Slice.len st = 0#usize := by intro h; apply h0; have := congrArg UScalar.val h; simpa using this
    have he : (msSetS st.val).isEmpty = false := by
      simp [msSetS, List.isEmpty_iff]; intro h; exact h0 (by simp [h])
    obtain ⟨r, hr, hrk, hrv⟩ := ms_tmk_loop1 acr hs defs hd st hv hj v0 hk0
    refine ⟨{ acronym := acr, known := true, settings := r }, by simp only [h0', if_false, hr, bind_ok], hrk, ?_⟩
    · simp only [he, Bool.false_eq_true, if_false, mcS, hrv, hvs]


theorem ms_forIn_yield_foldl {X S : Type} (G : X → S → Id (ForInStep S)) (g : S → X → S)
    (hG : ∀ x s, G x s = .yield (g s x)) : ∀ (l : List X) (s : S), forIn (m := Id) l s G = l.foldl g s := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons x t ih => intro s; rw [List.forIn_cons, hG]; exact ih _

theorem ms_toMod_some (a : String) (st : List (String × JsonVal)) (defs : List SettingDef)
    (h : Settings.table (a.map Char.toUpper) = some defs) :
    Settings.toMod a st = msKnownS (a.map Char.toUpper) defs st := by
  unfold Settings.toMod msKnownS
  simp only [h, Id.run]
  split
  · rfl
  · rw [id_bind_eq, ms_forIn_yield_foldl _ (msApplyS (a.map Char.toUpper) defs st) ?hG]
    · rfl
    · intro d s
      simp only [msApplyS]
      split
      · rename_i h1; simp [h1]; rfl
      · rename_i j h1
        simp only [h1]
        generalize hP : Settings.parse (toModTypeS (a.map Char.toUpper) s d.type)
          ((Option.map (fun x => x.2) (s.find? (fun x => x.1 == d.key))).getD d.default) j = P
        split
        · rename_i v hv; have e := hv.symm.trans hP; subst e; rfl
        · rename_i hv; have e := hv.symm.trans hP; subst e; rfl

set_option maxHeartbeats 2000000 in
theorem ms_table_keys (acr : String) (defs : List SettingDef) (h : Settings.table acr = some defs) :
    ∀ d ∈ defs, d.key ≠ "" := by
  unfold Settings.table at h
  split at h <;> (try cases h) <;>
    simp [Settings.sFloat, Settings.sDouble, Settings.sBool, Settings.sInt, Settings.sEnum, Settings.sSeed, Settings.rateHT, Settings.rateDT, Settings.sDiff]

theorem ms_upper_chOf (c r : U32) (hc : c.val.isValidChar)
    (hr : r.val = if 97 ≤ c.val ∧ c.val ≤ 122 then c.val - 32 else c.val) :
    chOf r = (chOf c).toUpper ∧ r.val.isValidChar := by
  have hrv : r.val.isValidChar := by
    rw [hr]; split
    · simp only [Nat.isValidChar]; omega
    · exact hc
  refine ⟨?_, hrv⟩
  apply Char.toNat_inj.mp
  rw [chOf_toNat r hrv, toUpper_toNat, chOf_toNat c hc, hr]

theorem ms_to_mod_loop (a : Slice U32) (ha : ValidStr a) :
    ∀ (ts : alloc.vec.Vec U32) (i : Usize), i.val ≤ a.val.length → ts.val.length = i.val → VValid ts →
      ts.val.map chOf = ((strS a).take i.val).map Char.toUpper →
      ∃ u, beatmap.mod_settings.to_mod_loop a ts i = ok u ∧ VValid u ∧ u.val.map chOf = (strS a).map Char.toUpper := by
  intro ts i
  induction hk : a.val.length - i.val using Nat.strong_induction_on generalizing ts i with
  | _ k ih =>
    intro hle hts hvt hmap
    unfold beatmap.mod_settings.to_mod_loop
    rw [loop_unfold]
    by_cases hlt : i.val < a.val.length
    · have hl : i < Slice.len a := by show i.val < (Slice.len a).val; simpa using hlt
      have hc : (a.val[i.val]'hlt).val.isValidChar := ha _ (List.getElem_mem hlt)
      obtain ⟨r, hr, hrv⟩ := net.parse.ascii_upper_refines (a.val[i.val]'hlt)
      obtain ⟨hch, hrval⟩ := ms_upper_chOf _ r hc hrv
      obtain ⟨w, hw, hwv⟩ := push_eq ts r (by have := a.property; omega)
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := a.property; omega)
      have hb : beatmap.mod_settings.to_mod_loop.body a ts i = ok (.cont (w, i1)) := by
        simp [beatmap.mod_settings.to_mod_loop.body, hl, index_eq a i hlt, hr, hw, hi1]
      obtain ⟨u, hu, hu1, hu2⟩ := ih (a.val.length - i1.val) (by omega) w i1 rfl (by omega)
        (by rw [hwv]; simp [hts, hi1v]) (by intro x hx; rw [hwv] at hx; simp at hx; rcases hx with hx | hx; exact hvt x hx; subst hx; exact hrval)
        (by rw [hwv, hi1v, List.map_append, hmap]
            have : (strS a).take (i.val + 1) = (strS a).take i.val ++ [chOf (a.val[i.val]'hlt)] := by
              simp [strS, List.take_succ, List.getElem?_eq_getElem hlt]
            rw [this]; simp [hch])
      refine ⟨u, ?_, hu1, hu2⟩
      simp only [hb, bind_ok]; unfold beatmap.mod_settings.to_mod_loop at hu; exact hu
    · have hl : ¬ i < Slice.len a := by show ¬ i.val < (Slice.len a).val; simpa using hlt
      refine ⟨ts, by simp [beatmap.mod_settings.to_mod_loop.body, hl], hvt, ?_⟩
      rw [hmap, List.take_of_length_le (by simp [strS]; omega)]


/-- `APIMod.ToMod(ruleset)`; spec `Settings.toMod` (valid strings; JSON values as `parse` expects) -/
theorem beatmap.mod_settings.to_mod_refines (a : Slice U32) (ha : ValidStr a)
    (st : Slice (alloc.vec.Vec U32 × beatmap.mod_settings.JsonVal))
    (hv : ∀ p ∈ st.val, VValid p.1) (hj : ∀ p ∈ st.val, JOk' p.2) :
    ∃ r, beatmap.mod_settings.to_mod a st = ok r ∧ mcS r = Settings.toMod (String.ofList (strS a)) (msSetS st.val) := by
  obtain ⟨u, hu, hu1, hu2⟩ := ms_to_mod_loop a ha (alloc.vec.Vec.new U32) 0#usize (by simp) (by simp)
    (by intro x hx; simp at hx) (by simp)
  have hU : String.ofList (strS (alloc.vec.Vec.deref u)) = (String.ofList (strS a)).map Char.toUpper := by
    apply String.ext; simp only [String.toList_map, String.toList_ofList]
    simp only [strS, ms_deref_val] at hu2 ⊢; exact hu2
  obtain ⟨o, ho, hov⟩ := beatmap.mod_settings.table_refines (alloc.vec.Vec.deref u) (vvalid_deref u hu1)
  rw [hU] at hov
  unfold beatmap.mod_settings.to_mod
  simp only [hu, bind_ok, ho]
  cases o with
  | none =>
    obtain ⟨v, hv1, hvv⟩ := beatmap.mod_settings.copy_str_refines a
    refine ⟨{ acronym := v, known := false, settings := alloc.vec.Vec.new _ }, by simp only [hv1, bind_ok], ?_⟩
    unfold Settings.toMod
    simp only [Option.map_none] at hov
    simp only []
    rw [← hov]
    simp [mcS, vstrS, hvv, strS, valsS]
  | some defs =>
    simp only [Option.map_some] at hov
    have hd : DefsOk defs.val := by
      intro d hdm
      have := ms_table_keys _ _ hov.symm (sdS d) (List.mem_map_of_mem hdm)
      exact (keyName_ne_empty _).mp this
    obtain ⟨r, hr, -, hrv⟩ := beatmap.mod_settings.to_mod_known_refines u hu1 defs hd st hv hj
    refine ⟨r, hr, ?_⟩
    rw [hrv, ms_toMod_some _ _ _ hov.symm]
    congr 1
    apply String.ext; simp only [String.toList_map, String.toList_ofList, vstrS]
    simp only [strS, ms_deref_val] at hu2 ⊢; exact hu2

end OsuProofs
