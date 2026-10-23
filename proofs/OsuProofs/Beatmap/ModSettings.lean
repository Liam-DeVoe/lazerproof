/-
`beatmap::mod_settings` (`OsuModel/Beatmap/ModSettings.lean`), part 1: the representation of the
Rust types (setting keys are `beatmap::names` ids, enum tables are table ids, see `Beatmap/Names`),
value equality, lookups and the `ModConfig.get*` accessors.

Setting-key lookups compare ids in Rust and strings in the spec; they agree when every key id in the
list is a known id (`< 44`, `KeysOk`), which holds for every list built from `Settings.table`.
-/
import OsuProofs.Beatmap.Names
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

/-! ## Representation -/

/-- Rust string (`Vec<u32>` of scalar values) ↦ spec `String`. -/
def vstrS (s : alloc.vec.Vec U32) : String := String.ofList (s.val.map chOf)

def jvS : beatmap.mod_settings.JsonVal → JsonVal
  | .Long v => .long v.val
  | .Big => .big
  | .Double v => .double v
  | .Bool b => .bool b
  | .Str s => .str (vstrS s)
  | .Null => .null

/-- a JSON string value is a valid scalar-value string of reasonable length -/
def VValid (s : alloc.vec.Vec U32) : Prop := ∀ u ∈ s.val, u.val.isValidChar

def JOk : beatmap.mod_settings.JsonVal → Prop
  | .Str s => VValid s ∧ s.val.length < 2^62
  | _ => True

def styS : beatmap.mod_settings.SettingType → SettingType
  | .Bool b => .bool b
  | .Int a b => .int (i32S a) (i32S b)
  | .Double a b c => .double a b c
  | .Float a b c => .float a b c
  | .Enum t => .enum (enumTable t.val)
  | .NullableInt => .nullableInt
  | .Difficulty a b c d => .difficulty a b c d

def svS : beatmap.mod_settings.SettingValue → SettingValue
  | .Bool b => .bool b
  | .Int v => .int (i32S v)
  | .Double v => .double v
  | .Float v => .float v
  | .Enum v => .enum (i32S v)
  | .OptInt v => .optInt (v.map i32S)
  | .OptFloat v => .optFloat v

def sdS (d : beatmap.mod_settings.SettingDef) : SettingDef := ⟨keyName d.key.val, styS d.stype, svS d.default⟩

/-- the settings list (key id, value) ↦ (key, value) -/
def valsS (l : List (U32 × beatmap.mod_settings.SettingValue)) : List (String × SettingValue) :=
  l.map fun p => (keyName p.1.val, svS p.2)

def mcS (m : beatmap.mod_settings.ModConfig) : ModConfig :=
  { acronym := vstrS m.acronym, known := m.known, settings := (valsS m.settings.val).toArray }

/-- every key id of a settings list is a known id -/
def KeysOk (l : List (U32 × beatmap.mod_settings.SettingValue)) : Prop := ∀ p ∈ l, p.1.val < 44

@[simp] theorem ms_deref_val {α} (v : alloc.vec.Vec α) : (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref]

theorem i32S_inj (a b : I32) : i32S a = i32S b ↔ a = b := by
  constructor
  · intro h
    have := congrArg Int32.toBitVec h
    simp only [i32S] at this
    cases a; cases b; simp_all
  · intro h; rw [h]

/-! ## `setting_value_beq` (derived `BEq SettingValue`) -/

theorem sv_beq_int (x y : Int32) : (SettingValue.int x == SettingValue.int y) = (x == y) := rfl
theorem sv_beq_enum (x y : Int32) : (SettingValue.enum x == SettingValue.enum y) = (x == y) := rfl
theorem sv_beq_optInt (x y : Option Int32) : (SettingValue.optInt x == SettingValue.optInt y) = (x == y) := rfl

theorem sv_beq_optFloat (x y : Option F32) : (SettingValue.optFloat x == SettingValue.optFloat y) = (x == y) := rfl
theorem i32S_beq (x y : I32) : (i32S x == i32S y) = decide (x = y) := by
  rw [Bool.eq_iff_iff]; simp [i32S_inj]
theorem opt_beq_some {α} [BEq α] (a b : α) : (some a == some b) = (a == b) := rfl
theorem opt_beq_none_some {α} [BEq α] (b : α) : (none == some b) = false := rfl
theorem opt_beq_some_none {α} [BEq α] (a : α) : (some a == none) = false := rfl
theorem opt_beq_none {α} [BEq α] : ((none : Option α) == none) = true := rfl

theorem beatmap.mod_settings.setting_value_beq_refines (a b : beatmap.mod_settings.SettingValue) :
    beatmap.mod_settings.setting_value_beq a b = ok (svS a == svS b) := by
  cases a <;> cases b <;> simp [beatmap.mod_settings.setting_value_beq, svS, float.F64.eq, float.F32.eq]
  all_goals try rfl
  all_goals simp only [sv_beq_int, sv_beq_enum, sv_beq_optInt, sv_beq_optFloat, i32S_beq]
  all_goals rename_i x y; cases x <;> cases y <;> simp [opt_beq_some, opt_beq_none_some, opt_beq_some_none, i32S_beq]

/-! ## `bytes_eq` (helper, no spec def): byte-string equality -/

theorem take_succ_get {α} (l : List α) (k : Nat) (h : k < l.length) :
    l.take (k + 1) = l.take k ++ [l[k]'h] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]; rfl

theorem bytes_eq_loop_ok (a b : Slice U8) (hn : a.val.length = b.val.length) :
    ∀ (i : Usize) (acc : Bool), i.val ≤ a.val.length →
      acc = decide (a.val.take i.val = b.val.take i.val) →
      beatmap.mod_settings.bytes_eq_loop a b i acc = ok (decide (a.val = b.val)) := by
  intro i acc hi hacc
  unfold beatmap.mod_settings.bytes_eq_loop
  have := loop_ok (fun (x : Usize × Bool) => beatmap.mod_settings.bytes_eq_loop.body a b x.1 x.2)
    (fun (x : Usize × Bool) => a.val.length - x.1.val)
    (fun (x : Usize × Bool) => x.1.val ≤ a.val.length ∧ x.2 = decide (a.val.take x.1.val = b.val.take x.1.val))
    (fun (r : Bool) => r = decide (a.val = b.val))
    (by
      rintro ⟨k, c⟩ ⟨hk, hc⟩
      dsimp only at hk hc ⊢
      by_cases hlt : k.val < a.val.length
      · right
        have hlt' : k < Slice.len a := by show k.val < (Slice.len a).val; simpa using hlt
        have hkb : k.val < b.val.length := by omega
        obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := a.property; omega)
        refine ⟨(k1, c && decide (a.val[k.val]'hlt = b.val[k.val]'hkb)), ?_, ⟨by dsimp only; omega, ?_⟩,
          by dsimp only; omega⟩
        · simp only [beatmap.mod_settings.bytes_eq_loop.body, hlt', ite_true, index_eq a k hlt, index_eq b k hkb,
            bind_ok, hk1]
          congr 2
          cases c <;> by_cases hc' : a.val[k.val]'hlt = b.val[k.val]'hkb <;> simp [hc']
        · dsimp only
          rw [hc, hk1v, take_succ_get a.val k.val hlt, take_succ_get b.val k.val hkb]
          by_cases hall : a.val.take k.val = b.val.take k.val
          · rw [hall, decide_eq_true rfl, Bool.true_and]
            exact decide_eq_decide.mpr ⟨fun h => by rw [h], fun h => by
              have := List.append_cancel_left h; simpa using this⟩
          · have : ¬ (a.val.take k.val ++ [a.val[k.val]'hlt] = b.val.take k.val ++ [b.val[k.val]'hkb]) := by
              intro h; apply hall
              exact (List.append_inj h (by simp; omega)).1
            rw [decide_eq_false hall, Bool.false_and, decide_eq_false this]
      · left
        have hlt' : ¬ k < Slice.len a := by show ¬ k.val < (Slice.len a).val; simpa using hlt
        refine ⟨c, by simp [beatmap.mod_settings.bytes_eq_loop.body, hlt'], ?_⟩
        have : k.val = a.val.length := by omega
        rw [hc, this, List.take_length, hn, List.take_length])
    (i, acc) ⟨hi, hacc⟩
  obtain ⟨y, hy, rfl⟩ := this
  exact hy

theorem beatmap.mod_settings.bytes_eq_refines (a b : Slice U8) :
    beatmap.mod_settings.bytes_eq a b = ok (decide (a.val = b.val)) := by
  unfold beatmap.mod_settings.bytes_eq
  dsimp only
  by_cases hl : a.val.length = b.val.length
  · have hl' : (Slice.len a != Slice.len b) = false := by
      rw [bne_eq_false_iff_eq]; apply UScalar.eq_of_val_eq; simp [hl]
    rw [hl']; simp only [Bool.false_eq_true, ite_false]
    exact bytes_eq_loop_ok a b hl 0#usize true (by simp) (by simp)
  · have hl' : (Slice.len a != Slice.len b) = true := by
      rw [bne_iff_ne, ne_eq]; intro h; apply hl; have := congrArg UScalar.val h; simpa using this
    rw [hl']; simp only [ite_true]
    congr 1; symm; simp only [decide_eq_false_iff_not]
    intro h; apply hl; rw [h]

/-! ## settings-list lookup -/

/-- first entry with key id `key` (Rust id comparison) -/
def valsFind (l : List (U32 × beatmap.mod_settings.SettingValue)) (key : U32) :
    Option beatmap.mod_settings.SettingValue :=
  (l.find? (fun p => decide (p.1 = key))).map (·.2)

theorem valsFind_drop (l : List (U32 × beatmap.mod_settings.SettingValue)) (key : U32) (i : Nat)
    (h : i < l.length) :
    ((l.drop i).find? (fun p => decide (p.1 = key))).map (·.2) =
      if (l[i]'h).1 = key then some (l[i]'h).2
      else ((l.drop (i+1)).find? (fun p => decide (p.1 = key))).map (·.2) := by
  rw [List.drop_eq_getElem_cons h, List.find?_cons]
  by_cases hk : (l[i]'h).1 = key <;> simp [hk]

theorem vals_get_loop_ok (l : Slice (U32 × beatmap.mod_settings.SettingValue)) (key : U32) :
    ∀ (i : Usize), i.val ≤ l.val.length →
      beatmap.mod_settings.vals_get_loop l key i none =
        ok (((l.val.drop i.val).find? (fun p => decide (p.1 = key))).map (·.2)) := by
  intro i hi
  unfold beatmap.mod_settings.vals_get_loop
  have := loop_ok (fun (x : Usize × Option beatmap.mod_settings.SettingValue) =>
      beatmap.mod_settings.vals_get_loop.body l key x.1 x.2)
    (fun x => l.val.length + 1 - x.1.val - (if x.2.isSome then 1 else 0))
    (fun x => x.1.val ≤ l.val.length ∧
      (x.2 = none → ((l.val.drop x.1.val).find? (fun p => decide (p.1 = key))).map (·.2) =
        ((l.val.drop i.val).find? (fun p => decide (p.1 = key))).map (·.2)) ∧
      (x.2.isSome → x.2 = ((l.val.drop i.val).find? (fun p => decide (p.1 = key))).map (·.2)))
    (fun r => r = ((l.val.drop i.val).find? (fun p => decide (p.1 = key))).map (·.2))
    (by
      rintro ⟨k, r⟩ ⟨hk, hn, hs⟩
      dsimp only at hk hn hs ⊢
      cases r with
      | some v =>
        left; exact ⟨some v, by simp [beatmap.mod_settings.vals_get_loop.body, core.option.Option.is_none],
          hs rfl⟩
      | none =>
        by_cases hlt : k.val < l.val.length
        · right
          have hlt' : k < Slice.len l := by show k.val < (Slice.len l).val; simpa using hlt
          obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := l.property; omega)
          have hd := valsFind_drop l.val key k.val hlt
          have hn' := hn rfl
          have hidx := index_eq l k hlt
          generalize l.val[k.val]'hlt = p at hd hidx ⊢
          obtain ⟨kk, vv⟩ := p
          by_cases hkey : kk = key
          · refine ⟨(k1, some vv), ?_, ⟨by dsimp only; omega, by simp, ?_⟩, by simp; omega⟩
            · simp [beatmap.mod_settings.vals_get_loop.body, core.option.Option.is_none, hlt',
                hidx, hk1, hkey]
            · intro _; rw [← hn', hd]; simp [hkey]
          · refine ⟨(k1, none), ?_, ⟨by dsimp only; omega, ?_, by simp⟩, by simp; omega⟩
            · simp [beatmap.mod_settings.vals_get_loop.body, core.option.Option.is_none, hlt',
                hidx, hk1, hkey]
            · intro _; rw [← hn', hd, hk1v]; simp [hkey]
        · left
          have hlt' : ¬ k < Slice.len l := by show ¬ k.val < (Slice.len l).val; simpa using hlt
          refine ⟨none, by simp [beatmap.mod_settings.vals_get_loop.body, core.option.Option.is_none, hlt'], ?_⟩
          rw [← hn rfl, show k.val = l.val.length by omega, List.drop_length]; rfl)
    (i, none) ⟨hi, fun _ => rfl, by simp⟩
  obtain ⟨y, hy, rfl⟩ := this
  exact hy

theorem beatmap.mod_settings.vals_get_refines (l : Slice (U32 × beatmap.mod_settings.SettingValue)) (key : U32) :
    beatmap.mod_settings.vals_get l key = ok (valsFind l.val key) := by
  unfold beatmap.mod_settings.vals_get
  rw [vals_get_loop_ok l key 0#usize (by simp)]; rfl

theorem valsS_find (l : List (U32 × beatmap.mod_settings.SettingValue)) (hk : KeysOk l) (key : U32) :
    ((valsS l).find? (fun p => p.1 == keyName key.val)).map (·.2) = (valsFind l key).map svS := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have hp : p.1.val < 44 := hk p (by simp)
    have hl : KeysOk l := fun q hq => hk q (by simp [hq])
    have e : (keyName p.1.val == keyName key.val) = decide (p.1 = key) := by
      by_cases hkey : key.val < 44
      · rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, decide_eq_true_eq, keyName_inj _ _ hp hkey]
        exact ⟨fun h => UScalar.eq_of_val_eq h, fun h => h ▸ rfl⟩
      · have h1 : keyName key.val = "" := by
          by_contra h; exact hkey ((keyName_ne_empty _).mp h)
        have h2 : keyName p.1.val ≠ "" := (keyName_ne_empty _).mpr hp
        have h3 : p.1 ≠ key := by intro h; rw [h] at hp; exact hkey hp
        simp [h1, h2, h3]
    simp only [valsS, valsFind, List.map_cons, List.find?_cons] at ih ⊢
    rw [e]
    by_cases hpk : p.1 = key
    · simp [hpk]
    · simp only [hpk, decide_false]; exact ih hl

theorem beatmap.mod_settings.mc_get_refines (m : beatmap.mod_settings.ModConfig) (key : U32) :
    beatmap.mod_settings.mc_get m key = ok (valsFind m.settings.val key) := by
  unfold beatmap.mod_settings.mc_get
  dsimp only; rw [beatmap.mod_settings.vals_get_refines, ms_deref_val]

theorem mcS_get (m : beatmap.mod_settings.ModConfig) (hk : KeysOk m.settings.val) (key : U32) :
    (mcS m).get? (keyName key.val) = (valsFind m.settings.val key).map svS := by
  rw [← valsS_find _ hk key]
  simp only [ModConfig.get?, mcS, List.find?_toArray]

theorem f64_from_bits_zero : float.F64.from_bits 0#u64 = ok (0 : F64) := by
  simp [float.F64.from_bits] <;> decide
theorem f32_from_bits_zero : float.F32.from_bits 0#u32 = ok (0 : F32) := by
  simp [float.F32.from_bits] <;> decide

theorem beatmap.mod_settings.get_bool_refines (m : beatmap.mod_settings.ModConfig) (hk : KeysOk m.settings.val)
    (key : U32) : beatmap.mod_settings.get_bool m key = ok ((mcS m).getBool (keyName key.val)) := by
  unfold beatmap.mod_settings.get_bool ModConfig.getBool
  rw [beatmap.mod_settings.mc_get_refines, bind_ok, mcS_get m hk]
  cases valsFind m.settings.val key with
  | none => rfl
  | some v => cases v <;> rfl

theorem beatmap.mod_settings.get_int_refines (m : beatmap.mod_settings.ModConfig) (hk : KeysOk m.settings.val)
    (key : U32) : ∃ r, beatmap.mod_settings.get_int m key = ok r ∧ i32S r = (mcS m).getInt (keyName key.val) := by
  unfold beatmap.mod_settings.get_int ModConfig.getInt
  rw [beatmap.mod_settings.mc_get_refines, bind_ok, mcS_get m hk]
  cases valsFind m.settings.val key with
  | none => exact ⟨_, rfl, rfl⟩
  | some v => cases v <;> exact ⟨_, rfl, rfl⟩

theorem beatmap.mod_settings.get_double_refines (m : beatmap.mod_settings.ModConfig) (hk : KeysOk m.settings.val)
    (key : U32) : beatmap.mod_settings.get_double m key = ok ((mcS m).getDouble (keyName key.val)) := by
  unfold beatmap.mod_settings.get_double ModConfig.getDouble
  rw [beatmap.mod_settings.mc_get_refines, bind_ok, mcS_get m hk]
  cases valsFind m.settings.val key with
  | none => exact f64_from_bits_zero
  | some v => cases v <;> first | exact f64_from_bits_zero | rfl

theorem beatmap.mod_settings.get_float_refines (m : beatmap.mod_settings.ModConfig) (hk : KeysOk m.settings.val)
    (key : U32) : beatmap.mod_settings.get_float m key = ok ((mcS m).getFloat (keyName key.val)) := by
  unfold beatmap.mod_settings.get_float ModConfig.getFloat
  rw [beatmap.mod_settings.mc_get_refines, bind_ok, mcS_get m hk]
  cases valsFind m.settings.val key with
  | none => exact f32_from_bits_zero
  | some v => cases v <;> first | exact f32_from_bits_zero | rfl

theorem beatmap.mod_settings.get_opt_int_refines (m : beatmap.mod_settings.ModConfig) (hk : KeysOk m.settings.val)
    (key : U32) : ∃ r, beatmap.mod_settings.get_opt_int m key = ok r ∧
      r.map i32S = (mcS m).getOptInt (keyName key.val) := by
  unfold beatmap.mod_settings.get_opt_int ModConfig.getOptInt
  rw [beatmap.mod_settings.mc_get_refines, bind_ok, mcS_get m hk]
  cases valsFind m.settings.val key with
  | none => exact ⟨_, rfl, rfl⟩
  | some v => cases v <;> exact ⟨_, rfl, rfl⟩

theorem beatmap.mod_settings.get_opt_float_refines (m : beatmap.mod_settings.ModConfig) (hk : KeysOk m.settings.val)
    (key : U32) : beatmap.mod_settings.get_opt_float m key = ok ((mcS m).getOptFloat (keyName key.val)) := by
  unfold beatmap.mod_settings.get_opt_float ModConfig.getOptFloat
  rw [beatmap.mod_settings.mc_get_refines, bind_ok, mcS_get m hk]
  cases valsFind m.settings.val key with
  | none => rfl
  | some v => cases v <;> rfl

end OsuProofs
