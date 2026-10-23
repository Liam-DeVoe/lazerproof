/-
`eval::mods_json` settings + mod-list layer (json agent, D46): `to_setting`, `key_is_at`, `first_match`,
`find_first`, `find_last`, `acronym_str`, `settings_of`, `settings_obj`, `parse_mod`, `parse_mod_list` and the
top-level `parse_mods` (refines `SimJson.parseMods`).

Statements: `to_setting` = `SimJson.toSetting ∘ ev_vS` (`jvS`), with `JOk` of the result; `find_first` = `List.findIdx?`
of the key test (`js_keyP`; spec `kvs.find? (·.1 == key)` via `js_find_some`/`js_find_none`); `find_last` = `js_lastIdx`
(the last index; spec `kvs.reverse.find?` via `js_lastIdx_mem`/`js_lastIdx_none`, used by eval.osr). `parse_mod` is
stated against `js_modSpec` = the `mapM` function of `parseMods` (bridge `js_parseMods_eq`, by `rfl`), result
relation `js_mRel` (config + `js_mcOk` = the eval agent's `ev_mcOk`, or the same message `js_mjeS`).
`parse_mods`: hypotheses 64-bit (`JOk'` of string settings), valid scalar values, `len + 8 ≤ usize::MAX`, `len < 2^62`.
`js_to_mod_ok` is a copy of the eval agent's `ev_to_mod_ok` (Eval/Osr.lean) so this file does not import Osr.
-/
import OsuProofs.Eval.JsonNum
import OsuProofs.Beatmap.ModSettings9
import OsuProofs.Beatmap.ControlPoints
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl
theorem js_range_sat (neg : Bool) (N : Nat) :
    (decide (-(2^63 : Int) ≤ (if neg then -((min N (2^64) : Nat) : Int) else ((min N (2^64) : Nat) : Int))) &&
      decide ((if neg then -((min N (2^64) : Nat) : Int) else ((min N (2^64) : Nat) : Int)) ≤ 2^63 - 1)) =
    (decide (-9223372036854775808 ≤ (if neg then -(N : Int) else (N : Int))) &&
      decide ((if neg then -(N : Int) else (N : Int)) ≤ 9223372036854775807)) := by
  by_cases h : N ≤ 2^64
  · rw [Nat.min_eq_left h]; cases neg <;> simp <;> omega
  · rw [Nat.min_eq_right (by omega)]; cases neg <;> simp <;> omega

theorem js_vstrS_deref (t : alloc.vec.Vec U32) : vstrS t = String.ofList (strS (alloc.vec.Vec.deref t)) := by
  simp [vstrS, strS]

theorem eval.mods_json.to_setting_refines (v : eval.mods_json.V) (hv : ev_vOk v) :
    ∃ r, eval.mods_json.to_setting v = ok r ∧ jvS r = SimJson.toSetting (ev_vS v) ∧ JOk r := by
  cases v with
  | Num t =>
    have ht : ev_VV t := hv
    have hs : ValidStr (alloc.vec.Vec.deref t) := fun u hu => ht.1 u (by simpa using hu)
    have hl : (alloc.vec.Vec.deref t).val.length < 2^62 := by simpa using ht.2
    simp only [ev_vS_num, SimJson.toSetting, js_vstrS_deref]
    unfold eval.mods_json.to_setting
    simp only [eval.mods_json.has_frac_or_exp_refines, bind_ok]
    split
    · rename_i hb
      rw [net.parse.double_parse_refines _ hs hl, bind_ok]
      simp only [hb, if_true, OsuModel.Net.doubleParse, String.toList_ofList]
      cases OsuModel.Net.doubleParseChars (strS (alloc.vec.Vec.deref t)) with
      | ok d => exact ⟨_, rfl, rfl, by simp [JOk]⟩
      | error e => exact ⟨_, rfl, rfl, by simp [JOk]⟩
    · rename_i hb
      obtain ⟨neg, m, hm, hneg, hmv⟩ := eval.mods_json.int_of_text_refines _ hs
      simp only [hm, bind_ok, eval.mods_json.in_range_refines, js_lo_mag, js_hi]
      subst hneg
      generalize hA : ((String.ofList (strS (alloc.vec.Vec.deref t))).drop 1).toNat! = A at hmv ⊢
      generalize hB : (String.ofList (strS (alloc.vec.Vec.deref t))).toNat! = B at hmv ⊢
      cases hsw : (String.ofList (strS (alloc.vec.Vec.deref t))).startsWith "-" with
      | true =>
        rw [hsw] at hmv
        simp only [↓reduceIte] at hmv ⊢
        by_cases hr : -(9223372036854775808:Int) ≤ -(A:Int) ∧ -(A:Int) ≤ 9223372036854775807
        · obtain ⟨x, hx, hxv⟩ := eval.mods_json.long_of_refines true m (by simp; omega)
          refine ⟨.Long x, ?_, ?_, by simp [JOk]⟩
          · simp [hx, hmv]; omega
          · rw [if_pos (by simp; omega)]; simp [jvS, hxv]; omega
        · refine ⟨.Big, ?_, ?_, by simp [JOk]⟩
          · simp [hmv]; omega
          · rw [if_neg (by simp; omega)]; rfl
      | false =>
        rw [hsw] at hmv
        simp only [Bool.false_eq_true, ↓reduceIte] at hmv ⊢
        by_cases hr : -(9223372036854775808:Int) ≤ (B:Int) ∧ (B:Int) ≤ 9223372036854775807
        · obtain ⟨x, hx, hxv⟩ := eval.mods_json.long_of_refines false m (by simp; omega)
          refine ⟨.Long x, ?_, ?_, by simp [JOk]⟩
          · simp [hx, hmv]; omega
          · rw [if_pos (by simp; omega)]; simp [jvS, hxv]; omega
        · refine ⟨.Big, ?_, ?_, by simp [JOk]⟩
          · simp [hmv]; omega
          · rw [if_neg (by simp; omega)]; rfl
  | VStr t =>
    refine ⟨.Str t, by simp [eval.mods_json.to_setting, clone_vec_u32], rfl, ?_⟩
    have ht : ev_VV t := hv
    exact ⟨ht.1, ht.2⟩
  | Bool b => exact ⟨_, rfl, rfl, by simp [JOk]⟩
  | Null => exact ⟨_, rfl, rfl, by simp [JOk]⟩
  | Arr xs => exact ⟨_, rfl, by obtain ⟨⟨n, l, h⟩⟩ := xs; rfl, by simp [JOk]⟩
  | Obj xs => exact ⟨_, rfl, by obtain ⟨⟨n, l, h⟩⟩ := xs; rfl, by simp [JOk]⟩
end OsuProofs

namespace OsuProofs
open OsuImpl
/-- key test of `kvs.find? (·.1 == key)` on a Rust member -/
def js_keyP (key : Slice U8) (kv : alloc.vec.Vec U32 × eval.mods_json.V) : Bool := vstrS kv.1 == String.ofList (litS key)

theorem js_vstrS_eq_iff (v : alloc.vec.Vec U32) (L : List Char) :
    vstrS v = String.ofList L ↔ strS (alloc.vec.Vec.deref v) = L := by
  unfold vstrS strS; simp only [ms_deref_val]
  constructor
  · intro h; have := congrArg String.toList h; simpa using this
  · intro h; rw [h]

theorem eval.mods_json.key_is_at_refines (kvs : Slice (alloc.vec.Vec U32 × eval.mods_json.V)) (i : Usize)
    (key : Slice U8) (hi : i.val < kvs.val.length) (hk : VValid (kvs.val[i.val]'hi).1) :
    eval.mods_json.key_is_at kvs i key = ok (js_keyP key (kvs.val[i.val]'hi)) := by
  unfold eval.mods_json.key_is_at
  rw [slice_index_ok kvs i hi]
  simp only [bind_ok]
  generalize kvs.val[i.val]'hi = kv at hk ⊢
  obtain ⟨k, v⟩ := kv
  show beatmap.dotnet.str_eq (alloc.vec.Vec.deref k) key = _
  rw [beatmap.dotnet.str_eq_refines _ (vvalid_deref _ hk)]
  congr 1
  unfold js_keyP
  rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq, js_vstrS_eq_iff]

theorem eval.mods_json.first_match_refines (m : Bool) (i : Usize) :
    eval.mods_json.first_match m i = ok (if m then some i else none) := by
  unfold eval.mods_json.first_match; cases m <;> rfl

def js_kOk (kvs : List (alloc.vec.Vec U32 × eval.mods_json.V)) : Prop := ∀ kv ∈ kvs, VValid kv.1

/-- `find_first` = the index of the first member whose key is `key` (`List.findIdx?`; spec `kvs.find? (·.1 == key)`) -/
theorem eval.mods_json.find_first_refines (kvs : Slice (alloc.vec.Vec U32 × eval.mods_json.V)) (key : Slice U8)
    (hk : js_kOk kvs.val) :
    ∃ r, eval.mods_json.find_first kvs key = ok r ∧ r.map (·.val) = kvs.val.findIdx? (js_keyP key) := by
  have hmax : kvs.val.length ≤ Usize.max := Slice.length_ineq kvs
  have H := loop_ok (fun (x : Option Usize × Usize) => eval.mods_json.find_first_loop.body kvs key x.1 x.2)
    (fun x => kvs.val.length + 1 - x.2.val - (if x.1.isSome then 1 else 0))
    (fun x => x.2.val ≤ kvs.val.length ∧
      ((x.1 = none ∧ kvs.val.findIdx? (js_keyP key) = ((kvs.val.drop x.2.val).findIdx? (js_keyP key)).map (· + x.2.val)) ∨
       (∃ j : Usize, x.1 = some j ∧ kvs.val.findIdx? (js_keyP key) = some j.val)))
    (fun y => y.map (·.val) = kvs.val.findIdx? (js_keyP key)) ?_ (none, 0#usize) ⟨by simp, Or.inl ⟨rfl, by simp⟩⟩
  · obtain ⟨y, hy, hq⟩ := H
    refine ⟨y, ?_, hq⟩
    unfold eval.mods_json.find_first eval.mods_json.find_first_loop
    rw [show (fun (x : Option Usize × Usize) => match x with
        | (r1, i1) => eval.mods_json.find_first_loop.body kvs key r1 i1) =
        (fun (x : Option Usize × Usize) => eval.mods_json.find_first_loop.body kvs key x.1 x.2) from rfl, hy]
  · rintro ⟨r, i⟩ ⟨h1, h2⟩
    simp only at h1 h2 ⊢
    rcases h2 with ⟨rfl, h2⟩ | ⟨j, rfl, h2⟩
    · by_cases hlt : i.val < kvs.val.length
      · right
        have hlt' : i < Slice.len kvs := (slice_lt_len_iff i kvs).mpr hlt
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
        have hka := eval.mods_json.key_is_at_refines kvs i key hlt (hk _ (List.getElem_mem hlt))
        rw [List.drop_eq_getElem_cons hlt, List.findIdx?_cons] at h2
        cases hp : js_keyP key (kvs.val[i.val]'hlt) with
        | true =>
          refine ⟨(some i, i1), by simp [eval.mods_json.find_first_loop.body, hlt', hka, hp,
            eval.mods_json.first_match_refines, hi1], ⟨by dsimp only; omega, Or.inr ⟨i, rfl, ?_⟩⟩, by simp; omega⟩
          rw [h2, hp]; simp
        | false =>
          refine ⟨(none, i1), by simp [eval.mods_json.find_first_loop.body, hlt', hka, hp,
            eval.mods_json.first_match_refines, hi1], ⟨by dsimp only; omega, Or.inl ⟨rfl, ?_⟩⟩, by simp; omega⟩
          rw [h2, hp]; simp only [Bool.false_eq_true, ↓reduceIte, Option.map_map, hi1v]
          congr 1; funext k; simp; omega
      · left
        have hlt' : ¬ i < Slice.len kvs := by rw [slice_lt_len_iff]; exact hlt
        refine ⟨none, by simp [eval.mods_json.find_first_loop.body, hlt'], ?_⟩
        rw [h2, List.drop_eq_nil_of_le (by omega)]; simp
    · left
      exact ⟨some j, by simp [eval.mods_json.find_first_loop.body], by simp [h2]⟩

/-- the index of the last member satisfying `p` (spec `kvs.reverse.find? p`) -/
def js_lastIdx {α} (p : α → Bool) (L : List α) : Option Nat := (L.reverse.findIdx? p).map (fun k => L.length - 1 - k)

theorem js_lastIdx_snoc {α} (p : α → Bool) (L : List α) (x : α) :
    js_lastIdx p (L ++ [x]) = if p x then some L.length else js_lastIdx p L := by
  unfold js_lastIdx
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append, List.findIdx?_cons]
  cases p x with
  | true => simp
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Option.map_map, List.length_append, List.length_singleton]
    congr 1; funext k; simp only [Function.comp]; omega

theorem js_lastIdx_mem {α} (p : α → Bool) (L : List α) (j : Nat) (h : js_lastIdx p L = some j) :
    ∃ hj : j < L.length, p (L[j]'hj) = true ∧ (L.reverse.find? p) = some (L[j]'hj) := by
  unfold js_lastIdx at h
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
  have hk' := List.findIdx?_eq_some_iff_getElem.mp hk
  obtain ⟨hkl, hpk, hbefore⟩ := hk'
  simp only [List.length_reverse] at hkl
  refine ⟨by omega, ?_, ?_⟩
  · rw [List.getElem_reverse] at hpk; convert hpk using 3
  · rw [List.find?_eq_some_iff_getElem]
    refine ⟨?_, ⟨k, hkl.trans_eq (by simp), ?_, ?_⟩⟩
    · rw [List.getElem_reverse] at hpk; convert hpk using 3
    · rw [List.getElem_reverse]
    · intro j' hj'; have := hbefore j' hj'; simpa using this

theorem js_lastIdx_none {α} (p : α → Bool) (L : List α) (h : js_lastIdx p L = none) : L.reverse.find? p = none := by
  unfold js_lastIdx at h
  simp only [Option.map_eq_none_iff, List.findIdx?_eq_none_iff] at h
  simp only [List.find?_eq_none]; intro x hx; simpa using h x hx

/-- `find_last` = the index of the last member whose key is `key` (`js_lastIdx`; spec `kvs.reverse.find? (·.1 == key)`) -/
theorem eval.mods_json.find_last_refines (kvs : Slice (alloc.vec.Vec U32 × eval.mods_json.V)) (key : Slice U8)
    (hk : js_kOk kvs.val) :
    ∃ r, eval.mods_json.find_last kvs key = ok r ∧ r.map (·.val) = js_lastIdx (js_keyP key) kvs.val := by
  have H := loop_ok (fun (x : Option Usize × Usize) => eval.mods_json.find_last_loop.body kvs key x.1 x.2)
    (fun x => x.2.val + (if x.1.isSome then 0 else 1))
    (fun x => x.2.val ≤ kvs.val.length ∧
      ((x.1 = none ∧ js_lastIdx (js_keyP key) kvs.val = js_lastIdx (js_keyP key) (kvs.val.take x.2.val)) ∨
       (∃ j : Usize, x.1 = some j ∧ js_lastIdx (js_keyP key) kvs.val = some j.val)))
    (fun y => y.map (·.val) = js_lastIdx (js_keyP key) kvs.val) ?_ (none, Slice.len kvs)
    ⟨by simp, Or.inl ⟨rfl, by simp⟩⟩
  · obtain ⟨y, hy, hq⟩ := H
    refine ⟨y, ?_, hq⟩
    unfold eval.mods_json.find_last eval.mods_json.find_last_loop
    rw [show (fun (x : Option Usize × Usize) => match x with
        | (r1, i1) => eval.mods_json.find_last_loop.body kvs key r1 i1) =
        (fun (x : Option Usize × Usize) => eval.mods_json.find_last_loop.body kvs key x.1 x.2) from rfl, hy]
  · rintro ⟨r, i⟩ ⟨h1, h2⟩
    simp only at h1 h2 ⊢
    rcases h2 with ⟨rfl, h2⟩ | ⟨j, rfl, h2⟩
    · by_cases hz : 0 < i.val
      · right
        have hz' : i > 0#usize := by show (0#usize).val < i.val; simpa using hz
        obtain ⟨i1, hi1, hi1v, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := i) (y := 1#usize) (by simp; omega))
        simp at hi1v
        have hlt : i1.val < kvs.val.length := by omega
        have hka := eval.mods_json.key_is_at_refines kvs i1 key hlt (hk _ (List.getElem_mem hlt))
        have htake : kvs.val.take i.val = kvs.val.take i1.val ++ [kvs.val[i1.val]'hlt] := by
          rw [show i.val = i1.val + 1 by omega, List.take_succ_eq_append_getElem hlt]
        rw [htake, js_lastIdx_snoc] at h2
        cases hp : js_keyP key (kvs.val[i1.val]'hlt) with
        | true =>
          refine ⟨(some i1, i1), by simp [eval.mods_json.find_last_loop.body, hz', hi1, hka, hp,
            eval.mods_json.first_match_refines], ⟨by dsimp only; omega, Or.inr ⟨i1, rfl, ?_⟩⟩, by simp; omega⟩
          rw [h2, hp]; simp; omega
        | false =>
          refine ⟨(none, i1), by simp [eval.mods_json.find_last_loop.body, hz', hi1, hka, hp,
            eval.mods_json.first_match_refines], ⟨by dsimp only; omega, Or.inl ⟨rfl, ?_⟩⟩, by simp; omega⟩
          rw [h2, hp]; rfl
      · left
        have hz' : ¬ i > 0#usize := by show ¬ (0#usize).val < i.val; simpa using hz
        refine ⟨none, by simp [eval.mods_json.find_last_loop.body, hz'], ?_⟩
        rw [h2, show i.val = 0 by omega]; rfl
    · left
      exact ⟨some j, by simp [eval.mods_json.find_last_loop.body], by simp [h2]⟩
end OsuProofs

namespace OsuProofs
open OsuImpl
theorem eval.mods_json.acronym_str_refines (v : eval.mods_json.V) (hv : ev_vOk v) :
    ∃ r, eval.mods_json.acronym_str v = ok r ∧
      vstrS r = (match ev_vS v with | .str a => a | _ => "") ∧ VValid r ∧ r.val.length < 2^62 := by
  cases v with
  | VStr a =>
    have ha : ev_VV a := hv
    exact ⟨a, by simp [eval.mods_json.acronym_str, clone_vec_u32], rfl, ha.1, ha.2⟩
  | Num t => exact ⟨_, rfl, by simp [vstrS], by simp [VValid], by simp⟩
  | Bool b => exact ⟨_, rfl, by simp [vstrS], by simp [VValid], by simp⟩
  | Null => exact ⟨_, rfl, by simp [vstrS], by simp [VValid], by simp⟩
  | Arr xs => exact ⟨_, rfl, by obtain ⟨⟨n, l, h⟩⟩ := xs; simp [vstrS, ev_vS], by simp [VValid], by simp⟩
  | Obj xs => exact ⟨_, rfl, by obtain ⟨⟨n, l, h⟩⟩ := xs; simp [vstrS, ev_vS], by simp [VValid], by simp⟩

/-- `settings_of` = `ss.map fun (k, v) => (k, toSetting v)` -/
theorem eval.mods_json.settings_of_refines (ss : Slice (alloc.vec.Vec U32 × eval.mods_json.V))
    (hok : ∀ kv ∈ ss.val, ev_VV kv.1 ∧ ev_vOk kv.2) :
    ∃ r, eval.mods_json.settings_of ss = ok r ∧
      msSetS r.val = ss.val.map (fun kv => (vstrS kv.1, SimJson.toSetting (ev_vS kv.2))) ∧
      ∀ p ∈ r.val, VValid p.1 ∧ p.1.val.length < 2^62 ∧ JOk p.2 := by
  have hmax : ss.val.length ≤ Usize.max := Slice.length_ineq ss
  have H := loop_ok (fun (x : alloc.vec.Vec (alloc.vec.Vec U32 × beatmap.mod_settings.JsonVal) × Usize) =>
      eval.mods_json.settings_of_loop.body ss x.1 x.2)
    (fun x => ss.val.length - x.2.val)
    (fun x => x.2.val ≤ ss.val.length ∧ x.1.val.length = x.2.val ∧
      msSetS x.1.val = (ss.val.take x.2.val).map (fun kv => (vstrS kv.1, SimJson.toSetting (ev_vS kv.2))) ∧
      ∀ p ∈ x.1.val, VValid p.1 ∧ p.1.val.length < 2^62 ∧ JOk p.2)
    (fun y => msSetS y.val = ss.val.map (fun kv => (vstrS kv.1, SimJson.toSetting (ev_vS kv.2))) ∧
      ∀ p ∈ y.val, VValid p.1 ∧ p.1.val.length < 2^62 ∧ JOk p.2) ?_ (alloc.vec.Vec.new _, 0#usize)
    ⟨by simp, by simp, by simp [msSetS], by simp⟩
  · obtain ⟨y, hy, hq⟩ := H
    refine ⟨y, ?_, hq⟩
    unfold eval.mods_json.settings_of eval.mods_json.settings_of_loop
    rw [show (fun (x : alloc.vec.Vec (alloc.vec.Vec U32 × beatmap.mod_settings.JsonVal) × Usize) => match x with
        | (out1, i1) => eval.mods_json.settings_of_loop.body ss out1 i1) =
        (fun x => eval.mods_json.settings_of_loop.body ss x.1 x.2) from rfl, hy]
  · rintro ⟨out, i⟩ ⟨h1, h2, h3, h4⟩
    simp only at h1 h2 h3 h4 ⊢
    by_cases hlt : i.val < ss.val.length
    · right
      have hlt' : i < Slice.len ss := (slice_lt_len_iff i ss).mpr hlt
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
      have hkv := hok _ (List.getElem_mem hlt)
      have htake : ss.val.take (i.val + 1) = ss.val.take i.val ++ [ss.val[i.val]'hlt] :=
        List.take_succ_eq_append_getElem hlt
      generalize hx : ss.val[i.val]'hlt = kv at hkv htake
      obtain ⟨k, v⟩ := kv
      obtain ⟨jv, hjv, hjvs, hjok⟩ := eval.mods_json.to_setting_refines v hkv.2
      have hout : out.val.length < Usize.max := by omega
      refine ⟨(vpush out (k, jv) hout, i1), ?_, ⟨by dsimp only; omega, ?_, ?_, ?_⟩, by dsimp only; omega⟩
      · simp only [eval.mods_json.settings_of_loop.body, hlt', if_true, slice_index_ok ss i hlt, hx, bind_ok]
        show (do
          let v2 ← alloc.vec.CloneVec.clone core.clone.CloneU32 k
          let jv ← eval.mods_json.to_setting v
          let out1 ← alloc.vec.Vec.push out (v2, jv)
          let i2 ← i + 1#usize
          ok (ControlFlow.cont (out1, i2))) = _
        simp [clone_vec_u32, hjv, vec_push_ok out _ hout, hi1]
      · simp [vpush_val]; omega
      · simp only [vpush_val, hi1v, htake, msSetS, List.map_append, ← h3]
        simp [msSetS, hjvs]
      · intro p hp
        simp only [vpush_val, List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact h4 p hp
        · exact ⟨hkv.1.1, hkv.1.2, hjok⟩
    · left
      have hlt' : ¬ i < Slice.len ss := by rw [slice_lt_len_iff]; exact hlt
      refine ⟨out, by simp [eval.mods_json.settings_of_loop.body, hlt'], ?_, h4⟩
      rw [h3, List.take_of_length_le (by omega)]

theorem eval.mods_json.settings_obj_refines (v : eval.mods_json.V) (hv : ev_vOk v) :
    ∃ r, eval.mods_json.settings_obj v = ok r ∧
      msSetS r.val = (match ev_vS v with | .obj ss => ss.map (fun (k, v) => (k, SimJson.toSetting v)) | _ => []) ∧
      ∀ p ∈ r.val, VValid p.1 ∧ p.1.val.length < 2^62 ∧ JOk p.2 := by
  cases v with
  | Obj kvs =>
    obtain ⟨r, hr, hrs, hrok⟩ := eval.mods_json.settings_of_refines (alloc.vec.Vec.deref kvs)
      (by simpa using (ev_vOk_obj kvs).mp hv)
    refine ⟨r, by simpa [eval.mods_json.settings_obj] using hr, ?_, hrok⟩
    rw [hrs, ev_vS_obj]; simp
  | Num t => exact ⟨_, rfl, by simp [msSetS], by simp⟩
  | VStr t => exact ⟨_, rfl, by simp [msSetS], by simp⟩
  | Bool b => exact ⟨_, rfl, by simp [msSetS], by simp⟩
  | Null => exact ⟨_, rfl, by simp [msSetS], by simp⟩
  | Arr xs => exact ⟨_, rfl, by simp [msSetS, ev_vS_arr], by simp⟩
end OsuProofs

namespace OsuProofs
open OsuImpl
/-- the per-element function of `SimJson.parseMods`'s `xs.mapM` (bridge `js_parseMods_eq`) -/
def js_modSpec (x : SimJson.V) : Except String ModConfig :=
  match x with
  | .obj kvs =>
    let acr := match kvs.find? (·.1 == "acronym") with | some (_, .str a) => a | _ => ""
    let settings := match kvs.find? (·.1 == "settings") with
      | some (_, .obj ss) => ss.map fun (k, v) => (k, SimJson.toSetting v)
      | _ => []
    pure (Settings.toMod acr settings)
  | _ => throw "mod is not an object"

theorem js_parseMods_eq (s : String) : SimJson.parseMods s =
    match (SimJson.value).run s.toList with
    | .error e => .error e
    | .ok (v, _) => match v with
      | .arr xs => xs.mapM js_modSpec
      | _ => .error "mods is not an array" := by
  unfold SimJson.parseMods
  cases (SimJson.value).run s.toList with
  | error e => rfl
  | ok p => obtain ⟨v, L⟩ := p; cases v <;> rfl
end OsuProofs

namespace OsuProofs
open OsuImpl
theorem js_find_some {α β} (L : List α) (f : α → β) (q : β → Bool) (P : α → Bool) (hP : ∀ a, P a = q (f a))
    (i : Nat) (h : L.findIdx? P = some i) : ∃ hi : i < L.length, (L.map f).find? q = some (f (L[i]'hi)) := by
  obtain ⟨hi, hpi, hb⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  refine ⟨hi, ?_⟩
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by rw [← hP]; exact hpi, i, by simpa using hi, by simp, ?_⟩
  intro j hj; simp only [List.getElem_map]; rw [← hP]; simpa using hb j hj

theorem js_find_none {α β} (L : List α) (f : α → β) (q : β → Bool) (P : α → Bool) (hP : ∀ a, P a = q (f a))
    (h : L.findIdx? P = none) : (L.map f).find? q = none := by
  rw [List.findIdx?_eq_none_iff] at h
  rw [List.find?_eq_none]; intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  rw [← hP]; simpa using h a ha

/-- well-formed decoded mod config (= `ev_mcOk` of Eval/E2EBase.lean) -/
def js_mcOk (m : beatmap.mod_settings.ModConfig) : Prop :=
  VValid m.acronym ∧ m.acronym.val.length < 2^62 ∧ KeysOk m.settings.val

theorem js_to_mod_known_acr (acr : alloc.vec.Vec U32) (defs : alloc.vec.Vec beatmap.mod_settings.SettingDef)
    (st : Slice (alloc.vec.Vec U32 × beatmap.mod_settings.JsonVal)) (r : beatmap.mod_settings.ModConfig)
    (h : beatmap.mod_settings.to_mod_known acr defs st = ok r) : r.acronym = acr := by
  obtain ⟨v0, hv0, -⟩ := ms_tmk_loop0 defs
  unfold beatmap.mod_settings.to_mod_known at h
  rw [hv0, bind_ok] at h
  simp only [] at h
  split at h
  · simp only [ok.injEq] at h; rw [← h]
  · generalize hL : beatmap.mod_settings.to_mod_known_loop1 acr defs st v0 0#usize = L at h
    cases L <;> simp at h
    all_goals rw [← h]

/-- `to_mod_refines` plus the well-formedness `js_mcOk` of the result (eval agent's `ev_to_mod_ok`, Osr.lean) -/
theorem js_to_mod_ok (a : Slice U32) (ha : ValidStr a) (hal : a.val.length < 2^62)
    (st : Slice (alloc.vec.Vec U32 × beatmap.mod_settings.JsonVal))
    (hv : ∀ p ∈ st.val, VValid p.1) (hj : ∀ p ∈ st.val, JOk' p.2) :
    ∃ r, beatmap.mod_settings.to_mod a st = ok r ∧
      mcS r = OsuModel.Beatmap.Settings.toMod (String.ofList (strS a)) (msSetS st.val) ∧ js_mcOk r := by
  obtain ⟨r, hr, hrv⟩ := beatmap.mod_settings.to_mod_refines a ha st hv hj
  refine ⟨r, hr, hrv, ?_⟩
  obtain ⟨u, hu, hu1, hu2⟩ := ms_to_mod_loop a ha (alloc.vec.Vec.new U32) 0#usize (by simp) (by simp)
    (by intro x hx; simp at hx) (by simp)
  have hul : u.val.length = a.val.length := by
    have := congrArg List.length hu2; simpa [strS] using this
  obtain ⟨o, ho, hov⟩ := beatmap.mod_settings.table_refines (alloc.vec.Vec.deref u) (vvalid_deref u hu1)
  unfold beatmap.mod_settings.to_mod at hr
  simp only [hu, bind_ok, ho] at hr
  cases o with
  | none =>
    obtain ⟨v, hv1, hvv⟩ := beatmap.mod_settings.copy_str_refines a
    simp only [hv1, bind_ok, ok.injEq] at hr
    subst hr
    refine ⟨?_, ?_, ?_⟩
    · intro x hx; simp only [hvv] at hx; exact ha x hx
    · simp only [hvv]; exact hal
    · intro p hp; simp at hp
  | some defs =>
    simp only [Option.map_some] at hov
    have hd : DefsOk defs.val := by
      intro d hdm
      have := ms_table_keys _ _ hov.symm (sdS d) (List.mem_map_of_mem hdm)
      exact (keyName_ne_empty _).mp this
    obtain ⟨r', hr', hk, -⟩ := beatmap.mod_settings.to_mod_known_refines u hu1 defs hd st hv hj
    simp only [hr', ok.injEq] at hr
    subst hr
    have hacr := js_to_mod_known_acr u defs st r' hr'
    refine ⟨?_, ?_, hk⟩
    · rw [hacr]; exact hu1
    · rw [hacr, hul]; exact hal

theorem js_lit_acronym : String.ofList (litS (Array.to_slice (Array.make 7#usize [
          97#u8, 99#u8, 114#u8, 111#u8, 110#u8, 121#u8, 109#u8 ]))) = "acronym" := by
  simp [litS, Array.to_slice, Array.make]
theorem js_lit_settings : String.ofList (litS (Array.to_slice (Array.make 8#usize [
          115#u8, 101#u8, 116#u8, 116#u8, 105#u8, 110#u8, 103#u8, 115#u8 ]))) = "settings" := by
  simp [litS, Array.to_slice, Array.make]
end OsuProofs

namespace OsuProofs
open OsuImpl
def js_mjeS : eval.mods_json.ModsJsonErr → String
  | .Json j => ev_jeS j
  | .NotArray => "mods is not an array"
  | .NotObject => "mod is not an object"

/-- a Rust `Result<ModConfig, ModsJsonErr>` vs the spec: same config (+ well-formed) or the same message -/
def js_mRel : core.result.Result beatmap.mod_settings.ModConfig eval.mods_json.ModsJsonErr → Except String ModConfig → Prop
  | .Ok m, .ok M => mcS m = M ∧ js_mcOk m
  | .Err e, .error s => s = js_mjeS e
  | _, _ => False

def js_kvS (kv : alloc.vec.Vec U32 × eval.mods_json.V) : String × SimJson.V := (vstrS kv.1, ev_vS kv.2)

theorem js_acr_match (x : String) (w : SimJson.V) :
    (match some (x, w) with | some (_, .str a) => a | _ => "") = (match w with | .str a => a | _ => "") := by
  cases w <;> rfl
theorem js_set_match (x : String) (w : SimJson.V) :
    (match some (x, w) with | some (_, .obj ss) => ss.map (fun (x : String × SimJson.V) => match x with | (k, v) => (k, SimJson.toSetting v)) | _ => []) =
    (match w with | .obj ss => ss.map (fun (x : String × SimJson.V) => match x with | (k, v) => (k, SimJson.toSetting v)) | _ => []) := by
  cases w <;> rfl

theorem js_acr_part (kvs : alloc.vec.Vec (alloc.vec.Vec U32 × eval.mods_json.V))
    (hok : ∀ kv ∈ kvs.val, ev_VV kv.1 ∧ ev_vOk kv.2) (o : Option Usize)
    (ho : o.map (·.val) = kvs.val.findIdx? (js_keyP (Array.to_slice (Array.make 7#usize [
          97#u8, 99#u8, 114#u8, 111#u8, 110#u8, 121#u8, 109#u8 ])))) :
    ∃ acr, (match o with
      | none => ok (alloc.vec.Vec.new U32)
      | some i => do
        let (_, v) ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
            ((alloc.vec.Vec U32) × eval.mods_json.V)) kvs i
        eval.mods_json.acronym_str v) = ok acr ∧
      vstrS acr = (match (kvs.val.map js_kvS).find? (·.1 == "acronym") with | some (_, .str a) => a | _ => "") ∧
      VValid acr ∧ acr.val.length < 2^62 := by
  have hP : ∀ a, js_keyP (Array.to_slice (Array.make 7#usize [
          97#u8, 99#u8, 114#u8, 111#u8, 110#u8, 121#u8, 109#u8 ])) a = ((js_kvS a).1 == "acronym") := by
    intro a; unfold js_keyP js_kvS; rw [js_lit_acronym]
  cases o with
  | none =>
    rw [js_find_none _ js_kvS (fun p => p.1 == "acronym") _ hP ho.symm]
    exact ⟨_, rfl, by simp [vstrS], by simp [VValid], by simp⟩
  | some i =>
    obtain ⟨hi, hf⟩ := js_find_some _ js_kvS (fun p => p.1 == "acronym") _ hP i.val ho.symm
    rw [hf]
    have hkv := hok _ (List.getElem_mem hi)
    generalize hx : kvs.val[i.val]'hi = kv at hkv
    obtain ⟨k, v⟩ := kv
    obtain ⟨r, hr, hrv, hrok⟩ := eval.mods_json.acronym_str_refines v hkv.2
    refine ⟨r, ?_, by rw [hrv]; unfold js_kvS; exact (js_acr_match _ _).symm, hrok⟩
    have hix : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice ((alloc.vec.Vec U32) × eval.mods_json.V))
        kvs i = ok (k, v) := by rw [← hx]; exact vec_index_eq _ _ hi
    simp only [hix, bind_ok]; exact hr

theorem js_set_part (kvs : alloc.vec.Vec (alloc.vec.Vec U32 × eval.mods_json.V))
    (hok : ∀ kv ∈ kvs.val, ev_VV kv.1 ∧ ev_vOk kv.2) (o : Option Usize)
    (ho : o.map (·.val) = kvs.val.findIdx? (js_keyP (Array.to_slice (Array.make 8#usize [
          115#u8, 101#u8, 116#u8, 116#u8, 105#u8, 110#u8, 103#u8, 115#u8 ])))) :
    ∃ st, (match o with
      | none => ok (alloc.vec.Vec.new ((alloc.vec.Vec U32) × beatmap.mod_settings.JsonVal))
      | some i => do
        let (_, v) ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
            ((alloc.vec.Vec U32) × eval.mods_json.V)) kvs i
        eval.mods_json.settings_obj v) = ok st ∧
      msSetS st.val = (match (kvs.val.map js_kvS).find? (·.1 == "settings") with
        | some (_, .obj ss) => ss.map (fun (x : String × SimJson.V) => match x with | (k, v) => (k, SimJson.toSetting v))
        | _ => []) ∧
      ∀ p ∈ st.val, VValid p.1 ∧ p.1.val.length < 2^62 ∧ JOk p.2 := by
  have hP : ∀ a, js_keyP (Array.to_slice (Array.make 8#usize [
          115#u8, 101#u8, 116#u8, 116#u8, 105#u8, 110#u8, 103#u8, 115#u8 ])) a = ((js_kvS a).1 == "settings") := by
    intro a; unfold js_keyP js_kvS; rw [js_lit_settings]
  cases o with
  | none =>
    rw [js_find_none _ js_kvS (fun p => p.1 == "settings") _ hP ho.symm]
    exact ⟨_, rfl, by simp [msSetS], by simp⟩
  | some i =>
    obtain ⟨hi, hf⟩ := js_find_some _ js_kvS (fun p => p.1 == "settings") _ hP i.val ho.symm
    rw [hf]
    have hkv := hok _ (List.getElem_mem hi)
    generalize hx : kvs.val[i.val]'hi = kv at hkv
    obtain ⟨k, v⟩ := kv
    obtain ⟨r, hr, hrv, hrok⟩ := eval.mods_json.settings_obj_refines v hkv.2
    refine ⟨r, ?_, by rw [hrv]; unfold js_kvS; exact (js_set_match _ _).symm, hrok⟩
    have hix : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice ((alloc.vec.Vec U32) × eval.mods_json.V))
        kvs i = ok (k, v) := by rw [← hx]; exact vec_index_eq _ _ hi
    simp only [hix, bind_ok]; exact hr
end OsuProofs

namespace OsuProofs
open OsuImpl
theorem js_vec_index_pair (kvs : alloc.vec.Vec (alloc.vec.Vec U32 × eval.mods_json.V)) (i : Usize)
    (h : i.val < kvs.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice ((alloc.vec.Vec U32) × eval.mods_json.V)) kvs i =
      ok ((kvs.val[i.val]'h).1, (kvs.val[i.val]'h).2) := vec_index_eq _ _ h

theorem js_JOk' (h64 : System.Platform.numBits = 64) (j : beatmap.mod_settings.JsonVal) (h : JOk j) : JOk' j := by
  refine ⟨h, ?_⟩
  cases j with
  | Str s =>
    have hm : Usize.max = 2^64 - 1 := by simp [Usize.max, Usize.numBits, h64]
    have := h.2; simp only []; rw [hm]; omega
  | _ => trivial

/-- one element of the mod list (`parseMods`' `mapM` function `js_modSpec`) -/
theorem eval.mods_json.parse_mod_refines (h64 : System.Platform.numBits = 64) (x : eval.mods_json.V) (hx : ev_vOk x) :
    ∃ r, eval.mods_json.parse_mod x = ok r ∧ js_mRel r (js_modSpec (ev_vS x)) := by
  cases x with
  | Obj kvs =>
    have hok := (ev_vOk_obj kvs).mp hx
    have hk : js_kOk (alloc.vec.Vec.deref kvs).val := fun kv h => (hok kv (by simpa using h)).1.1
    obtain ⟨o, ho, hov⟩ := eval.mods_json.find_first_refines (alloc.vec.Vec.deref kvs) _ hk
    obtain ⟨acr, hA, hAv, hAok, hAl⟩ := js_acr_part kvs hok o (by simpa using hov)
    obtain ⟨o1, ho1, ho1v⟩ := eval.mods_json.find_first_refines (alloc.vec.Vec.deref kvs) _ hk
    obtain ⟨st, hS, hSv, hSok⟩ := js_set_part kvs hok o1 (by simpa using ho1v)
    obtain ⟨mc, hmc, hmcv, hmok⟩ := js_to_mod_ok (alloc.vec.Vec.deref acr) (vvalid_deref _ hAok) (by simpa using hAl)
      (alloc.vec.Vec.deref st) (fun p hp => (hSok p (by simpa using hp)).1)
      (fun p hp => js_JOk' h64 _ (hSok p (by simpa using hp)).2.2)
    refine ⟨.Ok mc, ?_, ?_⟩
    · have hA' : ∃ X, (match o with
          | none => (ok (alloc.vec.Vec.new U32) : Result _)
          | some i => eval.mods_json.acronym_str X) = ok acr ∧
          ∀ i (hi : i.val < kvs.val.length), o = some i → X = (kvs.val[i.val]'hi).2 := by
        cases o with
        | none => exact ⟨.Null, by simpa using hA, by intro i _ h; cases h⟩
        | some i =>
          obtain ⟨hi, -⟩ := List.findIdx?_eq_some_iff_getElem.mp (by simpa using hov.symm)
          refine ⟨(kvs.val[i.val]'(by simpa using hi)).2, ?_, by intro j hj h; cases h; rfl⟩
          simp only [js_vec_index_pair kvs i (by simpa using hi), bind_ok, Aeneas.Std.uncurry_apply_pair] at hA
          exact hA
      unfold eval.mods_json.parse_mod
      simp only [lift, bind_ok, ho, ho1]
      cases o with
      | none =>
        obtain ⟨X, hX, -⟩ := hA'
        simp only [ok.injEq] at hX
        subst hX
        cases o1 with
        | none => simp only [ok.injEq] at hS; subst hS; simp only [bind_ok, hmc]
        | some i =>
          obtain ⟨hi, -⟩ := List.findIdx?_eq_some_iff_getElem.mp (by simpa using ho1v.symm)
          simp only [js_vec_index_pair kvs i (by simpa using hi), bind_ok] at hS ⊢
          simp only [hS, bind_ok, hmc]
      | some j =>
        obtain ⟨X, hX, hXv⟩ := hA'
        obtain ⟨hj, -⟩ := List.findIdx?_eq_some_iff_getElem.mp (by simpa using hov.symm)
        have hX' := hXv j (by simpa using hj) rfl
        subst hX'
        simp only [js_vec_index_pair kvs j (by simpa using hj), bind_ok]
        simp only [Aeneas.Std.uncurry_apply_pair]
        dsimp only at hX
        simp only [hX, bind_ok]
        cases o1 with
        | none => simp only [ok.injEq] at hS; subst hS; simp only [bind_ok, hmc]
        | some i =>
          obtain ⟨hi, -⟩ := List.findIdx?_eq_some_iff_getElem.mp (by simpa using ho1v.symm)
          simp only [js_vec_index_pair kvs i (by simpa using hi), bind_ok] at hS ⊢
          simp only [hS, bind_ok, hmc]
    · rw [ev_vS_obj]
      refine ⟨?_, hmok⟩
      rw [hmcv, ← js_vstrS_deref, hAv]
      simp only [ms_deref_val, hSv]
      rfl
  | Num t => exact ⟨_, rfl, rfl⟩
  | VStr t => exact ⟨_, rfl, rfl⟩
  | Bool b => exact ⟨_, rfl, rfl⟩
  | Null => exact ⟨_, rfl, rfl⟩
  | Arr xs => exact ⟨_, rfl, by obtain ⟨⟨n, l, h⟩⟩ := xs; rfl⟩
end OsuProofs

namespace OsuProofs
open OsuImpl
def js_lRel : core.result.Result (alloc.vec.Vec beatmap.mod_settings.ModConfig) eval.mods_json.ModsJsonErr →
    Except String (List ModConfig) → Prop
  | .Ok ms, .ok MS => ms.val.map mcS = MS ∧ ∀ m ∈ ms.val, js_mcOk m
  | .Err e, .error s => s = js_mjeS e
  | _, _ => False

theorem js_mapM_snoc {α β} (f : α → Except String β) (l : List α) (x : α) (a : List β) (h : l.mapM f = .ok a) :
    (l ++ [x]).mapM f = (f x).map (fun b => a ++ [b]) := by
  rw [List.mapM_append, h]; simp only [List.mapM_cons, List.mapM_nil]
  cases f x <;> rfl

theorem js_mapM_err {α β} (f : α → Except String β) (l r : List α) (x : α) (a : List β) (s : String)
    (h : l.mapM f = .ok a) (hx : f x = .error s) : (l ++ x :: r).mapM f = .error s := by
  rw [List.mapM_append, h]; simp only [List.mapM_cons, hx]; rfl

theorem eval.mods_json.parse_mod_list_refines (h64 : System.Platform.numBits = 64) (xs : Slice eval.mods_json.V)
    (hok : ∀ x ∈ xs.val, ev_vOk x) :
    ∃ r, eval.mods_json.parse_mod_list xs = ok r ∧ js_lRel r ((xs.val.map ev_vS).mapM js_modSpec) := by
  have hmax : xs.val.length ≤ Usize.max := Slice.length_ineq xs
  have H := loop_ok (fun (x : alloc.vec.Vec beatmap.mod_settings.ModConfig × Option eval.mods_json.ModsJsonErr × Usize) =>
      eval.mods_json.parse_mod_list_loop.body xs x.1 x.2.1 x.2.2)
    (fun x => xs.val.length + 1 - x.2.2.val - (if x.2.1.isSome then 1 else 0))
    (fun x => x.2.2.val ≤ xs.val.length ∧ x.1.val.length ≤ x.2.2.val ∧
      ((x.2.1 = none ∧ ((xs.val.take x.2.2.val).map ev_vS).mapM js_modSpec = .ok (x.1.val.map mcS) ∧
          ∀ m ∈ x.1.val, js_mcOk m) ∨
       (∃ e, x.2.1 = some e ∧ (xs.val.map ev_vS).mapM js_modSpec = .error (js_mjeS e))))
    (fun y => (y.2 = none ∧ (xs.val.map ev_vS).mapM js_modSpec = .ok (y.1.val.map mcS) ∧ ∀ m ∈ y.1.val, js_mcOk m) ∨
       (∃ e, y.2 = some e ∧ (xs.val.map ev_vS).mapM js_modSpec = .error (js_mjeS e))) ?_
    (alloc.vec.Vec.new _, none, 0#usize) ⟨by simp, by simp, Or.inl ⟨rfl, by simp, by simp⟩⟩
  · obtain ⟨⟨out, err⟩, hy, hq⟩ := H
    unfold eval.mods_json.parse_mod_list eval.mods_json.parse_mod_list_loop
    rw [show (fun (x : alloc.vec.Vec beatmap.mod_settings.ModConfig × Option eval.mods_json.ModsJsonErr × Usize) =>
        match x with
        | (out1, err1, i1) => eval.mods_json.parse_mod_list_loop.body xs out1 err1 i1) =
        (fun x => eval.mods_json.parse_mod_list_loop.body xs x.1 x.2.1 x.2.2) from rfl, hy]
    rcases hq with ⟨h1, h2, h3⟩ | ⟨e, h1, h2⟩
    · simp only at h1; subst h1
      exact ⟨.Ok out, by simp, by rw [h2]; exact ⟨rfl, h3⟩⟩
    · simp only at h1; subst h1
      exact ⟨.Err e, by simp, by rw [h2]; rfl⟩
  · rintro ⟨out, err, i⟩ ⟨h1, h2, h3⟩
    simp only at h1 h2 h3 ⊢
    rcases h3 with ⟨rfl, h3, h4⟩ | ⟨e, rfl, h3⟩
    · by_cases hlt : i.val < xs.val.length
      · right
        have hlt' : i < Slice.len xs := (slice_lt_len_iff i xs).mpr hlt
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
        have htake : xs.val.take (i.val + 1) = xs.val.take i.val ++ [xs.val[i.val]'hlt] :=
          List.take_succ_eq_append_getElem hlt
        have hfull : xs.val = xs.val.take i.val ++ (xs.val[i.val]'hlt) :: xs.val.drop (i.val + 1) := by
          rw [List.getElem_cons_drop]; exact (List.take_append_drop _ _).symm
        have hx := hok _ (List.getElem_mem hlt)
        obtain ⟨r, hr, hrel⟩ := eval.mods_json.parse_mod_refines h64 _ hx
        cases r with
        | Ok m =>
          have hout : out.val.length < Usize.max := by omega
          refine ⟨(vpush out m hout, none, i1), ?_, ⟨by dsimp only; omega, by simp [vpush_val]; omega, Or.inl ⟨rfl, ?_, ?_⟩⟩,
            by simp; omega⟩
          · simp [eval.mods_json.parse_mod_list_loop.body, hlt', slice_index_ok xs i hlt, hr, vec_push_ok out m hout, hi1]
          · rw [hi1v, htake, List.map_append, List.map_singleton, js_mapM_snoc _ _ _ _ h3]
            revert hrel; cases js_modSpec (ev_vS (xs.val[i.val]'hlt)) with
            | ok M => rintro ⟨hm, -⟩; simp [vpush_val, hm]; rfl
            | error _ => intro h; exact h.elim
          · intro m' hm'; simp only [vpush_val, List.mem_append, List.mem_singleton] at hm'
            rcases hm' with hm' | rfl
            · exact h4 _ hm'
            · revert hrel; cases js_modSpec (ev_vS (xs.val[i.val]'hlt)) with
              | ok M => rintro ⟨-, hm⟩; exact hm
              | error _ => intro h; exact h.elim
        | Err e =>
          refine ⟨(out, some e, i1), ?_, ⟨by dsimp only; omega, by dsimp only; omega, Or.inr ⟨e, rfl, ?_⟩⟩,
            by simp; omega⟩
          · simp [eval.mods_json.parse_mod_list_loop.body, hlt', slice_index_ok xs i hlt, hr, hi1]
          · rw [hfull, List.map_append, List.map_cons]
            revert hrel; cases hs : js_modSpec (ev_vS (xs.val[i.val]'hlt)) with
            | ok M => intro h; exact h.elim
            | error s => intro h; rw [js_mapM_err _ _ _ _ _ _ h3 hs, h]
      · left
        have hlt' : ¬ i < Slice.len xs := by rw [slice_lt_len_iff]; exact hlt
        refine ⟨(out, none), by simp [eval.mods_json.parse_mod_list_loop.body, hlt'], Or.inl ⟨rfl, ?_, h4⟩⟩
        rw [← h3, List.take_of_length_le (by omega)]
    · left
      exact ⟨(out, some e), by simp [eval.mods_json.parse_mod_list_loop.body], Or.inr ⟨e, rfl, h3⟩⟩
end OsuProofs

namespace OsuProofs
open OsuImpl
/-- TOP: `mods_json::parse_mods` (the `--mods` JSON) refines `SimJson.parseMods`: the same decoded mod configs
(all well-formed, `js_mcOk` = `ev_mcOk`) or the same error message. -/
theorem eval.mods_json.parse_mods_refines (h64 : System.Platform.numBits = 64) (s : Slice U32) (hs : ValidStr s)
    (hlen : s.val.length + 8 ≤ Usize.max) (h62 : s.val.length < 2^62) :
    ∃ r, eval.mods_json.parse_mods s = ok r ∧ js_lRel r (SimJson.parseMods (String.ofList (strS s))) := by
  rw [js_parseMods_eq, String.toList_ofList]
  obtain ⟨r, hr, hrel⟩ := eval.mods_json.value_refines s hs hlen h62 0#usize (by simp)
  simp only [UScalar.ofNatCore_val_eq, List.drop_zero] at hrel
  revert hrel
  cases hV : (SimJson.value).run (strS s) with
  | error m =>
    cases r with
    | Ok _ => intro h; exact h.elim
    | Err e =>
      intro h
      exact ⟨.Err (.Json e), by simp [eval.mods_json.parse_mods, hr], h⟩
  | ok wL =>
    obtain ⟨w, L⟩ := wL
    cases r with
    | Err _ => intro h; exact h.elim
    | Ok vq =>
      obtain ⟨v, q⟩ := vq
      rintro ⟨hw, -, -, -, hok⟩
      subst hw
      cases v with
      | Arr xs =>
        obtain ⟨r, hr', hrel'⟩ := eval.mods_json.parse_mod_list_refines h64 (alloc.vec.Vec.deref xs)
          (by simpa using (ev_vOk_arr xs).mp hok)
        refine ⟨r, by simp [eval.mods_json.parse_mods, hr, hr'], ?_⟩
        simpa [ev_vS_arr] using hrel'
      | Num _ => exact ⟨.Err .NotArray, by simp [eval.mods_json.parse_mods, hr], rfl⟩
      | VStr _ => exact ⟨.Err .NotArray, by simp [eval.mods_json.parse_mods, hr], rfl⟩
      | Bool _ => exact ⟨.Err .NotArray, by simp [eval.mods_json.parse_mods, hr], rfl⟩
      | Null => exact ⟨.Err .NotArray, by simp [eval.mods_json.parse_mods, hr], rfl⟩
      | Obj xs => exact ⟨.Err .NotArray, by simp [eval.mods_json.parse_mods, hr], by obtain ⟨⟨n, l, h⟩⟩ := xs; rfl⟩
end OsuProofs

