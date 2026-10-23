/-
Lazer score-info JSON (`eval::osr` JSON part, json agent D46/D50): `json_int`, `is_int`, `eq_ci`, `hr_*`,
`is_hit_result_key`, `enum_name_*`, `stats_*`, `pauses_ok`, `check_*`, `bad_unless`, `api_*`, `has_trailing`,
`score_info_mods` and the top `decode_score_info` (refines `OsuModel.Replay.Osr.decodeScoreInfo`; discharges the
eval agent's `ev_scoreInfoOk` given 64-bit, see STATE Requests).

Relations: errors are related only as "both reject" (`js_eRel`, `js_mRel'`, `js_lRel'`; the score-info error texts
are not part of the evaluator's observable output). `checkScoreInfo` is characterised by `js_memberOk`
(`js_check_spec`: `js_isOk (checkScoreInfo kvs) = kvs.all js_memberOk`); `apiModToMod` / `decodeScoreInfo` are
unfolded into `js_acrSpec`/`js_setSpec`/`js_simSpec` by the `rfl`/case bridges `js_apiModToMod_eq`,
`js_decodeScoreInfo_eq` (so the `_refines` theorems are against the real spec, not fragments).
String API bridges: `String.toInt?` (`js_isInt`), `String.map Char.toLower` equality = `eqIgnoreCase` (`js_eqIC`),
`hitResultKeys` = the 36 literal names (`js_hitResultKeys`, by `decide`).
-/
import OsuProofs.Eval.JsonMods
import OsuModel.Replay.Osr
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
theorem js_isInt (L : List Char) : (String.ofList L).toInt?.isSome =
    (if L.head? = some '-' then js_isNatAux false (L.drop 1) else js_isNatAux false L) := by
  by_cases hc : L.head? = some '-'
  · obtain ⟨R, rfl⟩ : ∃ R, L = '-' :: R := by
      cases L with
      | nil => simp at hc
      | cons c R => simp at hc; exact ⟨R, by rw [hc]⟩
    have : String.ofList ('-' :: R) = "-" ++ String.ofList R := by
      apply String.toList_injective; simp
    rw [this, String.toInt?_minus_append, if_pos hc]
    simp only [Option.isSome_map, String.isSome_toNat?, js_isNat_eq, List.drop_succ_cons, List.drop_zero]
  · rw [String.toInt?_eq_toNat?_of_startsWith_eq_false, if_neg hc]
    · simp only [Option.isSome_map, String.isSome_toNat?, js_isNat_eq]
    · rw [String.startsWith_char_eq_head?]; simpa using hc
end OsuProofs

namespace OsuProofs
open OsuImpl
theorem js_eqIC (A B : List Char) :
    OsuModel.Net.Parse.eqIgnoreCase A B = ((String.ofList B).map Char.toLower == (String.ofList A).map Char.toLower) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, ← String.toList_inj, String.toList_map, String.toList_map,
    String.toList_ofList, String.toList_ofList]
  induction A generalizing B with
  | nil => cases B <;> simp [OsuModel.Net.Parse.eqIgnoreCase]
  | cons a t ih =>
    cases B with
    | nil => simp [OsuModel.Net.Parse.eqIgnoreCase]
    | cons b bs =>
      simp only [OsuModel.Net.Parse.eqIgnoreCase, Bool.and_eq_true, beq_iff_eq, ih, List.map_cons, List.cons.injEq]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2⟩

theorem eval.osr.eq_ci_refines (s : Slice U32) (hs : ValidStr s) (lit : Slice U8) :
    eval.osr.eq_ci s lit = ok ((String.ofList (litS lit)).map Char.toLower == (String.ofList (strS s)).map Char.toLower) := by
  unfold eval.osr.eq_ci
  rw [net.parse.eq_ignore_case_refines s hs 0#usize (Slice.len s) (by simp) (by simp) lit, ← js_eqIC]
  congr 2; simp [List.take_of_length_le, strS_length]

theorem eval.osr.is_int_refines (s : Slice U32) (hs : ValidStr s) :
    eval.osr.is_int s = ok (String.ofList (strS s)).toInt?.isSome := by
  unfold eval.osr.is_int
  rw [eval.mods_json.starts_minus_refines, js_startsWith_minus, js_isInt, bind_ok]
  have hl : (Slice.len s).val = s.val.length := by simp
  by_cases hc : (strS s).head? = some '-'
  · have h1 : 1 ≤ s.val.length := by
      cases ht : s.val with
      | nil => simp [strS, ht] at hc
      | cons _ _ => simp
    simp only [hc, decide_true, if_true]
    rw [eval.mods_json.is_nat_refines s hs 1#usize (Slice.len s) (by simp; omega) (by simp), js_isNat_eq, hl, js_sub_all]
    rfl
  · simp only [hc, decide_false, Bool.false_eq_true, if_false]
    rw [eval.mods_json.is_nat_refines s hs 0#usize (Slice.len s) (by simp) (by simp), js_isNat_eq, hl, js_sub_all]
    rfl
end OsuProofs

namespace OsuProofs
open OsuImpl
theorem eval.osr.json_int_refines (v : eval.mods_json.V) (hv : ev_vOk v) (lo hi : U128)
    (hlo : lo.val < 2^64) (hhi : hi.val < 2^64) :
    eval.osr.json_int v lo hi = ok (OsuModel.Replay.Osr.jsonInt (ev_vS v) (-(lo.val : Int)) hi.val) := by
  cases v with
  | Num t =>
    have ht : ev_VV t := hv
    have hs : ValidStr (alloc.vec.Vec.deref t) := fun u hu => ht.1 u (by simpa using hu)
    simp only [ev_vS_num, OsuModel.Replay.Osr.jsonInt, js_vstrS_deref]
    unfold eval.osr.json_int
    simp only [eval.mods_json.has_frac_or_exp_refines, bind_ok]
    split
    · rename_i hb; simp [hb]
    · rename_i hb
      obtain ⟨neg, m, hm, hneg, hmv⟩ := eval.mods_json.int_of_text_refines _ hs
      rw [hm, bind_ok]
      show eval.mods_json.in_range neg m lo hi = _
      rw [eval.mods_json.in_range_refines]
      simp only [hb, Bool.not_false, Bool.true_and]
      subst hneg
      generalize ((String.ofList (strS (alloc.vec.Vec.deref t))).drop 1).toNat! = A at hmv ⊢
      generalize (String.ofList (strS (alloc.vec.Vec.deref t))).toNat! = B at hmv ⊢
      cases hsw : (String.ofList (strS (alloc.vec.Vec.deref t))).startsWith "-" <;> rw [hsw] at hmv <;>
        simp at hmv ⊢ <;> omega
  | VStr _ => rfl
  | Bool _ => rfl
  | Null => rfl
  | Arr xs => obtain ⟨⟨n, l, h⟩⟩ := xs; rfl
  | Obj xs => obtain ⟨⟨n, l, h⟩⟩ := xs; rfl
end OsuProofs

namespace OsuProofs
open OsuImpl
theorem js_ite_ok_or (b c : Bool) : (if b = true then (ok true : Result Bool) else ok c) = ok (b || c) := by
  cases b <;> rfl

theorem eval.osr.enum_name_rank_refines (s : Slice U32) (hs : ValidStr s) :
    eval.osr.enum_name_rank s =
      ok (OsuModel.Replay.Osr.enumName OsuModel.Replay.Osr.scoreRankNames (String.ofList (strS s))) := by
  unfold eval.osr.enum_name_rank
  simp only [lift, bind_ok, eval.osr.eq_ci_refines s hs, eval.osr.is_int_refines s hs, js_ite_ok_or]
  simp only [litS, Array.to_slice, Array.make, OsuModel.Replay.Osr.enumName, OsuModel.Replay.Osr.scoreRankNames,
    List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
  rfl
end OsuProofs
namespace OsuProofs
open OsuImpl
def js_hrNamesA : List String := ["None", "Miss", "Meh", "Ok", "Good", "Great", "Perfect", "SmallTickMiss", "SmallTickHit"]
def js_hrNamesB : List String := ["LargeTickMiss", "LargeTickHit", "SmallBonus", "LargeBonus", "IgnoreMiss", "IgnoreHit",
  "ComboBreak", "SliderTailHit", "LegacyComboIncrease"]
def js_hrSnakeA : List String := ["none", "miss", "meh", "ok", "good", "great", "perfect", "small_tick_miss", "small_tick_hit"]
def js_hrSnakeB : List String := ["large_tick_miss", "large_tick_hit", "small_bonus", "large_bonus", "ignore_miss",
  "ignore_hit", "combo_break", "slider_tail_hit", "legacy_combo_increase"]

theorem js_hitResultKeys : OsuModel.Replay.Osr.hitResultKeys = js_hrNamesA ++ js_hrNamesB ++ js_hrSnakeA ++ js_hrSnakeB := by
  decide

/-- case-insensitive membership in a name list (`enumName`'s first disjunct) -/
def js_ciAny (L : List String) (s : String) : Bool := L.any (fun n => n.map Char.toLower == s.map Char.toLower)

theorem eval.osr.hr_names_a_refines (s : Slice U32) (hs : ValidStr s) :
    eval.osr.hr_names_a s = ok (js_ciAny js_hrNamesA (String.ofList (strS s))) := by
  unfold eval.osr.hr_names_a
  simp only [lift, bind_ok, eval.osr.eq_ci_refines s hs, js_ite_ok_or, js_ciAny, js_hrNamesA, List.any_cons, List.any_nil,
    Bool.or_false]
  rfl
theorem eval.osr.hr_names_b_refines (s : Slice U32) (hs : ValidStr s) :
    eval.osr.hr_names_b s = ok (js_ciAny js_hrNamesB (String.ofList (strS s))) := by
  unfold eval.osr.hr_names_b
  simp only [lift, bind_ok, eval.osr.eq_ci_refines s hs, js_ite_ok_or, js_ciAny, js_hrNamesB, List.any_cons, List.any_nil,
    Bool.or_false]
  rfl
theorem eval.osr.hr_snake_a_refines (s : Slice U32) (hs : ValidStr s) :
    eval.osr.hr_snake_a s = ok (js_ciAny js_hrSnakeA (String.ofList (strS s))) := by
  unfold eval.osr.hr_snake_a
  simp only [lift, bind_ok, eval.osr.eq_ci_refines s hs, js_ite_ok_or, js_ciAny, js_hrSnakeA, List.any_cons, List.any_nil,
    Bool.or_false]
  rfl
theorem eval.osr.hr_snake_b_refines (s : Slice U32) (hs : ValidStr s) :
    eval.osr.hr_snake_b s = ok (js_ciAny js_hrSnakeB (String.ofList (strS s))) := by
  unfold eval.osr.hr_snake_b
  simp only [lift, bind_ok, eval.osr.eq_ci_refines s hs, js_ite_ok_or, js_ciAny, js_hrSnakeB, List.any_cons, List.any_nil,
    Bool.or_false]
  rfl
theorem js_ciAny_append (A B : List String) (s : String) : js_ciAny (A ++ B) s = (js_ciAny A s || js_ciAny B s) := by
  simp [js_ciAny, List.any_append]

theorem eval.osr.is_hit_result_key_refines (s : Slice U32) (hs : ValidStr s) :
    eval.osr.is_hit_result_key s = ok (js_ciAny OsuModel.Replay.Osr.hitResultKeys (String.ofList (strS s))) := by
  unfold eval.osr.is_hit_result_key
  simp only [bind_ok, eval.osr.hr_names_a_refines s hs, eval.osr.hr_names_b_refines s hs, eval.osr.hr_snake_a_refines s hs,
    eval.osr.hr_snake_b_refines s hs, js_ite_ok_or, js_hitResultKeys, js_ciAny_append, Bool.or_assoc]

theorem eval.osr.enum_name_hit_result_refines (s : Slice U32) (hs : ValidStr s) :
    eval.osr.enum_name_hit_result s =
      ok (OsuModel.Replay.Osr.enumName OsuModel.Replay.Osr.hitResultKeys (String.ofList (strS s))) := by
  unfold eval.osr.enum_name_hit_result
  simp only [bind_ok, eval.osr.is_hit_result_key_refines s hs, eval.osr.is_int_refines s hs, js_ite_ok_or]
  rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr
def js_isOk {ε α} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

def js_statsP (p : String × SimJson.V) : Bool := enumName hitResultKeys p.1 && jsonInt p.2 i32lo i32hi

/-- the members accepted by `checkScoreInfo` -/
def js_memberOk (kv : String × SimJson.V) : Bool :=
  if kv.1 = "statistics" ∨ kv.1 = "maximum_statistics" then
    (match kv.2 with | .obj es => es.all js_statsP | _ => false)
  else if kv.1 = "online_id" then jsonInt kv.2 i64lo i64hi
  else if kv.1 = "user_id" then jsonInt kv.2 i32lo i32hi
  else if kv.1 = "total_score_without_mods" then (match kv.2 with | .null => true | v => jsonInt v i64lo i64hi)
  else if kv.1 = "client_version" then (match kv.2 with | .str _ => true | .null => true | _ => false)
  else if kv.1 = "rank" then
    (match kv.2 with | .null => true | .str s => enumName scoreRankNames s | v => jsonInt v i32lo i32hi)
  else if kv.1 = "pauses" then (match kv.2 with | .arr xs => xs.all (fun x => jsonInt x i32lo i32hi) | _ => false)
  else true

theorem js_forIn_unit {α} (L : List α) (f : α → PUnit → Except String (ForInStep PUnit)) (P : α → Bool)
    (h1 : ∀ x, js_isOk (f x PUnit.unit) = P x) (h2 : ∀ x, f x PUnit.unit ≠ .ok (.done PUnit.unit)) :
    js_isOk (forIn L PUnit.unit f) = L.all P := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons]
    have e1 := h1 x; have e2 := h2 x
    revert e1 e2
    cases f x PUnit.unit with
    | error e => intro e1 _; simp only [List.all_cons, ← e1]; rfl
    | ok st =>
      cases st with
      | done u => intro _ e2; exact absurd rfl e2
      | yield u => intro e1 _; simp only [List.all_cons, ← e1]; exact ih

@[simp] theorem js_isOk_seq (r : Except String PUnit) :
    js_isOk (r >>= fun _ => (pure (ForInStep.yield PUnit.unit) : Except String _)) = js_isOk r := by
  cases r <;> rfl
theorem js_seq_ne_done (r : Except String PUnit) :
    (r >>= fun _ => (pure (ForInStep.yield PUnit.unit) : Except String _)) ≠ .ok (.done PUnit.unit) := by
  cases r <;> simp [Bind.bind, Except.bind, Pure.pure, Except.pure]
@[simp] theorem js_isOk_throw {α} (m : String) : js_isOk (throw m : Except String α) = false := rfl
@[simp] theorem js_isOk_pure {α} (a : α) : js_isOk (pure a : Except String α) = true := rfl

@[simp] theorem js_isOk_error {α} (m : String) : js_isOk (Except.error m : Except String α) = false := rfl
@[simp] theorem js_isOk_ok {α} (a : α) : js_isOk (Except.ok a : Except String α) = true := rfl
@[simp] theorem js_isOk_ite {α} (c : Prop) [Decidable c] (a b : Except String α) :
    js_isOk (if c then a else b) = if c then js_isOk a else js_isOk b := by split <;> rfl
@[simp] theorem js_isOk_seq' (r : Except String PUnit) :
    js_isOk (r >>= fun _ => (Except.ok (ForInStep.yield PUnit.unit) : Except String _)) = js_isOk r := by
  cases r <;> rfl

theorem js_seq_ne_done' (r : Except String PUnit) :
    ¬ (r >>= fun _ => (Except.ok (ForInStep.yield PUnit.unit) : Except String _)) = .ok (.done PUnit.unit) := by
  cases r <;> simp [Bind.bind, Except.bind]

theorem js_stats_forIn (es : List (String × SimJson.V)) (m : String) :
    js_isOk (forIn es PUnit.unit fun x __s =>
      if enumName hitResultKeys x.1 = false ∨ jsonInt x.2 i32lo i32hi = false then Except.error m
      else Except.ok (ForInStep.yield PUnit.unit)) = es.all js_statsP := by
  refine js_forIn_unit es _ js_statsP ?_ ?_
  · intro x; simp only [js_statsP]
    by_cases h1 : enumName hitResultKeys x.1 <;> by_cases h2 : jsonInt x.2 i32lo i32hi <;> simp [h1, h2]
  · intro x; split <;> simp

theorem js_pauses_forIn (xs : List SimJson.V) (m : String) :
    js_isOk (forIn xs PUnit.unit fun x __s =>
      if jsonInt x i32lo i32hi = false then Except.error m
      else Except.ok (ForInStep.yield PUnit.unit)) = xs.all (fun x => jsonInt x i32lo i32hi) := by
  refine js_forIn_unit xs _ _ ?_ ?_
  · intro x; by_cases h1 : jsonInt x i32lo i32hi <;> simp [h1]
  · intro x; split <;> simp

theorem js_isOk_bind_pure (r : Except String PUnit) : js_isOk (r >>= fun _ => pure ()) = js_isOk r := by
  cases r <;> rfl

theorem js_check_spec (kvs : List (String × SimJson.V)) : js_isOk (checkScoreInfo kvs) = kvs.all js_memberOk := by
  unfold checkScoreInfo
  rw [js_isOk_bind_pure]
  refine js_forIn_unit kvs _ js_memberOk ?_ ?_
  · rintro ⟨k, v⟩
    dsimp only
    split
    all_goals (try split) <;> simp [js_memberOk, js_stats_forIn, js_pauses_forIn, *]
    all_goals simp_all
  · rintro ⟨k, v⟩
    dsimp only
    split
    all_goals (try split) <;> (try split) <;> simp
    all_goals exact js_seq_ne_done' _
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr
def js_rOk {α ε} : core.result.Result α ε → Bool
  | .Ok _ => true
  | .Err _ => false

theorem js_lo32 : eval.mods_json.I32_LO_MAG.val = 2^31 := by unfold eval.mods_json.I32_LO_MAG; rfl
theorem js_hi32 : eval.mods_json.I32_HI.val = 2^31 - 1 := by unfold eval.mods_json.I32_HI; rfl

theorem js_ji32 (v : eval.mods_json.V) (hv : ev_vOk v) :
    eval.osr.json_int v eval.mods_json.I32_LO_MAG eval.mods_json.I32_HI = ok (jsonInt (ev_vS v) i32lo i32hi) := by
  rw [eval.osr.json_int_refines v hv _ _ (by rw [js_lo32]; omega) (by rw [js_hi32]; omega), js_lo32, js_hi32]; rfl
theorem js_ji64 (v : eval.mods_json.V) (hv : ev_vOk v) :
    eval.osr.json_int v eval.mods_json.I64_LO_MAG eval.mods_json.I64_HI = ok (jsonInt (ev_vS v) i64lo i64hi) := by
  rw [eval.osr.json_int_refines v hv _ _ (by rw [js_lo_mag]; omega) (by rw [js_hi]; omega), js_lo_mag, js_hi]; rfl

theorem eval.osr.bad_unless_refines (c : Bool) (k : eval.osr.InfoKey) :
    ∃ r, eval.osr.bad_unless c k = ok r ∧ js_rOk r = c := by
  cases c <;> exact ⟨_, rfl, rfl⟩

theorem eval.osr.stats_entry_ok_refines (es : Slice (alloc.vec.Vec U32 × eval.mods_json.V)) (i : Usize)
    (hi : i.val < es.val.length) (hok : ev_VV (es.val[i.val]'hi).1 ∧ ev_vOk (es.val[i.val]'hi).2) :
    eval.osr.stats_entry_ok es i = ok (js_statsP (js_kvS (es.val[i.val]'hi))) := by
  unfold eval.osr.stats_entry_ok
  rw [slice_index_ok es i hi, bind_ok]
  generalize es.val[i.val]'hi = kv at hok ⊢
  obtain ⟨k, v⟩ := kv
  show (do
    let b ← eval.osr.enum_name_hit_result (alloc.vec.Vec.deref k)
    if b then eval.osr.json_int v eval.mods_json.I32_LO_MAG eval.mods_json.I32_HI else ok false) = _
  have hs : ValidStr (alloc.vec.Vec.deref k) := fun u hu => hok.1.1 u (by simpa using hu)
  rw [eval.osr.enum_name_hit_result_refines _ hs]
  simp only [js_statsP, js_kvS, ← js_vstrS_deref, bind_tc_ok, js_ji32 v hok.2]
  split <;> simp_all

theorem eval.osr.stats_entries_ok_refines (es : Slice (alloc.vec.Vec U32 × eval.mods_json.V))
    (hok : ∀ kv ∈ es.val, ev_VV kv.1 ∧ ev_vOk kv.2) :
    eval.osr.stats_entries_ok es = ok ((es.val.map js_kvS).all js_statsP) := by
  have hmax : es.val.length ≤ Usize.max := Slice.length_ineq es
  have H := loop_ok (fun (x : Bool × Usize) => eval.osr.stats_entries_ok_loop.body es x.1 x.2)
    (fun x => es.val.length + 1 - x.2.val - (if x.1 then 0 else 1))
    (fun x => x.2.val ≤ es.val.length ∧
      (x.1 = true → (es.val.map js_kvS).all js_statsP = ((es.val.drop x.2.val).map js_kvS).all js_statsP) ∧
      (x.1 = false → (es.val.map js_kvS).all js_statsP = false))
    (fun y => y = (es.val.map js_kvS).all js_statsP) ?_ (true, 0#usize) ⟨by simp, fun _ => by simp, by simp⟩
  · obtain ⟨y, hy, hq⟩ := H
    unfold eval.osr.stats_entries_ok eval.osr.stats_entries_ok_loop
    rw [show (fun (x : Bool × Usize) => match x with
        | (ok_1, i1) => eval.osr.stats_entries_ok_loop.body es ok_1 i1) =
        (fun x => eval.osr.stats_entries_ok_loop.body es x.1 x.2) from rfl, hy, hq]
  · rintro ⟨b, i⟩ ⟨h1, h2, h3⟩
    simp only at h1 h2 h3 ⊢
    cases b with
    | false => left; exact ⟨false, by simp [eval.osr.stats_entries_ok_loop.body], (h3 rfl).symm⟩
    | true =>
      have h2 := h2 rfl
      by_cases hlt : i.val < es.val.length
      · right
        have hlt' : i < Slice.len es := (slice_lt_len_iff i es).mpr hlt
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
        have he := eval.osr.stats_entry_ok_refines es i hlt (hok _ (List.getElem_mem hlt))
        rw [List.drop_eq_getElem_cons hlt, List.map_cons, List.all_cons] at h2
        refine ⟨(js_statsP (js_kvS (es.val[i.val]'hlt)), i1), by simp [eval.osr.stats_entries_ok_loop.body, hlt', he, hi1],
          ⟨by dsimp only; omega, fun h => ?_, fun h => ?_⟩, ?_⟩
        · simp only at h; rw [h2, h, hi1v]; rfl
        · simp only at h; rw [h2, h]; rfl
        · dsimp only; simp only [↓reduceIte]; split <;> omega
      · left
        have hlt' : ¬ i < Slice.len es := by rw [slice_lt_len_iff]; exact hlt
        refine ⟨true, by simp [eval.osr.stats_entries_ok_loop.body, hlt'], ?_⟩
        rw [h2, List.drop_eq_nil_of_le (by omega)]; rfl

theorem eval.osr.pauses_ok_refines (xs : Slice eval.mods_json.V) (hok : ∀ x ∈ xs.val, ev_vOk x) :
    eval.osr.pauses_ok xs = ok ((xs.val.map ev_vS).all (fun x => jsonInt x i32lo i32hi)) := by
  have hmax : xs.val.length ≤ Usize.max := Slice.length_ineq xs
  have H := loop_ok (fun (x : Bool × Usize) => eval.osr.pauses_ok_loop.body xs x.1 x.2)
    (fun x => xs.val.length + 1 - x.2.val - (if x.1 then 0 else 1))
    (fun x => x.2.val ≤ xs.val.length ∧
      (x.1 = true → (xs.val.map ev_vS).all (fun x => jsonInt x i32lo i32hi) =
        ((xs.val.drop x.2.val).map ev_vS).all (fun x => jsonInt x i32lo i32hi)) ∧
      (x.1 = false → (xs.val.map ev_vS).all (fun x => jsonInt x i32lo i32hi) = false))
    (fun y => y = (xs.val.map ev_vS).all (fun x => jsonInt x i32lo i32hi)) ?_ (true, 0#usize)
    ⟨by simp, fun _ => by simp, by simp⟩
  · obtain ⟨y, hy, hq⟩ := H
    unfold eval.osr.pauses_ok eval.osr.pauses_ok_loop
    rw [show (fun (x : Bool × Usize) => match x with
        | (ok_1, i1) => eval.osr.pauses_ok_loop.body xs ok_1 i1) =
        (fun x => eval.osr.pauses_ok_loop.body xs x.1 x.2) from rfl, hy, hq]
  · rintro ⟨b, i⟩ ⟨h1, h2, h3⟩
    simp only at h1 h2 h3 ⊢
    cases b with
    | false => left; exact ⟨false, by simp [eval.osr.pauses_ok_loop.body], (h3 rfl).symm⟩
    | true =>
      have h2 := h2 rfl
      by_cases hlt : i.val < xs.val.length
      · right
        have hlt' : i < Slice.len xs := (slice_lt_len_iff i xs).mpr hlt
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
        have he := js_ji32 _ (hok _ (List.getElem_mem hlt))
        rw [List.drop_eq_getElem_cons hlt, List.map_cons, List.all_cons] at h2
        refine ⟨(jsonInt (ev_vS (xs.val[i.val]'hlt)) i32lo i32hi, i1), ?_,
          ⟨by dsimp only; omega, fun h => ?_, fun h => ?_⟩, ?_⟩
        · simp only [eval.osr.pauses_ok_loop.body, hlt', if_true, slice_index_ok xs i hlt, bind_ok, he, hi1]
          split <;> simp_all
        · simp only at h; rw [h2, h, hi1v]; rfl
        · simp only at h; rw [h2, h]; rfl
        · dsimp only; simp only [↓reduceIte]; split <;> omega
      · left
        have hlt' : ¬ i < Slice.len xs := by rw [slice_lt_len_iff]; exact hlt
        refine ⟨true, by simp [eval.osr.pauses_ok_loop.body, hlt'], ?_⟩
        rw [h2, List.drop_eq_nil_of_le (by omega)]; rfl
end OsuProofs

namespace OsuProofs
open OsuImpl
theorem js_lit_statistics : String.ofList (litS (Array.to_slice (Array.make 10#usize [ 115#u8, 116#u8, 97#u8, 116#u8, 105#u8, 115#u8, 116#u8, 105#u8, 99#u8, 115#u8 ]))) = "statistics" := by
  simp [litS, Array.to_slice, Array.make]
theorem js_lit_maximum_statistics : String.ofList (litS (Array.to_slice (Array.make 18#usize [ 109#u8, 97#u8, 120#u8, 105#u8, 109#u8, 117#u8, 109#u8, 95#u8, 115#u8, 116#u8, 97#u8, 116#u8, 105#u8, 115#u8, 116#u8, 105#u8, 99#u8, 115#u8 ]))) = "maximum_statistics" := by
  simp [litS, Array.to_slice, Array.make]
theorem js_lit_online_id : String.ofList (litS (Array.to_slice (Array.make 9#usize [ 111#u8, 110#u8, 108#u8, 105#u8, 110#u8, 101#u8, 95#u8, 105#u8, 100#u8 ]))) = "online_id" := by
  simp [litS, Array.to_slice, Array.make]
theorem js_lit_user_id : String.ofList (litS (Array.to_slice (Array.make 7#usize [ 117#u8, 115#u8, 101#u8, 114#u8, 95#u8, 105#u8, 100#u8 ]))) = "user_id" := by
  simp [litS, Array.to_slice, Array.make]
theorem js_lit_total_score_without_mods : String.ofList (litS (Array.to_slice (Array.make 24#usize [ 116#u8, 111#u8, 116#u8, 97#u8, 108#u8, 95#u8, 115#u8, 99#u8, 111#u8, 114#u8, 101#u8, 95#u8, 119#u8, 105#u8, 116#u8, 104#u8, 111#u8, 117#u8, 116#u8, 95#u8, 109#u8, 111#u8, 100#u8, 115#u8 ]))) = "total_score_without_mods" := by
  simp [litS, Array.to_slice, Array.make]
theorem js_lit_client_version : String.ofList (litS (Array.to_slice (Array.make 14#usize [ 99#u8, 108#u8, 105#u8, 101#u8, 110#u8, 116#u8, 95#u8, 118#u8, 101#u8, 114#u8, 115#u8, 105#u8, 111#u8, 110#u8 ]))) = "client_version" := by
  simp [litS, Array.to_slice, Array.make]
theorem js_lit_rank : String.ofList (litS (Array.to_slice (Array.make 4#usize [ 114#u8, 97#u8, 110#u8, 107#u8 ]))) = "rank" := by
  simp [litS, Array.to_slice, Array.make]
theorem js_lit_pauses : String.ofList (litS (Array.to_slice (Array.make 6#usize [ 112#u8, 97#u8, 117#u8, 115#u8, 101#u8, 115#u8 ]))) = "pauses" := by
  simp [litS, Array.to_slice, Array.make]
end OsuProofs
namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr
theorem js_str_eq_dec (k : Slice U32) (hk : ValidStr k) (lit : Slice U8) :
    beatmap.dotnet.str_eq k lit = ok (decide (String.ofList (strS k) = String.ofList (litS lit))) := by
  rw [beatmap.dotnet.str_eq_refines k hk lit]
  congr 2; apply propext; constructor
  · intro h; rw [h]
  · intro h; have := congrArg String.toList h; simpa using this

theorem eval.osr.check_stats_refines (k : eval.osr.InfoKey) (v : eval.mods_json.V) (hv : ev_vOk v) :
    ∃ r, eval.osr.check_stats k v = ok r ∧ js_rOk r = (match ev_vS v with | .obj es => es.all js_statsP | _ => false) := by
  cases v with
  | Obj es =>
    have hok := (ev_vOk_obj es).mp hv
    have h := eval.osr.stats_entries_ok_refines (alloc.vec.Vec.deref es) (by simpa using hok)
    simp only [ms_deref_val] at h
    rw [ev_vS_obj]
    cases hb : (es.val.map js_kvS).all js_statsP
    · exact ⟨.Err (.BadValue k), by simp [eval.osr.check_stats, h, hb], hb.symm⟩
    · exact ⟨.Ok (), by simp [eval.osr.check_stats, h, hb], hb.symm⟩
  | Num _ => exact ⟨_, rfl, rfl⟩
  | VStr _ => exact ⟨_, rfl, rfl⟩
  | Bool _ => exact ⟨_, rfl, rfl⟩
  | Null => exact ⟨_, rfl, rfl⟩
  | Arr xs => exact ⟨_, rfl, by obtain ⟨⟨n, l, h⟩⟩ := xs; rfl⟩

theorem eval.osr.check_client_version_refines (v : eval.mods_json.V) :
    ∃ r, eval.osr.check_client_version v = ok r ∧
      js_rOk r = (match ev_vS v with | .str _ => true | .null => true | _ => false) := by
  cases v with
  | Arr xs => exact ⟨_, rfl, by obtain ⟨⟨n, l, h⟩⟩ := xs; rfl⟩
  | Obj xs => exact ⟨_, rfl, by obtain ⟨⟨n, l, h⟩⟩ := xs; rfl⟩
  | _ => exact ⟨_, rfl, rfl⟩

theorem eval.osr.check_total_without_mods_refines (v : eval.mods_json.V) (hv : ev_vOk v) :
    ∃ r, eval.osr.check_total_without_mods v = ok r ∧
      js_rOk r = (match ev_vS v with | .null => true | w => jsonInt w i64lo i64hi) := by
  have hj := js_ji64 v hv
  cases v with
  | Null => exact ⟨_, rfl, rfl⟩
  | Num t =>
    obtain ⟨r, hr, hrv⟩ := eval.osr.bad_unless_refines (jsonInt (ev_vS (.Num t)) i64lo i64hi) .TotalScoreWithoutMods
    exact ⟨r, by simp only [eval.osr.check_total_without_mods, hj, bind_ok, hr], hrv⟩
  | VStr t =>
    obtain ⟨r, hr, hrv⟩ := eval.osr.bad_unless_refines (jsonInt (ev_vS (.VStr t)) i64lo i64hi) .TotalScoreWithoutMods
    exact ⟨r, by simp only [eval.osr.check_total_without_mods, hj, bind_ok, hr], hrv⟩
  | Bool t =>
    obtain ⟨r, hr, hrv⟩ := eval.osr.bad_unless_refines (jsonInt (ev_vS (.Bool t)) i64lo i64hi) .TotalScoreWithoutMods
    exact ⟨r, by simp only [eval.osr.check_total_without_mods, hj, bind_ok, hr], hrv⟩
  | Arr t =>
    obtain ⟨r, hr, hrv⟩ := eval.osr.bad_unless_refines (jsonInt (ev_vS (.Arr t)) i64lo i64hi) .TotalScoreWithoutMods
    refine ⟨r, by simp only [eval.osr.check_total_without_mods, hj, bind_ok, hr], ?_⟩
    rw [hrv]; obtain ⟨⟨n, l, h⟩⟩ := t; rfl
  | Obj t =>
    obtain ⟨r, hr, hrv⟩ := eval.osr.bad_unless_refines (jsonInt (ev_vS (.Obj t)) i64lo i64hi) .TotalScoreWithoutMods
    refine ⟨r, by simp only [eval.osr.check_total_without_mods, hj, bind_ok, hr], ?_⟩
    rw [hrv]; obtain ⟨⟨n, l, h⟩⟩ := t; rfl
end OsuProofs
namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr
theorem eval.osr.check_rank_refines (v : eval.mods_json.V) (hv : ev_vOk v) :
    ∃ r, eval.osr.check_rank v = ok r ∧
      js_rOk r = (match ev_vS v with | .null => true | .str s => enumName scoreRankNames s | w => jsonInt w i32lo i32hi) := by
  have hj := js_ji32 v hv
  cases v with
  | Null => exact ⟨_, rfl, rfl⟩
  | VStr s =>
    have hs : ev_VV s := hv
    have hs' : ValidStr (alloc.vec.Vec.deref s) := fun u hu => hs.1 u (by simpa using hu)
    obtain ⟨r, hr, hrv⟩ := eval.osr.bad_unless_refines (enumName scoreRankNames (vstrS s)) .Rank
    refine ⟨r, ?_, hrv⟩
    simp only [eval.osr.check_rank, eval.osr.enum_name_rank_refines _ hs', bind_ok, ← js_vstrS_deref, hr]
  | Num t =>
    obtain ⟨r, hr, hrv⟩ := eval.osr.bad_unless_refines (jsonInt (ev_vS (.Num t)) i32lo i32hi) .Rank
    exact ⟨r, by simp only [eval.osr.check_rank, hj, bind_ok, hr], hrv⟩
  | Bool t =>
    obtain ⟨r, hr, hrv⟩ := eval.osr.bad_unless_refines (jsonInt (ev_vS (.Bool t)) i32lo i32hi) .Rank
    exact ⟨r, by simp only [eval.osr.check_rank, hj, bind_ok, hr], hrv⟩
  | Arr t =>
    obtain ⟨r, hr, hrv⟩ := eval.osr.bad_unless_refines (jsonInt (ev_vS (.Arr t)) i32lo i32hi) .Rank
    refine ⟨r, by simp only [eval.osr.check_rank, hj, bind_ok, hr], ?_⟩
    rw [hrv]; obtain ⟨⟨n, l, h⟩⟩ := t; rfl
  | Obj t =>
    obtain ⟨r, hr, hrv⟩ := eval.osr.bad_unless_refines (jsonInt (ev_vS (.Obj t)) i32lo i32hi) .Rank
    refine ⟨r, by simp only [eval.osr.check_rank, hj, bind_ok, hr], ?_⟩
    rw [hrv]; obtain ⟨⟨n, l, h⟩⟩ := t; rfl

theorem eval.osr.check_pauses_refines (v : eval.mods_json.V) (hv : ev_vOk v) :
    ∃ r, eval.osr.check_pauses v = ok r ∧
      js_rOk r = (match ev_vS v with | .arr xs => xs.all (fun x => jsonInt x i32lo i32hi) | _ => false) := by
  cases v with
  | Arr xs =>
    have hok := (ev_vOk_arr xs).mp hv
    have h := eval.osr.pauses_ok_refines (alloc.vec.Vec.deref xs) (by simpa using hok)
    simp only [ms_deref_val] at h
    obtain ⟨r, hr, hrv⟩ := eval.osr.bad_unless_refines ((xs.val.map ev_vS).all (fun x => jsonInt x i32lo i32hi)) .Pauses
    refine ⟨r, by simp only [eval.osr.check_pauses, h, bind_ok, hr], ?_⟩
    rw [hrv, ev_vS_arr]
  | Num _ => exact ⟨_, rfl, rfl⟩
  | VStr _ => exact ⟨_, rfl, rfl⟩
  | Bool _ => exact ⟨_, rfl, rfl⟩
  | Null => exact ⟨_, rfl, rfl⟩
  | Obj xs => exact ⟨_, rfl, by obtain ⟨⟨n, l, h⟩⟩ := xs; rfl⟩

theorem eval.osr.check_member_refines (k : Slice U32) (hk : ValidStr k) (v : eval.mods_json.V) (hv : ev_vOk v) :
    ∃ r, eval.osr.check_member k v = ok r ∧ js_rOk r = js_memberOk (String.ofList (strS k), ev_vS v) := by
  obtain ⟨r1, h1, h1v⟩ := eval.osr.check_stats_refines .Statistics v hv
  obtain ⟨r2, h2, h2v⟩ := eval.osr.check_stats_refines .MaximumStatistics v hv
  obtain ⟨r3, h3, h3v⟩ := eval.osr.bad_unless_refines (jsonInt (ev_vS v) i64lo i64hi) .OnlineId
  obtain ⟨r4, h4, h4v⟩ := eval.osr.bad_unless_refines (jsonInt (ev_vS v) i32lo i32hi) .UserId
  obtain ⟨r5, h5, h5v⟩ := eval.osr.check_total_without_mods_refines v hv
  obtain ⟨r6, h6, h6v⟩ := eval.osr.check_client_version_refines v
  obtain ⟨r7, h7, h7v⟩ := eval.osr.check_rank_refines v hv
  obtain ⟨r8, h8, h8v⟩ := eval.osr.check_pauses_refines v hv
  unfold eval.osr.check_member
  simp only [lift, bind_ok, js_str_eq_dec k hk, js_lit_statistics, js_lit_maximum_statistics, js_lit_online_id,
    js_lit_user_id, js_lit_total_score_without_mods, js_lit_client_version, js_lit_rank, js_lit_pauses,
    js_ji64 v hv, js_ji32 v hv, h1, h2, h3, h4, h5, h6, h7, h8]
  generalize String.ofList (strS k) = S
  unfold js_memberOk
  by_cases e1 : S = "statistics"
  · subst e1; simp [h1v]
  by_cases e2 : S = "maximum_statistics"
  · subst e2; simp [h2v]
  by_cases e3 : S = "online_id"
  · subst e3; simp [h3v]
  by_cases e4 : S = "user_id"
  · subst e4; simp [h4v]
  by_cases e5 : S = "total_score_without_mods"
  · subst e5; simp [h5v]
  by_cases e6 : S = "client_version"
  · subst e6; simp [h6v]
  by_cases e7 : S = "rank"
  · subst e7; simp [h7v]
  by_cases e8 : S = "pauses"
  · subst e8; simp [h8v]
  simp [e1, e2, e3, e4, e5, e6, e7, e8]; rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr
def js_errOf {α ε} : core.result.Result α ε → Option ε
  | .Ok _ => none
  | .Err e => some e
theorem js_csi_body (kvs : Slice (alloc.vec.Vec U32 × eval.mods_json.V)) (i i1 : Usize) (hlt : i.val < kvs.val.length)
    (hlt' : i < Slice.len kvs) (hi1 : i + 1#usize = ok i1) (r : core.result.Result Unit eval.osr.OsrErr)
    (hr : eval.osr.check_member (alloc.vec.Vec.deref (kvs.val[i.val]'hlt).1) (kvs.val[i.val]'hlt).2 = ok r) :
    eval.osr.check_score_info_loop.body kvs none i = ok (.cont (js_errOf r, i1)) := by
  simp only [eval.osr.check_score_info_loop.body, core.option.Option.is_none, Option.isNone_none, if_true, hlt', bind_ok,
    slice_index_ok kvs i hlt]
  rw [show kvs.val[i.val]'hlt = ((kvs.val[i.val]'hlt).1, (kvs.val[i.val]'hlt).2) from rfl]
  simp only [Aeneas.Std.uncurry_apply_pair, hr, bind_ok]
  cases r <;> simp [hi1, js_errOf]

theorem eval.osr.check_score_info_refines (kvs : Slice (alloc.vec.Vec U32 × eval.mods_json.V))
    (hok : ∀ kv ∈ kvs.val, ev_VV kv.1 ∧ ev_vOk kv.2) :
    ∃ r, eval.osr.check_score_info kvs = ok r ∧ js_rOk r = js_isOk (checkScoreInfo (kvs.val.map js_kvS)) := by
  rw [js_check_spec]
  have hmax : kvs.val.length ≤ Usize.max := Slice.length_ineq kvs
  have H := loop_ok (fun (x : Option eval.osr.OsrErr × Usize) => eval.osr.check_score_info_loop.body kvs x.1 x.2)
    (fun x => kvs.val.length + 2 - x.2.val - (if x.1.isSome then 1 else 0))
    (fun x => x.2.val ≤ kvs.val.length ∧
      (x.1 = none → (kvs.val.map js_kvS).all js_memberOk = ((kvs.val.drop x.2.val).map js_kvS).all js_memberOk) ∧
      (x.1.isSome → (kvs.val.map js_kvS).all js_memberOk = false))
    (fun y => y.isNone = (kvs.val.map js_kvS).all js_memberOk) ?_ (none, 0#usize) ⟨by simp, fun _ => by simp, by simp⟩
  · obtain ⟨y, hy, hq⟩ := H
    have hloop : eval.osr.check_score_info_loop kvs none 0#usize = ok y := by
      unfold eval.osr.check_score_info_loop
      rw [show (fun (x : Option eval.osr.OsrErr × Usize) => match x with
          | (err1, i1) => eval.osr.check_score_info_loop.body kvs err1 i1) =
          (fun x => eval.osr.check_score_info_loop.body kvs x.1 x.2) from rfl, hy]
    cases y with
    | none => exact ⟨.Ok (), by simp [eval.osr.check_score_info, hloop], by rw [← hq]; rfl⟩
    | some e => exact ⟨.Err e, by simp [eval.osr.check_score_info, hloop], by rw [← hq]; rfl⟩
  · rintro ⟨e, i⟩ ⟨h1, h2, h3⟩
    simp only at h1 h2 h3 ⊢
    cases e with
    | some e => left; exact ⟨some e, by simp [eval.osr.check_score_info_loop.body], by simp [h3 rfl]⟩
    | none =>
      have h2 := h2 rfl
      by_cases hlt : i.val < kvs.val.length
      · right
        have hlt' : i < Slice.len kvs := (slice_lt_len_iff i kvs).mpr hlt
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
        have hkv := hok _ (List.getElem_mem hlt)
        rw [List.drop_eq_getElem_cons hlt, List.map_cons, List.all_cons] at h2
        have hk' : ValidStr (alloc.vec.Vec.deref (kvs.val[i.val]'hlt).1) := fun u hu => hkv.1.1 u (by simpa using hu)
        obtain ⟨r, hr, hrv⟩ := eval.osr.check_member_refines _ hk' _ hkv.2
        have hb := js_csi_body kvs i i1 hlt hlt' hi1 r hr
        simp only [js_kvS] at h2
        rw [js_vstrS_deref, ← hrv] at h2
        refine ⟨_, hb, ⟨by dsimp only; omega, fun h => ?_, fun h => ?_⟩, ?_⟩
        · cases r with
          | Ok _ => rw [h2, hi1v]; rfl
          | Err _ => simp [js_errOf] at h
        · cases r with
          | Ok _ => simp [js_errOf] at h
          | Err _ => rw [h2]; rfl
        · cases r <;> simp [js_errOf] <;> omega
      · left
        have hlt' : ¬ i < Slice.len kvs := by rw [slice_lt_len_iff]; exact hlt
        refine ⟨none, by simp [eval.osr.check_score_info_loop.body, hlt'], ?_⟩
        rw [h2, List.drop_eq_nil_of_le (by omega)]; rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr
/-- `apiModToMod`'s acronym match (bridge `js_apiModToMod_eq`) -/
def js_acrSpec (o : Option SimJson.V) : Except String (Option String) :=
  match o with
  | some (.str s) => pure (some s)
  | some (.num t) => pure (some t)
  | some (.bool b) => pure (some (if b then "True" else "False"))
  | some .null | none => pure none
  | _ => throw "JsonSerializationException: bad acronym"
/-- `apiModToMod`'s settings match (bridge `js_apiModToMod_eq`) -/
def js_setSpec (o : Option SimJson.V) : Except String (List (String × JsonVal)) :=
  match o with
  | some (.obj ss) => pure (ss.map fun (k, x) => (k, SimJson.toSetting x))
  | none => pure []
  | some .null => throw "NullReferenceException: mod settings are null"
  | _ => throw "JsonSerializationException: bad mod settings"

def js_last (kvs : List (String × SimJson.V)) (k : String) : Option SimJson.V := (kvs.reverse.find? (·.1 == k)).map (·.2)

theorem js_apiModToMod_eq (kvs : List (String × SimJson.V)) : apiModToMod (.obj kvs) =
    (do
      let acronym ← js_acrSpec (js_last kvs "acronym")
      let settings ← js_setSpec (js_last kvs "settings")
      match acronym with
      | some a => return Settings.toMod a settings
      | none => return { acronym := "", known := false }) := by
  unfold apiModToMod js_acrSpec js_setSpec js_last
  dsimp only
  generalize (List.find? (fun x => x.1 == "acronym") kvs.reverse) = A
  generalize (List.find? (fun x => x.1 == "settings") kvs.reverse) = B
  rcases A with _ | ⟨_, _ | _ | _ | _ | _ | _⟩ <;> rcases B with _ | ⟨_, _ | _ | _ | _ | _ | _⟩ <;> rfl
end OsuProofs
namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr
def js_eRel {α β ε} (f : α → β) : core.result.Result α ε → Except String β → Prop
  | .Ok a, .ok b => f a = b
  | .Err _, .error _ => True
  | _, _ => False

theorem js_lit_str_ok (s : Slice U8) (hs : s.val.length < 2^62) :
    ∃ v, beatmap.dotnet.lit_str s = ok v ∧ vstrS v = String.ofList (litS s) ∧ VValid v ∧ v.val.length < 2^62 := by
  obtain ⟨v, hv, hvv⟩ := beatmap.dotnet.lit_str_refines s
  have hl : v.val.length = s.val.length := by have := congrArg List.length hvv; simpa using this
  refine ⟨v, hv, ?_, ?_, by omega⟩
  · unfold vstrS litS; congr 1
    have : v.val.map chOf = (v.val.map (·.val)).map Char.ofNat := by simp [chOf, Function.comp_def]
    rw [this, hvv]; simp [Function.comp_def]
  · intro u hu
    have hu' : u.val ∈ v.val.map (·.val) := List.mem_map_of_mem hu
    rw [hvv] at hu'
    obtain ⟨x, -, hx⟩ := List.mem_map.mp hu'
    rw [← hx]; exact byte_valid x

theorem js_lit_True : String.ofList (litS (Array.to_slice (Array.make 4#usize [ 84#u8, 114#u8, 117#u8, 101#u8 ]))) = "True" := by
  simp [litS, Array.to_slice, Array.make]
theorem js_lit_False : String.ofList (litS (Array.to_slice (Array.make 5#usize [ 70#u8, 97#u8, 108#u8, 115#u8, 101#u8 ]))) = "False" := by
  simp [litS, Array.to_slice, Array.make]

theorem eval.osr.api_acronym_refines (v : eval.mods_json.V) (hv : ev_vOk v) :
    ∃ r, eval.osr.api_acronym v = ok r ∧ js_eRel (Option.map vstrS) r (js_acrSpec (some (ev_vS v))) ∧
      ∀ a, r = .Ok (some a) → VValid a ∧ a.val.length < 2^62 := by
  cases v with
  | Num t =>
    have ht : ev_VV t := hv
    exact ⟨.Ok (some t), by simp [eval.osr.api_acronym, clone_vec_u32], rfl, by
      intro a h; simp at h; subst h; exact ht⟩
  | VStr t =>
    have ht : ev_VV t := hv
    exact ⟨.Ok (some t), by simp [eval.osr.api_acronym, clone_vec_u32], rfl, by
      intro a h; simp at h; subst h; exact ht⟩
  | Bool b =>
    cases b with
    | true =>
      obtain ⟨w, hw, hwv, hwok, hwl⟩ := js_lit_str_ok (Array.to_slice (Array.make 4#usize [ 84#u8, 114#u8, 117#u8, 101#u8 ]))
        (by simp [Array.to_slice, Array.make])
      refine ⟨.Ok (some w), by simp [eval.osr.api_acronym, lift, hw], ?_, by intro a h; simp at h; subst h; exact ⟨hwok, hwl⟩⟩
      show some (vstrS w) = some _; rw [hwv, js_lit_True]; rfl
    | false =>
      obtain ⟨w, hw, hwv, hwok, hwl⟩ := js_lit_str_ok (Array.to_slice (Array.make 5#usize [ 70#u8, 97#u8, 108#u8, 115#u8, 101#u8 ]))
        (by simp [Array.to_slice, Array.make])
      refine ⟨.Ok (some w), by simp [eval.osr.api_acronym, lift, hw], ?_, by intro a h; simp at h; subst h; exact ⟨hwok, hwl⟩⟩
      show some (vstrS w) = some _; rw [hwv, js_lit_False]; rfl
  | Null => exact ⟨.Ok none, rfl, rfl, by intro a h; simp at h⟩
  | Arr xs => exact ⟨.Err .BadAcronym, rfl, by obtain ⟨⟨n, l, h⟩⟩ := xs; trivial, by intro a h; simp at h⟩
  | Obj xs => exact ⟨.Err .BadAcronym, rfl, by obtain ⟨⟨n, l, h⟩⟩ := xs; trivial, by intro a h; simp at h⟩

theorem eval.osr.api_settings_refines (v : eval.mods_json.V) (hv : ev_vOk v) :
    ∃ r, eval.osr.api_settings v = ok r ∧ js_eRel (fun st => msSetS st.val) r (js_setSpec (some (ev_vS v))) ∧
      ∀ st, r = .Ok st → ∀ p ∈ st.val, VValid p.1 ∧ p.1.val.length < 2^62 ∧ JOk p.2 := by
  cases v with
  | Obj kvs =>
    obtain ⟨r, hr, hrs, hrok⟩ := eval.mods_json.settings_of_refines (alloc.vec.Vec.deref kvs)
      (by simpa using (ev_vOk_obj kvs).mp hv)
    refine ⟨.Ok r, by simp [eval.osr.api_settings, hr], ?_, by intro st h; simp at h; subst h; exact hrok⟩
    simp only [js_eRel, ev_vS_obj, js_setSpec, pure, Except.pure]
    rw [hrs]; simp
  | Num _ => exact ⟨_, rfl, trivial, by intro st h; simp at h⟩
  | VStr _ => exact ⟨_, rfl, trivial, by intro st h; simp at h⟩
  | Bool _ => exact ⟨_, rfl, trivial, by intro st h; simp at h⟩
  | Null => exact ⟨_, rfl, trivial, by intro st h; simp at h⟩
  | Arr xs => exact ⟨_, rfl, by obtain ⟨⟨n, l, h⟩⟩ := xs; trivial, by intro st h; simp at h⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr
def js_mRel' : core.result.Result beatmap.mod_settings.ModConfig eval.osr.OsrErr → Except String ModConfig → Prop
  | .Ok m, .ok M => mcS m = M ∧ js_mcOk m
  | .Err _, .error _ => True
  | _, _ => False

theorem js_last_none (kvs : List (alloc.vec.Vec U32 × eval.mods_json.V)) (lit : Slice U8) (k : String)
    (hl : String.ofList (litS lit) = k) (h : js_lastIdx (js_keyP lit) kvs = none) :
    js_last (kvs.map js_kvS) k = none := by
  have hf := js_lastIdx_none _ _ h
  unfold js_last
  rw [← List.map_reverse, List.find?_map]
  have : ((fun x : String × SimJson.V => x.1 == k) ∘ js_kvS) = js_keyP lit := by
    funext kv; simp [js_keyP, js_kvS, hl]
  rw [this, hf]; rfl

theorem js_last_some (kvs : List (alloc.vec.Vec U32 × eval.mods_json.V)) (lit : Slice U8) (k : String)
    (hl : String.ofList (litS lit) = k) (j : Nat) (h : js_lastIdx (js_keyP lit) kvs = some j) :
    ∃ hj : j < kvs.length, js_last (kvs.map js_kvS) k = some (ev_vS (kvs[j]'hj).2) := by
  obtain ⟨hj, -, hf⟩ := js_lastIdx_mem _ _ _ h
  refine ⟨hj, ?_⟩
  unfold js_last
  rw [← List.map_reverse, List.find?_map]
  have : ((fun x : String × SimJson.V => x.1 == k) ∘ js_kvS) = js_keyP lit := by
    funext kv; simp [js_keyP, js_kvS, hl]
  rw [this, hf]; rfl

theorem js_default_mc : mcS ({ acronym := alloc.vec.Vec.new U32, known := false, settings := alloc.vec.Vec.new (U32 × beatmap.mod_settings.SettingValue) } : beatmap.mod_settings.ModConfig) = { acronym := "", known := false } := by
  simp [mcS, vstrS, valsS]

theorem js_default_ok : js_mcOk ({ acronym := alloc.vec.Vec.new U32, known := false, settings := alloc.vec.Vec.new (U32 × beatmap.mod_settings.SettingValue) } : beatmap.mod_settings.ModConfig) := by
  simp [js_mcOk, VValid, KeysOk]
end OsuProofs
namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

theorem js_vec_index_usize_pair (kvs : alloc.vec.Vec (alloc.vec.Vec U32 × eval.mods_json.V)) (i : Usize)
    (h : i.val < kvs.val.length) :
    alloc.vec.Vec.index_usize kvs i = ok ((kvs.val[i.val]'h).1, (kvs.val[i.val]'h).2) := vec_index_usize_ok _ _ h

theorem js_tomod_some (h64 : System.Platform.numBits = 64) (a : alloc.vec.Vec U32) (ha : VValid a ∧ a.val.length < 2^62)
    (st : alloc.vec.Vec (alloc.vec.Vec U32 × beatmap.mod_settings.JsonVal))
    (hst : ∀ p ∈ st.val, VValid p.1 ∧ p.1.val.length < 2^62 ∧ JOk p.2) :
    ∃ mc, beatmap.mod_settings.to_mod (alloc.vec.Vec.deref a) (alloc.vec.Vec.deref st) = ok mc ∧
      mcS mc = Settings.toMod (vstrS a) (msSetS st.val) ∧ js_mcOk mc := by
  obtain ⟨mc, hmc, hmcv, hmok⟩ := js_to_mod_ok (alloc.vec.Vec.deref a) (vvalid_deref _ ha.1) (by simpa using ha.2)
    (alloc.vec.Vec.deref st) (fun p hp => (hst p (by simpa using hp)).1)
    (fun p hp => js_JOk' h64 _ (hst p (by simpa using hp)).2.2)
  refine ⟨mc, hmc, ?_, hmok⟩
  rw [hmcv, ← js_vstrS_deref]; simp

theorem eval.osr.api_mod_to_mod_refines (h64 : System.Platform.numBits = 64) (v : eval.mods_json.V) (hv : ev_vOk v) :
    ∃ r, eval.osr.api_mod_to_mod v = ok r ∧ js_mRel' r (apiModToMod (ev_vS v)) := by
  cases v with
  | Obj kvs =>
    have hok := (ev_vOk_obj kvs).mp hv
    have hk : js_kOk (alloc.vec.Vec.deref kvs).val := fun kv h => (hok kv (by simpa using h)).1.1
    rw [ev_vS_obj, show (fun kv : alloc.vec.Vec U32 × eval.mods_json.V => (vstrS kv.1, ev_vS kv.2)) = js_kvS from rfl,
      js_apiModToMod_eq]
    obtain ⟨o, ho, hov⟩ := eval.mods_json.find_last_refines (alloc.vec.Vec.deref kvs)
      (Array.to_slice (Array.make 7#usize [ 97#u8, 99#u8, 114#u8, 111#u8, 110#u8, 121#u8, 109#u8 ])) hk
    obtain ⟨o1, ho1, ho1v⟩ := eval.mods_json.find_last_refines (alloc.vec.Vec.deref kvs)
      (Array.to_slice (Array.make 8#usize [ 115#u8, 101#u8, 116#u8, 116#u8, 105#u8, 110#u8, 103#u8, 115#u8 ])) hk
    simp only [ms_deref_val] at hov ho1v
    have hSnone : o1 = none → js_last (kvs.val.map js_kvS) "settings" = none := by
      intro h; subst h; exact js_last_none _ _ _ js_lit_settings (by simpa using ho1v.symm)
    have hSsome : ∀ i : Usize, o1 = some i → ∃ hi : i.val < kvs.val.length,
        js_last (kvs.val.map js_kvS) "settings" = some (ev_vS (kvs.val[i.val]'hi).2) := by
      intro i h; subst h; exact js_last_some _ _ _ js_lit_settings i.val (by simpa using ho1v.symm)
    cases o with
    | none =>
      rw [js_last_none _ _ _ js_lit_acronym (by simpa using hov.symm)]
      simp only [js_acrSpec, pure_bind]
      cases o1 with
      | none =>
        rw [hSnone rfl]
        exact ⟨.Ok ⟨alloc.vec.Vec.new U32, false, alloc.vec.Vec.new _⟩, by (simp only [eval.osr.api_mod_to_mod, lift, bind_ok, Aeneas.Std.uncurry_apply_pair, ho, ho1]) <;> rfl, ⟨js_default_mc, js_default_ok⟩⟩
      | some i =>
        obtain ⟨hi, hB⟩ := hSsome i rfl
        rw [hB]
        obtain ⟨rs, hrs, hrsv, hrsok⟩ := eval.osr.api_settings_refines _ (hok _ (List.getElem_mem hi)).2
        cases rs with
        | Ok st =>
          refine ⟨_, by (simp only [eval.osr.api_mod_to_mod, lift, bind_ok, Aeneas.Std.uncurry_apply_pair, ho, ho1, js_vec_index_pair kvs i hi, js_vec_index_usize_pair kvs i hi, hrs]) <;> rfl, ?_⟩
          revert hrsv; cases js_setSpec (some (ev_vS (kvs.val[i.val]'hi).2)) with
          | ok _ => intro _; exact ⟨js_default_mc, js_default_ok⟩
          | error _ => intro h; exact h.elim
        | Err e =>
          refine ⟨_, by (simp only [eval.osr.api_mod_to_mod, lift, bind_ok, Aeneas.Std.uncurry_apply_pair, ho, ho1, js_vec_index_pair kvs i hi, js_vec_index_usize_pair kvs i hi, hrs]) <;> rfl, ?_⟩
          revert hrsv; cases js_setSpec (some (ev_vS (kvs.val[i.val]'hi).2)) with
          | ok _ => intro h; exact h.elim
          | error _ => intro _; trivial
    | some j =>
      obtain ⟨hj, hA⟩ := js_last_some _ _ _ js_lit_acronym j.val (by simpa using hov.symm)
      rw [hA]
      obtain ⟨ra, hra, hrav, hraok⟩ := eval.osr.api_acronym_refines _ (hok _ (List.getElem_mem hj)).2
      cases ra with
      | Err e =>
        refine ⟨_, by (simp only [eval.osr.api_mod_to_mod, lift, bind_ok, Aeneas.Std.uncurry_apply_pair, ho, js_vec_index_pair kvs j hj, js_vec_index_usize_pair kvs j hj, hra]) <;> rfl, ?_⟩
        revert hrav; cases js_acrSpec (some (ev_vS (kvs.val[j.val]'hj).2)) with
        | ok _ => intro h; exact h.elim
        | error _ => intro _; trivial
      | Ok a =>
        have hA2 : js_acrSpec (some (ev_vS (kvs.val[j.val]'hj).2)) = .ok (a.map vstrS) := by
          revert hrav; cases js_acrSpec (some (ev_vS (kvs.val[j.val]'hj).2)) with
          | ok _ => intro h; rw [← h]
          | error _ => intro h; exact h.elim
        rw [hA2]
        cases o1 with
        | none =>
          rw [hSnone rfl]
          cases a with
          | none =>
            exact ⟨.Ok ⟨alloc.vec.Vec.new U32, false, alloc.vec.Vec.new _⟩, by (simp only [eval.osr.api_mod_to_mod, lift, bind_ok, Aeneas.Std.uncurry_apply_pair, ho, ho1, js_vec_index_pair kvs j hj, js_vec_index_usize_pair kvs j hj, hra]) <;> rfl,
              ⟨js_default_mc, js_default_ok⟩⟩
          | some a =>
            obtain ⟨mc, hmc, hmcv, hmok⟩ := js_tomod_some h64 a (hraok a rfl) (alloc.vec.Vec.new _) (by simp)
            refine ⟨_, by (simp only [eval.osr.api_mod_to_mod, lift, bind_ok, Aeneas.Std.uncurry_apply_pair, ho, ho1, js_vec_index_pair kvs j hj, js_vec_index_usize_pair kvs j hj, hra, hmc]) <;> rfl, ?_⟩
            exact ⟨by rw [hmcv]; simp [msSetS], hmok⟩
        | some i =>
          obtain ⟨hi, hB⟩ := hSsome i rfl
          rw [hB]
          obtain ⟨rs, hrs, hrsv, hrsok⟩ := eval.osr.api_settings_refines _ (hok _ (List.getElem_mem hi)).2
          cases rs with
          | Err e =>
            refine ⟨_, by (simp only [eval.osr.api_mod_to_mod, lift, bind_ok, Aeneas.Std.uncurry_apply_pair, ho, ho1, js_vec_index_pair kvs j hj, js_vec_index_usize_pair kvs j hj, hra,
              js_vec_index_pair kvs i hi, js_vec_index_usize_pair kvs i hi, hrs]) <;> rfl, ?_⟩
            revert hrsv; cases js_setSpec (some (ev_vS (kvs.val[i.val]'hi).2)) with
            | ok _ => intro h; exact h.elim
            | error _ => intro _; trivial
          | Ok st =>
            have hB2 : js_setSpec (some (ev_vS (kvs.val[i.val]'hi).2)) = .ok (msSetS st.val) := by
              revert hrsv; cases js_setSpec (some (ev_vS (kvs.val[i.val]'hi).2)) with
              | ok _ => intro h; rw [← h]
              | error _ => intro h; exact h.elim
            rw [hB2]
            cases a with
            | none =>
              exact ⟨.Ok ⟨alloc.vec.Vec.new U32, false, alloc.vec.Vec.new _⟩, by (simp only [eval.osr.api_mod_to_mod, lift, bind_ok, Aeneas.Std.uncurry_apply_pair, ho, ho1, js_vec_index_pair kvs j hj, js_vec_index_usize_pair kvs j hj, hra,
                js_vec_index_pair kvs i hi, js_vec_index_usize_pair kvs i hi, hrs]) <;> rfl, ⟨js_default_mc, js_default_ok⟩⟩
            | some a =>
              obtain ⟨mc, hmc, hmcv, hmok⟩ := js_tomod_some h64 a (hraok a rfl) st (hrsok st rfl)
              refine ⟨_, by (simp only [eval.osr.api_mod_to_mod, lift, bind_ok, Aeneas.Std.uncurry_apply_pair, ho, ho1, js_vec_index_pair kvs j hj, js_vec_index_usize_pair kvs j hj, hra,
                js_vec_index_pair kvs i hi, js_vec_index_usize_pair kvs i hi, hrs, hmc]) <;> rfl, ?_⟩
              exact ⟨hmcv, hmok⟩
  | Num _ => exact ⟨_, rfl, trivial⟩
  | VStr _ => exact ⟨_, rfl, trivial⟩
  | Bool _ => exact ⟨_, rfl, trivial⟩
  | Null => exact ⟨_, rfl, trivial⟩
  | Arr xs => exact ⟨_, rfl, by obtain ⟨⟨n, l, h⟩⟩ := xs; trivial⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr
def js_lRel' : core.result.Result (alloc.vec.Vec beatmap.mod_settings.ModConfig) eval.osr.OsrErr →
    Except String (List ModConfig) → Prop
  | .Ok ms, .ok MS => ms.val.map mcS = MS ∧ ∀ m ∈ ms.val, js_mcOk m
  | .Err _, .error _ => True
  | _, _ => False

theorem eval.osr.api_mods_refines (h64 : System.Platform.numBits = 64) (xs : Slice eval.mods_json.V)
    (hok : ∀ x ∈ xs.val, ev_vOk x) :
    ∃ r, eval.osr.api_mods xs = ok r ∧ js_lRel' r ((xs.val.map ev_vS).mapM apiModToMod) := by
  have hmax : xs.val.length ≤ Usize.max := Slice.length_ineq xs
  have H := loop_ok (fun (x : alloc.vec.Vec beatmap.mod_settings.ModConfig × Option eval.osr.OsrErr × Usize) =>
      eval.osr.api_mods_loop.body xs x.1 x.2.1 x.2.2)
    (fun x => xs.val.length + 1 - x.2.2.val - (if x.2.1.isSome then 1 else 0))
    (fun x => x.2.2.val ≤ xs.val.length ∧ x.1.val.length ≤ x.2.2.val ∧
      ((x.2.1 = none ∧ ((xs.val.take x.2.2.val).map ev_vS).mapM apiModToMod = .ok (x.1.val.map mcS) ∧
          ∀ m ∈ x.1.val, js_mcOk m) ∨
       (∃ e, x.2.1 = some e ∧ ∃ s, (xs.val.map ev_vS).mapM apiModToMod = .error s)))
    (fun y => (y.2 = none ∧ (xs.val.map ev_vS).mapM apiModToMod = .ok (y.1.val.map mcS) ∧ ∀ m ∈ y.1.val, js_mcOk m) ∨
       (∃ e, y.2 = some e ∧ ∃ s, (xs.val.map ev_vS).mapM apiModToMod = .error s)) ?_
    (alloc.vec.Vec.new _, none, 0#usize) ⟨by simp, by simp, Or.inl ⟨rfl, by simp, by simp⟩⟩
  · obtain ⟨⟨out, err⟩, hy, hq⟩ := H
    unfold eval.osr.api_mods eval.osr.api_mods_loop
    rw [show (fun (x : alloc.vec.Vec beatmap.mod_settings.ModConfig × Option eval.osr.OsrErr × Usize) =>
        match x with
        | (out1, err1, i1) => eval.osr.api_mods_loop.body xs out1 err1 i1) =
        (fun x => eval.osr.api_mods_loop.body xs x.1 x.2.1 x.2.2) from rfl, hy]
    rcases hq with ⟨h1, h2, h3⟩ | ⟨e, h1, h2⟩
    · simp only at h1; subst h1
      exact ⟨.Ok out, by simp, by rw [h2]; exact ⟨rfl, h3⟩⟩
    · simp only at h1; subst h1
      obtain ⟨s, h2⟩ := h2
      exact ⟨.Err e, by simp, by rw [h2]; trivial⟩
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
        obtain ⟨r, hr, hrel⟩ := eval.osr.api_mod_to_mod_refines h64 _ hx
        cases r with
        | Ok m =>
          have hout : out.val.length < Usize.max := by omega
          refine ⟨(vpush out m hout, none, i1), ?_, ⟨by dsimp only; omega, by simp [vpush_val]; omega, Or.inl ⟨rfl, ?_, ?_⟩⟩,
            by simp; omega⟩
          · simp [eval.osr.api_mods_loop.body, hlt', slice_index_ok xs i hlt, hr, vec_push_ok out m hout, hi1]
          · rw [hi1v, htake, List.map_append, List.map_singleton, js_mapM_snoc _ _ _ _ h3]
            revert hrel; cases apiModToMod (ev_vS (xs.val[i.val]'hlt)) with
            | ok M => rintro ⟨hm, -⟩; simp [vpush_val, hm]; rfl
            | error _ => intro h; exact h.elim
          · intro m' hm'; simp only [vpush_val, List.mem_append, List.mem_singleton] at hm'
            rcases hm' with hm' | rfl
            · exact h4 _ hm'
            · revert hrel; cases apiModToMod (ev_vS (xs.val[i.val]'hlt)) with
              | ok M => rintro ⟨-, hm⟩; exact hm
              | error _ => intro h; exact h.elim
        | Err e =>
          refine ⟨(out, some e, i1), ?_, ⟨by dsimp only; omega, by dsimp only; omega, Or.inr ⟨e, rfl, ?_⟩⟩,
            by simp; omega⟩
          · simp [eval.osr.api_mods_loop.body, hlt', slice_index_ok xs i hlt, hr, hi1]
          · rw [hfull, List.map_append, List.map_cons]
            revert hrel; cases hs : apiModToMod (ev_vS (xs.val[i.val]'hlt)) with
            | ok M => intro h; exact h.elim
            | error s => intro _; exact ⟨s, js_mapM_err _ _ _ _ _ _ h3 hs⟩
      · left
        have hlt' : ¬ i < Slice.len xs := by rw [slice_lt_len_iff]; exact hlt
        refine ⟨(out, none), by simp [eval.osr.api_mods_loop.body, hlt'], Or.inl ⟨rfl, ?_, h4⟩⟩
        rw [← h3, List.take_of_length_le (by omega)]
    · left
      exact ⟨(out, some e), by simp [eval.osr.api_mods_loop.body], Or.inr ⟨e, rfl, h3⟩⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr
/-- the object case of `decodeScoreInfo` (bridge `js_decodeScoreInfo_eq`) -/
def js_simSpec (kvs : List (String × SimJson.V)) : Except String (List ModConfig) := do
  checkScoreInfo kvs
  match js_last kvs "mods" with
  | none => pure []
  | some (.arr xs) => xs.mapM apiModToMod
  | some .null => throw "NullReferenceException: mods is null"
  | some _ => throw "JsonSerializationException: mods is not an array"

def js_trailP (c : Char) : Bool := !(c == ' ' || c == '\n' || c == '\t' || c == '\r')

theorem js_decodeScoreInfo_eq (text : String) : decodeScoreInfo text =
    match (SimJson.value).run text.toList with
    | .error e => .error (toString "JsonReaderException: " ++ toString e)
    | .ok (v, rest) =>
      if rest.any js_trailP then .error "JsonReaderException: Additional text encountered after finished reading JSON content."
      else match v with
        | .obj kvs => js_simSpec kvs
        | .null => .error "NullReferenceException: lazer score info is null"
        | _ => .error "JsonSerializationException: lazer score info is not an object" := by
  unfold decodeScoreInfo
  cases (SimJson.value).run text.toList with
  | error e => rfl
  | ok p =>
    obtain ⟨v, rest⟩ := p
    dsimp only
    simp only [pure_bind]
    by_cases h : (rest.any fun c => !(c == ' ' || c == '\n' || c == '\t' || c == '\r')) = true
    · rw [if_pos h, if_pos (show rest.any js_trailP = true from h)]; rfl
    · rw [if_neg h, if_neg (show ¬ rest.any js_trailP = true from h)]
      cases v <;> rfl

theorem eval.osr.has_trailing_refines (s : Slice U32) (p : Usize) (hp : p.val ≤ s.val.length) :
    eval.osr.has_trailing s p = ok (((strS s).drop p.val).any js_trailP) := by
  have hmax := slice_len_lt s
  have H := loop_ok (fun (x : Bool × Usize) => eval.osr.has_trailing_loop.body s x.1 x.2)
    (fun x => s.val.length - x.2.val)
    (fun x => x.2.val ≤ s.val.length ∧ (x.1 || ((strS s).drop x.2.val).any js_trailP) = ((strS s).drop p.val).any js_trailP)
    (fun y => y = ((strS s).drop p.val).any js_trailP) ?_ (false, p) ⟨hp, by simp⟩
  · obtain ⟨y, hy, hq⟩ := H
    unfold eval.osr.has_trailing eval.osr.has_trailing_loop
    rw [show (fun (x : Bool × Usize) => match x with
        | (r1, i1) => eval.osr.has_trailing_loop.body s r1 i1) =
        (fun x => eval.osr.has_trailing_loop.body s x.1 x.2) from rfl, hy, hq]
  · rintro ⟨r, i⟩ ⟨h1, h2⟩
    simp only at h1 h2 ⊢
    by_cases hlt : i.val < s.val.length
    · right
      have hlt' : i < Slice.len s := (slice_lt_len_iff i s).mpr hlt
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
      rw [strS_drop s i.val hlt] at h2
      generalize hc : s.val[i.val]'hlt = c at h2
      refine ⟨(r || js_trailP (chOf c), i1), ?_, ⟨by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
      · simp only [eval.osr.has_trailing_loop.body, hlt', if_true, slice_index_ok s i hlt, hc, bind_ok,
          eval.mods_json.is_ws_refines, hi1]
        have hT : js_trailP (chOf c) = !ev_isWs (chOf c) := rfl
        rw [hT]; cases ev_isWs (chOf c) <;> simp
      · dsimp only; rw [hi1v, ← h2]; simp only [List.any_cons, Bool.or_assoc]
    · left
      have hlt' : ¬ i < Slice.len s := by rw [slice_lt_len_iff]; exact hlt
      refine ⟨r, by simp [eval.osr.has_trailing_loop.body, hlt'], ?_⟩
      rw [← h2, List.drop_eq_nil_of_le (by simp [strS_length]; omega)]; simp
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr
theorem js_lit_mods : String.ofList (litS (Array.to_slice (Array.make 4#usize [ 109#u8, 111#u8, 100#u8, 115#u8 ]))) = "mods" := by
  simp [litS, Array.to_slice, Array.make]

theorem js_slice_index_pair (kvs : Slice (alloc.vec.Vec U32 × eval.mods_json.V)) (i : Usize)
    (h : i.val < kvs.val.length) :
    Slice.index_usize kvs i = ok ((kvs.val[i.val]'h).1, (kvs.val[i.val]'h).2) := slice_index_ok _ _ h

theorem eval.osr.score_info_mods_refines (h64 : System.Platform.numBits = 64)
    (kvs : Slice (alloc.vec.Vec U32 × eval.mods_json.V)) (hok : ∀ kv ∈ kvs.val, ev_VV kv.1 ∧ ev_vOk kv.2) :
    ∃ r, eval.osr.score_info_mods kvs = ok r ∧ js_lRel' r (js_simSpec (kvs.val.map js_kvS)) := by
  obtain ⟨rc, hrc, hrcv⟩ := eval.osr.check_score_info_refines kvs hok
  cases rc with
  | Err e =>
    refine ⟨.Err e, by simp only [eval.osr.score_info_mods, hrc, bind_ok], ?_⟩
    unfold js_simSpec
    revert hrcv
    cases checkScoreInfo (kvs.val.map js_kvS) with
    | error m => intro _; trivial
    | ok _ => intro h; simp [js_rOk, js_isOk] at h
  | Ok u =>
    have hC : checkScoreInfo (kvs.val.map js_kvS) = .ok () := by
      revert hrcv
      cases checkScoreInfo (kvs.val.map js_kvS) with
      | error m => intro h; simp [js_rOk, js_isOk] at h
      | ok _ => intro _; rfl
    have hk : js_kOk kvs.val := fun kv h => (hok kv h).1.1
    obtain ⟨o, ho, hov⟩ := eval.mods_json.find_last_refines kvs
      (Array.to_slice (Array.make 4#usize [ 109#u8, 111#u8, 100#u8, 115#u8 ])) hk
    unfold js_simSpec
    rw [hC]
    cases o with
    | none =>
      rw [js_last_none _ _ _ js_lit_mods (by simpa using hov.symm)]
      exact ⟨.Ok (alloc.vec.Vec.new _), by simp only [eval.osr.score_info_mods, hrc, bind_ok, lift, ho], by simp [js_lRel']⟩
    | some i =>
      obtain ⟨hi, hM⟩ := js_last_some _ _ _ js_lit_mods i.val (by simpa using hov.symm)
      rw [hM]
      have hkv := hok _ (List.getElem_mem hi)
      have hR : eval.osr.score_info_mods kvs = (match (kvs.val[i.val]'hi).2 with
          | .Arr xs => eval.osr.api_mods (alloc.vec.Vec.deref xs)
          | .Null => ok (core.result.Result.Err eval.osr.OsrErr.ModsNull)
          | _ => ok (core.result.Result.Err eval.osr.OsrErr.ModsNotArray)) := by
        simp only [eval.osr.score_info_mods, hrc, bind_ok, lift, ho, js_slice_index_pair kvs i hi,
          Aeneas.Std.uncurry_apply_pair]
        split <;> simp_all
      rw [hR]
      generalize (kvs.val[i.val]'hi) = kv at hkv ⊢
      obtain ⟨k, v⟩ := kv
      cases v with
      | Arr xs =>
        obtain ⟨r, hr, hrel⟩ := eval.osr.api_mods_refines h64 (alloc.vec.Vec.deref xs)
          (by simpa using (ev_vOk_arr xs).mp hkv.2)
        refine ⟨r, hr, ?_⟩
        simpa [ev_vS_arr] using hrel
      | Null => exact ⟨_, rfl, trivial⟩
      | Num _ => exact ⟨_, rfl, trivial⟩
      | VStr _ => exact ⟨_, rfl, trivial⟩
      | Bool _ => exact ⟨_, rfl, trivial⟩
      | Obj xs => exact ⟨_, rfl, by obtain ⟨⟨n, l, h⟩⟩ := xs; trivial⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr
/-- TOP (score info): `osr::decode_score_info` refines `decodeScoreInfo`: same mods (well-formed, `js_mcOk` =
`ev_mcOk`) or both reject. 64-bit (for `JOk'` of string settings and `len + 8 ≤ usize::MAX`). -/
theorem eval.osr.decode_score_info_refines (h64 : System.Platform.numBits = 64) (text : Slice U32) (hs : ValidStr text)
    (h62 : text.val.length < 2^62) :
    ∃ r, eval.osr.decode_score_info text = ok r ∧ js_lRel' r (decodeScoreInfo (String.ofList (strS text))) := by
  have hm : Usize.max = 2^64 - 1 := by simp [Usize.max, Usize.numBits, h64]
  have hlen : text.val.length + 8 ≤ Usize.max := by rw [hm]; omega
  rw [js_decodeScoreInfo_eq, String.toList_ofList]
  obtain ⟨r, hr, hrel⟩ := eval.mods_json.value_refines text hs hlen h62 0#usize (by simp)
  simp only [UScalar.ofNatCore_val_eq, List.drop_zero] at hrel
  revert hrel
  cases (SimJson.value).run (strS text) with
  | error m =>
    cases r with
    | Ok _ => intro h; exact h.elim
    | Err e => intro _; exact ⟨.Err (.JsonReader e), by simp [eval.osr.decode_score_info, hr], trivial⟩
  | ok wL =>
    obtain ⟨w, L⟩ := wL
    cases r with
    | Err _ => intro h; exact h.elim
    | Ok vq =>
      obtain ⟨v, q⟩ := vq
      rintro ⟨hw, hL, -, hq, hok⟩
      subst hw hL
      have ht := eval.osr.has_trailing_refines text q hq
      by_cases hb : ((strS text).drop q.val).any js_trailP = true
      · refine ⟨.Err .JsonTrailing, ?_, by simp only [hb, if_true]; trivial⟩
        simp only [eval.osr.decode_score_info, hr, bind_ok, Aeneas.Std.uncurry_apply_pair, ht, hb, if_true]
      · have hb' : ((strS text).drop q.val).any js_trailP = false := by simpa using hb
        simp only [hb', Bool.false_eq_true, if_false]
        have hR : eval.osr.decode_score_info text = (match v with
            | .Obj kvs => eval.osr.score_info_mods (alloc.vec.Vec.deref kvs)
            | .Null => ok (core.result.Result.Err eval.osr.OsrErr.InfoNull)
            | _ => ok (core.result.Result.Err eval.osr.OsrErr.InfoNotObject)) := by
          simp only [eval.osr.decode_score_info, hr, bind_ok, Aeneas.Std.uncurry_apply_pair, ht, hb', Bool.false_eq_true,
            if_false]
          cases v <;> rfl
        rw [hR]
        cases v with
        | Obj kvs =>
          obtain ⟨r, hr', hrel'⟩ := eval.osr.score_info_mods_refines h64 (alloc.vec.Vec.deref kvs)
            (by simpa using (ev_vOk_obj kvs).mp hok)
          refine ⟨r, hr', ?_⟩
          rw [ev_vS_obj]; simp only [ms_deref_val] at hrel'; exact hrel'
        | Null => exact ⟨_, rfl, trivial⟩
        | Num _ => exact ⟨_, rfl, trivial⟩
        | VStr _ => exact ⟨_, rfl, trivial⟩
        | Bool _ => exact ⟨_, rfl, trivial⟩
        | Arr xs => exact ⟨_, rfl, by obtain ⟨⟨n, l, h⟩⟩ := xs; trivial⟩
end OsuProofs

