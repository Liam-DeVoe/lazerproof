/-
`eval::mods_json` (Rust, `impl/osu_eval_core/src/eval/mods_json.rs`) refines `OsuModel/Sim/ModsJson.lean`
(`SimJson`): the strict JSON reader, `toSetting`, `parseMods`.

Representation: the spec parser `StateT (List Char) (Except String)` runs on the remaining input; the Rust parser
takes the input slice `s` and a position `p`: remaining = `(strS s).drop p` (`ev_pRel`). Values: `ev_vS`
(`mods_json::V` ↦ `SimJson.V`, structural on the nested inductive). Errors: `ev_jeS` (the exact spec messages).
Side conditions: the input is a string of Unicode scalar values (`ValidStr`) shorter than `2^62`.
Spec normal forms (`ev_valueF_*`, `ev_arr_loop`, `ev_obj_loop`) are proved by unfolding the `StateT` program
(`StateT.run_bind` …) and `Lean.Loop.forIn_eq_of_monadTail` for the `repeat` loops.
-/
import OsuProofs.Generated.EvalFuns
import OsuProofs.Beatmap.ModSettings
import OsuProofs.Net.Parse
import OsuProofs.Beatmap.Text
import OsuProofs.LoopsR
import OsuModel.Sim.ModsJson
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl Aeneas.Data.ListN

/-! ## Representation -/

-- Rust `mods_json::V` ↦ spec `SimJson.V` (structural on the nested inductive)
mutual
def ev_vS : eval.mods_json.V → SimJson.V
  | .Num t => .num (vstrS t)
  | .VStr t => .str (vstrS t)
  | .Bool b => .bool b
  | .Null => .null
  | .Arr ⟨⟨_, l, _⟩⟩ => .arr (ev_vlS l)
  | .Obj ⟨⟨_, l, _⟩⟩ => .obj (ev_kvlS l)
def ev_vlS : {n : Nat} → ListN eval.mods_json.V n → List SimJson.V
  | _, .nil => []
  | _, .cons x t => ev_vS x :: ev_vlS t
def ev_kvlS : {n : Nat} → ListN (alloc.vec.Vec U32 × eval.mods_json.V) n → List (String × SimJson.V)
  | _, .nil => []
  | _, .cons kv t => (vstrS kv.1, ev_vS kv.2) :: ev_kvlS t
end

theorem ev_vlS_eq {n} (l : ListN eval.mods_json.V n) : ev_vlS l = l.toList.map ev_vS := by
  induction l with
  | nil => rfl
  | cons x t ih => simp [ev_vlS, ListN.toList, ih]
theorem ev_kvlS_eq {n} (l : ListN (alloc.vec.Vec U32 × eval.mods_json.V) n) :
    ev_kvlS l = l.toList.map fun kv => (vstrS kv.1, ev_vS kv.2) := by
  induction l with
  | nil => rfl
  | cons x t ih => simp [ev_kvlS, ListN.toList, ih]
@[simp] theorem ev_vS_arr (xs : alloc.vec.Vec eval.mods_json.V) : ev_vS (.Arr xs) = .arr (xs.val.map ev_vS) := by
  obtain ⟨⟨n, l, h⟩⟩ := xs; simp [ev_vS, ev_vlS_eq]; rfl
@[simp] theorem ev_vS_obj (kvs : alloc.vec.Vec (alloc.vec.Vec U32 × eval.mods_json.V)) :
    ev_vS (.Obj kvs) = .obj (kvs.val.map fun kv => (vstrS kv.1, ev_vS kv.2)) := by
  obtain ⟨⟨n, l, h⟩⟩ := kvs; simp [ev_vS, ev_kvlS_eq]; rfl
@[simp] theorem ev_vS_num (t : alloc.vec.Vec U32) : ev_vS (.Num t) = .num (vstrS t) := rfl
@[simp] theorem ev_vS_str (t : alloc.vec.Vec U32) : ev_vS (.VStr t) = .str (vstrS t) := rfl
@[simp] theorem ev_vS_bool (b : Bool) : ev_vS (.Bool b) = .bool b := rfl
@[simp] theorem ev_vS_null : ev_vS .Null = .null := rfl

/-- the parser's error messages (`mods_json::text::json_err`) -/
def ev_jeS : eval.mods_json.JsonErr → String
  | .Expected c => s!"expected {chOf c}"
  | .BadU => "bad \\u"
  | .Unterminated => "unterminated string"
  | .BadArray => "bad array"
  | .BadObject => "bad object"
  | .BadValue => "bad value"
  | .Fuel => "internal: JSON nesting fuel exhausted"

/-- A Rust parser result at input `s` vs the spec parser's `Except String (β × remaining)`: same value and
remaining input `(strS s).drop q` (`q ≤ len`), or the same message. -/
def ev_pRel {α β} (f : α → β) (s : Slice U32) :
    core.result.Result (α × Usize) eval.mods_json.JsonErr → Except String (β × List Char) → Prop
  | .Ok (a, q), .ok (b, L) => f a = b ∧ L = (strS s).drop q.val ∧ q.val ≤ s.val.length
  | .Err e, .error m => m = ev_jeS e
  | _, _ => False

/-! ## Leaves -/

/-- `ws`'s character test -/
def ev_isWs (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'
theorem ev_wsL_cons (c : Char) (cs : List Char) :
    SimJson.wsL (c :: cs) = if ev_isWs c then SimJson.wsL cs else c :: cs := rfl

theorem eval.mods_json.is_ws_refines (c : U32) : eval.mods_json.is_ws c = ok (ev_isWs (chOf c)) := by
  unfold ev_isWs
  rw [chOf_beq_lit c ' ' (by decide), chOf_beq_lit c '\n' (by decide), chOf_beq_lit c '\t' (by decide),
    chOf_beq_lit c '\r' (by decide)]
  unfold eval.mods_json.is_ws
  by_cases h1 : c.val = 32 <;> by_cases h2 : c.val = 10 <;> by_cases h3 : c.val = 9 <;>
    simp [h1, h2, h3, UScalar.eq_equiv]

theorem eval.mods_json.ws_refines (s : Slice U32) (p : Usize) (hp : p.val ≤ s.val.length) :
    ∃ q, eval.mods_json.ws s p = ok q ∧ (strS s).drop q.val = SimJson.wsL ((strS s).drop p.val) ∧
      p.val ≤ q.val ∧ q.val ≤ s.val.length := by
  let T := SimJson.wsL ((strS s).drop p.val)
  unfold eval.mods_json.ws eval.mods_json.ws_loop
  refine loop_ok _ (fun (j : Usize) => s.val.length - j.val)
    (fun (j : Usize) => p.val ≤ j.val ∧ j.val ≤ s.val.length ∧ SimJson.wsL ((strS s).drop j.val) = T)
    (fun (q : Usize) => (strS s).drop q.val = T ∧ p.val ≤ q.val ∧ q.val ≤ s.val.length) ?_ p ?_
  · rintro j ⟨hpj, hjl, hT⟩
    have hl := slice_len_lt s
    by_cases hlt : j.val < s.val.length
    · rw [strS_drop s j.val hlt] at hT
      by_cases hw : ev_isWs (chOf (s.val[j.val]'hlt)) = true
      · right
        obtain ⟨j1, hj1, hv⟩ := usize_add_one j (by omega)
        refine ⟨j1, by simp [eval.mods_json.ws_loop.body, (slice_lt_len_iff j s).mpr hlt, slice_index_ok s j hlt,
          eval.mods_json.is_ws_refines, hw, hj1], ⟨by omega, by omega, ?_⟩, by omega⟩
        rw [hv, ← hT, ev_wsL_cons, if_pos hw]
      · left
        refine ⟨j, by simp [eval.mods_json.ws_loop.body, (slice_lt_len_iff j s).mpr hlt, slice_index_ok s j hlt,
          eval.mods_json.is_ws_refines, hw], ?_, hpj, hjl⟩
        rw [strS_drop s j.val hlt, ← hT, ev_wsL_cons, if_neg hw]
    · left
      have hlt' : ¬ j < Slice.len s := by rw [slice_lt_len_iff]; exact hlt
      refine ⟨j, by simp [eval.mods_json.ws_loop.body, hlt'], ?_, hpj, hjl⟩
      have e : (strS s).drop j.val = [] := List.drop_eq_nil_of_le (by simp [strS_length]; omega)
      rw [e] at hT ⊢; rw [← hT]; rfl
  · exact ⟨le_refl _, hp, rfl⟩

end OsuProofs

namespace OsuProofs
open OsuImpl
theorem ev_expect_spec (c : Char) (L : List Char) : SimJson.expect c L =
    match SimJson.wsL L with
    | d :: cs => if c == d then .ok ((), cs) else .error s!"expected {c}"
    | [] => .error s!"expected {c}" := by
  unfold SimJson.expect SimJson.ws
  show StateT.run _ L = _
  simp only [StateT.run_bind, StateT.run_modify, StateT.run_get]
  cases h : SimJson.wsL L with
  | nil => rfl
  | cons d cs =>
    by_cases hc : c = d
    · subst hc; simp
    · simp [hc]
end OsuProofs

namespace OsuProofs
open OsuImpl
abbrev EvP := StateT (List Char) (Except String)
def ev_arrBody (fuel : Nat) : Unit → Array SimJson.V → EvP (ForInStep (Array SimJson.V)) := fun _ xs => do
  let v ← SimJson.valueF fuel
  modify SimJson.wsL
  match (← get) with
  | ',' :: r => do set r; pure (ForInStep.yield (xs.push v))
  | ']' :: r => do set r; pure (ForInStep.done (xs.push v))
  | _ => do throw "bad array"; pure (ForInStep.yield (xs.push v))
def ev_objBody (fuel : Nat) : Unit → Array (String × SimJson.V) → EvP (ForInStep (Array (String × SimJson.V))) := fun _ kvs => do
  SimJson.expect '"'
  let k ← SimJson.strBody []
  SimJson.expect ':'
  let v ← SimJson.valueF fuel
  modify SimJson.wsL
  match (← get) with
  | ',' :: r => do set r; pure (ForInStep.yield (kvs.push (k, v)))
  | '}' :: r => do set r; pure (ForInStep.done (kvs.push (k, v)))
  | _ => do throw "bad object"; pure (ForInStep.yield (kvs.push (k, v)))

theorem ev_valueF_arr (fuel : Nat) (L cs : List Char) (h : SimJson.wsL L = '[' :: cs) :
    SimJson.valueF (fuel+1) L =
      if (SimJson.wsL cs).head? == some ']' then .ok (.arr [], (SimJson.wsL cs).tail)
      else ((forIn Lean.Loop.mk #[] (ev_arrBody fuel) : EvP _).run (SimJson.wsL cs)).map
        fun r => (SimJson.V.arr r.1.toList, r.2) := by
  unfold SimJson.valueF SimJson.ws
  show StateT.run _ L = _
  simp only [StateT.run_bind, StateT.run_modify, StateT.run_get, h, pure_bind, StateT.run_set]
  split
  · rfl
  · show (StateT.run (forIn Lean.Loop.mk #[] (ev_arrBody fuel)) (SimJson.wsL cs) >>= _) = _
    cases StateT.run (forIn Lean.Loop.mk #[] (ev_arrBody fuel)) (SimJson.wsL cs) <;> rfl
end OsuProofs

namespace OsuProofs
open OsuImpl
theorem ev_arr_loop (fuel : Nat) (xs : Array SimJson.V) (M : List Char) :
    (forIn Lean.Loop.mk xs (ev_arrBody fuel) : EvP _).run M =
      match SimJson.valueF fuel M with
      | .error e => .error e
      | .ok (v, M1) => match SimJson.wsL M1 with
        | ',' :: r => (forIn Lean.Loop.mk (xs.push v) (ev_arrBody fuel) : EvP _).run r
        | ']' :: r => .ok (xs.push v, r)
        | _ => .error "bad array" := by
  show StateT.run (Lean.Loop.forIn _ _ _) M = _
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [StateT.run_bind, ev_arrBody, StateT.run_modify, StateT.run_get, pure_bind]
  rw [show StateT.run (SimJson.valueF fuel) M = SimJson.valueF fuel M from rfl]
  cases SimJson.valueF fuel M with
  | error e => rfl
  | ok r =>
    obtain ⟨v, M1⟩ := r
    simp only [except_bind_ok]
    split
    · rename_i hh; simp only [hh]; rfl
    · rename_i hh; simp only [hh]; rfl
    · rename_i h1 h2
      generalize hW : SimJson.wsL M1 = W at *
      rfl
end OsuProofs

namespace OsuProofs
open OsuImpl
theorem ev_valueF_obj (fuel : Nat) (L cs : List Char) (h : SimJson.wsL L = '{' :: cs) :
    SimJson.valueF (fuel+1) L =
      if (SimJson.wsL cs).head? == some '}' then .ok (.obj [], (SimJson.wsL cs).tail)
      else ((forIn Lean.Loop.mk #[] (ev_objBody fuel) : EvP _).run (SimJson.wsL cs)).map
        fun r => (SimJson.V.obj r.1.toList, r.2) := by
  unfold SimJson.valueF SimJson.ws
  show StateT.run _ L = _
  simp only [StateT.run_bind, StateT.run_modify, StateT.run_get, h, pure_bind, StateT.run_set]
  split
  · rfl
  · show (StateT.run (forIn Lean.Loop.mk #[] (ev_objBody fuel)) (SimJson.wsL cs) >>= _) = _
    cases StateT.run (forIn Lean.Loop.mk #[] (ev_objBody fuel)) (SimJson.wsL cs) <;> rfl

theorem ev_valueF_true (fuel : Nat) (L cs : List Char) (h : SimJson.wsL L = 't' :: 'r' :: 'u' :: 'e' :: cs) :
    SimJson.valueF (fuel+1) L = .ok (.bool true, cs) := by
  unfold SimJson.valueF SimJson.ws
  show StateT.run _ L = _
  simp only [StateT.run_bind, StateT.run_modify, StateT.run_get, h, pure_bind]; rfl
theorem ev_valueF_false (fuel : Nat) (L cs : List Char) (h : SimJson.wsL L = 'f' :: 'a' :: 'l' :: 's' :: 'e' :: cs) :
    SimJson.valueF (fuel+1) L = .ok (.bool false, cs) := by
  unfold SimJson.valueF SimJson.ws
  show StateT.run _ L = _
  simp only [StateT.run_bind, StateT.run_modify, StateT.run_get, h, pure_bind]; rfl
theorem ev_valueF_null (fuel : Nat) (L cs : List Char) (h : SimJson.wsL L = 'n' :: 'u' :: 'l' :: 'l' :: cs) :
    SimJson.valueF (fuel+1) L = .ok (.null, cs) := by
  unfold SimJson.valueF SimJson.ws
  show StateT.run _ L = _
  simp only [StateT.run_bind, StateT.run_modify, StateT.run_get, h, pure_bind]; rfl

def ev_isNumChar (c : Char) : Bool := c.isDigit || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E'

theorem ev_valueF_num (fuel : Nat) (L : List Char) (h1 : (SimJson.wsL L).head? ≠ some '"')
    (h2 : (SimJson.wsL L).head? ≠ some '[') (h3 : (SimJson.wsL L).head? ≠ some '{')
    (h4 : ¬ ['t','r','u','e'] <+: SimJson.wsL L) (h5 : ¬ ['f','a','l','s','e'] <+: SimJson.wsL L)
    (h6 : ¬ ['n','u','l','l'] <+: SimJson.wsL L) :
    SimJson.valueF (fuel+1) L = (let cs := SimJson.wsL L; let t := cs.takeWhile fun c => c.isDigit || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E'
      if t.isEmpty then .error "bad value" else .ok (.num (String.ofList t), cs.drop t.length)) := by
  unfold SimJson.valueF SimJson.ws
  show StateT.run _ L = _
  simp only [StateT.run_bind, StateT.run_modify, StateT.run_get, pure_bind]
  generalize SimJson.wsL L = M at *
  split
  all_goals first
    | (simp_all; done)
    | (split <;> rfl)

theorem ev_valueF_zero (L : List Char) : SimJson.valueF 0 L = .error "internal: JSON nesting fuel exhausted" := rfl

theorem ev_obj_loop (fuel : Nat) (kvs : Array (String × SimJson.V)) (M : List Char) :
    (forIn Lean.Loop.mk kvs (ev_objBody fuel) : EvP _).run M =
      match SimJson.expect '"' M with
      | .error e => .error e
      | .ok (_, M1) => match SimJson.strBodyL [] M1 with
        | .error e => .error e
        | .ok (k, M2) => match SimJson.expect ':' M2 with
          | .error e => .error e
          | .ok (_, M3) => match SimJson.valueF fuel M3 with
            | .error e => .error e
            | .ok (v, M4) => match SimJson.wsL M4 with
              | ',' :: r => (forIn Lean.Loop.mk (kvs.push (k, v)) (ev_objBody fuel) : EvP _).run r
              | '}' :: r => .ok (kvs.push (k, v), r)
              | _ => .error "bad object" := by
  show StateT.run (Lean.Loop.forIn _ _ _) M = _
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [StateT.run_bind, ev_objBody, StateT.run_modify, StateT.run_get, pure_bind]
  rw [show StateT.run (SimJson.expect '"') M = SimJson.expect '"' M from rfl]
  cases SimJson.expect '"' M with
  | error e => rfl
  | ok r1 =>
    obtain ⟨_, M1⟩ := r1
    simp only [except_bind_ok]
    rw [show StateT.run (SimJson.strBody []) M1 = SimJson.strBodyL [] M1 from rfl]
    cases SimJson.strBodyL [] M1 with
    | error e => rfl
    | ok r2 =>
      obtain ⟨k, M2⟩ := r2
      simp only [except_bind_ok]
      rw [show StateT.run (SimJson.expect ':') M2 = SimJson.expect ':' M2 from rfl]
      cases SimJson.expect ':' M2 with
      | error e => rfl
      | ok r3 =>
        obtain ⟨_, M3⟩ := r3
        simp only [except_bind_ok]
        rw [show StateT.run (SimJson.valueF fuel) M3 = SimJson.valueF fuel M3 from rfl]
        cases SimJson.valueF fuel M3 with
        | error e => rfl
        | ok r4 =>
          obtain ⟨v, M4⟩ := r4
          simp only [except_bind_ok]
          split
          · rename_i hh; simp only [hh]; rfl
          · rename_i hh; simp only [hh]; rfl
          · rfl
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem ev_isDigit_chOf (u : U32) (h : u.val.isValidChar) :
    (chOf u).isDigit = (decide (48 ≤ u.val) && decide (u.val ≤ 57)) := by
  have e : (chOf u).val.toNat = u.val := chOf_toNat u h
  unfold Char.isDigit
  by_cases h1 : 48 ≤ u.val <;> by_cases h2 : u.val ≤ 57 <;>
    simp [UInt32.le_iff_toNat_le, UInt32.lt_iff_toNat_lt, e, h1, h2] <;> omega

theorem eval.mods_json.is_digit_refines (c : U32) (h : c.val.isValidChar) :
    eval.mods_json.is_digit c = ok (chOf c).isDigit := by
  rw [ev_isDigit_chOf c h]; unfold eval.mods_json.is_digit
  by_cases h1 : 48 ≤ c.val <;> simp [h1, UScalar.le_equiv]

theorem ev_u32_sub (x y : U32) (h : y.val ≤ x.val) : ∃ z, x - y = ok z ∧ z.val = x.val - y.val := by
  obtain ⟨z, hz, hv, _⟩ := eq_ok_of_spec (U32.sub_spec (x := x) (y := y) h)
  exact ⟨z, hz, hv⟩
theorem ev_u32_add (x y : U32) (h : x.val + y.val ≤ U32.max) : ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (U32.add_spec (x := x) (y := y) h)
  exact ⟨z, hz, by simpa using hv⟩
theorem ev_u64_add (x y : U64) (h : x.val + y.val ≤ U64.max) : ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (U64.add_spec (x := x) (y := y) h)
  exact ⟨z, hz, by simpa using hv⟩
theorem ev_u64_mul (x y : U64) (h : x.val * y.val ≤ U64.max) : ∃ z, x * y = ok z ∧ z.val = x.val * y.val := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (U64.mul_spec (x := x) (y := y) h)
  exact ⟨z, hz, by simpa using hv⟩
theorem ev_usize_add (i k : Usize) (h : i.val + k.val ≤ Usize.max) :
    ∃ z, i + k = ok z ∧ z.val = i.val + k.val := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (Usize.add_spec (x := i) (y := k) h)
  exact ⟨z, hz, by simpa using hv⟩

theorem eval.mods_json.hex_val_refines (c : U32) (h : c.val.isValidChar) :
    ∃ r, eval.mods_json.hex_val c = ok r ∧ r.val = SimJson.hexVal (chOf c) ∧ r.val ≤ 1114112 + 10 := by
  have e : (chOf c).val.toNat = c.val := chOf_toNat c h
  have hb : c.val < 1114112 := by unfold Nat.isValidChar at h; omega
  unfold eval.mods_json.hex_val SimJson.hexVal
  rw [eval.mods_json.is_digit_refines c h]
  have l1 : ('a' ≤ chOf c) ↔ 97 ≤ c.val := by
    rw [Char.le_def, UInt32.le_iff_toNat_le]; rw [e]; rfl
  have l2 : (chOf c ≤ 'f') ↔ c.val ≤ 102 := by
    rw [Char.le_def, UInt32.le_iff_toNat_le]; rw [e]; rfl
  have et : (chOf c).toNat = c.val := e
  by_cases hd : (chOf c).isDigit = true
  · have hd' := hd; rw [ev_isDigit_chOf c h] at hd'; simp at hd'
    obtain ⟨z, hz, hv⟩ := ev_u32_sub c 48#u32 (by simp; omega)
    refine ⟨UScalar.cast .U64 z, by simp only [hd, if_true, hz, bind_ok], ?_, ?_⟩
    · simp [hv, et, hd]
    · simp [hv]; omega
  · simp only [hd, Bool.false_eq_true, if_false]
    by_cases ha : 97 ≤ c.val <;> by_cases hf : c.val ≤ 102
    · obtain ⟨z, hz, hv⟩ := ev_u32_sub c 97#u32 (by simp; omega)
      obtain ⟨z2, hz2, hv2⟩ := ev_u32_add z 10#u32 (by rw [hv]; scalar_tac)
      refine ⟨UScalar.cast .U64 z2, by simp [UScalar.le_equiv, ha, hf, hz, hz2], ?_, ?_⟩
      · simp [hv2, hv, l1.mpr ha, l2.mpr hf, et, hd]
      · simp [hv2, hv]; omega
    all_goals by_cases h65 : 65 ≤ c.val
    · obtain ⟨z, hz, hv⟩ := ev_u32_sub c 65#u32 (by simp; omega)
      obtain ⟨z2, hz2, hv2⟩ := ev_u64_add (UScalar.cast .U64 z) 10#u64 (by simp [hv]; scalar_tac)
      refine ⟨z2, by simp [UScalar.le_equiv, ha, hf, h65, hz, hz2, lift], ?_, ?_⟩
      · simp [hv2, hv, l1, l2, et, ha, hf]
      · simp [hv2, hv]; omega
    · omega
    · obtain ⟨z, hz, hv⟩ := ev_u32_sub c 65#u32 (by simp; omega)
      obtain ⟨z2, hz2, hv2⟩ := ev_u64_add (UScalar.cast .U64 z) 10#u64 (by simp [hv]; scalar_tac)
      refine ⟨z2, by simp [UScalar.le_equiv, ha, hf, h65, hz, hz2, lift], ?_, ?_⟩
      · simp [hv2, hv, l1, l2, et, ha, hf]
      · simp [hv2, hv]; omega
    · refine ⟨10#u64, by simp [UScalar.le_equiv, ha, hf, h65], ?_, by simp⟩
      simp [l1, l2, et, ha, hf]; omega
    · omega
    · omega
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem eval.mods_json.char_of_nat_refines (n : U64) :
    ∃ r, eval.mods_json.char_of_nat n = ok r ∧ chOf r = Char.ofNat n.val ∧ r.val.isValidChar := by
  unfold eval.mods_json.char_of_nat
  by_cases h1 : n.val < 55296
  · refine ⟨UScalar.cast .U32 n, by simp [UScalar.lt_equiv, h1], ?_, ?_⟩
    · have : (UScalar.cast .U32 n).val = n.val := by simp [UScalar.cast_val_eq]; omega
      simp [chOf, this]
    · have : (UScalar.cast .U32 n).val = n.val := by simp [UScalar.cast_val_eq]; omega
      rw [this]; unfold Nat.isValidChar; omega
  · by_cases h2 : 57343 < n.val ∧ n.val < 1114112
    · have : (UScalar.cast .U32 n).val = n.val := by simp [UScalar.cast_val_eq]; omega
      refine ⟨UScalar.cast .U32 n, by simp [UScalar.lt_equiv, h1, h2.1, h2.2], ?_, ?_⟩
      · simp [chOf, this]
      · rw [this]; unfold Nat.isValidChar; omega
    · refine ⟨0#u32, ?_, ?_, ?_⟩
      · by_cases h3 : 57343 < n.val <;> simp [UScalar.lt_equiv, h1, h3] <;> omega
      · have hv : ¬ n.val.isValidChar := by unfold Nat.isValidChar; omega
        simp [chOf, Char.ofNat, hv]; intro _; rfl
      · simp; decide

/-- the one-character escapes of `strBody` (`\n \t \r \b \f`; others stand for themselves) -/
def ev_esc (c : Char) : Char :=
  if c = 'n' then '\n' else if c = 't' then '\t' else if c = 'r' then '\r' else if c = 'b' then '\x08'
  else if c = 'f' then '\x0c' else c

theorem eval.mods_json.escape_char_refines (e : U32) (h : e.val.isValidChar) :
    ∃ r, eval.mods_json.escape_char e = ok r ∧ chOf r = ev_esc (chOf e) ∧ r.val.isValidChar := by
  have he : ∀ c : Char, c.toNat ≠ 0 → (chOf e = c ↔ e.val = c.toNat) := fun c hc => chOf_eq_lit e c hc
  unfold eval.mods_json.escape_char ev_esc
  split
  any_goals (refine ⟨_, rfl, ?_, ?_⟩ <;> decide)
  rename_i h1 h2 h3 h4 h5
  have k : ∀ (c : Char) (lit : U32), c.toNat ≠ 0 → lit.val = c.toNat → (e = lit → False) → ¬ chOf e = c :=
    fun c lit hc hl hne hh => hne (UScalar.eq_of_val_eq (by rw [(he c hc).mp hh, hl]))
  refine ⟨e, rfl, ?_, h⟩
  rw [if_neg (k 'n' 110#u32 (by decide) (by decide) h1), if_neg (k 't' 116#u32 (by decide) (by decide) h2),
    if_neg (k 'r' 114#u32 (by decide) (by decide) h3), if_neg (k 'b' 98#u32 (by decide) (by decide) h4),
    if_neg (k 'f' 102#u32 (by decide) (by decide) h5)]
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem ev_strBodyL_esc (acc : List Char) (e : Char) (cs : List Char) (he : e ≠ 'u') :
    SimJson.strBodyL acc ('\\' :: e :: cs) = SimJson.strBodyL (ev_esc e :: acc) cs := by
  rw [SimJson.strBodyL.eq_def]
  simp only
  split <;> simp_all [ev_esc]

theorem ev_strBodyL_u (acc : List Char) (a b c d : Char) (cs : List Char) :
    SimJson.strBodyL acc ('\\' :: 'u' :: a :: b :: c :: d :: cs) =
      SimJson.strBodyL (Char.ofNat (((SimJson.hexVal a * 16 + SimJson.hexVal b) * 16 + SimJson.hexVal c) * 16 +
        SimJson.hexVal d) :: acc) cs := by
  rw [SimJson.strBodyL.eq_def]; rfl

theorem ev_strBodyL_badu (acc : List Char) (cs : List Char) (h : cs.length < 4) :
    SimJson.strBodyL acc ('\\' :: 'u' :: cs) = .error "bad \\u" := by
  rw [SimJson.strBodyL.eq_def]
  match cs, h with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl

theorem ev_strBodyL_quote (acc cs : List Char) :
    SimJson.strBodyL acc ('"' :: cs) = .ok (String.ofList acc.reverse, cs) := by rw [SimJson.strBodyL.eq_def]; rfl
theorem ev_strBodyL_bs_end (acc : List Char) :
    SimJson.strBodyL acc ['\\'] = SimJson.strBodyL ('\\' :: acc) [] := by rw [SimJson.strBodyL.eq_def]; rfl
theorem ev_strBodyL_other (acc cs : List Char) (c : Char) (h1 : c ≠ '"') (h2 : c ≠ '\\') :
    SimJson.strBodyL acc (c :: cs) = SimJson.strBodyL (c :: acc) cs := by
  rw [SimJson.strBodyL.eq_def]; split <;> simp_all
theorem ev_strBodyL_nil (acc : List Char) : SimJson.strBodyL acc [] = .error "unterminated string" := by
  rw [SimJson.strBodyL.eq_def]
end OsuProofs

namespace OsuProofs
open OsuImpl

/-- result of the `str_body` loop vs `strBodyL` -/
def ev_sbRel (s : Slice U32) (p0 : Nat) (y : alloc.vec.Vec U32 × Usize × Option eval.mods_json.JsonErr)
    (R : Except String (String × List Char)) : Prop :=
  match y.2.2 with
  | none => R = .ok (vstrS y.1, (strS s).drop y.2.1.val) ∧ y.2.1.val ≤ s.val.length ∧ (∀ u ∈ y.1.val, u.val.isValidChar) ∧
      p0 ≤ y.2.1.val ∧ y.1.val.length ≤ y.2.1.val
  | some e => R = .error (ev_jeS e)

theorem ev_sbRel_mono (s : Slice U32) {a b : Nat} (h : a ≤ b) (y) (R) : ev_sbRel s b y R → ev_sbRel s a y R := by
  unfold ev_sbRel; split
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, h3, by omega, h5⟩
  · exact id

theorem ev_sb_fin (s : Slice U32) (n : Usize) (acc : alloc.vec.Vec U32) (p : Usize) (d : Bool)
    (e : Option eval.mods_json.JsonErr) (h : d = true ∨ e.isSome = true) :
    eval.mods_json.str_body_loop s n acc p d e = ok (acc, p, e) := by
  unfold eval.mods_json.str_body_loop; rw [loop_unfold]
  rcases h with h | h
  · subst h; simp [eval.mods_json.str_body_loop.body]
  · obtain ⟨e', rfl⟩ := Option.isSome_iff_exists.mp h
    cases d <;> simp [eval.mods_json.str_body_loop.body]

theorem ev_sb_step (s : Slice U32) (n : Usize) (acc : alloc.vec.Vec U32) (p : Usize) (x)
    (h : eval.mods_json.str_body_loop.body s n acc p false none = ok (.cont x)) :
    eval.mods_json.str_body_loop s n acc p false none =
      eval.mods_json.str_body_loop s n x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  conv => lhs; unfold eval.mods_json.str_body_loop
  rw [loop_unfold]; simp only [h, bind_ok]; rfl

theorem ev_str_body_loop (s : Slice U32) (hs : ValidStr s) (hlen : s.val.length + 8 ≤ Usize.max) :
    ∀ (p : Usize) (acc : alloc.vec.Vec U32), p.val ≤ s.val.length → acc.val.length ≤ p.val →
      (∀ u ∈ acc.val, u.val.isValidChar) →
      ∃ y, eval.mods_json.str_body_loop s (Slice.len s) acc p false none = ok y ∧
        ev_sbRel s p.val y (SimJson.strBodyL (acc.val.map chOf).reverse ((strS s).drop p.val)) := by
  intro p
  induction hk : s.val.length - p.val using Nat.strong_induction_on generalizing p with
  | _ k ih =>
    intro acc hp hacc hv
    have hmax : s.val.length ≤ Usize.max := slice_len_lt s
    have hn : (Slice.len s).val = s.val.length := by simp
    by_cases hlt : p.val < s.val.length
    · have hc := hs.get p.val hlt
      have hd := strS_drop s p.val hlt
      have hlt' : p < Slice.len s := (slice_lt_len_iff p s).mpr hlt
      have hnge : ¬ (p ≥ Slice.len s) := by simp [ge_iff_le, UScalar.le_equiv]; omega
      have hidx := slice_index_ok s p hlt
      generalize hcv : s.val[p.val]'hlt = c at hc hd hidx
      obtain ⟨p1, hp1, hp1v⟩ := usize_add_one p (by omega)
      have hpush : acc.val.length < Usize.max := by omega
      by_cases h34 : c.val = 34
      · have hb : eval.mods_json.str_body_loop.body s (Slice.len s) acc p false none =
            ok (.cont (acc, p1, true, none)) := by
          simp [eval.mods_json.str_body_loop.body, hnge, hidx, hp1, UScalar.eq_equiv, h34]
        refine ⟨_, by rw [ev_sb_step s _ acc p _ hb, ev_sb_fin _ _ _ _ _ _ (Or.inl rfl)], ?_⟩
        have hq : chOf c = '"' := (chOf_eq_lit c '"' (by decide)).mpr h34
        simp only [ev_sbRel, hd, hq, ev_strBodyL_quote, List.reverse_reverse, hp1v]
        exact ⟨rfl, by omega, hv, by omega, by omega⟩
      by_cases h92 : c.val = 92
      · have hq : chOf c = '\\' := (chOf_eq_lit c '\\' (by decide)).mpr h92
        by_cases hlt1 : p1.val < s.val.length
        · have hlt1' : p1 < Slice.len s := (slice_lt_len_iff p1 s).mpr hlt1
          have hc1 := hs.get p1.val hlt1
          have hd1 := strS_drop s p1.val hlt1
          have hidx1 := slice_index_ok s p1 hlt1
          generalize hev : s.val[p1.val]'hlt1 = e at hc1 hd1 hidx1
          obtain ⟨p2, hp2, hp2v⟩ := ev_usize_add p 2#usize (by simp; omega)
          simp only [hp1v] at hd1
          have hp2v' : p2.val = p.val + 2 := by rw [hp2v]; simp
          by_cases h117 : e.val = 117
          · have hu : chOf e = 'u' := (chOf_eq_lit e 'u' (by decide)).mpr h117
            have he117 : e = 117#u32 := UScalar.eq_of_val_eq (by rw [h117]; rfl)
            obtain ⟨p6, hp6, hp6v⟩ := ev_usize_add p2 4#usize (by simp; omega)
            have hp6v' : p6.val = p.val + 6 := by rw [hp6v, hp2v']; simp
            rw [hd, hq, hd1, hu]
            by_cases h6 : p6.val ≤ s.val.length
            · have l0 : p2.val < s.val.length := by omega
              have l1 : p2.val + 1 < s.val.length := by omega
              have l2 : p2.val + 2 < s.val.length := by omega
              have l3 : p2.val + 3 < s.val.length := by omega
              obtain ⟨q1, hq1, hq1v⟩ := ev_usize_add p2 1#usize (by simp; omega)
              obtain ⟨q2, hq2, hq2v⟩ := ev_usize_add p2 2#usize (by simp; omega)
              obtain ⟨q3, hq3, hq3v⟩ := ev_usize_add p2 3#usize (by simp; omega)
              simp at hq1v hq2v hq3v
              have hi0 := slice_index_ok s p2 l0
              have hi1 := slice_index_ok s q1 (by omega)
              have hi2 := slice_index_ok s q2 (by omega)
              have hi3 := slice_index_ok s q3 (by omega)
              obtain ⟨x0, hx0, hx0v, hx0b⟩ := eval.mods_json.hex_val_refines _ (hs.get p2.val l0)
              obtain ⟨x1, hx1, hx1v, hx1b⟩ := eval.mods_json.hex_val_refines _ (hs.get q1.val (by omega))
              obtain ⟨x2, hx2, hx2v, hx2b⟩ := eval.mods_json.hex_val_refines _ (hs.get q2.val (by omega))
              obtain ⟨x3, hx3, hx3v, hx3b⟩ := eval.mods_json.hex_val_refines _ (hs.get q3.val (by omega))
              obtain ⟨m1, hm1, hm1v⟩ := ev_u64_mul x0 16#u64 (by simp; scalar_tac)
              obtain ⟨a1, ha1, ha1v⟩ := ev_u64_add m1 x1 (by simp at hm1v; rw [hm1v]; scalar_tac)
              obtain ⟨m2, hm2, hm2v⟩ := ev_u64_mul a1 16#u64 (by simp at hm1v; rw [ha1v, hm1v]; scalar_tac)
              obtain ⟨a2, ha2, ha2v⟩ := ev_u64_add m2 x2 (by simp at hm1v hm2v; rw [hm2v, ha1v, hm1v]; scalar_tac)
              obtain ⟨m3, hm3, hm3v⟩ := ev_u64_mul a2 16#u64 (by simp at hm1v hm2v; rw [ha2v, hm2v, ha1v, hm1v]; scalar_tac)
              obtain ⟨a3, ha3, ha3v⟩ := ev_u64_add m3 x3
                (by simp at hm1v hm2v hm3v; rw [hm3v, ha2v, hm2v, ha1v, hm1v]; scalar_tac)
              obtain ⟨ch, hch, hchc, hchv⟩ := eval.mods_json.char_of_nat_refines a3
              have hb : eval.mods_json.str_body_loop.body s (Slice.len s) acc p false none =
                  ok (.cont (vpush acc ch hpush, p6, false, none)) := by
                simp [eval.mods_json.str_body_loop.body, hnge, hidx, hp1, UScalar.eq_equiv, h34, h92, hlt1,
                  hidx1, hp2, he117, hp6, hp6v', h6, hi0, hq1, hi1, hq2, hi2, hq3, hi3, hx0, hx1, hx2, hx3, hm1, ha1, hm2,
                  ha2, hm3, ha3, hch, vec_push_ok acc ch hpush, (by omega : p.val + 6 ≤ s.val.length)]
              obtain ⟨y, hy, hr'⟩ := ih (s.val.length - p6.val) (by omega) p6 rfl (vpush acc ch hpush)
                (by omega) (by rw [vpush_val]; simp; omega)
                (by intro u hu; simp at hu; rcases hu with hu | hu; exact hv u hu; subst hu; exact hchv)
              refine ⟨y, by rw [ev_sb_step s _ acc p _ hb]; exact hy, ?_⟩
              have e2 : p.val + 1 + 1 = p2.val := by omega
              rw [e2, strS_drop s p2.val l0, strS_drop s (p2.val+1) l1, strS_drop s (p2.val+1+1) l2,
                strS_drop s (p2.val+1+1+1) l3, ev_strBodyL_u]
              have e6 : p2.val + 1 + 1 + 1 + 1 = p6.val := by omega
              rw [e6]
              have g1 : (s.val[p2.val + 1]'l1) = s.val[q1.val]'(by omega) := by simp [hq1v]
              have g2 : (s.val[p2.val + 1 + 1]'l2) = s.val[q2.val]'(by omega) := by simp [hq2v]
              have g3 : (s.val[p2.val + 1 + 1 + 1]'l3) = s.val[q3.val]'(by omega) := by simp [hq3v]
              rw [g1, g2, g3, ← hx0v, ← hx1v, ← hx2v, ← hx3v]
              have : a3.val = ((x0.val * 16 + x1.val) * 16 + x2.val) * 16 + x3.val := by
                simp at hm1v hm2v hm3v; rw [ha3v, hm3v, ha2v, hm2v, ha1v, hm1v]
              rw [← this, ← hchc]
              exact ev_sbRel_mono s (b := p6.val) (by omega) _ _ (by simpa using hr')
            · have hb : eval.mods_json.str_body_loop.body s (Slice.len s) acc p false none =
                  ok (.cont (acc, p2, false, some .BadU)) := by
                simp [eval.mods_json.str_body_loop.body, hnge, hidx, hp1, UScalar.eq_equiv, h34, h92, hlt1,
                  hidx1, hp2, he117, hp6, hp6v', h6, eq_false (by omega : ¬ p.val + 6 ≤ s.val.length)]
              refine ⟨_, by rw [ev_sb_step s _ acc p _ hb, ev_sb_fin _ _ _ _ _ _ (Or.inr rfl)], ?_⟩
              have e2 : p.val + 1 + 1 = p2.val := by omega
              rw [e2, ev_strBodyL_badu _ _ (by simp [strS_length]; omega)]
              rfl
          · -- one-character escape
            obtain ⟨r, hr, hrc, hrv⟩ := eval.mods_json.escape_char_refines e hc1
            have hb : eval.mods_json.str_body_loop.body s (Slice.len s) acc p false none =
                ok (.cont (vpush acc r hpush, p2, false, none)) := by
              simp [eval.mods_json.str_body_loop.body, hnge, hidx, hp1, UScalar.eq_equiv, h34, h92, hlt1', hidx1,
                hp2, h117, hr, vec_push_ok acc r hpush, hlt1, Nat.not_le.mpr hlt1]
            obtain ⟨y, hy, hr'⟩ := ih (s.val.length - p2.val) (by omega) p2 rfl (vpush acc r hpush)
              (by omega) (by rw [vpush_val]; simp; omega)
              (by intro u hu; simp at hu; rcases hu with hu | hu; exact hv u hu; subst hu; exact hrv)
            refine ⟨y, by rw [ev_sb_step s _ acc p _ hb]; exact hy, ?_⟩
            have hne : chOf e ≠ 'u' := fun hh => h117 ((chOf_eq_lit e 'u' (by decide)).mp hh)
            rw [hd, hq, hd1, ev_strBodyL_esc _ _ _ hne]
            exact ev_sbRel_mono s (b := p2.val) (by omega) _ _ (by simpa [hp2v', hrc] using hr')
        · -- a backslash at the end of the input
          have hb : eval.mods_json.str_body_loop.body s (Slice.len s) acc p false none =
              ok (.cont (vpush acc c hpush, p1, false, none)) := by
            have : ¬ p1 < Slice.len s := by rw [slice_lt_len_iff]; exact hlt1
            simp [eval.mods_json.str_body_loop.body, hnge, hidx, hp1, UScalar.eq_equiv, h34, h92, this, hlt1,
              vec_push_ok acc c hpush]
          obtain ⟨y, hy, hr⟩ := ih (s.val.length - p1.val) (by omega) p1 rfl (vpush acc c hpush) (by omega)
            (by simp; omega) (by intro u hu; simp at hu; rcases hu with hu | hu; exact hv u hu; subst hu; exact hc)
          refine ⟨y, by rw [ev_sb_step s _ acc p _ hb]; exact hy, ?_⟩
          have e1 : (strS s).drop (p.val + 1) = [] := List.drop_eq_nil_of_le (by simp [strS_length]; omega)
          rw [hd, hq, e1, ev_strBodyL_bs_end]
          have e2 : (strS s).drop p1.val = [] := by rw [hp1v]; exact e1
          rw [e2] at hr; exact ev_sbRel_mono s (b := p1.val) (by omega) _ _ (by simpa [hq] using hr)
      · -- an ordinary character
        have hb : eval.mods_json.str_body_loop.body s (Slice.len s) acc p false none =
            ok (.cont (vpush acc c hpush, p1, false, none)) := by
          simp [eval.mods_json.str_body_loop.body, hnge, hidx, hp1, UScalar.eq_equiv, h34, h92, vec_push_ok acc c hpush]
        obtain ⟨y, hy, hr⟩ := ih (s.val.length - p1.val) (by omega) p1 rfl (vpush acc c hpush) (by omega)
          (by simp; omega) (by intro u hu; simp at hu; rcases hu with hu | hu; exact hv u hu; subst hu; exact hc)
        refine ⟨y, by rw [ev_sb_step s _ acc p _ hb]; exact hy, ?_⟩
        have hq1 : chOf c ≠ '"' := fun hh => h34 ((chOf_eq_lit c '"' (by decide)).mp hh)
        have hq2 : chOf c ≠ '\\' := fun hh => h92 ((chOf_eq_lit c '\\' (by decide)).mp hh)
        rw [hd, ev_strBodyL_other _ _ _ hq1 hq2]
        exact ev_sbRel_mono s (b := p1.val) (by omega) _ _ (by simpa [hp1v] using hr)
    · -- end of input: unterminated
      have e : (strS s).drop p.val = [] := List.drop_eq_nil_of_le (by simp [strS_length]; omega)
      have hb : eval.mods_json.str_body_loop.body s (Slice.len s) acc p false none =
          ok (.cont (acc, p, false, some .Unterminated)) := by
        simp [eval.mods_json.str_body_loop.body, ge_iff_le, UScalar.le_equiv, hn]; omega
      refine ⟨_, by rw [ev_sb_step s _ acc p _ hb, ev_sb_fin _ _ _ _ _ _ (Or.inr rfl)], ?_⟩
      simp only [ev_sbRel, e, ev_strBodyL_nil, ev_jeS]
end OsuProofs

namespace OsuProofs
open OsuImpl

/-- valid scalar values -/
def ev_VV (t : alloc.vec.Vec U32) : Prop := (∀ u ∈ t.val, u.val.isValidChar) ∧ t.val.length < 2^62

theorem eval.mods_json.str_body_refines (s : Slice U32) (hs : ValidStr s) (hlen : s.val.length + 8 ≤ Usize.max)
    (h62 : s.val.length < 2^62)
    (p : Usize) (hp : p.val ≤ s.val.length) :
    ∃ r, eval.mods_json.str_body s p = ok r ∧ ev_pRel vstrS s r (SimJson.strBodyL [] ((strS s).drop p.val)) ∧
      ∀ t q, r = .Ok (t, q) → ev_VV t ∧ p.val ≤ q.val := by
  obtain ⟨⟨acc, q, err⟩, hy, hr⟩ := ev_str_body_loop s hs hlen p (alloc.vec.Vec.new U32) hp (by simp) (by simp)
  unfold eval.mods_json.str_body
  simp only [hy, bind_ok]
  rw [show (List.map chOf (alloc.vec.Vec.new U32).val).reverse = [] by simp] at hr
  cases err with
  | none =>
    simp only [ev_sbRel] at hr
    obtain ⟨hR, hq, hv, hpq, hal⟩ := hr
    refine ⟨_, rfl, ?_, ?_⟩
    · rw [hR]; exact ⟨rfl, rfl, hq⟩
    · intro t q' h; simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨⟨hv, by omega⟩, hpq⟩
  | some e =>
    simp only [ev_sbRel] at hr
    refine ⟨_, rfl, ?_, by simp⟩
    rw [hr]; rfl

/-- a parser result with unit value -/
def ev_uRel (s : Slice U32) : core.result.Result Usize eval.mods_json.JsonErr → Except String (Unit × List Char) → Prop
  | .Ok q, .ok (_, L) => L = (strS s).drop q.val ∧ q.val ≤ s.val.length
  | .Err e, .error m => m = ev_jeS e
  | _, _ => False

theorem eval.mods_json.expect_refines (s : Slice U32) (p : Usize) (hp : p.val ≤ s.val.length) (c : U32)
    (hc : (chOf c).toNat ≠ 0) (hcv : c.val.isValidChar) :
    ∃ r, eval.mods_json.expect s p c = ok r ∧ ev_uRel s r (SimJson.expect (chOf c) ((strS s).drop p.val)) ∧
      ∀ q, r = .Ok q → p.val < q.val := by
  obtain ⟨q, hq, hd, hpq, hql⟩ := eval.mods_json.ws_refines s p hp
  rw [ev_expect_spec, ← hd]
  unfold eval.mods_json.expect
  rw [hq]
  simp only [bind_ok]
  by_cases hlt : q.val < s.val.length
  · rw [strS_drop s q.val hlt]
    have hlt' : q < Slice.len s := (slice_lt_len_iff q s).mpr hlt
    obtain ⟨q1, hq1, hq1v⟩ := usize_add_one q (by have := slice_len_lt s; omega)
    have hcx : (chOf c == chOf (s.val[q.val]'hlt)) = decide (s.val[q.val]'hlt = c) := by
      have ht := chOf_toNat c hcv
      by_cases h : s.val[q.val]'hlt = c
      · simp [h]
      · have h1 : ¬ (s.val[q.val]'hlt).val = c.val := fun hh => h (UScalar.eq_of_val_eq hh)
        have h2 : ¬ chOf (s.val[q.val]'hlt) = chOf c := fun hh => h1 (by rw [(chOf_eq_lit _ _ hc).mp hh]; exact ht)
        simp only [h, decide_false]
        exact beq_false_of_ne (fun hh => h2 hh.symm)
    by_cases h : s.val[q.val]'hlt = c
    · refine ⟨.Ok q1, by simp [hlt', slice_index_ok s q hlt, h, hq1], ?_, by intro q' hq'; simp at hq'; subst hq'; omega⟩
      simp [hcx, h, ev_uRel, hq1v]; omega
    · refine ⟨.Err (.Expected c), by simp [hlt', slice_index_ok s q hlt, h], ?_, by simp⟩
      simp [hcx, h, ev_uRel, ev_jeS]
  · have e : (strS s).drop q.val = [] := List.drop_eq_nil_of_le (by simp [strS_length]; omega)
    have hlt' : ¬ q < Slice.len s := by rw [slice_lt_len_iff]; exact hlt
    refine ⟨.Err (.Expected c), by simp [hlt'], ?_, by simp⟩
    rw [e]; simp [ev_uRel, ev_jeS]
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem eval.mods_json.is_num_char_refines (c : U32) (h : c.val.isValidChar) :
    eval.mods_json.is_num_char c = ok (ev_isNumChar (chOf c)) := by
  unfold eval.mods_json.is_num_char ev_isNumChar
  rw [eval.mods_json.is_digit_refines c h]
  rw [chOf_beq_lit c '-' (by decide), chOf_beq_lit c '+' (by decide), chOf_beq_lit c '.' (by decide),
    chOf_beq_lit c 'e' (by decide), chOf_beq_lit c 'E' (by decide)]
  by_cases hd : (chOf c).isDigit = true
  · simp [hd]
  · simp only [hd, Bool.false_eq_true, if_false, Bool.false_or]
    by_cases h1 : c.val = 45 <;> by_cases h2 : c.val = 43 <;> by_cases h3 : c.val = 46 <;>
      by_cases h4 : c.val = 101 <;> simp [h1, h2, h3, h4, UScalar.eq_equiv] <;> omega

theorem ev_number_loop0 (s : Slice U32) (hs : ValidStr s) (p : Usize) (hp : p.val ≤ s.val.length) :
    ∃ q, eval.mods_json.number_value_loop0 s p = ok q ∧ p.val ≤ q.val ∧ q.val ≤ s.val.length ∧
      ((strS s).drop p.val).takeWhile ev_isNumChar = ((strS s).drop p.val).take (q.val - p.val) ∧
      (strS s).drop q.val = ((strS s).drop p.val).drop (q.val - p.val) := by
  unfold eval.mods_json.number_value_loop0
  refine loop_ok _ (fun (j : Usize) => s.val.length - j.val)
    (fun (j : Usize) => p.val ≤ j.val ∧ j.val ≤ s.val.length ∧
      ((strS s).drop p.val).takeWhile ev_isNumChar =
        ((strS s).drop p.val).take (j.val - p.val) ++ ((strS s).drop j.val).takeWhile ev_isNumChar)
    _ ?_ p ⟨le_refl _, hp, by simp⟩
  rintro j ⟨hpj, hjl, hT⟩
  have hl := slice_len_lt s
  have hdj : (strS s).drop j.val = ((strS s).drop p.val).drop (j.val - p.val) := by
    rw [List.drop_drop]; congr 1; omega
  by_cases hlt : j.val < s.val.length
  · have hc := hs.get j.val hlt
    have hd := strS_drop s j.val hlt
    by_cases hw : ev_isNumChar (chOf (s.val[j.val]'hlt)) = true
    · right
      obtain ⟨j1, hj1, hv⟩ := usize_add_one j (by omega)
      refine ⟨j1, by simp [eval.mods_json.number_value_loop0.body, (slice_lt_len_iff j s).mpr hlt,
        slice_index_ok s j hlt, eval.mods_json.is_num_char_refines _ hc, hw, hj1], ⟨by omega, by omega, ?_⟩, by omega⟩
      rw [hT, hd, List.takeWhile_cons, if_pos hw, hv]
      have e1 : ((strS s).drop p.val).take (j.val + 1 - p.val) =
          ((strS s).drop p.val).take (j.val - p.val) ++ [chOf (s.val[j.val]'hlt)] := by
        rw [show j.val + 1 - p.val = (j.val - p.val) + 1 by omega, List.take_add_one]
        congr 1
        have : ((strS s).drop p.val)[j.val - p.val]? = some (chOf (s.val[j.val]'hlt)) := by
          rw [List.getElem?_drop, show p.val + (j.val - p.val) = j.val by omega]; simp [strS, hlt]
        rw [this]; rfl
      rw [e1, List.append_assoc]; rfl
    · left
      refine ⟨j, by simp [eval.mods_json.number_value_loop0.body, (slice_lt_len_iff j s).mpr hlt,
        slice_index_ok s j hlt, eval.mods_json.is_num_char_refines _ hc, hw], hpj, hjl, ?_, hdj⟩
      rw [hT, hd, List.takeWhile_cons, if_neg hw, List.append_nil]
  · left
    have hlt' : ¬ j < Slice.len s := by rw [slice_lt_len_iff]; exact hlt
    refine ⟨j, by simp [eval.mods_json.number_value_loop0.body, hlt'], hpj, hjl, ?_, hdj⟩
    have e : (strS s).drop j.val = [] := List.drop_eq_nil_of_le (by simp [strS_length]; omega)
    rw [hT, e]; simp
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem ev_number_loop1 (s : Slice U32) (q : Usize) (hq : q.val ≤ s.val.length) :
    ∀ (t : alloc.vec.Vec U32) (k : Usize), k.val ≤ q.val → t.val.length + (q.val - k.val) ≤ Usize.max →
      ∃ r, eval.mods_json.number_value_loop1 s q t k = ok r ∧
        r.val = t.val ++ (s.val.drop k.val).take (q.val - k.val) := by
  intro t k hk hmax
  unfold eval.mods_json.number_value_loop1
  obtain ⟨r, hr, hv⟩ := loop_push_map (fun x => eval.mods_json.number_value_loop1.body s q x.1 x.2) q.val
    (fun i => s.val.getD i 0#u32)
    (by
      intro ts i hi hm
      obtain ⟨i1, hi1, hv1⟩ := usize_add_one i (by have := slice_len_lt s; omega)
      have hlt : i.val < s.val.length := by omega
      have hpu : ts.val.length < Usize.max := by omega
      refine ⟨vpush ts (s.val[i.val]'hlt) hpu, i1, by simp [eval.mods_json.number_value_loop1.body,
        (show i < q by scalar_tac), slice_index_ok s i hlt, vec_push_ok ts _ hpu, hi1], by simp [hlt], hv1⟩)
    (by intro ts i hi; simp [eval.mods_json.number_value_loop1.body, (show ¬ i < q by scalar_tac)])
    t k hk hmax
  refine ⟨r, hr, ?_⟩
  rw [hv]; congr 1
  apply List.ext_getElem
  · simp; omega
  · intro n h1 h2; simp at h1 ⊢; rw [List.getElem?_eq_getElem (by omega)]; simp

theorem eval.mods_json.number_value_refines (s : Slice U32) (hs : ValidStr s) (h62 : s.val.length < 2^62) (p : Usize)
    (hp : p.val ≤ s.val.length) :
    ∃ r, eval.mods_json.number_value s p = ok r ∧
      ev_pRel ev_vS s r (let cs := (strS s).drop p.val; let t := cs.takeWhile fun c => c.isDigit || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E'
        if t.isEmpty then .error "bad value" else .ok (.num (String.ofList t), cs.drop t.length)) ∧
      p.val ≤ s.val.length ∧ ∀ v q, r = .Ok (v, q) → p.val ≤ q.val ∧ ∃ t, v = .Num t ∧ ev_VV t := by
  obtain ⟨q, hq, hpq, hql, hT, hD⟩ := ev_number_loop0 s hs p hp
  have hT' : ((strS s).drop p.val).takeWhile (fun c => c.isDigit || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E')
      = ((strS s).drop p.val).take (q.val - p.val) := hT
  unfold eval.mods_json.number_value
  rw [hq]; simp only [bind_ok]
  simp only [hT']
  by_cases he : q = p
  · subst he
    refine ⟨.Err .BadValue, by simp, by simp [ev_pRel, ev_jeS], hp, by simp⟩
  · have hne : q.val ≠ p.val := fun h => he (UScalar.eq_of_val_eq h)
    have hlt : p.val < q.val := by omega
    obtain ⟨r, hr, hrv⟩ := ev_number_loop1 s q hql (alloc.vec.Vec.new U32) p (by omega)
      (by have := slice_len_lt s; simp; omega)
    refine ⟨.Ok (.Num r, q), by simp [he, hr], ?_, hp, ?_⟩
    · have hlen : (((strS s).drop p.val).take (q.val - p.val)).length = q.val - p.val := by
        simp [strS_length]; omega
      have hne' : (((strS s).drop p.val).take (q.val - p.val)).isEmpty = false := by
        rw [List.isEmpty_eq_false_iff]; intro h; rw [h] at hlen; simp at hlen; omega
      simp only [hne', Bool.false_eq_true, if_false, ev_pRel, ev_vS_num]
      refine ⟨?_, by rw [hlen, hD], hql⟩
      simp [vstrS, hrv, strS, List.map_take, List.map_drop]
    · intro v q' h; simp at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨by omega, r, rfl, ?_, by rw [hrv]; simp; omega⟩
      intro u hu; rw [hrv] at hu; simp at hu
      exact hs u (List.mem_of_mem_drop (List.mem_of_mem_take hu))
end OsuProofs

namespace OsuProofs
open OsuImpl

/-- the characters of an ASCII byte literal -/
def ev_litS (lit : Slice U8) : List Char := lit.val.map fun b => Char.ofNat b.val

theorem ev_prefix_iff (M : List Char) (l : List Char) :
    l <+: M ↔ l.length ≤ M.length ∧ ∀ j (h1 : j < l.length) (h2 : j < M.length), l[j] = M[j] := by
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨by simp, fun j h1 h2 => ?_⟩
    rw [List.getElem_append_left h1]
  · rintro ⟨hl, h⟩
    refine ⟨M.drop l.length, ?_⟩
    conv => rhs; rw [← List.take_append_drop l.length M]
    congr 1
    apply List.ext_getElem (by simp; omega)
    intro j h1 h2; rw [List.getElem_take]; exact h j h1 (by omega)

theorem eval.mods_json.has_lit_refines (s : Slice U32) (p : Usize) (lit : Slice U8)
    (hlit : ∀ b ∈ lit.val, 0 < b.val ∧ b.val < 128) (hp : p.val ≤ s.val.length)
    (hmax : s.val.length + lit.val.length ≤ Usize.max) :
    eval.mods_json.has_lit s p lit = ok (decide (ev_litS lit <+: (strS s).drop p.val)) := by
  have hl := slice_len_lt s
  obtain ⟨e, he, hev⟩ := ev_usize_add p (Slice.len lit) (by simp; omega)
  have hev' : e.val = p.val + lit.val.length := by rw [hev]; simp
  unfold eval.mods_json.has_lit
  simp only [he, bind_ok]
  by_cases hgt : e > Slice.len s
  · have hgt' : s.val.length < p.val + lit.val.length := by
      have := (UScalar.lt_equiv _ _).mp hgt
      have h2 : (Slice.len s).val = s.val.length := by simp
      omega
    rw [if_pos hgt]; congr 1
    rw [eq_comm, decide_eq_false_iff_not]
    intro hpre; have := hpre.length_le; simp [ev_litS, strS_length] at this; omega
  · rw [if_neg hgt]
    have hle : p.val + lit.val.length ≤ s.val.length := by
      have : ¬ (s.val.length < e.val) := fun h => hgt ((UScalar.lt_equiv _ _).mpr (by simpa using h))
      omega
    let P : Nat → Prop := fun k => ∀ j, j < k → (s.val.getD (p.val + j) 0#u32).val = (lit.val.getD j 0#u8).val
    obtain ⟨y, hy, hq⟩ := loop_ok (fun (x : Usize × Bool) => eval.mods_json.has_lit_loop.body s p lit x.1 x.2)
      (fun x => lit.val.length - x.1.val)
      (fun x => x.1.val ≤ lit.val.length ∧ (x.2 = true ↔ P x.1.val))
      (fun y => y = true ↔ P lit.val.length)
      (by
        rintro ⟨k, okb⟩ ⟨hk, hok⟩
        dsimp only at hk hok ⊢
        by_cases hkl : k.val < lit.val.length
        · right
          obtain ⟨pk, hpk, hpkv⟩ := ev_usize_add p k (by omega)
          obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by omega)
          have i1 := slice_index_ok s pk (by omega)
          have i2 := slice_index_ok lit k hkl
          have hc := hlit _ (List.getElem_mem hkl)
          have hcast : (UScalar.cast .U32 (lit.val[k.val]'hkl)).val = (lit.val[k.val]'hkl).val := by simp
          let ok1 := okb && decide ((s.val[pk.val]'(by omega)).val = (lit.val[k.val]'hkl).val)
          refine ⟨(k1, ok1), ?_, ⟨by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
          · simp only [eval.mods_json.has_lit_loop.body, (show k < Slice.len lit by scalar_tac), if_true, hpk, i1, i2,
              bind_ok, hk1, lift]
            by_cases heq : (s.val[pk.val]'(by omega)).val = (lit.val[k.val]'hkl).val
            · have : (s.val[pk.val]'(by omega)) = UScalar.cast .U32 (lit.val[k.val]'hkl) :=
                UScalar.eq_of_val_eq (by rw [hcast]; exact heq)
              simp [this, ok1, heq]
            · have : (s.val[pk.val]'(by omega)) ≠ UScalar.cast .U32 (lit.val[k.val]'hkl) :=
                fun hh => heq (by rw [hh, hcast])
              simp [this, ok1, heq]
          · simp only [ok1, Bool.and_eq_true, hok, decide_eq_true_eq, hk1v]
            constructor
            · rintro ⟨h1, h2⟩ j hj
              by_cases hjk : j < k.val
              · exact h1 j hjk
              · have : j = k.val := by omega
                subst this
                rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hkl]
                have e1 : p.val + k.val = pk.val := hpkv.symm
                simp only [e1]; exact h2
            · intro h
              refine ⟨fun j hj => h j (by omega), ?_⟩
              have := h k.val (by omega)
              rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hkl] at this
              have e1 : p.val + k.val = pk.val := hpkv.symm
              simp only [e1] at this; exact this
        · left
          refine ⟨okb, by simp [eval.mods_json.has_lit_loop.body, (show ¬ k < Slice.len lit by scalar_tac)], ?_⟩
          have : k.val = lit.val.length := by omega
          rw [hok, this])
      (0#usize, true) ⟨by simp, by simp [P]⟩
    unfold eval.mods_json.has_lit_loop
    rw [hy]; congr 1
    rw [Bool.eq_iff_iff, hq, decide_eq_true_iff, ev_prefix_iff]
    simp only [ev_litS, List.length_map, List.length_drop, strS_length, List.getElem_map, List.getElem_drop]
    have hch : ∀ j (hj : j < lit.val.length), (Char.ofNat (lit.val[j]'hj).val).toNat = (lit.val[j]'hj).val := by
      intro j hj; have := hlit _ (List.getElem_mem hj)
      simp [Char.ofNat, Nat.isValidChar, show (lit.val[j]'hj).val < 55296 by omega, Char.ofNatAux]
    constructor
    · intro h
      refine ⟨by omega, fun j h1 h2 => ?_⟩
      have := h j h1
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ h1] at this
      simp only [strS, List.getElem_map]
      have hc := hlit _ (List.getElem_mem h1)
      exact ((chOf_eq_lit _ _ (by rw [hch j h1]; omega)).mpr (by rw [hch j h1]; exact this)).symm
    · rintro ⟨_, h⟩ j hj
      have hc := hlit _ (List.getElem_mem hj)
      have := h j hj (by omega)
      simp only [strS, List.getElem_map] at this
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hj]
      rw [← hch j hj]; exact (chOf_eq_lit _ _ (by rw [hch j hj]; omega)).mp this.symm
end OsuProofs

namespace OsuProofs
open OsuImpl Aeneas.Data.ListN

-- validity of the strings inside a value (structural, as `ev_vS`)
mutual
def ev_vOk : eval.mods_json.V → Prop
  | .Num t => ev_VV t
  | .VStr t => ev_VV t
  | .Bool _ => True
  | .Null => True
  | .Arr ⟨⟨_, l, _⟩⟩ => ev_vlOk l
  | .Obj ⟨⟨_, l, _⟩⟩ => ev_kvlOk l
def ev_vlOk : {n : Nat} → ListN eval.mods_json.V n → Prop
  | _, .nil => True
  | _, .cons x t => ev_vOk x ∧ ev_vlOk t
def ev_kvlOk : {n : Nat} → ListN (alloc.vec.Vec U32 × eval.mods_json.V) n → Prop
  | _, .nil => True
  | _, .cons kv t => (ev_VV kv.1 ∧ ev_vOk kv.2) ∧ ev_kvlOk t
end

theorem ev_vlOk_iff {n} (l : ListN eval.mods_json.V n) : ev_vlOk l ↔ ∀ x ∈ l.toList, ev_vOk x := by
  induction l with
  | nil => simp [ev_vlOk, ListN.toList]
  | cons x t ih => simp [ev_vlOk, ListN.toList, ih]
theorem ev_kvlOk_iff {n} (l : ListN (alloc.vec.Vec U32 × eval.mods_json.V) n) :
    ev_kvlOk l ↔ ∀ kv ∈ l.toList, ev_VV kv.1 ∧ ev_vOk kv.2 := by
  induction l with
  | nil => simp [ev_kvlOk, ListN.toList]
  | cons x t ih => simp [ev_kvlOk, ListN.toList, ih]
theorem ev_vOk_arr (xs : alloc.vec.Vec eval.mods_json.V) : ev_vOk (.Arr xs) ↔ ∀ x ∈ xs.val, ev_vOk x := by
  obtain ⟨⟨n, l, h⟩⟩ := xs; simp only [ev_vOk, ev_vlOk_iff]; rfl
theorem ev_vOk_obj (kvs : alloc.vec.Vec (alloc.vec.Vec U32 × eval.mods_json.V)) :
    ev_vOk (.Obj kvs) ↔ ∀ kv ∈ kvs.val, ev_VV kv.1 ∧ ev_vOk kv.2 := by
  obtain ⟨⟨n, l, h⟩⟩ := kvs; simp only [ev_vOk, ev_kvlOk_iff]; rfl

/-- a value parse starting at `p0` -/
def ev_vRel (s : Slice U32) (p0 : Nat) :
    core.result.Result (eval.mods_json.V × Usize) eval.mods_json.JsonErr → Except String (SimJson.V × List Char) → Prop
  | .Ok (v, q), .ok (w, L) => ev_vS v = w ∧ L = (strS s).drop q.val ∧ p0 ≤ q.val ∧ q.val ≤ s.val.length ∧ ev_vOk v
  | .Err e, .error m => m = ev_jeS e
  | _, _ => False

/-- array / object items parse starting at `p0` -/
def ev_itRel {α β} (f : α → β) (ok : α → Prop) (s : Slice U32) (p0 : Nat) :
    core.result.Result (alloc.vec.Vec α × Usize) eval.mods_json.JsonErr → Except String (Array β × List Char) → Prop
  | .Ok (xs, q), .ok (A, L) => A = (xs.val.map f).toArray ∧ L = (strS s).drop q.val ∧ p0 ≤ q.val ∧
      q.val ≤ s.val.length ∧ ∀ x ∈ xs.val, ok x
  | .Err e, .error m => m = ev_jeS e
  | _, _ => False

/-- the induction hypothesis on the nesting fuel -/
def ev_VF (s : Slice U32) (fuel : Usize) (f : Nat) : Prop :=
  ∀ p : Usize, p.val ≤ s.val.length → ∃ r, eval.mods_json.value_f s p fuel = ok r ∧
    ev_vRel s p.val r (SimJson.valueF f ((strS s).drop p.val))

theorem ev_array_items_rec (s : Slice U32) (hs : ValidStr s) (hlen : s.val.length + 8 ≤ Usize.max)
    (fuel : Usize) (f : Nat) (hIH : ev_VF s fuel f) :
    ∀ (q : Usize) (xs : alloc.vec.Vec eval.mods_json.V), q.val ≤ s.val.length → xs.val.length ≤ q.val →
      (∀ x ∈ xs.val, ev_vOk x) →
      ∃ r, eval.mods_json.array_items_rec s q fuel xs = ok r ∧
        ev_itRel ev_vS ev_vOk s q.val r
          ((forIn Lean.Loop.mk (xs.val.map ev_vS).toArray (ev_arrBody f) : EvP _).run ((strS s).drop q.val)) := by
  intro q
  induction hk : s.val.length - q.val using Nat.strong_induction_on generalizing q with
  | _ k ih =>
    intro xs hq hxs hok
    have hmax : s.val.length ≤ Usize.max := slice_len_lt s
    rw [eval.mods_json.array_items_rec, ev_arr_loop]
    obtain ⟨r, hr, hrel⟩ := hIH q hq
    cases hR : SimJson.valueF f ((strS s).drop q.val) with
    | error m =>
      rw [hR] at hrel
      cases r with
      | Err e => exact ⟨.Err e, by simp [hr], hrel⟩
      | Ok _ => exact hrel.elim
    | ok wM =>
      obtain ⟨w, M1⟩ := wM
      rw [hR] at hrel
      cases r with
      | Err e => exact hrel.elim
      | Ok vq =>
      obtain ⟨v, q1⟩ := vq
      obtain ⟨hw, hM1, hqq1, hq1, hvok⟩ := hrel
      simp only
      have hpu : xs.val.length < Usize.max := by omega
      have hpo := vec_push_ok xs v hpu
      obtain ⟨r1, hr1, hd1, hq1r1, hr1l⟩ := eval.mods_json.ws_refines s q1 hq1
      rw [hM1, ← hd1]
      have hpush : (xs.val.map ev_vS).toArray.push w = ((vpush xs v hpu).val.map ev_vS).toArray := by
        simp [hw]
      have hok' : ∀ x ∈ (vpush xs v hpu).val, ev_vOk x := by
        intro x hx; simp at hx; rcases hx with hx | hx; exact hok x hx; subst hx; exact hvok
      by_cases hlt : r1.val < s.val.length
      · have hlt' : r1 < Slice.len s := (slice_lt_len_iff r1 s).mpr hlt
        have hidx := slice_index_ok s r1 hlt
        rw [strS_drop s r1.val hlt]
        obtain ⟨r2, hr2, hr2v⟩ := usize_add_one r1 (by omega)
        generalize hcv : s.val[r1.val]'hlt = c at hidx
        by_cases h44 : c.val = 44
        · have hq : chOf c = ',' := (chOf_eq_lit c ',' (by decide)).mpr h44
          obtain ⟨y, hy, hyr⟩ := ih (s.val.length - r2.val) (by omega) r2 rfl (vpush xs v hpu) (by omega)
            (by simp; omega) hok'
          refine ⟨y, by simp [hr, hpo, hr1, hlt', hlt, Nat.not_le.mpr hlt, hidx, UScalar.eq_equiv, h44, hr2, hy], ?_⟩
          simp only [hq]; rw [hpush, ← hr2v]
          revert hyr
          cases y with
          | Ok ab =>
            obtain ⟨a, b⟩ := ab
            cases (forIn Lean.Loop.mk ((vpush xs v hpu).val.map ev_vS).toArray (ev_arrBody f) : EvP _).run ((strS s).drop r2.val) with
            | ok _ => intro hyr; obtain ⟨h1, h2, h3, h4⟩ := hyr; exact ⟨h1, h2, by omega, h4⟩
            | error _ => intro hyr; exact hyr.elim
          | Err e =>
            cases (forIn Lean.Loop.mk ((vpush xs v hpu).val.map ev_vS).toArray (ev_arrBody f) : EvP _).run ((strS s).drop r2.val) with
            | ok _ => intro hyr; exact hyr.elim
            | error _ => intro hyr; exact hyr
        · by_cases h93 : c.val = 93
          · have hq : chOf c = ']' := (chOf_eq_lit c ']' (by decide)).mpr h93
            refine ⟨.Ok (vpush xs v hpu, r2), by simp [hr, hpo, hr1, hlt', hlt, Nat.not_le.mpr hlt, hidx, UScalar.eq_equiv, h44, h93, hr2], ?_⟩
            simp only [hq]
            exact ⟨hpush, by rw [hr2v], by omega, by omega, hok'⟩
          · have hq1' : chOf c ≠ ',' := fun hh => h44 ((chOf_eq_lit c ',' (by decide)).mp hh)
            have hq2' : chOf c ≠ ']' := fun hh => h93 ((chOf_eq_lit c ']' (by decide)).mp hh)
            refine ⟨.Err .BadArray, by simp [hr, hpo, hr1, hlt', hlt, Nat.not_le.mpr hlt, hidx, UScalar.eq_equiv, h44, h93], ?_⟩
            generalize chOf c = ch at hq1' hq2'
            split
            · rename_i hh; simp at hh; exact absurd hh.1 hq1'
            · rename_i hh; simp at hh; exact absurd hh.1 hq2'
            · rfl
      · have e : (strS s).drop r1.val = [] := List.drop_eq_nil_of_le (by simp [strS_length]; omega)
        have hlt' : ¬ r1 < Slice.len s := by rw [slice_lt_len_iff]; exact hlt
        refine ⟨.Err .BadArray, by simp [hr, hpo, hr1, hlt', hlt], ?_⟩
        rw [e]; rfl
end OsuProofs

namespace OsuProofs
open OsuImpl

/-- one object member of the spec loop body: `expect '"'`, `strBody`, `expect ':'`, `valueF` -/
def ev_omSpec (f : Nat) (M : List Char) : Except String ((String × SimJson.V) × List Char) :=
  match SimJson.expect '"' M with
  | .error e => .error e
  | .ok (_, M1) => match SimJson.strBodyL [] M1 with
    | .error e => .error e
    | .ok (k, M2) => match SimJson.expect ':' M2 with
      | .error e => .error e
      | .ok (_, M3) => match SimJson.valueF f M3 with
        | .error e => .error e
        | .ok (v, M4) => .ok ((k, v), M4)

theorem ev_obj_loop' (fuel : Nat) (kvs : Array (String × SimJson.V)) (M : List Char) :
    (forIn Lean.Loop.mk kvs (ev_objBody fuel) : EvP _).run M =
      match ev_omSpec fuel M with
      | .error e => .error e
      | .ok (kv, M4) => match SimJson.wsL M4 with
        | ',' :: r => (forIn Lean.Loop.mk (kvs.push kv) (ev_objBody fuel) : EvP _).run r
        | '}' :: r => .ok (kvs.push kv, r)
        | _ => .error "bad object" := by
  rw [ev_obj_loop]; unfold ev_omSpec
  cases SimJson.expect '"' M with
  | error e => rfl
  | ok r1 =>
    obtain ⟨_, M1⟩ := r1; simp only
    cases SimJson.strBodyL [] M1 with
    | error e => rfl
    | ok r2 =>
      obtain ⟨k, M2⟩ := r2; simp only
      cases SimJson.expect ':' M2 with
      | error e => rfl
      | ok r3 =>
        obtain ⟨_, M3⟩ := r3; simp only
        cases SimJson.valueF fuel M3 with
        | error e => rfl
        | ok r4 => obtain ⟨v, M4⟩ := r4; rfl

/-- an object member parse -/
def ev_omRel (s : Slice U32) (p0 : Nat) :
    core.result.Result ((alloc.vec.Vec U32 × eval.mods_json.V) × Usize) eval.mods_json.JsonErr →
      Except String ((String × SimJson.V) × List Char) → Prop
  | .Ok (kv, q), .ok (kw, L) => (vstrS kv.1, ev_vS kv.2) = kw ∧ L = (strS s).drop q.val ∧ p0 ≤ q.val ∧
      q.val ≤ s.val.length ∧ ev_VV kv.1 ∧ ev_vOk kv.2
  | .Err e, .error m => m = ev_jeS e
  | _, _ => False

theorem eval.mods_json.object_member_refines (s : Slice U32) (hs : ValidStr s) (hlen : s.val.length + 8 ≤ Usize.max)
    (h62 : s.val.length < 2^62)
    (fuel : Usize) (f : Nat) (hIH : ev_VF s fuel f) (p : Usize) (hp : p.val ≤ s.val.length) :
    ∃ r, eval.mods_json.object_member s p fuel = ok r ∧ ev_omRel s p.val r (ev_omSpec f ((strS s).drop p.val)) := by
  unfold eval.mods_json.object_member ev_omSpec
  have c34 : chOf 34#u32 = '"' := by decide
  have c58 : chOf 58#u32 = ':' := by decide
  obtain ⟨r1, hr1, hrel1, hpos1⟩ := eval.mods_json.expect_refines s p hp 34#u32 (by decide) (by decide)
  rw [c34] at hrel1
  cases hE1 : SimJson.expect '"' ((strS s).drop p.val) with
  | error m => rw [hE1] at hrel1; cases r1 with
    | Err e => exact ⟨.Err e, by simp [hr1], hrel1⟩
    | Ok _ => exact hrel1.elim
  | ok uM =>
    obtain ⟨_, M1⟩ := uM; rw [hE1] at hrel1
    cases r1 with
    | Err e => exact hrel1.elim
    | Ok q1 =>
    obtain ⟨hM1, hq1⟩ := hrel1
    have hpq1 := hpos1 q1 rfl
    simp only
    obtain ⟨r2, hr2, hrel2, hv2⟩ := eval.mods_json.str_body_refines s hs hlen h62 q1 hq1
    rw [hM1]
    cases hE2 : SimJson.strBodyL [] ((strS s).drop q1.val) with
    | error m => rw [hE2] at hrel2; cases r2 with
      | Err e => exact ⟨.Err e, by simp [hr1, hr2], hrel2⟩
      | Ok _ => exact hrel2.elim
    | ok kM =>
      obtain ⟨k, M2⟩ := kM; rw [hE2] at hrel2
      cases r2 with
      | Err e => exact hrel2.elim
      | Ok kq =>
      obtain ⟨kr, q2⟩ := kq
      obtain ⟨hk, hM2, hq2⟩ := hrel2
      have hkv := (hv2 kr q2 rfl).1
      have hq12 := (hv2 kr q2 rfl).2
      simp only
      obtain ⟨r3, hr3, hrel3, hpos3⟩ := eval.mods_json.expect_refines s q2 hq2 58#u32 (by decide) (by decide)
      rw [c58] at hrel3
      rw [hM2]
      cases hE3 : SimJson.expect ':' ((strS s).drop q2.val) with
      | error m => rw [hE3] at hrel3; cases r3 with
        | Err e => exact ⟨.Err e, by simp [hr1, hr2, hr3], hrel3⟩
        | Ok _ => exact hrel3.elim
      | ok uM3 =>
        obtain ⟨_, M3⟩ := uM3; rw [hE3] at hrel3
        cases r3 with
        | Err e => exact hrel3.elim
        | Ok q3 =>
        obtain ⟨hM3, hq3⟩ := hrel3
        have hpq3 := hpos3 q3 rfl
        simp only
        obtain ⟨r4, hr4, hrel4⟩ := hIH q3 hq3
        rw [hM3]
        cases hE4 : SimJson.valueF f ((strS s).drop q3.val) with
        | error m => rw [hE4] at hrel4; cases r4 with
          | Err e => exact ⟨.Err e, by simp [hr1, hr2, hr3, hr4], hrel4⟩
          | Ok _ => exact hrel4.elim
        | ok vM =>
          obtain ⟨w, M4⟩ := vM; rw [hE4] at hrel4
          cases r4 with
          | Err e => exact hrel4.elim
          | Ok vq =>
          obtain ⟨v, q4⟩ := vq
          obtain ⟨hw, hM4, hq34, hq4, hvok⟩ := hrel4
          refine ⟨.Ok ((kr, v), q4), by simp [hr1, hr2, hr3, hr4], ?_⟩
          exact ⟨by rw [hk, hw], hM4, by omega, hq4, hkv, hvok⟩
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem ev_object_items_rec (s : Slice U32) (hs : ValidStr s) (hlen : s.val.length + 8 ≤ Usize.max)
    (h62 : s.val.length < 2^62)
    (fuel : Usize) (f : Nat) (hIH : ev_VF s fuel f) :
    ∀ (q : Usize) (xs : alloc.vec.Vec (alloc.vec.Vec U32 × eval.mods_json.V)), q.val ≤ s.val.length → xs.val.length ≤ q.val →
      (∀ x ∈ xs.val, ev_VV x.1 ∧ ev_vOk x.2) →
      ∃ r, eval.mods_json.object_items_rec s q fuel xs = ok r ∧
        ev_itRel (fun kv => (vstrS kv.1, ev_vS kv.2)) (fun kv => ev_VV kv.1 ∧ ev_vOk kv.2) s q.val r
          ((forIn Lean.Loop.mk (xs.val.map fun kv => (vstrS kv.1, ev_vS kv.2)).toArray (ev_objBody f) : EvP _).run ((strS s).drop q.val)) := by
  intro q
  induction hk : s.val.length - q.val using Nat.strong_induction_on generalizing q with
  | _ k ih =>
    intro xs hq hxs hok
    have hmax : s.val.length ≤ Usize.max := slice_len_lt s
    rw [eval.mods_json.object_items_rec, ev_obj_loop']
    obtain ⟨r, hr, hrel⟩ := eval.mods_json.object_member_refines s hs hlen h62 fuel f hIH q hq
    cases hR : ev_omSpec f ((strS s).drop q.val) with
    | error m =>
      rw [hR] at hrel
      cases r with
      | Err e => exact ⟨.Err e, by simp [hr], hrel⟩
      | Ok _ => exact hrel.elim
    | ok wM =>
      obtain ⟨w, M1⟩ := wM
      rw [hR] at hrel
      cases r with
      | Err e => exact hrel.elim
      | Ok vq =>
      obtain ⟨v, q1⟩ := vq
      obtain ⟨hw, hM1, hqq1, hq1, hkok, hvok⟩ := hrel
      simp only
      have hpu : xs.val.length < Usize.max := by omega
      have hpo := vec_push_ok xs v hpu
      obtain ⟨r1, hr1, hd1, hq1r1, hr1l⟩ := eval.mods_json.ws_refines s q1 hq1
      rw [hM1, ← hd1]
      have hpush : (xs.val.map fun kv => (vstrS kv.1, ev_vS kv.2)).toArray.push w = ((vpush xs v hpu).val.map fun kv => (vstrS kv.1, ev_vS kv.2)).toArray := by
        simp [hw]
      have hok' : ∀ x ∈ (vpush xs v hpu).val, ev_VV x.1 ∧ ev_vOk x.2 := by
        intro x hx; simp at hx; rcases hx with hx | hx; exact hok x hx; subst hx; exact ⟨hkok, hvok⟩
      by_cases hlt : r1.val < s.val.length
      · have hlt' : r1 < Slice.len s := (slice_lt_len_iff r1 s).mpr hlt
        have hidx := slice_index_ok s r1 hlt
        rw [strS_drop s r1.val hlt]
        obtain ⟨r2, hr2, hr2v⟩ := usize_add_one r1 (by omega)
        generalize hcv : s.val[r1.val]'hlt = c at hidx
        by_cases h44 : c.val = 44
        · have hq : chOf c = ',' := (chOf_eq_lit c ',' (by decide)).mpr h44
          obtain ⟨y, hy, hyr⟩ := ih (s.val.length - r2.val) (by omega) r2 rfl (vpush xs v hpu) (by omega)
            (by simp; omega) hok'
          refine ⟨y, by simp [hr, hpo, hr1, hlt', hlt, Nat.not_le.mpr hlt, hidx, UScalar.eq_equiv, h44, hr2, hy], ?_⟩
          simp only [hq]; rw [hpush, ← hr2v]
          revert hyr
          cases y with
          | Ok ab =>
            obtain ⟨a, b⟩ := ab
            cases (forIn Lean.Loop.mk ((vpush xs v hpu).val.map fun kv => (vstrS kv.1, ev_vS kv.2)).toArray (ev_objBody f) : EvP _).run ((strS s).drop r2.val) with
            | ok _ => intro hyr; obtain ⟨h1, h2, h3, h4⟩ := hyr; exact ⟨h1, h2, by omega, h4⟩
            | error _ => intro hyr; exact hyr.elim
          | Err e =>
            cases (forIn Lean.Loop.mk ((vpush xs v hpu).val.map fun kv => (vstrS kv.1, ev_vS kv.2)).toArray (ev_objBody f) : EvP _).run ((strS s).drop r2.val) with
            | ok _ => intro hyr; exact hyr.elim
            | error _ => intro hyr; exact hyr
        · by_cases h125 : c.val = 125
          · have hq : chOf c = '}' := (chOf_eq_lit c '}' (by decide)).mpr h125
            refine ⟨.Ok (vpush xs v hpu, r2), by simp [hr, hpo, hr1, hlt', hlt, Nat.not_le.mpr hlt, hidx, UScalar.eq_equiv, h44, h125, hr2], ?_⟩
            simp only [hq]
            exact ⟨hpush, by rw [hr2v], by omega, by omega, hok'⟩
          · have hq1' : chOf c ≠ ',' := fun hh => h44 ((chOf_eq_lit c ',' (by decide)).mp hh)
            have hq2' : chOf c ≠ '}' := fun hh => h125 ((chOf_eq_lit c '}' (by decide)).mp hh)
            refine ⟨.Err .BadObject, by simp [hr, hpo, hr1, hlt', hlt, Nat.not_le.mpr hlt, hidx, UScalar.eq_equiv, h44, h125], ?_⟩
            generalize chOf c = ch at hq1' hq2'
            split
            · rename_i hh; simp at hh; exact absurd hh.1 hq1'
            · rename_i hh; simp at hh; exact absurd hh.1 hq2'
            · rfl
      · have e : (strS s).drop r1.val = [] := List.drop_eq_nil_of_le (by simp [strS_length]; omega)
        have hlt' : ¬ r1 < Slice.len s := by rw [slice_lt_len_iff]; exact hlt
        refine ⟨.Err .BadObject, by simp [hr, hpo, hr1, hlt', hlt], ?_⟩
        rw [e]; rfl
end OsuProofs

namespace OsuProofs
open OsuImpl

/-- the array/object value from an items result -/
def ev_wrapR {α} (g : alloc.vec.Vec α → eval.mods_json.V) :
    core.result.Result (alloc.vec.Vec α × Usize) eval.mods_json.JsonErr →
      core.result.Result (eval.mods_json.V × Usize) eval.mods_json.JsonErr
  | .Ok (xs, q) => .Ok (g xs, q)
  | .Err e => .Err e

theorem ev_array_value (s : Slice U32) (hs : ValidStr s) (hlen : s.val.length + 8 ≤ Usize.max)
    (fuel : Usize) (f : Nat) (hIH : ev_VF s fuel f) (p : Usize) (hp : p.val ≤ s.val.length) :
    ∃ r, eval.mods_json.array_value s p fuel = ok r ∧ ev_vRel s p.val r
      (if (SimJson.wsL ((strS s).drop p.val)).head? == some ']' then .ok (.arr [], (SimJson.wsL ((strS s).drop p.val)).tail)
       else ((forIn Lean.Loop.mk #[] (ev_arrBody f) : EvP _).run (SimJson.wsL ((strS s).drop p.val))).map
        fun r => (SimJson.V.arr r.1.toList, r.2)) := by
  obtain ⟨q, hq, hd, hpq, hql⟩ := eval.mods_json.ws_refines s p hp
  rw [← hd]
  have hmax := slice_len_lt s
  obtain ⟨r, hr, hrel⟩ := ev_array_items_rec s hs hlen fuel f hIH q (alloc.vec.Vec.new _) hql (by simp) (by simp)
  have hr' : eval.mods_json.array_items s q fuel = ok r := by unfold eval.mods_json.array_items; exact hr
  rw [show ((alloc.vec.Vec.new eval.mods_json.V).val.map ev_vS).toArray = #[] by simp] at hrel
  have tail : ev_vRel s p.val (ev_wrapR eval.mods_json.V.Arr r)
      (((forIn Lean.Loop.mk #[] (ev_arrBody f) : EvP _).run ((strS s).drop q.val)).map
          fun r => (SimJson.V.arr r.1.toList, r.2)) := by
    revert hrel
    cases r with
    | Ok xq =>
      obtain ⟨xs, q1⟩ := xq
      cases ((forIn Lean.Loop.mk #[] (ev_arrBody f) : EvP _).run ((strS s).drop q.val)) with
      | ok AL =>
        obtain ⟨A, L⟩ := AL
        rintro ⟨h1, h2, h3, h4, h5⟩
        exact ⟨by simp [h1], h2, by omega, h4, (ev_vOk_arr xs).mpr h5⟩
      | error _ => intro h; exact h.elim
    | Err e =>
      cases ((forIn Lean.Loop.mk #[] (ev_arrBody f) : EvP _).run ((strS s).drop q.val)) with
      | ok _ => intro h; exact h.elim
      | error _ => intro h; exact h
  have hw : ∀ r0, r = r0 → (do let r ← ok r0; match r with
      | core.result.Result.Ok v => (let (xs, q) := v; ok (core.result.Result.Ok (eval.mods_json.V.Arr xs, q)))
      | core.result.Result.Err e => ok (core.result.Result.Err e) : Result _) = ok (ev_wrapR eval.mods_json.V.Arr r0) := by
    intro r0 _; cases r0 <;> simp [ev_wrapR]
  unfold eval.mods_json.array_value
  by_cases hlt : q.val < s.val.length
  · have hlt' : q < Slice.len s := (slice_lt_len_iff q s).mpr hlt
    have hidx := slice_index_ok s q hlt
    obtain ⟨q2, hq2, hq2v⟩ := usize_add_one q (by omega)
    by_cases h93 : (s.val[q.val]'hlt).val = 93
    · have hc : chOf (s.val[q.val]'hlt) = ']' := (chOf_eq_lit _ ']' (by decide)).mpr h93
      refine ⟨.Ok (.Arr (alloc.vec.Vec.new _), q2), by simp [hq, hlt', hlt, hidx, UScalar.eq_equiv, h93, hq2], ?_⟩
      rw [strS_drop s q.val hlt, hc]
      exact ⟨by simp, by rw [hq2v]; rfl, by omega, by omega, by simp [ev_vOk_arr]⟩
    · have hc : chOf (s.val[q.val]'hlt) ≠ ']' := fun hh => h93 ((chOf_eq_lit _ ']' (by decide)).mp hh)
      refine ⟨ev_wrapR eval.mods_json.V.Arr r, ?_, ?_⟩
      · simp only [hq, bind_ok, hlt', if_true, hidx]
        rw [if_neg (by simp [UScalar.eq_equiv, h93])]
        rw [hr']; exact hw r rfl
      · rw [strS_drop s q.val hlt] at tail ⊢
        simp [hc]; exact tail
  · have hlt' : ¬ q < Slice.len s := by rw [slice_lt_len_iff]; exact hlt
    refine ⟨ev_wrapR eval.mods_json.V.Arr r, ?_, ?_⟩
    · simp only [hq, bind_ok, hlt', if_false]; rw [hr']; exact hw r rfl
    · have e : (strS s).drop q.val = [] := List.drop_eq_nil_of_le (by simp [strS_length]; omega)
      rw [e] at tail ⊢; simpa using tail
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem ev_object_value (s : Slice U32) (hs : ValidStr s) (hlen : s.val.length + 8 ≤ Usize.max)
    (h62 : s.val.length < 2^62)
    (fuel : Usize) (f : Nat) (hIH : ev_VF s fuel f) (p : Usize) (hp : p.val ≤ s.val.length) :
    ∃ r, eval.mods_json.object_value s p fuel = ok r ∧ ev_vRel s p.val r
      (if (SimJson.wsL ((strS s).drop p.val)).head? == some '}' then .ok (.obj [], (SimJson.wsL ((strS s).drop p.val)).tail)
       else ((forIn Lean.Loop.mk #[] (ev_objBody f) : EvP _).run (SimJson.wsL ((strS s).drop p.val))).map
        fun r => (SimJson.V.obj r.1.toList, r.2)) := by
  obtain ⟨q, hq, hd, hpq, hql⟩ := eval.mods_json.ws_refines s p hp
  rw [← hd]
  have hmax := slice_len_lt s
  obtain ⟨r, hr, hrel⟩ := ev_object_items_rec s hs hlen h62 fuel f hIH q (alloc.vec.Vec.new _) hql (by simp) (by simp)
  have hr' : eval.mods_json.object_items s q fuel = ok r := by unfold eval.mods_json.object_items; exact hr
  rw [show ((alloc.vec.Vec.new (alloc.vec.Vec U32 × eval.mods_json.V)).val.map fun kv => (vstrS kv.1, ev_vS kv.2)).toArray = #[] by simp] at hrel
  have tail : ev_vRel s p.val (ev_wrapR eval.mods_json.V.Obj r)
      (((forIn Lean.Loop.mk #[] (ev_objBody f) : EvP _).run ((strS s).drop q.val)).map
          fun r => (SimJson.V.obj r.1.toList, r.2)) := by
    revert hrel
    cases r with
    | Ok xq =>
      obtain ⟨xs, q1⟩ := xq
      cases ((forIn Lean.Loop.mk #[] (ev_objBody f) : EvP _).run ((strS s).drop q.val)) with
      | ok AL =>
        obtain ⟨A, L⟩ := AL
        rintro ⟨h1, h2, h3, h4, h5⟩
        exact ⟨by simp [h1], h2, by omega, h4, (ev_vOk_obj xs).mpr h5⟩
      | error _ => intro h; exact h.elim
    | Err e =>
      cases ((forIn Lean.Loop.mk #[] (ev_objBody f) : EvP _).run ((strS s).drop q.val)) with
      | ok _ => intro h; exact h.elim
      | error _ => intro h; exact h
  have hw : ∀ r0, r = r0 → (do let r ← ok r0; match r with
      | core.result.Result.Ok v => (let (xs, q) := v; ok (core.result.Result.Ok (eval.mods_json.V.Obj xs, q)))
      | core.result.Result.Err e => ok (core.result.Result.Err e) : Result _) = ok (ev_wrapR eval.mods_json.V.Obj r0) := by
    intro r0 _; cases r0 <;> simp [ev_wrapR]
  unfold eval.mods_json.object_value
  by_cases hlt : q.val < s.val.length
  · have hlt' : q < Slice.len s := (slice_lt_len_iff q s).mpr hlt
    have hidx := slice_index_ok s q hlt
    obtain ⟨q2, hq2, hq2v⟩ := usize_add_one q (by omega)
    by_cases h125 : (s.val[q.val]'hlt).val = 125
    · have hc : chOf (s.val[q.val]'hlt) = '}' := (chOf_eq_lit _ '}' (by decide)).mpr h125
      refine ⟨.Ok (.Obj (alloc.vec.Vec.new _), q2), by simp [hq, hlt', hlt, hidx, UScalar.eq_equiv, h125, hq2], ?_⟩
      rw [strS_drop s q.val hlt, hc]
      exact ⟨by simp, by rw [hq2v]; rfl, by omega, by omega, by simp [ev_vOk_obj]⟩
    · have hc : chOf (s.val[q.val]'hlt) ≠ '}' := fun hh => h125 ((chOf_eq_lit _ '}' (by decide)).mp hh)
      refine ⟨ev_wrapR eval.mods_json.V.Obj r, ?_, ?_⟩
      · simp only [hq, bind_ok, hlt', if_true, hidx]
        rw [if_neg (by simp [UScalar.eq_equiv, h125])]
        rw [hr']; exact hw r rfl
      · rw [strS_drop s q.val hlt] at tail ⊢
        simp [hc]; exact tail
  · have hlt' : ¬ q < Slice.len s := by rw [slice_lt_len_iff]; exact hlt
    refine ⟨ev_wrapR eval.mods_json.V.Obj r, ?_, ?_⟩
    · simp only [hq, bind_ok, hlt', if_false]; rw [hr']; exact hw r rfl
    · have e : (strS s).drop q.val = [] := List.drop_eq_nil_of_le (by simp [strS_length]; omega)
      rw [e] at tail ⊢; simpa using tail
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem ev_lit_true : (Array.to_slice (Array.make 4#usize [ 116#u8, 114#u8, 117#u8, 101#u8 ])).val =
    [116#u8, 114#u8, 117#u8, 101#u8] := by simp [Array.to_slice, Array.make]
theorem ev_lit_false : (Array.to_slice (Array.make 5#usize [ 102#u8, 97#u8, 108#u8, 115#u8, 101#u8 ])).val =
    [102#u8, 97#u8, 108#u8, 115#u8, 101#u8] := by simp [Array.to_slice, Array.make]
theorem ev_lit_null : (Array.to_slice (Array.make 4#usize [ 110#u8, 117#u8, 108#u8, 108#u8 ])).val =
    [110#u8, 117#u8, 108#u8, 108#u8] := by simp [Array.to_slice, Array.make]

/-- the literal / number tail of `value_f` (copied from the translation, position `q`) -/
def ev_tailR (s : Slice U32) (q : Usize) :
    Result (core.result.Result (eval.mods_json.V × Usize) eval.mods_json.JsonErr) := do
  let s1 ← lift (Array.to_slice (Array.make 4#usize [ 116#u8, 114#u8, 117#u8, 101#u8 ]))
  let b ← eval.mods_json.has_lit s q s1
  if b
  then
    let i1 ← q + 4#usize
    ok (core.result.Result.Ok (eval.mods_json.V.Bool true, i1))
  else
    let s2 ← lift (Array.to_slice (Array.make 5#usize [ 102#u8, 97#u8, 108#u8, 115#u8, 101#u8 ]))
    let b1 ← eval.mods_json.has_lit s q s2
    if b1
    then
      let i1 ← q + 5#usize
      ok (core.result.Result.Ok (eval.mods_json.V.Bool false, i1))
    else
      let s3 ← lift (Array.to_slice (Array.make 4#usize [ 110#u8, 117#u8, 108#u8, 108#u8 ]))
      let b2 ← eval.mods_json.has_lit s q s3
      if b2
      then
        let i1 ← q + 4#usize
        ok (core.result.Result.Ok (eval.mods_json.V.Null, i1))
      else eval.mods_json.number_value s q

theorem ev_prefix_drop (s : Slice U32) (q : Nat) (l : List Char) (h : l <+: (strS s).drop q) :
    (strS s).drop q = l ++ (strS s).drop (q + l.length) := by
  obtain ⟨t, ht⟩ := h
  have : t = (strS s).drop (q + l.length) := by
    have := congrArg (List.drop l.length) ht
    simpa using this
  rw [← ht, this]

theorem ev_tail (s : Slice U32) (hs : ValidStr s) (hlen : s.val.length + 8 ≤ Usize.max) (h62 : s.val.length < 2^62) (q : Usize)
    (hq : q.val ≤ s.val.length) (L : List Char) (hL : SimJson.wsL L = (strS s).drop q.val)
    (h1 : (SimJson.wsL L).head? ≠ some '"') (h2 : (SimJson.wsL L).head? ≠ some '[')
    (h3 : (SimJson.wsL L).head? ≠ some '{') (f : Nat) :
    ∃ r, ev_tailR s q = ok r ∧ ev_vRel s q.val r (SimJson.valueF (f + 1) L) := by
  have hT := eval.mods_json.has_lit_refines s q (Array.to_slice (Array.make 4#usize [ 116#u8, 114#u8, 117#u8, 101#u8 ]))
    (by rw [ev_lit_true]; decide) hq (by rw [ev_lit_true]; simp; omega)
  have hF := eval.mods_json.has_lit_refines s q (Array.to_slice (Array.make 5#usize [ 102#u8, 97#u8, 108#u8, 115#u8, 101#u8 ]))
    (by rw [ev_lit_false]; decide) hq (by rw [ev_lit_false]; simp; omega)
  have hN := eval.mods_json.has_lit_refines s q (Array.to_slice (Array.make 4#usize [ 110#u8, 117#u8, 108#u8, 108#u8 ]))
    (by rw [ev_lit_null]; decide) hq (by rw [ev_lit_null]; simp; omega)
  have lT : ev_litS (Array.to_slice (Array.make 4#usize [ 116#u8, 114#u8, 117#u8, 101#u8 ])) = ['t','r','u','e'] := by
    rw [ev_litS, ev_lit_true]; decide
  have lF : ev_litS (Array.to_slice (Array.make 5#usize [ 102#u8, 97#u8, 108#u8, 115#u8, 101#u8 ])) = ['f','a','l','s','e'] := by
    rw [ev_litS, ev_lit_false]; decide
  have lN : ev_litS (Array.to_slice (Array.make 4#usize [ 110#u8, 117#u8, 108#u8, 108#u8 ])) = ['n','u','l','l'] := by
    rw [ev_litS, ev_lit_null]; decide
  rw [lT] at hT; rw [lF] at hF; rw [lN] at hN
  unfold ev_tailR
  by_cases pT : ['t','r','u','e'] <+: (strS s).drop q.val
  · have e := ev_prefix_drop s q.val _ pT
    obtain ⟨q4, hq4, hq4v⟩ := ev_usize_add q 4#usize (by simp; omega)
    have hl4 : q.val + 4 ≤ s.val.length := by
      have := pT.length_le; simp [strS_length] at this; omega
    refine ⟨.Ok (.Bool true, q4), by simp [lift, hT, pT, hq4], ?_⟩
    rw [ev_valueF_true f L _ (by rw [hL, e]; rfl)]
    exact ⟨rfl, by simp at hq4v; rw [hq4v]; rfl, by simp at hq4v; omega, by simp at hq4v; omega, trivial⟩
  by_cases pF : ['f','a','l','s','e'] <+: (strS s).drop q.val
  · have e := ev_prefix_drop s q.val _ pF
    obtain ⟨q5, hq5, hq5v⟩ := ev_usize_add q 5#usize (by simp; omega)
    have hl5 : q.val + 5 ≤ s.val.length := by
      have := pF.length_le; simp [strS_length] at this; omega
    refine ⟨.Ok (.Bool false, q5), by simp [lift, hT, pT, hF, pF, hq5], ?_⟩
    rw [ev_valueF_false f L _ (by rw [hL, e]; rfl)]
    exact ⟨rfl, by simp at hq5v; rw [hq5v]; rfl, by simp at hq5v; omega, by simp at hq5v; omega, trivial⟩
  by_cases pN : ['n','u','l','l'] <+: (strS s).drop q.val
  · have e := ev_prefix_drop s q.val _ pN
    obtain ⟨q4, hq4, hq4v⟩ := ev_usize_add q 4#usize (by simp; omega)
    have hl4 : q.val + 4 ≤ s.val.length := by
      have := pN.length_le; simp [strS_length] at this; omega
    refine ⟨.Ok (.Null, q4), by simp [lift, hT, pT, hF, pF, hN, pN, hq4], ?_⟩
    rw [ev_valueF_null f L _ (by rw [hL, e]; rfl)]
    exact ⟨rfl, by simp at hq4v; rw [hq4v]; rfl, by simp at hq4v; omega, by simp at hq4v; omega, trivial⟩
  obtain ⟨r, hr, hrel, -, hmono⟩ := eval.mods_json.number_value_refines s hs h62 q hq
  refine ⟨r, by simp [lift, hT, pT, hF, pF, hN, pN, hr], ?_⟩
  rw [ev_valueF_num f L h1 h2 h3 (by rw [hL]; exact pT) (by rw [hL]; exact pF) (by rw [hL]; exact pN)]
  simp only [hL]
  revert hrel hmono
  cases r with
  | Ok vq =>
    obtain ⟨v, q'⟩ := vq
    intro hrel hmono
    obtain ⟨hle, t, rfl, htv⟩ := hmono v q' rfl
    revert hrel
    generalize (let cs := (strS s).drop q.val; let t := cs.takeWhile fun c => c.isDigit || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E'
        if t.isEmpty then (.error "bad value" : Except String (SimJson.V × List Char)) else .ok (.num (String.ofList t), cs.drop t.length)) = R
    cases R with
    | ok wL => obtain ⟨w, L'⟩ := wL; rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, hle, h3, htv⟩
    | error _ => intro h; exact h.elim
  | Err e =>
    intro hrel _
    revert hrel
    generalize (let cs := (strS s).drop q.val; let t := cs.takeWhile fun c => c.isDigit || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E'
        if t.isEmpty then (.error "bad value" : Except String (SimJson.V × List Char)) else .ok (.num (String.ofList t), cs.drop t.length)) = R
    cases R with
    | ok _ => intro h; exact h.elim
    | error _ => intro h; exact h
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem ev_valueF_str (fuel : Nat) (L cs : List Char) (h : SimJson.wsL L = '"' :: cs) :
    SimJson.valueF (fuel+1) L = (SimJson.strBodyL [] cs).map fun r => (SimJson.V.str r.1, r.2) := by
  unfold SimJson.valueF SimJson.ws
  show StateT.run _ L = _
  simp only [StateT.run_bind, StateT.run_modify, StateT.run_get, h, pure_bind]
  simp only [StateT.run_set, pure_bind]
  show (SimJson.strBodyL [] cs >>= _) = _
  cases SimJson.strBodyL [] cs <;> rfl

theorem ev_vRel_mono (s : Slice U32) {a b : Nat} (h : a ≤ b) (r R) : ev_vRel s b r R → ev_vRel s a r R := by
  unfold ev_vRel; split
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, by omega, h4, h5⟩
  · exact id
  · exact id

theorem ev_value_f_main (s : Slice U32) (hs : ValidStr s) (hlen : s.val.length + 8 ≤ Usize.max)
    (h62 : s.val.length < 2^62) :
    ∀ (f : Nat) (fuel : Usize), fuel.val = f → ev_VF s fuel f := by
  intro f
  induction f with
  | zero =>
    intro fuel hf p hp
    have : fuel = 0#usize := UScalar.eq_of_val_eq (by rw [hf]; rfl)
    subst this
    exact ⟨.Err .Fuel, by simp [eval.mods_json.value_f], by rw [ev_valueF_zero]; rfl⟩
  | succ f ih =>
    intro fuel hf p hp
    have hmax := slice_len_lt s
    have hne : fuel ≠ 0#usize := fun h => by rw [h] at hf; simp at hf
    obtain ⟨fuel1, hf1, hf1v, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := fuel) (y := 1#usize) (by simp; omega))
    simp at hf1v
    have IH := ih fuel1 (by omega)
    obtain ⟨q, hq, hd, hpq, hql⟩ := eval.mods_json.ws_refines s p hp
    have hne' : ¬ fuel = 0#usize := hne
    by_cases hlt : q.val < s.val.length
    · have hlt' : q < Slice.len s := (slice_lt_len_iff q s).mpr hlt
      have hidx := slice_index_ok s q hlt
      obtain ⟨q1, hq1, hq1v⟩ := usize_add_one q (by omega)
      have hdq := strS_drop s q.val hlt
      generalize hcv : s.val[q.val]'hlt = c at hidx hdq
      by_cases h34 : c.val = 34
      · have hc : chOf c = '"' := (chOf_eq_lit c '"' (by decide)).mpr h34
        rw [hc] at hdq
        obtain ⟨r, hr, hrel, hv⟩ := eval.mods_json.str_body_refines s hs hlen h62 q1 (by omega)
        rw [ev_valueF_str f _ _ (by rw [← hd, hdq])]
        rw [hq1v] at hrel hv
        revert hrel hv
        cases r with
        | Ok tq =>
          obtain ⟨t, q'⟩ := tq
          cases hS : SimJson.strBodyL [] ((strS s).drop (q.val + 1)) with
          | ok bL =>
            obtain ⟨b, L'⟩ := bL
            rintro ⟨h1, h2, h3⟩ hv
            obtain ⟨hvv, hqq⟩ := hv t q' rfl
            refine ⟨.Ok (.VStr t, q'), ?_, ?_⟩
            · rw [eval.mods_json.value_f]; simp [hne', hf1, hq, hlt', hlt, hidx, UScalar.eq_equiv, h34, hq1, hr]
            · exact ⟨by simp [h1], h2, by omega, h3, hvv⟩
          | error _ => intro h; exact h.elim
        | Err e =>
          cases hS : SimJson.strBodyL [] ((strS s).drop (q.val + 1)) with
          | ok _ => intro h; exact h.elim
          | error m =>
            intro h _
            refine ⟨.Err e, ?_, h⟩
            rw [eval.mods_json.value_f]; simp [hne', hf1, hq, hlt', hlt, hidx, UScalar.eq_equiv, h34, hq1, hr]
      by_cases h91 : c.val = 91
      · have hc : chOf c = '[' := (chOf_eq_lit c '[' (by decide)).mpr h91
        rw [hc] at hdq
        obtain ⟨r, hr, hrel⟩ := ev_array_value s hs hlen fuel1 f IH q1 (by omega)
        rw [hq1v] at hrel
        rw [ev_valueF_arr f _ _ (by rw [← hd, hdq])]
        refine ⟨r, ?_, ev_vRel_mono s (b := q.val + 1) (by omega) _ _ hrel⟩
        rw [eval.mods_json.value_f]; simp [hne', hf1, hq, hlt', hlt, hidx, UScalar.eq_equiv, h34, h91, hq1, hr]
      by_cases h123 : c.val = 123
      · have hc : chOf c = '{' := (chOf_eq_lit c '{' (by decide)).mpr h123
        rw [hc] at hdq
        obtain ⟨r, hr, hrel⟩ := ev_object_value s hs hlen h62 fuel1 f IH q1 (by omega)
        rw [hq1v] at hrel
        rw [ev_valueF_obj f _ _ (by rw [← hd, hdq])]
        refine ⟨r, ?_, ev_vRel_mono s (b := q.val + 1) (by omega) _ _ hrel⟩
        rw [eval.mods_json.value_f]; simp [hne', hf1, hq, hlt', hlt, hidx, UScalar.eq_equiv, h34, h91, h123, hq1, hr]
      have n1 : chOf c ≠ '"' := fun hh => h34 ((chOf_eq_lit c '"' (by decide)).mp hh)
      have n2 : chOf c ≠ '[' := fun hh => h91 ((chOf_eq_lit c '[' (by decide)).mp hh)
      have n3 : chOf c ≠ '{' := fun hh => h123 ((chOf_eq_lit c '{' (by decide)).mp hh)
      obtain ⟨r, hr, hrel⟩ := ev_tail s hs hlen h62 q hql _ hd.symm (by rw [← hd, hdq]; simpa using n1)
        (by rw [← hd, hdq]; simpa using n2) (by rw [← hd, hdq]; simpa using n3) f
      refine ⟨r, ?_, ev_vRel_mono s (b := q.val) hpq _ _ hrel⟩
      rw [eval.mods_json.value_f]; simp [hne', hf1, hq, hlt', hlt, hidx, UScalar.eq_equiv, h34, h91, h123]
      exact hr
    · have e : (strS s).drop q.val = [] := List.drop_eq_nil_of_le (by simp [strS_length]; omega)
      have hlt' : ¬ q < Slice.len s := by rw [slice_lt_len_iff]; exact hlt
      obtain ⟨r, hr, hrel⟩ := ev_tail s hs hlen h62 q hql _ hd.symm (by rw [← hd, e]; simp)
        (by rw [← hd, e]; simp) (by rw [← hd, e]; simp) f
      refine ⟨r, ?_, ev_vRel_mono s (b := q.val) hpq _ _ hrel⟩
      rw [eval.mods_json.value_f]; simp [hne', hf1, hq, hlt', hlt]
      exact hr
end OsuProofs
