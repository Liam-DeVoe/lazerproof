/-
Size bound for the score-info mods (json agent): every array/object inside a value parsed by `SimJson.valueF` from
`L` has at most `L.length` elements (`JsSmall`, `js_valueF_small`, spec-only), hence the decoded score-info mod list
is no longer than the text (`js_scoreInfo_len`). With Eval/JsonScore.lean this gives `js_scoreInfoOk h64` = the
eval agent's `ev_scoreInfoOk` (Eval/E2EBase.lean) under 64-bit (`js_mcOk` has `ev_mcOk`'s body).
-/
import OsuProofs.Eval.JsonScore
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
/-- every array / object inside a JSON value has at most `n` elements -/
inductive JsSmall (n : Nat) : SimJson.V → Prop
  | arr (xs : List SimJson.V) : xs.length ≤ n → (∀ x ∈ xs, JsSmall n x) → JsSmall n (.arr xs)
  | obj (kvs : List (String × SimJson.V)) : kvs.length ≤ n → (∀ kv ∈ kvs, JsSmall n kv.2) → JsSmall n (.obj kvs)
  | num (t : String) : JsSmall n (.num t)
  | str (t : String) : JsSmall n (.str t)
  | bool (b : Bool) : JsSmall n (.bool b)
  | null : JsSmall n .null

theorem JsSmall.mono {n m : Nat} (h : n ≤ m) : ∀ v, JsSmall n v → JsSmall m v := by
  intro v hv
  induction hv with
  | arr xs h1 _ ih => exact .arr xs (by omega) ih
  | obj kvs h1 _ ih => exact .obj kvs (by omega) ih
  | num t => exact .num t
  | str t => exact .str t
  | bool b => exact .bool b
  | null => exact .null

theorem js_wsL_len : ∀ L : List Char, (SimJson.wsL L).length ≤ L.length
  | [] => le_refl _
  | c :: cs => by
    unfold SimJson.wsL; split
    · have := js_wsL_len cs; simp; omega
    · simp

theorem js_strBodyL_len : ∀ (L acc : List Char) (s : String) (L' : List Char),
    SimJson.strBodyL acc L = .ok (s, L') → L'.length < L.length := by
  intro L
  induction hn : L.length using Nat.strong_induction_on generalizing L with
  | _ n ih =>
    intro acc s L' h
    match L with
    | [] => rw [ev_strBodyL_nil] at h; cases h
    | c :: cs =>
      by_cases hq : c = '"'
      · subst hq; rw [ev_strBodyL_quote] at h; simp at h; obtain ⟨-, rfl⟩ := h; simp at hn; omega
      by_cases hb : c = '\\'
      · subst hb
        match cs with
        | [] => rw [ev_strBodyL_bs_end, ev_strBodyL_nil] at h; cases h
        | e :: cs' =>
          by_cases hu : e = 'u'
          · subst hu
            match cs' with
            | a :: b :: c :: d :: rest =>
              rw [ev_strBodyL_u] at h
              have := ih rest.length (by simp at hn; omega) rest rfl _ _ _ h; simp at hn; omega
            | [] => rw [ev_strBodyL_badu _ _ (by simp)] at h; cases h
            | [_] => rw [ev_strBodyL_badu _ _ (by simp)] at h; cases h
            | [_, _] => rw [ev_strBodyL_badu _ _ (by simp)] at h; cases h
            | [_, _, _] => rw [ev_strBodyL_badu _ _ (by simp)] at h; cases h
          · rw [ev_strBodyL_esc _ _ _ hu] at h
            have := ih cs'.length (by simp at hn; omega) cs' rfl _ _ _ h; simp at hn; omega
      · rw [ev_strBodyL_other _ _ _ hq hb] at h
        have := ih cs.length (by simp at hn; omega) cs rfl _ _ _ h; simp at hn; omega
end OsuProofs

namespace OsuProofs
open OsuImpl
theorem js_expect_len (c : Char) (L L' : List Char) (h : SimJson.expect c L = .ok ((), L')) : L'.length < L.length := by
  rw [ev_expect_spec] at h
  have hw := js_wsL_len L
  revert h hw
  cases SimJson.wsL L with
  | nil => intro h; cases h
  | cons d cs =>
    intro h hw
    by_cases hcd : c = d
    · subst hcd; simp at h; subst h; simp at hw; omega
    · simp [hcd] at h

theorem js_arr_loop_small (f : Nat)
    (ih : ∀ L v L', SimJson.valueF f L = .ok (v, L') → L'.length < L.length ∧ JsSmall L.length v) (n : Nat) :
    ∀ (M : List Char) (xs A : Array SimJson.V) (M' : List Char),
      (forIn Lean.Loop.mk xs (ev_arrBody f) : EvP _).run M = .ok (A, M') → M.length ≤ n →
      (∀ x ∈ xs.toList, JsSmall n x) →
      (∀ x ∈ A.toList, JsSmall n x) ∧ A.size + M'.length ≤ xs.size + M.length ∧ M'.length < M.length := by
  intro M
  induction hm : M.length using Nat.strong_induction_on generalizing M with
  | _ m IH =>
    intro xs A M' h hn hxs
    rw [ev_arr_loop] at h
    revert h
    cases hv : SimJson.valueF f M with
    | error e => intro h; cases h
    | ok vM =>
      obtain ⟨v, M1⟩ := vM
      intro h
      dsimp only at h
      obtain ⟨h1, h2⟩ := ih M v M1 hv
      have h2' : JsSmall n v := JsSmall.mono (n := M.length) (m := n) (by omega) v h2
      have hw := js_wsL_len M1
      revert hw h
      cases SimJson.wsL M1 with
      | nil => intro h _; cases h
      | cons d r =>
        intro h hw
        by_cases hd1 : d = ','
        · subst hd1
          have := IH r.length (by simp at hw; omega) r rfl (xs.push v) A M' h (by simp at hw; omega)
            (by intro x hx; simp at hx; rcases hx with hx | hx; exact hxs x (by simpa using hx); subst hx; exact h2')
          simp at hw this ⊢; exact ⟨this.1, by omega, by omega⟩
        by_cases hd2 : d = ']'
        · subst hd2
          simp at h; obtain ⟨rfl, rfl⟩ := h
          refine ⟨?_, ?_, ?_⟩
          · intro x hx; simp at hx; rcases hx with hx | hx; exact hxs x (by simpa using hx); subst hx; exact h2'
          · simp at hw ⊢; omega
          · simp at hw; omega
        · simp [hd1, hd2] at h
end OsuProofs

namespace OsuProofs
open OsuImpl
theorem js_obj_loop_small (f : Nat)
    (ih : ∀ L v L', SimJson.valueF f L = .ok (v, L') → L'.length < L.length ∧ JsSmall L.length v) (n : Nat) :
    ∀ (M : List Char) (xs A : Array (String × SimJson.V)) (M' : List Char),
      (forIn Lean.Loop.mk xs (ev_objBody f) : EvP _).run M = .ok (A, M') → M.length ≤ n →
      (∀ x ∈ xs.toList, JsSmall n x.2) →
      (∀ x ∈ A.toList, JsSmall n x.2) ∧ A.size + M'.length ≤ xs.size + M.length ∧ M'.length < M.length := by
  intro M
  induction hm : M.length using Nat.strong_induction_on generalizing M with
  | _ m IH =>
    intro xs A M' h hn hxs
    rw [ev_obj_loop] at h
    revert h
    cases he1 : SimJson.expect '"' M with
    | error e => intro h; cases h
    | ok uM1 =>
      obtain ⟨u, M1⟩ := uM1
      have l1 := js_expect_len _ _ _ he1
      intro h; dsimp only at h; revert h
      cases hs : SimJson.strBodyL [] M1 with
      | error e => intro h; cases h
      | ok kM2 =>
        obtain ⟨k, M2⟩ := kM2
        have l2 := js_strBodyL_len _ _ _ _ hs
        intro h; dsimp only at h; revert h
        cases he2 : SimJson.expect ':' M2 with
        | error e => intro h; cases h
        | ok uM3 =>
          obtain ⟨u', M3⟩ := uM3
          have l3 := js_expect_len _ _ _ he2
          intro h; dsimp only at h; revert h
          cases hv : SimJson.valueF f M3 with
          | error e => intro h; cases h
          | ok vM =>
            obtain ⟨v, M4⟩ := vM
            intro h; dsimp only at h
            obtain ⟨h1, h2⟩ := ih M3 v M4 hv
            have h2' : JsSmall n v := JsSmall.mono (n := M3.length) (m := n) (by omega) v h2
            have hw := js_wsL_len M4
            revert hw h
            cases SimJson.wsL M4 with
            | nil => intro h _; cases h
            | cons d r =>
              intro h hw
              by_cases hd1 : d = ','
              · subst hd1
                have := IH r.length (by simp at hw; omega) r rfl (xs.push (k, v)) A M' h (by simp at hw; omega)
                  (by intro x hx; simp at hx; rcases hx with hx | hx; exact hxs x (by simpa using hx); subst hx; exact h2')
                simp at hw this ⊢; exact ⟨this.1, by omega, by omega⟩
              by_cases hd2 : d = '}'
              · subst hd2
                simp at h; obtain ⟨rfl, rfl⟩ := h
                refine ⟨?_, ?_, ?_⟩
                · intro x hx; simp at hx; rcases hx with hx | hx; exact hxs x (by simpa using hx); subst hx; exact h2'
                · simp at hw ⊢; omega
                · simp at hw; omega
              · simp [hd1, hd2] at h
end OsuProofs

namespace OsuProofs
open OsuImpl
theorem js_prefix_cons {l : List Char} {p : List Char} (h : p <+: l) : ∃ r, l = p ++ r := by
  obtain ⟨r, hr⟩ := h; exact ⟨r, hr.symm⟩

theorem js_valueF_small : ∀ (f : Nat) (L : List Char) (v : SimJson.V) (L' : List Char),
    SimJson.valueF f L = .ok (v, L') → L'.length < L.length ∧ JsSmall L.length v := by
  intro f
  induction f with
  | zero => intro L v L' h; rw [ev_valueF_zero] at h; cases h
  | succ f ih =>
    intro L v L' h
    have hw := js_wsL_len L
    generalize hM : SimJson.wsL L = M at hw
    by_cases h1 : M.head? = some '"'
    · obtain ⟨cs, rfl⟩ : ∃ cs, M = '"' :: cs := by cases M <;> simp_all
      rw [ev_valueF_str f L cs hM] at h
      revert h; cases hs : SimJson.strBodyL [] cs with
      | error e => intro h; cases h
      | ok sL =>
        intro h; simp [Except.map] at h; obtain ⟨rfl, rfl⟩ := h
        have := js_strBodyL_len _ _ _ _ hs; simp at hw
        exact ⟨by omega, .str _⟩
    by_cases h2 : M.head? = some '['
    · obtain ⟨cs, rfl⟩ : ∃ cs, M = '[' :: cs := by cases M <;> simp_all
      rw [ev_valueF_arr f L cs hM] at h
      split at h
      · rename_i hh; simp at h; obtain ⟨rfl, rfl⟩ := h
        have := js_wsL_len cs; simp at hw
        refine ⟨?_, .arr [] (by simp) (by simp)⟩
        have : (SimJson.wsL cs).tail.length ≤ cs.length := by simp; omega
        omega
      · revert h
        cases hl : (forIn Lean.Loop.mk #[] (ev_arrBody f) : EvP _).run (SimJson.wsL cs) with
        | error e => intro h; cases h
        | ok AM =>
          obtain ⟨A, M'⟩ := AM
          intro h; simp [Except.map] at h; obtain ⟨rfl, rfl⟩ := h
          have hcs := js_wsL_len cs
          obtain ⟨hA, hsz, hlt⟩ := js_arr_loop_small f ih L.length _ _ _ _ hl (by simp at hw; omega) (by simp)
          simp at hw hsz
          exact ⟨by omega, .arr _ (by simp; omega) (by simpa using hA)⟩
    by_cases h3 : M.head? = some '{'
    · obtain ⟨cs, rfl⟩ : ∃ cs, M = '{' :: cs := by cases M <;> simp_all
      rw [ev_valueF_obj f L cs hM] at h
      split at h
      · rename_i hh; simp at h; obtain ⟨rfl, rfl⟩ := h
        have := js_wsL_len cs; simp at hw
        refine ⟨?_, .obj [] (by simp) (by simp)⟩
        have : (SimJson.wsL cs).tail.length ≤ cs.length := by simp; omega
        omega
      · revert h
        cases hl : (forIn Lean.Loop.mk #[] (ev_objBody f) : EvP _).run (SimJson.wsL cs) with
        | error e => intro h; cases h
        | ok AM =>
          obtain ⟨A, M'⟩ := AM
          intro h; simp [Except.map] at h; obtain ⟨rfl, rfl⟩ := h
          have hcs := js_wsL_len cs
          obtain ⟨hA, hsz, hlt⟩ := js_obj_loop_small f ih L.length _ _ _ _ hl (by simp at hw; omega) (by simp)
          simp at hw hsz
          exact ⟨by omega, .obj _ (by simp; omega) (by simpa using hA)⟩
    by_cases h4 : ['t','r','u','e'] <+: M
    · obtain ⟨cs, rfl⟩ := js_prefix_cons h4
      rw [ev_valueF_true f L cs hM] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
      simp at hw; exact ⟨by omega, .bool _⟩
    by_cases h5 : ['f','a','l','s','e'] <+: M
    · obtain ⟨cs, rfl⟩ := js_prefix_cons h5
      rw [ev_valueF_false f L cs hM] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
      simp at hw; exact ⟨by omega, .bool _⟩
    by_cases h6 : ['n','u','l','l'] <+: M
    · obtain ⟨cs, rfl⟩ := js_prefix_cons h6
      rw [ev_valueF_null f L cs hM] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
      simp at hw; exact ⟨by omega, .null⟩
    rw [ev_valueF_num f L (by rw [hM]; exact h1) (by rw [hM]; exact h2) (by rw [hM]; exact h3)
      (by rw [hM]; exact h4) (by rw [hM]; exact h5) (by rw [hM]; exact h6), hM] at h
    simp only at h
    split at h
    · cases h
    · rename_i hne
      simp at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, .num _⟩
      have : 0 < (M.takeWhile fun c => c.isDigit || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E').length := by
        cases ht : (M.takeWhile fun c => c.isDigit || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E') with
        | nil => simp [ht] at hne
        | cons _ _ => simp
      have := (List.takeWhile_prefix (p := fun c => c.isDigit || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E') (l := M)).length_le
      simp; omega
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr
theorem js_mapM_len {α β} (f : α → Except String β) : ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys → ys.length = xs.length
  | [], ys, h => by simp [List.mapM_nil] at h; cases h; rfl
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e => rw [hx] at h; cases h
    | ok y =>
      rw [hx] at h
      cases hxs : xs.mapM f with
      | error e => simp [hxs, Bind.bind, Except.bind] at h
      | ok ys' =>
        simp [hxs, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        subst h; simp [js_mapM_len f xs ys' hxs]

/-- the number of decoded score-info mods is bounded by the text length -/
theorem js_scoreInfo_len (text : String) (MS : List ModConfig) (h : decodeScoreInfo text = .ok MS) :
    MS.length ≤ text.toList.length := by
  rw [js_decodeScoreInfo_eq] at h
  revert h
  cases hv : (SimJson.value).run text.toList with
  | error e => intro h; cases h
  | ok vr =>
    obtain ⟨v, rest⟩ := vr
    intro h
    rw [js_value_run] at hv
    obtain ⟨-, hs⟩ := js_valueF_small _ _ _ _ hv
    dsimp only at h
    split at h
    · cases h
    · cases v with
      | obj kvs =>
        simp only at h
        unfold js_simSpec at h
        cases hc : checkScoreInfo kvs with
        | error e => rw [hc] at h; cases h
        | ok u =>
          rw [hc] at h
          simp only [Bind.bind, Except.bind] at h
          cases hl : js_last kvs "mods" with
          | none => rw [hl] at h; simp [Pure.pure, Except.pure] at h; subst h; simp
          | some w =>
            rw [hl] at h
            cases w with
            | arr xs =>
              simp only at h
              rw [js_mapM_len _ _ _ h]
              unfold js_last at hl
              obtain ⟨kv, hkv, hkv2⟩ := Option.map_eq_some_iff.mp hl
              have hmem := List.mem_reverse.mp (List.mem_of_find?_eq_some hkv)
              cases hs with
              | obj _ _ hall =>
                have := hall kv hmem
                rw [hkv2] at this
                cases this with
                | arr _ hlen _ => exact hlen
            | _ => simp [throw, throwThe, MonadExceptOf.throw] at h <;> cases h
      | _ => simp at h <;> cases h

/-- `ev_scoreInfoOk` (Eval/E2EBase.lean) with `js_mcOk` (same body as `ev_mcOk`), given 64-bit. -/
theorem js_scoreInfoOk (h64 : System.Platform.numBits = 64) : ∀ (text : Slice U32), ValidStr text →
    text.val.length < 2^62 → ∃ r, eval.osr.decode_score_info text = ok r ∧
      (match r, decodeScoreInfo (String.ofList (strS text)) with
       | .Ok ms, .ok MS => ms.val.map mcS = MS ∧ (∀ m ∈ ms.val, js_mcOk m) ∧ ms.val.length < 2^62
       | .Err _, .error _ => True
       | _, _ => False) := by
  intro text hs h62
  obtain ⟨r, hr, hrel⟩ := eval.osr.decode_score_info_refines h64 text hs h62
  refine ⟨r, hr, ?_⟩
  revert hrel
  cases hD : decodeScoreInfo (String.ofList (strS text)) with
  | error e => cases r <;> simp [js_lRel']
  | ok MS =>
    cases r with
    | Err _ => simp [js_lRel']
    | Ok ms =>
      rintro ⟨h1, h2⟩
      refine ⟨h1, h2, ?_⟩
      have hl := js_scoreInfo_len _ _ hD
      have : ms.val.length = MS.length := by rw [← h1]; simp
      simp [strS_length] at hl
      omega
end OsuProofs

