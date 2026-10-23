/-
`net::decimal` part 9: `VarDecDiv` loop step and loop (Rust `DivState` ↔ spec loop state).
-/
import OsuProofs.Net.Decimal8
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

def dRel (st : net.decimal.DivState) (s : DS) : Prop :=
  st.scale.val = s.1 ∧ st.flag = s.2.1 ∧ st.q.val = s.2.2.1 ∧ st.r.val = s.2.2.2.1 ∧
  st.round_it = s.2.2.2.2.1 ∧ st.done = s.2.2.2.2.2

def dB (st : net.decimal.DivState) (den : U128) : Prop :=
  st.q.val < 2^96 + 2^64 ∧ st.r.val < den.val ∧ -30 ≤ st.scale.val ∧ st.scale.val ≤ 28

theorem exnI_S (e : net.basic.NetExn) : exnI (exnS e) = e := by cases e <;> rfl

theorem u128_bne_zero (x : U128) : (x != 0#u128) = (x.val != 0) := by
  have e : (x = 0#u128) ↔ x.val = 0 := ⟨fun h => by rw [h]; rfl, fun h => UScalar.eq_of_val_eq (by simp [h])⟩
  by_cases h : x.val = 0 <;> simp [bne, e, h]

theorem p96_lit : (2:Nat)^96 = 79228162514264337593543950336 := rfl

/-- The shared "scale up by `10^p`" block of `div_step` (both of its copies). -/
theorem div_inc (st : net.decimal.DivState) (den : U128) (p : U32) (fl : Bool) (s : DS)
    (h : dRel st s) (hb : dB st den) (hq : st.q.val < 2^96) (hden : 0 < den.val) (hden96 : den.val < 2^96)
    (hp : p.val ≤ 9) (hsp : st.scale.val + p.val ≤ 28) :
    ∃ r, (do
      let i ← lift (UScalar.hcast .I64 p)
      let i1 ← st.scale + i
      let pw ← net.decimal.pow10 p
      let i2 ← st.q * pw
      let i3 ← net.decimal.TWO96
      if i2 >= i3 then ok (core.result.Result.Err net.basic.NetExn.Overflow)
      else
        let rr ← st.r * pw
        let i4 ← rr / den
        let i5 ← i2 + i4
        let i6 ← rr % den
        if i5 >= i3 then
          let r ← net.decimal.overflow_unscale i5 i1 (i6 != 0#u128)
          match r with
          | core.result.Result.Ok v =>
            let (q2, s2) := v
            ok (core.result.Result.Ok (net.decimal.DivState.mk s2 fl q2 i6 st.round_it true))
          | core.result.Result.Err e => ok (core.result.Result.Err e)
        else ok (core.result.Result.Ok (net.decimal.DivState.mk i1 fl i5 i6 st.round_it st.done))) = ok r ∧
      (match divInc den.val s p.val fl with
       | .ok (.yield s') => ∃ st', r = .Ok st' ∧ dRel st' s' ∧ dB st' den ∧ st'.q.val < 2^96 ∧ st'.done = st.done
       | .ok (.done s') => ∃ st', r = .Ok st' ∧ dRel st' s' ∧ dB st' den ∧ st'.done = true
       | .error e => r = .Err (exnI e)) := by
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ := h
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  have hmax : U128.max = 2^128 - 1 := by simp [U128.max_eq]
  have hpI : (UScalar.hcast .I64 p).val = (p.val : Int) := hcast_i64_u32 p
  obtain ⟨i1, hi1, hi1v⟩ := eq_ok_of_spec (I64.add_spec (x := st.scale) (y := UScalar.hcast .I64 p)
    (by rw [hpI]; simp [I64.min_eq]; omega) (by rw [hpI]; simp [I64.max_eq]; omega))
  rw [hpI] at hi1v
  obtain ⟨pw, hpw, hpwv⟩ := net.decimal.pow10_refines p (by omega)
  have hpwl : pw.val ≤ 10^9 := by rw [hpwv]; exact Nat.pow_le_pow_right (by decide) hp
  have hpw0 : 0 < pw.val := by rw [hpwv]; exact Nat.pow_pos (by decide)
  have hqp : st.q.val * pw.val < 2^128 := by
    calc st.q.val * pw.val < 2^96 * 10^9 := by
          apply Nat.mul_lt_mul_of_lt_of_le hq hpwl (by omega)
      _ < 2^128 := by norm_num
  obtain ⟨i2, hi2, hi2v⟩ := eq_ok_of_spec (U128.mul_spec (x := st.q) (y := pw) (by rw [hmax]; omega))
  have hT := TWO96_eq
  generalize hTT : (⟨BitVec.ofNat 128 (2^96)⟩ : U128) = T at hT
  have hTv : T.val = 2^96 := by rw [← hTT]; exact TWO96_val
  have hge : ∀ x : U128, x >= T ↔ 2^96 ≤ x.val := fun x => by show T.val ≤ x.val ↔ _; rw [hTv]
  simp only [lift, bind_ok, hi1, hpw, hi2, hT]
  by_cases ho : 2^96 ≤ st.q.val * pw.val
  · rw [if_pos ((hge _).mpr (by rw [hi2v]; exact ho))]
    refine ⟨_, rfl, ?_⟩
    have hsp : divInc den.val s p.val fl = .error .overflow := by
      unfold divInc; rw [if_pos (by rw [← hs3, ← hpwv]; exact ho)]; rfl
    rw [hsp]; rfl
  · rw [if_neg (by rw [hge, hi2v]; exact ho)]
    have hrp : st.r.val * pw.val < 2^128 := by
      calc st.r.val * pw.val < 2^96 * 10^9 := by
            apply Nat.mul_lt_mul_of_lt_of_le (by omega) hpwl (by omega)
        _ < 2^128 := by norm_num
    obtain ⟨rr, hrr, hrrv⟩ := eq_ok_of_spec (U128.mul_spec (x := st.r) (y := pw) (by rw [hmax]; omega))
    have hd0 : den.val ≠ 0 := by omega
    obtain ⟨i4, hi4, hi4v⟩ := UScalar.div_spec rr hd0
    have hi4l : i4.val < pw.val := by
      rw [hi4v, hrrv]; apply Nat.div_lt_of_lt_mul
      exact Nat.mul_lt_mul_of_pos_right hb2 hpw0
    obtain ⟨i5, hi5, hi5v⟩ := eq_ok_of_spec (U128.add_spec (x := i2) (y := i4) (by rw [hmax, hi2v]; rw [p96_lit] at ho; omega))
    obtain ⟨i6, hi6, hi6v⟩ := eq_ok_of_spec (UScalar.rem_spec rr hd0)
    have hi6l : i6.val < den.val := by rw [hi6v]; exact Nat.mod_lt _ hden
    rw [hrr, bind_ok, hi4, bind_ok, hi5, bind_ok, hi6, bind_ok]
    have e5 : i5.val = s.2.2.1 * 10 ^ p.val + s.2.2.2.1 * 10 ^ p.val / den.val := by
      rw [hi5v, hi2v, hi4v, hrrv, ← hs3, ← hs4, hpwv]
    have e6 : i6.val = s.2.2.2.1 * 10 ^ p.val % den.val := by rw [hi6v, hrrv, ← hs4, hpwv]
    have hnov : ¬ s.2.2.1 * 10 ^ p.val ≥ NetDecimal.two96 := by rw [← hs3, ← hpwv]; exact ho
    by_cases ho2 : 2^96 ≤ i5.val
    · rw [if_pos ((hge _).mpr ho2)]
      obtain ⟨r, hr, hrv⟩ := net.decimal.overflow_unscale_refines i5 i1 (i6 != 0#u128) (by omega)
      rw [hr, bind_ok]
      have hov2 : s.2.2.1 * 10 ^ p.val + s.2.2.2.1 * 10 ^ p.val / den.val ≥ NetDecimal.two96 := by
        rw [← e5]; exact ho2
      have hsp : divInc den.val s p.val fl = (do
          let x ← NetDecimal.overflowUnscale i5.val i1.val (i6.val != 0)
          pure (.done (x.2, fl, x.1, i6.val, s.2.2.2.2.1, true))) := by
        unfold divInc; rw [if_neg hnov, if_pos hov2, e5, e6, hi1v, hs1]
      rw [hsp, u128_bne_zero] at *
      revert hrv
      cases r with
      | Ok v =>
        obtain ⟨q2, s2⟩ := v
        cases hou : NetDecimal.overflowUnscale i5.val i1.val (i6.val != 0) with
        | error e => simp [resRel]
        | ok w =>
          intro hrv
          simp only [resRel, qsRel] at hrv
          obtain ⟨w1, w2⟩ := w
          simp only at hrv
          have hw : w2 ≥ 0 ∧ w2 = i1.val - 1 ∧ w1 ≤ i5.val / 10 + 1 := by
            unfold NetDecimal.overflowUnscale at hou
            dsimp only at hou
            split at hou
            · simp at hou
            · simp only [Except.ok.injEq, Prod.mk.injEq] at hou
              obtain ⟨h1, h2⟩ := hou
              refine ⟨by omega, by omega, ?_⟩
              rw [← h1]; split <;> omega
          refine ⟨_, rfl, ?_⟩
          refine ⟨net.decimal.DivState.mk s2 fl q2 i6 st.round_it true, rfl, ⟨by simp [hrv.2], rfl, by simp [hrv.1],
            by simp [e6], by simp [hs5], rfl⟩, ⟨?_, by simpa using hi6l, by simp; omega, by simp; omega⟩, rfl⟩
          simp only; rw [hrv.1]
          have : i5.val < 2^96 + 10^9 := by rw [hi5v, hi2v]; rw [p96_lit] at ho; omega
          rw [p96_lit] at this ⊢; norm_num at this ⊢; omega
      | Err e =>
        cases hou : NetDecimal.overflowUnscale i5.val i1.val (i6.val != 0) with
        | error e' =>
          intro hrv; simp only [resRel] at hrv
          refine ⟨_, rfl, ?_⟩
          show core.result.Result.Err e = core.result.Result.Err (exnI e')
          rw [← hrv, exnI_S]
        | ok w => simp [resRel]
    · rw [if_neg (by rw [hge]; exact ho2)]
      refine ⟨_, rfl, ?_⟩
      have hov2 : ¬ s.2.2.1 * 10 ^ p.val + s.2.2.2.1 * 10 ^ p.val / den.val ≥ NetDecimal.two96 := by
        rw [← e5]; exact ho2
      have hsp : divInc den.val s p.val fl = .ok (.yield (s.1 + p.val, fl, i5.val, i6.val, s.2.2.2.2.1, s.2.2.2.2.2)) := by
        unfold divInc; rw [if_neg hnov, if_neg hov2, e5, e6]; rfl
      rw [hsp]
      refine ⟨_, rfl, ⟨by simp [hi1v, hs1], rfl, rfl, rfl, by simp [hs5], by simp [hs6]⟩,
        ⟨by simp; omega, by simpa using hi6l, by simp; omega, by simp; omega⟩, by simp; omega, rfl⟩

abbrev DStepRel (r : core.result.Result net.decimal.DivState net.basic.NetExn) (den : U128) :
    Except NetExn (ForInStep DS) → Prop
  | .ok (.yield s') => ∃ st', r = .Ok st' ∧ dRel st' s' ∧ dB st' den ∧ st'.q.val < 2^96 ∧ st'.done = false
  | .ok (.done s') => ∃ st', r = .Ok st' ∧ dRel st' s' ∧ dB st' den ∧ st'.done = true
  | .error e => r = .Err (exnI e)

theorem div_inc' (st : net.decimal.DivState) (den : U128) (p : U32) (fl : Bool) (s : DS)
    (h : dRel st s) (hb : dB st den) (hq : st.q.val < 2^96) (hden : 0 < den.val) (hden96 : den.val < 2^96)
    (hp : p.val ≤ 9) (hsp : st.scale.val + p.val ≤ 28) (hnd : st.done = false) :
    ∃ r, (do
      let i ← lift (UScalar.hcast .I64 p)
      let i1 ← st.scale + i
      let pw ← net.decimal.pow10 p
      let i2 ← st.q * pw
      let i3 ← net.decimal.TWO96
      if i2 >= i3 then ok (core.result.Result.Err net.basic.NetExn.Overflow)
      else
        let rr ← st.r * pw
        let i4 ← rr / den
        let i5 ← i2 + i4
        let i6 ← rr % den
        if i5 >= i3 then
          let r ← net.decimal.overflow_unscale i5 i1 (i6 != 0#u128)
          match r with
          | core.result.Result.Ok v =>
            let (q2, s2) := v
            ok (core.result.Result.Ok (net.decimal.DivState.mk s2 fl q2 i6 st.round_it true))
          | core.result.Result.Err e => ok (core.result.Result.Err e)
        else ok (core.result.Result.Ok (net.decimal.DivState.mk i1 fl i5 i6 st.round_it st.done))) = ok r ∧
      DStepRel r den (divInc den.val s p.val fl) := by
  obtain ⟨r, hr, hm⟩ := div_inc st den p fl s h hb hq hden hden96 hp hsp
  refine ⟨r, hr, ?_⟩
  revert hm
  cases divInc den.val s p.val fl with
  | error e => intro hm; exact hm
  | ok st2 =>
    cases st2 with
    | yield s' => intro hm; obtain ⟨st', h1, h2, h3, h4, h5⟩ := hm; exact ⟨st', h1, h2, h3, h4, by rw [h5, hnd]⟩
    | done s' => intro hm; exact hm

theorem div_step_ok (st : net.decimal.DivState) (den : U128) (s : DS)
    (h : dRel st s) (hb : dB st den) (hq : st.q.val < 2^96) (hden : 0 < den.val) (hden96 : den.val < 2^96)
    (hnd : st.done = false) :
    ∃ r, net.decimal.div_step st den = ok r ∧ DStepRel r den (divStep den.val s) := by
  have h' := h
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ := h'
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  have hsnd : s.2.2.2.2.2 = false := by rw [← hs6, hnd]
  unfold net.decimal.div_step
  by_cases hr0 : st.r.val = 0
  · have hr0' : st.r = 0#u128 := UScalar.eq_of_val_eq (by simp [hr0])
    rw [if_pos hr0']
    by_cases hsc : 0 ≤ st.scale.val
    · have hsc' : st.scale >= 0#i64 := by show (0#i64).val ≤ st.scale.val; simpa using hsc
      rw [if_pos hsc']
      refine ⟨_, rfl, ?_⟩
      have hsp : divStep den.val s = .ok (.done (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, true)) := by
        unfold divStep; rw [if_neg (by simp [hsnd]), if_pos (by rw [← hs4, hr0]), if_pos (by rw [← hs1]; exact hsc)]; rfl
      rw [hsp]
      exact ⟨_, rfl, ⟨hs1, hs2, hs3, hs4, hs5, rfl⟩, ⟨by simp; omega, by simpa using hb2, hb3, hb4⟩, rfl⟩
    · have hsc' : ¬ st.scale >= 0#i64 := by show ¬ (0#i64).val ≤ st.scale.val; simpa using hsc
      rw [if_neg hsc']
      obtain ⟨m, hm, hmv⟩ := eq_ok_of_spec (IScalar.neg_step st.scale (by
        intro he; rw [he] at hb3; simp [IScalar.min, I64.min_eq] at hb3))
      have hpv : ∃ pp : U32, (if m < 9#i64 then ok (IScalar.hcast .U32 m) else ok 9#u32 : Result U32) = ok pp ∧
          pp.val = Nat.min 9 (-st.scale.val).toNat := by
        by_cases h9 : m.val < 9
        · have h9' : m < 9#i64 := by show m.val < (9#i64).val; simpa using h9
          refine ⟨IScalar.hcast .U32 m, by rw [if_pos h9'], ?_⟩
          rw [hcast_u32_val m (by omega) (by omega), hmv]; unfold Nat.min; rw [Nat.min_def]; split <;> omega
        · have h9' : ¬ m < 9#i64 := by show ¬ m.val < (9#i64).val; simpa using h9
          refine ⟨9#u32, by rw [if_neg h9'], ?_⟩
          unfold Nat.min; rw [Nat.min_def]; split <;> simp <;> omega
      obtain ⟨pp, hpp, hppv⟩ := hpv
      have hpp9 : pp.val ≤ 9 := by rw [hppv]; exact Nat.min_le_left _ _
      have hpps : pp.val ≤ (-st.scale.val).toNat := by rw [hppv]; exact Nat.min_le_right _ _
      have hm' : (-. st.scale) = ok m := hm
      rw [hm', bind_ok, hpp, bind_ok]
      obtain ⟨r, hr, hrel⟩ := div_inc' st den pp st.flag s h ⟨hb1, hb2, hb3, hb4⟩ hq hden hden96 hpp9 (by omega) hnd
      refine ⟨r, hr, ?_⟩
      have hsp : divStep den.val s = divInc den.val s (Nat.min 9 (-s.1).toNat) s.2.1 := by
        unfold divStep; rw [if_neg (by simp [hsnd]), if_pos (by rw [← hs4, hr0]), if_neg (by rw [← hs1]; exact hsc)]
      rw [hsp, ← hs1, ← hppv, ← hs2]; exact hrel
  · have hr0' : ¬ st.r = 0#u128 := fun he => hr0 (by rw [he]; rfl)
    rw [if_neg hr0']
    by_cases h28 : st.scale.val = 28
    · have h28' : st.scale = 28#i64 := IScalar.eq_of_val_eq (by simp [h28])
      rw [if_pos h28']
      refine ⟨_, rfl, ?_⟩
      have hsp : divStep den.val s = .ok (.done (s.1, true, s.2.2.1, s.2.2.2.1, true, true)) := by
        unfold divStep; rw [if_neg (by simp [hsnd]), if_neg (by rw [← hs4]; exact hr0), if_pos (by rw [← hs1]; exact h28)]; rfl
      rw [hsp]
      exact ⟨_, rfl, ⟨hs1, rfl, hs3, hs4, rfl, rfl⟩, ⟨by simp; omega, by simpa using hb2, hb3, hb4⟩, rfl⟩
    · have h28' : ¬ st.scale = 28#i64 := fun he => h28 (by rw [he]; rfl)
      rw [if_neg h28']
      obtain ⟨sr, hsr, hsrv⟩ := net.decimal.search_scale_refines st.q st.scale hq ⟨by omega, by omega⟩
      rw [hsr, bind_ok]
      have hsp0 : divStep den.val s = (do
          let p ← NetDecimal.searchScale s.2.2.1 s.1
          if p = 0 then pure (.done (s.1, true, s.2.2.1, s.2.2.2.1, true, true))
          else divInc den.val s p true) := by
        unfold divStep; rw [if_neg (by simp [hsnd]), if_neg (by rw [← hs4]; exact hr0), if_neg (by rw [← hs1]; exact h28)]
      rw [hsp0, ← hs3, ← hs1]
      revert hsrv
      cases sr with
      | Ok v =>
        cases hss : NetDecimal.searchScale st.q.val st.scale.val with
        | error e => simp [resRel]
        | ok w =>
          intro hsrv
          dsimp only
          simp only [resRel] at hsrv
          have hwb := searchScale_le st.q.val st.scale.val (by omega) w hss
          by_cases hv0 : v.val = 0
          · have hv0' : v = 0#u32 := UScalar.eq_of_val_eq (by simp [hv0])
            rw [if_pos hv0']
            refine ⟨_, rfl, ?_⟩
            simp only [except_bind_ok, show w = 0 by omega, if_true]
            exact ⟨_, rfl, ⟨by rw [hs1], rfl, by rw [hs3], hs4, rfl, rfl⟩, ⟨by simp; omega, by simpa using hb2, hb3, hb4⟩, rfl⟩
          · have hv0' : ¬ v = 0#u32 := fun he => hv0 (by rw [he]; rfl)
            rw [if_neg hv0']
            obtain ⟨r, hr, hrel⟩ := div_inc' st den v true s h ⟨hb1, hb2, hb3, hb4⟩ hq hden hden96 (by omega) (by omega) hnd
            refine ⟨r, hr, ?_⟩
            simp only [except_bind_ok, show ¬ w = 0 by omega, if_false]
            rw [← hsrv]; exact hrel
      | Err e =>
        cases hss : NetDecimal.searchScale st.q.val st.scale.val with
        | error e' =>
          intro hsrv; simp only [resRel] at hsrv
          dsimp only
          refine ⟨_, rfl, ?_⟩
          show core.result.Result.Err e = core.result.Result.Err (exnI e')
          rw [← hsrv, exnI_S]
        | ok w => simp [resRel]

/-- Helper (no spec def): one `VarDecDiv` iteration = one spec loop step (`DStepRel`). -/
theorem net.decimal.div_step_refines (st : net.decimal.DivState) (den : U128) (s : DS)
    (h : dRel st s) (hb : dB st den) (hq : st.q.val < 2^96) (hden : 0 < den.val) (hden96 : den.val < 2^96)
    (hnd : st.done = false) :
    ∃ r, net.decimal.div_step st den = ok r ∧ DStepRel r den (divStep den.val s) :=
  div_step_ok st den s h hb hq hden hden96 hnd

/-! ## the loop -/

theorem iterEx_divDone (den : Nat) (s : DS) (h : s.2.2.2.2.2 = true) : ∀ n, iterEx (divStep den) n s = .ok s
  | 0 => rfl
  | _+1 => by
    obtain ⟨a, b, c, d, e, f⟩ := s
    simp only at h; subst h
    simp only [iterEx, divStep, if_true]; rfl

abbrev DLR := net.decimal.DivState × I32 × Option net.basic.NetExn

/-- Rust loop result tuple as a `DivState`. -/
def dsOf (y : I64 × Bool × U128 × U128 × Bool × Bool × Option net.basic.NetExn) : net.decimal.DivState :=
  ⟨y.1, y.2.1, y.2.2.1, y.2.2.2.1, y.2.2.2.2.1, y.2.2.2.2.2.1⟩

theorem div_loop_ok (den : U128) (hden : 0 < den.val) (hden96 : den.val < 2^96) (FIN : Except NetExn DS) :
    ∀ x : DLR, ((x.2.2 = none ∧ ∃ s, dRel x.1 s ∧ dB x.1 den ∧ (x.1.done = false → x.1.q.val < 2^96) ∧
        0 ≤ x.2.1.val ∧ x.2.1.val ≤ 40 ∧ iterEx (divStep den.val) (40 - x.2.1.val.toNat) s = FIN) ∨
        (∃ e, x.2.2 = some e ∧ FIN = .error (exnS e))) →
      ∃ y, net.decimal.div_loop den x.1 x.2.1 x.2.2 = ok y ∧
        ((y.2.2.2.2.2.2 = none ∧ ∃ s, dRel (dsOf y) s ∧ dB (dsOf y) den ∧ FIN = .ok s) ∨
         (∃ e, y.2.2.2.2.2.2 = some e ∧ FIN = .error (exnS e))) := by
  intro x hx
  unfold net.decimal.div_loop
  refine loop_ok _ (fun (x : DLR) => 41 - x.2.1.val.toNat + (if x.2.2 = none ∧ x.1.done = false then 1 else 0))
    (fun (x : DLR) => (x.2.2 = none ∧ ∃ s, dRel x.1 s ∧ dB x.1 den ∧ (x.1.done = false → x.1.q.val < 2^96) ∧
        0 ≤ x.2.1.val ∧ x.2.1.val ≤ 40 ∧ iterEx (divStep den.val) (40 - x.2.1.val.toNat) s = FIN) ∨
        (∃ e, x.2.2 = some e ∧ FIN = .error (exnS e)))
    (fun (y : I64 × Bool × U128 × U128 × Bool × Bool × Option net.basic.NetExn) =>
      (y.2.2.2.2.2.2 = none ∧ ∃ s, dRel (dsOf y) s ∧ dB (dsOf y) den ∧ FIN = .ok s) ∨
         (∃ e, y.2.2.2.2.2.2 = some e ∧ FIN = .error (exnS e))) ?_ x hx
  rintro ⟨st, it, err⟩ hx
  rcases hx with ⟨herr, s, hrel, hb, hq, hit0, hit40, hfin⟩ | ⟨e, herr, hfin⟩
  · dsimp only at herr hrel hb hq hit0 hit40 hfin ⊢
    subst herr
    by_cases hd : st.done = true
    · left
      refine ⟨(st.scale, st.flag, st.q, st.r, st.round_it, st.done, none), by simp [net.decimal.div_loop.body, hd],
        Or.inl ⟨rfl, s, hrel, hb, ?_⟩⟩
      rw [← hfin]; exact iterEx_divDone _ s (by rw [← hrel.2.2.2.2.2, hd]) _
    · have hd' : st.done = false := by simpa using hd
      by_cases hit : it.val < 40
      · right
        have hit' : it < 40#i32 := by show it.val < (40#i32).val; simpa using hit
        obtain ⟨it1, hit1, hit1v⟩ := eq_ok_of_spec (I32.add_spec (x := it) (y := 1#i32)
          (by simp [I32.min_eq]; omega) (by simp [I32.max_eq]; omega))
        simp at hit1v
        obtain ⟨r, hr, hrel2⟩ := div_step_ok st den s hrel hb (hq hd') hden hden96 hd'
        have e40 : 40 - it.val.toNat = (40 - it1.val.toNat) + 1 := by omega
        rw [e40] at hfin
        simp only [iterEx] at hfin
        revert hrel2 hfin
        cases divStep den.val s with
        | error e =>
          intro hfin hrel2
          simp only [DStepRel] at hrel2
          rw [hrel2] at hr
          refine ⟨(st, it1, some (exnI e)), by simp [net.decimal.div_loop.body, hd', hit', hr, hit1], ?_, ?_⟩
          · right; exact ⟨exnI e, rfl, by rw [exnS_I]; exact hfin.symm⟩
          · dsimp only; simp; omega
        | ok stp =>
          cases stp with
          | yield s' =>
            intro hfin hrel2
            obtain ⟨st', h1, h2, h3, h4, h5⟩ := hrel2
            subst h1
            refine ⟨(st', it1, none), by simp [net.decimal.div_loop.body, hd', hit', hr, hit1], ?_, ?_⟩
            · left; exact ⟨rfl, s', h2, h3, fun _ => h4, by simp; omega, by simp; omega, hfin⟩
            · dsimp only; simp [h5, hd']; omega
          | done s' =>
            intro hfin hrel2
            obtain ⟨st', h1, h2, h3, h4⟩ := hrel2
            subst h1
            refine ⟨(st', it1, none), by simp [net.decimal.div_loop.body, hd', hit', hr, hit1], ?_, ?_⟩
            · left
              refine ⟨rfl, s', h2, h3, fun h => by rw [h4] at h; simp at h, by simp; omega, by simp; omega, ?_⟩
              rw [iterEx_divDone _ s' (by rw [← h2.2.2.2.2.2, h4])]; exact hfin
            · dsimp only; simp [h4, hd']; omega
      · left
        have hit' : ¬ it < 40#i32 := by show ¬ it.val < (40#i32).val; simpa using hit
        refine ⟨(st.scale, st.flag, st.q, st.r, st.round_it, st.done, none), by simp [net.decimal.div_loop.body, hd', hit'],
          Or.inl ⟨rfl, s, hrel, hb, ?_⟩⟩
        rw [← hfin]
        have : 40 - it.val.toNat = 0 := by omega
        rw [this]; rfl
  · left
    dsimp only at herr hfin ⊢
    subst herr
    by_cases hd : st.done = true
    · exact ⟨(st.scale, st.flag, st.q, st.r, st.round_it, st.done, some e), by simp [net.decimal.div_loop.body, hd],
        Or.inr ⟨e, rfl, hfin⟩⟩
    · exact ⟨(st.scale, st.flag, st.q, st.r, st.round_it, st.done, some e), by simp [net.decimal.div_loop.body, hd],
        Or.inr ⟨e, rfl, hfin⟩⟩

/-! ## the rounding / unscale tail -/

theorem ustep_le (K : Nat) (c : Int) (hc : 0 ≤ c) (x : Nat × Int) : (ustep K c x).2 ≤ x.2 := by
  unfold ustep; split <;> simp <;> omega

theorem unscale_le (q : Nat) (s : Int) : (NetDecimal.unscale q s).2 ≤ s := by
  rw [unscale_eq]
  have := ustep_le 10 1 (by omega) (ustep 100 2 (ustep 10000 4 (ustep 100000000 8 (ustep 100000000 8
    (ustep 100000000 8 (ustep 100000000 8 (q, s)))))))
  have := ustep_le 100 2 (by omega) (ustep 10000 4 (ustep 100000000 8 (ustep 100000000 8
    (ustep 100000000 8 (ustep 100000000 8 (q, s))))))
  have := ustep_le 10000 4 (by omega) (ustep 100000000 8 (ustep 100000000 8
    (ustep 100000000 8 (ustep 100000000 8 (q, s)))))
  have := ustep_le 100000000 8 (by omega) (ustep 100000000 8 (ustep 100000000 8 (ustep 100000000 8 (q, s))))
  have := ustep_le 100000000 8 (by omega) (ustep 100000000 8 (ustep 100000000 8 (q, s)))
  have := ustep_le 100000000 8 (by omega) (ustep 100000000 8 (q, s))
  have := ustep_le 100000000 8 (by omega) (q, s)
  simp only at *
  omega

theorem div_fin_ok (neg fl : Bool) (q : U128) (sc : I64) (h1 : -2^61 ≤ sc.val) (h2 : sc.val ≤ 28) :
    ∃ r, (do
      let (q1, scale) ← (if fl then net.decimal.unscale q sc else ok (q, sc))
      if scale < 0#i64 then ok (core.result.Result.Ok ({ neg := neg, mant := q1, scale := 0#u32 } : net.decimal.NetDecimal))
      else do
        let i ← lift (IScalar.hcast .U32 scale)
        ok (core.result.Result.Ok ({ neg := neg, mant := q1, scale := i } : net.decimal.NetDecimal))) = ok r ∧
      resRel decRel r (divFin neg fl q.val sc.val) := by
  have fin2 : ∀ (q1 : U128) (s1 : I64), s1.val ≤ 28 → ∃ d, (if s1 < 0#i64 then ok (core.result.Result.Ok (E := net.basic.NetExn)
      ({ neg := neg, mant := q1, scale := 0#u32 } : net.decimal.NetDecimal))
      else do
        let i ← lift (IScalar.hcast .U32 s1)
        ok (core.result.Result.Ok (E := net.basic.NetExn) ({ neg := neg, mant := q1, scale := i } : net.decimal.NetDecimal))) =
        ok (core.result.Result.Ok (E := net.basic.NetExn) d) ∧ decS d = ⟨neg, q1.val, s1.val.toNat⟩ := by
    intro q1 s1 hs
    by_cases hn : s1.val < 0
    · have hn' : s1 < 0#i64 := by show s1.val < (0#i64).val; simpa using hn
      refine ⟨_, by rw [if_pos hn'], ?_⟩
      simp [decS]; omega
    · have hn' : ¬ s1 < 0#i64 := by show ¬ s1.val < (0#i64).val; simpa using hn
      refine ⟨⟨neg, q1, IScalar.hcast .U32 s1⟩, by rw [if_neg hn']; simp [lift], ?_⟩
      simp [decS, hcast_u32_val s1 (by omega) (by omega)]
  cases fl with
  | true =>
    obtain ⟨q1, s1, hu, huv⟩ := net.decimal.unscale_refines q sc h1
    have hs1 : s1.val ≤ 28 := by
      have := unscale_le q.val sc.val
      have e := congrArg Prod.snd huv; simp only at e; omega
    obtain ⟨d, hr, hd⟩ := fin2 q1 s1 hs1
    refine ⟨_, by simp only [if_true, hu, bind_ok]; exact hr, ?_⟩
    have e1 := congrArg Prod.fst huv; have e2 := congrArg Prod.snd huv
    simp only at e1 e2
    show decS d = _
    rw [hd, ← e1, ← e2]
  | false =>
    obtain ⟨d, hr, hd⟩ := fin2 q sc h2
    refine ⟨_, by simp only [Bool.false_eq_true, if_false, bind_ok]; exact hr, ?_⟩
    show decS d = _
    rw [hd]

theorem div_ovf_ok (neg fl : Bool) (q : U128) (sc : I64) (h1 : -2^61 ≤ sc.val) (h2 : sc.val ≤ 28) :
    ∃ r, (do
      let r ← net.decimal.overflow_unscale q sc true
      match r with
      | core.result.Result.Ok v =>
        let (q2, s2) := v
        let (q1, scale) ← (if fl then net.decimal.unscale q2 s2 else ok v)
        if scale < 0#i64 then ok (core.result.Result.Ok ({ neg := neg, mant := q1, scale := 0#u32 } : net.decimal.NetDecimal))
        else do
          let i ← lift (IScalar.hcast .U32 scale)
          ok (core.result.Result.Ok ({ neg := neg, mant := q1, scale := i } : net.decimal.NetDecimal))
      | core.result.Result.Err e => ok (core.result.Result.Err e)) = ok r ∧
      resRel decRel r (do let x ← NetDecimal.overflowUnscale q.val sc.val true; divFin neg fl x.1 x.2) := by
  obtain ⟨r, hr, hrv⟩ := net.decimal.overflow_unscale_refines q sc true (by omega)
  rw [hr, bind_ok]
  revert hrv
  cases r with
  | Ok v =>
    obtain ⟨q2, s2⟩ := v
    cases hou : NetDecimal.overflowUnscale q.val sc.val true with
    | error e => simp [resRel]
    | ok w =>
      intro hrv
      simp only [resRel, qsRel] at hrv
      obtain ⟨w1, w2⟩ := w
      simp only at hrv
      have hw : w2 = sc.val - 1 ∧ 0 ≤ w2 := by
        unfold NetDecimal.overflowUnscale at hou; dsimp only at hou
        split at hou
        · simp at hou
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hou; omega
      have hs2v : s2.val = w2 := hrv.2
      obtain ⟨r2, hr2, hrr2⟩ := div_fin_ok neg fl q2 s2 (by rw [hs2v]; omega) (by rw [hs2v]; omega)
      refine ⟨r2, by simpa using hr2, ?_⟩
      simp only [except_bind_ok]
      rw [← hrv.1, ← hrv.2]; exact hrr2
  | Err e =>
    cases hou : NetDecimal.overflowUnscale q.val sc.val true with
    | error e' =>
      intro hrv; simp only [resRel] at hrv
      exact ⟨_, rfl, by simp only [except_bind_error, resRel]; exact hrv⟩
    | ok w => simp [resRel]

theorem net.decimal.div_finish_refines (d1 d2 : net.decimal.NetDecimal) (st : net.decimal.DivState) (den : U128)
    (s : DS) (h : dRel st s) (hb : dB st den) (hden : 0 < den.val) (hden96 : den.val < 2^96) :
    ∃ r, net.decimal.div_finish d1 d2 st den = ok r ∧ resRel decRel r (divPost (d1.neg != d2.neg) den.val s) := by
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ := h
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  have hmax : U128.max = 2^128 - 1 := by simp [U128.max_eq]
  have hT := TWO96_eq
  generalize hTT : (⟨BitVec.ofNat 128 (2^96)⟩ : U128) = T at hT
  have hTv : T.val = 2^96 := by rw [← hTT]; exact TWO96_val
  have hge : ∀ x : U128, x >= T ↔ 2^96 ≤ x.val := fun x => by show T.val ≤ x.val ↔ _; rw [hTv]
  obtain ⟨fn, hfn, hfnv⟩ := div_fin_ok (d1.neg != d2.neg) st.flag st.q st.scale (by omega) hb4
  obtain ⟨q1, hq1, hq1v⟩ := eq_ok_of_spec (U128.add_spec (x := st.q) (y := 1#u128) (by simp [hmax]; omega))
  simp at hq1v
  -- the increment path
  have hinc : ∃ r, (do
      let q ← st.q + 1#u128
      let i1 ← net.decimal.TWO96
      if q >= i1 then
        let r ← net.decimal.overflow_unscale q st.scale true
        match r with
        | core.result.Result.Ok v =>
          let (q2, s2) := v
          let (q1, scale) ← (if st.flag then net.decimal.unscale q2 s2 else ok v)
          if scale < 0#i64 then ok (core.result.Result.Ok ({ neg := (d1.neg != d2.neg), mant := q1, scale := 0#u32 } : net.decimal.NetDecimal))
          else do
            let i2 ← lift (IScalar.hcast .U32 scale)
            ok (core.result.Result.Ok ({ neg := (d1.neg != d2.neg), mant := q1, scale := i2 } : net.decimal.NetDecimal))
        | core.result.Result.Err e => ok (core.result.Result.Err e)
      else
        let (q1, scale) ← (if st.flag then net.decimal.unscale q st.scale else ok (q, st.scale))
        if scale < 0#i64 then ok (core.result.Result.Ok ({ neg := (d1.neg != d2.neg), mant := q1, scale := 0#u32 } : net.decimal.NetDecimal))
        else do
          let i2 ← lift (IScalar.hcast .U32 scale)
          ok (core.result.Result.Ok ({ neg := (d1.neg != d2.neg), mant := q1, scale := i2 } : net.decimal.NetDecimal))) = ok r ∧
      resRel decRel r (if s.2.2.1 + 1 ≥ NetDecimal.two96 then do
          let x ← NetDecimal.overflowUnscale (s.2.2.1 + 1) s.1 true
          divFin (d1.neg != d2.neg) s.2.1 x.1 x.2
        else divFin (d1.neg != d2.neg) s.2.1 (s.2.2.1 + 1) s.1) := by
    rw [hq1, bind_ok, hT, bind_ok]
    by_cases ho : 2^96 ≤ st.q.val + 1
    · rw [if_pos ((hge _).mpr (by rw [hq1v]; exact ho)), if_pos (show s.2.2.1 + 1 ≥ NetDecimal.two96 by rw [← hs3]; exact ho)]
      obtain ⟨r, hr, hrr⟩ := div_ovf_ok (d1.neg != d2.neg) st.flag q1 st.scale (by omega) hb4
      refine ⟨r, hr, ?_⟩
      rw [← hs3, ← hs1, ← hs2, ← hq1v]; exact hrr
    · rw [if_neg (by rw [hge, hq1v]; exact ho), if_neg (show ¬ s.2.2.1 + 1 ≥ NetDecimal.two96 by rw [← hs3]; exact ho)]
      obtain ⟨r, hr, hrr⟩ := div_fin_ok (d1.neg != d2.neg) st.flag q1 st.scale (by omega) hb4
      refine ⟨r, hr, ?_⟩
      rw [← hs3, ← hs1, ← hs2, ← hq1v]; exact hrr
  obtain ⟨ri, hri, hrri⟩ := hinc
  unfold net.decimal.div_finish divPost
  rw [← hs5]
  cases hrd : st.round_it with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    refine ⟨fn, hfn, ?_⟩
    rw [← hs3, ← hs1, ← hs2]; exact hfnv
  | true =>
    simp only [if_true]
    obtain ⟨i, hi, hiv⟩ := eq_ok_of_spec (U128.mul_spec (x := 2#u128) (y := st.r) (by simp [hmax]; omega))
    simp at hiv
    rw [hi, bind_ok]
    have hcond : (decide (2 * s.2.2.2.1 > den.val) || 2 * s.2.2.2.1 == den.val && s.2.2.1 % 2 == 1) =
        (decide (2 * st.r.val > den.val) || 2 * st.r.val == den.val && st.q.val % 2 == 1) := by rw [hs3, hs4]
    rw [hcond]
    by_cases c1 : 2 * st.r.val > den.val
    · have c1' : i > den := by show den.val < i.val; rw [hiv]; exact c1
      rw [if_pos c1', if_pos (show (decide (2 * st.r.val > den.val) || 2 * st.r.val == den.val && st.q.val % 2 == 1) = true by simp [c1])]
      exact ⟨ri, hri, hrri⟩
    · have c1' : ¬ i > den := by show ¬ den.val < i.val; rw [hiv]; exact c1
      rw [if_neg c1']
      by_cases c2 : 2 * st.r.val = den.val
      · have c2' : i = den := UScalar.eq_of_val_eq (by rw [hiv]; exact c2)
        rw [if_pos c2']
        obtain ⟨m, hm, hmv⟩ := eq_ok_of_spec (UScalar.rem_spec st.q (y := 2#u128) (by simp))
        simp at hmv
        rw [hm, bind_ok]
        by_cases c3 : st.q.val % 2 = 1
        · have c3' : m = 1#u128 := UScalar.eq_of_val_eq (by rw [hmv]; simpa using c3)
          rw [if_pos c3', if_pos (show (decide (2 * st.r.val > den.val) || 2 * st.r.val == den.val && st.q.val % 2 == 1) = true by simp [c2, c3])]
          exact ⟨ri, hri, hrri⟩
        · have c3' : ¬ m = 1#u128 := fun he => c3 (by have := congrArg UScalar.val he; rw [hmv] at this; simpa using this)
          rw [if_neg c3', if_neg (show ¬ (decide (2 * st.r.val > den.val) || 2 * st.r.val == den.val && st.q.val % 2 == 1) = true by simp [c1, c3])]
          refine ⟨fn, hfn, ?_⟩
          rw [← hs3, ← hs1, ← hs2]; exact hfnv
      · have c2' : ¬ i = den := fun he => c2 (by rw [← hiv, he])
        rw [if_neg c2', if_neg (show ¬ (decide (2 * st.r.val > den.val) || 2 * st.r.val == den.val && st.q.val % 2 == 1) = true by simp [c1, c2])]
        refine ⟨fn, hfn, ?_⟩
        rw [← hs3, ← hs1, ← hs2]; exact hfnv

/-- Guarded: both operands are valid decimals (mantissa `< 2^96`, scale `≤ 28`). -/
theorem net.decimal.div_refines (d1 d2 : net.decimal.NetDecimal) (hm1 : d1.mant.val < 2^96) (hm2 : d2.mant.val < 2^96)
    (hs1 : d1.scale.val ≤ 28) (hs2 : d2.scale.val ≤ 28) :
    ∃ r, net.decimal.div d1 d2 = ok r ∧ resRel decRel r (NetDecimal.div (decS d1) (decS d2)) := by
  rw [div_nf]
  unfold net.decimal.div
  by_cases hz : d2.mant.val = 0
  · have hz' : d2.mant = 0#u128 := UScalar.eq_of_val_eq (by simp [hz])
    rw [if_pos hz', if_pos (show (decS d2).mant = 0 from hz)]
    exact ⟨_, rfl, rfl⟩
  · have hz' : ¬ d2.mant = 0#u128 := fun he => hz (by rw [he]; rfl)
    rw [if_neg hz', if_neg (show ¬ (decS d2).mant = 0 from hz)]
    have c1 := hcast_i64_u32 d1.scale
    have c2 := hcast_i64_u32 d2.scale
    obtain ⟨i2, hi2, hi2v⟩ := eq_ok_of_spec (I64.sub_spec (x := UScalar.hcast .I64 d1.scale) (y := UScalar.hcast .I64 d2.scale)
      (by rw [c1, c2]; simp [I64.min_eq]; omega) (by rw [c1, c2]; simp [I64.max_eq]; omega))
    rw [c1, c2] at hi2v
    obtain ⟨i3, hi3, hi3v⟩ := UScalar.div_spec d1.mant hz
    obtain ⟨i4, hi4, hi4v⟩ := eq_ok_of_spec (UScalar.rem_spec d1.mant hz)
    simp only [lift, bind_ok, hi2, hi3, hi4]
    have hden : 0 < d2.mant.val := by omega
    obtain ⟨y, hy, hyr⟩ := div_loop_ok d2.mant hden hm2
      (iterEx (divStep d2.mant.val) 40 ((d1.scale.val : Int) - d2.scale.val, false, d1.mant.val / d2.mant.val,
        d1.mant.val % d2.mant.val, false, false))
      (⟨i2, false, i3, i4, false, false⟩, 0#i32, none)
      (Or.inl ⟨rfl, ((d1.scale.val : Int) - d2.scale.val, false, d1.mant.val / d2.mant.val,
        d1.mant.val % d2.mant.val, false, false), ⟨hi2v, rfl, hi3v, hi4v, rfl, rfl⟩,
        ⟨by simp only; rw [hi3v]; have := Nat.div_le_self d1.mant.val d2.mant.val; omega,
         by simp only; rw [hi4v]; exact Nat.mod_lt _ hden, by simp only; omega, by simp only; omega⟩,
        fun _ => by simp only; rw [hi3v]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm1,
        by simp, by simp, by simp⟩)
    rw [hy, bind_ok]
    obtain ⟨y1, y2, y3, y4, y5, y6, y7⟩ := y
    rcases hyr with ⟨he, s, hrel, hb, hfin⟩ | ⟨e, he, hfin⟩
    · simp only at he; subst he
      obtain ⟨r, hr, hrr⟩ := net.decimal.div_finish_refines d1 d2 (dsOf (y1, y2, y3, y4, y5, y6, none)) d2.mant s
        hrel hb hden hm2
      refine ⟨r, hr, ?_⟩
      simp only [decS]
      rw [hfin, except_bind_ok]; exact hrr
    · simp only at he; subst he
      refine ⟨_, rfl, ?_⟩
      simp only [decS]
      rw [hfin, except_bind_error]; rfl

end OsuProofs
