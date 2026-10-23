/-
`net::decimal` part 5: the `ScaleResult` loop in lockstep with the spec loop, `ScaleResult`,
`decimal * decimal`.
-/
import OsuProofs.Net.Decimal4
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

theorem sr_chunk (num : I64) (h1 : 1 ≤ num.val) (h29 : num.val ≤ 29) :
    ∃ ch : U32, (if num >= 9#i64 then ok 9#u32 else if num < 0#i64 then ok 0#u32 else ok (IScalar.hcast .U32 num)) = ok ch ∧
      ch.val = (if num.val ≥ 9 then 9 else num.val.toNat) ∧ ch.val ≤ 9 := by
  by_cases h9 : 9 ≤ num.val
  · have h9' : num >= 9#i64 := by show (9#i64).val ≤ num.val; simpa using h9
    exact ⟨9#u32, by simp [h9'], by simp [h9], by simp⟩
  · have h9' : ¬ num >= 9#i64 := by show ¬ (9#i64).val ≤ num.val; simpa using h9
    have h0 : ¬ num < 0#i64 := by show ¬ num.val < (0#i64).val; simp; omega
    refine ⟨IScalar.hcast .U32 num, by simp [h9', h0], ?_, ?_⟩
    · rw [hcast_u32_val num (by omega) (by omega)]; simp [h9]
    · rw [hcast_u32_val num (by omega) (by omega)]; omega

theorem ite_round {α} (b1 b2 b3 b4 : Prop) [Decidable b1] [Decidable b2] [Decidable b3] [Decidable b4] (E N : α) :
    (if b1 then (if b2 then E else if b3 then E else if b4 then E else N) else N) =
      if b1 ∧ (b2 ∨ b3 ∨ b4) then E else N := by
  by_cases h1 : b1 <;> by_cases h2 : b2 <;> by_cases h3 : b3 <;> by_cases h4 : b4 <;> simp [h1, h2, h3, h4]

set_option maxHeartbeats 2000000 in
theorem sr_step (x : SRR) (s : SRS) (h : srRel x s) :
    ∃ x', net.decimal.scale_result_loop_loop.body x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1
        x.2.2.2.2.2.2 = ok (.cont x') ∧
      x'.2.2.2.2.2.2.val = x.2.2.2.2.2.2.val + 1 ∧
      (match srStep s with
       | .ok (.yield s') => srRel x' s'
       | .ok (.done s') => ∃ r, x'.2.2.2.2.2.1 = some r ∧ resRel qsR r (srPost s')
       | .error e => x'.2.2.2.2.2.1 = some (.Err (exnI e))) := by
  obtain ⟨q, sc, num, sticky, rem, res, it⟩ := x
  obtain ⟨r0, ns, ss, qs, sts, rs, pws⟩ := s
  obtain ⟨hres, hr0, hq, hsc, hnum, hst, hrem, hn1, hn29, hs0, hs56, hit0, hpot⟩ := h
  dsimp only at hres hr0 hq hsc hnum hst hrem hn1 hn29 hs0 hs56 hit0 hpot ⊢
  subst hres hr0 hst hq hsc hnum hrem
  have hit120 : it.val < 120 := by omega
  have hit' : it < 120#i32 := by show it.val < (120#i32).val; simpa using hit120
  obtain ⟨it1, hit1, hit1v⟩ := eq_ok_of_spec (I32.add_spec (x := it) (y := 1#i32)
    (by simp [I32.min_eq]; omega) (by simp [I32.max_eq]; omega))
  simp at hit1v
  obtain ⟨ch, hch, hchv, hch9⟩ := sr_chunk num hn1 hn29
  obtain ⟨pw0, hpw0, hpw0v⟩ := net.decimal.pow10_refines ch (by omega)
  have hpwl : 10 ^ ch.val < 2^64 := by
    calc 10 ^ ch.val ≤ 10 ^ 9 := Nat.pow_le_pow_right (by decide) hch9
      _ < 2^64 := by decide
  have hpwc : (UScalar.cast .U64 pw0).val = 10 ^ ch.val := by
    rw [UScalar.cast_val_eq, hpw0v]; simp; omega
  generalize hPW : UScalar.cast .U64 pw0 = pw at hpwc
  have hpwpos : 0 < pw.val := by rw [hpwc]; exact Nat.pow_pos (by decide)
  obtain ⟨q2, r2, hdm, hq2v, hr2v⟩ := net.decimal.u192_divmod_small_refines q pw hpwpos
  obtain ⟨num1, hnum1, hnum1v⟩ := eq_ok_of_spec (I64.sub_spec (x := num) (y := 9#i64)
    (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
  simp at hnum1v
  have hst1 : (if sticky then ok true else ok (rem != 0#u64) : Result Bool) = ok (sticky || rem.val != 0) := by
    have e : (rem = 0#u64) ↔ rem.val = 0 := ⟨fun h => by rw [h]; rfl, fun h => UScalar.eq_of_val_eq (by simp [h])⟩
    cases sticky <;> simp [bne, e]
  have hcv : (if num.val ≥ 9 then 9 else num.val.toNat) = ch.val := by exact hchv.symm
  have hge := net.decimal.u192_ge_two96_refines
  have p96 : NetDecimal.two96 = 2^96 := rfl
  by_cases hA : num.val - 9 > 0
  · have hA' : num1 > 0#i64 := by show (0#i64).val < num1.val; simp; omega
    refine ⟨(q2, sc, num1, sticky || rem.val != 0, r2, none, it1), ?_, by simp [hit1v], ?_⟩
    · simp only [net.decimal.scale_result_loop_loop.body, core.option.Option.is_none, hit', hit1, hst1, hch, hpw0,
        hPW, hdm, hnum1, bind_ok, lift, ite_true]
      simp [hA']
    · have hsp : srStep (none, num.val, sc.val, u192S q, sticky, rem.val, pws) =
          .ok (.yield (none, num.val - 9, sc.val, u192S q / 10 ^ ch.val, sticky || rem.val != 0,
            u192S q % 10 ^ ch.val, 10 ^ ch.val)) := by
        simp only [srStep, hcv, hA]; rfl
      rw [hsp]
      refine ⟨rfl, rfl, by rw [hq2v, hpwc], rfl, hnum1v, rfl, by rw [hr2v, hpwc], ?_⟩
      dsimp only; omega
  · have hA' : ¬ num1 > 0#i64 := by show ¬ (0#i64).val < num1.val; simp; omega
    have hQ : u192S q2 = u192S q / 10 ^ ch.val := by rw [hq2v, hpwc]
    have hR : r2.val = u192S q % 10 ^ ch.val := by rw [hr2v, hpwc]
    have hAv : ¬ (0 < num1.val) := by omega
    have hsc0 : sc = 0#i64 ↔ sc.val = 0 := i64_val_eq_zero sc
    by_cases hB : u192S q / 10 ^ ch.val ≥ 2^96
    all_goals have hBv := hB; simp only [show (2:Nat)^96 = 79228162514264337593543950336 from rfl] at hBv
    · have hB' : 79228162514264337593543950336 ≤ u192S q2 := by rw [hQ]; exact hB
      by_cases hs : sc.val = 0
      · refine ⟨(q2, sc, num1, sticky || rem.val != 0, r2, some (.Err .Overflow), it1), ?_, by simp [hit1v], ?_⟩
        · simp only [net.decimal.scale_result_loop_loop.body, core.option.Option.is_none, hit', hit1, hst1, hch,
            bind_ok, lift, ite_true]
          simp [hpw0, hPW, hdm, hnum1, hAv, hge, hB', (hsc0).mpr hs]
        · have hsp : srStep (none, num.val, sc.val, u192S q, sticky, rem.val, pws) = .error .overflow := by
            simp only [srStep, hcv, hA, p96]; simp [hBv, hs]
          rw [hsp]; rfl
      · obtain ⟨sc1, hsc1, hsc1v⟩ := i64_sub_one sc (by omega) (by omega)
        refine ⟨(q2, sc1, 1#i64, sticky || rem.val != 0, r2, none, it1), ?_, by simp [hit1v], ?_⟩
        · simp only [net.decimal.scale_result_loop_loop.body, core.option.Option.is_none, hit', hit1, hst1, hch,
            bind_ok, lift, ite_true]
          simp [hpw0, hPW, hdm, hnum1, hAv, hge, hB', hsc0, hs, hsc1]
        · have hsp : srStep (none, num.val, sc.val, u192S q, sticky, rem.val, pws) =
              .ok (.yield (none, 1, sc.val - 1, u192S q / 10 ^ ch.val, sticky || rem.val != 0,
                u192S q % 10 ^ ch.val, 10 ^ ch.val)) := by
            simp only [srStep, hcv, hA, p96]; simp [hBv, hs]
          rw [hsp]
          refine ⟨rfl, rfl, hQ, hsc1v, by simp, rfl, hR, by simp, by simp, by dsimp only; omega, by dsimp only; omega,
            by dsimp only; omega, ?_⟩
          dsimp only; simp; omega
    · have hB'' : ¬ 79228162514264337593543950336 ≤ u192S q2 := by rw [hQ]; exact hBv
      have hQl : u192S q2 < 2^128 := by rw [p128_eq]; omega
      have hlo : q2.lo.val = u192S q / 10 ^ ch.val := by rw [u192_lo_of_lt q2 hQl, hQ]
      have hhi : q2.hi.val = 0 := by
        have := u128_bounds q2.lo; unfold u192S at hQl hB''
        by_contra hne; have : q2.hi.val * 2^128 ≥ 2^128 := Nat.le_mul_of_pos_left _ (by omega); omega
      obtain ⟨half, hhalf, hhalfv⟩ := UScalar.div_spec pw (y := 2#u64) (by simp)
      simp only [hpwc] at hhalfv
      have hpar : (q2.lo &&& 1#u128 = 1#u128) ↔ u192S q / 10 ^ ch.val % 2 = 1 := by
        rw [uscalar_eq_val]
        have : (q2.lo &&& 1#u128).val = q2.lo.val % 2 := by
          simp only [UScalar.val, UScalar.bv_and, BitVec.toNat_and]; rw [← UScalar.val]; simp [Nat.and_one_is_mod]
        rw [this, hlo]; simp
      obtain ⟨q1, hq1, hq1v⟩ := net.decimal.u192_add_one_refines q2 (by rw [hhi]; decide)
      have hst' : (sticky = true ∨ ¬ rem.val = 0) ↔ (sticky || rem.val != 0) = true := by simp
      have hge1 : net.decimal.u192_ge_two96 q1 = ok (decide (u192S q / 10 ^ ch.val + 1 ≥ 2^96)) := by
        rw [hge, hq1v, hQ]
      have hlo1 : u192S q / 10 ^ ch.val + 1 < 2^96 → q1.lo.val = u192S q / 10 ^ ch.val + 1 := by
        intro h; rw [u192_lo_of_lt q1 (by rw [hq1v, hQ, p128_eq]; rw [show (2:Nat)^96 = 79228162514264337593543950336 from rfl] at h; omega), hq1v, hQ]
      have hscv : (IScalar.hcast .U32 sc).val = sc.val.toNat := hcast_u32_val sc hs0 (by omega)
      have hsp0 : srStep (none, num.val, sc.val, u192S q, sticky, rem.val, pws) =
          (let Q := u192S q / 10 ^ ch.val; let R := u192S q % 10 ^ ch.val; let pow := 10 ^ ch.val
           let st := sticky || rem.val != 0
           if (decide (pow / 2 ≤ R) && (decide (pow / 2 < R) || Q % 2 == 1 || st)) = true then
             if Q + 1 ≥ NetDecimal.two96 then
               if (sc.val == 0) = true then throw .overflow else pure (.yield (none, 1, sc.val - 1, Q + 1, false, 0, pow))
             else pure (.done (some (Q + 1, sc.val.toNat), num.val - 9, sc.val, Q + 1, st, R, pow))
           else pure (.done (some (Q, sc.val.toNat), num.val - 9, sc.val, Q, st, R, pow))) := by
        simp only [srStep, hcv, hA, ite_false]
        rw [if_neg (by rw [p96]; exact hB)]
      rw [hsp0]
      dsimp only
      have hbodyC : net.decimal.scale_result_loop_loop.body q sc num sticky rem none it =
          (if (10 ^ ch.val / 2 ≤ u192S q % 10 ^ ch.val ∧ (10 ^ ch.val / 2 < u192S q % 10 ^ ch.val ∨
              u192S q / 10 ^ ch.val % 2 = 1 ∨ (sticky || rem.val != 0) = true)) then
            (do let q1 ← net.decimal.u192_add_one q2
                let b2 ← net.decimal.u192_ge_two96 q1
                if b2 = true then
                  (if sc = 0#i64 then ok (ControlFlow.cont (q1, sc, num1, sticky || rem.val != 0, r2,
                      some (core.result.Result.Err net.basic.NetExn.Overflow), it1))
                   else do let sc1 ← sc - 1#i64; ok (ControlFlow.cont (q1, sc1, 1#i64, false, 0#u64, none, it1)))
                else ok (ControlFlow.cont (q1, sc, num1, sticky || rem.val != 0, r2,
                    some (core.result.Result.Ok (q1.lo, IScalar.hcast .U32 sc)), it1)))
          else ok (ControlFlow.cont (q2, sc, num1, sticky || rem.val != 0, r2,
                    some (core.result.Result.Ok (q2.lo, IScalar.hcast .U32 sc)), it1))) := by
        simp only [net.decimal.scale_result_loop_loop.body, core.option.Option.is_none, hit', hit1, hst1, hch,
          bind_ok, lift, ite_true]
        by_cases c1 : 10 ^ ch.val / 2 ≤ u192S q % 10 ^ ch.val
        · by_cases c2 : 10 ^ ch.val / 2 < u192S q % 10 ^ ch.val
          · simp [hpw0, hPW, hdm, hnum1, hAv, hge, hB'', hhalf, hhalfv, hR, c1, c2]
          · by_cases c3 : u192S q / 10 ^ ch.val % 2 = 1
            · simp [hpw0, hPW, hdm, hnum1, hAv, hge, hB'', hhalf, hhalfv, hR, hpar, c1, c2, c3]
            · by_cases c4 : (sticky || rem.val != 0) = true
              · simp [hpw0, hPW, hdm, hnum1, hAv, hge, hB'', hhalf, hhalfv, hR, hpar, c1, c2, c3, c4]
              · simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at c4
                simp [hpw0, hPW, hdm, hnum1, hAv, hge, hB'', hhalf, hhalfv, hR, hpar, c1, c2, c3, c4]
        · simp [hpw0, hPW, hdm, hnum1, hAv, hge, hB'', hhalf, hhalfv, hR, c1]
      rw [hbodyC]
      by_cases hinc : (10 ^ ch.val / 2 ≤ u192S q % 10 ^ ch.val) ∧ (10 ^ ch.val / 2 < u192S q % 10 ^ ch.val ∨
          u192S q / 10 ^ ch.val % 2 = 1 ∨ (sticky || rem.val != 0) = true)
      · have hinc' : (decide (10 ^ ch.val / 2 ≤ u192S q % 10 ^ ch.val) && (decide (10 ^ ch.val / 2 < u192S q % 10 ^ ch.val) ||
            u192S q / 10 ^ ch.val % 2 == 1 || (sticky || rem.val != 0))) = true := by
          have h := hinc
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, or_assoc] at h ⊢; exact h
        rw [if_pos hinc', if_pos hinc]
        simp only [hq1, bind_ok, hge1]
        by_cases hov : u192S q / 10 ^ ch.val + 1 ≥ 2^96
        all_goals have hovv := hov; simp only [show (2:Nat)^96 = 79228162514264337593543950336 from rfl] at hovv
        · have hov' : u192S q / 10 ^ ch.val + 1 ≥ NetDecimal.two96 := hov
          have hovn : 79228162514264337593543950335 ≤ u192S q / 10 ^ ch.val := by omega
          rw [if_pos hov']
          by_cases hs : sc.val = 0
          · have hs' : (sc.val == 0) = true := by simp [hs]
            rw [if_pos hs']
            exact ⟨(q1, sc, num1, sticky || rem.val != 0, r2, some (.Err .Overflow), it1),
              by simp [hovn, (hsc0).mpr hs], by simp [hit1v], rfl⟩
          · have hs' : ¬ (sc.val == 0) = true := by simp [hs]
            rw [if_neg hs']
            obtain ⟨sc1, hsc1, hsc1v⟩ := i64_sub_one sc (by omega) (by omega)
            refine ⟨(q1, sc1, 1#i64, false, 0#u64, none, it1), by simp [hovn, hsc0, hs, hsc1], by simp [hit1v], ?_⟩
            refine ⟨rfl, rfl, by rw [hq1v, hQ], hsc1v, by simp, rfl, by simp, by simp, by simp, by dsimp only; omega,
              by dsimp only; omega, by dsimp only; omega, ?_⟩
            dsimp only; simp; omega
        · have hov' : ¬ u192S q / 10 ^ ch.val + 1 ≥ NetDecimal.two96 := hov
          rw [if_neg hov']
          have hovn : ¬ 79228162514264337593543950335 ≤ u192S q / 10 ^ ch.val := by omega
          refine ⟨(q1, sc, num1, sticky || rem.val != 0, r2, some (.Ok (q1.lo, IScalar.hcast .U32 sc)), it1),
            by simp [hovn], by simp [hit1v], ⟨_, rfl, ⟨by rw [hlo1 (by omega)], by rw [hscv]⟩⟩⟩
      · have hinc' : ¬ (decide (10 ^ ch.val / 2 ≤ u192S q % 10 ^ ch.val) && (decide (10 ^ ch.val / 2 < u192S q % 10 ^ ch.val) ||
            u192S q / 10 ^ ch.val % 2 == 1 || (sticky || rem.val != 0))) = true := by
          have h := hinc
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, or_assoc] at h ⊢; exact h
        rw [if_neg hinc', if_neg hinc]
        exact ⟨_, rfl, by simp [hit1v], ⟨_, rfl, ⟨by rw [hlo], by rw [hscv]⟩⟩⟩

end OsuProofs
