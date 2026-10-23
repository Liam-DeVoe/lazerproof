/-
`net::decimal` part 7: `ScaleResult` and `decimal * decimal` (`VarDecMul`).
-/
import OsuProofs.Net.Decimal6
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

theorem u192S_lt (x : net.decimal.U192) : u192S x < 2^192 := by
  have h1 := u128_bounds x.lo; have h2 := u64_bounds x.hi
  unfold u192S
  calc x.hi.val * 2^128 + x.lo.val < x.hi.val * 2^128 + 2^128 := by omega
    _ = (x.hi.val + 1) * 2^128 := by ring
    _ ≤ 2^64 * 2^128 := Nat.mul_le_mul_right _ (by omega)
    _ = 2^192 := by norm_num

theorem sar8_eq (v : Int) (h : 0 ≤ v) : NetDecimal.sar v 8 = v / 256 := by
  unfold NetDecimal.sar; rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]; rfl

theorem log_num_bounds (L : Nat) (h1 : 96 ≤ L) (h2 : L < 192) :
    0 ≤ (((L + 1 : Nat) : Int) - 97) * 77 / 256 ∧ (((L + 1 : Nat) : Int) - 97) * 77 / 256 ≤ 28 := by
  omega

theorem log_num_nonneg (L : Nat) (h1 : 96 ≤ L) : 0 ≤ (((L + 1 : Nat) : Int) - 97) * 77 := by
  omega

theorem hcast_i64_u32 (x : U32) : (UScalar.hcast .I64 x).val = (x.val : Int) := by
  rw [UScalar.hcast_val_eq]
  have hb : x.val < 2^32 := by have := x.hBounds; simpa using this
  exact Int.bmod_eq_of_le (by simp) (by simp; omega)

/-- The common tail of `scale_result` once `num` is known (`1 ≤ num ≤ 29`, `num ≤ scale`). -/
theorem sr_tail (p : net.decimal.U192) (scale : U32) (hs : scale.val ≤ 56) (n : I64) (hn0 : 0 ≤ n.val)
    (hn29 : n.val ≤ 29) (hns : n.val ≤ scale.val) (hz : n.val = 0 → u192S p < 2^128) :
    ∃ r, (do
      let i1 ← lift (UScalar.hcast .I64 scale)
      let i2 ← i1 - 28#i64
      let num1 ← if n < i2 then do let i3 ← lift (UScalar.hcast .I64 scale); i3 - 28#i64 else ok n
      if num1 = 0#i64 then ok (core.result.Result.Ok (p.lo, scale))
      else do
        let i3 ← lift (UScalar.hcast .I64 scale)
        let i4 ← i3 - num1
        net.decimal.scale_result_loop p i4 num1) = ok r ∧
      resRel qsR r (
        let num := if n.val < (scale.val : Int) - 28 then (scale.val : Int) - 28 else n.val
        if num = 0 then .ok (u192S p, scale.val)
        else iterEx srStep 120 (none, num, scale.val - num, u192S p, false, 0, 1) >>= srPost) := by
  have hsI : (UScalar.hcast .I64 scale).val = (scale.val : Int) := hcast_i64_u32 scale
  obtain ⟨i2, hi2, hi2v⟩ := eq_ok_of_spec (I64.sub_spec (x := UScalar.hcast .I64 scale) (y := 28#i64)
    (by rw [hsI]; simp [I64.min_eq]; omega) (by rw [hsI]; simp [I64.max_eq]; omega))
  simp only [hsI] at hi2v; simp at hi2v
  -- the effective `num` (≥ 1)
  obtain ⟨m, hm, hmv⟩ : ∃ m : I64, (if n < i2 then ok i2 else ok n : Result I64) = ok m ∧ m.val = (if n.val < (scale.val : Int) - 28 then (scale.val : Int) - 28 else n.val) := by
    by_cases hlt : n.val < (scale.val : Int) - 28
    · have hlt' : n < i2 := by show n.val < i2.val; rw [hi2v]; exact hlt
      exact ⟨i2, by simp [hlt'], by rw [hi2v]; simp [hlt]⟩
    · have hlt' : ¬ n < i2 := by show ¬ n.val < i2.val; rw [hi2v]; exact hlt
      exact ⟨n, by simp [hlt'], by simp [hlt]⟩
  by_cases hmz : m.val = 0
  · have hm0 : m = 0#i64 := (i64_val_eq_zero m).mpr hmz
    have hmz' : (if n.val < (scale.val : Int) - 28 then (scale.val : Int) - 28 else n.val) = 0 := by rw [← hmv]; exact hmz
    have hn : n.val = 0 := by revert hmz'; split <;> omega
    refine ⟨.Ok (p.lo, scale), ?_, ?_⟩
    · simp only [lift, bind_ok, hi2, hm, hm0, if_true]
    · simp only [hmz', if_true]
      exact ⟨u192_lo_of_lt p (hz hn), rfl⟩
  have hm1 : 1 ≤ m.val := by rw [hmv]; revert hmz; rw [hmv]; split <;> omega
  have hm29 : m.val ≤ 29 := by rw [hmv]; split <;> omega
  have hms : m.val ≤ scale.val := by rw [hmv]; split <;> omega
  have hm0 : ¬ m = 0#i64 := by intro h; rw [h] at hm1; simp at hm1
  have hm0' : ¬ (if n.val < (scale.val : Int) - 28 then (scale.val : Int) - 28 else n.val) = 0 := by
    rw [← hmv]; omega
  obtain ⟨sc0, hsc0, hsc0v⟩ := eq_ok_of_spec (I64.sub_spec (x := UScalar.hcast .I64 scale) (y := m)
    (by rw [hsI]; simp [I64.min_eq]; omega) (by rw [hsI]; simp [I64.max_eq]; omega))
  rw [hsI] at hsc0v
  have hrel : srRel (p, sc0, m, false, 0#u64, none, 0#i32) (none, m.val, sc0.val, u192S p, false, 0, 1) := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp, hm1, hm29, by dsimp only; omega, by dsimp only; omega, by simp, ?_⟩
    dsimp only; simp; omega
  obtain ⟨r, hr, hrr⟩ := sr_loop_run p sc0 m _ hrel rfl
  refine ⟨r, ?_, ?_⟩
  · simp only [lift, bind_ok, hi2, hm, hm0, if_false, hsc0, hr]
  · simp only [hm0', if_false]
    rw [← hmv, show (scale.val : Int) - m.val = sc0.val by omega]
    exact hrr

/-- Guarded: `scale ≤ 56` (the sum of two decimal scales). -/
theorem net.decimal.scale_result_refines (p : net.decimal.U192) (scale : U32) (hs : scale.val ≤ 56) :
    ∃ r, net.decimal.scale_result p scale = ok r ∧ resRel qsR r (NetDecimal.scaleResult (u192S p) scale.val) := by
  rw [scaleResult_nf]
  have hpb := u192S_lt p
  obtain ⟨b, hb, hbv⟩ := net.decimal.u192_bitlen_refines p
  have hbI : (UScalar.hcast .I64 b).val = (b.val : Int) := hcast_i64_u32 b
  have hsI : (UScalar.hcast .I64 scale).val = (scale.val : Int) := hcast_i64_u32 scale
  have hlog : u192S p ≠ 0 → (u192S p).log2 < 192 := fun h => (Nat.log2_lt h).mpr hpb
  unfold net.decimal.scale_result
  simp only [hb, lift, bind_ok, net.decimal.u192_ge_two96_refines]
  by_cases h96 : u192S p ≥ 2^96
  · have h96' : u192S p ≥ NetDecimal.two96 := h96
    have hp0 : u192S p ≠ 0 := by omega
    have hlg : 96 ≤ (u192S p).log2 := (Nat.le_log2 hp0).mpr h96
    have hl192 := hlog hp0
    rw [if_neg hp0] at hbv
    obtain ⟨i1, hi1, hi1v⟩ := eq_ok_of_spec (I64.sub_spec (x := UScalar.hcast .I64 b) (y := 97#i64)
      (by rw [hbI]; simp [I64.min_eq]; omega) (by rw [hbI]; simp [I64.max_eq]; omega))
    simp only [hbI] at hi1v; simp at hi1v
    obtain ⟨i2, hi2, hi2v⟩ := eq_ok_of_spec (I64.mul_spec (x := i1) (y := 77#i64)
      (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
    simp at hi2v
    obtain ⟨i3, hi3, hi3v⟩ := net.decimal.sar_refines i2 8#u32 (by simp)
    have hi2nn : 0 ≤ i2.val := by rw [hi2v, hi1v, hbv]; omega
    have hS : NetDecimal.sar i2.val 8 = i2.val / 256 := sar8_eq _ hi2nn
    have h8 : ((8#u32 : U32).val) = 8 := by simp
    have hi3e : i3.val = (((u192S p).log2 + 1 : Nat) - (97 : Int)) * 77 / 256 := by
      rw [hi3v, h8, hS, hi2v, hi1v, hbv]
    have hi3b : 0 ≤ i3.val ∧ i3.val ≤ 28 := by rw [hi3e]; exact log_num_bounds _ hlg hl192
    clear hlog hpb hi3v hS hi2nn
    obtain ⟨n1, hn1, hn1v⟩ := i64_add_one i3 (by clear * - hi3b; omega) (by clear * - hi3b; omega)
    have hspecN : NetDecimal.sar ((((u192S p).log2 + 1 : Nat) - (97 : Int)) * 77) 8 + 1 = n1.val := by
      rw [hn1v, sar8_eq _ (log_num_nonneg _ hlg), hi3e]
    clear hi3e
    have hdec : decide (u192S p ≥ 2^96) = true := decide_eq_true h96
    have h96n : 79228162514264337593543950336 ≤ u192S p := h96
    simp only [h96', if_true, true_and, hdec, hi1, hi2, hi3, hn1, bind_ok]
    rw [hspecN]
    by_cases hbad : n1.val > scale.val
    · have hbad' : n1 > UScalar.hcast .I64 scale := by show (UScalar.hcast .I64 scale).val < n1.val; rw [hsI]; exact hbad
      refine ⟨.Err .Overflow, ?_, ?_⟩
      · simp [hbad', h96n]
      · rw [if_pos hbad]; rfl
    · have hbad' : ¬ n1 > UScalar.hcast .I64 scale := by
        show ¬ (UScalar.hcast .I64 scale).val < n1.val; rw [hsI]; exact hbad
      rw [if_neg hbad]
      obtain ⟨r, hr, hrr⟩ := sr_tail p scale hs n1 (by clear * - hn1v hi3b; omega) (by clear * - hn1v hi3b; omega)
        (by clear * - hbad; omega) (by clear * - hn1v hi3b; omega)
      refine ⟨r, ?_, hrr⟩
      simp only [lift, bind_ok] at hr
      simp [hbad', h96n]
      simpa using hr
  · have h96' : ¬ u192S p ≥ NetDecimal.two96 := h96
    simp only [h96', if_false, false_and, decide_false, bind_ok, Bool.false_eq_true]
    obtain ⟨r, hr, hrr⟩ := sr_tail p scale hs 0#i64 (by simp) (by simp) (by simp)
      (fun _ => by clear * - h96; rw [p128_eq]; rw [show (2:Nat)^96 = 79228162514264337593543950336 from rfl] at h96; omega)
    have h96n : ¬ 79228162514264337593543950336 ≤ u192S p := h96
    refine ⟨r, ?_, by simpa using hrr⟩
    simp only [lift, bind_ok] at hr
    simp [h96n]
    simpa using hr

/-! ## `decimal * decimal` -/

theorem mul_nf (d1 d2 : NetDecimal) : NetDecimal.mul d1 d2 =
    (if d1.mant < 2^32 ∧ d2.mant < 2^32 then
      (if d1.scale + d2.scale > 28 then
        (if d1.scale + d2.scale > 47 then .ok NetDecimal.zero
         else
          let pw := 10 ^ (d1.scale + d2.scale - 28)
          let q := d1.mant * d2.mant / pw
          let item := d1.mant * d2.mant % pw
          .ok ⟨d1.neg != d2.neg, if item ≥ pw / 2 ∧ (item > pw / 2 ∨ q % 2 = 1) then q + 1 else q, 28⟩)
       else .ok ⟨d1.neg != d2.neg, d1.mant * d2.mant, d1.scale + d2.scale⟩)
    else
      (if d1.mant * d2.mant = 0 then .ok NetDecimal.zero
       else if d1.mant * d2.mant ≥ NetDecimal.two96 ∨ d1.scale + d2.scale > 28 then
         (NetDecimal.scaleResult (d1.mant * d2.mant) (d1.scale + d2.scale)) >>= fun qs => .ok ⟨d1.neg != d2.neg, qs.1, qs.2⟩
       else .ok ⟨d1.neg != d2.neg, d1.mant * d2.mant, d1.scale + d2.scale⟩)) := by
  unfold NetDecimal.mul
  by_cases hs : d1.mant < 2^32 ∧ d2.mant < 2^32
  · simp only [hs, and_self, decide_true, Bool.and_self, if_true, ite_true]
    by_cases h28 : d1.scale + d2.scale > 28
    · by_cases h47 : d1.scale + d2.scale > 47
      · simp [h28, h47]
      · simp [h28, h47]
    · simp [h28]
  · rw [if_neg hs]
    have hs' : (decide (d1.mant < 2^32) && decide (d2.mant < 2^32)) = false := by simpa using hs
    simp only [hs', Bool.false_eq_true, if_false, ite_false]
    by_cases hz : d1.mant * d2.mant = 0
    · simp [hz]
    · by_cases hb : d1.mant * d2.mant ≥ NetDecimal.two96 ∨ d1.scale + d2.scale > 28
      · simp [hz, hb]
      · simp [hz, hb]


theorem u128_shl32_one : ∃ z, (1#u128 : U128) <<< 32#i32 = ok z ∧ z.val = 2^32 := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (UScalar.ShiftLeft_IScalar_spec (1#u128 : U128) (y := 32#i32) (2^128) (by simp) (by simp)
    (by simp [U128.size_eq]))
  exact ⟨z, hz, by simpa [Nat.shiftLeft_eq] using hv.1⟩

theorem mul_sr_tail (pp : net.decimal.U192) (sc : U32) (hs : sc.val ≤ 56) (neg : Bool) :
    ∃ r, (do
      let r ← net.decimal.scale_result pp sc
      match r with
      | core.result.Result.Ok v =>
        let (q, s) := v
        ok (core.result.Result.Ok ({ neg := neg, mant := q, scale := s } : net.decimal.NetDecimal))
      | core.result.Result.Err e => ok (core.result.Result.Err e)) = ok r ∧
      resRel decRel r (NetDecimal.scaleResult (u192S pp) sc.val >>= fun qs => .ok ⟨neg, qs.1, qs.2⟩) := by
  obtain ⟨r, hr, hrr⟩ := net.decimal.scale_result_refines pp sc hs
  rw [hr, bind_ok]
  revert hrr
  cases r with
  | Ok v =>
    obtain ⟨q, s⟩ := v
    cases hsp : NetDecimal.scaleResult (u192S pp) sc.val with
    | error e => simp [resRel]
    | ok w =>
      intro hrr
      simp only [resRel, qsR] at hrr
      exact ⟨_, rfl, by simp [resRel, decRel, decS, hrr.1, hrr.2]⟩
  | Err e =>
    cases hsp : NetDecimal.scaleResult (u192S pp) sc.val with
    | error e' => intro hrr; exact ⟨_, rfl, by simp only [resRel] at hrr ⊢; exact hrr⟩
    | ok w => simp [resRel]

/-- Guarded: both operands are valid decimals (mantissa `< 2^96`, scale `≤ 28`). -/
theorem net.decimal.mul_refines (d1 d2 : net.decimal.NetDecimal) (hm1 : d1.mant.val < 2^96) (hm2 : d2.mant.val < 2^96)
    (hs1 : d1.scale.val ≤ 28) (hs2 : d2.scale.val ≤ 28) :
    ∃ r, net.decimal.mul d1 d2 = ok r ∧ resRel decRel r (NetDecimal.mul (decS d1) (decS d2)) := by
  obtain ⟨sc, hsc, hscv⟩ := eq_ok_of_spec (U32.add_spec (x := d1.scale) (y := d2.scale) (by simp [U32.max_eq]; omega))
  obtain ⟨t32, ht32, ht32v⟩ := u128_shl32_one
  have hmax : U128.max = 2^128 - 1 := by simp [U128.max_eq]
  rw [mul_nf]
  simp only [decS, ← hscv]
  unfold net.decimal.mul
  simp only [hsc, ht32, bind_ok]
  have hlt : ∀ x : U128, x < t32 ↔ x.val < 2^32 := fun x => by
    show x.val < t32.val ↔ _; rw [ht32v]
  by_cases hsm : d1.mant.val < 2^32 ∧ d2.mant.val < 2^32
  · rw [if_pos hsm, if_pos ((hlt _).mpr hsm.1), if_pos ((hlt _).mpr hsm.2)]
    have hpl : d1.mant.val * d2.mant.val < 2^64 := by
      calc d1.mant.val * d2.mant.val < 2^32 * 2^32 := Nat.mul_lt_mul'' hsm.1 hsm.2
        _ = 2^64 := by norm_num
    obtain ⟨p, hp, hpv⟩ := eq_ok_of_spec (U128.mul_spec (x := d1.mant) (y := d2.mant) (by rw [hmax]; omega))
    rw [hp, bind_ok]
    by_cases h28 : sc.val > 28
    · have h28' : sc > 28#u32 := by show (28#u32).val < sc.val; simpa using h28
      rw [if_pos h28', if_pos h28]
      by_cases h47 : sc.val > 47
      · have h47' : sc > 47#u32 := by show (47#u32).val < sc.val; simpa using h47
        rw [if_pos h47', if_pos h47]
        exact ⟨_, rfl, by simp [resRel, decRel]⟩
      · have h47' : ¬ sc > 47#u32 := by show ¬ (47#u32).val < sc.val; simpa using h47
        rw [if_neg h47', if_neg h47]
        obtain ⟨i1, hi1, hi1v, _⟩ := eq_ok_of_spec (U32.sub_spec (x := sc) (y := 28#u32) (by simp; omega))
        simp at hi1v
        obtain ⟨pw, hpw, hpwv⟩ := net.decimal.pow10_refines i1 (by omega)
        have hpw0 : pw.val ≠ 0 := by rw [hpwv]; exact Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide))
        obtain ⟨q, hq, hqv⟩ := UScalar.div_spec p hpw0
        obtain ⟨item, hitem, hitemv⟩ := eq_ok_of_spec (UScalar.rem_spec p hpw0)
        obtain ⟨half, hhalf, hhalfv⟩ := UScalar.div_spec pw (y := 2#u128) (by simp)
        rw [hi1, bind_ok, hpw, bind_ok, hq, bind_ok, hitem, bind_ok, hhalf, bind_ok]
        have hQ : q.val = d1.mant.val * d2.mant.val / 10 ^ (sc.val - 28) := by rw [hqv, hpv, hpwv, hi1v]
        have hR : item.val = d1.mant.val * d2.mant.val % 10 ^ (sc.val - 28) := by rw [hitemv, hpv, hpwv, hi1v]
        have hA : half.val = 10 ^ (sc.val - 28) / 2 := by rw [hhalfv, hpwv, hi1v]; rfl
        have hql : q.val + 1 ≤ U128.max := by
          rw [hmax, hQ]; have := Nat.div_le_self (d1.mant.val * d2.mant.val) (10 ^ (sc.val - 28)); omega
        obtain ⟨q1, hq1, hq1v⟩ := eq_ok_of_spec (U128.add_spec (x := q) (y := 1#u128) (by simpa using hql))
        obtain ⟨m2, hm2', hm2v⟩ := eq_ok_of_spec (UScalar.rem_spec q (y := 2#u128) (by simp))
        by_cases c1 : 10 ^ (sc.val - 28) / 2 ≤ d1.mant.val * d2.mant.val % 10 ^ (sc.val - 28)
        · have c1' : item >= half := by show half.val ≤ item.val; rw [hA, hR]; exact c1
          rw [if_pos c1']
          by_cases c2 : 10 ^ (sc.val - 28) / 2 < d1.mant.val * d2.mant.val % 10 ^ (sc.val - 28)
          · have c2' : item > half := by show half.val < item.val; rw [hA, hR]; exact c2
            rw [if_pos c2', hq1, bind_ok]
            exact ⟨_, rfl, by simp [resRel, decRel, decS, hq1v, hQ, c1, c2]⟩
          · have c2' : ¬ item > half := by show ¬ half.val < item.val; rw [hA, hR]; exact c2
            rw [if_neg c2', hm2', bind_ok]
            by_cases c3 : d1.mant.val * d2.mant.val / 10 ^ (sc.val - 28) % 2 = 1
            · have c3' : m2 = 1#u128 := UScalar.eq_of_val_eq (by rw [hm2v, hQ]; simpa using c3)
              rw [if_pos c3', hq1, bind_ok]
              exact ⟨_, rfl, by simp [resRel, decRel, decS, hq1v, hQ, c1, c2, c3]⟩
            · have c3' : ¬ m2 = 1#u128 := fun h => c3 (by rw [← hQ]; have := congrArg UScalar.val h; rw [hm2v] at this; simpa using this)
              rw [if_neg c3']
              exact ⟨_, rfl, by simp [resRel, decRel, decS, hQ, c1, c2, c3]⟩
        · have c1' : ¬ item >= half := by show ¬ half.val ≤ item.val; rw [hA, hR]; exact c1
          rw [if_neg c1']
          exact ⟨_, rfl, by simp [resRel, decRel, decS, hQ, c1]⟩
    · have h28' : ¬ sc > 28#u32 := by show ¬ (28#u32).val < sc.val; simpa using h28
      rw [if_neg h28', if_neg h28]
      exact ⟨_, rfl, by simp [resRel, decRel, decS, hpv]⟩
  · rw [if_neg hsm]
    have hbigc : (¬ d1.mant < t32) ∨ (d1.mant < t32 ∧ ¬ d2.mant < t32) := by
      by_cases c1 : d1.mant.val < 2^32
      · right; exact ⟨(hlt _).mpr c1, fun h => hsm ⟨c1, (hlt _).mp h⟩⟩
      · left; exact fun h => c1 ((hlt _).mp h)
    obtain ⟨pp, hpp, hppv⟩ := net.decimal.mul_u96_refines d1.mant d2.mant hm1 hm2
    have hsc56 : sc.val ≤ 56 := by omega
    rcases hbigc with c1 | ⟨c1, c2⟩
    all_goals first | rw [if_neg c1] | rw [if_pos c1, if_neg c2]
    all_goals
      rw [hpp, bind_ok, net.decimal.u192_is_zero_refines, bind_ok, hppv]
      by_cases hz : d1.mant.val * d2.mant.val = 0
      · rw [if_pos (by simp [hz]), if_pos hz]
        exact ⟨_, rfl, by simp [resRel, decRel]⟩
      · rw [if_neg (by simp [hz]), if_neg hz, net.decimal.u192_ge_two96_refines, bind_ok, hppv]
        by_cases h96 : d1.mant.val * d2.mant.val ≥ 2^96
        · have h96' : d1.mant.val * d2.mant.val ≥ NetDecimal.two96 := h96
          rw [if_pos (decide_eq_true h96), if_pos (Or.inl h96')]
          obtain ⟨r, hr, hrr⟩ := mul_sr_tail pp sc hsc56 (d1.neg != d2.neg)
          rw [hppv] at hrr
          exact ⟨r, hr, hrr⟩
        · rw [if_neg (by simpa using h96)]
          by_cases h28 : sc.val > 28
          · have h28' : sc > 28#u32 := by show (28#u32).val < sc.val; simpa using h28
            rw [if_pos h28', if_pos (Or.inr h28)]
            obtain ⟨r, hr, hrr⟩ := mul_sr_tail pp sc hsc56 (d1.neg != d2.neg)
            rw [hppv] at hrr
            exact ⟨r, hr, hrr⟩
          · have h28' : ¬ sc > 28#u32 := by show ¬ (28#u32).val < sc.val; simpa using h28
            have h96' : ¬ d1.mant.val * d2.mant.val ≥ NetDecimal.two96 := h96
            rw [if_neg h28', if_neg (by rintro (h | h) <;> contradiction)]
            have hlo : pp.lo.val = d1.mant.val * d2.mant.val := by
              rw [u192_lo_of_lt pp (by rw [hppv, p128_eq]; rw [show (2:Nat)^96 = 79228162514264337593543950336 from rfl] at h96; omega), hppv]
            exact ⟨_, rfl, by simp [resRel, decRel, decS, hlo]⟩

end OsuProofs
