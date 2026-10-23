/-
`net::decimal` (Rust) refines `OsuModel.Net.NetDecimal` (`System.Decimal` subset). The Rust
`NetDecimal { neg, mant : u128, scale : u32 }` ↦ the spec record with `Nat` fields (`decS`).
Part 1: powers, rounding/unscaling helpers, `SearchScale`, conversions to binary floats.
-/
import OsuProofs.Net.Parse2
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

def decS (d : net.decimal.NetDecimal) : NetDecimal := ⟨d.neg, d.mant.val, d.scale.val⟩

theorem uscalar_eq_val {ty} (a b : UScalar ty) : a = b ↔ a.val = b.val :=
  ⟨fun h => h ▸ rfl, fun h => UScalar.eq_of_val_eq h⟩

theorem u128_max : U128.max = 2^128 - 1 := by simp [U128.max_eq]

theorem u128_and_mask64 (x : U128) : (x &&& 18446744073709551615#u128).val = x.val % 2^64 := by
  simp only [UScalar.val, UScalar.bv_and]
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.bv.toNat 64

theorem u128_shr64 (x : U128) : ∃ z, x >>> 64#i32 = ok z ∧ z.val = x.val / 2^64 := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (UScalar.ShiftRight_IScalar_spec x (y := 64#i32) (by simp) (by simp))
  exact ⟨z, hz, by simpa [Nat.shiftRight_eq_div_pow] using hv.1⟩

/-- Helper (no spec def): `10^k` for `k ≤ 38`. -/
theorem net.decimal.pow10_refines (k : U32) (hk : k.val ≤ 38) :
    ∃ y, net.decimal.pow10 k = ok y ∧ y.val = 10 ^ k.val := by
  unfold net.decimal.pow10 net.decimal.pow10_loop
  apply loop_ok _ (fun x => k.val - x.2.val) (fun x => x.2.val ≤ k.val ∧ x.1.val = 10 ^ x.2.val)
  · rintro ⟨r, i⟩ ⟨hi, hr⟩
    dsimp only at hi hr ⊢
    by_cases hlt : i < k
    · right
      have hlt' : i.val < k.val := hlt
      have hpow : 10 ^ i.val * 10 ≤ 10 ^ 38 := by
        rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega)
      obtain ⟨r1, hr1, hv⟩ := eq_ok_of_spec (U128.mul_spec (x := r) (y := 10#u128)
        (by simp [hr, U128.max_eq]; omega))
      obtain ⟨i1, hi1, hiv⟩ := eq_ok_of_spec (U32.add_spec (x := i) (y := 1#u32)
        (by simp [U32.max_eq]; omega))
      refine ⟨(r1, i1), by simp [net.decimal.pow10_loop.body, hlt, hr1, hi1], ?_, ?_⟩
      · simp at hv hiv; simp [hv, hiv, hr, Nat.pow_succ]; omega
      · simp at hiv; simp [hiv]; omega
    · left
      have : i.val = k.val := by have : ¬ i.val < k.val := hlt; omega
      exact ⟨r, by simp [net.decimal.pow10_loop.body, hlt], by rw [hr, this]⟩
  · simp

theorem net.decimal.is_positive_refines (d : net.decimal.NetDecimal) :
    net.decimal.is_positive d = ok (NetDecimal.isPositive (decS d)) := by
  have : (d.mant != 0#u128) = (d.mant.val != 0) := by
    rw [Bool.eq_iff_iff]; simp [uscalar_eq_val]
  cases h : d.neg <;> simp [net.decimal.is_positive, NetDecimal.isPositive, decS, h, this]

theorem u128_bounds (x : U128) : x.val < 2^128 := by have := x.hBounds; simpa using this

/-- Guarded: `scale ≤ 38` (decimals have `scale ≤ 28`). -/
theorem net.decimal.round_refines (d : net.decimal.NetDecimal) (hs : d.scale.val ≤ 38) :
    ∃ r, net.decimal.round d = ok r ∧ decS r = NetDecimal.round (decS d) := by
  unfold net.decimal.round NetDecimal.round
  by_cases h0 : d.scale.val = 0
  · have : d.scale = 0#u32 := UScalar.eq_of_val_eq (by simp [h0])
    exact ⟨d, by simp [this], by simp [decS, h0]⟩
  · have h0' : ¬ d.scale = 0#u32 := fun e => h0 (by rw [e]; simp)
    obtain ⟨pw, hpw, hpwv⟩ := net.decimal.pow10_refines d.scale hs
    have hpos : 0 < pw.val := by rw [hpwv]; exact Nat.pow_pos (by decide)
    have hpw38 : pw.val ≤ 10^38 := by rw [hpwv]; exact Nat.pow_le_pow_right (by decide) hs
    have hpw10 : 10 ≤ pw.val := by rw [hpwv]; calc 10 = 10^1 := rfl
                                                 _ ≤ 10 ^ d.scale.val := Nat.pow_le_pow_right (by decide) (by omega)
    have hm := u128_bounds d.mant
    obtain ⟨q, hq, hqv⟩ := eq_ok_of_spec (U128.div_spec d.mant (y := pw) (by omega))
    obtain ⟨r, hr, hrv⟩ := eq_ok_of_spec (U128.rem_spec d.mant (y := pw) (by omega))
    have hrl : r.val < pw.val := by rw [hrv]; exact Nat.mod_lt _ hpos
    obtain ⟨r2, hr2, hr2v⟩ := eq_ok_of_spec (U128.mul_spec (x := 2#u128) (y := r) (by simp [U128.max_eq]; omega))
    simp at hr2v
    have hql : q.val < 2^128 - 1 := by
      rw [hqv]; have : d.mant.val / pw.val ≤ d.mant.val / 10 := Nat.div_le_div_left hpw10 (by decide)
      omega
    obtain ⟨q1, hq1, hq1v⟩ := eq_ok_of_spec (U128.add_spec (x := q) (y := 1#u128) (by simp [U128.max_eq]; omega))
    simp at hq1v
    have e1 : (r2 > pw) ↔ 2 * (d.mant.val % 10 ^ d.scale.val) > 10 ^ d.scale.val := by
      show pw.val < r2.val ↔ _; rw [hr2v, hrv, hpwv]
    have e2 : (r2 = pw) ↔ 2 * (d.mant.val % 10 ^ d.scale.val) = 10 ^ d.scale.val := by
      rw [uscalar_eq_val, hr2v, hrv, hpwv]
    have hdv : decS d = ⟨d.neg, d.mant.val, d.scale.val⟩ := rfl
    have e1' : (pw.val < r2.val) ↔ 2 * (d.mant.val % 10 ^ d.scale.val) > 10 ^ d.scale.val := e1
    by_cases c1 : 2 * (d.mant.val % 10 ^ d.scale.val) > 10 ^ d.scale.val
    · refine ⟨{ d with mant := q1, scale := 0#u32 }, by simp [h0', hpw, hq, hr, hr2, e1.mpr c1, e1'.mpr c1, hq1], ?_⟩
      simp [decS, h0, c1, hq1v, hqv, hpwv]
    · have hc1 : ¬ r2 > pw := fun h => c1 (e1.mp h)
      by_cases c2 : 2 * (d.mant.val % 10 ^ d.scale.val) = 10 ^ d.scale.val
      · obtain ⟨t, ht, htv⟩ := eq_ok_of_spec (U128.rem_spec q (y := 2#u128) (by simp))
        by_cases c3 : q.val % 2 = 1
        · have hc3 : t = 1#u128 := by rw [uscalar_eq_val]; simpa [c3] using htv
          refine ⟨{ d with mant := q1, scale := 0#u32 }, by simp [h0', hpw, hq, hr, hr2, hc1, (not_congr e1').mpr c1, e2.mpr c2, ht, hc3, hq1], ?_⟩
          rw [hqv, hpwv] at c3
          simp [decS, h0, c1, c2, c3, hq1v, hqv, hpwv]
        · have hc3 : ¬ t = 1#u128 := by rw [uscalar_eq_val]; simp at htv; simp [htv]; omega
          refine ⟨{ d with mant := q, scale := 0#u32 }, by simp [h0', hpw, hq, hr, hr2, hc1, (not_congr e1').mpr c1, e2.mpr c2, ht, hc3], ?_⟩
          rw [hqv, hpwv] at c3
          simp [decS, h0, c1, c2, c3, hqv, hpwv]
      · have hc2 : ¬ r2 = pw := fun h => c2 (e2.mp h)
        refine ⟨{ d with mant := q, scale := 0#u32 }, by simp [h0', hpw, hq, hr, hr2, hc1, (not_congr e1').mpr c1, hc2], ?_⟩
        simp [decS, h0, c1, c2, hqv, hpwv]

def qsRel (x : U128 × I64) (y : Nat × Int) : Prop := x.1.val = y.1 ∧ x.2.val = y.2

theorem net.decimal.overflow_unscale_refines (q : U128) (sc : I64) (sticky : Bool) (hsc : -2^62 ≤ sc.val) :
    ∃ r, net.decimal.overflow_unscale q sc sticky = ok r ∧
      resRel qsRel r (NetDecimal.overflowUnscale q.val sc.val sticky) := by
  unfold net.decimal.overflow_unscale NetDecimal.overflowUnscale
  obtain ⟨s1, hs1, hs1v⟩ := eq_ok_of_spec (I64.sub_spec (x := sc) (y := 1#i64)
    (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; have := sc.hmax; simp [IScalar.max] at this; omega))
  simp at hs1v
  by_cases hneg : sc.val - 1 < 0
  · have : s1 < 0#i64 := by show s1.val < 0; simp [hs1v]; omega
    have hv2 : ¬ 0 ≤ s1.val := by omega
    exact ⟨.Err .Overflow, by simp [hs1, this, hv2], by simp [resRel, exnS, hneg]⟩
  · have hn' : ¬ s1 < 0#i64 := by show ¬ s1.val < 0; simp [hs1v]; omega
    have hv : 0 ≤ s1.val := by omega
    have hq := u128_bounds q
    obtain ⟨r, hr, hrv⟩ := eq_ok_of_spec (U128.rem_spec q (y := 10#u128) (by simp))
    obtain ⟨q2, hq2, hq2v⟩ := eq_ok_of_spec (U128.div_spec q (y := 10#u128) (by simp))
    simp at hrv hq2v
    obtain ⟨q21, hq21, hq21v⟩ := eq_ok_of_spec (U128.add_spec (x := q2) (y := 1#u128) (by simp [U128.max_eq]; omega))
    simp at hq21v
    obtain ⟨t, ht, htv⟩ := eq_ok_of_spec (U128.rem_spec q2 (y := 2#u128) (by simp))
    simp at htv
    have b5 : (r > 5#u128) ↔ q.val % 10 > 5 := by show 5 < r.val ↔ _; rw [hrv]
    have e5 : (r = 5#u128) ↔ q.val % 10 = 5 := by rw [uscalar_eq_val, hrv]; simp
    have e1 : (t = 1#u128) ↔ q.val / 10 % 2 = 1 := by rw [uscalar_eq_val, htv, hq2v]; simp
    have b5' : (5 < r.val) ↔ q.val % 10 > 5 := b5
    by_cases c1 : q.val % 10 > 5
    · exact ⟨.Ok (q21, s1), by simp [hs1, hn', hv, hr, hq2, b5.mpr c1, b5'.mpr c1, hq21],
        by simp [resRel, qsRel, hneg, c1, hq21v, hq2v, hs1v]⟩
    · by_cases c2 : q.val % 10 = 5
      · cases sticky
        · by_cases c3 : q.val / 10 % 2 = 1
          · exact ⟨.Ok (q21, s1), by simp [hs1, hn', hv, hr, hq2, (not_congr b5).mpr c1, (not_congr b5').mpr c1,
              e5.mpr c2, ht, e1.mpr c3, hq21], by simp [resRel, qsRel, hneg, c1, c2, c3, hq21v, hq2v, hs1v]⟩
          · exact ⟨.Ok (q2, s1), by simp [hs1, hn', hv, hr, hq2, (not_congr b5).mpr c1, (not_congr b5').mpr c1,
              e5.mpr c2, ht, (not_congr e1).mpr c3], by simp [resRel, qsRel, hneg, c1, c2, c3, hq2v, hs1v]⟩
        · exact ⟨.Ok (q21, s1), by simp [hs1, hn', hv, hr, hq2, (not_congr b5).mpr c1, (not_congr b5').mpr c1,
            e5.mpr c2, hq21], by simp [resRel, qsRel, hneg, c1, c2, hq21v, hq2v, hs1v]⟩
      · exact ⟨.Ok (q2, s1), by simp [hs1, hn', hv, hr, hq2, (not_congr b5).mpr c1, (not_congr b5').mpr c1,
          (not_congr e5).mpr c2], by simp [resRel, qsRel, hneg, c1, c2, hq2v, hs1v]⟩

def ustep (K : Nat) (c : Int) (x : Nat × Int) : Nat × Int :=
  if x.1 % K == 0 && decide (x.2 ≥ c) then (x.1 / K, x.2 - c) else x

theorem id_bind_eq {α β : Type} (x : α) (f : α → Id β) : (x >>= f : Id β) = f x := rfl
theorem id_pure_eq {α : Type} (x : α) : (pure x : Id α) = x := rfl

theorem ite_pure_yield {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep α)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

theorem unscale_eq (q : Nat) (s : Int) : NetDecimal.unscale q s =
    ustep 10 1 (ustep 100 2 (ustep 10000 4 (ustep 100000000 8 (ustep 100000000 8 (ustep 100000000 8
      (ustep 100000000 8 (q, s))))))) := by
  simp only [NetDecimal.unscale, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', ite_pure_yield,
    List.forIn_pure_yield_eq_foldl]
  generalize hF : List.foldl _ (q, s) _ = X
  have hX : X = ustep 100000000 8 (ustep 100000000 8 (ustep 100000000 8 (ustep 100000000 8 (q, s)))) := by
    rw [← hF]; simp only [Std.Legacy.Range.size, List.range', List.foldl, ustep]
  rw [← hX]
  obtain ⟨a, b⟩ := X
  rw [id_bind_eq]
  simp only [ustep, id_pure_eq]
  by_cases h1 : a % 10000 = 0 ∧ 4 ≤ b <;> by_cases h2 : a / 10000 % 100 = 0 ∧ 2 ≤ b - 4 <;>
    by_cases h3 : a % 100 = 0 ∧ 2 ≤ b <;> by_cases h4 : a / 10000 / 100 % 10 = 0 ∧ 1 ≤ b - 4 - 2 <;>
    by_cases h5 : a / 10000 % 10 = 0 ∧ 1 ≤ b - 4 <;> by_cases h6 : a / 100 % 10 = 0 ∧ 1 ≤ b - 2 <;>
    by_cases h7 : a % 10 = 0 ∧ 1 ≤ b <;> simp [h1, h2, h3, h4, h5, h6, h7]

theorem ustep_impl (q : U128) (s : I64) (K : U128) (c : I64) (hK : 0 < K.val) (hc0 : 0 ≤ c.val) (hc : c.val ≤ 8)
    (hs : -2^62 ≤ s.val) :
    ∃ q' s', (∀ {β : Type} (f : U128 → I64 → Result β),
      (do let i1 ← q % K
          let (q1, s1) ← (if i1 = 0#u128 then (if s >= c then (do let q2 ← q / K; let s2 ← s - c; ok (q2, s2))
                          else ok (q, s)) else ok (q, s))
          f q1 s1) = f q' s') ∧
      (q'.val, s'.val) = ustep K.val c.val (q.val, s.val) ∧ -2^62 ≤ s'.val ∧ s.val - c.val ≤ s'.val := by
  obtain ⟨r, hr, hrv⟩ := eq_ok_of_spec (U128.rem_spec q (y := K) (by omega))
  try simp at hrv
  by_cases h1 : q.val % K.val = 0 ∧ c.val ≤ s.val
  · have hr0 : r = 0#u128 := by rw [uscalar_eq_val]; simp [hrv, h1.1]
    have hsc : s >= c := h1.2
    obtain ⟨q2, hq2, hq2v⟩ := eq_ok_of_spec (U128.div_spec q (y := K) (by omega))
    obtain ⟨s2, hs2, hs2v⟩ := eq_ok_of_spec (I64.sub_spec (x := s) (y := c)
      (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; have := s.hmax; simp [IScalar.max] at this; omega))
    refine ⟨q2, s2, by intro β f; simp [hr, hr0, hsc, hq2, hs2], ?_, by omega, by omega⟩
    try simp at hq2v hs2v
    simp [ustep, hq2v, hs2v, h1.1, h1.2]
  · refine ⟨q, s, ?_, ?_, hs, by omega⟩
    · intro β f
      by_cases hz : q.val % K.val = 0
      · have hr0 : r = 0#u128 := by rw [uscalar_eq_val]; simp [hrv, hz]
        have hsc : ¬ s >= c := fun h => h1 ⟨hz, h⟩
        simp [hr, hr0, hsc]
      · have hr0 : ¬ r = 0#u128 := by rw [uscalar_eq_val]; simp [hrv, hz]
        simp [hr, hr0]
    · simp only [ustep]
      have : ¬ ((q.val % K.val == 0 && decide (s.val ≥ c.val)) = true) := by simpa using h1
      simp only [this, ite_false, Bool.false_eq_true]

theorem ustep_impl_tail (q : U128) (s : I64) (K : U128) (c : I64) (hK : 0 < K.val) (hc0 : 0 ≤ c.val) (hc : c.val ≤ 8)
    (hs : -2^62 ≤ s.val) :
    ∃ q' s', (do let i1 ← q % K; if i1 = 0#u128 then (if s >= c then (do let q2 ← q / K; let s2 ← s - c; ok (q2, s2)) else ok (q, s)) else ok (q, s)) = ok (q', s') ∧
      (q'.val, s'.val) = ustep K.val c.val (q.val, s.val) ∧ -2^62 ≤ s'.val ∧ s.val - c.val ≤ s'.val := by
  obtain ⟨r, hr, hrv⟩ := eq_ok_of_spec (U128.rem_spec q (y := K) (by omega))
  try simp at hrv
  by_cases h1 : q.val % K.val = 0 ∧ c.val ≤ s.val
  · have hr0 : r = 0#u128 := by rw [uscalar_eq_val]; simp [hrv, h1.1]
    have hsc : s >= c := h1.2
    obtain ⟨q2, hq2, hq2v⟩ := eq_ok_of_spec (U128.div_spec q (y := K) (by omega))
    obtain ⟨s2, hs2, hs2v⟩ := eq_ok_of_spec (I64.sub_spec (x := s) (y := c)
      (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; have := s.hmax; simp [IScalar.max] at this; omega))
    refine ⟨q2, s2, by simp [hr, hr0, hsc, hq2, hs2], ?_, by omega, by omega⟩
    try simp at hq2v hs2v
    simp [ustep, hq2v, hs2v, h1.1, h1.2]
  · refine ⟨q, s, ?_, ?_, hs, by omega⟩
    · by_cases hz : q.val % K.val = 0
      · have hr0 : r = 0#u128 := by rw [uscalar_eq_val]; simp [hrv, hz]
        have hsc : ¬ s >= c := fun h => h1 ⟨hz, h⟩
        simp [hr, hr0, hsc]
      · have hr0 : ¬ r = 0#u128 := by rw [uscalar_eq_val]; simp [hrv, hz]
        simp [hr, hr0]
    · simp only [ustep]
      have : ¬ ((q.val % K.val == 0 && decide (s.val ≥ c.val)) = true) := by simpa using h1
      simp only [this, ite_false, Bool.false_eq_true]

def u8iter : Nat → Nat × Int → Nat × Int
  | 0, x => x
  | n+1, x => u8iter n (ustep 100000000 8 x)

theorem net.decimal.unscale_refines (q0 : U128) (s0 : I64) (hs : -2^61 ≤ s0.val) :
    ∃ q s, net.decimal.unscale q0 s0 = ok (q, s) ∧ (q.val, s.val) = NetDecimal.unscale q0.val s0.val := by
  rw [unscale_eq]
  have hl : ∃ q s, net.decimal.unscale_loop q0 s0 0#i32 = ok (q, s) ∧ (q.val, s.val) = u8iter 4 (q0.val, s0.val) ∧
      -2^61 - 32 ≤ s.val := by
    unfold net.decimal.unscale_loop
    obtain ⟨y, hy, hq⟩ := loop_ok (fun (x : U128 × I64 × I32) => net.decimal.unscale_loop.body x.1 x.2.1 x.2.2)
      (fun x => (4 - x.2.2.val).toNat)
      (fun x => 0 ≤ x.2.2.val ∧ x.2.2.val ≤ 4 ∧ -2^61 - 8 * x.2.2.val ≤ x.2.1.val ∧
        u8iter (4 - x.2.2.val).toNat (x.1.val, x.2.1.val) = u8iter 4 (q0.val, s0.val))
      (fun y => (y.1.val, y.2.val) = u8iter 4 (q0.val, s0.val) ∧ -2^61 - 32 ≤ y.2.val)
      (by
        rintro ⟨q, s, i⟩ ⟨hi0, hi4, hsb, hT⟩
        dsimp only at hi0 hi4 hsb hT ⊢
        by_cases hlt : i < 4#i32
        · right
          have hlt' : i.val < 4 := hlt
          obtain ⟨q', s', hst, hsv, hsb', hsb''⟩ := ustep_impl q s 100000000#u128 8#i64 (by simp) (by simp) (by simp) (by omega)
          simp only [show (8#i64 : I64).val = 8 from rfl] at hsb''
          obtain ⟨i1, hi1, hi1v⟩ := eq_ok_of_spec (I32.add_spec (x := i) (y := 1#i32)
            (by simp [I32.min_eq]; omega) (by simp [I32.max_eq]; omega))
          simp at hi1v
          refine ⟨(q', s', i1), ?_, ⟨by dsimp only; omega, by dsimp only; omega, ?_, ?_⟩, by dsimp only; omega⟩
          · simp only [net.decimal.unscale_loop.body, hlt, ite_true]
            rw [hst]; simp [hi1]
          · dsimp only; omega
          · dsimp only
            have e : (4 - i.val).toNat = (4 - i1.val).toNat + 1 := by omega
            have hsv' : ustep 100000000 8 (q.val, s.val) = (q'.val, s'.val) := hsv.symm
            rw [e, u8iter, hsv'] at hT; exact hT
        · left
          have : i.val = 4 := by have : ¬ i.val < 4 := hlt; omega
          refine ⟨(q, s), by simp [net.decimal.unscale_loop.body, hlt], ?_, by dsimp only; omega⟩
          rw [this] at hT; simpa [u8iter] using hT)
      (q0, s0, 0#i32) ⟨by simp, by simp, by simp; omega, by simp⟩
    obtain ⟨q, s⟩ := y
    exact ⟨q, s, hy, hq⟩
  obtain ⟨q4, s4, hlp, hlv, hsb⟩ := hl
  obtain ⟨qa, sa, hA, hAv, -, hAb⟩ := ustep_impl q4 s4 10000#u128 4#i64 (by simp) (by simp) (by simp) (by omega)
  simp only [show (4#i64 : I64).val = 4 from rfl] at hAb
  obtain ⟨qb, sb, hB, hBv, -, hBb⟩ := ustep_impl qa sa 100#u128 2#i64 (by simp) (by simp) (by simp) (by omega)
  simp only [show (2#i64 : I64).val = 2 from rfl] at hBb
  obtain ⟨qc, sc, hC, hCv, -, -⟩ := ustep_impl_tail qb sb 10#u128 1#i64 (by simp) (by simp) (by simp) (by omega)
  refine ⟨qc, sc, ?_, ?_⟩
  · unfold net.decimal.unscale
    simp at hA hB hC
    simp [hlp, hA, hB, hC]
  · rw [hCv, hBv, hAv, hlv]; rfl

theorem net.decimal.sar_refines (x : I64) (k : U32) (hk : k.val < 64) :
    ∃ r, net.decimal.sar x k = ok r ∧ r.val = NetDecimal.sar x.val k.val := by
  unfold net.decimal.sar NetDecimal.sar
  refine ⟨⟨x.bv.sshiftRight k.val⟩, ?_, ?_⟩
  · simp [HShiftRight.hShiftRight, IScalar.shiftRight_UScalar, IScalar.shiftRight, hk]
  · show (x.bv.sshiftRight k.val).toInt = _
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow, IScalar.bv_toInt_eq]
    rw [Int.fdiv_eq_ediv]; simp

theorem TWO96_eq : net.decimal.TWO96 = ok (⟨BitVec.ofNat 128 (2^96)⟩ : U128) := by
  unfold net.decimal.TWO96; rfl
theorem TWO96_val : (⟨BitVec.ofNat 128 (2^96)⟩ : U128).val = NetDecimal.two96 := by rfl

theorem net.decimal.power_ovfl_refines (i : U32) (hi : i.val ≤ 37) :
    ∃ a b, net.decimal.power_ovfl i = ok (a, b) ∧ (a.val, b.val) = NetDecimal.powerOvfl i.val := by
  unfold net.decimal.power_ovfl NetDecimal.powerOvfl
  have ht : NetDecimal.two96 = 2^96 := rfl
  obtain ⟨t1, ht1, ht1v, _⟩ := eq_ok_of_spec (U128.sub_spec (x := ⟨BitVec.ofNat 128 (2^96)⟩) (y := 1#u128)
    (by rw [TWO96_val, ht]; simp))
  obtain ⟨i1, hi1, hi1v⟩ := eq_ok_of_spec (U32.add_spec (x := i) (y := 1#u32) (by simp [U32.max_eq]; omega))
  simp at hi1v
  obtain ⟨p, hp, hpv⟩ := net.decimal.pow10_refines i1 (by omega)
  have hpos : 0 < p.val := by rw [hpv]; exact Nat.pow_pos (by decide)
  obtain ⟨v, hv, hvv⟩ := eq_ok_of_spec (U128.div_spec t1 (y := p) (by omega))
  obtain ⟨a, ha, hav⟩ := u128_shr64 v
  refine ⟨a, v &&& 18446744073709551615#u128, by simp only [TWO96_eq, ht1, hi1, hp, hv, ha, lift, bind_ok], ?_⟩
  rw [u128_and_mask64, hav, hvv, ht1v, TWO96_val, hpv, hi1v]
  simp [Nat.shiftRight_eq_div_pow]

/-- Helper (the spec's local `searchScale.check`). -/
theorem net.decimal.search_check_refines (num : U32) (sc : I64) (hs : -2^62 ≤ sc.val ∧ sc.val ≤ 2^62) :
    net.decimal.search_check num sc =
      ok (if (num.val : Int) + sc.val < 0 then .Err .Overflow else .Ok num) := by
  unfold net.decimal.search_check
  have hc : (UScalar.hcast .I64 num).val = (num.val : Int) := by
    rw [UScalar.hcast_val_eq]
    have hb : num.val < 2^32 := by have := num.hBounds; simpa using this
    exact Int.bmod_eq_of_le (by simp) (by simp; omega)
  have hb : num.val < 2^32 := by have := num.hBounds; simpa using this
  obtain ⟨t, ht, htv⟩ := eq_ok_of_spec (I64.add_spec (x := UScalar.hcast .I64 num) (y := sc)
    (by rw [hc]; simp [I64.min_eq]; omega) (by rw [hc]; simp [I64.max_eq]; omega))
  rw [hc] at htv
  by_cases h : (num.val : Int) + sc.val < 0
  · have : t < 0#i64 := by show t.val < 0; simp [htv]; omega
    have h' : t.val < 0 := by omega
    simp [lift, ht, this, h, h']
  · have : ¬ t < 0#i64 := by show ¬ t.val < 0; simp [htv]; omega
    have h' : 0 ≤ t.val := by omega
    simp [lift, ht, this, h, h']

theorem net.decimal.search_scale_refines (q : U128) (sc : I64) (hq : q.val < 2^96)
    (hs : -2^62 ≤ sc.val ∧ sc.val < 28) :
    ∃ r, net.decimal.search_scale q sc = ok r ∧
      resRel (fun (a : U32) (b : Nat) => a.val = b) r (NetDecimal.searchScale q.val sc.val) := by
  obtain ⟨u, hu, huv⟩ := u128_shr64 q
  have hlow := u128_and_mask64 q
  have hul : u.val < 2^32 := by rw [huv]; omega
  -- num0
  have hn0 : ∃ n0 : U32, (if u > 42949#u128 then (if u > 4294967#u128 then (if u > 42949672#u128 then ok 1#u32 else ok 2#u32)
        else if u > 429496#u128 then ok 3#u32 else ok 4#u32)
      else if u > 429#u128 then (if u > 4294#u128 then ok 5#u32 else ok 6#u32)
      else if u > 42#u128 then ok 7#u32 else ok 8#u32) = ok n0 ∧
      n0.val = (if u.val > 42949 then (if u.val > 4294967 then (if u.val > 42949672 then 1 else 2)
        else (if u.val > 429496 then 3 else 4)) else if u.val > 429 then (if u.val > 4294 then 5 else 6)
        else (if u.val > 42 then 7 else 8)) ∧ 1 ≤ n0.val ∧ n0.val ≤ 8 := by
    by_cases a1 : u.val > 42949
    · by_cases a2 : u.val > 4294967
      · by_cases a3 : u.val > 42949672
        · exact ⟨1#u32, by simp [a1, a2, a3], by simp [a1, a2, a3], by simp, by simp⟩
        · exact ⟨2#u32, by simp [a1, a2, a3], by simp [a1, a2, a3], by simp, by simp⟩
      · by_cases a3 : u.val > 429496
        · exact ⟨3#u32, by simp [a1, a2, a3], by simp [a1, a2, a3], by simp, by simp⟩
        · exact ⟨4#u32, by simp [a1, a2, a3], by simp [a1, a2, a3], by simp, by simp⟩
    · by_cases a2 : u.val > 429
      · by_cases a3 : u.val > 4294
        · exact ⟨5#u32, by simp [a1, a2, a3], by simp [a1, a2, a3], by simp, by simp⟩
        · exact ⟨6#u32, by simp [a1, a2, a3], by simp [a1, a2, a3], by simp, by simp⟩
      · by_cases a3 : u.val > 42
        · exact ⟨7#u32, by simp [a1, a2, a3], by simp [a1, a2, a3], by simp, by simp⟩
        · exact ⟨8#u32, by simp [a1, a2, a3], by simp [a1, a2, a3], by simp, by simp⟩
  obtain ⟨n0, hn0e, hn0v, hn01, hn08⟩ := hn0
  have hsc := fun (n : U32) => net.decimal.search_check_refines n sc ⟨hs.1, by omega⟩
  unfold net.decimal.search_scale NetDecimal.searchScale
  simp only [hu, bind_ok, lift]
  have huv' : q.val >>> 64 = u.val := by rw [huv, Nat.shiftRight_eq_div_pow]
  rw [huv', ← hlow]
  generalize hL : (q &&& 18446744073709551615#u128) = L at hlow ⊢
  by_cases c0 : u.val > 429496729
  · have c0' : u > 429496729#u128 := c0
    obtain h := hsc 0#u32
    refine ⟨if ((0#u32 : U32).val : Int) + sc.val < 0 then .Err .Overflow else .Ok 0#u32, by simp [c0', h], ?_⟩
    simp only [c0, ite_true]
    by_cases hh : sc.val < 0
    · simp [hh, resRel, exnS]
    · simp [hh, resRel]
  · have c0' : ¬ u > 429496729#u128 := c0
    simp only [c0', c0, ite_false, hn0e, bind_ok]
    rw [← hn0v]
    obtain ⟨i, hi, hiv, _⟩ := eq_ok_of_spec (U32.sub_spec (x := n0) (y := 1#u32) (by simp; omega))
    simp at hiv
    obtain ⟨hi', ml, hpo, hpov⟩ := net.decimal.power_ovfl_refines i (by omega)
    rw [hiv] at hpov
    simp only [hi, hpo, bind_ok]
    rw [← hpov]
    simp only
    -- band
    have hband : ∃ band : U32, (if u = hi' then (if L > ml then ok i else ok n0) else ok n0) = ok band ∧
        band.val = (if (u.val == hi'.val && decide (L.val > ml.val)) = true then n0.val - 1 else n0.val) := by
      by_cases b1 : u.val = hi'.val
      · have b1' : u = hi' := UScalar.eq_of_val_eq b1
        by_cases b2 : L.val > ml.val
        · exact ⟨i, by simp [b1', b2], by simp [b1, b2, hiv]⟩
        · exact ⟨n0, by simp [b1', show ¬ L > ml from b2], by simp [b1, b2]⟩
      · have b1' : ¬ u = hi' := fun e => b1 (by rw [e])
        exact ⟨n0, by simp [b1'], by simp [b1]⟩
    obtain ⟨band, hbe, hbv⟩ := hband
    have hbe' := hbe
    simp at hbe'
    have hbv' : (band.val : Int) = ((if (u.val == hi'.val && decide (L.val > ml.val)) = true then n0.val - 1 else n0.val : Nat) : Int) := by
      rw [hbv]
    by_cases c19 : sc.val > 19
    · obtain ⟨i1, hi1, hi1v⟩ := eq_ok_of_spec (I64.sub_spec (x := 28#i64) (y := sc)
        (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
      simp at hi1v
      have hc1 : (IScalar.hcast .U32 i1).val = (28 - sc.val).toNat := by
        rw [IScalar.hcast_val_eq, hi1v]; simp; omega
      obtain ⟨i2, hi2, hi2v, _⟩ := eq_ok_of_spec (U32.sub_spec (x := IScalar.hcast .U32 i1) (y := 1#u32)
        (by simp [hc1]; omega))
      have hi2v' : i2.val = (28 - sc.val).toNat - 1 := by rw [hi2v, hc1]; rfl
      obtain ⟨h2, m2, hpo2, hpo2v⟩ := net.decimal.power_ovfl_refines i2 (by omega)
      rw [hi2v'] at hpo2v
      have hpo2v' := congrArg Prod.fst hpo2v
      simp only at hpo2v'
      by_cases c2 : u.val < h2.val
      · refine ⟨if (((IScalar.hcast .U32 i1).val : Nat) : Int) + sc.val < 0 then .Err .Overflow else .Ok (IScalar.hcast .U32 i1),
          by simp [hbe', c19, hi1, hi2, hpo2, c2, hsc], ?_⟩
        have c2' : u.val < (NetDecimal.powerOvfl ((28 - sc.val).toNat - 1)).1 := by rw [← hpo2v']; exact c2
        have hnn : ¬ (((28 - sc.val).toNat : Nat) : Int) + sc.val < 0 := by omega
        simp only [c19, ite_true, c2', hc1, hnn, ite_false, resRel]
      · refine ⟨if (band.val : Int) + sc.val < 0 then .Err .Overflow else .Ok band,
          by simp [hbe', c19, hi1, hi2, hpo2, c2, hsc], ?_⟩
        have c2' : ¬ u.val < (NetDecimal.powerOvfl ((28 - sc.val).toNat - 1)).1 := by rw [← hpo2v']; exact c2
        simp only [c19, ite_true, c2', ite_false, ← hbv]
        by_cases hneg : (band.val : Int) + sc.val < 0
        · simp [hneg, resRel, exnS]
        · simp [hneg, resRel]
    · have c19' : ¬ sc > 19#i64 := c19
      by_cases d1 : u.val < 4
      · refine ⟨.Ok 9#u32, by simp [hbe', c19, c19', d1], ?_⟩
        simp [c19, d1, resRel]
      · by_cases d2 : u.val = 4 ∧ L.val ≤ 5441186219426131129
        · refine ⟨.Ok 9#u32, by simp [hbe', c19, c19', d1, d2.1, d2.2], ?_⟩
          simp [c19, d1, d2.1, d2.2, resRel]
        · refine ⟨if (band.val : Int) + sc.val < 0 then .Err .Overflow else .Ok band, ?_, ?_⟩
          · by_cases d3 : u.val = 4
            · have d4 : ¬ L.val ≤ 5441186219426131129 := fun h => d2 ⟨d3, h⟩
              simp [hbe', c19, c19', d1, d3, d4, hsc]
            · simp [hbe', c19, c19', d1, d3, hsc]
          · have hd : ¬ ((decide (u.val < 4) || u.val == 4 && decide (L.val ≤ 5441186219426131129)) = true) := by
              simp; omega
            simp only [c19, ite_false, hd, ← hbv]
            by_cases hneg : (band.val : Int) + sc.val < 0
            · simp [hneg, resRel, exnS]
            · simp [hneg, resRel]

end OsuProofs
