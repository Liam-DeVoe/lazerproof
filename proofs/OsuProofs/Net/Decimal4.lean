/-
`net::decimal` part 4: `ScaleResult`, `decimal * decimal` (`VarDecMul`) and its 192-bit helpers.
-/
import OsuProofs.Net.Decimal3
import OsuProofs.SpecLoops
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

theorem u128_or_val (a b : U128) : (a ||| b).val = a.val ||| b.val := by
  simp only [UScalar.val, UScalar.bv_or, BitVec.toNat_or]

theorem or_mul64 (k b : Nat) (hb : b < 2^64) : (k * 2^64) ||| b = k * 2^64 + b := by
  rw [← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt hb]

theorem u128_cast_u64 (x : U64) : (UScalar.cast .U128 x).val = x.val := by
  rw [UScalar.cast_val_eq]; simp; have := u64_bounds x; omega

theorem ld3 (B d xhi l1 lm qh r1 qm r2 ql r3 : Nat) (e1 : xhi = qh * d + r1) (e2 : r1 * B + l1 = qm * d + r2)
    (e3 : r2 * B + lm = ql * d + r3) :
    xhi * (B * B) + (l1 * B + lm) = (qh * (B * B) + qm * B + ql) * d + r3 := by
  subst e1
  calc (qh * d + r1) * (B * B) + (l1 * B + lm) = qh * d * (B * B) + (r1 * B + l1) * B + lm := by ring
    _ = qh * d * (B * B) + (qm * d + r2) * B + lm := by rw [e2]
    _ = qh * d * (B * B) + qm * d * B + (r2 * B + lm) := by ring
    _ = qh * d * (B * B) + qm * d * B + (ql * d + r3) := by rw [e3]
    _ = (qh * (B * B) + qm * B + ql) * d + r3 := by ring

theorem p128_mul : (2:Nat)^128 = 2^64 * 2^64 := by rfl

/-- Helper: 192-by-64-bit division with remainder (long division in three 64-bit digits). -/
theorem net.decimal.u192_divmod_small_refines (x : net.decimal.U192) (d : U64) (hd : 0 < d.val) :
    ∃ q r, net.decimal.u192_divmod_small x d = ok (q, r) ∧
      u192S q = u192S x / d.val ∧ r.val = u192S x % d.val := by
  have hdb := u64_bounds d
  have hhb := u64_bounds x.hi
  have hlb := u128_bounds x.lo
  have cd := u128_cast_u64 d
  have ch := u128_cast_u64 x.hi
  generalize hD : UScalar.cast .U128 d = dd at cd
  generalize hH : UScalar.cast .U128 x.hi = hh at ch
  have hdd0 : dd.val ≠ 0 := by omega
  obtain ⟨qh, hqh, hqhv⟩ := UScalar.div_spec hh hdd0
  obtain ⟨r1, hr1, hr1v⟩ := eq_ok_of_spec (UScalar.rem_spec hh hdd0)
  obtain ⟨s1, hs1, hs1v⟩ := u128_shl64 r1
  obtain ⟨l1, hl1, hl1v⟩ := u128_shr64 x.lo
  have hr1l : r1.val < d.val := by rw [hr1v, ← cd]; exact Nat.mod_lt _ (by omega)
  have hs1v' : s1.val = r1.val * 2^64 := by
    rw [hs1v]; apply Nat.mod_eq_of_lt; rw [p128_eq]; rw [p64_eq] at hdb ⊢; nlinarith
  have hl1l : l1.val < 2^64 := by rw [hl1v]; rw [p128_eq] at hlb; rw [p64_eq]; omega
  generalize hT : s1 ||| l1 = top
  have htop : top.val = r1.val * 2^64 + l1.val := by rw [← hT, u128_or_val, hs1v', or_mul64 _ _ hl1l]
  obtain ⟨qm, hqm, hqmv⟩ := UScalar.div_spec top hdd0
  obtain ⟨r2, hr2, hr2v⟩ := eq_ok_of_spec (UScalar.rem_spec top hdd0)
  obtain ⟨s2, hs2, hs2v⟩ := u128_shl64 r2
  have hr2l : r2.val < d.val := by rw [hr2v, ← cd]; exact Nat.mod_lt _ (by omega)
  have hs2v' : s2.val = r2.val * 2^64 := by
    rw [hs2v]; apply Nat.mod_eq_of_lt; rw [p128_eq]; rw [p64_eq] at hdb ⊢; nlinarith
  have hml := u128_and_mask64 x.lo
  generalize hM : (x.lo &&& 18446744073709551615#u128) = lm at hml
  have hlml : lm.val < 2^64 := by rw [hml]; exact Nat.mod_lt _ (by decide)
  generalize hB : s2 ||| lm = bot
  have hbot : bot.val = r2.val * 2^64 + lm.val := by rw [← hB, u128_or_val, hs2v', or_mul64 _ _ hlml]
  obtain ⟨ql, hql, hqlv⟩ := UScalar.div_spec bot hdd0
  obtain ⟨r3, hr3, hr3v⟩ := eq_ok_of_spec (UScalar.rem_spec bot hdd0)
  obtain ⟨s3, hs3, hs3v⟩ := u128_shl64 qm
  -- digit bounds
  have hqml : qm.val < 2^64 := by
    rw [hqmv, htop, cd]; apply Nat.div_lt_of_lt_mul; rw [p64_eq] at *; nlinarith
  have hqll : ql.val < 2^64 := by
    rw [hqlv, hbot, cd]; apply Nat.div_lt_of_lt_mul; rw [p64_eq] at *; nlinarith
  have hs3v' : s3.val = qm.val * 2^64 := by
    rw [hs3v]; apply Nat.mod_eq_of_lt; rw [p128_eq]; rw [p64_eq] at hqml ⊢; omega
  have hov := core.num.U128.overflowing_add_eq s3 ql
  generalize hz : core.num.U128.overflowing_add s3 ql = z at hov
  obtain ⟨lo, c⟩ := z
  have hmx : UScalar.max .U128 = 340282366920938463463374607431768211455 := by simp [U128.max_eq]
  have hnc : ¬ (s3.val + ql.val > UScalar.max .U128) := by
    rw [hmx, hs3v']; rw [p64_eq] at hqml hqll; omega
  rw [if_neg hnc] at hov
  obtain ⟨hlo, hcv⟩ := hov
  subst hcv
  dsimp only at hlo
  have hqhl : qh.val < 2^64 := by rw [hqhv, ch]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hhb
  have cq : (UScalar.cast .U64 qh).val = qh.val := by
    rw [UScalar.cast_val_eq]; simp; rw [p64_eq] at hqhl; omega
  obtain ⟨h9, hh9, hh9v⟩ := eq_ok_of_spec (U64.add_spec (x := UScalar.cast .U64 qh) (y := 0#u64)
    (by simp [U64.max_eq]; omega))
  have hr3l : r3.val < d.val := by rw [hr3v, ← cd]; exact Nat.mod_lt _ (by omega)
  have cr : (UScalar.cast .U64 r3).val = r3.val := by
    rw [UScalar.cast_val_eq]; simp; omega
  refine ⟨⟨h9, lo⟩, UScalar.cast .U64 r3, ?_, ?_, ?_⟩
  · unfold net.decimal.u192_divmod_small
    simp only [lift, bind_ok, hD, hH, hqh, hr1, hs1, hl1, hT, hqm, hr2, hs2, hM, hB, hql, hr3, hs3, hz]
    simp [hh9]
  · -- value: long division identities
    have e1 : hh.val = qh.val * d.val + r1.val := by rw [hqhv, hr1v, cd]; exact (Nat.div_add_mod' _ _).symm
    have e2 : top.val = qm.val * d.val + r2.val := by rw [hqmv, hr2v, cd]; exact (Nat.div_add_mod' _ _).symm
    have e3 : bot.val = ql.val * d.val + r3.val := by rw [hqlv, hr3v, cd]; exact (Nat.div_add_mod' _ _).symm
    have el : x.lo.val = l1.val * 2^64 + lm.val := by rw [hl1v, hml]; exact (Nat.div_add_mod' _ _).symm
    have ex : u192S x = (qh.val * 2^128 + qm.val * 2^64 + ql.val) * d.val + r3.val := by
      unfold u192S; rw [p128_mul, el]
      exact ld3 (2^64) d.val x.hi.val l1.val lm.val qh.val r1.val qm.val r2.val ql.val r3.val
        (by rw [← ch, e1]) (by rw [← htop, e2]) (by rw [← hbot, e3])
    rw [ex, Nat.add_comm _ r3.val, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hr3l, Nat.zero_add]
    simp only [u192S, hh9v, cq, hlo, hs3v']
    simp; omega
  · rw [cr]
    have e3 : bot.val = ql.val * d.val + r3.val := by rw [hqlv, hr3v, cd]; exact (Nat.div_add_mod' _ _).symm
    have e1 : hh.val = qh.val * d.val + r1.val := by rw [hqhv, hr1v, cd]; exact (Nat.div_add_mod' _ _).symm
    have e2 : top.val = qm.val * d.val + r2.val := by rw [hqmv, hr2v, cd]; exact (Nat.div_add_mod' _ _).symm
    have el : x.lo.val = l1.val * 2^64 + lm.val := by rw [hl1v, hml]; exact (Nat.div_add_mod' _ _).symm
    have ex : u192S x = (qh.val * 2^128 + qm.val * 2^64 + ql.val) * d.val + r3.val := by
      unfold u192S; rw [p128_mul, el]
      exact ld3 (2^64) d.val x.hi.val l1.val lm.val qh.val r1.val qm.val r2.val ql.val r3.val
        (by rw [← ch, e1]) (by rw [← htop, e2]) (by rw [← hbot, e3])
    rw [ex, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr3l]

/-! ## `ScaleResult` -/

abbrev SRS := Option (Nat × Nat) × Int × Int × Nat × Bool × Nat × Nat

/-- The spec `ScaleResult` loop body (as elaborated; the loop index is unused). -/
def srStep (s : SRS) : Except NetExn (ForInStep SRS) :=
  let num := s.2.1; let sc := s.2.2.1; let q := s.2.2.2.1; let sticky := s.2.2.2.2.1; let rem := s.2.2.2.2.2.1
  let sticky := sticky || rem != 0
  let chunk := if num ≥ 9 then 9 else num.toNat
  let pow := 10 ^ chunk
  let rem := q % pow
  let q := q / pow
  let num := num - 9
  if num > 0 then pure (.yield (none, num, sc, q, sticky, rem, pow))
  else if q ≥ NetDecimal.two96 then
    if (sc == 0) = true then throw .overflow else pure (.yield (none, 1, sc - 1, q, sticky, rem, pow))
  else
    let half := pow / 2
    if (decide (half ≤ rem) && (decide (half < rem) || q % 2 == 1 || sticky)) = true then
      if q + 1 ≥ NetDecimal.two96 then
        if (sc == 0) = true then throw .overflow else pure (.yield (none, 1, sc - 1, q + 1, false, 0, pow))
      else pure (.done (some (q + 1, sc.toNat), num, sc, q + 1, sticky, rem, pow))
    else pure (.done (some (q, sc.toNat), num, sc, q, sticky, rem, pow))

def srPost (s : SRS) : Except NetExn (Nat × Nat) :=
  match s.1 with | some r => .ok r | none => .ok (s.2.2.2.1, s.2.2.1.toNat)

def qsR (x : U128 × U32) (y : Nat × Nat) : Prop := x.1.val = y.1 ∧ x.2.val = y.2

abbrev SRR := net.decimal.U192 × I64 × I64 × Bool × U64 ×
  Option (core.result.Result (U128 × U32) net.basic.NetExn) × I32

/-- Rust/spec state correspondence while the loop runs (`res = none`), with the bounds that keep
all arithmetic exact and the potential `it + ⌈num/9⌉ + 2 sc ≤ 119` that rules out exhausting the
120-iteration budget. -/
def srRel (x : SRR) (s : SRS) : Prop :=
  x.2.2.2.2.2.1 = none ∧ s.1 = none ∧ u192S x.1 = s.2.2.2.1 ∧ x.2.1.val = s.2.2.1 ∧ x.2.2.1.val = s.2.1 ∧
  x.2.2.2.1 = s.2.2.2.2.1 ∧ x.2.2.2.2.1.val = s.2.2.2.2.2.1 ∧
  1 ≤ x.2.2.1.val ∧ x.2.2.1.val ≤ 29 ∧ 0 ≤ x.2.1.val ∧ x.2.1.val ≤ 56 ∧ 0 ≤ x.2.2.2.2.2.2.val ∧
  x.2.2.2.2.2.2.val + (x.2.2.1.val + 8) / 9 + 2 * x.2.1.val ≤ 119

theorem hcast_u32_val (x : I64) (h0 : 0 ≤ x.val) (h1 : x.val < 2^32) : (IScalar.hcast .U32 x).val = x.val.toNat := by
  rw [IScalar.hcast_val_eq]
  rw [Int.emod_eq_of_lt h0 (by simpa using h1)]

theorem u192_lo_of_lt (x : net.decimal.U192) (h : u192S x < 2^128) : x.lo.val = u192S x := by
  unfold u192S at *
  have : x.hi.val = 0 := by
    by_contra hne
    have : x.hi.val * 2^128 ≥ 2^128 := Nat.le_mul_of_pos_left _ (by omega)
    omega
  rw [this]; simp

theorem i64_val_eq_zero (x : I64) : x = 0#i64 ↔ x.val = 0 := by
  constructor
  · intro h; rw [h]; rfl
  · intro h; apply IScalar.eq_of_val_eq; simp [h]

end OsuProofs
