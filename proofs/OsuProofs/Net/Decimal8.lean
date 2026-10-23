/-
`net::decimal` part 8: `decimal / decimal` (`VarDecDiv`): the 40-iteration division loop in
lockstep with the spec loop, the rounding/unscale tail.
-/
import OsuProofs.Net.Decimal7
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

theorem powerOvfl_hi_table : (NetDecimal.powerOvfl 0).1 = 429496729 ∧ (NetDecimal.powerOvfl 1).1 = 42949672 ∧
    (NetDecimal.powerOvfl 2).1 = 4294967 ∧ (NetDecimal.powerOvfl 3).1 = 429496 ∧
    (NetDecimal.powerOvfl 4).1 = 42949 ∧ (NetDecimal.powerOvfl 5).1 = 4294 ∧
    (NetDecimal.powerOvfl 6).1 = 429 ∧ (NetDecimal.powerOvfl 7).1 = 42 := by
  unfold NetDecimal.powerOvfl NetDecimal.two96; decide +kernel

/-- `SearchScale` never lets the scale exceed 28 (and scales by at most `10^9`). -/
theorem searchScale_le (q : Nat) (scale : Int) (hs : scale < 28) (p : Nat)
    (h : NetDecimal.searchScale q scale = .ok p) : scale + p ≤ 28 ∧ p ≤ 9 := by
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7⟩ := powerOvfl_hi_table
  unfold NetDecimal.searchScale at h
  dsimp only at h
  generalize hu : q >>> 64 = u at h
  generalize hl : q % 2^64 = low at h
  split at h
  · split at h <;> simp at h <;> omega
  · -- band ≤ num0 ≤ 8
    generalize hn0 : (if u > 42949 then
          if u > 4294967 then (if u > 42949672 then 1 else 2)
          else (if u > 429496 then 3 else 4)
        else if u > 429 then (if u > 4294 then 5 else 6)
        else (if u > 42 then 7 else 8)) = num0 at h
    have hn0b : 1 ≤ num0 ∧ num0 ≤ 8 := by rw [← hn0]; split_ifs <;> omega
    generalize hb : (if u == (NetDecimal.powerOvfl (num0 - 1)).1 && low > (NetDecimal.powerOvfl (num0 - 1)).2
        then num0 - 1 else num0) = band at h
    have hbb : band ≤ num0 := by rw [← hb]; split <;> omega
    split at h
    · rename_i h19
      have hn : 1 ≤ (28 - scale).toNat ∧ (28 - scale).toNat ≤ 8 := by omega
      split at h
      · rename_i hlt
        split at h <;> simp at h <;> omega
      · rename_i hge
        have hband : band ≤ (28 - scale).toNat := by
          have hn0le : num0 ≤ (28 - scale).toNat := by
            rw [← hn0]
            rcases (show (28 - scale).toNat = 1 ∨ (28 - scale).toNat = 2 ∨ (28 - scale).toNat = 3 ∨
                (28 - scale).toNat = 4 ∨ (28 - scale).toNat = 5 ∨ (28 - scale).toNat = 6 ∨
                (28 - scale).toNat = 7 ∨ (28 - scale).toNat = 8 by omega) with e | e | e | e | e | e | e | e <;>
              rw [e] at hge <;> simp only [Nat.sub_self, Nat.add_one_sub_one] at hge <;>
              simp only [t0, t1, t2, t3, t4, t5, t6, t7] at hge <;> rw [e] <;> split_ifs <;> omega
          omega
        split at h <;> simp at h <;> omega
    · split at h
      · simp at h <;> omega
      · split at h <;> simp at h <;> omega

/-! ## the spec division loop -/

abbrev DS := Int × Bool × Nat × Nat × Bool × Bool

/-- One `IncreaseScale` step of the spec loop (`p` digits, `flag'` the new flag). -/
def divInc (den : Nat) (s : DS) (p : Nat) (flag' : Bool) : Except NetExn (ForInStep DS) :=
  if s.2.2.1 * 10 ^ p ≥ NetDecimal.two96 then throw .overflow
  else if s.2.2.1 * 10 ^ p + s.2.2.2.1 * 10 ^ p / den ≥ NetDecimal.two96 then do
    let x ← NetDecimal.overflowUnscale (s.2.2.1 * 10 ^ p + s.2.2.2.1 * 10 ^ p / den) (s.1 + p)
      (s.2.2.2.1 * 10 ^ p % den != 0)
    pure (.done (x.2, flag', x.1, s.2.2.2.1 * 10 ^ p % den, s.2.2.2.2.1, true))
  else pure (.yield (s.1 + p, flag', s.2.2.1 * 10 ^ p + s.2.2.2.1 * 10 ^ p / den, s.2.2.2.1 * 10 ^ p % den,
    s.2.2.2.2.1, s.2.2.2.2.2))

/-- The spec `VarDecDiv` loop body (as elaborated; the loop index is unused). -/
def divStep (den : Nat) (s : DS) : Except NetExn (ForInStep DS) :=
  if s.2.2.2.2.2 = true then pure (.done (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2))
  else if s.2.2.2.1 = 0 then
    if s.1 ≥ 0 then pure (.done (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, true))
    else divInc den s (Nat.min 9 (-s.1).toNat) s.2.1
  else if s.1 = 28 then pure (.done (s.1, true, s.2.2.1, s.2.2.2.1, true, true))
  else do
    let p ← NetDecimal.searchScale s.2.2.1 s.1
    if p = 0 then pure (.done (s.1, true, s.2.2.1, s.2.2.2.1, true, true))
    else divInc den s p true

/-- The final `Unscale` (when `flag`) and scale clamp. -/
def divFin (neg : Bool) (flag : Bool) (q : Nat) (sc : Int) : Except NetExn NetDecimal :=
  if flag = true then pure ⟨neg, (NetDecimal.unscale q sc).1, (NetDecimal.unscale q sc).2.toNat⟩
  else pure ⟨neg, q, sc.toNat⟩

/-- The spec tail after the loop (rounding, overflow-unscale, unscale). -/
def divPost (neg : Bool) (den : Nat) (s : DS) : Except NetExn NetDecimal :=
  if s.2.2.2.2.1 = true then
    if (decide (2 * s.2.2.2.1 > den) || 2 * s.2.2.2.1 == den && s.2.2.1 % 2 == 1) = true then
      if s.2.2.1 + 1 ≥ NetDecimal.two96 then do
        let x ← NetDecimal.overflowUnscale (s.2.2.1 + 1) s.1 true
        divFin neg s.2.1 x.1 x.2
      else divFin neg s.2.1 (s.2.2.1 + 1) s.1
    else divFin neg s.2.1 s.2.2.1 s.1
  else divFin neg s.2.1 s.2.2.1 s.1

theorem div_nf (d1 d2 : NetDecimal) : NetDecimal.div d1 d2 =
    if d2.mant = 0 then .error .arithmetic
    else iterEx (divStep d2.mant) 40 ((d1.scale : Int) - d2.scale, false, d1.mant / d2.mant, d1.mant % d2.mant,
      false, false) >>= divPost (d1.neg != d2.neg) d2.mant := by
  unfold NetDecimal.div
  dsimp only
  by_cases h : d2.mant = 0
  · simp [h]
  · simp only [h, beq_iff_eq, if_false, ite_false]
    rw [forIn_range_ex' _ (fun _ _ => rfl)]
    congr 1

end OsuProofs
