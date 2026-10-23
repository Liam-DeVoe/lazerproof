/-
Spec-level validity facts for `NetDecimal` (mantissa `< 2^96`, scale `≤ 28`) of the results of
`CreateTruncating`, `/`, `*` and `Round`: they discharge the validity guards of the Rust
refinement theorems when the operations are chained (`BindableNumber` snapping).
-/
import OsuProofs.Net.Decimal9
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

def DValid (d : NetDecimal) : Prop := d.mant < 2^96 ∧ d.scale ≤ 28

theorem finishFromR_valid (neg : Bool) (mant : Nat) (power : Int) (ms : Nat) (steps : List Nat)
    (hm : mant < 2^96) (hp : power ≤ 28) (d : NetDecimal)
    (h : NetDecimal.finishFromR neg mant power ms steps = .ok d) : DValid d := by
  unfold NetDecimal.finishFromR at h
  dsimp only at h
  split at h
  · split at h
    · simp at h
    · simp only [Except.ok.injEq] at h; subst h
      refine ⟨?_, by simp⟩
      rename_i h1 h2; simp only [NetDecimal.two96] at h2; simp only; omega
  · have key : ∀ (l : List Nat) (x : Nat × Nat × Nat), x.1 ≤ mant → x.2.1 ≤ 28 →
        (l.foldl (fun (acc : Nat × Nat × Nat) k =>
          if acc.2.2 ≥ k && acc.1 % 10 ^ k == 0 then (acc.1 / 10 ^ k, acc.2.1 - k, acc.2.2 - k) else (acc.1, acc.2.1, acc.2.2)) x).1 ≤ mant ∧
        (l.foldl (fun (acc : Nat × Nat × Nat) k =>
          if acc.2.2 ≥ k && acc.1 % 10 ^ k == 0 then (acc.1 / 10 ^ k, acc.2.1 - k, acc.2.2 - k) else (acc.1, acc.2.1, acc.2.2)) x).2.1 ≤ 28 := by
      intro l
      induction l with
      | nil => intro x h1 h2; exact ⟨h1, h2⟩
      | cons k t ih =>
        intro x h1 h2
        simp only [List.foldl_cons]
        apply ih
        · split
          · simp only; exact Nat.le_trans (Nat.div_le_self _ _) h1
          · exact h1
        · split
          · simp only; omega
          · exact h2
    simp only [Except.ok.injEq] at h; subst h
    have := key steps (mant, power.toNat, Nat.min power.toNat ms) (by simp) (by simp; omega)
    exact ⟨Nat.lt_of_le_of_lt this.1 hm, this.2⟩

theorem zero_valid : DValid NetDecimal.zero := by simp [DValid, NetDecimal.zero]

theorem int64_toNat_lt (x : Int64) : x.toInt.toNat < 2^96 := by
  have := Int64.toInt_lt x; omega

theorem int32_toNat_lt (x : Int32) : x.toInt.toNat < 2^96 := by
  have := Int32.toInt_lt x; omega

theorem fin_shape (neg : Bool) (M : Nat) (P : Int) (ms : Nat) (steps : List Nat) (hM : M < 2^96) (hP : P ≤ 28)
    (d : NetDecimal) (h : (if (M == 0) = true then .ok NetDecimal.zero else NetDecimal.finishFromR neg M P ms steps) = .ok d) :
    DValid d := by
  split at h
  · simp only [Except.ok.injEq] at h; subst h; exact zero_valid
  · exact finishFromR_valid neg M P ms steps hM hP d h

theorem pow_bound1 (P : Int) (c : Bool) (a b z : F64) :
    (if P ≥ 0 then (a, if P > 28 then 28 else P) else if c = true then (b, P) else (z, (0 : Int))).2 ≤ 28 := by
  split_ifs <;> simp <;> omega

theorem pow_bound2 (X : F64 × Int) (b : Bool) (g : F64) (hX : X.2 ≤ 28) :
    (if (b && decide (X.2 < 28)) = true then (g, X.2 + 1) else X).2 ≤ 28 := by
  split_ifs with h
  · simp at h; simp; omega
  · exact hX

theorem ofF64_valid (x : F64) (d : NetDecimal) (h : NetDecimal.ofF64 x = .ok d) : DValid d := by
  unfold NetDecimal.ofF64 at h
  generalize ((x.toBits >>> 52) &&& 0x7FF).toNat = E at h
  dsimp only at h
  by_cases h1 : (E : Int) - 1022 < -94
  · rw [if_pos h1, Except.ok.injEq] at h; subst h; exact zero_valid
  · rw [if_neg h1] at h
    by_cases h2 : (E : Int) - 1022 > 96
    · rw [if_pos h2] at h; simp at h
    · rw [if_neg h2] at h
      refine fin_shape _ _ _ _ _ (int64_toNat_lt _) ?_ d h
      exact pow_bound2 _ _ _ (pow_bound1 _ _ _ _ _)

theorem ofF32_valid (x : F32) (d : NetDecimal) (h : NetDecimal.ofF32 x = .ok d) : DValid d := by
  unfold NetDecimal.ofF32 at h
  generalize ((x.toBits >>> 23) &&& 0xFF).toNat = E at h
  dsimp only at h
  by_cases h1 : (E : Int) - 126 < -94
  · rw [if_pos h1, Except.ok.injEq] at h; subst h; exact zero_valid
  · rw [if_neg h1] at h
    by_cases h2 : (E : Int) - 126 > 96
    · rw [if_pos h2] at h; simp at h
    · rw [if_neg h2] at h
      refine fin_shape _ _ _ _ _ (int32_toNat_lt _) ?_ d h
      exact pow_bound2 _ _ _ (pow_bound1 _ _ _ _ _)

theorem createTruncatingF64_valid (x : F64) (d : NetDecimal) (h : NetDecimal.createTruncatingF64 x = .ok d) :
    DValid d := by
  unfold NetDecimal.createTruncatingF64 at h
  split at h
  · simp only [Except.ok.injEq] at h; subst h; simp [DValid, NetDecimal.maxValue, NetDecimal.two96]
  · split at h
    · simp only [Except.ok.injEq] at h; subst h; simp [DValid, NetDecimal.minValue, NetDecimal.two96]
    · split at h
      · simp only [Except.ok.injEq] at h; subst h; simp [DValid]
      · exact ofF64_valid x d h

theorem createTruncatingF32_valid (x : F32) (d : NetDecimal) (h : NetDecimal.createTruncatingF32 x = .ok d) :
    DValid d := by
  unfold NetDecimal.createTruncatingF32 at h
  split at h
  · simp only [Except.ok.injEq] at h; subst h; simp [DValid, NetDecimal.maxValue, NetDecimal.two96]
  · split at h
    · simp only [Except.ok.injEq] at h; subst h; simp [DValid, NetDecimal.minValue, NetDecimal.two96]
    · split at h
      · simp only [Except.ok.injEq] at h; subst h; simp [DValid]
      · exact ofF32_valid x d h

/-! ## division -/

def fisS : ForInStep DS → DS | .done c => c | .yield c => c

def DI (den : Nat) (s : DS) : Prop := s.2.2.1 < 2^96 ∧ s.2.2.2.1 < den ∧ -30 ≤ s.1 ∧ s.1 ≤ 28

theorem overflowUnscale_res (q : Nat) (sc : Int) (st : Bool) (w : Nat × Int)
    (h : NetDecimal.overflowUnscale q sc st = .ok w) : w.1 ≤ q / 10 + 1 ∧ w.2 = sc - 1 ∧ 0 ≤ w.2 := by
  unfold NetDecimal.overflowUnscale at h
  dsimp only at h
  split at h
  · simp at h
  · simp only [Except.ok.injEq] at h; subst h
    refine ⟨?_, rfl, by omega⟩
    simp only; split <;> omega

theorem divInc_inv (den : Nat) (hden : 0 < den) (s : DS) (p : Nat) (fl : Bool) (hI : DI den s) (hp : p ≤ 9)
    (hsp : s.1 + p ≤ 28) (st : ForInStep DS) (h : divInc den s p fl = .ok st) :
    DI den (fisS st) := by
  obtain ⟨h1, h2, h3, h4⟩ := hI
  have hpw : 10 ^ p ≤ 10 ^ 9 := Nat.pow_le_pow_right (by decide) hp
  have hpw0 : 0 < 10 ^ p := Nat.pow_pos (by decide)
  have hdl : s.2.2.2.1 * 10 ^ p / den < 10 ^ p := by
    apply Nat.div_lt_of_lt_mul; exact Nat.mul_lt_mul_of_pos_right h2 hpw0
  unfold divInc at h
  split at h
  · simp at h
  · rename_i hq
    split at h
    · rename_i hq2
      revert h
      cases hou : NetDecimal.overflowUnscale (s.2.2.1 * 10 ^ p + s.2.2.2.1 * 10 ^ p / den) (s.1 + p)
          (s.2.2.2.1 * 10 ^ p % den != 0) with
      | error e => intro h; simp at h
      | ok w =>
        intro h
        simp only [except_bind_ok] at h
        have h' := Except.ok.inj h; subst h'
        obtain ⟨w1, w2, w3⟩ := overflowUnscale_res _ _ _ w hou
        refine ⟨?_, Nat.mod_lt _ hden, by simp only [fisS]; omega, by simp only [fisS]; omega⟩
        simp only [NetDecimal.two96] at hq hq2 ⊢
        simp only [fisS]
        have : s.2.2.1 * 10 ^ p + s.2.2.2.1 * 10 ^ p / den < 2^96 + 10^9 := by omega
        rw [show (2:Nat)^96 = 79228162514264337593543950336 from rfl] at this ⊢; omega
    · rename_i hq2
      have h' := Except.ok.inj h; subst h'
      simp only [NetDecimal.two96] at hq2
      exact ⟨by simp only [fisS]; omega, Nat.mod_lt _ hden, by simp only [fisS]; omega, by simp only [fisS]; omega⟩

theorem divStep_inv (den : Nat) (hden : 0 < den) (s : DS) (hI : DI den s) (st : ForInStep DS)
    (h : divStep den s = .ok st) : DI den (fisS st) := by
  have hI' := hI
  obtain ⟨h1, h2, h3, h4⟩ := hI'
  unfold divStep at h
  split at h
  · have h' := Except.ok.inj h; subst h'; exact hI
  · split at h
    · split at h
      · have h' := Except.ok.inj h; subst h'; exact hI
      · exact divInc_inv den hden s _ _ hI (Nat.min_le_left _ _)
          (by have := Nat.min_le_right 9 (-s.1).toNat; omega) st h
    · split at h
      · have h' := Except.ok.inj h; subst h'; exact hI
      · revert h
        cases hss : NetDecimal.searchScale s.2.2.1 s.1 with
        | error e => intro h; simp at h
        | ok p =>
          intro h
          simp only [except_bind_ok] at h
          rename_i h28
          have hb := searchScale_le s.2.2.1 s.1 (by omega) p hss
          split at h
          · have h' := Except.ok.inj h; subst h'; exact hI
          · exact divInc_inv den hden s p true hI hb.2 hb.1 st h

theorem iterEx_div_inv (den : Nat) (hden : 0 < den) : ∀ (n : Nat) (s : DS), DI den s →
    ∀ s', iterEx (divStep den) n s = .ok s' → DI den s'
  | 0, s, hI, s', h => by simp only [iterEx, Except.ok.injEq] at h; subst h; exact hI
  | n+1, s, hI, s', h => by
    simp only [iterEx] at h
    revert h
    cases hst : divStep den s with
    | error e => intro h; simp at h
    | ok st =>
      have := divStep_inv den hden s hI st hst
      cases st with
      | done c => intro h; simp only [Except.ok.injEq] at h; subst h; exact this
      | yield c => intro h; exact iterEx_div_inv den hden n c this s' h

theorem unscale_mant_le (q : Nat) (s : Int) : (NetDecimal.unscale q s).1 ≤ q := by
  rw [unscale_eq]
  have st : ∀ (K : Nat) (c : Int) (x : Nat × Int), (ustep K c x).1 ≤ x.1 := by
    intro K c x; unfold ustep; split
    · exact Nat.div_le_self _ _
    · exact Nat.le_refl _
  exact Nat.le_trans (st _ _ _) (Nat.le_trans (st _ _ _) (Nat.le_trans (st _ _ _) (Nat.le_trans (st _ _ _)
    (Nat.le_trans (st _ _ _) (Nat.le_trans (st _ _ _) (st _ _ _))))))

theorem divFin_valid (neg fl : Bool) (q : Nat) (sc : Int) (hq : q < 2^96) (hs : sc ≤ 28) (d : NetDecimal)
    (h : divFin neg fl q sc = .ok d) : DValid d := by
  unfold divFin at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact ⟨Nat.lt_of_le_of_lt (unscale_mant_le q sc) hq, by have := unscale_le q sc; simp only; omega⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact ⟨hq, by simp only; omega⟩

theorem divPost_valid (neg : Bool) (den : Nat) (s : DS) (hI : DI den s) (d : NetDecimal)
    (h : divPost neg den s = .ok d) : DValid d := by
  obtain ⟨h1, h2, h3, h4⟩ := hI
  unfold divPost at h
  split at h
  · split at h
    · split at h
      · revert h
        cases hou : NetDecimal.overflowUnscale (s.2.2.1 + 1) s.1 true with
        | error e => intro h; simp at h
        | ok w =>
          intro h
          simp only [except_bind_ok] at h
          obtain ⟨w1, w2, w3⟩ := overflowUnscale_res _ _ _ w hou
          exact divFin_valid _ _ _ _ (by omega) (by omega) d h
      · rename_i hq; simp only [NetDecimal.two96] at hq
        exact divFin_valid _ _ _ _ (by omega) h4 d h
    · exact divFin_valid _ _ _ _ h1 h4 d h
  · exact divFin_valid _ _ _ _ h1 h4 d h

theorem div_valid (d1 d2 : NetDecimal) (h1 : DValid d1) (h2 : DValid d2) (d : NetDecimal)
    (h : NetDecimal.div d1 d2 = .ok d) : DValid d := by
  rw [div_nf] at h
  split at h
  · simp at h
  · rename_i hz
    revert h
    cases hit : iterEx (divStep d2.mant) 40 ((d1.scale : Int) - d2.scale, false, d1.mant / d2.mant, d1.mant % d2.mant,
        false, false) with
    | error e => intro h; simp at h
    | ok s =>
      intro h
      simp only [except_bind_ok] at h
      have hI := iterEx_div_inv d2.mant (by omega) 40 _
        ⟨Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h1.1, Nat.mod_lt _ (by omega),
          by have := h2.2; simp only; omega, by have := h1.2; simp only; omega⟩ s hit
      exact divPost_valid _ _ s hI d h

/-! ## rounding and multiplication -/

theorem round_valid (d : NetDecimal) (h : DValid d) : DValid (NetDecimal.round d) := by
  unfold NetDecimal.round
  split
  · exact h
  · rename_i hs
    have hs' : 1 ≤ d.scale := by simp at hs; omega
    have hp : 10 ^ 1 ≤ 10 ^ d.scale := Nat.pow_le_pow_right (by decide) hs'
    have h10 : d.mant / 10 ^ d.scale ≤ d.mant / 10 ^ 1 := Nat.div_le_div_left hp (by decide)
    have := h.1
    dsimp only
    refine ⟨?_, by simp⟩
    simp only; split <;> omega

def fisR : ForInStep SRS → SRS | .done c => c | .yield c => c

def SI (s : SRS) : Prop := s.2.2.1 ≤ 28 ∧ (s.1.map (·.2)).getD 0 ≤ 28

theorem srStep_inv (s : SRS) (hI : SI s) (st : ForInStep SRS) (h : srStep s = .ok st) : SI (fisR st) := by
  obtain ⟨h1, h2⟩ := hI
  unfold srStep at h
  dsimp only at h
  generalize (if s.2.1 ≥ 9 then 9 else s.2.1.toNat) = ch at h
  split at h
  · have h' := Except.ok.inj h; subst h'; simp [SI, fisR]; omega
  · split at h
    · split at h
      · simp at h
      · have h' := Except.ok.inj h; subst h'; simp [SI, fisR]; omega
    · split at h
      · split at h
        · split at h
          · simp at h
          · have h' := Except.ok.inj h; subst h'; simp [SI, fisR]; omega
        · have h' := Except.ok.inj h; subst h'; simp [SI, fisR]; omega
      · have h' := Except.ok.inj h; subst h'; simp [SI, fisR]; omega

theorem iterEx_sr_inv : ∀ (n : Nat) (s : SRS), SI s → ∀ s', iterEx srStep n s = .ok s' → SI s'
  | 0, s, hI, s', h => by simp only [iterEx, Except.ok.injEq] at h; subst h; exact hI
  | n+1, s, hI, s', h => by
    simp only [iterEx] at h
    revert h
    cases hst : srStep s with
    | error e => intro h; simp at h
    | ok st =>
      have := srStep_inv s hI st hst
      cases st with
      | done c => intro h; simp only [Except.ok.injEq] at h; subst h; exact this
      | yield c => intro h; exact iterEx_sr_inv n c this s' h

theorem scaleResult_scale (p scale : Nat) (w : Nat × Nat) (h : NetDecimal.scaleResult p scale = .ok w) : w.2 ≤ 28 := by
  rw [scaleResult_nf] at h
  generalize (if p ≥ NetDecimal.two96 then NetDecimal.sar ((((p.log2 + 1 : Nat) : Int) - 97) * 77) 8 + 1 else 0) = N at h
  dsimp only at h
  by_cases hov : p ≥ NetDecimal.two96 ∧ N > scale
  · rw [if_pos hov] at h; simp at h
  · rw [if_neg hov] at h
    have hgo : ∀ M : Int, M ≥ (scale : Int) - 28 →
        (if M = 0 then Except.ok (p, scale) else iterEx srStep 120 (none, M, (scale : Int) - M, p, false, 0, 1) >>= srPost) = .ok w →
        w.2 ≤ 28 := by
      intro M hM h
      by_cases hz : M = 0
      · rw [if_pos hz] at h; simp only [Except.ok.injEq] at h; subst h; simp only; omega
      · rw [if_neg hz] at h
        revert h
        cases hit : iterEx srStep 120 (none, M, (scale : Int) - M, p, false, 0, 1) with
        | error e => intro h; simp at h
        | ok s' =>
          intro h
          simp only [except_bind_ok] at h
          have hI := iterEx_sr_inv 120 _ ⟨by simp only; omega, by simp⟩ s' hit
          unfold srPost at h
          obtain ⟨hI1, hI2⟩ := hI
          cases hs1 : s'.1 with
          | some r =>
            rw [hs1] at h hI2; simp only [Except.ok.injEq] at h; subst h; simpa using hI2
          | none =>
            rw [hs1] at h; simp only [Except.ok.injEq] at h; subst h; simp only; omega
    by_cases hlt : N < (scale : Int) - 28
    · rw [if_pos hlt] at h; exact hgo _ (by omega) h
    · rw [if_neg hlt] at h; exact hgo _ (by omega) h

theorem mul_scale (d1 d2 : NetDecimal) (h1 : DValid d1) (h2 : DValid d2) (d : NetDecimal)
    (h : NetDecimal.mul d1 d2 = .ok d) : d.scale ≤ 28 := by
  rw [mul_nf] at h
  split at h
  · split at h
    · split at h
      · simp only [Except.ok.injEq] at h; subst h; simp [NetDecimal.zero]
      · simp only [Except.ok.injEq] at h; subst h; simp
    · rename_i hs; simp only [Except.ok.injEq] at h; subst h; simp only; omega
  · split at h
    · simp only [Except.ok.injEq] at h; subst h; simp [NetDecimal.zero]
    · split at h
      · revert h
        cases hsr : NetDecimal.scaleResult (d1.mant * d2.mant) (d1.scale + d2.scale) with
        | error e => intro h; simp at h
        | ok w =>
          intro h
          simp only [except_bind_ok, Except.ok.injEq] at h; subst h
          exact scaleResult_scale _ _ w hsr
      · rename_i hb; simp only [Except.ok.injEq] at h; subst h; simp only; omega

end OsuProofs
