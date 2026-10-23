/-
`net::decimal` part 6: the `ScaleResult` loop, `ScaleResult`, `decimal * decimal`.
-/
import OsuProofs.Net.Decimal5
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

theorem exnS_I (e : NetExn) : exnS (exnI e) = e := by cases e <;> rfl

theorem sr_loop (FINAL : Except NetExn (Nat × Nat)) :
    ∀ x : SRR, ((∃ s, srRel x s ∧ (iterEx srStep (120 - x.2.2.2.2.2.2.val.toNat) s >>= srPost) = FINAL) ∨
        (∃ r, x.2.2.2.2.2.1 = some r ∧ resRel qsR r FINAL)) →
      ∃ y, net.decimal.scale_result_loop_loop x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2 = ok y ∧
        ∃ r, y.2.2 = some r ∧ resRel qsR r FINAL := by
  intro x hx
  unfold net.decimal.scale_result_loop_loop
  refine loop_ok _ (fun (x : SRR) => 121 - x.2.2.2.2.2.2.val.toNat)
    (fun (x : SRR) => (∃ s, srRel x s ∧ (iterEx srStep (120 - x.2.2.2.2.2.2.val.toNat) s >>= srPost) = FINAL) ∨
        (∃ r, x.2.2.2.2.2.1 = some r ∧ resRel qsR r FINAL))
    (fun (y : net.decimal.U192 × I64 × Option (core.result.Result (U128 × U32) net.basic.NetExn)) =>
      ∃ r, y.2.2 = some r ∧ resRel qsR r FINAL) ?_ x hx
  rintro ⟨q, sc, num, sticky, rem, res, it⟩ hx
  rcases hx with ⟨s, hrel, hfin⟩ | ⟨r, hr, hrr⟩
  · right
    obtain ⟨x', hb, hit', hm⟩ := sr_step (q, sc, num, sticky, rem, res, it) s hrel
    have hres : res = none := hrel.1
    have hit120 : it.val < 120 := by have := hrel; unfold srRel at this; dsimp only at this; omega
    have hit0 : 0 ≤ it.val := by have := hrel; unfold srRel at this; dsimp only at this; omega
    refine ⟨x', by simpa [hres] using hb, ?_, by dsimp only at hit' ⊢; omega⟩
    dsimp only at hfin hit' hm
    have e : 120 - it.val.toNat = (120 - x'.2.2.2.2.2.2.val.toNat) + 1 := by omega
    rw [e] at hfin
    simp only [iterEx] at hfin
    revert hm hfin
    cases srStep s with
    | error e =>
      intro hfin hm
      right; refine ⟨_, hm, ?_⟩
      rw [← hfin]; simp [resRel, exnS_I]
    | ok st =>
      cases st with
      | yield s' => intro hfin hm; left; exact ⟨s', hm, hfin⟩
      | done s' =>
        intro hfin hm
        obtain ⟨r, hr, hrr⟩ := hm
        right; refine ⟨r, hr, ?_⟩
        rw [← hfin]; exact hrr
  · left
    dsimp only at hr
    subst hr
    exact ⟨(q, sc, some r), by simp [net.decimal.scale_result_loop_loop.body], r, rfl, hrr⟩

theorem sr_loop_run (p : net.decimal.U192) (sc0 num0 : I64) (FINAL : Except NetExn (Nat × Nat))
    (h : srRel (p, sc0, num0, false, 0#u64, none, 0#i32) (none, num0.val, sc0.val, u192S p, false, 0, 1))
    (hF : (iterEx srStep 120 (none, num0.val, sc0.val, u192S p, false, 0, 1) >>= srPost) = FINAL) :
    ∃ r, net.decimal.scale_result_loop p sc0 num0 = ok r ∧ resRel qsR r FINAL := by
  obtain ⟨y, hy, r, hr, hrr⟩ := sr_loop FINAL (p, sc0, num0, false, 0#u64, none, 0#i32) (Or.inl ⟨_, h, by simpa using hF⟩)
  obtain ⟨q, sc, res⟩ := y
  dsimp only at hr; subst hr
  exact ⟨r, by simp only [net.decimal.scale_result_loop] at *; simp [hy], hrr⟩

theorem scaleResult_loop_eq (p : Nat) (num sc : Int) :
    (do let __s ← forIn (m := Except NetExn) [:120] ((none : Option (Nat × Nat)), num, sc, p, false, 0, 1) (fun _ s => srStep s)
        srPost __s) = (iterEx srStep 120 (none, num, sc, p, false, 0, 1) >>= srPost) := by
  rw [forIn_range_ex]

theorem scaleResult_nf (p scale : Nat) : NetDecimal.scaleResult p scale =
    (let num1 : Int := if p ≥ NetDecimal.two96 then NetDecimal.sar ((((p.log2 + 1 : Nat) : Int) - 97) * 77) 8 + 1 else 0
     if p ≥ NetDecimal.two96 ∧ num1 > scale then .error .overflow
     else
       let num := if num1 < (scale : Int) - 28 then (scale : Int) - 28 else num1
       if num = 0 then .ok (p, scale)
       else iterEx srStep 120 (none, num, scale - num, p, false, 0, 1) >>= srPost) := by
  unfold NetDecimal.scaleResult
  dsimp only
  by_cases h96 : p ≥ NetDecimal.two96
  · rw [if_pos h96]
    simp only [h96, if_true, true_and]
    by_cases hov : NetDecimal.sar ((((p.log2 + 1 : Nat) : Int) - 97) * 77) 8 + 1 > scale
    · rw [if_pos hov, if_pos hov]; rfl
    · rw [if_neg hov, if_neg hov]
      by_cases hlt : NetDecimal.sar ((((p.log2 + 1 : Nat) : Int) - 97) * 77) 8 + 1 < (scale : Int) - 28
      · simp only [hlt, if_true]
        by_cases h0 : (scale : Int) - 28 = 0
        · simp [h0]
        · rw [if_neg (by simpa using h0), if_neg h0, ← scaleResult_loop_eq]
          congr 1; funext i; unfold srPost; cases i.1 <;> rfl
      · simp only [hlt, if_false]
        by_cases h0 : NetDecimal.sar ((((p.log2 + 1 : Nat) : Int) - 97) * 77) 8 + 1 = 0
        · simp only [h0, beq_self_eq_true, if_true]; rfl
        · rw [if_neg (by simpa using h0), if_neg h0, ← scaleResult_loop_eq]
          congr 1; funext i; unfold srPost; cases i.1 <;> rfl
  · rw [if_neg h96]
    simp only [h96, false_and, if_false]
    by_cases hlt : (0 : Int) < (scale : Int) - 28
    · simp only [hlt, if_true]
      by_cases h0 : (scale : Int) - 28 = 0
      · omega
      · rw [if_neg (by simpa using h0), if_neg h0, ← scaleResult_loop_eq]
        congr 1; funext i; unfold srPost; cases i.1 <;> rfl
    · simp only [hlt, if_false]; rfl

end OsuProofs
