/-
Generic reasoning about Aeneas `loop`s (a `partial_fixpoint`): a loop whose body either finishes
with a value satisfying `Q`, or continues in a state that keeps the invariant `P` and decreases a
natural-number measure, terminates with `ok y`, `Q y`.
-/
import OsuProofs.Prims
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result

namespace OsuProofs

theorem loop_unfold {α β} (body : α → Result (ControlFlow α β)) (x : α) :
    loop body x = (do
      let r ← body x
      match r with
      | .cont x' => loop body x'
      | .done y => ok y) := by
  rw [loop]; rfl

theorem loop_ok {α β} (body : α → Result (ControlFlow α β)) (measure : α → Nat) (P : α → Prop)
    (Q : β → Prop)
    (h : ∀ x, P x → (∃ y, body x = ok (.done y) ∧ Q y) ∨
      (∃ x', body x = ok (.cont x') ∧ P x' ∧ measure x' < measure x)) :
    ∀ x, P x → ∃ y, loop body x = ok y ∧ Q y := by
  intro x
  induction hm : measure x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    intro hx
    rcases h x hx with ⟨y, hb, hq⟩ | ⟨x', hb, hp, hlt⟩
    · exact ⟨y, by rw [loop_unfold, hb]; simp, hq⟩
    · obtain ⟨y, hy, hq⟩ := ih (measure x') (hm ▸ hlt) x' rfl hp
      exact ⟨y, by rw [loop_unfold, hb]; simpa using hy, hq⟩

/-- Equational form: the loop computes `f x` for a function `f` that is invariant along the loop. -/
theorem loop_eq {α β} (body : α → Result (ControlFlow α β)) (measure : α → Nat) (P : α → Prop)
    (f : α → β)
    (h : ∀ x, P x → body x = ok (.done (f x)) ∨
      (∃ x', body x = ok (.cont x') ∧ P x' ∧ measure x' < measure x ∧ f x' = f x)) :
    ∀ x, P x → loop body x = ok (f x) := by
  intro x hx
  have := loop_ok body measure (fun z => P z ∧ f z = f x) (fun y => y = f x)
    (by
      intro z ⟨hz, hf⟩
      rcases h z hz with hb | ⟨x', hb, hp, hlt, hf'⟩
      · exact Or.inl ⟨f z, hb, hf⟩
      · exact Or.inr ⟨x', hb, ⟨hp, hf'.trans hf⟩, hlt⟩) x ⟨hx, rfl⟩
  obtain ⟨y, hy, rfl⟩ := this
  exact hy

end OsuProofs
