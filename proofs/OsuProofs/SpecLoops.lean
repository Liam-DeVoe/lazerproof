/-
Spec-side normal forms for `for _ in [0:n]` loops whose body ignores the index (Lean's `do`
elaboration produces `forIn [:n] init (fun _ s => ...)`): in `Id` and in `Except ε`, the loop is a
bounded iteration of the body.
-/
import OsuProofs.Loops
set_option linter.unusedSimpArgs false
open Aeneas Aeneas.Std Result

namespace OsuProofs

/-- `n` iterations of an `Id`-loop body with early exit. -/
def iterId {β : Type} (g : β → ForInStep β) : Nat → β → β
  | 0, b => b
  | n+1, b => match g b with
    | .done c => c
    | .yield c => iterId g n c

theorem forIn_range'_id {β : Type} (g : β → ForInStep β) :
    ∀ (n s : Nat) (b : β), forIn (m := Id) (List.range' s n) b (fun _ x => pure (g x)) = iterId g n b := by
  intro n
  induction n with
  | zero => intro s b; rfl
  | succ n ih =>
    intro s b
    rw [List.range'_succ, List.forIn_cons]
    simp only [iterId]
    cases g b with
    | done c => rfl
    | yield c => exact ih (s + 1) c

theorem forIn_range_id {β : Type} (g : β → ForInStep β) (n : Nat) (b : β) :
    forIn (m := Id) [:n] b (fun _ x => pure (g x)) = iterId g n b := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  exact forIn_range'_id g n 0 b

/-- `n` iterations of an `Except`-loop body with early exit. -/
def iterEx {ε β : Type} (g : β → Except ε (ForInStep β)) : Nat → β → Except ε β
  | 0, b => .ok b
  | n+1, b => match g b with
    | .error e => .error e
    | .ok (.done c) => .ok c
    | .ok (.yield c) => iterEx g n c

theorem forIn_range'_ex {ε β : Type} (g : β → Except ε (ForInStep β)) :
    ∀ (n s : Nat) (b : β), forIn (m := Except ε) (List.range' s n) b (fun _ x => g x) = iterEx g n b := by
  intro n
  induction n with
  | zero => intro s b; rfl
  | succ n ih =>
    intro s b
    rw [List.range'_succ, List.forIn_cons]
    simp only [iterEx]
    cases h : g b with
    | error e => rfl
    | ok r =>
      cases r with
      | done c => rfl
      | yield c => exact ih (s + 1) c

theorem forIn_range_ex {ε β : Type} (g : β → Except ε (ForInStep β)) (n : Nat) (b : β) :
    forIn (m := Except ε) [:n] b (fun _ x => g x) = iterEx g n b := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  exact forIn_range'_ex g n 0 b

theorem forIn_range_id' {β : Type} (f : Nat → β → Id (ForInStep β)) (hf : ∀ i x, f i x = f 0 x) (n : Nat) (b : β) :
    forIn (m := Id) [:n] b f = iterId (f 0) n b := by
  have : f = fun _ x => pure (f 0 x) := by funext i x; exact hf i x
  rw [this]; exact forIn_range_id (f 0) n b
theorem forIn_range_ex' {ε β : Type} (f : Nat → β → Except ε (ForInStep β)) (hf : ∀ i x, f i x = f 0 x) (n : Nat) (b : β) :
    forIn (m := Except ε) [:n] b f = iterEx (f 0) n b := by
  have : f = fun _ x => f 0 x := by funext i x; exact hf i x
  rw [this]; exact forIn_range_ex (f 0) n b

end OsuProofs
