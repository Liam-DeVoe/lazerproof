/-
Spec-side normal form of `OsuModel.Sim.simulateSteps` (no Aeneas import: fast to check).
The `for`/`while`/`break` do-block of the spec (in `Except`: a `Math.Clamp` on out-of-order frames and
fuel exhaustion throw) is related to explicit structural recursion (`inner`, fold over the references):
whenever the spec succeeds, its steps are `outer`'s (`simulateSteps_ok`); the Aeneas-side proof targets `outer`.
-/
import OsuModel.Sim.Schedule
open OsuModel.Net OsuModel.Sim

namespace OsuProofs.SpecSched

/-- `frameTime` of the spec. -/
def ft (frames : Array F64) (i : Int) : F64 :=
  if i < 0 then F64.negInf else if i ≥ frames.size then F64.posInf else frames[i.toNat]!

/-- The proposed time after the FSC clamping (first part of the loop body). -/
def propose (gst r : F64) (first : Bool) (manual : F64) : F64 :=
  if first then r
  else if manual < gst then F64.min gst r
  else if catchupThreshold < F64.abs (manual - r) then
    (if manual < r then F64.min r (manual + sixtyFrameTime) else F64.max r (manual - sixtyFrameTime))
  else r

/-- One step: `(first, manual, idx, handlerTime)` ↦ new state (the spec's loop body). -/
def stepT (frames : Array F64) (gst r : F64) (s : Bool × F64 × Int × F64) : Bool × F64 × Int × F64 :=
  let (first, manual, idx, ht) := s
  let p := propose gst r first manual
  if frames.size == 0 then (false, p, idx, p)
  else
    let fs := ft frames idx
    let fe := ft frames (idx + 1)
    let (p, idx) := if fe ≤ p then (fe, idx + 1)
      else if (p < fs && ht == fs) = true then (p, idx - 1) else (p, idx)
    let h := match F64.clamp p (ft frames idx) (ft frames (idx + 1)) with
      | .ok v => v
      | .error _ => p
    (false, h, idx, h)

theorem ft_fold (frames : Array F64) (i : Int) :
    (if i < 0 then F64.negInf else if i ≥ frames.size then F64.posInf else frames[i.toNat]!) = ft frames i := rfl

/-- A step moves the replay-frame index by at most one. -/
theorem stepT_idx (frames : Array F64) (gst r : F64) (s : Bool × F64 × Int × F64) :
    (stepT frames gst r s).2.2.1 = s.2.2.1 ∨ (stepT frames gst r s).2.2.1 = s.2.2.1 + 1 ∨
      (stepT frames gst r s).2.2.1 = s.2.2.1 - 1 := by
  rcases s with ⟨first, manual, idx, ht⟩
  simp only [stepT]
  repeat' split
  all_goals simp_all

abbrev St6 := Array Step × Bool × F64 × Int × F64 × Nat

/-- The inner `while fuel > 0` loop (one reference `r`), as structural recursion on the fuel. -/
def inner (frames : Array F64) (gst r : F64) :
    Nat → Array Step → Bool → F64 → Int → F64 → St6
  | 0, steps, first, manual, idx, ht => (steps, first, manual, idx, ht, 0)
  | n + 1, steps, first, manual, idx, ht =>
    let s := stepT frames gst r (first, manual, idx, ht)
    let steps' := steps.push { time := s.2.1, frameIndex := s.2.2.1 }
    if (s.2.2.2 == r) = true then (steps', s.1, s.2.1, s.2.2.1, s.2.2.2, n)
    else inner frames gst r n steps' s.1 s.2.1 s.2.2.1 s.2.2.2

/-- Generic: a `while` loop in `Id` whose body is `inner`'s step equals `inner`. -/
theorem loop_inner (frames : Array F64) (gst r : F64)
    (F : Unit → St6 → Id (ForInStep St6))
    (hF : ∀ (steps : Array Step) (first : Bool) (manual : F64) (idx : Int) (ht : F64) (fuel : Nat),
      F () (steps, first, manual, idx, ht, fuel) =
        if fuel > 0 then
          let s := stepT frames gst r (first, manual, idx, ht)
          let steps' := steps.push { time := s.2.1, frameIndex := s.2.2.1 }
          if (s.2.2.2 == r) = true then pure (.done (steps', s.1, s.2.1, s.2.2.1, s.2.2.2, fuel - 1))
          else pure (.yield (steps', s.1, s.2.1, s.2.2.1, s.2.2.2, fuel - 1))
        else pure (.done (steps, first, manual, idx, ht, fuel))) :
    ∀ (fuel : Nat) (steps : Array Step) (first : Bool) (manual : F64) (idx : Int) (ht : F64),
      (forIn Lean.Loop.mk (steps, first, manual, idx, ht, fuel) F : Id St6) =
        pure (inner frames gst r fuel steps first manual idx ht) := by
  intro fuel
  induction fuel with
  | zero =>
    intro steps first manual idx ht
    show Lean.Loop.forIn _ _ _ = _
    rw [Lean.Loop.forIn_eq_of_monadTail, hF]
    simp [inner]
  | succ n ih =>
    intro steps first manual idx ht
    show Lean.Loop.forIn _ _ _ = _
    rw [Lean.Loop.forIn_eq_of_monadTail, hF]
    simp only [inner, gt_iff_lt, Nat.zero_lt_succ, ite_true, Nat.add_sub_cancel]
    split
    · rfl
    · exact ih _ _ _ _ _

/-- Generic: a `for r in refs` loop in `Id` whose body always yields is a left fold. -/
theorem forIn_yield {β} {G : F64 → β → Id (ForInStep β)} (g : F64 → β → β)
    (hG : ∀ r s, G r s = pure (.yield (g r s))) (refs : Array F64) (init : β) :
    forIn refs init G = pure (refs.foldl (fun s r => g r s) init) := by
  have : G = fun r s => pure (.yield (g r s)) := by funext r s; exact hG r s
  subst this
  exact Array.forIn_pure_yield_eq_foldl _ _

def FUEL : Nat := 100000000

/-- The outer `for r in refs` loop as a fold over references. -/
def outer (frames : Array F64) (gst : F64) (refs : Array F64) : Array Step :=
  (refs.foldl (fun (s : Array Step × Bool × F64 × Int × F64) r =>
      let o := inner frames gst r FUEL s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2
      (o.1, o.2.1, o.2.2.1, o.2.2.2.1, o.2.2.2.2.1))
    (#[], true, 0, -1, F64.negInf)).1

theorem ft_match (frames : Array F64) (i : Int) :
    (if i < 0 then F64.negInf
     else simulateSteps.match_1 (fun _ => F64) frames[i.toNat]? (fun t => t) fun _ => F64.posInf) = ft frames i := by
  unfold ft
  by_cases h : i < 0
  · simp [h]
  · simp only [h, if_false]
    by_cases h2 : i ≥ frames.size
    · have : frames.size ≤ i.toNat := by omega
      simp [h2, Array.getElem?_eq_none this, simulateSteps.match_1]
    · have : i.toNat < frames.size := by omega
      simp [h2, Array.getElem?_eq_getElem this, getElem!_pos frames i.toNat this, simulateSteps.match_1]

/-- The spec's inner `while fuel > 0` loop in `Except`: an `ok` result is `inner`'s. -/
theorem loop_innerE (frames : Array F64) (gst r : F64)
    (F : Unit → St6 → Except String (ForInStep St6))
    (hF : ∀ (steps : Array Step) (first : Bool) (manual : F64) (idx : Int) (ht : F64) (fuel : Nat) x,
      F () (steps, first, manual, idx, ht, fuel) = .ok x →
        x = if fuel > 0 then
          let s := stepT frames gst r (first, manual, idx, ht)
          let steps' := steps.push { time := s.2.1, frameIndex := s.2.2.1 }
          if (s.2.2.2 == r) = true then .done (steps', s.1, s.2.1, s.2.2.1, s.2.2.2, fuel - 1)
          else .yield (steps', s.1, s.2.1, s.2.2.1, s.2.2.2, fuel - 1)
        else .done (steps, first, manual, idx, ht, fuel)) :
    ∀ (fuel : Nat) (steps : Array Step) (first : Bool) (manual : F64) (idx : Int) (ht : F64) o,
      (forIn Lean.Loop.mk (steps, first, manual, idx, ht, fuel) F : Except String St6) = .ok o →
        o = inner frames gst r fuel steps first manual idx ht := by
  intro fuel
  induction fuel with
  | zero =>
    intro steps first manual idx ht o h
    change Lean.Loop.forIn _ _ _ = _ at h
    rw [Lean.Loop.forIn_eq_of_monadTail] at h
    cases hx : F () (steps, first, manual, idx, ht, 0) with
    | error e => rw [hx] at h; cases h
    | ok x =>
      have := hF _ _ _ _ _ _ x hx
      simp only [gt_iff_lt, Nat.lt_irrefl, ite_false] at this
      subst this; rw [hx] at h; simp [Bind.bind, Except.bind] at h; cases h; simp [inner]
  | succ n ih =>
    intro steps first manual idx ht o h
    change Lean.Loop.forIn _ _ _ = _ at h
    rw [Lean.Loop.forIn_eq_of_monadTail] at h
    cases hx : F () (steps, first, manual, idx, ht, n + 1) with
    | error e => rw [hx] at h; cases h
    | ok x =>
      have := hF _ _ _ _ _ _ x hx
      simp only [gt_iff_lt, Nat.zero_lt_succ, ite_true, Nat.add_sub_cancel] at this
      subst this; rw [hx] at h
      simp only [inner]
      split
      · rename_i hb; simp only [hb, ite_true] at h; simp [Bind.bind, Except.bind] at h; cases h; rfl
      · rename_i hb; simp only [hb, ite_false, Bool.false_eq_true] at h; simp only [Bind.bind, Except.bind] at h
        exact ih _ _ _ _ _ _ h

/-- A `for r in l` loop in `Except` whose `ok` steps always yield `g r s`. -/
theorem forIn_okE {β : Type} (G : F64 → β → Except String (ForInStep β)) (g : F64 → β → β)
    (hG : ∀ r s x, G r s = .ok x → x = .yield (g r s)) :
    ∀ (l : List F64) (init res : β), forIn l init G = .ok res → res = l.foldl (fun s r => g r s) init := by
  intro l
  induction l with
  | nil => intro init res h; rw [List.forIn_nil] at h; simp [pure, Except.pure] at h; exact h.symm
  | cons a t ih =>
    intro init res h
    rw [List.forIn_cons] at h
    cases hx : G a init with
    | error e => rw [hx] at h; cases h
    | ok x =>
      have := hG _ _ _ hx; subst this; rw [hx] at h
      simp only [Bind.bind, Except.bind] at h
      exact ih _ _ h

theorem bind_okE {α β : Type} (m : Except String α) (k : α → Except String β) (x : β)
    (h : (m >>= k) = .ok x) : ∃ a, m = .ok a ∧ k a = .ok x := by
  cases hm : m with
  | error e => rw [hm] at h; cases h
  | ok a => rw [hm] at h; exact ⟨a, rfl, h⟩

/-- The fold step of the spec's outer loop. -/
def outerStepS (frames : Array F64) (gst : F64) (s : Array Step × Bool × F64 × Int × F64) (r : F64) :
    Array Step × Bool × F64 × Int × F64 :=
  let o := inner frames gst r FUEL s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2
  (o.1, o.2.1, o.2.2.1, o.2.2.2.1, o.2.2.2.2.1)

set_option hygiene false in
/-- Closes one FSC-proposal case of the spec loop body: split the frame part of `hx` and match it
with `stepT`. -/
macro "sched_tail" : tactic => `(tactic| (
  by_cases c4 : (frames.size == 0) = true <;> simp only [c4, ite_true, ite_false, Bool.false_eq_true] at hx ⊢
  · split at hx <;> cases hx <;> simp [*]
  · repeat' split at hx
    all_goals (cases hx)
    all_goals (try simp only [Int.sub_add_cancel] at *)
    all_goals (simp [*])))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- **Spec normal form**: whenever the spec's `simulateSteps` succeeds, its steps are `outer`'s. -/
theorem simulateSteps_ok (refs frames : Array F64) (gst : F64) (s : Array Step)
    (h : simulateSteps refs frames gst = .ok s) : s = outer frames gst refs := by
  unfold simulateSteps at h
  obtain ⟨o, ho, hk⟩ := bind_okE _ _ _ h
  have hk' : o.1 = s := by simpa [pure, Except.pure] using hk
  subst hk'
  rw [← Array.forIn_toList] at ho
  have := forIn_okE _ (fun r s => outerStepS frames gst s r) ?_ refs.toList _ o ho
  · rw [this]; unfold outer; rw [← Array.foldl_toList]; rfl
  · intro r st x hx
    obtain ⟨o2, ho2, hk2⟩ := bind_okE _ _ _ hx
    have hin := loop_innerE frames gst r _ ?_ _ _ _ _ _ _ o2 ho2
    · subst hin
      simp only [] at hk2
      split at hk2
      · cases hk2
      · simp [pure, Except.pure] at hk2; subst hk2; rfl
    · intro steps first manual idx ht fuel x hx
      clear ho2 hk2 ho h
      simp only [ft_match frames] at hx
      rcases Nat.eq_zero_or_pos fuel with hf | hf
      · subst hf
        simp only [gt_iff_lt, Nat.lt_irrefl, ite_false] at hx ⊢
        simp only [pure, Except.pure, Except.ok.injEq] at hx; exact hx.symm
      · simp only [hf, ite_true] at hx ⊢
        simp only [stepT, propose]
        simp only [Bind.bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hx
        cases first <;> simp only [ite_true, ite_false, Bool.false_eq_true] at hx ⊢
        · by_cases c1 : manual < gst <;> simp only [c1, ite_true, ite_false] at hx ⊢
          · sched_tail
          · by_cases c2 : catchupThreshold < F64.abs (manual - r) <;> simp only [c2, ite_true, ite_false] at hx ⊢
            · by_cases c3 : manual < r <;> simp only [c3, ite_true, ite_false] at hx ⊢
              · sched_tail
              · sched_tail
            · sched_tail
        · sched_tail

end OsuProofs.SpecSched
