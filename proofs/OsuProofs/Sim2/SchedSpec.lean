/-
Spec-side normal form of the total `OsuModel.Sim.simulateSteps` (Except: `Math.Clamp` on out-of-order frame
times and step-fuel exhaustion throw) as an `Option`-valued structural recursion: `s2_eo (simulateSteps ..)`
(`ok` ↦ `some`, any error ↦ `none`) equals `s2_outerO`. Builds on `OsuProofs.SpecSched` (stepT, propose, ft).
The Rust side (`sim::schedule::simulate_steps`, Sim2/Schedule.lean) is matched against `s2_outerO`.
-/
import OsuProofs.Schedule
set_option linter.unusedSimpArgs false
open OsuModel.Net OsuModel.Sim OsuProofs.SpecSched

namespace OsuProofs

/-- `Except` ↦ `Option` (forgets the error message). -/
def s2_eo {ε α : Type} : Except ε α → Option α
  | .ok v => some v
  | .error _ => none

/-- The `Math.Clamp` of one FSC step succeeds (or there are no replay frames). -/
def s2_stepOk (frames : Array F64) (gst r : F64) (s : Bool × F64 × Int × F64) : Bool :=
  let (first, manual, idx, ht) := s
  let p := propose gst r first manual
  if frames.size == 0 then true
  else
    let fs := ft frames idx
    let fe := ft frames (idx + 1)
    let (p, idx) := if fe ≤ p then (fe, idx + 1)
      else if (p < fs && ht == fs) = true then (p, idx - 1) else (p, idx)
    match F64.clamp p (ft frames idx) (ft frames (idx + 1)) with
      | .ok _ => true
      | .error _ => false

/-- The inner `while fuel > 0` loop for one reference, failing (`none`) when a step's clamp throws. -/
def s2_innerO (frames : Array F64) (gst r : F64) :
    Nat → _root_.Array Step → Bool → F64 → Int → F64 → Option St6
  | 0, steps, first, manual, idx, ht => some (steps, first, manual, idx, ht, 0)
  | n + 1, steps, first, manual, idx, ht =>
    if s2_stepOk frames gst r (first, manual, idx, ht) then
      let s := stepT frames gst r (first, manual, idx, ht)
      let steps' := steps.push { time := s.2.1, frameIndex := s.2.2.1 }
      if (s.2.2.2 == r) = true then some (steps', s.1, s.2.1, s.2.2.1, s.2.2.2, n)
      else s2_innerO frames gst r n steps' s.1 s.2.1 s.2.2.1 s.2.2.2
    else none

abbrev S2St := _root_.Array Step × Bool × F64 × Int × F64

/-- One reference: the inner loop, then the spec's `if fuel == 0 then throw`. -/
def s2_refO (frames : Array F64) (gst : F64) (s : S2St) (r : F64) : Option S2St :=
  match s2_innerO frames gst r FUEL s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2 with
  | none => none
  | some o => if o.2.2.2.2.2 == 0 then none else some (o.1, o.2.1, o.2.2.1, o.2.2.2.1, o.2.2.2.2.1)

/-- The whole `simulateSteps` as an `Option` fold. -/
def s2_outerO (frames : Array F64) (gst : F64) (refs : List F64) (s : S2St) : Option S2St :=
  match refs with
  | [] => some s
  | r :: t => match s2_refO frames gst s r with
    | none => none
    | some s' => s2_outerO frames gst t s'

theorem s2_loop_innerO (frames : Array F64) (gst r : F64)
    (F : Unit → St6 → Except String (ForInStep St6))
    (hF : ∀ (steps : _root_.Array Step) (first : Bool) (manual : F64) (idx : Int) (ht : F64) (fuel : Nat),
      s2_eo (F () (steps, first, manual, idx, ht, fuel)) =
        if fuel > 0 then
          if s2_stepOk frames gst r (first, manual, idx, ht) then
            let s := stepT frames gst r (first, manual, idx, ht)
            let steps' := steps.push { time := s.2.1, frameIndex := s.2.2.1 }
            if (s.2.2.2 == r) = true then some (.done (steps', s.1, s.2.1, s.2.2.1, s.2.2.2, fuel - 1))
            else some (.yield (steps', s.1, s.2.1, s.2.2.1, s.2.2.2, fuel - 1))
          else none
        else some (.done (steps, first, manual, idx, ht, fuel))) :
    ∀ (fuel : Nat) (steps : _root_.Array Step) (first : Bool) (manual : F64) (idx : Int) (ht : F64),
      s2_eo (forIn Lean.Loop.mk (steps, first, manual, idx, ht, fuel) F : Except String St6) =
        s2_innerO frames gst r fuel steps first manual idx ht := by
  intro fuel
  induction fuel with
  | zero =>
    intro steps first manual idx ht
    show s2_eo (Lean.Loop.forIn _ _ _) = _
    rw [Lean.Loop.forIn_eq_of_monadTail]
    have h := hF steps first manual idx ht 0
    simp only [gt_iff_lt, Nat.lt_irrefl, ite_false] at h
    cases hx : F () (steps, first, manual, idx, ht, 0) with
    | error e => rw [hx] at h; cases h
    | ok x => rw [hx] at h; cases h; simp [s2_eo, s2_innerO, Bind.bind, Except.bind, pure, Except.pure]
  | succ n ih =>
    intro steps first manual idx ht
    show s2_eo (Lean.Loop.forIn _ _ _) = _
    rw [Lean.Loop.forIn_eq_of_monadTail]
    have h := hF steps first manual idx ht (n + 1)
    simp only [gt_iff_lt, Nat.zero_lt_succ, ite_true, Nat.add_sub_cancel] at h
    simp only [s2_innerO]
    cases hx : F () (steps, first, manual, idx, ht, n + 1) with
    | error e =>
      rw [hx] at h
      by_cases hok : s2_stepOk frames gst r (first, manual, idx, ht) = true
      · simp only [hok, ite_true] at h; split at h <;> cases h
      · simp only [hok] at h ⊢; simp [s2_eo, Bind.bind, Except.bind]
    | ok x =>
      rw [hx] at h
      by_cases hok : s2_stepOk frames gst r (first, manual, idx, ht) = true
      · simp only [hok, ite_true] at h ⊢
        split
        · rename_i hb; simp only [hb, ite_true] at h; cases h; simp [s2_eo, Bind.bind, Except.bind, pure, Except.pure]
        · rename_i hb; simp only [hb, ite_false, Bool.false_eq_true] at h; cases h
          simp only [Bind.bind, Except.bind]
          exact ih _ _ _ _ _
      · simp only [hok, Bool.false_eq_true, ite_false] at h; cases h

/-- A `for r in l` loop in `Except` whose steps are an `Option`-valued yield-only fold. -/
theorem s2_forIn_optE {β : Type} (G : F64 → β → Except String (ForInStep β)) (g : β → F64 → Option β)
    (hG : ∀ r s, s2_eo (G r s) = (g s r).map ForInStep.yield) :
    ∀ (l : List F64) (init : β), s2_eo (forIn l init G) = l.foldlM g init := by
  intro l
  induction l with
  | nil => intro init; simp [s2_eo, pure, Except.pure]
  | cons a t ih =>
    intro init
    rw [List.forIn_cons]
    have h := hG a init
    cases hx : G a init with
    | error e =>
      rw [hx] at h
      cases hg : g init a with
      | none => simp [hg, s2_eo, Bind.bind, Except.bind]
      | some v => rw [hg] at h; cases h
    | ok x =>
      rw [hx] at h
      cases hg : g init a with
      | none => rw [hg] at h; cases h
      | some v =>
        rw [hg] at h; simp [s2_eo] at h; subst h
        simp only [Bind.bind, Except.bind, List.foldlM_cons, hg]
        exact ih v

theorem s2_outerO_foldlM (frames : Array F64) (gst : F64) :
    ∀ (refs : List F64) (s : S2St), refs.foldlM (s2_refO frames gst) s = s2_outerO frames gst refs s := by
  intro refs
  induction refs with
  | nil => intro s; rfl
  | cons r t ih =>
    intro s
    simp only [List.foldlM_cons, s2_outerO]
    cases s2_refO frames gst s r with
    | none => rfl
    | some s' => exact ih s'


theorem s2_eo_bind {α β : Type} (m : Except String α) (k : α → Except String β) :
    s2_eo (m >>= k) = (s2_eo m).bind (fun a => s2_eo (k a)) := by
  cases m <;> rfl

set_option hygiene false in
macro "s2_tail" : tactic => `(tactic| (
  simp only [s2_stepOk, stepT, propose, ite_true, ite_false, Bool.false_eq_true, *]
  by_cases c4 : (frames.size == 0) = true <;> simp only [c4, ite_true, ite_false, Bool.false_eq_true]
  · split <;> simp_all [s2_eo, pure, Except.pure]
  · repeat' split
    all_goals simp_all [s2_eo, pure, Except.pure, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem s2_simulateSteps_eo (refs frames : Array F64) (gst : F64) :
    s2_eo (simulateSteps refs frames gst) =
      (s2_outerO frames gst refs.toList (#[], true, 0, -1, F64.negInf)).map (·.1) := by
  unfold simulateSteps
  dsimp only
  rw [s2_eo_bind, ← Array.forIn_toList, s2_forIn_optE _ (s2_refO frames gst) ?hG, s2_outerO_foldlM]
  · cases s2_outerO frames gst refs.toList (#[], true, 0, -1, F64.negInf) <;> rfl
  case hG =>
    intro r st
    rw [s2_eo_bind, s2_loop_innerO frames gst r _ ?hF]
    · simp only [s2_refO, FUEL]
      cases s2_innerO frames gst r 100000000 st.1 st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2 with
      | none => rfl
      | some o => 
        simp only [Option.bind_some]
        by_cases h0 : o.2.2.2.2.2 = 0
        · simp [h0, s2_eo, FUEL, throw, throwThe, MonadExceptOf.throw]
        · simp [h0, s2_eo, FUEL, pure, Except.pure]
    case hF => 
      intro steps first manual idx ht fuel
      simp only [ft_match frames]
      rcases Nat.eq_zero_or_pos fuel with hf | hf
      · subst hf; simp [s2_eo, pure, Except.pure]
      · simp only [hf, ite_true]
        cases first <;> simp only [ite_true, ite_false, Bool.false_eq_true]
        · by_cases c1 : manual < gst <;> simp only [c1, ite_true, ite_false]
          · s2_tail
          · by_cases c2 : catchupThreshold < F64.abs (manual - r) <;> simp only [c2, ite_true, ite_false]
            · by_cases c3 : manual < r <;> simp only [c3, ite_true, ite_false]
              · s2_tail
              · s2_tail
            · s2_tail
        · s2_tail
end OsuProofs
