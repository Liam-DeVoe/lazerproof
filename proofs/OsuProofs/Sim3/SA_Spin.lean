/-
sim3a (D37): spinner leaves of `sim::step` (Rust) refine `OsuModel.Sim.Sim` (Step.lean, "Spinners"):
`total_rotation`, `spinner_progress`, `report_delta` (+ its fuel loop).
Side conditions are the integer ranges of the Rust counters (`completed_spins : u64` ↦ `Nat`).
-/
import OsuProofs.Sim.Hit
import OsuProofs.Sim2.Geometry
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

@[simp] theorem s3a_ostateS_completedSpins (o : sim.state.OState) :
    (abs o : OsuModel.Sim.OState).completedSpins = o.completed_spins.val := rfl
@[simp] theorem s3a_ostateS_currentSpinMax (o : sim.state.OState) :
    (abs o : OsuModel.Sim.OState).currentSpinMax = o.current_spin_max := rfl

theorem sim.step.total_rotation_refines (os : sim.state.OState) (h : os.completed_spins.val * 360 < 2 ^ 63) :
    sim.step.total_rotation os = ok (OsuModel.Sim.Sim.totalRotation (abs os)) := by
  have hc : (UScalar.hcast .I64 os.completed_spins).val = (os.completed_spins.val : Int) := by
    rw [UScalar.hcast_val_eq]; simp; rw [Int.bmod_eq_of_le] <;> omega
  unfold sim.step.total_rotation
  simp only [lift, bind_ok]
  have hm : ∃ z : I64, 360#i64 * UScalar.hcast .I64 os.completed_spins = ok z ∧ z.val = 360 * (os.completed_spins.val : Int) := by
    have hb : (360#i64 : I64).val * (UScalar.hcast .I64 os.completed_spins).val ≤ I64.max := by
      rw [hc]; simp [I64.max, I64.numBits]; omega
    have hb0 : I64.min ≤ (360#i64 : I64).val * (UScalar.hcast .I64 os.completed_spins).val := by
      rw [hc]; simp [I64.min, I64.numBits]; omega
    have := I64.mul_spec (x := 360#i64) (y := UScalar.hcast .I64 os.completed_spins)
    obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (this hb0 hb)
    exact ⟨z, hz, by rw [hzv, hc]; simp⟩
  obtain ⟨z, hz, hzv⟩ := hm
  simp [hz, float.F32.from_i64, float.F32.add, OsuModel.Sim.Sim.totalRotation, hzv]

@[simp] theorem s3a_step_F32_360 : sim.step.F32_360 = ok (360 : F32) := by
  simp [sim.step.F32_360]; decide +kernel

theorem sim.step.spinner_progress_refines (sp : sim.playable.SpinnerData) (os : sim.state.OState)
    (h : os.completed_spins.val * 360 < 2 ^ 63) :
    sim.step.spinner_progress sp os = ok (OsuModel.Sim.Sim.spinnerProgress (abs sp) (abs os)) := by
  unfold sim.step.spinner_progress OsuModel.Sim.Sim.spinnerProgress
  have hsr : (abs sp : OsuModel.Sim.SpinnerData).spinsRequired = sp.spins_required.val := rfl
  by_cases hz : sp.spins_required = 0#i64
  · have : sp.spins_required.val = 0 := by simp [hz]
    simp [hz, hsr, this]
  · have : sp.spins_required.val ≠ 0 := fun e => hz (IScalar.eq_of_val_eq (by simpa using e))
    simp only [hz, if_false, sim.step.total_rotation_refines os h, bind_ok, s3a_step_F32_360, float.F32.div,
      float.F32.from_i64, sim_basic_F32_0, sim_basic_F32_1, sim.netx.f32_clamp_or_refines, simClampOrF, F32.clamp, hsr]
    simp [this]
    rw [if_neg (by decide +kernel)]
    generalize OsuModel.Sim.Sim.totalRotation (abs os) / 360 / F32.ofInt ↑sp.spins_required = q
    by_cases h1 : q < 0 <;> by_cases h2 : 1 < q <;> simp [h1, h2]

/-! ## reportDelta: the spin-completion loop as a structural recursion on the fuel -/
/-- `(acc, curMax, spins, fuel left)` after the `ReportDelta` while loop with total `ta`; `none` = `Math.Sign(NaN)` threw -/
def s3aRD (ta : F32) : Nat → F32 → F32 → Nat → Option (F32 × F32 × Nat × Nat)
  | 0, acc, cm, k => some (acc, cm, k, 0)
  | n + 1, acc, cm, k =>
    if (360 : F32) ≤ cm then
      match F32.sign (ta - acc) with
      | .ok v => s3aRD ta n (acc + F32.ofInt (v.toInt * 360)) (F32.abs (ta - (acc + F32.ofInt (v.toInt * 360)))) (k + 1)
      | .error _ => none
    else some (acc, cm, k, n + 1)

/-- relation of the Rust loop result `(r, acc, curMax, spins, lastReportTime)` to `s3aRD` -/
def s3aRDRel (_lrt t : F64) : Option (F32 × F32 × Nat × Nat) →
    (core.result.Result Unit sim.err.SimErr) × F32 × F32 × U64 × F64 → Prop
  | none, y => ∃ e, y.1 = .Err e
  | some (a, c, k, f), y => y.2.1 = a ∧ y.2.2.1 = c ∧ y.2.2.2.1.val = k ∧
      (if f = 0 ∧ (360 : F32) ≤ c then ∃ e, y.1 = .Err e else y.1 = .Ok () ∧ y.2.2.2.2 = t)

theorem s3a_cast_i32I (v : Int32) : (IScalar.cast .I64 (i32I v)).val = v.toInt := by
  have hv : ((i32I v).val : Int) = v.toInt := by rw [← i32S_toInt, i32S_i32I]
  simp [IScalar.cast_val_eq, hv]

theorem s3a_sign_small (x : F32) (v : Int32) (h : F32.sign x = .ok v) : -1 ≤ v.toInt ∧ v.toInt ≤ 1 := by
  unfold F32.sign at h
  split at h
  · cases h; decide
  · split at h
    · cases h; decide
    · split at h
      · cases h; decide
      · cases h

theorem s3a_rd_loop (ta : F32) (lrt t : F64) :
    ∀ n (fuel : U32) (acc cm : F32) (sp : U64), fuel.val = n → sp.val + n ≤ U64.max →
      ∃ y, sim.step.report_delta_loop ta acc cm sp lrt t fuel = ok y ∧ s3aRDRel lrt t (s3aRD ta n acc cm sp.val) y := by
  intro n
  induction n with
  | zero =>
    intro fuel acc cm sp hf _
    have hf0 : fuel = 0#u32 := UScalar.eq_of_val_eq (by simp [hf])
    subst hf0
    unfold sim.step.report_delta_loop
    rw [loop_unfold]
    by_cases hc : (360 : F32) ≤ cm
    · refine ⟨_, by simp [sim.step.report_delta_loop.body, s3a_step_F32_360, float.F32.le, hc]; rfl, ?_⟩
      simp [s3aRD, s3aRDRel, hc]
    · refine ⟨_, by simp [sim.step.report_delta_loop.body, s3a_step_F32_360, float.F32.le, hc]; rfl, ?_⟩
      simp [s3aRD, s3aRDRel, hc]
  | succ n ih =>
    intro fuel acc cm sp hf hsp
    have hpos : fuel > 0#u32 := by scalar_tac
    obtain ⟨f1, hf1, hf1v⟩ : ∃ f1 : U32, fuel - 1#u32 = ok f1 ∧ f1.val = n := by
      obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (U32.sub_spec (x := fuel) (y := 1#u32) (by scalar_tac))
      exact ⟨z, hz, by simp at hzv; omega⟩
    obtain ⟨sp1, hsp1, hsp1v⟩ : ∃ s1 : U64, sp + 1#u64 = ok s1 ∧ s1.val = sp.val + 1 := by
      obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (U64.add_spec (x := sp) (y := 1#u64) (by scalar_tac))
      exact ⟨z, hz, by simp at hzv; omega⟩
    unfold sim.step.report_delta_loop
    rw [loop_unfold]
    by_cases hc : (360 : F32) ≤ cm
    · cases hsg : F32.sign (ta - acc) with
      | error e =>
        refine ⟨_, by simp [sim.step.report_delta_loop.body, s3a_step_F32_360, float.F32.le, hc, hpos, hf1,
          float.F32.sub, net.mathops.f32_sign_refines, hsg, exceptI]; rfl, ?_⟩
        simp [s3aRD, s3aRDRel, hc, hsg]
      | ok v =>
        have hsm := s3a_sign_small _ _ hsg
        have hcv := s3a_cast_i32I v
        obtain ⟨m, hm, hmv⟩ : ∃ m : I64, IScalar.cast .I64 (i32I v) * 360#i64 = ok m ∧ m.val = v.toInt * 360 := by
          obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (I64.mul_spec (x := IScalar.cast .I64 (i32I v)) (y := 360#i64)
            (by rw [hcv]; simp [I64.min, I64.numBits]; omega) (by rw [hcv]; simp [I64.max, I64.numBits]; omega))
          exact ⟨z, hz, by rw [hzv, hcv]; simp⟩
        obtain ⟨y, hy, hyr⟩ := ih f1 (acc + F32.ofInt (v.toInt * 360)) (F32.abs (ta - (acc + F32.ofInt (v.toInt * 360)))) sp1
          hf1v (by omega)
        have hb : sim.step.report_delta_loop.body ta lrt t acc cm sp fuel = ok (.cont (acc + F32.ofInt (v.toInt * 360),
            F32.abs (ta - (acc + F32.ofInt (v.toInt * 360))), sp1, f1)) := by
          simp only [sim.step.report_delta_loop.body, s3a_step_F32_360, float.F32.le, hc, decide_true, if_true, hpos,
            hf1, bind_ok, float.F32.sub, net.mathops.f32_sign_refines, hsg, exceptI, lift, hsp1, hm,
            float.F32.from_i64, float.F32.add, float.F32.abs, hmv]
        refine ⟨y, ?_, ?_⟩
        · dsimp only; rw [hb]; simp only [bind_ok]
          unfold sim.step.report_delta_loop at hy
          exact hy
        · simp only [s3aRD, hc, if_true, hsg]
          rw [hsp1v] at hyr; exact hyr
    · refine ⟨_, by simp [sim.step.report_delta_loop.body, s3a_step_F32_360, float.F32.le, hc]; rfl, ?_⟩
      simp [s3aRD, s3aRDRel, hc]

/-- one completed spin of the spec loop (the two record updates of `ReportDelta`'s loop body) -/
def s3aSpinStep (os : OsuModel.Sim.OState) (v : Int32) : OsuModel.Sim.OState :=
  { os with accumulatedAtLastCompletion := os.accumulatedAtLastCompletion + F32.ofInt (v.toInt * 360),
            completedSpins := os.completedSpins + 1,
            currentSpinMax := F32.abs (os.totalAccumulated - (os.accumulatedAtLastCompletion + F32.ofInt (v.toInt * 360))) }

theorem s3a_rd_spec (ta : F32)
    (F : Unit → OsuModel.Sim.OState × Nat → Except String (ForInStep (OsuModel.Sim.OState × Nat)))
    (hF : ∀ os n, os.totalAccumulated = ta →
      ((¬ ((360 : F32) ≤ os.currentSpinMax ∧ n > 0)) → F () (os, n) = .ok (.done (os, n))) ∧
      ((360 : F32) ≤ os.currentSpinMax → n > 0 → ∀ v, F32.sign (ta - os.accumulatedAtLastCompletion) = .ok v →
        F () (os, n) = .ok (.yield (s3aSpinStep os v, n - 1))) ∧
      ((360 : F32) ≤ os.currentSpinMax → n > 0 → ∀ e, F32.sign (ta - os.accumulatedAtLastCompletion) = .error e →
        ∃ m, F () (os, n) = .error m)) :
    ∀ n (os : OsuModel.Sim.OState), os.totalAccumulated = ta →
      match s3aRD ta n os.accumulatedAtLastCompletion os.currentSpinMax os.completedSpins with
      | none => ∃ m, forIn (m := Except String) Lean.Loop.mk (os, n) F = .error m
      | some (a, c, k, f) => forIn (m := Except String) Lean.Loop.mk (os, n) F =
          .ok ({ os with accumulatedAtLastCompletion := a, currentSpinMax := c, completedSpins := k }, f) := by
  intro n
  induction n with
  | zero =>
    intro os hta
    simp only [s3aRD]
    show Lean.Loop.forIn _ _ _ = _
    rw [Lean.Loop.forIn_eq_of_monadTail, (hF os 0 hta).1 (by omega)]
    rfl
  | succ n ih =>
    intro os hta
    by_cases hc : (360 : F32) ≤ os.currentSpinMax
    · obtain ⟨-, hy, he⟩ := hF os (n + 1) hta
      cases hsg : F32.sign (ta - os.accumulatedAtLastCompletion) with
      | error e =>
        obtain ⟨m, hm⟩ := he hc (by omega) e hsg
        simp only [s3aRD, hc, if_true, hsg]
        exact ⟨m, by show Lean.Loop.forIn _ _ _ = _; rw [Lean.Loop.forIn_eq_of_monadTail, hm]; rfl⟩
      | ok v =>
        have h1 := ih (s3aSpinStep os v) hta
        have e : forIn (m := Except String) Lean.Loop.mk (os, n + 1) F =
            forIn (m := Except String) Lean.Loop.mk (s3aSpinStep os v, n) F := by
          show Lean.Loop.forIn _ _ _ = _
          rw [Lean.Loop.forIn_eq_of_monadTail, hy hc (by omega) v hsg]
          rfl
        simp only [s3aRD, hc, if_true, hsg]
        rw [e]
        have e2 : (s3aSpinStep os v).accumulatedAtLastCompletion = os.accumulatedAtLastCompletion + F32.ofInt (v.toInt * 360) := rfl
        have e3 : (s3aSpinStep os v).currentSpinMax = F32.abs (ta - (os.accumulatedAtLastCompletion + F32.ofInt (v.toInt * 360))) := by
          rw [← hta]; rfl
        have e4 : (s3aSpinStep os v).completedSpins = os.completedSpins + 1 := rfl
        rw [e2, e3, e4] at h1
        exact h1
    · simp only [s3aRD, hc, if_false]
      show Lean.Loop.forIn _ _ _ = _
      rw [Lean.Loop.forIn_eq_of_monadTail, (hF os (n + 1) hta).1 (fun h => hc h.1)]
      rfl

theorem s3a_rd_some (ta : F32) {F : Unit → OsuModel.Sim.OState × Nat → Except String (ForInStep (OsuModel.Sim.OState × Nat))}
    (hF : ∀ os n, os.totalAccumulated = ta →
      ((¬ ((360 : F32) ≤ os.currentSpinMax ∧ n > 0)) → F () (os, n) = .ok (.done (os, n))) ∧
      ((360 : F32) ≤ os.currentSpinMax → n > 0 → ∀ v, F32.sign (ta - os.accumulatedAtLastCompletion) = .ok v →
        F () (os, n) = .ok (.yield (s3aSpinStep os v, n - 1))) ∧
      ((360 : F32) ≤ os.currentSpinMax → n > 0 → ∀ e, F32.sign (ta - os.accumulatedAtLastCompletion) = .error e →
        ∃ m, F () (os, n) = .error m))
    (n : Nat) (os : OsuModel.Sim.OState) (hta : os.totalAccumulated = ta) (a c : F32) (k f : Nat)
    (hs : s3aRD ta n os.accumulatedAtLastCompletion os.currentSpinMax os.completedSpins = some (a, c, k, f)) :
    forIn (m := Except String) Lean.Loop.mk (os, n) F =
      .ok ({ os with accumulatedAtLastCompletion := a, currentSpinMax := c, completedSpins := k }, f) := by
  have := s3a_rd_spec ta F hF n os hta
  rw [hs] at this; exact this

theorem s3a_rd_none (ta : F32) {F : Unit → OsuModel.Sim.OState × Nat → Except String (ForInStep (OsuModel.Sim.OState × Nat))}
    (hF : ∀ os n, os.totalAccumulated = ta →
      ((¬ ((360 : F32) ≤ os.currentSpinMax ∧ n > 0)) → F () (os, n) = .ok (.done (os, n))) ∧
      ((360 : F32) ≤ os.currentSpinMax → n > 0 → ∀ v, F32.sign (ta - os.accumulatedAtLastCompletion) = .ok v →
        F () (os, n) = .ok (.yield (s3aSpinStep os v, n - 1))) ∧
      ((360 : F32) ≤ os.currentSpinMax → n > 0 → ∀ e, F32.sign (ta - os.accumulatedAtLastCompletion) = .error e →
        ∃ m, F () (os, n) = .error m))
    (n : Nat) (os : OsuModel.Sim.OState) (hta : os.totalAccumulated = ta)
    (hs : s3aRD ta n os.accumulatedAtLastCompletion os.currentSpinMax os.completedSpins = none) :
    ∃ m, forIn (m := Except String) Lean.Loop.mk (os, n) F = .error m := by
  have := s3a_rd_spec ta F hF n os hta
  rw [hs] at this; exact this

/-- the spec object state after a forward `ReportDelta` -/
def s3aFwdO (O : OsuModel.Sim.OState) (delta a c : F32) (k : Nat) (t : F64) : OsuModel.Sim.OState :=
  { O with totalAccumulated := O.totalAccumulated + delta, accumulatedAtLastCompletion := a, currentSpinMax := c,
           completedSpins := k, lastReportTime := t }

theorem s3a_bind_loop_none {β : Type} (ta : F32)
    {F : Unit → OsuModel.Sim.OState × Nat → Except String (ForInStep (OsuModel.Sim.OState × Nat))}
    (hF : ∀ os n, os.totalAccumulated = ta →
      ((¬ ((360 : F32) ≤ os.currentSpinMax ∧ n > 0)) → F () (os, n) = .ok (.done (os, n))) ∧
      ((360 : F32) ≤ os.currentSpinMax → n > 0 → ∀ v, F32.sign (ta - os.accumulatedAtLastCompletion) = .ok v →
        F () (os, n) = .ok (.yield (s3aSpinStep os v, n - 1))) ∧
      ((360 : F32) ≤ os.currentSpinMax → n > 0 → ∀ e, F32.sign (ta - os.accumulatedAtLastCompletion) = .error e →
        ∃ m, F () (os, n) = .error m))
    (n : Nat) (os : OsuModel.Sim.OState) (hta : os.totalAccumulated = ta)
    (hs : s3aRD ta n os.accumulatedAtLastCompletion os.currentSpinMax os.completedSpins = none)
    (K : OsuModel.Sim.OState × Nat → Except String β) :
    ∃ m, (forIn (m := Except String) Lean.Loop.mk (os, n) F >>= K) = .error m := by
  obtain ⟨m, hm⟩ := s3a_rd_none ta hF n os hta hs
  exact ⟨m, by rw [hm]; rfl⟩

theorem s3a_bind_loop_some {β : Type} (ta : F32)
    {F : Unit → OsuModel.Sim.OState × Nat → Except String (ForInStep (OsuModel.Sim.OState × Nat))}
    (hF : ∀ os n, os.totalAccumulated = ta →
      ((¬ ((360 : F32) ≤ os.currentSpinMax ∧ n > 0)) → F () (os, n) = .ok (.done (os, n))) ∧
      ((360 : F32) ≤ os.currentSpinMax → n > 0 → ∀ v, F32.sign (ta - os.accumulatedAtLastCompletion) = .ok v →
        F () (os, n) = .ok (.yield (s3aSpinStep os v, n - 1))) ∧
      ((360 : F32) ≤ os.currentSpinMax → n > 0 → ∀ e, F32.sign (ta - os.accumulatedAtLastCompletion) = .error e →
        ∃ m, F () (os, n) = .error m))
    (n : Nat) (os : OsuModel.Sim.OState) (hta : os.totalAccumulated = ta) (a c : F32) (k f : Nat)
    (hs : s3aRD ta n os.accumulatedAtLastCompletion os.currentSpinMax os.completedSpins = some (a, c, k, f))
    (K : OsuModel.Sim.OState × Nat → Except String β) :
    (forIn (m := Except String) Lean.Loop.mk (os, n) F >>= K) =
      K ({ os with accumulatedAtLastCompletion := a, currentSpinMax := c, completedSpins := k }, f) := by
  rw [s3a_rd_some ta hF n os hta a c k f hs]; rfl

/-- the object state entering the `ReportDelta` loop -/
def s3aO1 (O : OsuModel.Sim.OState) (delta : F32) : OsuModel.Sim.OState :=
  { O with totalAccumulated := O.totalAccumulated + delta,
           currentSpinMax := F32.max O.currentSpinMax (F32.abs (O.totalAccumulated + delta - O.accumulatedAtLastCompletion)) }

/-- the forward branch of `ReportDelta` on the spec side, by the loop's fuel recursion -/
theorem s3a_reportDelta_fwd (O : OsuModel.Sim.OState) (t : F64) (delta : F32) (hz : (delta == 0) = false)
    (hl : O.lastReportTime ≤ t) :
    match s3aRD (O.totalAccumulated + delta) 1000000 O.accumulatedAtLastCompletion
        (F32.max O.currentSpinMax (F32.abs (O.totalAccumulated + delta - O.accumulatedAtLastCompletion)))
        O.completedSpins with
    | none => ∃ m, OsuModel.Sim.Sim.reportDelta O t delta = .error m
    | some (a, c, k, f) =>
      if f = 0 ∧ (360 : F32) ≤ c then ∃ m, OsuModel.Sim.Sim.reportDelta O t delta = .error m
      else OsuModel.Sim.Sim.reportDelta O t delta = .ok (s3aFwdO O delta a c k t) := by
  simp only [OsuModel.Sim.Sim.reportDelta, hz, Bool.false_eq_true, if_false, hl, decide_true, if_true]
  rcases hs : s3aRD (O.totalAccumulated + delta) 1000000 O.accumulatedAtLastCompletion
      (F32.max O.currentSpinMax (F32.abs (O.totalAccumulated + delta - O.accumulatedAtLastCompletion)))
      O.completedSpins with _ | ⟨a, c, k, f⟩
  · simp only
    refine s3a_bind_loop_none (O.totalAccumulated + delta) ?hF 1000000 (s3aO1 O delta) rfl hs _
    intro os n hta
    refine ⟨fun h => ?_, fun hc hn v hv => ?_, fun hc hn e he => ?_⟩
    · rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact h)]; rfl
    · rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hc, hn⟩)]
      have hv' : (os.totalAccumulated - os.accumulatedAtLastCompletion).sign = .ok v := by rw [hta]; exact hv
      simp only [hv']
      rfl
    · rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hc, hn⟩)]
      have he' : (os.totalAccumulated - os.accumulatedAtLastCompletion).sign = .error e := by rw [hta]; exact he
      simp only [he']
      exact ⟨_, rfl⟩
  · simp only
    by_cases hfc : f = 0 ∧ (360 : F32) ≤ c
    · rw [if_pos hfc]
      suffices h : (do
          let __s ← forIn (m := Except String) Lean.Loop.mk (s3aO1 O delta, 1000000) _
          _) = Except.error "internal: ReportDelta fuel exhausted" by exact ⟨_, h⟩
      refine Eq.trans (s3a_bind_loop_some (O.totalAccumulated + delta) ?hF3 1000000 (s3aO1 O delta) rfl a c k f hs _) ?_
      case hF3 =>
        intro os n hta
        refine ⟨fun h => ?_, fun hc hn v hv => ?_, fun hc hn e he => ?_⟩
        · rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact h)]; rfl
        · rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hc, hn⟩)]
          have hv' : (os.totalAccumulated - os.accumulatedAtLastCompletion).sign = .ok v := by rw [hta]; exact hv
          simp only [hv']
          rfl
        · rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hc, hn⟩)]
          have he' : (os.totalAccumulated - os.accumulatedAtLastCompletion).sign = .error e := by rw [hta]; exact he
          simp only [he']
          exact ⟨_, rfl⟩
      have : (f == 0 && decide ((360 : F32) ≤ c)) = true := by simp [hfc.1, hfc.2]
      simp only [this, if_true]
      rfl
    · rw [if_neg hfc]
      refine Eq.trans (s3a_bind_loop_some (O.totalAccumulated + delta) ?hF3 1000000 (s3aO1 O delta) rfl a c k f hs _) ?_
      case hF3 =>
        intro os n hta
        refine ⟨fun h => ?_, fun hc hn v hv => ?_, fun hc hn e he => ?_⟩
        · rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact h)]; rfl
        · rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hc, hn⟩)]
          have hv' : (os.totalAccumulated - os.accumulatedAtLastCompletion).sign = .ok v := by rw [hta]; exact hv
          simp only [hv']
          rfl
        · rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hc, hn⟩)]
          have he' : (os.totalAccumulated - os.accumulatedAtLastCompletion).sign = .error e := by rw [hta]; exact he
          simp only [he']
          exact ⟨_, rfl⟩
      have : (f == 0 && decide ((360 : F32) ≤ c)) = false := by
        by_cases h0 : f = 0 <;> simp_all
      simp only [this, Bool.false_eq_true, if_false]
      rfl

/-- the rewind branch of `ReportDelta` (Rust state) -/
def s3aRDBack (os : sim.state.OState) (t : F64) (delta : F32) : sim.state.OState :=
  { os with total_accumulated := os.total_accumulated + delta,
            current_spin_max := F32.abs (os.total_accumulated + delta - os.accumulated_at_last_completion),
            last_report_time := t }

/-- `Result<(), SimErr>` + new object state vs the spec `Except String OState` -/
def s3aOR (spec : Except String OsuModel.Sim.OState) (r : core.result.Result Unit sim.err.SimErr) (os : sim.state.OState) : Prop :=
  match r with
  | .Ok _ => spec = .ok (ostateS os)
  | .Err _ => ∃ m, spec = .error m

theorem sim.step.report_delta_refines (os : sim.state.OState) (t : F64) (delta : F32)
    (hsp : os.completed_spins.val + 1000000 ≤ U64.max) :
    ∃ r os', sim.step.report_delta os t delta = ok (r, os') ∧
      (∃ (ta acc cm : F32) (sp : U64) (lrt : F64),
        os' = { os with total_accumulated := ta, accumulated_at_last_completion := acc, current_spin_max := cm, completed_spins := sp, last_report_time := lrt }) ∧
      s3aOR (OsuModel.Sim.Sim.reportDelta (abs os) t delta) r os' := by
  unfold sim.step.report_delta
  by_cases hz : (delta == 0) = true
  · refine ⟨.Ok (), os, by simp [float.F32.eq, sim_basic_F32_0, hz], ⟨_, _, _, _, _, rfl⟩, ?_⟩
    simp [s3aOR, OsuModel.Sim.Sim.reportDelta, hz]; rfl
  have hz' : (delta == 0) = false := by simpa using hz
  by_cases hl : os.last_report_time ≤ t
  · obtain ⟨y, hy, hrel⟩ := s3a_rd_loop (os.total_accumulated + delta) os.last_report_time t 1000000 1000000#u32
      os.accumulated_at_last_completion (F32.max os.current_spin_max (F32.abs (os.total_accumulated + delta - os.accumulated_at_last_completion)))
      os.completed_spins rfl hsp
    refine ⟨y.1, { os with total_accumulated := os.total_accumulated + delta, accumulated_at_last_completion := y.2.1, current_spin_max := y.2.2.1, completed_spins := y.2.2.2.1, last_report_time := y.2.2.2.2 }, ?_, ⟨_, _, _, _, _, rfl⟩, ?_⟩
    · simp only [float.F32.eq, sim_basic_F32_0, hz', bind_ok, Bool.false_eq_true, if_false, float.F32.add, float.F64.le, hl,
        decide_true, if_true, float.F32.sub, float.F32.abs, sim.netx.f32_max_refines, hy]
      rfl
    · have hl' : (abs os : OsuModel.Sim.OState).lastReportTime ≤ t := hl
      have hf := s3a_reportDelta_fwd (abs os) t delta hz' hl'
      have e1 : (abs os : OsuModel.Sim.OState).totalAccumulated = os.total_accumulated := rfl
      have e2 : (abs os : OsuModel.Sim.OState).accumulatedAtLastCompletion = os.accumulated_at_last_completion := rfl
      have e3 : (abs os : OsuModel.Sim.OState).currentSpinMax = os.current_spin_max := rfl
      have e4 : (abs os : OsuModel.Sim.OState).completedSpins = os.completed_spins.val := rfl
      rw [e1, e2, e3, e4] at hf
      revert hf hrel
      rcases s3aRD (os.total_accumulated + delta) 1000000 os.accumulated_at_last_completion
        (F32.max os.current_spin_max (F32.abs (os.total_accumulated + delta - os.accumulated_at_last_completion)))
        os.completed_spins.val with _ | ⟨a, c, k, f⟩
      · intro hrel hf
        obtain ⟨e, he⟩ := hrel
        simp only [s3aOR, he]; exact hf
      · intro hrel hf
        obtain ⟨h1, h2, h3, h4⟩ := hrel
        simp only at hf
        by_cases hfc : f = 0 ∧ (360 : F32) ≤ c
        · rw [if_pos hfc] at hf h4; obtain ⟨e, he⟩ := h4
          simp only [s3aOR, he]; exact hf
        · rw [if_neg hfc] at hf h4; obtain ⟨h5, h6⟩ := h4
          simp only [s3aOR, h5, hf]
          congr 1
          unfold s3aFwdO
          rw [← h1, ← h2, ← h3, ← h6]
          rfl
  · refine ⟨.Ok (), s3aRDBack os t delta, ?_, ⟨_, os.accumulated_at_last_completion, _, os.completed_spins, _, rfl⟩, ?_⟩
    · simp [float.F32.eq, sim_basic_F32_0, hz', float.F64.le, hl, float.F32.add, float.F32.sub, float.F32.abs]; rfl
    have hl' : ¬ (abs os : OsuModel.Sim.OState).lastReportTime ≤ t := hl
    simp only [s3aOR, OsuModel.Sim.Sim.reportDelta, hz', Bool.false_eq_true, if_false, hl']
    rfl

end OsuProofs
