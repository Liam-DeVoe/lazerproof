-- (was `import OsuProofs.Manual`: a cycle, Manual imports PathApprox)
import OsuProofs.Generated.Funs
import OsuProofs.Prims
import OsuProofs.HitWindows
import OsuProofs.Slider
import OsuProofs.Axioms
import OsuProofs.Loops
import OsuProofs.Repr
import OsuProofs.Spec.FloatFacts
import OsuProofs.Net.OsuTK
import OsuProofs.Net.Basic
import OsuProofs.Net.MathOps
import OsuProofs.Net.SysMisc
import OsuProofs.Net.FrameworkA
import OsuProofs.Net.Random
import OsuProofs.Beatmap.Vector2
import OsuProofs.Net.Parse
import OsuProofs.Net.Parse2
import OsuProofs.Net.Decimal
import OsuProofs.Net.Decimal2
import OsuProofs.Net.Decimal3
import OsuProofs.Net.FrameworkB
import OsuProofs.SpecLoops
import OsuProofs.LoopsR
import OsuProofs.Beatmap.CharTable
import OsuProofs.Beatmap.DotNet
import OsuProofs.Beatmap.ControlPoints
import OsuProofs.Net.Decimal4
import OsuProofs.Net.Decimal5
import OsuProofs.Net.Decimal6
import OsuProofs.Net.Decimal7
import OsuProofs.Net.Decimal8
import OsuProofs.Net.Decimal9
import OsuProofs.Net.DecimalValid
import OsuProofs.Net.FrameworkC
import OsuProofs.Net.OsuTK2
import OsuProofs.Beatmap.DotNetStr
import OsuProofs.Beatmap.Names
import OsuProofs.Beatmap.Text
import OsuProofs.Generated.SimFuns  -- sim slice: sim+replay translation (shares net/beatmap items with Generated.Funs)
import OsuModel.Sim.Step  -- sim slice: spec closure of the sim (Step, State, Scoring, Mods, ...)
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

/-- `n` iterations from index `i` of an index-dependent `Id`-loop body with early exit. -/
def iterIdx {β : Type} (f : Nat → β → Id (ForInStep β)) : Nat → Nat → β → β
  | _, 0, b => b
  | i, n+1, b => match (f i b : ForInStep β) with
    | .done c => c
    | .yield c => iterIdx f (i+1) n c

theorem iterIdx_zero {β} (f : Nat → β → Id (ForInStep β)) (i : Nat) (b : β) : iterIdx f i 0 b = b := rfl
theorem iterIdx_succ {β} (f : Nat → β → Id (ForInStep β)) (i n : Nat) (b : β) :
    iterIdx f i (n+1) b = match (f i b : ForInStep β) with
      | .done c => c
      | .yield c => iterIdx f (i+1) n c := rfl

theorem forIn_range'_idx {β : Type} (f : Nat → β → Id (ForInStep β)) :
    ∀ (n s : Nat) (b : β), forIn (m := Id) (List.range' s n) b f = iterIdx f s n b := by
  intro n
  induction n with
  | zero => intro s b; rfl
  | succ n ih =>
    intro s b
    rw [List.range'_succ, List.forIn_cons]
    simp only [iterIdx]
    cases (f s b : ForInStep β) with
    | done c => rfl
    | yield c => exact ih (s + 1) c

theorem forIn_range_idx {β : Type} (f : Nat → β → Id (ForInStep β)) (s e : Nat) (b : β) :
    forIn (m := Id) [s:e] b f = iterIdx f s (e - s) b := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
  exact forIn_range'_idx f (e - s) s b

/-- Lockstep simulation of an Aeneas loop against `iterIdx` up to bound `e`. -/
theorem loop_iterIdx {α γ β : Type} (body : α → Result (ControlFlow α γ))
    (f : Nat → β → Id (ForInStep β)) (e : Nat) (R : α → Nat → β → Prop) (Fin : γ → β → Prop)
    (hstep : ∀ x i b, R x i b → i < e →
      (∃ c, (f i b : ForInStep β) = .yield c ∧ ∃ x', body x = ok (.cont x') ∧ R x' (i+1) c) ∨
      (∃ c, (f i b : ForInStep β) = .done c ∧ ∃ y, loop body x = ok y ∧ Fin y c))
    (hend : ∀ x i b, R x i b → e ≤ i → ∃ y, body x = ok (.done y) ∧ Fin y b) :
    ∀ x i b, R x i b → ∃ y, loop body x = ok y ∧ Fin y (iterIdx f i (e - i) b) := by
  intro x i b
  induction hm : e - i using Nat.strong_induction_on generalizing x i b with
  | _ n ih =>
    intro hR
    by_cases hlt : i < e
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [iterIdx_succ]
      rcases hstep x i b hR hlt with ⟨c, hc, x', hb, hR'⟩ | ⟨c, hc, y, hy, hF⟩
      · rw [hc]
        obtain ⟨y, hy, hF⟩ := ih n' (by omega) x' (i+1) c (by omega) hR'
        exact ⟨y, by rw [loop_unfold, hb]; simpa using hy, hF⟩
      · rw [hc]; exact ⟨y, hy, hF⟩
    · have : n = 0 := by omega
      subst this
      obtain ⟨y, hb, hF⟩ := hend x i b hR (by omega)
      exact ⟨y, by rw [loop_unfold, hb]; simp, by rw [iterIdx_zero]; exact hF⟩

/-- `loop_iterIdx` with the spec's final state named (`generalize hS : iterIdx _ i _ b = S` in the goal fixes `f`). -/
theorem loop_iterIdx' {α γ β : Type} (body : α → Result (ControlFlow α γ))
    (f : Nat → β → Id (ForInStep β)) (e : Nat) (R : α → Nat → β → Prop) (Fin : γ → β → Prop)
    (hstep : ∀ x i b, R x i b → i < e →
      (∃ c, (f i b : ForInStep β) = .yield c ∧ ∃ x', body x = ok (.cont x') ∧ R x' (i+1) c) ∨
      (∃ c, (f i b : ForInStep β) = .done c ∧ ∃ y, loop body x = ok y ∧ Fin y c))
    (hend : ∀ x i b, R x i b → e ≤ i → ∃ y, body x = ok (.done y) ∧ Fin y b)
    (x : α) (i : Nat) (b : β) (hR : R x i b) {S : β} (hS : iterIdx f i (e - i) b = S) :
    ∃ y, loop body x = ok y ∧ Fin y S := by
  subst hS; exact loop_iterIdx body f e R Fin hstep hend x i b hR

theorem ok_of_ex {γ : Type} {m : Result γ} {P : γ → Prop} {v : γ} (H : ∃ y, m = ok y ∧ P y)
    (hv : ∀ y, P y → y = v) : m = ok v := by
  obtain ⟨y, h, hp⟩ := H; rw [h, hv y hp]

/-- Equational form of `loop_iterIdx`: the loop returns `G` of the spec loop's final state. -/
theorem loop_iterIdx_eq {α γ β : Type} (body : α → Result (ControlFlow α γ))
    (f : Nat → β → Id (ForInStep β)) (e : Nat) (R : α → Nat → β → Prop) (G : β → γ)
    (hstep : ∀ x i b, R x i b → i < e →
      (∃ c, (f i b : ForInStep β) = .yield c ∧ ∃ x', body x = ok (.cont x') ∧ R x' (i+1) c) ∨
      (∃ c, (f i b : ForInStep β) = .done c ∧ loop body x = ok (G c)))
    (hend : ∀ x i b, R x i b → e ≤ i → body x = ok (.done (G b)))
    (x : α) (i : Nat) (b : β) (hR : R x i b) :
    loop body x = ok (G (iterIdx f i (e - i) b)) := by
  obtain ⟨y, hy, rfl⟩ := loop_iterIdx body f e R (fun y c => y = G c)
    (fun x i b hR hi => (hstep x i b hR hi).imp id (fun ⟨c, hc, h⟩ => ⟨c, hc, _, h, rfl⟩))
    (fun x i b hR hi => ⟨_, hend x i b hR hi, rfl⟩) x i b hR
  exact hy

theorem usize_sub_one (i : Usize) (h : 1 ≤ i.val) : ∃ z, i - 1#usize = ok z ∧ z.val = i.val - 1 := by
  obtain ⟨z, hz, hzv, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := i) (y := 1#usize) (by simp; omega))
  exact ⟨z, hz, by rw [hzv]; simp⟩

theorem nat_sub_eq (a b : Usize) : ∃ r, beatmap.dotnet.nat_sub a b = ok r ∧ r.val = a.val - b.val :=
  beatmap.dotnet.nat_sub_refines a b
/-! ## Float constants of the slice (shortest round-trip literal, kernel-checked) -/
@[simp] theorem bmc_beatmap_slider_path_D0 : beatmap.slider_path.D0 = ok (0 : F64) := by
  simp [beatmap.slider_path.D0, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_path_approximator_K2 : beatmap.path_approximator.K2 = ok (2 : F32) := by
  simp [beatmap.path_approximator.K2, float.F32.from_bits] <;> decide

@[simp] theorem bmc_beatmap_path_approximator_K0_25 : beatmap.path_approximator.K0_25 = ok (0.25 : F32) := by
  simp [beatmap.path_approximator.K0_25, float.F32.from_bits] <;> decide

@[simp] theorem bmc_beatmap_path_approximator_K4 : beatmap.path_approximator.K4 = ok (4 : F32) := by
  simp [beatmap.path_approximator.K4, float.F32.from_bits] <;> decide

@[simp] theorem bmc_beatmap_path_approximator_BEZIER_TOLERANCE : beatmap.path_approximator.BEZIER_TOLERANCE = ok (0.25 : F32) := by
  simp [beatmap.path_approximator.BEZIER_TOLERANCE, float.F32.from_bits] <;> decide

@[simp] theorem bmc_beatmap_slider_path_D6 : beatmap.slider_path.D6 = ok (6 : F64) := by
  simp [beatmap.slider_path.D6, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_path_approximator_D2 : beatmap.path_approximator.D2 = ok (2 : F64) := by
  simp [beatmap.path_approximator.D2, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_path_approximator_K1 : beatmap.path_approximator.K1 = ok (1 : F32) := by
  simp [beatmap.path_approximator.K1, float.F32.from_bits] <;> decide

@[simp] theorem bmc_beatmap_path_approximator_CIRCULAR_ARC_TOLERANCE : beatmap.path_approximator.CIRCULAR_ARC_TOLERANCE = ok (0.1 : F32) := by
  simp [beatmap.path_approximator.CIRCULAR_ARC_TOLERANCE, float.F32.from_bits] <;> decide

@[simp] theorem bmc_beatmap_path_approximator_D0 : beatmap.path_approximator.D0 = ok (0 : F64) := by
  simp [beatmap.path_approximator.D0, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_path_approximator_F32_ZERO : beatmap.path_approximator.F32_ZERO = ok (0 : F32) := by
  simp [beatmap.path_approximator.F32_ZERO, float.F32.from_bits] <;> decide

@[simp] theorem bmc_beatmap_path_approximator_D1 : beatmap.path_approximator.D1 = ok (1 : F64) := by
  simp [beatmap.path_approximator.D1, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_path_approximator_PI : beatmap.path_approximator.PI = ok OsuModel.Beatmap.PathApproximator.PI := by
  simp [beatmap.path_approximator.PI, float.F64.from_bits, OsuModel.Beatmap.PathApproximator.PI] <;> decide

@[simp] theorem bmc_beatmap_path_approximator_K5 : beatmap.path_approximator.K5 = ok (5 : F32) := by
  simp [beatmap.path_approximator.K5, float.F32.from_bits] <;> decide

@[simp] theorem bmc_beatmap_path_approximator_K3 : beatmap.path_approximator.K3 = ok (3 : F32) := by
  simp [beatmap.path_approximator.K3, float.F32.from_bits] <;> decide

@[simp] theorem bmc_beatmap_path_approximator_K0_5 : beatmap.path_approximator.K0_5 = ok (0.5 : F32) := by
  simp [beatmap.path_approximator.K0_5, float.F32.from_bits] <;> decide

@[simp] theorem bmc_beatmap_slider_path_D1 : beatmap.slider_path.D1 = ok (1 : F64) := by
  simp [beatmap.slider_path.D1, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_D1 : beatmap.objects.D1 = ok (1 : F64) := by
  simp [beatmap.objects.D1, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_OBJECT_RADIUS : beatmap.objects.OBJECT_RADIUS = ok (64 : F32) := by
  simp [beatmap.objects.OBJECT_RADIUS, float.F32.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_D400 : beatmap.objects.D400 = ok (400 : F64) := by
  simp [beatmap.objects.D400, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_D600 : beatmap.objects.D600 = ok (600 : F64) := by
  simp [beatmap.objects.D600, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_F32_ONE : beatmap.objects.F32_ONE = ok (1 : F32) := by
  simp [beatmap.objects.F32_ONE, float.F32.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_D0 : beatmap.objects.D0 = ok (0 : F64) := by
  simp [beatmap.objects.D0, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_DURATION_ERROR : beatmap.objects.DURATION_ERROR = ok (0.0001 : F64) := by
  simp [beatmap.objects.DURATION_ERROR, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_D1000 : beatmap.objects.D1000 = ok (1000 : F64) := by
  simp [beatmap.objects.D1000, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_D60 : beatmap.objects.D60 = ok (60 : F64) := by
  simp [beatmap.objects.D60, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_D5 : beatmap.objects.D5 = ok (5 : F64) := by
  simp [beatmap.objects.D5, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_slider_event_generator_D1 : beatmap.slider_event_generator.D1 = ok (1 : F64) := by
  simp [beatmap.slider_event_generator.D1, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_slider_event_generator_MAX_LENGTH : beatmap.slider_event_generator.MAX_LENGTH = ok (100000 : F64) := by
  simp [beatmap.slider_event_generator.MAX_LENGTH, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_slider_event_generator_D10 : beatmap.slider_event_generator.D10 = ok (10 : F64) := by
  simp [beatmap.slider_event_generator.D10, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_slider_event_generator_D2 : beatmap.slider_event_generator.D2 = ok (2 : F64) := by
  simp [beatmap.slider_event_generator.D2, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_slider_event_generator_D0 : beatmap.slider_event_generator.D0 = ok (0 : F64) := by
  simp [beatmap.slider_event_generator.D0, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_slider_event_generator_TAIL_LENIENCY : beatmap.slider_event_generator.TAIL_LENIENCY = ok (-36 : F64) := by
  simp [beatmap.slider_event_generator.TAIL_LENIENCY, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_D200 : beatmap.objects.D200 = ok (200 : F64) := by
  simp [beatmap.objects.D200, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_F_0_66 : beatmap.objects.F_0_66 = ok (0.66 : F32) := by
  simp [beatmap.objects.F_0_66, float.F32.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_D450 : beatmap.objects.D450 = ok (450 : F64) := by
  simp [beatmap.objects.D450, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_D1200 : beatmap.objects.D1200 = ok (1200 : F64) := by
  simp [beatmap.objects.D1200, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_D1800 : beatmap.objects.D1800 = ok (1800 : F64) := by
  simp [beatmap.objects.D1800, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_F32_FUDGE : beatmap.objects.F32_FUDGE = ok (1.00041 : F32) := by
  simp [beatmap.objects.F32_FUDGE, float.F32.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_F32_2 : beatmap.objects.F32_2 = ok (2 : F32) := by
  simp [beatmap.objects.F32_2, float.F32.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_F32_0_7 : beatmap.objects.F32_0_7 = ok (0.7 : F32) := by
  simp [beatmap.objects.F32_0_7, float.F32.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_D_HALF : beatmap.objects.D_HALF = ok (0.5 : F64) := by
  simp [beatmap.objects.D_HALF, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_D2 : beatmap.objects.D2 = ok (2 : F64) := by
  simp [beatmap.objects.D2, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_F1000 : beatmap.objects.F1000 = ok (1000 : F32) := by
  simp [beatmap.objects.F1000, float.F32.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_F10 : beatmap.objects.F10 = ok (10 : F32) := by
  simp [beatmap.objects.F10, float.F32.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_D100 : beatmap.objects.D100 = ok (100 : F64) := by
  simp [beatmap.objects.D100, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_D_M100 : beatmap.objects.D_M100 = ok (-100 : F64) := by
  simp [beatmap.objects.D_M100, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_BASE_SCORING_DISTANCE : beatmap.objects.BASE_SCORING_DISTANCE = ok (100 : F32) := by
  simp [beatmap.objects.BASE_SCORING_DISTANCE, float.F32.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_MISS_WINDOW : beatmap.objects.MISS_WINDOW = ok (400 : F64) := by
  simp [beatmap.objects.MISS_WINDOW, float.F64.from_bits] <;> decide

@[simp] theorem bmc_beatmap_objects_F32_M6_4 : beatmap.objects.F32_M6_4 = ok (-6.4 : F32) := by
  simp [beatmap.objects.F32_M6_4, float.F32.from_bits] <;> decide


section
open OsuModel.Beatmap.PathApproximator

/-! Rust constants ↦ the spec's named constants (normal form used by `pa_simp`). -/
theorem pa_K2 : beatmap.path_approximator.K2 = ok k2 := by simp [k2]
theorem pa_K3 : beatmap.path_approximator.K3 = ok k3 := by simp [k3]
theorem pa_K4 : beatmap.path_approximator.K4 = ok k4 := by simp [k4]
theorem pa_K5 : beatmap.path_approximator.K5 = ok k5 := by simp [k5]
theorem pa_K0_25 : beatmap.path_approximator.K0_25 = ok k0_25 := by simp [k0_25]
theorem pa_K0_5 : beatmap.path_approximator.K0_5 = ok k0_5 := by simp [k0_5]
theorem pa_CAT : beatmap.path_approximator.CIRCULAR_ARC_TOLERANCE = ok circular_arc_tolerance := by
  simp [circular_arc_tolerance]
theorem pa_k_flat : beatmap.path_approximator.k_flat = ok kFlat := by
  simp [beatmap.path_approximator.k_flat, beatmap.path_approximator.BEZIER_TOLERANCE,
    beatmap.path_approximator.K4, kFlat, BEZIER_TOLERANCE] <;> decide

/-! Spec `Vec2` operator notation ↦ the named functions (which the Rust refinement lemmas produce). -/
theorem vec2_add_def (a b : Vec2) : a + b = Vec2.add a b := rfl
theorem vec2_sub_def (a b : Vec2) : a - b = Vec2.sub a b := rfl
theorem vec2_neg_def (a : Vec2) : -a = Vec2.neg a := rfl
theorem vec2_smul_def (s : F32) (a : Vec2) : s * a = Vec2.scale a s := rfl
theorem vec2_muls_def (a : Vec2) (s : F32) : a * s = Vec2.scale a s := rfl
theorem vec2_div_def (a : Vec2) (s : F32) : a / s = Vec2.div a s := rfl
@[simp] theorem id_run_eq {α} (a : Id α) : Id.run a = a := rfl

def vS (l : List net.osutk.Vector2) : Array Vec2 := (l.map bv2S).toArray

@[simp] theorem vS_size (l : List net.osutk.Vector2) : (vS l).size = l.length := by simp [vS]
theorem vS_get! (l : List net.osutk.Vector2) (i : Nat) (h : i < l.length) : (vS l)[i]! = bv2S (l[i]'h) := by
  simp [vS, h]

/-- Straight-line float code: Rust primitives and `beatmap::vector2` wrappers ↦ spec ops. -/
macro "pa_simp" : tactic => `(tactic| (simp only [bind_ok, float.F32.add, float.F32.sub, float.F32.mul, float.F32.div,
  float.F32.neg, float.F32.to_f64, float.F32.from_i64, float.F64.add,
  float.F64.sub, float.F64.mul, float.F64.div, float.F64.neg,
  float.F64.to_f32, float.F64.from_i64, float.F64.sin, float.F64.cos, float.F64.atan2, float.F64.acos,
  float.F64.ceil, float.F64.floor, float.F64.to_i32_sat, float.F64.sqrt, float.F64.abs, float.F32.abs,
  beatmap.vector2.add_refines, beatmap.vector2.sub_refines, beatmap.vector2.scale_refines,
  beatmap.vector2.div_refines, beatmap.vector2.length_refines, beatmap.vector2.length_squared_refines,
  beatmap.vector2.dot_refines, beatmap.vector2.eq_refines, beatmap.vector2.normalized_refines,
  beatmap.vector2.distance_refines, beatmap.vector2.neg_refines, beatmap.vector2.splat_refines,
  beatmap.vector2.almost_equals_f32_refines, beatmap.vector2.almost_equals_f64_refines, bm_vector2_ZERO,
  bv2S_I, bv2I_S, bv2S_x, bv2S_y, bv2I_x, bv2I_y,
  pa_K2, pa_K0_25, pa_K4, pa_K5, pa_K3, pa_K0_5, pa_CAT, pa_k_flat,
  bmc_beatmap_path_approximator_D2, bmc_beatmap_path_approximator_K1, bmc_beatmap_path_approximator_D0,
  bmc_beatmap_path_approximator_F32_ZERO, bmc_beatmap_path_approximator_D1, bmc_beatmap_path_approximator_PI,
  ← vec2_add_def, ← vec2_sub_def, ← vec2_div_def, ← vec2_neg_def]; try simp only [bind_ok, decide_eq_true_eq, float.F32.lt, float.F32.le, float.F32.eq, float.F64.lt, float.F64.le,
    float.F64.eq]))

end
end OsuProofs
