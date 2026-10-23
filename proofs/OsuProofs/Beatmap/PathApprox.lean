/-
`beatmap::path_approximator` (Rust) refines `OsuModel.Beatmap.PathApproximator` (osu-framework
`PathApproximator` / `CircularArcProperties`): lockstep simulations of the float32/float64 code.
Rust `Vec<Vec2>`/`&[Vec2]` ↦ spec `Array Vec2` via `vS` (= `abs`); indexing preconditions are the
explicit length hypotheses (the spec's `a[i]!` defaults are never reached).
-/
import OsuProofs.Beatmap.PathApproxBase
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl
open OsuModel.Beatmap.PathApproximator

theorem beatmap.path_approximator.bezier_is_flat_enough_refines (cp : Slice net.osutk.Vector2) :
    beatmap.path_approximator.bezier_is_flat_enough cp = ok (bezierIsFlatEnough (vS cp.val)) := by
  unfold beatmap.path_approximator.bezier_is_flat_enough bezierIsFlatEnough
  simp only [pa_k_flat, bind_ok, Id.run_bind, vS_size]
  rw [forIn_range_idx]
  generalize hS : iterIdx _ 1 _ (none, ()) = S
  have hlen := Slice.length_ineq cp
  unfold beatmap.path_approximator.bezier_is_flat_enough_loop
  refine ok_of_ex (loop_iterIdx' _ _ (cp.val.length - 1)
    (fun (x : Usize × Bool) i (b : Option Bool × Unit) => x.1.val = i ∧ x.2 = true ∧ b = (none, ()) ∧ 1 ≤ i)
    (fun (y : Bool) (c : Option Bool × Unit) => (c.1 = none ∧ y = true) ∨ c.1 = some y)
    ?hstep ?hend (1#usize, true) 1 (none, ()) ⟨by simp, rfl, rfl, le_refl _⟩ hS) ?hv
  case hv => rintro y (⟨h1, rfl⟩ | h1) <;> simp [h1] <;> rfl
  case hstep =>
    rintro ⟨i, fl⟩ k b ⟨hi, hfl, hb, h1⟩ hk
    dsimp only at hi hfl hb
    subst hi hfl hb
    obtain ⟨i2, hi2, hi2v⟩ := nat_sub_eq (Slice.len cp) 1#usize
    obtain ⟨i3, hi3, hi3v⟩ := usize_sub_one i h1
    obtain ⟨i4, hi4, hi4v⟩ := usize_add_one i (by omega)
    have hlt : i < i2 := by show i.val < i2.val; rw [hi2v]; simp; omega
    have e3 : i3.val < cp.val.length := by omega
    have e0 : i.val < cp.val.length := by omega
    have e4 : i4.val < cp.val.length := by omega
    have g3 : (vS cp.val)[i.val - 1]! = bv2S (cp.val[i3.val]'e3) := by rw [vS_get! _ _ (by omega)]; congr 2; omega
    have g0 : (vS cp.val)[i.val]! = bv2S (cp.val[i.val]'e0) := vS_get! _ _ e0
    have g4 : (vS cp.val)[i.val + 1]! = bv2S (cp.val[i4.val]'e4) := by rw [vS_get! _ _ (by omega)]; congr 2; omega
    have hbody : beatmap.path_approximator.bezier_is_flat_enough_loop.body cp kFlat i true =
        ok (.cont (i4, if kFlat < ((vS cp.val)[i.val - 1]! - k2 * (vS cp.val)[i.val]! + (vS cp.val)[i.val + 1]!).lengthSquared
          then false else true)) := by
      rw [g3, g0, g4]
      simp only [beatmap.path_approximator.bezier_is_flat_enough_loop.body, ite_true, hi2, bind_ok, hlt, hi3, hi4,
        index_eq cp i3 e3, index_eq cp i e0, index_eq cp i4 e4, pa_K2, beatmap.vector2.scale_refines,
        beatmap.vector2.sub_refines, beatmap.vector2.add_refines, beatmap.vector2.length_squared_refines, float.F32.lt,
        bv2S_I, vec2_add_def, vec2_sub_def, vec2_smul_def]
      split <;> simp_all
    by_cases hc : kFlat < ((vS cp.val)[i.val - 1]! - k2 * (vS cp.val)[i.val]! + (vS cp.val)[i.val + 1]!).lengthSquared
    · right
      refine ⟨_, by simp only [hc, ite_true]; rfl, false, ?_, Or.inr rfl⟩
      rw [loop_unfold]; dsimp only; rw [hbody]
      simp only [hc, ite_true, bind_ok]
      rw [loop_unfold]; dsimp only
      simp [beatmap.path_approximator.bezier_is_flat_enough_loop.body]
    · left
      refine ⟨_, by simp only [hc, ite_false]; rfl, _, by dsimp only; rw [hbody], ?_⟩
      exact ⟨by simp [hi4v], by simp [hc], rfl, by omega⟩
  case hend =>
    rintro ⟨i, fl⟩ k b ⟨hi, hfl, hb, h1⟩ hk
    dsimp only at hi hfl hb
    subst hi hfl hb
    obtain ⟨i2, hi2, hi2v⟩ := nat_sub_eq (Slice.len cp) 1#usize
    have hlt : ¬ i.val < i2.val := by rw [hi2v]; simp; omega
    exact ⟨true, by simp [beatmap.path_approximator.bezier_is_flat_enough_loop.body, hi2, hlt], Or.inl ⟨rfl, rfl⟩⟩

def arcS (p : beatmap.path_approximator.CircularArcProperties) : CircularArcProperties :=
  { isValid := p.is_valid, thetaStart := p.theta_start, thetaRange := p.theta_range, direction := p.direction,
    radius := p.radius, centre := bv2S p.centre }

theorem beatmap.path_approximator.ARC_INVALID_refines :
    ∃ r, beatmap.path_approximator.ARC_INVALID = ok r ∧ arcS r = { isValid := false } := by
  refine ⟨_, by simp [beatmap.path_approximator.ARC_INVALID, beatmap.vector2.ZERO, net.osutk.V2_ZERO]; rfl, ?_⟩
  simp [arcS, bv2S, Vec2.zero]

theorem beatmap.path_approximator.catmull_coord_refines (v1 v2 v3 v4 t t2 t3 : F32) :
    beatmap.path_approximator.catmull_coord v1 v2 v3 v4 t t2 t3 =
      ok (k0_5 * (k2 * v2 + (-v1 + v3) * t + (k2 * v1 - k5 * v2 + k4 * v3 - v4) * t2
        + (-v1 + k3 * v2 - k3 * v3 + v4) * t3)) := by
  simp [beatmap.path_approximator.catmull_coord, k0_5, k2, k3, k4, k5]

theorem beatmap.path_approximator.catmull_find_point_refines (v1 v2 v3 v4 : net.osutk.Vector2) (t : F32) :
    beatmap.path_approximator.catmull_find_point v1 v2 v3 v4 t =
      ok (bv2I (catmullFindPoint (bv2S v1) (bv2S v2) (bv2S v3) (bv2S v4) t)) := by
  simp [beatmap.path_approximator.catmull_find_point, beatmap.path_approximator.catmull_coord_refines,
    catmullFindPoint, bv2I, bv2S]

theorem i32_max2 (n : Int32) :
    (if (⟨n.toBitVec⟩ : I32) < 2#i32 then ok 2#i32 else ok ⟨n.toBitVec⟩ : Result I32) = ok (i32I (if n < 2 then 2 else n)) := by
  have : ((⟨n.toBitVec⟩ : I32) < 2#i32) ↔ n < 2 := by
    rw [Int32.lt_iff_toInt_lt]
    show (⟨n.toBitVec⟩ : I32).val < (2#i32).val ↔ _
    simp [IScalar.val]
  by_cases h2 : n < 2 <;> simp [h2, this] <;> rfl

theorem beatmap.path_approximator.arc_point_count_refines (pr : beatmap.path_approximator.CircularArcProperties) :
    beatmap.path_approximator.arc_point_count pr = ok (i32I (arcPointCount (arcS pr))) := by
  unfold beatmap.path_approximator.arc_point_count arcPointCount
  simp only [bmc_beatmap_path_approximator_K2, bmc_beatmap_path_approximator_CIRCULAR_ARC_TOLERANCE,
    bmc_beatmap_path_approximator_K1, bmc_beatmap_path_approximator_D2, bind_ok, float.F32.mul, float.F32.le,
    float.F32.div, float.F32.sub, float.F32.to_f64, float.F64.acos, float.F64.mul, float.F64.div, float.F64.ceil,
    float.F64.to_i32_sat, arcS, k2, circular_arc_tolerance]
  by_cases h1 : (2 : F32) * pr.radius ≤ 0.1
  · simp [h1]; rfl
  · simp only [h1, decide_false, Bool.false_eq_true, ite_false, i32_max2]
    rfl

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

def arcStep (ts : F64) (te : F64) : F64 := if te < ts then te + PI * 2 else te

theorem i32_add_one (i : I32) (h1 : -2147483648 ≤ i.val + 1) (h2 : i.val + 1 ≤ 2147483647) :
    ∃ z, i + 1#i32 = ok z ∧ z.val = i.val + 1 := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (I32.add_spec (x := i) (y := 1#i32)
    (by simp [I32.min_eq]; omega) (by simp [I32.max_eq]; omega))
  exact ⟨z, hz, by simpa using hv⟩

theorem arc_loop_eq (ts te : F64) :
    beatmap.path_approximator.circular_arc_properties_loop ts te 0#i32 =
      ok ((arcStep ts)^[4] te) := by
  unfold beatmap.path_approximator.circular_arc_properties_loop
  refine loop_eq _ (fun (x : F64 × I32) => (4 - x.2.val).toNat) (fun x => 0 ≤ x.2.val ∧ x.2.val ≤ 4)
    (fun x => (arcStep ts)^[(4 - x.2.val).toNat] x.1) ?_ (te, 0#i32) (by simp)
  rintro ⟨t, k⟩ ⟨h0, h4⟩
  dsimp only at h0 h4 ⊢
  by_cases hk : k.val < 4
  · right
    obtain ⟨k1, hk1, hk1v⟩ := i32_add_one k (by omega) (by omega)
    refine ⟨(arcStep ts t, k1), ?_, by simp [hk1v]; omega, by simp [hk1v]; omega, ?_⟩
    · have : k < 4#i32 := by show k.val < (4#i32).val; simpa using hk
      simp only [beatmap.path_approximator.circular_arc_properties_loop.body, this, ite_true, hk1]
      pa_simp
      simp only [arcStep]
      split <;> simp only [bind_ok]
    · dsimp only
      have e : (4 - k1.val).toNat + 1 = (4 - k.val).toNat := by omega
      rw [← e, Function.iterate_succ_apply]
  · left
    have : ¬ k < 4#i32 := by show ¬ k.val < (4#i32).val; simpa using hk
    have hk4 : (4 - k.val).toNat = 0 := by omega
    simp [beatmap.path_approximator.circular_arc_properties_loop.body, this, hk4]

theorem iterIdx_ite_yield {β : Type} (p : β → Prop) (dec : ∀ b, Decidable (p b)) (u : β → β) :
    ∀ (n i : Nat) (b : β), iterIdx (fun _ b => if p b then pure (.yield (u b)) else pure (.yield b)) i n b =
      (fun b => if p b then u b else b)^[n] b := by
  intro n; induction n with
  | zero => intro i b; rfl
  | succ n ih =>
    intro i b; rw [iterIdx_succ]
    by_cases h : p b
    · simp only [h, ite_true, Function.iterate_succ_apply]; exact ih _ _
    · simp only [h, ite_false, Function.iterate_succ_apply]; exact ih _ _

theorem slice_get (cp : Slice net.osutk.Vector2) (i : Usize) (n : Nat) (hn : i.val = n) (h : n < cp.val.length) :
    ∃ a, Slice.index_usize cp i = ok a ∧ (vS cp.val)[n]! = bv2S a :=
  ⟨cp.val[n], by rw [index_eq cp _ (by omega)]; simp [hn], vS_get! _ _ h⟩

theorem beatmap.path_approximator.circular_arc_properties_refines (cp : Slice net.osutk.Vector2)
    (h : 3 ≤ cp.val.length) :
    ∃ r, beatmap.path_approximator.circular_arc_properties cp = ok r ∧ arcS r = circularArcProperties (vS cp.val) := by
  obtain ⟨a, ha, ha'⟩ := slice_get cp 0#usize 0 (by simp) (by omega)
  obtain ⟨b, hb, hb'⟩ := slice_get cp 1#usize 1 (by simp) (by omega)
  obtain ⟨c, hc, hc'⟩ := slice_get cp 2#usize 2 (by simp) (by omega)
  unfold beatmap.path_approximator.circular_arc_properties
  rw [ha, hb, hc]
  pa_simp
  simp only [arc_loop_eq]
  pa_simp
  unfold circularArcProperties
  rw [ha', hb', hc']
  simp only [Id.run_bind]
  rw [forIn_range_idx]
  simp only [iterIdx_ite_yield]
  split
  · rename_i hcond
    obtain ⟨r, hr, hr'⟩ := beatmap.path_approximator.ARC_INVALID_refines
    refine ⟨r, hr, ?_⟩
    rw [hr']
    split
    · rfl
    · rename_i h2; exact absurd hcond h2
  · rename_i hcond
    split
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals rename_i hd
    all_goals rw [id_run_eq]
    all_goals split
    all_goals rename_i h2
    all_goals try exact absurd h2 hcond
    all_goals rw [id_bind_eq']
    all_goals split
    all_goals rename_i h3
    all_goals first | rfl | exact absurd h3 hd | exact absurd hd h3

theorem vS_extract (l : List net.osutk.Vector2) (lo hi : Nat) :
    (vS l).extract lo hi = vS ((l.take hi).drop lo) := by
  simp only [vS]
  apply Array.ext'
  simp [List.map_drop, List.map_take, List.drop_take]

theorem take_drop_push {α} (l : List α) (lo i : Nat) (h1 : lo ≤ i) (h2 : i < l.length) :
    (l.take i).drop lo ++ [l[i]] = (l.take (i+1)).drop lo := by
  rw [List.take_add_one, List.getElem?_eq_getElem h2]
  simp only [Option.toList_some]
  rw [List.drop_append_of_le_length (by simp; omega)]
theorem take_drop_end {α} (l : List α) (lo i hi : Nat) (h1 : lo ≤ i) (hc : ¬ (i < hi ∧ i < l.length))
    (h3 : i ≤ min hi l.length ∨ i = lo) : (l.take i).drop lo = (l.take hi).drop lo := by
  rcases h3 with h3 | h3
  · have e : i = min hi l.length := by omega
    by_cases hh : hi ≤ l.length
    · rw [e, Nat.min_eq_left hh]
    · rw [e, Nat.min_eq_right (by omega), List.take_of_length_le (le_refl _),
        List.take_of_length_le (l := l) (by omega)]
  · subst h3
    rw [List.drop_take_self]; symm
    rw [List.drop_eq_nil_iff, List.length_take]; omega

theorem beatmap.path_approximator.extract_refines (a : Slice net.osutk.Vector2) (lo hi : Usize) :
    ∃ v, beatmap.path_approximator.extract a lo hi = ok v ∧ v.val = (a.val.take hi.val).drop lo.val := by
  have hlen := Slice.length_ineq a
  unfold beatmap.path_approximator.extract beatmap.path_approximator.extract_loop
  refine loop_ok _ (fun (x : alloc.vec.Vec net.osutk.Vector2 × Usize) => a.val.length - x.2.val)
    (fun x => lo.val ≤ x.2.val ∧ x.1.val = (a.val.take x.2.val).drop lo.val ∧
      (x.2.val ≤ min hi.val a.val.length ∨ x.2.val = lo.val))
    (fun (v : alloc.vec.Vec net.osutk.Vector2) => v.val = (a.val.take hi.val).drop lo.val) ?_
    (alloc.vec.Vec.new net.osutk.Vector2, lo) ⟨le_refl _, by simp, Or.inr rfl⟩
  rintro ⟨out, i⟩ ⟨h1, h2, h3⟩
  dsimp only at h1 h2 h3 ⊢
  by_cases hc : i.val < hi.val ∧ i.val < a.val.length
  · right
    have hb : out.val.length < Usize.max := by rw [h2]; simp; omega
    obtain ⟨o1, ho1, ho1v⟩ := push_eq out (a.val[i.val]'hc.2) hb
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
    refine ⟨(o1, i1), ?_, ⟨by dsimp only; omega, ?_, Or.inl (by dsimp only; omega)⟩, by dsimp only; omega⟩
    · have c1 : i < hi := hc.1
      have c2 : i < Slice.len a := by show i.val < (Slice.len a).val; simp; exact hc.2
      simp [beatmap.path_approximator.extract_loop.body, c1, c2, index_eq a i hc.2, ho1, hi1]
    · dsimp only; rw [ho1v, h2, hi1v]; exact take_drop_push _ _ _ h1 hc.2
  · left
    refine ⟨out, ?_, ?_⟩
    · by_cases c1 : i < hi
      · have c2 : ¬ i < Slice.len a := by show ¬ i.val < (Slice.len a).val; simp; have : i.val < hi.val := c1; omega
        simp [beatmap.path_approximator.extract_loop.body, c1, c2]
      · simp [beatmap.path_approximator.extract_loop.body, c1]
    · rw [h2]; exact take_drop_end _ _ _ _ h1 hc h3

theorem usize_le_max (n : Usize) : n.val ≤ Usize.max := by
  have := n.hBounds; rw [Usize.max_def]; simp [Usize.numBits] at this ⊢; omega

theorem beatmap.path_approximator.replicate_zero_refines (n : Usize) :
    ∃ v, beatmap.path_approximator.replicate_zero n = ok v ∧ vS v.val = Array.replicate n.val Vec2.zero := by
  have hn := n.hBounds
  unfold beatmap.path_approximator.replicate_zero beatmap.path_approximator.replicate_zero_loop
  have H := loop_ok (fun (x : alloc.vec.Vec net.osutk.Vector2 × Usize) =>
      beatmap.path_approximator.replicate_zero_loop.body n x.1 x.2) (fun x => n.val - x.2.val)
    (fun x => x.2.val ≤ n.val ∧ x.1.val = List.replicate x.2.val (bv2I Vec2.zero))
    (fun (v : alloc.vec.Vec net.osutk.Vector2) => v.val = List.replicate n.val (bv2I Vec2.zero)) (by
      rintro ⟨out, i⟩ ⟨h1, h2⟩
      dsimp only at h1 h2 ⊢
      by_cases hc : i.val < n.val
      · right
        have hb : out.val.length < Usize.max := by rw [h2]; simp; have := usize_le_max n; omega
        obtain ⟨o1, ho1, ho1v⟩ := push_eq out (bv2I Vec2.zero) hb
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := usize_le_max n; omega)
        refine ⟨(o1, i1), ?_, ⟨by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
        · have c1 : i < n := hc
          simp [beatmap.path_approximator.replicate_zero_loop.body, c1, bm_vector2_ZERO, ho1, hi1]
        · dsimp only; rw [ho1v, h2, hi1v, List.replicate_succ']
      · left
        have c1 : ¬ i < n := hc
        exact ⟨out, by simp [beatmap.path_approximator.replicate_zero_loop.body, c1], by rw [h2]; congr 1; omega⟩)
    (alloc.vec.Vec.with_capacity net.osutk.Vector2 n, 0#usize) ⟨by simp, by simp [alloc.vec.Vec.with_capacity]⟩
  obtain ⟨v, hv, hvv⟩ := H
  refine ⟨v, hv, ?_⟩
  rw [hvv]; simp [vS, bv2I, bv2S, Vec2.zero]

theorem beatmap.path_approximator.linear_to_piecewise_linear_refines (cp : Slice net.osutk.Vector2) :
    ∃ v, beatmap.path_approximator.linear_to_piecewise_linear cp = ok v ∧
      vS v.val = linearToPiecewiseLinear (vS cp.val) := by
  obtain ⟨v, hv, hvv⟩ := beatmap.path_approximator.extract_refines cp 0#usize (Slice.len cp)
  refine ⟨v, by simpa [beatmap.path_approximator.linear_to_piecewise_linear] using hv, ?_⟩
  rw [hvv]; simp [linearToPiecewiseLinear]

theorem vS_set (l : List net.osutk.Vector2) (i : Nat) (v : net.osutk.Vector2) :
    vS (l.set i v) = (vS l).set! i (bv2S v) := by
  simp [vS, Array.set!, List.map_set]

theorem vS_length (l : List net.osutk.Vector2) : (vS l).size = l.length := by simp [vS]

theorem subdiv_inner (count i : Usize) (g : Nat → Array Vec2 → Id (ForInStep (Array Vec2)))
    (hg : ∀ j m, g j m = .yield (m.set! j ((m[j]! + m[j+1]!) / k2))) (hi : i.val < count.val) :
    ∀ (mid : alloc.vec.Vec net.osutk.Vector2), mid.val.length = count.val →
    ∃ mid', beatmap.path_approximator.bezier_subdivide_loop0_loop0 count mid i 0#usize = ok mid' ∧
      vS mid'.val = iterIdx g 0 (count.val - i.val - 1 - 0) (vS mid.val) ∧ mid'.val.length = count.val := by
  intro mid hmid
  unfold beatmap.path_approximator.bezier_subdivide_loop0_loop0
  have hcm := usize_le_max count
  obtain ⟨i1, hi1, hi1v⟩ := eq_ok_of_spec (Usize.sub_spec (x := count) (y := i) (by omega))
  obtain ⟨i2, hi2, hi2v⟩ := usize_sub_one i1 (by omega)
  refine loop_iterIdx' _ g (count.val - i.val - 1)
    (fun (x : alloc.vec.Vec net.osutk.Vector2 × Usize) j (b : Array Vec2) =>
      x.2.val = j ∧ vS x.1.val = b ∧ x.1.val.length = count.val)
    (fun (y : alloc.vec.Vec net.osutk.Vector2) (c : Array Vec2) => vS y.val = c ∧ y.val.length = count.val)
    ?_ ?_ (mid, 0#usize) 0 (vS mid.val) ⟨by simp, rfl, hmid⟩ rfl
  · rintro ⟨m, j⟩ k b ⟨hj, hb, hl⟩ hk
    dsimp only at hj hb hl
    subst hj hb
    left
    have hj1 : j.val + 1 < m.val.length := by omega
    have hj0 : j.val < m.val.length := by omega
    obtain ⟨j1, hj1e, hj1v⟩ := usize_add_one j (by omega)
    have hlt : j < i2 := by show j.val < i2.val; omega
    refine ⟨_, hg _ _, (alloc.vec.Vec.set m j (bv2I ((bv2S (m.val[j.val]'hj0) + bv2S (m.val[j.val+1]'hj1)) / k2)), j1), ?_, ?_⟩
    · simp only [beatmap.path_approximator.bezier_subdivide_loop0_loop0.body, hi1, hi2, bind_ok, hlt, ite_true,
        vec_index_eq' m j hj0, hj1e, vec_index_eq' m j1 (by omega), vec_index_mut_eq m j hj0, pa_K2,
        beatmap.vector2.add_refines, beatmap.vector2.div_refines, bv2S_I]
      simp [hj1v, vec2_add_def, vec2_div_def]
    · refine ⟨by simp [hj1v], ?_, by simp [hl]⟩
      dsimp only
      rw [alloc.vec.Vec.set_val_eq, vS_set, bv2S_I, vS_get! _ _ hj0, vS_get! _ _ hj1]
  · rintro ⟨m, j⟩ k b ⟨hj, hb, hl⟩ hk
    dsimp only at hj hb hl
    subst hj hb
    have hlt : ¬ j.val < i2.val := by omega
    exact ⟨m, by simp [beatmap.path_approximator.bezier_subdivide_loop0_loop0.body, hi1, hi2, hlt], rfl, hl⟩

theorem beatmap.path_approximator.bezier_subdivide_refines (cp : Slice net.osutk.Vector2) (count : Usize)
    (hc : count.val ≤ cp.val.length) :
    ∃ res, beatmap.path_approximator.bezier_subdivide cp count = ok res ∧
      (vS res.1.val, vS res.2.val) = bezierSubdivide (vS cp.val) count.val ∧
      res.1.val.length = count.val ∧ res.2.val.length = count.val := by
  obtain ⟨m0, hm0, hm0v⟩ := beatmap.path_approximator.extract_refines cp 0#usize count
  obtain ⟨z0, hz0, hz0v⟩ := beatmap.path_approximator.replicate_zero_refines count
  have hm0l : m0.val.length = count.val := by rw [hm0v]; simp; omega
  have hz0l : z0.val.length = count.val := by rw [← vS_length, hz0v]; simp
  unfold beatmap.path_approximator.bezier_subdivide bezierSubdivide
  simp only [hm0, hz0, bind_ok, Id.run_bind]
  simp only [forIn_range_idx]
  generalize hS : iterIdx _ 0 _ _ = S
  unfold beatmap.path_approximator.bezier_subdivide_loop0
  have hcm := usize_le_max count
  refine Exists.imp (fun y H => ⟨H.1, ?hv, H.2.2.2⟩) (loop_iterIdx' _ _ count.val
    (fun (x : alloc.vec.Vec net.osutk.Vector2 × alloc.vec.Vec net.osutk.Vector2 × alloc.vec.Vec net.osutk.Vector2 × Usize)
      i (b : Array Vec2 × Array Vec2 × Array Vec2) =>
      x.2.2.2.val = i ∧ vS x.1.val = b.1 ∧ vS x.2.1.val = b.2.1 ∧ vS x.2.2.1.val = b.2.2 ∧
      x.1.val.length = count.val ∧ x.2.1.val.length = count.val ∧ x.2.2.1.val.length = count.val)
    (fun (y : alloc.vec.Vec net.osutk.Vector2 × alloc.vec.Vec net.osutk.Vector2) (c : Array Vec2 × Array Vec2 × Array Vec2) =>
      vS y.1.val = c.2.1 ∧ vS y.2.val = c.2.2 ∧ y.1.val.length = count.val ∧ y.2.val.length = count.val)
    ?hstep ?hend (m0, z0, z0, 0#usize) 0 _ ⟨by simp, by rw [hm0v]; simp [vS_extract], hz0v, hz0v, hm0l, hz0l, hz0l⟩ hS)
  case hv => obtain ⟨_, h1, h2, _⟩ := H; rw [id_run_eq] at *; simp [h1, h2]; rfl
  case hstep =>
    rintro ⟨m, l, r, i⟩ k ⟨b1, b2, b3⟩ ⟨hi, hm, hl, hr, hml, hll, hrl⟩ hk
    dsimp only at hi hm hl hr hml hll hrl
    subst hi b1 b2 b3
    left
    have hik : i.val < count.val := hk
    obtain ⟨i1, hi1, hi1v⟩ := eq_ok_of_spec (Usize.sub_spec (x := count) (y := i) (by omega))
    obtain ⟨i2, hi2, hi2v⟩ := usize_sub_one i1 (by omega)
    obtain ⟨i4, hi4, hi4v⟩ := usize_add_one i (by omega)
    obtain ⟨m', hm', hm'v, hm'l⟩ := subdiv_inner count i _ (fun _ _ => rfl) hik m hml
    have e0 : 0 < m.val.length := by omega
    have e2 : i2.val < m.val.length := by omega
    have e2' : i2.val < r.val.length := by omega
    have el : i.val < l.val.length := by omega
    refine ⟨_, rfl, (m', alloc.vec.Vec.set l i (m.val[0]'e0), alloc.vec.Vec.set r i2 (m.val[i2.val]'e2), i4), ?_, ?_⟩
    · have c1 : i < count := hik
      simp only [beatmap.path_approximator.bezier_subdivide_loop0.body, c1, ite_true, bind_ok,
        vec_index_eq' m 0#usize (by simpa using e0), vec_index_mut_eq l i el, hi1, hi2, vec_index_eq' m i2 e2,
        vec_index_mut_eq r i2 e2', hm', hi4]
      simp
    · refine ⟨by simp [hi4v], hm'v, ?_, ?_, hm'l, by simp [hll], by simp [hrl]⟩
      · dsimp only; rw [alloc.vec.Vec.set_val_eq, vS_set, vS_get! _ _ e0]
      · dsimp only; rw [alloc.vec.Vec.set_val_eq, vS_set, vS_get! _ _ (by omega : count.val - i.val - 1 < m.val.length)]
        have : i2.val = count.val - i.val - 1 := by omega
        simp only [this]
  case hend =>
    rintro ⟨m, l, r, i⟩ k ⟨b1, b2, b3⟩ ⟨hi, hm, hl, hr, hml, hll, hrl⟩ hk
    dsimp only at hi hm hl hr hml hll hrl
    subst hi b1 b2 b3
    have hlt : ¬ i.val < count.val := by omega
    exact ⟨(l, r), by simp [beatmap.path_approximator.bezier_subdivide_loop0.body, hlt], rfl, rfl, hll, hrl⟩

theorem ba_loop0 (count : Usize) : ∀ (l : alloc.vec.Vec net.osutk.Vector2) (z : Usize),
    l.val.length + (count.val - 1 - z.val) ≤ Usize.max →
    ∃ l', beatmap.path_approximator.bezier_approximate_loop0 count l z = ok l' ∧
      l'.val = l.val ++ List.replicate (count.val - 1 - z.val) (bv2I Vec2.zero) := by
  intro l z hb
  unfold beatmap.path_approximator.bezier_approximate_loop0
  obtain ⟨i, hi, hiv⟩ := nat_sub_eq count 1#usize
  have H := loop_ok (fun (x : alloc.vec.Vec net.osutk.Vector2 × Usize) =>
      beatmap.path_approximator.bezier_approximate_loop0.body count x.1 x.2) (fun x => count.val - 1 - x.2.val)
    (fun x => x.1.val.length + (count.val - 1 - x.2.val) ≤ Usize.max ∧
      x.1.val ++ List.replicate (count.val - 1 - x.2.val) (bv2I Vec2.zero) =
        l.val ++ List.replicate (count.val - 1 - z.val) (bv2I Vec2.zero))
    (fun (v : alloc.vec.Vec net.osutk.Vector2) => v.val = l.val ++ List.replicate (count.val - 1 - z.val) (bv2I Vec2.zero))
    (by
      rintro ⟨out, j⟩ ⟨h1, h2⟩
      dsimp only at h1 h2 ⊢
      by_cases hc : j.val < count.val - 1
      · right
        obtain ⟨o1, ho1, ho1v⟩ := push_eq out (bv2I Vec2.zero) (by omega)
        obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := usize_le_max count; omega)
        refine ⟨(o1, j1), ?_, ⟨by dsimp only; rw [ho1v]; simp; omega, ?_⟩, by dsimp only; omega⟩
        · have c1 : j.val < i.val := by simp at hiv; omega
          simp [beatmap.path_approximator.bezier_approximate_loop0.body, hi, c1, bm_vector2_ZERO, ho1, hj1]
        · dsimp only; rw [ho1v, ← h2, hj1v]
          have e : count.val - 1 - j.val = (count.val - 1 - (j.val + 1)) + 1 := by omega
          rw [e, List.replicate_succ]; simp
      · left
        have c1 : ¬ j.val < i.val := by simp at hiv; omega
        refine ⟨out, by simp [beatmap.path_approximator.bezier_approximate_loop0.body, hi, c1], ?_⟩
        rw [← h2]; have e : count.val - 1 - j.val = 0 := by omega
        rw [e]; simp)
    (l, z) ⟨hb, rfl⟩
  exact H

theorem vec_index_mut_usize_eq {α} (v : alloc.vec.Vec α) (i : Usize) (h : i.val < v.val.length) :
    alloc.vec.Vec.index_mut_usize v i = ok (v.val[i.val]'h, alloc.vec.Vec.set v i) := by
  obtain ⟨⟨a, b⟩, hx, hx1, hx2⟩ := eq_ok_of_spec (alloc.vec.Vec.index_mut_usize_spec v i h)
  rw [hx, hx1, hx2]

theorem vS_push (l : List net.osutk.Vector2) (v : net.osutk.Vector2) : vS (l ++ [v]) = (vS l).push (bv2S v) := by
  simp [vS]

theorem ba_loop1 (count : Usize) (r : alloc.vec.Vec net.osutk.Vector2) (hr : r.val.length = count.val)
    (g : Nat → Array Vec2 → Id (ForInStep (Array Vec2)))
    (hg : ∀ i m, g i m = .yield (m.set! (count.val + i) (vS r.val)[i + 1]!)) :
    ∀ (l : alloc.vec.Vec net.osutk.Vector2), l.val.length = 2 * count.val - 1 →
    ∃ l', beatmap.path_approximator.bezier_approximate_loop1 count r l 0#usize = ok l' ∧
      vS l'.val = iterIdx g 0 (count.val - 1 - 0) (vS l.val) ∧ l'.val.length = 2 * count.val - 1 := by
  intro l hl
  unfold beatmap.path_approximator.bezier_approximate_loop1
  have hcm := usize_le_max count
  obtain ⟨i1, hi1, hi1v⟩ := nat_sub_eq count 1#usize
  refine loop_iterIdx' _ g (count.val - 1)
    (fun (x : alloc.vec.Vec net.osutk.Vector2 × Usize) j (b : Array Vec2) =>
      x.2.val = j ∧ vS x.1.val = b ∧ x.1.val.length = 2 * count.val - 1)
    (fun (y : alloc.vec.Vec net.osutk.Vector2) (c : Array Vec2) => vS y.val = c ∧ y.val.length = 2 * count.val - 1)
    ?_ ?_ (l, 0#usize) 0 (vS l.val) ⟨by simp, rfl, hl⟩ rfl
  · rintro ⟨m, j⟩ k b ⟨hj, hb, hml⟩ hk
    dsimp only at hj hb hml
    subst hj hb
    left
    have hmm := alloc.vec.Vec.property m
    obtain ⟨j1, hj1e, hj1v⟩ := usize_add_one j (by omega)
    obtain ⟨j3, hj3e, hj3v⟩ := eq_ok_of_spec (Usize.add_spec (x := count) (y := j) (by omega))
    have hlt : j.val < i1.val := by simp at hi1v; omega
    have er : j1.val < r.val.length := by omega
    have em : j3.val < m.val.length := by omega
    refine ⟨_, hg _ _, (alloc.vec.Vec.set m j3 (r.val[j1.val]'er), j1), ?_, ?_⟩
    · simp [beatmap.path_approximator.bezier_approximate_loop1.body, hi1, hlt, hj1e, vec_index_usize_eq r j1 er,
        hj3e, vec_index_mut_usize_eq m j3 em]
    · refine ⟨by simp [hj1v], ?_, by simp [hml]⟩
      dsimp only
      rw [alloc.vec.Vec.set_val_eq, vS_set, vS_get! _ _ (by omega : j.val + 1 < r.val.length), hj3v]
      simp [hj1v]
  · rintro ⟨m, j⟩ k b ⟨hj, hb, hml⟩ hk
    dsimp only at hj hb hml
    subst hj hb
    have hlt : ¬ j.val < i1.val := by simp at hi1v; omega
    exact ⟨m, by simp [beatmap.path_approximator.bezier_approximate_loop1.body, hi1, hlt], rfl, hml⟩

theorem ba_loop2 (count : Usize) (l : alloc.vec.Vec net.osutk.Vector2) (hl : l.val.length = 2 * count.val - 1)
    (h2 : 2 * count.val ≤ Usize.max) (hc1 : 1 ≤ count.val)
    (g : Nat → Array Vec2 → Id (ForInStep (Array Vec2)))
    (hg : ∀ i o, g i o = .yield (o.push (k0_25 * ((vS l.val)[2 * i - 1]! + k2 * (vS l.val)[2 * i]! + (vS l.val)[2 * i + 1]!)))) :
    ∀ (out : alloc.vec.Vec net.osutk.Vector2), out.val.length + count.val ≤ Usize.max →
    ∃ o', beatmap.path_approximator.bezier_approximate_loop2 out count l 1#usize = ok o' ∧
      vS o'.val = iterIdx g 1 (count.val - 1 - 1) (vS out.val) ∧ o'.val.length ≤ out.val.length + count.val := by
  intro out hout
  unfold beatmap.path_approximator.bezier_approximate_loop2
  obtain ⟨i1, hi1, hi1v⟩ := nat_sub_eq count 1#usize
  refine loop_iterIdx' _ g (count.val - 1)
    (fun (x : alloc.vec.Vec net.osutk.Vector2 × Usize) j (b : Array Vec2) =>
      x.2.val = j ∧ vS x.1.val = b ∧ 1 ≤ j ∧ x.1.val.length + count.val ≤ Usize.max + j - 1 ∧
      x.1.val.length + 1 = out.val.length + j ∧ j ≤ count.val)
    (fun (y : alloc.vec.Vec net.osutk.Vector2) (c : Array Vec2) => vS y.val = c ∧ y.val.length ≤ out.val.length + count.val)
    ?_ ?_ (out, 1#usize) 1 (vS out.val) ⟨by simp, rfl, le_refl _, by simp; omega, by simp, by omega⟩ rfl
  · rintro ⟨o, k⟩ kk b ⟨hj, hb, h1, hol, hlen1, hjc⟩ hk
    dsimp only at hj hb h1 hol hlen1 hjc
    subst hj hb
    left
    have hlt : k.val < i1.val := by simp at hi1v; omega
    obtain ⟨ix, hix, hixv⟩ := eq_ok_of_spec (Usize.mul_spec (x := 2#usize) (y := k) (by simp; omega))
    have hix2 : ix.val = 2 * k.val := by rw [hixv]; simp
    obtain ⟨ia, hia, hiav⟩ := usize_sub_one ix (by omega)
    obtain ⟨ib, hib, hibv⟩ := usize_add_one ix (by omega)
    obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by omega)
    have ea : ia.val < l.val.length := by omega
    have ex : ix.val < l.val.length := by omega
    have eb : ib.val < l.val.length := by omega
    let p := bv2I ((((bv2S (l.val[ia.val]'ea)).add ((bv2S (l.val[ix.val]'ex)).scale k2)).add (bv2S (l.val[ib.val]'eb))).scale k0_25)
    have hlt' : k < i1 := hlt
    obtain ⟨o1, ho1, ho1v⟩ := push_eq o p (by omega)
    refine ⟨_, hg _ _, (o1, k1), ?_, by simp [hk1v], ?_, by omega, by dsimp only; rw [ho1v]; simp; omega,
      by rw [ho1v]; simp; omega, by omega⟩
    · simp only [beatmap.path_approximator.bezier_approximate_loop2.body, hi1, hlt', bind_ok, hix, hia, hib, hk1,
        vec_index_eq' l ia ea, vec_index_eq' l ix ex, vec_index_eq' l ib eb, pa_K2, pa_K0_25, decide_true, ite_true,
        beatmap.vector2.scale_refines, beatmap.vector2.add_refines, bv2S_I]
      simp [p] at ho1; simp [ho1]
    · dsimp only
      rw [ho1v]
      rw [vS_push, vS_get! _ _ (by omega : 2 * k.val - 1 < l.val.length), vS_get! _ _ (by omega : 2 * k.val < l.val.length),
        vS_get! _ _ (by omega : 2 * k.val + 1 < l.val.length)]
      simp only [p, bv2S_I]
      have e1 : 2 * k.val - 1 = ia.val := by omega
      have e2 : 2 * k.val = ix.val := by omega
      have e3 : 2 * k.val + 1 = ib.val := by omega
      simp only [e1]; simp only [e3]; simp only [e2]; rfl
  · rintro ⟨o, k⟩ kk b ⟨hj, hb, h1, hol, hlen1, hjc⟩ hk
    dsimp only at hj hb h1 hol hlen1 hjc
    subst hj hb
    have hlt : ¬ k.val < i1.val := by simp at hi1v; omega
    exact ⟨o, by simp [beatmap.path_approximator.bezier_approximate_loop2.body, hi1, hlt], rfl, by omega⟩

theorem beatmap.path_approximator.bezier_approximate_refines (cp : Slice net.osutk.Vector2)
    (output : alloc.vec.Vec net.osutk.Vector2) (count : Usize)
    (hc1 : 1 ≤ count.val) (hc : count.val ≤ cp.val.length) (h2 : 2 * count.val ≤ Usize.max)
    (hout : output.val.length + count.val < Usize.max) :
    ∃ v, beatmap.path_approximator.bezier_approximate cp output count = ok v ∧
      vS v.val = bezierApproximate (vS cp.val) (vS output.val) count.val ∧
      v.val.length ≤ output.val.length + count.val + 1 := by
  obtain ⟨⟨l0, r⟩, hres, hresv, hl0, hr⟩ := beatmap.path_approximator.bezier_subdivide_refines cp count hc
  dsimp only at hresv hl0 hr
  obtain ⟨l1, hl1, hl1v⟩ := ba_loop0 count l0 0#usize (by simp; omega)
  have hl1l : l1.val.length = 2 * count.val - 1 := by rw [hl1v]; simp; omega
  obtain ⟨l2, hl2, hl2v, hl2l⟩ := ba_loop1 count r hr _ (fun _ _ => rfl) l1 hl1l
  obtain ⟨v0, hv0, hv0'⟩ := slice_get cp 0#usize 0 (by simp) (by omega)
  obtain ⟨o1, ho1, ho1v⟩ := push_eq output v0 (by omega)
  obtain ⟨o2, ho2, ho2v, ho2l⟩ := ba_loop2 count l2 hl2l h2 hc1 _ (fun _ _ => rfl) o1 (by rw [ho1v]; simp; omega)
  refine ⟨o2, ?_, ?_, by rw [ho1v] at ho2l; simp at ho2l; omega⟩
  · simp only [beatmap.path_approximator.bezier_approximate, hres, bind_ok, hv0, ho1]
    simp [hl1, hl2, ho2]
  · rw [ho2v]
    unfold bezierApproximate
    rw [← hresv]
    simp only [Id.run_bind, forIn_range_idx, id_run_eq]
    rw [hl2v, ho1v, vS_push, hv0', hl1v]
    have e : vS (l0.val ++ List.replicate (count.val - 1 - (0#usize).val) (bv2I Vec2.zero)) =
        vS l0.val ++ Array.replicate (count.val - 1) Vec2.zero := by
      simp [vS, bv2S, bv2I, Vec2.zero]
    rw [e]
    rfl

theorem usize_hcast_i64 (x : Usize) (h : x.val < 2^62) : (UScalar.hcast .I64 x).val = (x.val : Int) := by
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by simp) (by simp; omega)

theorem bsb_loop3 (degree point_count i j : Usize) (P D : Nat) (hP : point_count.val = P) (hD : degree.val = D)
    (hDP : D ≤ P) (hi : i.val < P - D) (hj : j.val < D - 1) (hP62 : P < 2^62)
    (g : Nat → Array Vec2 → Id (ForInStep (Array Vec2)))
    (hg : ∀ k p, g k p = .yield (p.set! (i.val + k) ((p[i.val + k]! * F32.ofInt ↑(min k (P - D - i.val)) + p[i.val + k + 1]!)
      / F32.ofInt (↑(min k (P - D - i.val)) + 1)))) :
    ∀ (pts : alloc.vec.Vec net.osutk.Vector2), pts.val.length = P + 1 →
    ∃ pts', beatmap.path_approximator.b_spline_to_bezier_internal_loop0_loop0_loop0 degree point_count pts i j 1#usize = ok pts' ∧
      vS pts'.val = iterIdx g 1 (D - j.val - 1) (vS pts.val) ∧ pts'.val.length = P + 1 := by
  intro pts hpts
  unfold beatmap.path_approximator.b_spline_to_bezier_internal_loop0_loop0_loop0
  obtain ⟨i1, hi1, hi1v⟩ := nat_sub_eq degree j
  obtain ⟨i2, hi2, hi2v⟩ := nat_sub_eq point_count degree
  obtain ⟨lim, hlim, hlimv⟩ := nat_sub_eq i2 i
  refine loop_iterIdx' _ g (D - j.val)
    (fun (x : alloc.vec.Vec net.osutk.Vector2 × Usize) k (b : Array Vec2) =>
      x.2.val = k ∧ vS x.1.val = b ∧ x.1.val.length = P + 1 ∧ 1 ≤ k)
    (fun (y : alloc.vec.Vec net.osutk.Vector2) (c : Array Vec2) => vS y.val = c ∧ y.val.length = P + 1)
    ?_ ?_ (pts, 1#usize) 1 (vS pts.val) ⟨by simp, rfl, hpts, le_refl _⟩ rfl
  · rintro ⟨m, k⟩ kk b ⟨hk, hb, hml, hk1⟩ hkk
    dsimp only at hk hb hml hk1
    subst hk hb
    left
    have hmm := alloc.vec.Vec.property m
    have hlt : k.val < i1.val := by omega
    have hlt' : k < i1 := hlt
    let l : Usize := if k.val < lim.val then k else lim
    have hl : l.val = min k.val (P - D - i.val) := by
      simp only [l]; split <;> omega
    have hlc : (if k < lim then ok k else ok lim : Result Usize) = ok l := by
      simp only [l]; split <;> simp_all
    obtain ⟨i4, hi4, hi4v⟩ := eq_ok_of_spec (Usize.add_spec (x := i) (y := k) (by omega))
    obtain ⟨i5, hi5, hi5v⟩ := usize_add_one i4 (by omega)
    obtain ⟨i6, hi6, hi6v⟩ := usize_add_one l (by omega)
    obtain ⟨k1, hk1e, hk1v⟩ := usize_add_one k (by omega)
    have e4 : i4.val < m.val.length := by omega
    have e5 : i5.val < m.val.length := by omega
    refine ⟨_, hg _ _, (alloc.vec.Vec.set m i4 (bv2I ((bv2S (m.val[i4.val]'e4) * F32.ofInt ↑l.val + bv2S (m.val[i5.val]'e5))
      / F32.ofInt ↑i6.val)), k1), ?_, ?_⟩
    · simp only [beatmap.path_approximator.b_spline_to_bezier_internal_loop0_loop0_loop0.body, hi1, hi2, hlim,
        bind_ok, hlc, hi4, hi5, hi6, hk1e, vec_index_eq' m i4 e4, vec_index_eq' m i5 e5, vec_index_mut_eq m i4 e4,
        lift, float.F32.from_i64, usize_hcast_i64 l (by omega), usize_hcast_i64 i6 (by omega),
        beatmap.vector2.scale_refines, beatmap.vector2.add_refines, beatmap.vector2.div_refines, bv2S_I, hlt', ite_true]
      rfl
    · refine ⟨by simp [hk1v], ?_, by simp [hml], by omega⟩
      dsimp only
      rw [alloc.vec.Vec.set_val_eq, vS_set, bv2S_I, vS_get! _ _ (by omega : i.val + k.val < m.val.length),
        vS_get! _ _ (by omega : i.val + k.val + 1 < m.val.length), hi6v, hl]
      have e4' : i4.val = i.val + k.val := hi4v
      have e5' : i5.val = i.val + k.val + 1 := by omega
      simp only [e4', e5']
      push_cast; rfl
  · rintro ⟨m, k⟩ kk b ⟨hk, hb, hml, hk1⟩ hkk
    dsimp only at hk hb hml hk1
    subst hk hb
    have hlt : ¬ k.val < i1.val := by omega
    exact ⟨m, by simp [beatmap.path_approximator.b_spline_to_bezier_internal_loop0_loop0_loop0.body, hi1, hlt], rfl, hml⟩

theorem bsb_loop2 (degree point_count i : Usize) (P D : Nat) (hP : point_count.val = P) (hD : degree.val = D)
    (hDP : D ≤ P) (hi : i.val < P - D) (hP62 : P < 2^62)
    (g3 : Nat → Array Vec2 → Id (ForInStep (Array Vec2)))
    (hg3 : ∀ k p, g3 k p = .yield (p.set! (i.val + k) ((p[i.val + k]! * F32.ofInt ↑(min k (P - D - i.val)) + p[i.val + k + 1]!)
      / F32.ofInt (↑(min k (P - D - i.val)) + 1))))
    (g2 : Nat → Array Vec2 × Array Vec2 → Id (ForInStep (Array Vec2 × Array Vec2)))
    (hg2 : ∀ j s, g2 j s = .yield (iterIdx g3 1 (D - j - 1) s.1, s.2.set! (j + 1) s.1[i.val + 1]!)) :
    ∀ (pts sub : alloc.vec.Vec net.osutk.Vector2), pts.val.length = P + 1 → sub.val.length = D + 1 →
    ∃ res, beatmap.path_approximator.b_spline_to_bezier_internal_loop0_loop0 degree point_count pts i sub 0#usize = ok res ∧
      (vS res.1.val, vS res.2.val) = iterIdx g2 0 (D - 1 - 0) (vS pts.val, vS sub.val) ∧
      res.1.val.length = P + 1 ∧ res.2.val.length = D + 1 := by
  intro pts sub hpts hsub
  unfold beatmap.path_approximator.b_spline_to_bezier_internal_loop0_loop0
  obtain ⟨i1, hi1, hi1v⟩ := nat_sub_eq degree 1#usize
  refine loop_iterIdx' _ g2 (D - 1)
    (fun (x : alloc.vec.Vec net.osutk.Vector2 × alloc.vec.Vec net.osutk.Vector2 × Usize) j (b : Array Vec2 × Array Vec2) =>
      x.2.2.val = j ∧ vS x.1.val = b.1 ∧ vS x.2.1.val = b.2 ∧ x.1.val.length = P + 1 ∧ x.2.1.val.length = D + 1)
    (fun (y : alloc.vec.Vec net.osutk.Vector2 × alloc.vec.Vec net.osutk.Vector2) (c : Array Vec2 × Array Vec2) =>
      (vS y.1.val, vS y.2.val) = c ∧ y.1.val.length = P + 1 ∧ y.2.val.length = D + 1)
    ?_ ?_ (pts, sub, 0#usize) 0 (vS pts.val, vS sub.val) ⟨by simp, rfl, rfl, hpts, hsub⟩ rfl
  · rintro ⟨m, sb, j⟩ jj ⟨b1, b2⟩ ⟨hj, hb1, hb2, hml, hsl⟩ hjj
    dsimp only at hj hb1 hb2 hml hsl
    subst hj hb1 hb2
    left
    have hlt : j.val < i1.val := by simp at hi1v; omega
    have hlt' : j < i1 := hlt
    obtain ⟨i2, hi2, hi2v⟩ := usize_add_one i (by have := alloc.vec.Vec.property m; omega)
    obtain ⟨i3, hi3, hi3v⟩ := usize_add_one j (by have := alloc.vec.Vec.property sb; omega)
    have e2 : i2.val < m.val.length := by omega
    have e3 : i3.val < sb.val.length := by omega
    obtain ⟨m', hm', hm'v, hm'l⟩ := bsb_loop3 degree point_count i j P D hP hD hDP hi (by omega) hP62 g3 hg3 m hml
    refine ⟨_, hg2 _ _, (m', alloc.vec.Vec.set sb i3 (m.val[i2.val]'e2), i3), ?_, ?_⟩
    · simp only [beatmap.path_approximator.b_spline_to_bezier_internal_loop0_loop0.body, hi1, bind_ok, hlt', ite_true,
        hi2, vec_index_eq' m i2 e2, hi3, vec_index_mut_eq sb i3 e3, hm']
      rfl
    · refine ⟨by simp [hi3v], hm'v, ?_, hm'l, by simp [hsl]⟩
      dsimp only
      rw [alloc.vec.Vec.set_val_eq, vS_set, vS_get! _ _ (by omega : i.val + 1 < m.val.length)]
      have e2' : i2.val = i.val + 1 := hi2v
      have e3' : i3.val = j.val + 1 := hi3v
      simp only [e2', e3']
  · rintro ⟨m, sb, j⟩ jj ⟨b1, b2⟩ ⟨hj, hb1, hb2, hml, hsl⟩ hjj
    dsimp only at hj hb1 hb2 hml hsl
    subst hj hb1 hb2
    have hlt : ¬ j.val < i1.val := by simp at hi1v; omega
    exact ⟨(m, sb), by simp [beatmap.path_approximator.b_spline_to_bezier_internal_loop0_loop0.body, hi1, hlt], rfl, hml, hsl⟩

/-- Spec-side loop bodies of `bSplineToBezierInternal` (definitionally the spec's `for` bodies). -/
def bsbG3 (P D i : Nat) : Nat → Array Vec2 → Id (ForInStep (Array Vec2)) := fun k p =>
  .yield (p.set! (i + k) ((p[i + k]! * F32.ofInt ↑(min k (P - D - i)) + p[i + k + 1]!) / F32.ofInt (↑(min k (P - D - i)) + 1)))
def bsbG2 (P D i : Nat) : Nat → Array Vec2 × Array Vec2 → Id (ForInStep (Array Vec2 × Array Vec2)) := fun j s =>
  .yield (iterIdx (bsbG3 P D i) 1 (D - j - 1) s.1, s.2.set! (j + 1) s.1[i + 1]!)
def bsbG1 (P D : Nat) : Nat → Array Vec2 × Array (Array Vec2) → Id (ForInStep (Array Vec2 × Array (Array Vec2))) :=
  fun i s =>
    let r := iterIdx (bsbG2 P D i) 0 (D - 1 - 0) (s.1, (Array.replicate (D + 1) Vec2.zero).set! 0 s.1[i]!)
    .yield (r.1, s.2.push (r.2.set! D r.1[i + 1]!))

def vvS (l : List (alloc.vec.Vec net.osutk.Vector2)) : Array (Array Vec2) := (l.map (fun v => vS v.val)).toArray

theorem bsb_loop1 (degree point_count : Usize) (P D : Nat) (hP : point_count.val = P) (hD : degree.val = D)
    (hDP : D < P) (hP62 : P < 2^62) :
    ∀ (pts : alloc.vec.Vec net.osutk.Vector2) (res : alloc.vec.Vec (alloc.vec.Vec net.osutk.Vector2)),
    pts.val.length = P + 1 → res.val.length = 0 →
    ∃ out, beatmap.path_approximator.b_spline_to_bezier_internal_loop0 degree point_count pts res 0#usize = ok out ∧
      (vS out.1.val, vvS out.2.val) = iterIdx (bsbG1 P D) 0 (P - D - 0) (vS pts.val, vvS res.val) ∧
      out.1.val.length = P + 1 ∧ out.2.val.length = P - D ∧ ∀ s ∈ out.2.val, s.val.length = D + 1 := by
  intro pts res hpts hres
  unfold beatmap.path_approximator.b_spline_to_bezier_internal_loop0
  obtain ⟨i1, hi1, hi1v⟩ := nat_sub_eq point_count degree
  refine loop_iterIdx' _ (bsbG1 P D) (P - D)
    (fun (x : alloc.vec.Vec net.osutk.Vector2 × alloc.vec.Vec (alloc.vec.Vec net.osutk.Vector2) × Usize) i
      (b : Array Vec2 × Array (Array Vec2)) =>
      x.2.2.val = i ∧ vS x.1.val = b.1 ∧ vvS x.2.1.val = b.2 ∧ x.1.val.length = P + 1 ∧ x.2.1.val.length = i ∧ i ≤ P - D ∧ ∀ s ∈ x.2.1.val, s.val.length = D + 1)
    (fun (y : alloc.vec.Vec net.osutk.Vector2 × alloc.vec.Vec (alloc.vec.Vec net.osutk.Vector2))
      (c : Array Vec2 × Array (Array Vec2)) =>
      (vS y.1.val, vvS y.2.val) = c ∧ y.1.val.length = P + 1 ∧ y.2.val.length = P - D ∧ ∀ s ∈ y.2.val, s.val.length = D + 1)
    ?_ ?_ (pts, res, 0#usize) 0 (vS pts.val, vvS res.val) ⟨by simp, rfl, rfl, hpts, by simp [hres], by omega, by simp [List.eq_nil_of_length_eq_zero hres]⟩ rfl
  · rintro ⟨m, rs, i⟩ ii ⟨b1, b2⟩ ⟨hi, hb1, hb2, hml, hrl, hiPD, hall⟩ hii
    dsimp only at hi hb1 hb2 hml hrl
    subst hi hb1 hb2
    left
    have hlt : i.val < i1.val := by omega
    have hlt' : i < i1 := hlt
    have hmm := alloc.vec.Vec.property m
    obtain ⟨d1, hd1, hd1v⟩ := usize_add_one degree (by omega)
    obtain ⟨z, hz, hzv⟩ := beatmap.path_approximator.replicate_zero_refines d1
    have hzl : z.val.length = D + 1 := by rw [← vS_length, hzv]; simp; omega
    have e0 : i.val < m.val.length := by omega
    have ez : (0#usize).val < z.val.length := by simp; omega
    obtain ⟨⟨m', sb'⟩, hlp, hlpv, hm'l, hsb'l⟩ := bsb_loop2 degree point_count i P D hP hD (by omega) (by omega) hP62
      (bsbG3 P D i.val) (fun _ _ => rfl) (bsbG2 P D i.val) (fun _ _ => rfl) m
      (alloc.vec.Vec.set z 0#usize (m.val[i.val]'e0)) hml (by simp [hzl])
    dsimp only at hlpv hm'l hsb'l
    obtain ⟨i3, hi3, hi3v⟩ := usize_add_one i (by omega)
    have e3 : i3.val < m'.val.length := by omega
    have ed : degree.val < sb'.val.length := by omega
    obtain ⟨rs1, hrs1, hrs1v⟩ := push_eq rs (alloc.vec.Vec.set sb' degree (m'.val[i3.val]'e3)) (by
      have := alloc.vec.Vec.property m; omega)
    refine ⟨_, rfl, (m', rs1, i3), ?_, ?_⟩
    · simp only [beatmap.path_approximator.b_spline_to_bezier_internal_loop0.body, hi1, bind_ok, hlt', ite_true,
        hd1, hz, vec_index_eq' m i e0, vec_index_mut_eq z 0#usize ez, uncurry_apply_pair, hlp, hi3,
        vec_index_eq' m' i3 e3, vec_index_mut_eq sb' degree ed, hrs1]
    · have hz' : vS (alloc.vec.Vec.set z 0#usize (m.val[i.val]'e0)).val =
          (Array.replicate (D + 1) Vec2.zero).set! 0 (vS m.val)[i.val]! := by
        rw [alloc.vec.Vec.set_val_eq, vS_set, hzv, vS_get! _ _ e0, hd1v, hD]; rfl
      rw [hz'] at hlpv
      simp only [bsbG1]
      rw [← hlpv]
      refine ⟨by simp [hi3v], rfl, ?_, hm'l, by simp [hrs1v, hrl], by omega, ?_⟩
      swap
      · intro s hs; rw [hrs1v] at hs; simp at hs
        rcases hs with hs | hs
        · exact hall s hs
        · subst hs; simp [hsb'l]
      dsimp only
      rw [hrs1v]
      simp only [vvS, List.map_append, List.map_cons, List.map_nil]
      rw [List.push_toArray]
      congr 3
      rw [alloc.vec.Vec.set_val_eq, vS_set, vS_get! _ _ (show i.val + 1 < m'.val.length by omega), hD]
      simp only [hi3v]
  · rintro ⟨m, rs, i⟩ ii ⟨b1, b2⟩ ⟨hi, hb1, hb2, hml, hrl, hiPD, hall⟩ hii
    dsimp only at hi hb1 hb2 hml hrl
    subst hi hb1 hb2
    have hlt : ¬ i.val < i1.val := by omega
    exact ⟨(m, rs), by simp [beatmap.path_approximator.b_spline_to_bezier_internal_loop0.body, hi1, hlt], rfl, hml,
      by dsimp only; omega, hall⟩

theorem beatmap.path_approximator.b_spline_to_bezier_internal_refines (cp : Slice net.osutk.Vector2) (degree0 : Usize)
    (hlen : cp.val.length < 2^62) :
    ∃ res, beatmap.path_approximator.b_spline_to_bezier_internal cp degree0 = ok res ∧
      (vvS res.1.val, res.2.val) = bSplineToBezierInternal (vS cp.val) degree0.val ∧
      res.2.val ≤ cp.val.length - 1 ∧ res.1.val.length ≤ cp.val.length + 1 ∧ (1 ≤ cp.val.length → ∀ s ∈ res.1.val, s.val.length = res.2.val + 1) := by
  obtain ⟨pc, hpc, hpcv⟩ := nat_sub_eq (Slice.len cp) 1#usize
  have hpcv' : pc.val = cp.val.length - 1 := by simp [Slice.length] at hpcv; omega
  obtain ⟨pts, hpts, hptsv⟩ := beatmap.path_approximator.extract_refines cp 0#usize (Slice.len cp)
  simp only [Slice.len_val, List.take_length] at hptsv
  have hpts' : pts.val = cp.val := by rw [hptsv]; simp
  have hd : (if degree0 < pc then ok degree0 else ok pc : Result Usize) = ok (if degree0.val < pc.val then degree0 else pc) := by
    split <;> simp_all
  have hdv : (if degree0.val < pc.val then degree0 else pc).val = min degree0.val (cp.val.length - 1) := by
    split <;> omega
  generalize hdg : (if degree0.val < pc.val then degree0 else pc) = dg at hd hdv
  unfold beatmap.path_approximator.b_spline_to_bezier_internal bSplineToBezierInternal
  simp only [hpc, bind_ok, hd, hpts, vS_size]
  by_cases he : dg = pc
  · have he' : (min degree0.val (cp.val.length - 1) == cp.val.length - 1) = true := by
      rw [← hdv, he, hpcv']; simp
    simp only [he, ite_true, he', id_run_eq]
    obtain ⟨r, hr, hrv⟩ := push_eq (alloc.vec.Vec.new (alloc.vec.Vec net.osutk.Vector2)) pts (by simp; have := usize_ge_32; omega)
    refine ⟨(r, pc), by simp [hr], ?_, by dsimp only; omega, by simp [hrv], ?_⟩
    · simp [hrv, vvS, hpts', hdv, ← he]
      rfl
    · intro h1 s hs; simp [hrv] at hs; subst hs; simp [hpts', hpcv']; omega
  · have he' : (min degree0.val (cp.val.length - 1) == cp.val.length - 1) = false := by
      have : dg.val ≠ pc.val := fun h => he (UScalar.eq_of_val_eq h)
      rw [← hdv, ← hpcv']; simpa using this
    have hDP : dg.val < pc.val := by
      have : dg.val ≠ pc.val := fun h => he (UScalar.eq_of_val_eq h)
      omega
    simp only [he, ite_false, he', Bool.false_eq_true, id_run_eq]
    obtain ⟨⟨p1, rs⟩, hl, hlv, hp1l, hrsl, hall⟩ := bsb_loop1 dg pc pc.val dg.val rfl rfl hDP (by omega) pts
      (alloc.vec.Vec.new _) (by rw [hpts']; omega) (by simp)
    dsimp only at hlv hp1l hrsl hall
    obtain ⟨i2, hi2, hi2v⟩ := nat_sub_eq pc dg
    obtain ⟨v, hv, hvv⟩ := beatmap.path_approximator.extract_refines (alloc.vec.Vec.deref p1) i2 (alloc.vec.Vec.len p1)
    obtain ⟨r, hr, hrv⟩ := push_eq rs v (by have := alloc.vec.Vec.property p1; omega)
    refine ⟨(r, dg), by simp only [hl, bind_ok, uncurry_apply_pair, hi2, hv, hr], ?_, by dsimp only; omega, by dsimp only; rw [hrv]; simp; omega, ?_⟩
    swap
    · intro _ s hs; simp [hrv] at hs
      rcases hs with hs | hs
      · exact hall s hs
      · subst hs; simp [hvv, alloc.vec.Vec.deref, hp1l, hi2v]; omega
    simp only [forIn_range_idx, Id.run_bind]
    rw [hpts'] at hlv
    generalize hS : iterIdx _ 0 _ (vS cp.val, #[]) = S
    have hS' : iterIdx (bsbG1 pc.val dg.val) 0 (pc.val - dg.val - 0) (vS cp.val, vvS (alloc.vec.Vec.new (alloc.vec.Vec net.osutk.Vector2)).val) = S := by
      rw [hpcv', hdv]; exact hS
    rw [← hS', ← hlv]
    simp only [id_bind_eq', id_pure_eq, hrv, vvS, List.map_append, List.map_cons, List.map_nil, hvv]
    rw [← List.push_toArray, ← hpcv']
    have hm : min degree0.val pc.val = dg.val := by omega
    rw [hm]
    congr 2
    rw [vS_extract]
    simp [hi2v, alloc.vec.Vec.deref, hp1l]

theorem vec2_vec_clone (v : alloc.vec.Vec net.osutk.Vector2) :
    alloc.vec.CloneVec.clone net.osutk.Vector2.Insts.CoreCloneClone v = ok v := by
  obtain ⟨s, hs, hsv⟩ := eq_ok_of_spec (Slice.clone_spec (clone := net.osutk.Vector2.Insts.CoreCloneClone.clone)
    (s := v.slice) (by intro x _; rfl))
  simp only [alloc.vec.CloneVec.clone, net.osutk.Vector2.Insts.CoreCloneClone, hs, bind_ok, ← hsv]
  rw [bind_tc_ok]

theorem bsp_loop0 (segs : alloc.vec.Vec (alloc.vec.Vec net.osutk.Vector2)) :
    ∀ (tf : alloc.vec.Vec (alloc.vec.Vec net.osutk.Vector2)) (s : Usize), s.val ≤ segs.val.length →
      tf.val = (segs.val.drop s.val).reverse →
    ∃ tf', beatmap.path_approximator.b_spline_to_piecewise_linear_loop0 segs tf s = ok tf' ∧ tf'.val = segs.val.reverse := by
  intro tf s hs htf
  unfold beatmap.path_approximator.b_spline_to_piecewise_linear_loop0
  have H := loop_ok (fun (x : alloc.vec.Vec (alloc.vec.Vec net.osutk.Vector2) × Usize) =>
      beatmap.path_approximator.b_spline_to_piecewise_linear_loop0.body segs x.1 x.2) (fun x => x.2.val)
    (fun x => x.2.val ≤ segs.val.length ∧ x.1.val = (segs.val.drop x.2.val).reverse)
    (fun (v : alloc.vec.Vec (alloc.vec.Vec net.osutk.Vector2)) => v.val = segs.val.reverse) (by
      rintro ⟨out, j⟩ ⟨h1, h2⟩
      dsimp only at h1 h2 ⊢
      by_cases hc : 0 < j.val
      · right
        have hc' : j > 0#usize := by show (0#usize).val < j.val; simpa using hc
        obtain ⟨j1, hj1, hj1v⟩ := usize_sub_one j hc
        have ej : j1.val < segs.val.length := by omega
        have hb : out.val.length < Usize.max := by
          rw [h2]; simp; have := alloc.vec.Vec.property segs; omega
        obtain ⟨o1, ho1, ho1v⟩ := push_eq out (segs.val[j1.val]'ej) hb
        refine ⟨(o1, j1), ?_, ⟨by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
        · simp [beatmap.path_approximator.b_spline_to_piecewise_linear_loop0.body, hc', hj1, vec_index_usize_eq segs j1 ej,
            vec2_vec_clone, ho1]
        · dsimp only; rw [ho1v, h2]
          rw [List.drop_eq_getElem_cons (by omega : j1.val < segs.val.length)]
          have : j1.val + 1 = j.val := by omega
          simp [this]
      · left
        have hc' : ¬ j > 0#usize := by show ¬ (0#usize).val < j.val; simpa using hc
        refine ⟨out, by simp [beatmap.path_approximator.b_spline_to_piecewise_linear_loop0.body, hc'], ?_⟩
        rw [h2]; have : j.val = 0 := by omega
        simp [this])
    (tf, s) ⟨hs, htf⟩
  exact H

theorem usize_max64 (h : System.Platform.numBits = 64) : Usize.max = 2^64 - 1 := by
  rw [Usize.max_def]; simp [Usize.numBits, h]

/-- The spec's flattening-loop body of `bSplineToPiecewiseLinear` (definitionally the spec's `for` body). -/
def bspBody (D : Nat) (b : Array (Array Vec2) × Array Vec2) : ForInStep (Array (Array Vec2) × Array Vec2) :=
  if (b.1.size == 0) = true then .done (b.1, b.2)
  else
    if bezierIsFlatEnough b.1.back! = true then .yield (b.1.pop, bezierApproximate b.1.back! b.2 (D + 1))
    else match bezierSubdivide b.1.back! (D + 1) with
      | (l, r) => .yield ((b.1.pop.push r).push (l.extract 0 (D + 1)), b.2)

theorem vvS_size (l : List (alloc.vec.Vec net.osutk.Vector2)) : (vvS l).size = l.length := by simp [vvS]
theorem vvS_back (l : List (alloc.vec.Vec net.osutk.Vector2)) (h : l ≠ []) :
    (vvS l).back! = vS (l.getLast h).val := by
  have : l.length - 1 < l.length := by have := List.length_pos_of_ne_nil h; omega
  simp [vvS, Array.back!, List.getLast_eq_getElem, List.getElem?_eq_getElem this]
theorem vvS_pop (l : List (alloc.vec.Vec net.osutk.Vector2)) : (vvS l).pop = vvS l.dropLast := by
  simp [vvS, List.map_dropLast]
theorem vvS_push (l : List (alloc.vec.Vec net.osutk.Vector2)) (v : alloc.vec.Vec net.osutk.Vector2) :
    vvS (l ++ [v]) = (vvS l).push (vS v.val) := by simp [vvS]

theorem deref_val {α} (v : alloc.vec.Vec α) : (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref]

theorem mul_bound (i D : Nat) (hi : i ≤ 100000000) (hD : D < 2^32) : i * (D + 2) ≤ 100000000 * (2^32 + 2) :=
  Nat.mul_le_mul hi (by omega)

theorem bsp_loop1 (degree : Usize) (D : Nat) (hD : degree.val = D) (h64 : System.Platform.numBits = 64)
    (hD32 : D < 2^32) (f : Nat → Array (Array Vec2) × Array Vec2 → Id (ForInStep (Array (Array Vec2) × Array Vec2)))
    (hf : ∀ i b, f i b = bspBody D b) (tf0 : alloc.vec.Vec (alloc.vec.Vec net.osutk.Vector2))
    (htf0 : ∀ s ∈ tf0.val, s.val.length = D + 1) (htf0l : tf0.val.length ≤ 2^33) :
    ∃ y, beatmap.path_approximator.b_spline_to_piecewise_linear_loop1 degree tf0
        (alloc.vec.Vec.new net.osutk.Vector2) 0#u64 = ok y ∧
      vvS y.1.val = (iterIdx f 0 (100000000 - 0) (vvS tf0.val, #[])).1 ∧
      vS y.2.val = (iterIdx f 0 (100000000 - 0) (vvS tf0.val, #[])).2 ∧ y.2.val.length ≤ 100000000 * (2^32 + 2) := by
  have hmax := usize_max64 h64
  unfold beatmap.path_approximator.b_spline_to_piecewise_linear_loop1
  refine loop_iterIdx' _ f 100000000
    (fun (x : alloc.vec.Vec (alloc.vec.Vec net.osutk.Vector2) × alloc.vec.Vec net.osutk.Vector2 × U64) i
      (b : Array (Array Vec2) × Array Vec2) =>
      x.2.2.val = i ∧ vvS x.1.val = b.1 ∧ vS x.2.1.val = b.2 ∧ (∀ s ∈ x.1.val, s.val.length = D + 1) ∧
      x.1.val.length ≤ 2^33 + i ∧ x.2.1.val.length ≤ i * (D + 2) ∧ i ≤ 100000000)
    (fun (y : alloc.vec.Vec (alloc.vec.Vec net.osutk.Vector2) × alloc.vec.Vec net.osutk.Vector2)
      (c : Array (Array Vec2) × Array Vec2) => vvS y.1.val = c.1 ∧ vS y.2.val = c.2 ∧ y.2.val.length ≤ 100000000 * (2^32 + 2))
    ?_ ?_ (tf0, alloc.vec.Vec.new _, 0#u64) 0 (vvS tf0.val, #[])
    ⟨by simp, rfl, by simp [vS], htf0, by omega, by simp, by omega⟩ rfl
  · rintro ⟨tf, out, fu⟩ i ⟨b1, b2⟩ ⟨hi, hb1, hb2, hall, htl, hol, hi8⟩ hilt
    dsimp only at hi hb1 hb2 hall htl hol hi8
    subst hb1 hb2
    rw [hf]
    by_cases he : tf.val = []
    · right
      have hsz : ((vvS tf.val).size == 0) = true := by simp [vvS_size, he]
      refine ⟨(vvS tf.val, vS out.val), by simp only [bspBody, hsz, ite_true], (tf, out), ?_, rfl, rfl,
        by dsimp only; have := mul_bound i D hi8 hD32; omega⟩
      rw [loop_unfold]
      have hl : ¬ (alloc.vec.Vec.len tf) > 0#usize := by
        show ¬ (0#usize).val < (alloc.vec.Vec.len tf).val; simp [he]
      simp [beatmap.path_approximator.b_spline_to_piecewise_linear_loop1.body, hl]
    · left
      have hsz : ((vvS tf.val).size == 0) = false := by simp [vvS_size, he]
      have hpm : tf.val.getLast he ∈ tf.val := List.getLast_mem he
      have hpl : (tf.val.getLast he).val.length = D + 1 := hall _ hpm
      have hlen0 : 0 < tf.val.length := List.length_pos_of_ne_nil he
      have hl : (alloc.vec.Vec.len tf) > 0#usize := by
        show (0#usize).val < (alloc.vec.Vec.len tf).val; simp; omega
      have hfu : fu < 100000000#u64 := by show fu.val < (100000000#u64).val; simp; omega
      have hpop : alloc.vec.Vec.pop alloc.alloc.Global tf =
          ok (some (tf.val.getLast he), alloc.vec.Vec.from tf.val.dropLast
            (by have := alloc.vec.Vec.property tf; simp; omega)) := by
        simp [alloc.vec.Vec.pop, List.getLast?_eq_some_getLast he]
      obtain ⟨d1, hd1, hd1v⟩ := usize_add_one degree (by omega)
      obtain ⟨fu1, hfu1, hfu1v⟩ := eq_ok_of_spec (U64.add_spec (x := fu) (y := 1#u64) (by simp [U64.max_eq]; omega))
      have hflat := beatmap.path_approximator.bezier_is_flat_enough_refines (alloc.vec.Vec.deref (tf.val.getLast he))
      rw [deref_val] at hflat
      have hback := vvS_back tf.val he
      have hdrop : (alloc.vec.Vec.from tf.val.dropLast (by have := alloc.vec.Vec.property tf; simp; omega) :
          alloc.vec.Vec (alloc.vec.Vec net.osutk.Vector2)).val = tf.val.dropLast := by simp
      have hd1D : d1.val = D + 1 := by omega
      have hfl' : (alloc.vec.Vec.len tf) > 0#usize := hl
      by_cases hfl : bezierIsFlatEnough (vS (tf.val.getLast he).val) = true
      · obtain ⟨v, hv, hvv, hvl⟩ := beatmap.path_approximator.bezier_approximate_refines
          (alloc.vec.Vec.deref (tf.val.getLast he)) out d1 (by omega) (by rw [deref_val]; omega)
          (by rw [hmax]; omega) (by rw [hmax]; have := mul_bound i D hi8 hD32; omega)
        rw [deref_val] at hvv
        refine ⟨((vvS tf.val).pop, bezierApproximate (vvS tf.val).back! (vS out.val) (D + 1)), ?_,
          (alloc.vec.Vec.from tf.val.dropLast (by have := alloc.vec.Vec.property tf; simp; omega), v, fu1), ?_, ?_⟩
        · simp only [bspBody, hsz, hback, hfl]; rfl
        · simp only [beatmap.path_approximator.b_spline_to_piecewise_linear_loop1.body, hfl', hfu, ite_true, hpop,
            bind_ok, uncurry_apply_pair, hflat, hfl, hd1, hv, hfu1]
        · have hm : (i + 1) * (D + 2) = i * (D + 2) + (D + 2) := by ring
          refine ⟨by simp [hfu1v, hi], by rw [hdrop, vvS_pop], by rw [hvv, hback, hd1D], ?_, ?_, ?_, by omega⟩
          · intro s hs; rw [hdrop] at hs; exact hall s (List.mem_of_mem_dropLast hs)
          · rw [hdrop]; simp; omega
          · dsimp only; omega
      · obtain ⟨⟨lc, rc⟩, hsd, hsdv, hll, hrl⟩ := beatmap.path_approximator.bezier_subdivide_refines
          (alloc.vec.Vec.deref (tf.val.getLast he)) d1 (by rw [deref_val]; omega)
        rw [deref_val] at hsdv
        dsimp only at hsdv hll hrl
        have hfl2 : bezierIsFlatEnough (vS (tf.val.getLast he).val) = false := by simpa using hfl
        obtain ⟨t3, ht3, ht3v⟩ := push_eq (alloc.vec.Vec.from tf.val.dropLast
          (by have := alloc.vec.Vec.property tf; simp; omega) : alloc.vec.Vec (alloc.vec.Vec net.osutk.Vector2)) rc
          (by simp; rw [hmax]; omega)
        obtain ⟨e, hev, hevv⟩ := beatmap.path_approximator.extract_refines (alloc.vec.Vec.deref lc) 0#usize d1
        rw [deref_val] at hevv
        have hel : e.val = lc.val := by rw [hevv]; simp [List.take_of_length_le, hll]
        obtain ⟨t4, ht4, ht4v⟩ := push_eq t3 e (by rw [ht3v]; simp; rw [hmax]; omega)
        refine ⟨(((vvS tf.val).pop.push (vS rc.val)).push ((vS lc.val).extract 0 (D + 1)), vS out.val), ?_,
          (t4, out, fu1), ?_, ?_⟩
        · simp only [bspBody, hsz, hback, hfl2, Bool.false_eq_true, ite_false]
          rw [← hd1D, ← hsdv]
        · simp only [beatmap.path_approximator.b_spline_to_piecewise_linear_loop1.body, hfl', hfu, ite_true, hpop,
            bind_ok, uncurry_apply_pair, hflat, hfl2, hd1, hsd, ht3, hev, ht4, hfu1, Bool.false_eq_true, ite_false]
        · refine ⟨by simp [hfu1v, hi], ?_, rfl, ?_, ?_, ?_, by omega⟩
          · dsimp only
            rw [ht4v, ht3v, vvS_push, vvS_push, hdrop, vvS_pop, hel, vS_extract,
              List.take_of_length_le (by omega : lc.val.length ≤ D + 1)]
            simp
          · intro s hs; dsimp only at hs; rw [ht4v, ht3v] at hs; simp at hs
            rcases hs with hs | hs | hs
            · exact hall s (List.mem_of_mem_dropLast hs)
            · subst hs; omega
            · subst hs; rw [hel]; omega
          · dsimp only; rw [ht4v, ht3v]; simp; omega
          · dsimp only
            have : i * (D + 2) ≤ (i + 1) * (D + 2) := Nat.mul_le_mul_right _ (by omega)
            omega
  · rintro ⟨tf, out, fu⟩ i ⟨b1, b2⟩ ⟨hi, hb1, hb2, hall, htl, hol, hi8⟩ hilt
    dsimp only at hi hb1 hb2 hol
    subst hb1 hb2
    refine ⟨(tf, out), ?_, rfl, rfl, by dsimp only; have := mul_bound i D hi8 hD32; omega⟩
    have hfu : ¬ fu < 100000000#u64 := by show ¬ fu.val < (100000000#u64).val; simp; omega
    by_cases hl : (alloc.vec.Vec.len tf) > 0#usize
    · simp [beatmap.path_approximator.b_spline_to_piecewise_linear_loop1.body, hl, hfu]
    · simp [beatmap.path_approximator.b_spline_to_piecewise_linear_loop1.body, hl]

theorem vvS_reverse (l : List (alloc.vec.Vec net.osutk.Vector2)) : vvS l.reverse = (vvS l).reverse := by
  simp [vvS, List.map_reverse]

theorem beatmap.path_approximator.b_spline_to_piecewise_linear_refines (cp : Slice net.osutk.Vector2) (degree0 : Usize)
    (h64 : System.Platform.numBits = 64) (hlen : cp.val.length < 2^32) :
    ∃ v, beatmap.path_approximator.b_spline_to_piecewise_linear cp degree0 = ok v ∧
      (vS v.1.val, v.2) = bSplineToPiecewiseLinear (vS cp.val) degree0.val := by
  have hmax := usize_max64 h64
  unfold beatmap.path_approximator.b_spline_to_piecewise_linear bSplineToPiecewiseLinear
  by_cases h2 : cp.val.length < 2
  · have h2' : Slice.len cp < 2#usize := by show (Slice.len cp).val < (2#usize).val; simpa using h2
    simp only [h2', ite_true, vS_size, h2, decide_true, id_run_eq]
    by_cases h1 : cp.val.length = 1
    · have h1' : Slice.len cp = 1#usize := by apply UScalar.eq_of_val_eq; simpa using h1
      obtain ⟨a, ha, ha'⟩ := slice_get cp 0#usize 0 (by simp) (by omega)
      obtain ⟨o, ho, hov⟩ := push_eq (alloc.vec.Vec.new net.osutk.Vector2) a (by simp; omega)
      refine ⟨(o, false), by simp only [h1', ite_true, ha, bind_ok, ho], ?_⟩
      rw [hov, ha']; simp [h1, vS]; rfl
    · have h1' : ¬ Slice.len cp = 1#usize := fun h => h1 (by simpa using congrArg UScalar.val h)
      have h0 : cp.val.length = 0 := by omega
      refine ⟨(alloc.vec.Vec.new _, false), by simp only [h1', ite_false], ?_⟩
      simp [vS, h0]; rfl
  · have h2' : ¬ Slice.len cp < 2#usize := by show ¬ (Slice.len cp).val < (2#usize).val; simpa using h2
    simp only [h2', ite_false, vS_size, h2, decide_false, Bool.false_eq_true]
    obtain ⟨pc, hpc, hpcv⟩ := usize_sub_one (Slice.len cp) (by simp; omega)
    have hpcv' : pc.val = cp.val.length - 1 := by simp [Slice.length] at hpcv; omega
    have hd : (if degree0 < pc then ok degree0 else ok pc : Result Usize) = ok (if degree0.val < pc.val then degree0 else pc) := by
      split <;> simp_all
    have hdv : (if degree0.val < pc.val then degree0 else pc).val = min degree0.val (cp.val.length - 1) := by
      split <;> omega
    generalize hdg : (if degree0.val < pc.val then degree0 else pc) = d1 at hd hdv
    obtain ⟨⟨segs, dg⟩, hb, hbv, hdgl, hsegn, hsegl⟩ := beatmap.path_approximator.b_spline_to_bezier_internal_refines cp d1 (by omega)
    dsimp only at hbv hdgl hsegn hsegl
    rw [hdv] at hbv
    rw [← hbv]
    obtain ⟨tf, htf, htfv⟩ := bsp_loop0 segs (alloc.vec.Vec.with_capacity _ (alloc.vec.Vec.len segs)) (alloc.vec.Vec.len segs)
      (by simp) (by simp [alloc.vec.Vec.with_capacity])
    have hall : ∀ s ∈ tf.val, s.val.length = dg.val + 1 := by
      intro s hs; rw [htfv, List.mem_reverse] at hs; exact hsegl (by omega) s hs
    obtain ⟨⟨tf2, out⟩, hout, houtv1, houtv2, houtl⟩ := bsp_loop1 dg dg.val rfl h64 (by omega) _ (fun _ _ => rfl) tf hall
      (by rw [htfv, List.length_reverse]; omega)
    dsimp only at houtl
    obtain ⟨a, ha, ha'⟩ := slice_get cp pc (cp.val.length - 1) hpcv' (by omega)
    obtain ⟨o2, ho2, ho2v⟩ := push_eq out a (by rw [hmax]; omega)
    refine ⟨(o2, alloc.vec.Vec.len tf2 != 0#usize),
      by simp only [hpc, bind_ok, hd, hb, uncurry_apply_pair, htf, hout, ha, ho2], ?_⟩
    rw [ho2v, vS_push, ← ha']
    simp only [forIn_range_idx, id_run_eq]
    generalize hS : iterIdx _ 0 _ _ = S
    have hS' : iterIdx (fun _ b => bspBody dg.val b) 0 (100000000 - 0) (vvS tf.val, #[]) = S := by
      rw [htfv, vvS_reverse]; exact hS
    rw [hS'] at houtv1 houtv2
    obtain ⟨S1, S2⟩ := S
    dsimp only at houtv1 houtv2 ⊢
    subst houtv1 houtv2
    show _ = ((vS out.val).push ((vS cp.val)[cp.val.length - 1]!), (vvS tf2.val).size != 0)
    rw [vvS_size]
    refine Prod.ext rfl ?_
    show (alloc.vec.Vec.len tf2 != 0#usize) = (tf2.val.length != 0)
    rw [Bool.eq_iff_iff]; simp only [bne_iff_ne, ne_eq]
    constructor
    · intro h e; exact h (by apply UScalar.eq_of_val_eq; simpa using e)
    · intro h e; exact h (by simpa using congrArg UScalar.val e)

theorem beatmap.path_approximator.bezier_to_piecewise_linear_refines (cp : Slice net.osutk.Vector2)
    (h64 : System.Platform.numBits = 64) (hlen : cp.val.length < 2^32) :
    ∃ v, beatmap.path_approximator.bezier_to_piecewise_linear cp = ok v ∧
      vS v.val = bezierToPiecewiseLinear (vS cp.val) := by
  obtain ⟨d, hd, hdv⟩ := nat_sub_eq (Slice.len cp) 1#usize
  have hd' : (if 1#usize < d then ok d else ok 1#usize : Result Usize) = ok (if 1 < d.val then d else 1#usize) := by
    split <;> simp_all
  obtain ⟨⟨v, fo⟩, hv, hvv⟩ := beatmap.path_approximator.b_spline_to_piecewise_linear_refines cp
    (if 1 < d.val then d else 1#usize) h64 hlen
  refine ⟨v, by simp only [beatmap.path_approximator.bezier_to_piecewise_linear, hd, bind_ok, hd', hv] <;> rfl, ?_⟩
  have hdeg : (if 1 < d.val then d else 1#usize).val = max 1 ((vS cp.val).size - 1) := by
    simp [Slice.length] at hdv
    split <;> simp <;> omega
  rw [bezierToPiecewiseLinear, ← hdeg, ← hvv]

theorem i32_cast_i64_val (x : I32) : (IScalar.cast .I64 x).val = x.val := by
  rw [IScalar.cast_val_eq]
  have := x.hBounds
  simp at this ⊢

theorem ca_loop (ts tr dir : F64) (rad : F32) (cen : net.osutk.Vector2) (am : I32) (n : Usize)
    (hn : n.val ≤ 2^31)
    (g : Nat → Array Vec2 → Id (ForInStep (Array Vec2)))
    (hg : ∀ i o, g i o = .yield (o.push (bv2S cen + (Vec2.mk (F64.cos (ts + dir * (F64.ofInt ↑i / F64.ofInt (am.val - 1)) * tr)).toF32 (F64.sin (ts + dir * (F64.ofInt ↑i / F64.ofInt (am.val - 1)) * tr)).toF32) * rad))) :
    ∃ out, beatmap.path_approximator.circular_arc_to_piecewise_linear_loop ts tr dir rad cen am
        (alloc.vec.Vec.new net.osutk.Vector2) n 0#usize = ok out ∧
      vS out.val = iterIdx g 0 (n.val - 0) #[] := by
  unfold beatmap.path_approximator.circular_arc_to_piecewise_linear_loop
  have := usize_ge_32
  refine loop_iterIdx' _ g n.val
    (fun (x : alloc.vec.Vec net.osutk.Vector2 × Usize) j (b : Array Vec2) =>
      x.2.val = j ∧ vS x.1.val = b ∧ x.1.val.length = j)
    (fun (y : alloc.vec.Vec net.osutk.Vector2) (c : Array Vec2) => vS y.val = c)
    ?_ ?_ (alloc.vec.Vec.new _, 0#usize) 0 #[] ⟨by simp, by simp [vS], by simp⟩ rfl
  · rintro ⟨o, j⟩ jj b ⟨hj, hb, hol⟩ hjj
    dsimp only at hj hb hol
    subst hj hb
    left
    have hlt : j < n := hjj
    have hab := am.hBounds
    obtain ⟨i3, hi3, hi3v⟩ := i64_sub_one (IScalar.cast .I64 am) (by rw [i32_cast_i64_val]; simp at hab; omega)
      (by rw [i32_cast_i64_val]; simp at hab; omega)
    rw [i32_cast_i64_val] at hi3v
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by omega)
    let th := ts + dir * (F64.ofInt ↑j.val / F64.ofInt (am.val - 1)) * tr
    let p := bv2I (bv2S cen + (Vec2.mk (F64.cos th).toF32 (F64.sin th).toF32) * rad)
    obtain ⟨o1, ho1, ho1v⟩ := push_eq o p (by omega)
    refine ⟨_, hg _ _, (o1, j1), ?_, by simp [hj1v], ?_, by rw [ho1v]; simp; omega⟩
    · simp only [beatmap.path_approximator.circular_arc_to_piecewise_linear_loop.body, hlt, ite_true, lift, bind_ok,
        float.F64.from_i64, usize_hcast_i64 j (by omega), hi3, hi3v, float.F64.div, float.F64.mul, float.F64.add,
        float.F64.cos, float.F64.sin, float.F64.to_f32, beatmap.vector2.scale_refines, beatmap.vector2.add_refines, hj1]
      simp only [p, th, vec2_add_def, vec2_muls_def] at ho1
      simp only [bv2S_I, bv2S_mk]
      rw [ho1, bind_ok]
    · rw [ho1v, vS_push]; simp only [p, th, bv2S_I]
  · rintro ⟨o, j⟩ jj b ⟨hj, hb, hol⟩ hjj
    dsimp only at hj hb hol
    subst hj hb
    have hlt : ¬ j < n := by show ¬ j.val < n.val; omega
    exact ⟨o, by simp [beatmap.path_approximator.circular_arc_to_piecewise_linear_loop.body, hlt], rfl⟩

theorem int32_max2_ge (n : Int32) : 2 ≤ (if n < 2 then 2 else n).toInt := by
  split
  · decide
  · rename_i h; rw [Int32.lt_iff_toInt_lt] at h; simp at h; omega
theorem apc_ge (p : CircularArcProperties) : 2 ≤ (arcPointCount p).toInt := by
  unfold arcPointCount
  split
  · decide
  · exact int32_max2_ge _

theorem beatmap.path_approximator.circular_arc_to_piecewise_linear_refines (cp : Slice net.osutk.Vector2)
    (h64 : System.Platform.numBits = 64) (h3 : 3 ≤ cp.val.length) (hlen : cp.val.length < 2^32) :
    ∃ v, beatmap.path_approximator.circular_arc_to_piecewise_linear cp = ok v ∧
      vS v.val = circularArcToPiecewiseLinear (vS cp.val) := by
  obtain ⟨r, hr, hrv⟩ := beatmap.path_approximator.circular_arc_properties_refines cp h3
  unfold beatmap.path_approximator.circular_arc_to_piecewise_linear circularArcToPiecewiseLinear
  rw [← hrv]
  rw [hr, bind_ok]
  by_cases hvld : r.is_valid = true
  · rw [if_pos hvld, beatmap.path_approximator.arc_point_count_refines, bind_ok]
    rw [id_run_eq, if_neg (show ¬ ((!(arcS r).isValid) = true) by simp [arcS, hvld])]
    have hge := apc_ge (arcS r)
    generalize hA : arcPointCount (arcS r) = A at hge
    have hAv : (i32I A).val = A.toInt := rfl
    have hAlt : A.toInt < 2^31 := A.toInt_lt
    have hneg : ¬ (i32I A) < 0#i32 := by show ¬ (i32I A).val < (0#i32).val; rw [hAv]; simp; omega
    have hcast : (IScalar.hcast .Usize (i32I A)).val = A.toNatClampNeg := by
      rw [IScalar.hcast_val_eq, hAv, Int.emod_eq_of_lt (by omega) (by simp [h64]; omega)]
      exact (Int32.toNat_toInt A)
    rw [if_neg hneg, bind_ok]
    simp only [forIn_range_idx]
    generalize hS : iterIdx _ 0 _ _ = S
    obtain ⟨out, hout, houtv⟩ := ca_loop r.theta_start r.theta_range r.direction r.radius r.centre (i32I A)
      (IScalar.hcast .Usize (i32I A)) (by rw [hcast, ← Int32.toNat_toInt]; omega) _ (fun _ _ => rfl)
    refine ⟨out, hout, ?_⟩
    rw [houtv, ← hS, hcast]
    rfl
  · have hvld' : r.is_valid = false := by simpa using hvld
    rw [if_neg hvld]
    obtain ⟨v, hv, hvv⟩ := beatmap.path_approximator.bezier_to_piecewise_linear_refines cp h64 hlen
    refine ⟨v, hv, ?_⟩
    rw [id_run_eq, if_pos (show ((!(arcS r).isValid) = true) by simp [arcS, hvld']), hvv]
    rfl

theorem pa_k_catmull_detail : beatmap.path_approximator.k_catmull_detail = ok kCatmullDetail := by
  simp [beatmap.path_approximator.k_catmull_detail, beatmap.path_approximator.CATMULL_DETAIL, kCatmullDetail,
    catmull_detail, lift, float.F32.from_i64]

theorem ct_inner (v1 v2 v3 v4 : net.osutk.Vector2)
    (g : Nat → Array Vec2 → Id (ForInStep (Array Vec2)))
    (hg : ∀ c r, g c r = .yield ((r.push (catmullFindPoint (bv2S v1) (bv2S v2) (bv2S v3) (bv2S v4)
      (F32.ofInt ↑c / kCatmullDetail))).push (catmullFindPoint (bv2S v1) (bv2S v2) (bv2S v3) (bv2S v4)
      (F32.ofInt (↑c + 1) / kCatmullDetail)))) :
    ∀ (res : alloc.vec.Vec net.osutk.Vector2), res.val.length + 100 ≤ Usize.max →
    ∃ res', beatmap.path_approximator.catmull_to_piecewise_linear_loop0_loop0 res kCatmullDetail v1 v2 v3 v4 0#usize = ok res' ∧
      vS res'.val = iterIdx g 0 (catmull_detail - 0) (vS res.val) ∧ res'.val.length = res.val.length + 100 := by
  intro res hres
  unfold beatmap.path_approximator.catmull_to_piecewise_linear_loop0_loop0
  refine loop_iterIdx' _ g catmull_detail
    (fun (x : alloc.vec.Vec net.osutk.Vector2 × Usize) j (b : Array Vec2) =>
      x.2.val = j ∧ vS x.1.val = b ∧ x.1.val.length = res.val.length + 2 * j ∧ j ≤ 50)
    (fun (y : alloc.vec.Vec net.osutk.Vector2) (c : Array Vec2) => vS y.val = c ∧ y.val.length = res.val.length + 100)
    ?_ ?_ (res, 0#usize) 0 (vS res.val) ⟨by simp, rfl, by simp, by omega⟩ rfl
  · rintro ⟨o, j⟩ jj b ⟨hj, hb, hol, h50⟩ hjj
    dsimp only at hj hb hol h50
    subst hj hb
    left
    have hlt : j < beatmap.path_approximator.CATMULL_DETAIL := by
      show j.val < (beatmap.path_approximator.CATMULL_DETAIL).val; simp [beatmap.path_approximator.CATMULL_DETAIL]
      simp [catmull_detail] at hjj; omega
    simp [catmull_detail] at hjj
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := usize_ge_32; omega)
    let p1 := bv2I (catmullFindPoint (bv2S v1) (bv2S v2) (bv2S v3) (bv2S v4) (F32.ofInt ↑j.val / kCatmullDetail))
    let p2 := bv2I (catmullFindPoint (bv2S v1) (bv2S v2) (bv2S v3) (bv2S v4) (F32.ofInt ↑j1.val / kCatmullDetail))
    obtain ⟨o1, ho1, ho1v⟩ := push_eq o p1 (by omega)
    obtain ⟨o2, ho2, ho2v⟩ := push_eq o1 p2 (by rw [ho1v]; simp; omega)
    refine ⟨_, hg _ _, (o2, j1), ?_, by simp [hj1v], ?_, by rw [ho2v, ho1v]; simp; omega, by omega⟩
    · simp only [beatmap.path_approximator.catmull_to_piecewise_linear_loop0_loop0.body, hlt, ite_true, lift, bind_ok,
        float.F32.from_i64, usize_hcast_i64 j (by omega), usize_hcast_i64 j1 (by omega), float.F32.div,
        beatmap.path_approximator.catmull_find_point_refines, hj1]
      simp only [p1, p2] at ho1 ho2
      rw [ho1, bind_ok, ho2, bind_ok]
    · rw [ho2v, ho1v, vS_push, vS_push]
      simp only [p1, p2, bv2S_I, hj1v]; push_cast; rfl
  · rintro ⟨o, j⟩ jj b ⟨hj, hb, hol, h50⟩ hjj
    dsimp only at hj hb hol h50
    subst hj hb
    simp [catmull_detail] at hjj
    have hlt : ¬ j < beatmap.path_approximator.CATMULL_DETAIL := by
      show ¬ j.val < (beatmap.path_approximator.CATMULL_DETAIL).val; simp [beatmap.path_approximator.CATMULL_DETAIL]; omega
    exact ⟨o, by simp [beatmap.path_approximator.catmull_to_piecewise_linear_loop0_loop0.body, hlt], rfl, by omega⟩

def ctG (a b c d : Vec2) : Nat → Array Vec2 → Id (ForInStep (Array Vec2)) := fun k r =>
  .yield ((r.push (catmullFindPoint a b c d (F32.ofInt ↑k / kCatmullDetail))).push
    (catmullFindPoint a b c d (F32.ofInt (↑k + 1) / kCatmullDetail)))

def ctF (cp : Array Vec2) : Nat → Array Vec2 → Id (ForInStep (Array Vec2)) := fun i r =>
  let v1 := if i > 0 then cp[i - 1]! else cp[i]!
  let v2 := cp[i]!
  let v3 := if i < cp.size - 1 then cp[i + 1]! else v2 + v2 - v1
  let v4 := if i + 2 < cp.size then cp[i + 2]! else v3 + v3 - v2
  .yield (iterIdx (ctG v1 v2 v3 v4) 0 (catmull_detail - 0) r)

theorem ct_v1 (cp : Slice net.osutk.Vector2) (j : Usize) (h : j.val < cp.val.length) :
    (if j > 0#usize then (do let i2 ← j - 1#usize; Slice.index_usize cp i2) else Slice.index_usize cp j) =
      ok (if 0 < j.val then cp.val[j.val - 1] else cp.val[j.val]) := by
  by_cases h0 : 0 < j.val
  · have h0' : j > 0#usize := by show (0#usize).val < j.val; simpa using h0
    obtain ⟨i2, hi2, hi2v⟩ := usize_sub_one j h0
    simp only [h0', ite_true, hi2, bind_ok, index_eq cp i2 (by omega), h0]
    simp [hi2v]
  · have h0' : ¬ j > 0#usize := by show ¬ (0#usize).val < j.val; simpa using h0
    simp only [h0', ite_false, index_eq cp j h, h0]

theorem ct_v4 (cp : Slice net.osutk.Vector2) (i3 : Usize) (v2 v3 : net.osutk.Vector2) :
    (if i3 < Slice.len cp then Slice.index_usize cp i3 else (do let v ← beatmap.vector2.add v3 v3; beatmap.vector2.sub v v2)) =
      ok (if h : i3.val < cp.val.length then cp.val[i3.val] else bv2I (bv2S v3 + bv2S v3 - bv2S v2)) := by
  by_cases h0 : i3.val < cp.val.length
  · have h0' : i3 < Slice.len cp := by show i3.val < (Slice.len cp).val; simpa using h0
    simp only [h0', ite_true, index_eq cp i3 h0, h0, _root_.dite_true]
  · have h0' : ¬ i3 < Slice.len cp := by show ¬ i3.val < (Slice.len cp).val; simpa using h0
    simp only [h0', ite_false, h0, _root_.dite_false, beatmap.vector2.add_refines, beatmap.vector2.sub_refines, bind_ok, bv2S_I]
    rfl

theorem beatmap.path_approximator.catmull_to_piecewise_linear_refines (cp : Slice net.osutk.Vector2)
    (h64 : System.Platform.numBits = 64) (hlen : cp.val.length < 2^32) :
    ∃ v, beatmap.path_approximator.catmull_to_piecewise_linear cp = ok v ∧
      vS v.val = catmullToPiecewiseLinear (vS cp.val) := by
  have hmax := usize_max64 h64
  unfold beatmap.path_approximator.catmull_to_piecewise_linear catmullToPiecewiseLinear
  rw [pa_k_catmull_detail, bind_ok]
  simp only [forIn_range_idx, id_run_eq]
  generalize hS : iterIdx _ 0 _ _ = S
  have hS' : iterIdx (ctF (vS cp.val)) 0 ((vS cp.val).size - 1 - 0) #[] = S := hS
  rw [← hS']
  unfold beatmap.path_approximator.catmull_to_piecewise_linear_loop0
  obtain ⟨i1, hi1, hi1v⟩ := nat_sub_eq (Slice.len cp) 1#usize
  have hi1v' : i1.val = cp.val.length - 1 := by simp [Slice.length] at hi1v; omega
  refine loop_iterIdx' _ (ctF (vS cp.val)) (cp.val.length - 1)
    (fun (x : alloc.vec.Vec net.osutk.Vector2 × Usize) j (b : Array Vec2) =>
      x.2.val = j ∧ vS x.1.val = b ∧ x.1.val.length = 100 * j)
    (fun (y : alloc.vec.Vec net.osutk.Vector2) (c : Array Vec2) => vS y.val = c)
    ?_ ?_ (alloc.vec.Vec.new _, 0#usize) 0 #[] ⟨by simp, by simp [vS], by simp⟩ (by simp)
  · rintro ⟨o, j⟩ jj b ⟨hj, hb, hol⟩ hjj
    dsimp only at hj hb hol
    subst hj hb
    left
    have hlt : j.val < i1.val := by omega
    have hjl : j.val < cp.val.length := by omega
    obtain ⟨n1, hn1, hn1v⟩ := usize_sub_one (Slice.len cp) (by simp; omega)
    have hn1' : n1.val = cp.val.length - 1 := by simp [Slice.length] at hn1v; omega
    have hlt2 : j.val < n1.val := by omega
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by omega)
    obtain ⟨j2, hj2, hj2v⟩ := eq_ok_of_spec (Usize.add_spec (x := j) (y := 2#usize) (by simp; omega))
    have hj2' : j2.val = j.val + 2 := by rw [hj2v]; simp
    have ej1 : j1.val < cp.val.length := by omega
    let a1 := if 0 < j.val then cp.val[j.val - 1] else cp.val[j.val]
    let a2 := cp.val[j.val]
    let a3 := cp.val[j1.val]
    let a4 := if h : j2.val < cp.val.length then cp.val[j2.val] else bv2I (bv2S a3 + bv2S a3 - bv2S a2)
    obtain ⟨o', ho', ho'v, ho'l⟩ := ct_inner a1 a2 a3 a4 (ctG (bv2S a1) (bv2S a2) (bv2S a3) (bv2S a4)) (fun _ _ => rfl) o
      (by rw [hmax]; omega)
    have hlt' : j < i1 := hlt
    have hlt2' : j < n1 := hlt2
    refine ⟨iterIdx (ctG (bv2S a1) (bv2S a2) (bv2S a3) (bv2S a4)) 0 (catmull_detail - 0) (vS o.val), ?_, (o', j1), ?_,
      by simp [hj1v], ho'v, by dsimp only; rw [ho'l, hol]; ring⟩
    · have e2 : (vS cp.val)[j.val]! = bv2S a2 := vS_get! _ _ hjl
      have e1 : (if j.val > 0 then (vS cp.val)[j.val - 1]! else (vS cp.val)[j.val]!) = bv2S a1 := by
        by_cases h : 0 < j.val
        · rw [if_pos (show j.val > 0 from h)]; simp only [a1, if_pos h]; exact vS_get! _ _ (by omega)
        · rw [if_neg (show ¬ j.val > 0 from h)]; simp only [a1, if_neg h]; exact vS_get! _ _ (by omega)
      have e3 : (if j.val < (vS cp.val).size - 1 then (vS cp.val)[j.val + 1]!
          else bv2S a2 + bv2S a2 - bv2S a1) = bv2S a3 := by
        rw [if_pos (by simp; omega), vS_get! _ _ (by omega)]; simp [a3, hj1v]
      have e4 : (if j.val + 2 < (vS cp.val).size then (vS cp.val)[j.val + 2]! else bv2S a3 + bv2S a3 - bv2S a2) = bv2S a4 := by
        simp only [a4]
        by_cases h : j.val + 2 < cp.val.length
        · rw [if_pos (by simpa using h), dif_pos (by omega), vS_get! _ _ h]; simp [hj2']
        · rw [if_neg (by simpa using h), dif_neg (by omega), bv2S_I]
      simp only [ctF]
      rw [e1, e2, e3, e4]
    · simp only [beatmap.path_approximator.catmull_to_piecewise_linear_loop0.body, hi1, hlt', ite_true, bind_ok]
      rw [ct_v1 cp j hjl]
      simp only [bind_ok, index_eq cp j hjl, hn1, hlt2', hj1, index_eq cp j1 ej1, hj2, ite_true]
      rw [ct_v4]
      simp only [bind_ok]
      rw [ho', bind_ok]
  · rintro ⟨o, j⟩ jj b ⟨hj, hb, hol⟩ hjj
    dsimp only at hj hb hol
    subst hj hb
    have hlt : ¬ j.val < i1.val := by omega
    exact ⟨o, by simp [beatmap.path_approximator.catmull_to_piecewise_linear_loop0.body, hi1, hlt], rfl⟩

end OsuProofs
