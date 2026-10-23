/-
`beatmap::mod_random` (Rust) refines `OsuModel.Beatmap.Mods.Reposition` / `RandomMod` (mods proof agent;
continues Beatmap/ModRandomBase.lean and Post/TargetPractice.lean).
-/
import OsuProofs.Post.ModsB
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

theorem mr2_PI : beatmap.mod_random.PI = ok Mods.Reposition.PI := by
  unfold beatmap.mod_random.PI; simp only [float.F32.from_bits]; rfl

theorem mr2_i32_add_one (k : I32) (h : k.val < 4) (h0 : 0 ≤ k.val) : ∃ z, k + 1#i32 = ok z ∧ z.val = k.val + 1 := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (IScalar.add_spec (x := k) (y := 1#i32)
    (by simp [IScalar.min, I32.min_eq] at *; omega) (by simp [IScalar.max, I32.max_eq] at *; omega))
  exact ⟨z, hz, by simpa using hv⟩

def rvtvS0 (tp d : F32) : F32 := if d < -Mods.Reposition.PI then d + tp else d
def rvtvS1 (tp d : F32) : F32 := if Mods.Reposition.PI < d then d - tp else d

theorem mr2_rvtv_loop0 (tp : F32) : ∀ (n : Nat) (d : F32) (k : I32), 0 ≤ k.val → k.val + n = 4 →
    beatmap.mod_random.rotate_vector_towards_vector_loop0 d tp k = ok ((rvtvS0 tp)^[n] d) := by
  intro n
  induction n with
  | zero =>
    intro d k h0 hk
    unfold beatmap.mod_random.rotate_vector_towards_vector_loop0
    rw [loop_unfold]
    have : ¬ k < 4#i32 := by
      show ¬ k.val < (4#i32 : I32).val; have : (4#i32 : I32).val = 4 := by decide
      rw [this]; omega
    simp [beatmap.mod_random.rotate_vector_towards_vector_loop0.body, this]
  | succ n ih =>
    intro d k h0 hk
    unfold beatmap.mod_random.rotate_vector_towards_vector_loop0
    rw [loop_unfold]
    have h4 : (4#i32 : I32).val = 4 := by decide
    have : k < 4#i32 := by show k.val < (4#i32 : I32).val; rw [h4]; omega
    obtain ⟨k1, hk1, hk1v⟩ := mr2_i32_add_one k (by omega) h0
    have e := ih (rvtvS0 tp d) k1 (by omega) (by omega)
    unfold beatmap.mod_random.rotate_vector_towards_vector_loop0 at e
    have hb : beatmap.mod_random.rotate_vector_towards_vector_loop0.body tp d k = ok (.cont (rvtvS0 tp d, k1)) := by
      simp only [beatmap.mod_random.rotate_vector_towards_vector_loop0.body, this, if_true, mr2_PI, float.F32.neg,
        float.F32.lt, bind_ok, hk1, rvtvS0, float.F32.add]
      split <;> simp_all
    simp only [hb, bind_ok]
    rw [Function.iterate_succ_apply]
    exact e

theorem mr2_rvtv_loop1 (tp : F32) : ∀ (n : Nat) (d : F32) (k : I32), 0 ≤ k.val → k.val + n = 4 →
    beatmap.mod_random.rotate_vector_towards_vector_loop1 d tp k = ok ((rvtvS1 tp)^[n] d) := by
  intro n
  induction n with
  | zero =>
    intro d k h0 hk
    unfold beatmap.mod_random.rotate_vector_towards_vector_loop1
    rw [loop_unfold]
    have : ¬ k < 4#i32 := by
      show ¬ k.val < (4#i32 : I32).val; have : (4#i32 : I32).val = 4 := by decide
      rw [this]; omega
    simp [beatmap.mod_random.rotate_vector_towards_vector_loop1.body, this]
  | succ n ih =>
    intro d k h0 hk
    unfold beatmap.mod_random.rotate_vector_towards_vector_loop1
    rw [loop_unfold]
    have h4 : (4#i32 : I32).val = 4 := by decide
    have : k < 4#i32 := by show k.val < (4#i32 : I32).val; rw [h4]; omega
    obtain ⟨k1, hk1, hk1v⟩ := mr2_i32_add_one k (by omega) h0
    have e := ih (rvtvS1 tp d) k1 (by omega) (by omega)
    unfold beatmap.mod_random.rotate_vector_towards_vector_loop1 at e
    have hb : beatmap.mod_random.rotate_vector_towards_vector_loop1.body tp d k = ok (.cont (rvtvS1 tp d, k1)) := by
      simp only [beatmap.mod_random.rotate_vector_towards_vector_loop1.body, this, if_true, mr2_PI, float.F32.lt, bind_ok, hk1, rvtvS1, float.F32.sub]
      split <;> simp_all
    simp only [hb, bind_ok]
    rw [Function.iterate_succ_apply]
    exact e

theorem mr2_iterR_iter {S : Type} (F : Nat → S → ForInStep S) (g : S → S) (hF : ∀ j s, F j s = .yield (g s)) :
    ∀ n j s, iterR F j n s = g^[n] s := by
  intro n
  induction n with
  | zero => intro j s; rfl
  | succ n ih => intro j s; simp only [iterR, hF]; rw [ih, Function.iterate_succ_apply]

theorem beatmap.mod_random.rotate_vector_towards_vector_refines (initial destination : net.osutk.Vector2) (rr : F32) :
    beatmap.mod_random.rotate_vector_towards_vector initial destination rr =
      ok (bv2I (Mods.Reposition.rotateVectorTowardsVector (bv2S initial) (bv2S destination) rr)) := by
  unfold beatmap.mod_random.rotate_vector_towards_vector Mods.Reposition.rotateVectorTowardsVector
  simp only [Id.run, id_bind_eq]
  rw [forIn_range_iterR, forIn_range_iterR]
  rw [mr2_iterR_iter _ (rvtvS1 Mods.Reposition.TWO_PI) (fun j s => by simp only [rvtvS1]; split <;> rfl)]
  rw [mr2_iterR_iter _ (rvtvS0 Mods.Reposition.TWO_PI) (fun j s => by simp only [rvtvS0]; split <;> rfl)]
  simp only [beatmap.mod_random.atan2f_refines, mr_two_pi, float.F32.sub, bind_ok,
    mr2_rvtv_loop0 _ 4 _ 0#i32 (by decide) (by decide), mr2_rvtv_loop1 _ 4 _ 0#i32 (by decide) (by decide),
    float.F32.mul, float.F32.add, beatmap.vector2.length_refines, float.F32.cos, float.F32.sin]
  simp [bv2I, bv2S, Mods.Reposition.atan2f]
  constructor <;> rfl

theorem mr2_border_x : beatmap.mod_random.border_x = ok Mods.Reposition.borderX := by
  unfold beatmap.mod_random.border_x Mods.Reposition.borderX
  have : (Float32.ofBits 1140850688 : F32) = 512 := by decide
  simp [float.F32.from_bits, float.F32.mul, Mods.Reposition.edgeRatio, this]
theorem mr2_border_y : beatmap.mod_random.border_y = ok Mods.Reposition.borderY := by
  unfold beatmap.mod_random.border_y Mods.Reposition.borderY
  have : (Float32.ofBits 1136656384 : F32) = 384 := by decide
  simp [float.F32.from_bits, float.F32.mul, Mods.Reposition.edgeRatio, this]
theorem mr2_CENTRE : beatmap.mod_random.CENTRE = ok (bv2I Mods.Reposition.centre) := by
  unfold beatmap.mod_random.CENTRE
  simp [float.F32.from_bits, bv2I, Mods.Reposition.centre] <;> decide

theorem beatmap.mod_random.rotate_away_from_edge_refines (prev rel : net.osutk.Vector2) (rr : F32) :
    beatmap.mod_random.rotate_away_from_edge prev rel rr =
      ok (bv2I (Mods.Reposition.rotateAwayFromEdge (bv2S prev) (bv2S rel) rr)) := by
  unfold beatmap.mod_random.rotate_away_from_edge Mods.Reposition.rotateAwayFromEdge
  simp only [mr2_border_x, mr2_border_y, mr2_CENTRE, mr_BASE_SIZE, cst_beatmap_mod_random_F0, cst_beatmap_mod_random_F1,
    bind_ok, float.F32.lt, float.F32.sub, float.F32.div, float.F32.mul, net.mathops.f32_max_refines,
    net.mathops.f32_min_refines, bv2I_x, bv2I_y, bv2S_x, bv2S_y]
  by_cases hx : prev.x < Mods.Reposition.centre.x <;> by_cases hy : prev.y < Mods.Reposition.centre.y <;>
    simp [hx, hy, beatmap.vector2.sub_refines, beatmap.mod_random.rotate_vector_towards_vector_refines, bv2S_I] <;> rfl

theorem beatmap.mod_random.rect_right_refines (r : beatmap.mod_random.RectF) :
    ∃ x, beatmap.mod_random.rect_right r = ok x ∧ Mods.Reposition.RectF.right (abs r) = abs x := by
  exact ⟨_, rfl, rfl⟩

theorem beatmap.mod_random.rect_bottom_refines (r : beatmap.mod_random.RectF) :
    ∃ x, beatmap.mod_random.rect_bottom r = ok x ∧ Mods.Reposition.RectF.bottom (abs r) = abs x := by
  exact ⟨_, rfl, rfl⟩

/-- `clampToPlayfieldWithPadding` (`Math.Clamp` throws when `padding > BASE_SIZE - padding`: both reject). -/
theorem beatmap.mod_random.clamp_with_padding_refines (p : net.osutk.Vector2) (pad : F32) :
    ∃ r, beatmap.mod_random.clamp_with_padding p pad = ok r ∧
      hRel bv2S r (Mods.Reposition.clampWithPadding (bv2S p) pad) := by
  unfold beatmap.mod_random.clamp_with_padding Mods.Reposition.clampWithPadding
  simp only [mr_BASE_SIZE, bind_ok, bv2I_x, bv2I_y, float.F32.sub, net.mathops.f32_clamp_refines, bv2S_x, bv2S_y]
  obtain ⟨r1, h1, hr1⟩ := lift_net_exceptI beatmap.errors.W_MATH_CLAMP id id (fun _ => rfl)
    (F32.clamp p.x pad (Mods.Reposition.BASE_SIZE.x - pad)) "Math.Clamp"
  rw [h1]; simp only [bind_ok]
  cases hc1 : F32.clamp p.x pad (Mods.Reposition.BASE_SIZE.x - pad) with
  | error e => rw [hc1] at hr1; cases r1 with
    | Ok _ => simp [hRel, liftNet] at hr1
    | Err e1 => exact ⟨_, rfl, by simp [hRel, liftNet]⟩
  | ok x =>
    rw [hc1] at hr1
    cases r1 with
    | Err _ => simp [hRel, liftNet] at hr1
    | Ok x1 =>
      simp [hRel, liftNet] at hr1; subst hr1
      obtain ⟨r2, h2, hr2⟩ := lift_net_exceptI beatmap.errors.W_MATH_CLAMP id id (fun _ => rfl)
        (F32.clamp p.y pad (Mods.Reposition.BASE_SIZE.y - pad)) "Math.Clamp"
      simp only [h2, bind_ok]
      cases hc2 : F32.clamp p.y pad (Mods.Reposition.BASE_SIZE.y - pad) with
      | error e => rw [hc2] at hr2; cases r2 with
        | Ok _ => simp [hRel, liftNet] at hr2
        | Err e2 => exact ⟨_, rfl, by simp [hRel, liftNet, hc1, hc2, Bind.bind, Except.bind]⟩
      | ok y =>
        rw [hc2] at hr2
        cases r2 with
        | Err _ => simp [hRel, liftNet] at hr2
        | Ok y1 =>
          simp [hRel, liftNet] at hr2; subst hr2
          exact ⟨_, rfl, by simp [hRel, liftNet, hc1, hc2, Bind.bind, Except.bind, pure, Except.pure, bv2S]⟩

theorem mr2_empty_path : ∃ p, beatmap.mod_random.empty_path = ok p ∧ spS p = (default : SliderPath) ∧ obPathOk p := by
  let sp : beatmap.slider_path.SliderPathSpec := ⟨alloc.vec.Vec.new _, none, false⟩
  refine ⟨⟨sp, alloc.vec.Vec.new _, alloc.vec.Vec.new _, Float.ofBits 0, false⟩, ?_, ?_, ?_⟩
  · unfold beatmap.mod_random.empty_path; simp [float.F64.from_bits, sp]
  · simp [spS, spsS, vS, pcpsS, alloc.vec.Vec.new, sp]
    first | rfl | decide | (congr 1 <;> decide)
  · simp [obPathOk]

theorem beatmap.mod_random.slider_path_of_refines (h : beatmap.objects.OsuHitObject) :
    ∃ r, beatmap.mod_random.slider_path_of h = ok r ∧ (r.map spS).getD default = Mods.Reposition.sliderPath (abs h) := by
  unfold beatmap.mod_random.slider_path_of Mods.Reposition.sliderPath
  rw [ob_kind_abs]
  cases hk : h.kind with
  | Circle => exact ⟨none, rfl, rfl⟩
  | Spinner sp => exact ⟨none, rfl, rfl⟩
  | Slider sd =>
    have e : (abs sd : SliderData).path = spS sd.path := ob_abs_sliderPath sd.path
    exact ⟨some sd.path, rfl, by simp only [ob_abs_slider, e]; rfl⟩

theorem beatmap.mod_random.slider_rotation_refines (h : beatmap.objects.OsuHitObject)
    (hp : ∀ s, h.kind = .Slider s → obPathOk s.path) (h64 : System.Platform.numBits = 64) :
    beatmap.mod_random.slider_rotation h = ok (Mods.Reposition.sliderRotation (abs h)) := by
  have hd1 : beatmap.mod_random.D1 = ok (1 : F64) := by
    unfold beatmap.mod_random.D1; simp [float.F64.from_bits] <;> decide
  obtain ⟨ep, hep, hep2, hep3⟩ := mr2_empty_path
  unfold beatmap.mod_random.slider_rotation Mods.Reposition.sliderRotation Mods.Reposition.sliderPath
  rw [ob_kind_abs]
  cases hk : h.kind with
  | Circle =>
    simp [hep, hd1, beatmap.slider_path.position_at_refines ep 1 hep3.1 hep3.2 h64, beatmap.mod_random.atan2f_refines,
      hep2, bv2I, Mods.Reposition.atan2f]
  | Spinner sp =>
    simp [hep, hd1, beatmap.slider_path.position_at_refines ep 1 hep3.1 hep3.2 h64, beatmap.mod_random.atan2f_refines,
      hep2, bv2I, Mods.Reposition.atan2f]
  | Slider sd =>
    have hs := hp sd hk
    have e : (abs sd : SliderData).path = spS sd.path := ob_abs_sliderPath sd.path
    simp only [ob_abs_slider, e]
    simp [hd1, beatmap.slider_path.position_at_refines sd.path 1 hs.1 hs.2 h64, beatmap.mod_random.atan2f_refines,
      bv2I, Mods.Reposition.atan2f]

def pmbG (s : F32 × F32 × F32 × F32) (q : Vec2) : F32 × F32 × F32 × F32 :=
  (F32.min s.1 q.x, F32.max s.2.1 q.x, F32.min s.2.2.1 q.y, F32.max s.2.2.2 q.y)

theorem mr2_pmb_loop (p : beatmap.slider_path.SliderPath) (a b c d : F32) :
    ∃ y, beatmap.mod_random.possible_movement_bounds_loop a b c d p 0#usize = ok y ∧
      y = (p.calculated_path.val.map bv2S).foldl pmbG (a, b, c, d) := by
  obtain ⟨y, hl, hy⟩ := loop_fold_gen
    (fun (x : F32 × F32 × F32 × F32 × Usize) => beatmap.mod_random.possible_movement_bounds_loop.body p x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (·.2.2.2.2) p.calculated_path.val.length (fun _ => True) (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1))
    (fun k s => pmbG s ((p.calculated_path.val.map bv2S)[k]!)) (fun y s => y = s)
    (by
      rintro ⟨a, b, c, d, i⟩ - hi
      simp only at hi ⊢
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := p.calculated_path.property; omega)
      have hl : i < alloc.vec.Vec.len p.calculated_path := by show i.val < (alloc.vec.Vec.len _).val; simpa using hi
      refine ⟨(F32.min a (p.calculated_path.val[i.val]'hi).x, F32.max b (p.calculated_path.val[i.val]'hi).x,
        F32.min c (p.calculated_path.val[i.val]'hi).y, F32.max d (p.calculated_path.val[i.val]'hi).y, i1), ?_, hi1v, ?_, trivial⟩
      · simp only [beatmap.mod_random.possible_movement_bounds_loop.body, hl, if_true, vec_index_eq _ _ hi, bind_ok,
          net.mathops.f32_min_refines, net.mathops.f32_max_refines, hi1]
      · rw [getElem!_pos _ _ (by simpa using hi)]; simp [pmbG, bv2S])
    (by
      rintro ⟨a, b, c, d, i⟩ - hi
      simp only at hi ⊢
      have hl : ¬ i < alloc.vec.Vec.len p.calculated_path := by show ¬ i.val < (alloc.vec.Vec.len _).val; simp; omega
      exact ⟨_, by simp [beatmap.mod_random.possible_movement_bounds_loop.body, hl], rfl⟩)
    (a, b, c, d, 0#usize) trivial (by simp)
  refine ⟨y, by unfold beatmap.mod_random.possible_movement_bounds_loop; exact hl, ?_⟩
  rw [hy, foldl_iterR]; simp

theorem beatmap.mod_random.possible_movement_bounds_refines (h : beatmap.objects.OsuHitObject) :
    ∃ r, beatmap.mod_random.possible_movement_bounds h = ok r ∧
      Mods.Reposition.possibleMovementBounds (abs h) = abs r := by
  obtain ⟨rad, hrad, hrad2⟩ := beatmap.objects.radius_refines h
  unfold beatmap.mod_random.possible_movement_bounds Mods.Reposition.possibleMovementBounds
  simp only [Id.run]
  rw [← Array.forIn_toList, forIn_yield_foldl _ pmbG ?hG]
  case hG => intro q s; rfl
  obtain ⟨o, ho, ho2⟩ := beatmap.mod_random.slider_path_of_refines h
  rw [← ho2]
  have hinf : net.basic.F32_POS_INF = ok F32.posInf := by
    unfold net.basic.F32_POS_INF; simp only [float.F32.from_bits]; rfl
  simp only [hinf, ho, bind_ok, float.F32.neg, hrad2, hrad, abs_id]
  cases o with
  | none =>
    simp [float.F64.to_f32, float.F32.sub, float.F32.add, mr_BASE_SIZE, float.F32.neg, bv2I]
    rfl
  | some p =>
    obtain ⟨y, hy, hyv⟩ := mr2_pmb_loop p F32.posInf (-F32.posInf) F32.posInf (-F32.posInf)
    simp [hy, hyv, float.F64.to_f32, float.F32.sub, float.F32.add, mr_BASE_SIZE, float.F32.neg, bv2I]
    refine ⟨_, rfl, ?_⟩
    simp only [spS, vS, List.foldl_toArray']
    rfl

end OsuProofs
