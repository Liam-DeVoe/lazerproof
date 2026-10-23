/-
Generator mods, part 3 (gen agent): `beatmap::mod_random::clamp_slider_to_playfield` (split into the Rust
rotation phase `gen_cspHead` and clamping phase `gen_cspTail`, spec normal form `gen_cspS`).
-/
import OsuProofs.Post.GenRD1
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
open ControlFlow

/-- phase 1 of `clamp_slider_to_playfield` (rotation of out-of-playfield sliders); Rust code -/
def gen_cspHead (h : beatmap.objects.OsuHitObject) (w : beatmap.mod_random.Working) (bounds : beatmap.mod_random.RectF) (f : F32) (b : Bool) :
    Result (beatmap.objects.OsuHitObject × beatmap.mod_random.Working × beatmap.mod_random.RectF) := do
  if b
  then
    do
    let current_rotation ← beatmap.mod_random.slider_rotation h
    let diff1 ←
      beatmap.mod_random.angle_difference w.rotation_original
        current_rotation
    let f1 ← beatmap.mod_random.PI
    let f2 ← float.F32.add w.rotation_original f1
    let diff2 ← beatmap.mod_random.angle_difference f2 current_rotation
    let b1 ← float.F32.lt diff1 diff2
    let h2 ←
      if b1
      then
        do
        let r ← float.F32.sub w.rotation_original current_rotation
        beatmap.mod_random.rotate_slider h r
      else
        do
        let f3 ← float.F32.add w.rotation_original f1
        let r ← float.F32.sub f3 current_rotation
        beatmap.mod_random.rotate_slider h r
    let bounds2 ← beatmap.mod_random.possible_movement_bounds h2
    ok (h2, w, bounds2)
  else
    do
    let b1 ← float.F32.lt bounds.h f
    if b1
    then
      let current_rotation ← beatmap.mod_random.slider_rotation h
      let diff1 ←
        beatmap.mod_random.angle_difference w.rotation_original
          current_rotation
      let f1 ← beatmap.mod_random.PI
      let f2 ← float.F32.add w.rotation_original f1
      let diff2 ← beatmap.mod_random.angle_difference f2 current_rotation
      let b2 ← float.F32.lt diff1 diff2
      let h2 ←
        if b2
        then
          do
          let r ← float.F32.sub w.rotation_original current_rotation
          beatmap.mod_random.rotate_slider h r
        else
          do
          let f3 ← float.F32.add w.rotation_original f1
          let r ← float.F32.sub f3 current_rotation
          beatmap.mod_random.rotate_slider h r
      let bounds2 ← beatmap.mod_random.possible_movement_bounds h2
      ok (h2, w, bounds2)
    else ok (h, w, bounds)

/-- phase 2 of `clamp_slider_to_playfield` (clamping + set_position); Rust code -/
def gen_cspTail (h1 : beatmap.objects.OsuHitObject) (w1 : beatmap.mod_random.Working) (bounds1 : beatmap.mod_random.RectF) (f : F32) :
    Result ((core.result.Result (beatmap.mod_random.Working × net.osutk.Vector2)
    beatmap.hit_object_parser.DecodeError) × beatmap.objects.OsuHitObject) := do
  let b1 ← float.F32.lt bounds1.w f
  if b1
  then
    let v ← beatmap.mod_random.BASE_SIZE
    let r ← net.mathops.f32_clamp bounds1.x f v.x
    let r1 ← beatmap.hit_object_parser.lift_net beatmap.errors.W_MATH_CLAMP r
    match r1 with
    | core.result.Result.Ok v1 =>
      let b2 ← float.F32.lt bounds1.h f
      if b2
      then
        let r2 ← net.mathops.f32_clamp bounds1.y f v.y
        let r3 ←
          beatmap.hit_object_parser.lift_net beatmap.errors.W_MATH_CLAMP r2
        match r3 with
        | core.result.Result.Ok v2 =>
          let h2 ← beatmap.mods.set_position h1 { x := v1, y := v2 }
          let v3 ← beatmap.objects.end_position h2
          let v4 ←
            beatmap.vector2.sub { x := v1, y := v2 } w1.position_modified
          ok (core.result.Result.Ok
            ({
               w1
                 with
                 position_modified := { x := v1, y := v2 },
                 end_position_modified := v3
             }, v4), h2)
        | core.result.Result.Err e => ok (core.result.Result.Err e, h1)
      else
        let f1 ← beatmap.mod_random.rect_bottom bounds1
        let r2 ← net.mathops.f32_clamp w1.position_modified.y bounds1.y f1
        let r3 ←
          beatmap.hit_object_parser.lift_net beatmap.errors.W_MATH_CLAMP r2
        match r3 with
        | core.result.Result.Ok v2 =>
          let h2 ← beatmap.mods.set_position h1 { x := v1, y := v2 }
          let v3 ← beatmap.objects.end_position h2
          let v4 ←
            beatmap.vector2.sub { x := v1, y := v2 } w1.position_modified
          ok (core.result.Result.Ok
            ({
               w1
                 with
                 position_modified := { x := v1, y := v2 },
                 end_position_modified := v3
             }, v4), h2)
        | core.result.Result.Err e => ok (core.result.Result.Err e, h1)
    | core.result.Result.Err e => ok (core.result.Result.Err e, h1)
  else
    let f1 ← beatmap.mod_random.rect_right bounds1
    let r ← net.mathops.f32_clamp w1.position_modified.x bounds1.x f1
    let r1 ← beatmap.hit_object_parser.lift_net beatmap.errors.W_MATH_CLAMP r
    match r1 with
    | core.result.Result.Ok v =>
      let b2 ← float.F32.lt bounds1.h f
      if b2
      then
        let v1 ← beatmap.mod_random.BASE_SIZE
        let r2 ← net.mathops.f32_clamp bounds1.y f v1.y
        let r3 ←
          beatmap.hit_object_parser.lift_net beatmap.errors.W_MATH_CLAMP r2
        match r3 with
        | core.result.Result.Ok v2 =>
          let h2 ← beatmap.mods.set_position h1 { x := v, y := v2 }
          let v3 ← beatmap.objects.end_position h2
          let v4 ←
            beatmap.vector2.sub { x := v, y := v2 } w1.position_modified
          ok (core.result.Result.Ok
            ({
               w1
                 with
                 position_modified := { x := v, y := v2 },
                 end_position_modified := v3
             }, v4), h2)
        | core.result.Result.Err e => ok (core.result.Result.Err e, h1)
      else
        let f2 ← beatmap.mod_random.rect_bottom bounds1
        let r2 ← net.mathops.f32_clamp w1.position_modified.y bounds1.y f2
        let r3 ←
          beatmap.hit_object_parser.lift_net beatmap.errors.W_MATH_CLAMP r2
        match r3 with
        | core.result.Result.Ok v1 =>
          let h2 ← beatmap.mods.set_position h1 { x := v, y := v1 }
          let v2 ← beatmap.objects.end_position h2
          let v3 ←
            beatmap.vector2.sub { x := v, y := v1 } w1.position_modified
          ok (core.result.Result.Ok
            ({
               w1
                 with
                 position_modified := { x := v, y := v1 },
                 end_position_modified := v2
             }, v3), h2)
        | core.result.Result.Err e => ok (core.result.Result.Err e, h1)
    | core.result.Result.Err e => ok (core.result.Result.Err e, h1)

theorem gen_csp_split (h : beatmap.objects.OsuHitObject) (w : beatmap.mod_random.Working) :
    beatmap.mod_random.clamp_slider_to_playfield h w = (do
  let bounds ← beatmap.mod_random.possible_movement_bounds h
  let f ← beatmap.mod_random.F0
  let b ← float.F32.lt bounds.w f
  let (h1, w1, bounds1) ← gen_cspHead h w bounds f b
  gen_cspTail h1 w1 bounds1 f) := rfl

open Mods.Reposition in
/-- the slider after `clampSliderToPlayfield`'s rotation step -/
def gen_cspRot (h : OsuHitObject) (w : Working) : OsuHitObject :=
  let bounds := possibleMovementBounds h
  if bounds.w < 0 || bounds.h < 0 then
    let cr := sliderRotation h
    if angleDifference w.rotationOriginal cr < angleDifference (w.rotationOriginal + PI) cr
    then rotateSlider h (w.rotationOriginal - sliderRotation h)
    else rotateSlider h (w.rotationOriginal + PI - sliderRotation h)
  else h

open Mods.Reposition in
/-- `clampSliderToPlayfield` after the rotation step -/
def gen_cspT (h : OsuHitObject) (w : Working) : DecodeM (OsuHitObject × Working × Vec2) := do
  let bounds := possibleMovementBounds h
  let previousPosition := w.positionModified
  let newX ← if bounds.w < 0 then liftNet "Math.Clamp" (F32.clamp bounds.x 0 BASE_SIZE.x)
             else liftNet "Math.Clamp" (F32.clamp previousPosition.x bounds.x bounds.right)
  let newY ← if bounds.h < 0 then liftNet "Math.Clamp" (F32.clamp bounds.y 0 BASE_SIZE.y)
             else liftNet "Math.Clamp" (F32.clamp previousPosition.y bounds.y bounds.bottom)
  let p : Vec2 := ⟨newX, newY⟩
  let h := Mods.setPosition h p
  return (h, { w with positionModified := p, endPositionModified := h.endPosition }, p - previousPosition)

/-- normal form of `Reposition.clampSliderToPlayfield` -/
def gen_cspS (h0 : OsuHitObject) (w : Mods.Reposition.Working) : DecodeM (OsuHitObject × Mods.Reposition.Working × Vec2) :=
  gen_cspT (gen_cspRot h0 w) w

theorem gen_csp_spec (h : OsuHitObject) (w : Mods.Reposition.Working) :
    Mods.Reposition.clampSliderToPlayfield h w = gen_cspS h w := by
  unfold Mods.Reposition.clampSliderToPlayfield gen_cspS gen_cspT gen_cspRot
  simp only [Id.run]
  split_ifs <;> rfl

theorem gen_except_bind_ok {ε α β} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl
theorem gen_except_bind_err {ε α β} (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = Except.error e := rfl

open Classical in
noncomputable def gen_pmbR (h : beatmap.objects.OsuHitObject) : beatmap.mod_random.RectF :=
  if hc : ∃ o, beatmap.mod_random.possible_movement_bounds h = ok o then hc.choose else ⟨0, 0, 0, 0⟩

theorem gen_pmb_ok (h : beatmap.objects.OsuHitObject) :
    beatmap.mod_random.possible_movement_bounds h = ok (gen_pmbR h) ∧
      (abs (gen_pmbR h) : Mods.Reposition.RectF) = Mods.Reposition.possibleMovementBounds (abs h) := by
  obtain ⟨o, ho, hov⟩ := beatmap.mod_random.possible_movement_bounds_refines h
  have hc : ∃ o, beatmap.mod_random.possible_movement_bounds h = ok o := ⟨o, ho⟩
  have e : gen_pmbR h = o := by
    unfold gen_pmbR; rw [dif_pos hc]
    exact Result.ok_injective (hc.choose_spec.symm.trans ho)
  rw [e]; exact ⟨ho, hov.symm⟩

theorem gen_csp_head (h : beatmap.objects.OsuHitObject) (w : beatmap.mod_random.Working)
    (hg : GenOk (abs h)) (h64 : System.Platform.numBits = 64) :
    ∃ h1 b1, gen_cspHead h w (gen_pmbR h) 0 (decide ((gen_pmbR h).w < 0)) = ok (h1, w, b1) ∧
      (abs h1 : OsuHitObject) = gen_cspRot (abs h) (abs w) ∧ b1 = gen_pmbR h1 ∧ GenOk (abs h1) := by
  have hpi := gen_paths_ok h hg
  have hb := (gen_pmb_ok h).2
  unfold gen_cspHead gen_cspRot
  rw [← hb]
  simp only [beatmap.mod_random.slider_rotation_refines h hpi h64, beatmap.mod_random.angle_difference_refines, mr2_PI,
    float.F32.add, float.F32.lt, float.F32.sub, bind_ok, gen_rot_eq h hg h64, (gen_pmb_ok _).1]
  have hgr := fun r => (gen_rot_ok h hg h64 r).2
  have hok := fun r => gen_ok_rotate (abs h) r hg
  have ew : (abs w : Mods.Reposition.Working).rotationOriginal = w.rotation_original := rfl
  have eb1 : (abs (gen_pmbR h) : Mods.Reposition.RectF).w = (gen_pmbR h).w := rfl
  have eb2 : (abs (gen_pmbR h) : Mods.Reposition.RectF).h = (gen_pmbR h).h := rfl
  simp only [ew, eb1, eb2]
  by_cases c1 : (gen_pmbR h).w < 0
  · simp only [c1, decide_true, if_true, Bool.true_or]
    split
    · next hd =>
      simp only [decide_eq_true_eq] at hd
      simp only [bind_ok]
      refine ⟨_, _, rfl, ?_, rfl, ?_⟩ <;> rw [hgr]
      · simp only [hd, if_true]
      · exact hok _
    · next hd =>
      simp only [decide_eq_true_eq] at hd
      simp only [bind_ok]
      refine ⟨_, _, rfl, ?_, rfl, ?_⟩ <;> rw [hgr]
      · simp only [hd, if_false]
      · exact hok _
  · simp only [c1, decide_false, Bool.false_eq_true, if_false, Bool.false_or]
    by_cases c2 : (gen_pmbR h).h < 0
    · simp only [c2, decide_true, if_true]
      split
      · next hd =>
        simp only [decide_eq_true_eq] at hd
        simp only [bind_ok]
        refine ⟨_, _, rfl, ?_, rfl, ?_⟩ <;> rw [hgr]
        · simp only [hd, if_true]
        · exact hok _
      · next hd =>
        simp only [decide_eq_true_eq] at hd
        simp only [bind_ok]
        refine ⟨_, _, rfl, ?_, rfl, ?_⟩ <;> rw [hgr]
        · simp only [hd, if_false]
        · exact hok _
    · simp only [c2, decide_false, Bool.false_eq_true, if_false]
      exact ⟨_, _, rfl, rfl, rfl, hg⟩

theorem gen_csp_tail (h1 : beatmap.objects.OsuHitObject) (w : beatmap.mod_random.Working)
    (hg : GenOk (abs h1)) (h64 : System.Platform.numBits = 64) :
    ∃ e h', gen_cspTail h1 w (gen_pmbR h1) 0 = ok (e, h') ∧ GenOk (abs h') ∧
      hRel (fun p : beatmap.mod_random.Working × net.osutk.Vector2 =>
        ((abs h' : OsuHitObject), (abs p.1 : Mods.Reposition.Working), bv2S p.2)) e (gen_cspT (abs h1) (abs w)) := by
  have hpi := gen_paths_ok h1 hg
  have hb := (gen_pmb_ok h1).2
  unfold gen_cspTail gen_cspT
  rw [← hb]
  simp only [float.F32.lt, mr_BASE_SIZE, bind_ok, net.mathops.f32_clamp_refines, beatmap.mod_random.rect_right,
    beatmap.mod_random.rect_bottom, float.F32.add]
  have ew : (abs w : Mods.Reposition.Working).positionModified = bv2S w.position_modified := rfl
  have eb : (abs (gen_pmbR h1) : Mods.Reposition.RectF) = ⟨(gen_pmbR h1).x, (gen_pmbR h1).y, (gen_pmbR h1).w, (gen_pmbR h1).h⟩ := rfl
  simp only [ew, eb, Mods.Reposition.RectF.right, Mods.Reposition.RectF.bottom]
  have hsp : ∀ p : net.osutk.Vector2, ∃ h2, beatmap.mods.set_position h1 p = ok h2 ∧
      Mods.setPosition (abs h1) (bv2S p) = abs h2 ∧ GenOk (abs h2) ∧ beatmap.objects.end_position h2 = ok (bv2I (abs h2 : OsuHitObject).endPosition) := by
    intro p
    obtain ⟨h2, e2, v2⟩ := beatmap.mods.set_position_refines h1 p hpi h64
    have g2 : GenOk (abs h2) := by rw [← v2, gen_ok_setpos]; exact hg
    exact ⟨h2, e2, v2, g2, beatmap.objects.end_position_refines _ (gen_paths_ok _ g2) h64⟩
  have ex : ∀ (c : Except NetExn F32), beatmap.hit_object_parser.lift_net beatmap.errors.W_MATH_CLAMP (exceptI id c) =
      ok (match c with | .ok x => core.result.Result.Ok x | .error e => .Err (.Net beatmap.errors.W_MATH_CLAMP (exnI e))) := by
    intro c; cases c <;> rfl
  simp only [ex]
  simp only [bv2I_x, bv2I_y, bv2S_x, bv2S_y]
  by_cases cw : (gen_pmbR h1).w < 0 <;> simp only [cw, decide_true, decide_false, if_true, Bool.false_eq_true, if_false]
  all_goals
    generalize F32.clamp _ _ _ = cx
    cases cx with
    | error e =>
      simp only [bind_ok, liftNet, gen_except_bind_err]
      exact ⟨_, _, rfl, hg, trivial⟩
    | ok x =>
      simp only [bind_ok, liftNet, gen_except_bind_ok]
      by_cases ch : (gen_pmbR h1).h < 0 <;> simp only [ch, decide_true, decide_false, if_true, Bool.false_eq_true, if_false]
      all_goals
        generalize F32.clamp _ _ _ = cy
        cases cy with
        | error e =>
          simp only [bind_ok, liftNet, gen_except_bind_err]
          exact ⟨_, _, rfl, hg, trivial⟩
        | ok y =>
          simp only [bind_ok, liftNet, gen_except_bind_ok]
          obtain ⟨h2, e2, v2, g2, ep2⟩ := hsp ⟨x, y⟩
          simp only [e2, ep2, bind_ok, beatmap.vector2.sub_refines]
          refine ⟨_, _, rfl, g2, ?_⟩
          show (_ : _ × _ × _) = _
          rw [← v2]; rfl

theorem beatmap.mod_random.clamp_slider_to_playfield_refines (h : beatmap.objects.OsuHitObject)
    (w : beatmap.mod_random.Working) (hg : GenOk (abs h)) (h64 : System.Platform.numBits = 64) :
    ∃ e h', beatmap.mod_random.clamp_slider_to_playfield h w = ok (e, h') ∧ GenOk (abs h') ∧
      hRel (fun p : beatmap.mod_random.Working × net.osutk.Vector2 =>
        ((abs h' : OsuHitObject), (abs p.1 : Mods.Reposition.Working), bv2S p.2)) e
        (Mods.Reposition.clampSliderToPlayfield (abs h) (abs w)) := by
  rw [gen_csp_split, gen_csp_spec]
  simp only [(gen_pmb_ok h).1, cst_beatmap_mod_random_F0, float.F32.lt, bind_ok]
  obtain ⟨h1, b1, e1, v1, hb1, g1⟩ := gen_csp_head h w hg h64
  rw [e1]
  simp only [bind_ok]
  subst hb1
  obtain ⟨e, h', e2, g2, r2⟩ := gen_csp_tail h1 w g1 h64
  refine ⟨e, h', e2, g2, ?_⟩
  unfold gen_cspS
  rw [← v1]; exact r2
end OsuProofs
