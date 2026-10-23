/-
Generator mods, part 5 (gen agent): `beatmap::mod_random::reposition_one` (vs one iteration `gen_rpOneS`) and
`reposition_hit_objects` (spec normal form `gen_rp_spec`: `repositionHitObjects` as `gen_iterE (gen_rpF ..)`).
-/
import OsuProofs.Post.GenRD3
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

open Mods.Reposition in
/-- one non-spinner iteration of `repositionHitObjects` (spec; without `previous := some i`) -/
def gen_rpOneS (hos0 : Array OsuHitObject) (ws0 : Array Working) (infos : Array PositionInfo) (i : Nat)
    (previous : Option Nat) : DecodeM (Array OsuHitObject × Array Working) := do
  let (hos', pm) := computeModifiedPosition hos0 ws0 infos i previous (if i > 1 then some (i - 2) else none)
  let mut hos := hos'
  let mut ws := ws0.set! i { ws0[i]! with positionModified := pm }
  let mut shift := Vec2.zero
  let h := hos[i]!
  match h.kind with
  | .circle =>
    let w := ws[i]!
    let previousPosition := w.positionModified
    let p ← clampWithPadding w.positionModified (F64.toF32 h.radius)
    ws := ws.set! i { w with positionModified := p, endPositionModified := p }
    hos := hos.set! i (Mods.setPosition h p)
    shift := p - previousPosition
  | .slider _ =>
    let (h', w', s) ← clampSliderToPlayfield h ws[i]!
    hos := hos.set! i h'
    ws := ws.set! i w'
    shift := s
  | .spinner _ => pure ()
  if !shift.eq Vec2.zero then
    hos ← gen_adsS hos i shift
  return (hos, ws)

theorem gen_deref_val {α} (v : alloc.vec.Vec α) : (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref, Slice.from_val]
theorem gen_abs_deref {α β} [AbsTo α β] (v : alloc.vec.Vec α) : (abs (alloc.vec.Vec.deref v) : Array β) = abs v := by
  show ((alloc.vec.Vec.deref v).val.map abs).toArray = (v.val.map abs).toArray
  rw [gen_deref_val]

noncomputable def gen_cmpR (hos : alloc.vec.Vec beatmap.objects.OsuHitObject) (ws : alloc.vec.Vec beatmap.mod_random.Working)
    (infos : Slice beatmap.mod_random.PositionInfo) (i : Usize) (prev bp : Option Usize) :
    net.osutk.Vector2 × alloc.vec.Vec beatmap.objects.OsuHitObject :=
  @gen_val _ ⟨(⟨0, 0⟩, hos)⟩ (beatmap.mod_random.compute_modified_position hos (alloc.vec.Vec.deref ws) infos i prev bp)

theorem gen_cmp_ok (hos : alloc.vec.Vec beatmap.objects.OsuHitObject) (ws : alloc.vec.Vec beatmap.mod_random.Working)
    (infos : Slice beatmap.mod_random.PositionInfo) (i : Usize) (prev bp : Option Usize)
    (hi : i.val < hos.val.length) (hii : i.val < infos.val.length)
    (hp : ∀ p, prev = some p → p.val < hos.val.length ∧ p.val < ws.val.length)
    (hb : ∀ b, bp = some b → b.val < hos.val.length) (hg : GenOkL hos.val) (h64 : System.Platform.numBits = 64) :
    beatmap.mod_random.compute_modified_position hos (alloc.vec.Vec.deref ws) infos i prev bp = ok (gen_cmpR hos ws infos i prev bp) ∧
      Mods.Reposition.computeModifiedPosition (abs hos) (abs ws) (abs infos) i.val (prev.map (·.val)) (bp.map (·.val)) =
        (abs (gen_cmpR hos ws infos i prev bp).2, bv2S (gen_cmpR hos ws infos i prev bp).1) ∧
      GenOkL (gen_cmpR hos ws infos i prev bp).2.val ∧ (gen_cmpR hos ws infos i prev bp).2.val.length = hos.val.length := by
  obtain ⟨pm, hos', e, r1, r2, r3⟩ := beatmap.mod_random.compute_modified_position_refines hos (alloc.vec.Vec.deref ws)
    infos i prev bp hi hii (fun p h => by rw [gen_deref_val]; exact hp p h) hb hg h64
  have := @gen_val_eq _ ⟨(⟨0, 0⟩, hos)⟩ _ ⟨_, e⟩
  rw [e] at this
  have h2 := Result.ok_injective this
  unfold gen_cmpR
  rw [e, ← h2]
  rw [gen_abs_deref] at r1
  exact ⟨rfl, r1, r2, r3⟩

instance : Inhabited (core.result.Result Unit beatmap.hit_object_parser.DecodeError) := ⟨.Ok ()⟩
instance : Inhabited (alloc.vec.Vec beatmap.objects.OsuHitObject) := ⟨alloc.vec.Vec.new _⟩

noncomputable def gen_adsR (H : alloc.vec.Vec beatmap.objects.OsuHitObject) (i : Usize) (S : net.osutk.Vector2) :
    core.result.Result Unit beatmap.hit_object_parser.DecodeError × alloc.vec.Vec beatmap.objects.OsuHitObject :=
  gen_val (beatmap.mod_random.apply_decreasing_shift H i S)

theorem gen_ads_ok (H : alloc.vec.Vec beatmap.objects.OsuHitObject) (i : Usize) (S : net.osutk.Vector2)
    (hi : i.val < H.val.length) (hg : GenOkL H.val) (h64 : System.Platform.numBits = 64) :
    beatmap.mod_random.apply_decreasing_shift H i S = ok (gen_adsR H i S) ∧ GenOkL (gen_adsR H i S).2.val ∧
      (gen_adsR H i S).2.val.length = H.val.length ∧
      hRel (fun _ => (abs (gen_adsR H i S).2 : Array OsuHitObject)) (gen_adsR H i S).1 (gen_adsS (abs H) i.val (bv2S S)) := by
  obtain ⟨e, hos', h1, h2, h3, h4⟩ := beatmap.mod_random.apply_decreasing_shift_refines H i S hi hg h64
  have := gen_val_eq _ ⟨_, h1⟩
  rw [h1] at this
  have h5 := Result.ok_injective this
  unfold gen_adsR; rw [h1, ← h5]; exact ⟨rfl, h2, h3, h4⟩

instance : Inhabited (core.result.Result (beatmap.mod_random.Working × net.osutk.Vector2) beatmap.hit_object_parser.DecodeError) :=
  ⟨.Err (.Msg 0#u32)⟩

noncomputable def gen_cstR (h : beatmap.objects.OsuHitObject) (w : beatmap.mod_random.Working) :=
  @gen_val _ ⟨(default, h)⟩ (beatmap.mod_random.clamp_slider_to_playfield h w)

theorem gen_cst_ok (h : beatmap.objects.OsuHitObject) (w : beatmap.mod_random.Working) (hg : GenOk (abs h))
    (h64 : System.Platform.numBits = 64) :
    beatmap.mod_random.clamp_slider_to_playfield h w = ok (gen_cstR h w) ∧ GenOk (abs (gen_cstR h w).2) ∧
      hRel (fun p : beatmap.mod_random.Working × net.osutk.Vector2 =>
        ((abs (gen_cstR h w).2 : OsuHitObject), (abs p.1 : Mods.Reposition.Working), bv2S p.2)) (gen_cstR h w).1
        (Mods.Reposition.clampSliderToPlayfield (abs h) (abs w)) := by
  obtain ⟨e, h', h1, h2, h3⟩ := beatmap.mod_random.clamp_slider_to_playfield_refines h w hg h64
  have := @gen_val_eq _ ⟨(default, h)⟩ _ ⟨_, h1⟩
  rw [h1] at this
  have h5 := Result.ok_injective this
  unfold gen_cstR; rw [h1, ← h5]; exact ⟨rfl, h2, h3⟩

theorem gen_v2sub (a b : Vec2) : Vec2.sub a b = a - b := rfl

theorem gen_set_get {α} [Inhabited α] (a : Array α) (i : Nat) (x : α) (h : i < a.size) : (a.set! i x)[i]! = x := by
  simp [Array.set!_eq_setIfInBounds, getElem!_pos, h]
theorem gen_vset_get {α} (v : alloc.vec.Vec α) (i : Usize) (x : α) (h : i.val < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) (alloc.vec.Vec.set v i x) i = ok x := by
  rw [vec_index_eq _ _ (by simp [vec_set_val', h])]; simp [vec_set_val']
theorem gen_vset_mut {α} (v : alloc.vec.Vec α) (i : Usize) (x : α) (h : i.val < v.val.length) :
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) (alloc.vec.Vec.set v i x) i =
      ok (x, alloc.vec.Vec.set (alloc.vec.Vec.set v i x) i) := by
  rw [vec_index_mut_eq _ _ (by simp [vec_set_val', h])]; simp [vec_set_val']
theorem gen_vset_set {α} (v : alloc.vec.Vec α) (i : Usize) (x y : α) :
    alloc.vec.Vec.set (alloc.vec.Vec.set v i x) i y = alloc.vec.Vec.set v i y := by
  unfold alloc.vec.Vec.set; simp [List.set_set]
theorem gen_aset_set {α} (a : Array α) (i : Nat) (x y : α) : (a.set! i x).set! i y = a.set! i y := by
  simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds]
  split <;> simp_all [Array.set_set]

theorem beatmap.mod_random.reposition_one_refines (hos : alloc.vec.Vec beatmap.objects.OsuHitObject)
    (ws : alloc.vec.Vec beatmap.mod_random.Working) (infos : Slice beatmap.mod_random.PositionInfo) (i : Usize)
    (previous : Option Usize) (hi : i.val < hos.val.length) (hw : ws.val.length = hos.val.length)
    (hii : i.val < infos.val.length) (hp : ∀ p, previous = some p → p.val < hos.val.length)
    (hg : GenOkL hos.val) (h64 : System.Platform.numBits = 64) :
    ∃ e hos' ws', beatmap.mod_random.reposition_one hos ws infos i previous = ok (e, hos', ws') ∧
      GenOkL hos'.val ∧ hos'.val.length = hos.val.length ∧ ws'.val.length = ws.val.length ∧
      hRel (fun _ => ((abs hos' : Array OsuHitObject), (abs ws' : Array Mods.Reposition.Working))) e
        (gen_rpOneS (abs hos) (abs ws) (abs infos) i.val (previous.map (·.val))) := by
  have hwi : i.val < ws.val.length := by omega
  unfold beatmap.mod_random.reposition_one gen_rpOneS
  by_cases hi1 : i > 1#usize
  on_goal 1 =>
    obtain ⟨i2, hi2, hi2v⟩ : ∃ i2 : Usize, i - 2#usize = ok i2 ∧ i2.val = i.val - 2 := by
      obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (Usize.sub_spec (x := i) (y := 2#usize) (by scalar_tac))
      exact ⟨z, hz, by have := hzv; scalar_tac⟩
    have hS : (if i.val > 1 then some (i.val - 2) else none) = (some i2).map (·.val) := by
      have : i.val > 1 := by scalar_tac
      simp [this, hi2v]
    simp only [hi1, if_true, hi2, bind_ok]
    rw [hS]
    have hbp : ∀ b, some i2 = some b → b.val < hos.val.length := by intro b hb; cases hb; omega
    revert hbp
    generalize (some i2 : Option Usize) = bp
    intro hbp
  on_goal 2 =>
    have hS : (if i.val > 1 then some (i.val - 2) else none) = (none : Option Usize).map (·.val) := by
      have : ¬ i.val > 1 := by scalar_tac
      simp [this]
    simp only [hi1, if_false]
    rw [hS]
    have hbp : ∀ b, (none : Option Usize) = some b → b.val < hos.val.length := by intro b hb; cases hb
    revert hbp
    generalize (none : Option Usize) = bp
    intro hbp
  all_goals
    obtain ⟨hc1, hc2, hc3, hc4⟩ := gen_cmp_ok hos ws infos i previous bp hi hii
      (fun p h => ⟨hp p h, by rw [hw]; exact hp p h⟩) hbp hg h64
    rw [hc1, hc2]
    simp only [bind_ok, uncurry_apply_pair]
    generalize gen_cmpR hos ws infos i previous bp = C at hc3 hc4 ⊢
    obtain ⟨pm, hos1⟩ := C
    simp only at hc3 hc4 ⊢
    have hi' : i.val < hos1.val.length := by omega
    simp only [vec_index_mut_eq _ _ hwi, bm_vector2_ZERO, vec_index_eq _ _ hi', bind_ok, uncurry_apply_pair,
      beatmap.objects.is_circle_refines, is_slider_ok, gen_abs_get hos1 _ hi', gen_abs_get ws _ hwi]
    have hgi := gen_okl_get _ hc3 _ hi'
    have hpi := gen_okl_paths _ hc3 _ hi'
    have hwsz : (abs ws : Array Mods.Reposition.Working).size = ws.val.length := by simp [abs]
    simp only [gen_vset_get _ _ _ hwi, gen_vset_mut _ _ _ hwi, gen_set_get _ _ _ (by rw [hwsz]; exact hwi), bind_ok,
      uncurry_apply_pair, gen_vset_set]
    rcases hk : (hos1.val[i.val]'hi').kind with _ | sd | spd
    · -- circle
      simp only [OsuHitObject.isCircle, ob_kind_abs, hk, ob_abs_circle, if_true, gen_rad_ok, float.F64.to_f32, bind_ok,
        gen_cwp_ok]
      simp only [gen_aset_set]
      generalize hR : gen_cwpR _ _ = R
      have hrel := gen_cwp_split _ _ _ hR
      rw [gen_rad_abs] at hrel
      generalize hS : Mods.Reposition.clampWithPadding _ _ = S
      have hSR : hRel bv2S R S := by rw [← hS]; exact hrel
      cases R with
      | Err e =>
        obtain ⟨e', he'⟩ := gen_hrel_err hSR
        subst he'
        exact ⟨_, _, _, rfl, hc3, hc4, by simp [vec_set_val'], trivial⟩
      | Ok q =>
        have hSq := gen_hrel_ok hSR
        subst hSq
        obtain ⟨h2, e2, v2⟩ := beatmap.mods.set_position_refines (hos1.val[i.val]'hi') q hpi h64
        have g2 : GenOk (abs h2) := by rw [← v2, gen_ok_setpos]; exact hgi
        simp only [vec_index_mut_eq _ _ hi', bind_ok, uncurry_apply_pair, e2, beatmap.vector2.sub_refines,
          beatmap.vector2.eq_refines, gen_except_bind_ok]
        simp only [bv2S_I, gen_v2sub]
        have hset : (abs (hos1.set i h2) : Array OsuHitObject) =
            (abs hos1 : Array OsuHitObject).set! i.val (Mods.setPosition (abs (hos1.val[i.val]'hi')) (bv2S q)) := by
          rw [gen_abs_set, v2]
        have hgs : GenOkL (hos1.set i h2).val := by rw [vec_set_val']; exact gen_okl_set _ hc3 _ _ g2
        have hls : (hos1.set i h2).val.length = hos.val.length := by simp [vec_set_val', hc4]
        by_cases hz : (bv2S q - bv2S pm).eq Vec2.zero
        · simp only [hz, if_true, Bool.not_true, Bool.false_eq_true, if_false]
          refine ⟨_, _, _, rfl, hgs, hls, by simp [vec_set_val'], ?_⟩
          show (_, _) = _
          rw [hset, gen_abs_set]; rfl
        · simp only [hz, Bool.false_eq_true, if_false, Bool.not_false, if_true]
          obtain ⟨a1, a2, a3, a4⟩ := gen_ads_ok (hos1.set i h2) i (bv2I (bv2S q - bv2S pm))
            (by simp [vec_set_val']; omega) hgs h64
          rw [a1]
          simp only [bind_ok, uncurry_apply_pair]
          rw [hset, bv2S_I] at a4
          revert a4
          generalize gen_adsR (hos1.set i h2) i (bv2I (bv2S q - bv2S pm)) = A at a2 a3 ⊢
          obtain ⟨r1, hos3⟩ := A
          intro a4
          simp only at a2 a3 a4 ⊢
          cases r1 with
          | Ok u =>
            have a5 := gen_hrel_ok a4
            rw [a5]
            refine ⟨_, _, _, rfl, a2, by omega, by simp [vec_set_val'], ?_⟩
            show (_, _) = _
            rw [gen_abs_set]; rfl
          | Err e =>
            obtain ⟨e', a5⟩ := gen_hrel_err a4
            rw [a5]
            exact ⟨_, _, _, rfl, a2, by omega, by simp [vec_set_val'], trivial⟩
    · -- slider
      simp only [OsuHitObject.isCircle, OsuHitObject.isSlider, ob_kind_abs, hk, ob_abs_slider, Bool.false_eq_true,
        if_false, if_true, vec_index_mut_eq _ _ hi', bind_ok, uncurry_apply_pair]
      obtain ⟨c1, c2, c3⟩ := gen_cst_ok (hos1.val[i.val]'hi')
        { (ws.val[i.val]'hwi) with position_modified := pm } hgi h64
      rw [c1]
      simp only [bind_ok, uncurry_apply_pair]
      revert c2 c3
      generalize gen_cstR (hos1.val[i.val]'hi') { (ws.val[i.val]'hwi) with position_modified := pm } = CR
      obtain ⟨r, oho2⟩ := CR
      intro c2 c3
      simp only at c2 c3 ⊢
      generalize hS : Mods.Reposition.clampSliderToPlayfield _ _ = S
      have c4 : hRel (fun p : beatmap.mod_random.Working × net.osutk.Vector2 =>
          ((abs oho2 : OsuHitObject), (abs p.1 : Mods.Reposition.Working), bv2S p.2)) r S := by rw [← hS]; exact c3
      have hgs : GenOkL (hos1.set i oho2).val := by rw [vec_set_val']; exact gen_okl_set _ hc3 _ _ c2
      have hls : (hos1.set i oho2).val.length = hos.val.length := by simp [vec_set_val', hc4]
      have hset : (abs (hos1.set i oho2) : Array OsuHitObject) = (abs hos1 : Array OsuHitObject).set! i.val (abs oho2) :=
        gen_abs_set _ _ _
      cases r with
      | Err e =>
        obtain ⟨e', a5⟩ := gen_hrel_err c4
        subst a5
        exact ⟨_, _, _, rfl, hgs, hls, by simp [vec_set_val'], trivial⟩
      | Ok v =>
        obtain ⟨w2, s1⟩ := v
        have a5 := gen_hrel_ok c4
        subst a5
        simp only [uncurry_apply_pair, gen_except_bind_ok, beatmap.vector2.eq_refines, bind_ok, bv2S_I, gen_aset_set]
        by_cases hz : (bv2S s1).eq Vec2.zero
        · simp only [hz, if_true, Bool.not_true, Bool.false_eq_true, if_false]
          refine ⟨_, _, _, rfl, hgs, hls, by simp [vec_set_val'], ?_⟩
          show (_, _) = _
          rw [hset, gen_abs_set]
        · simp only [hz, Bool.false_eq_true, if_false, Bool.not_false, if_true]
          obtain ⟨a1, a2, a3, a4⟩ := gen_ads_ok (hos1.set i oho2) i s1 (by simp [vec_set_val']; omega) hgs h64
          rw [a1]
          simp only [bind_ok, uncurry_apply_pair]
          rw [hset] at a4
          revert a4
          generalize gen_adsR (hos1.set i oho2) i s1 = A at a2 a3 ⊢
          obtain ⟨r1, hos3⟩ := A
          intro a4
          simp only at a2 a3 a4 ⊢
          cases r1 with
          | Ok u =>
            have a6 := gen_hrel_ok a4
            rw [a6]
            refine ⟨_, _, _, rfl, a2, by omega, by simp [vec_set_val'], ?_⟩
            show (_, _) = _
            rw [gen_abs_set]
          | Err e =>
            obtain ⟨e', a6⟩ := gen_hrel_err a4
            rw [a6]
            exact ⟨_, _, _, rfl, a2, by omega, by simp [vec_set_val'], trivial⟩
    · -- spinner
      simp only [OsuHitObject.isCircle, OsuHitObject.isSlider, ob_kind_abs, hk, ob_abs_spinner, Bool.false_eq_true,
        if_false, beatmap.vector2.eq_refines, bind_ok, bv2S_I]
      have hzz : Vec2.zero.eq Vec2.zero = true := by decide
      simp only [hzz, if_true, Bool.not_true, Bool.false_eq_true, if_false]
      refine ⟨_, _, _, rfl, hc3, hc4, by simp [vec_set_val'], ?_⟩
      show (_, _) = _
      rw [gen_abs_set]; rfl
end OsuProofs

open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl

theorem gen_iterE_pure {ε S : Type} (f : Nat → S → ForInStep S) :
    ∀ n j s, gen_iterE (ε := ε) (fun k s => pure (f k s)) j n s = .ok (iterR f j n s) := by
  intro n
  induction n with
  | zero => intro j s; rfl
  | succ n ih =>
    intro j s
    simp only [gen_iterE, iterR]
    cases h : f j s with
    | done c => rfl
    | yield c => exact ih (j + 1) c

theorem gen_shiftBlock {β : Type} (hos : Array OsuHitObject) (i : Nat) (shift : Vec2)
    (k : Array OsuHitObject → Except String β) :
    (do
      let tbs ← forIn (m := Except String) [1:11] (#[] : Array Nat) fun k s =>
        if k > i then pure (ForInStep.done s)
        else if (!hos[i - k]!.isCircle) = true then pure (ForInStep.done s)
        else pure (ForInStep.yield (s.push (i - k)))
      let h2 ← forIn [:tbs.size] hos fun idx s => do
        let p ← Mods.Reposition.clampWithPadding
          (s[tbs[idx]!]!.position + { x := shift.x * (F32.ofInt ↑(tbs.size - idx) / F32.ofInt ↑(tbs.size + 1)),
                                      y := shift.y * (F32.ofInt ↑(tbs.size - idx) / F32.ofInt ↑(tbs.size + 1)) })
          s[tbs[idx]!]!.radius.toF32
        pure (ForInStep.yield (s.set! tbs[idx]! (Mods.setPosition s[tbs[idx]!]! p)))
      k h2) = (gen_adsS hos i shift >>= k) := by
  rw [gen_forIn_range_iterE]
  have hF : (fun (k : Nat) (s : Array Nat) =>
      (if k > i then pure (ForInStep.done s)
        else if (!hos[i - k]!.isCircle) = true then pure (ForInStep.done s)
        else pure (ForInStep.yield (s.push (i - k))) : Except String (ForInStep (Array Nat)))) =
      fun k s => pure (gen_tbsF hos i k s) := by
    funext k s; unfold gen_tbsF; split_ifs <;> rfl
  rw [hF, gen_iterE_pure, ← gen_tbs_eq]
  rw [gen_ads_eq]
  simp only [gen_except_bind_ok]
  rw [gen_forIn_range_iterE, Nat.sub_zero]
  congr 2
  funext idx s
  unfold gen_adsF
  simp only []
  split <;> next heq => rw [heq]; rfl

def gen_wsInit (h : OsuHitObject) : Mods.Reposition.Working :=
  { rotationOriginal := if h.isSlider then Mods.Reposition.sliderRotation h else 0,
    positionModified := h.position, endPositionModified := h.endPosition }

/-- one iteration of `repositionHitObjects` (spec normal form; state: objects, working objects, previous) -/
def gen_rpF (infos : Array Mods.Reposition.PositionInfo) (i : Nat)
    (s : Array OsuHitObject × Array Mods.Reposition.Working × Option Nat) :
    Except String (ForInStep (Array OsuHitObject × Array Mods.Reposition.Working × Option Nat)) :=
  if s.1[i]!.isSpinner then .ok (.yield (s.1, s.2.1, some i))
  else gen_rpOneS s.1 s.2.1 infos i s.2.2 >>= fun r => pure (.yield (r.1, r.2, some i))

theorem gen_rp_spec (hos : Array OsuHitObject) (infos : Array Mods.Reposition.PositionInfo) :
    Mods.Reposition.repositionHitObjects hos infos =
      gen_iterE (gen_rpF infos) 0 hos.size (hos, hos.map gen_wsInit, none) >>= fun s => pure s.1 := by
  unfold Mods.Reposition.repositionHitObjects
  simp only []
  rw [gen_forIn_range_iterE, Nat.sub_zero]
  simp only [gen_shiftBlock]
  refine congrArg (fun F => gen_iterE F 0 hos.size (hos, hos.map gen_wsInit, none) >>= fun s => pure s.1) ?_
  funext i s
  unfold gen_rpF gen_rpOneS
  split
  · rfl
  · generalize Mods.Reposition.computeModifiedPosition s.1 s.2.1 infos i s.2.2 (if i > 1 then some (i - 2) else none) = CM
    obtain ⟨H, PM⟩ := CM
    simp only []
    generalize hK : H[i]!.kind = K
    cases K
    · simp only []
      generalize Mods.Reposition.clampWithPadding _ _ = C
      cases C
      · rfl
      · simp only [gen_except_bind_ok]
        split
        · generalize gen_adsS _ _ _ = A
          cases A <;> rfl
        · rfl
    · simp only []
      generalize Mods.Reposition.clampSliderToPlayfield _ _ = C
      cases C
      · rfl
      · simp only [gen_except_bind_ok]
        split
        · generalize gen_adsS _ _ _ = A
          cases A <;> rfl
        · rfl
    · rfl
end OsuProofs

open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl

theorem gen_iterR_push {α : Type} (f : Nat → α) :
    ∀ n j (a : Array α), iterR (fun k s => .yield (s.push (f k))) j n a = a ++ ((List.range' j n).map f).toArray := by
  intro n
  induction n with
  | zero => intro j a; simp [iterR]
  | succ n ih =>
    intro j a
    simp only [iterR]
    rw [ih, List.range'_succ]
    simp

theorem gen_map_range {α β} [Inhabited α] (a : Array α) (g : α → β) :
    a.map g = ((List.range' 0 a.size).map (fun k => g a[k]!)).toArray := by
  apply Array.ext
  · simp
  · intro n h1 h2
    simp at h1
    simp [getElem!_pos, h1]

theorem gen_rp_loop0 (hos : alloc.vec.Vec beatmap.objects.OsuHitObject) (hg : GenOkL hos.val)
    (h64 : System.Platform.numBits = 64) :
    ∃ ws, beatmap.mod_random.reposition_hit_objects_loop0 hos
        (alloc.vec.Vec.with_capacity beatmap.mod_random.Working (alloc.vec.Vec.len hos)) 0#usize = ok ws ∧
      (abs ws : Array Mods.Reposition.Working) = (abs hos : Array OsuHitObject).map gen_wsInit := by
  obtain ⟨y, hl, hv⟩ := loop_fold_gen'
    (fun x : alloc.vec.Vec beatmap.mod_random.Working × Usize =>
      beatmap.mod_random.reposition_hit_objects_loop0.body hos x.1 x.2) (·.2)
    hos.val.length (by have := hos.property; omega)
    (fun x => x.1.val.length = x.2.val)
    (fun x => (abs x.1 : Array Mods.Reposition.Working))
    (fun k s => s.push (gen_wsInit ((abs hos : Array OsuHitObject)[k]!)))
    (fun y s => (abs y : Array Mods.Reposition.Working) = s)
    (by
      rintro ⟨ws, k⟩ hI hlt j1 hj1 hj1v
      simp only at hI hlt hj1 hj1v ⊢
      have hk : k.val < hos.val.length := hlt
      have hpk := gen_okl_paths _ hg _ hk
      have hpush : ws.val.length < Usize.max := by have := hos.property; omega
      have hga := gen_abs_get (β := OsuHitObject) hos k.val hk
      simp only [beatmap.mod_random.reposition_hit_objects_loop0.body, vec_lt_len_iff, hk, if_true,
        vec_index_eq _ _ hk, bind_ok, is_slider_ok, beatmap.mod_random.slider_rotation_refines _ hpk h64,
        beatmap.objects.end_position_refines _ hpk h64, cst_beatmap_mod_random_F0, hj1]
      split
      · next hs =>
        simp only [vec_push_ok _ _ hpush, bind_ok, hj1]
        refine ⟨_, rfl, rfl, ?_, by simp [hI, hj1v]⟩
        rw [gen_abs_vpush, hga]
        simp only [gen_wsInit, hs, if_true]; rfl
      · next hs =>
        simp only [vec_push_ok _ _ hpush, bind_ok, hj1]
        refine ⟨_, rfl, rfl, ?_, by simp [hI, hj1v]⟩
        rw [gen_abs_vpush, hga]
        simp only [gen_wsInit, hs, Bool.false_eq_true, if_false]; rfl)
    (by
      rintro ⟨ws, k⟩ hI hge
      simp only at hI hge ⊢
      have : ¬ k < alloc.vec.Vec.len hos := by rw [vec_lt_len_iff]; omega
      exact ⟨ws, by simp [beatmap.mod_random.reposition_hit_objects_loop0.body, this], rfl⟩)
    (alloc.vec.Vec.with_capacity _ (alloc.vec.Vec.len hos), 0#usize) (by simp [alloc.vec.Vec.with_capacity]) (by simp)
  refine ⟨y, by unfold beatmap.mod_random.reposition_hit_objects_loop0; exact hl, ?_⟩
  rw [hv, gen_iterR_push, gen_map_range]
  have hS : (abs hos : Array OsuHitObject).size = hos.val.length := by simp [abs]
  rw [hS]
  simp [alloc.vec.Vec.with_capacity, abs]

theorem gen_rp_loop1 (hos0 : alloc.vec.Vec beatmap.objects.OsuHitObject) (infos : Slice beatmap.mod_random.PositionInfo)
    (ws0 : alloc.vec.Vec beatmap.mod_random.Working) (hw : ws0.val.length = hos0.val.length)
    (hii : hos0.val.length ≤ infos.val.length) (hg : GenOkL hos0.val) (h64 : System.Platform.numBits = 64) :
    ∃ y, beatmap.mod_random.reposition_hit_objects_loop1 hos0 infos ws0 none none 0#usize = ok y ∧
      GenOkL y.1.val ∧ y.1.val.length = hos0.val.length ∧
      (match gen_iterE (gen_rpF (abs infos)) 0 hos0.val.length ((abs hos0 : Array OsuHitObject), (abs ws0 : Array Mods.Reposition.Working), none) with
       | .ok s => y.2 = none ∧ (abs y.1 : Array OsuHitObject) = s.1
       | .error _ => y.2.isSome) := by
  have := gen_loop_iterE (fun t : alloc.vec.Vec beatmap.objects.OsuHitObject × alloc.vec.Vec beatmap.mod_random.Working ×
        Option Usize × Option beatmap.hit_object_parser.DecodeError × Usize =>
      beatmap.mod_random.reposition_hit_objects_loop1.body infos t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2)
    (gen_rpF (abs infos)) hos0.val.length (fun t => t.2.2.2.2.val)
    (fun t s => t.2.2.2.1 = none ∧ (abs t.1 : Array OsuHitObject) = s.1 ∧ (abs t.2.1 : Array Mods.Reposition.Working) = s.2.1 ∧
      t.2.2.1.map (·.val) = s.2.2 ∧ GenOkL t.1.val ∧ t.1.val.length = hos0.val.length ∧
      t.2.1.val.length = hos0.val.length ∧ (∀ p, t.2.2.1 = some p → p.val < hos0.val.length))
    (fun y q => GenOkL y.1.val ∧ y.1.val.length = hos0.val.length ∧
      (match q with
       | .ok s => y.2 = none ∧ (abs y.1 : Array OsuHitObject) = s.1
       | .error _ => y.2.isSome))
    (by
      rintro ⟨hs, ws, pv, err, i⟩ ⟨s1, s2, s3⟩ ⟨herr, h1, h2, h3, hgl, hl1, hl2, hpv⟩ hlt
      simp only at herr h1 h2 h3 hgl hl1 hl2 hpv hlt ⊢
      subst herr h1 h2 h3
      have hi : i.val < hs.val.length := by omega
      have hsp := is_spinner_ok (hs.val[i.val]'hi)
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := hs.property; omega)
      have hga := gen_abs_get (β := OsuHitObject) hs i.val hi
      by_cases hS : (abs (hs.val[i.val]'hi) : OsuHitObject).isSpinner
      · have hF : gen_rpF (abs infos) i.val (abs hs, abs ws, pv.map (·.val)) = .ok (.yield (abs hs, abs ws, some i.val)) := by
          unfold gen_rpF; simp only [hga, hS, if_true]
        rw [hF]
        refine ⟨fun s' h => ?_, (fun s' h => by cases h), (fun e h => by cases h)⟩
        cases h
        refine ⟨(hs, ws, some i, none, i1), ?_, hi1v, rfl, rfl, rfl, rfl, hgl, hl1, hl2, ?_⟩
        · simp only [beatmap.mod_random.reposition_hit_objects_loop1.body, core.option.Option.is_none, Option.isNone_none, vec_lt_len_iff, hi,
            if_true, vec_index_eq _ _ hi, bind_ok, hsp, hS, uncurry_apply_pair, hi1]
        · intro p hp; cases hp; omega
      · obtain ⟨e, hos', ws', r1, r2, r3, r4, r5⟩ := beatmap.mod_random.reposition_one_refines hs ws infos i pv hi
          (by omega) (by omega) (fun p hp => by have := hpv p hp; omega) hgl h64
        have hF : gen_rpF (abs infos) i.val (abs hs, abs ws, pv.map (·.val)) =
            gen_rpOneS (abs hs) (abs ws) (abs infos) i.val (pv.map (·.val)) >>= fun r => pure (.yield (r.1, r.2, some i.val)) := by
          unfold gen_rpF; simp only [hga, hS, Bool.false_eq_true, if_false]
        rw [hF]
        revert r5
        generalize gen_rpOneS (abs hs) (abs ws) (abs infos) i.val (pv.map (·.val)) = G
        intro r5
        cases e with
        | Ok u =>
          have hG := gen_hrel_ok r5
          subst hG
          refine ⟨fun s' h => ?_, (fun s' h => by cases h), (fun e h => by cases h)⟩
          cases h
          refine ⟨(hos', ws', some i, none, i1), ?_, hi1v, rfl, rfl, rfl, rfl, r2, by rw [r3, hl1], by rw [r4, hl2], ?_⟩
          · simp only [beatmap.mod_random.reposition_hit_objects_loop1.body, core.option.Option.is_none, Option.isNone_none, vec_lt_len_iff, hi,
              if_true, vec_index_eq _ _ hi, bind_ok, hsp, hS, Bool.false_eq_true, if_false, r1, uncurry_apply_pair, hi1]
          · intro p hp; cases hp; omega
        | Err er =>
          obtain ⟨e', hG⟩ := gen_hrel_err r5
          subst hG
          refine ⟨(fun s' h => by cases h), (fun s' h => by cases h), fun e h => ?_⟩
          refine ⟨(hos', some er), Or.inr ⟨(hos', ws', some i, some er, i1), ?_, ?_⟩, r2, by rw [r3, hl1], rfl⟩
          · simp only [beatmap.mod_random.reposition_hit_objects_loop1.body, core.option.Option.is_none, Option.isNone_none, vec_lt_len_iff, hi,
              if_true, vec_index_eq _ _ hi, bind_ok, hsp, hS, Bool.false_eq_true, if_false, r1, uncurry_apply_pair, hi1]
          · simp [beatmap.mod_random.reposition_hit_objects_loop1.body])
    (by
      rintro ⟨hs, ws, pv, err, i⟩ ⟨s1, s2, s3⟩ ⟨herr, h1, h2, h3, hgl, hl1, hl2, hpv⟩ hge
      simp only at herr h1 h2 h3 hgl hl1 hl2 hpv hge ⊢
      subst herr h1
      have : ¬ i < alloc.vec.Vec.len hs := by rw [vec_lt_len_iff]; omega
      exact ⟨(hs, none), by simp [beatmap.mod_random.reposition_hit_objects_loop1.body, this], hgl, hl1, rfl, rfl⟩)
    (hos0, ws0, none, none, 0#usize) (abs hos0, abs ws0, none)
    ⟨rfl, rfl, rfl, rfl, hg, rfl, hw, fun p hp => by cases hp⟩ (by simp)
  obtain ⟨y, hl, hq⟩ := this
  exact ⟨y, by unfold beatmap.mod_random.reposition_hit_objects_loop1; exact hl, hq⟩

theorem beatmap.mod_random.reposition_hit_objects_refines (hos : alloc.vec.Vec beatmap.objects.OsuHitObject)
    (infos : Slice beatmap.mod_random.PositionInfo) (hii : hos.val.length ≤ infos.val.length) (hg : GenOkL hos.val)
    (h64 : System.Platform.numBits = 64) :
    ∃ e hos', beatmap.mod_random.reposition_hit_objects hos infos = ok (e, hos') ∧ GenOkL hos'.val ∧
      hos'.val.length = hos.val.length ∧
      hRel (fun _ => (abs hos' : Array OsuHitObject)) e
        (Mods.Reposition.repositionHitObjects (abs hos) (abs infos)) := by
  obtain ⟨ws, h0, hws⟩ := gen_rp_loop0 hos hg h64
  have hwl : ws.val.length = hos.val.length := by
    have := congrArg Array.size hws; simpa [abs] using this
  obtain ⟨y, h1, g1, l1, hq⟩ := gen_rp_loop1 hos infos ws hwl hii hg h64
  unfold beatmap.mod_random.reposition_hit_objects
  simp only [h0, bind_ok, h1]
  rw [gen_rp_spec, ← hws]
  have hS : (abs hos : Array OsuHitObject).size = hos.val.length := by simp [abs]
  rw [hS]
  obtain ⟨hos', err⟩ := y
  simp only at g1 l1 hq ⊢
  revert hq
  generalize gen_iterE _ _ _ _ = q
  intro hq
  cases q with
  | ok s =>
    obtain ⟨he, hs⟩ := hq
    subst he
    exact ⟨_, _, rfl, g1, l1, hs⟩
  | error e =>
    cases err with
    | none => simp at hq
    | some e' => exact ⟨_, _, rfl, g1, l1, trivial⟩
end OsuProofs

