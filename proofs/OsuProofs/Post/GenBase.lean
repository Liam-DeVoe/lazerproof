/-
Generator mods (Random / Target Practice), part 1 (gen agent): the size side condition `GenOk` of
slider paths that are rebuilt from moved control points (closed under `modifySlider` / `setPosition`),
and the small `beatmap::mod_random` fns `rotate_slider`, `flip_slider_in_place_horizontally`,
`combo_started`, `centre_of_mass(_path)`.
-/
import OsuProofs.Post.ModsReflect
import OsuProofs.Post.ModRandom
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

/-- control points with every position moved by `ψ` -/
def genMapPos (ψ : Vec2 → Vec2) (cps : Array PathControlPoint) : Array PathControlPoint :=
  cps.map fun p => { p with position := ψ p.position }

/-- size bounds of the slider path rebuilt from `cps` (`new SliderPath(cps, e)`, `OptimiseCatmull`) -/
def GenPB (cps : Array PathControlPoint) (e : Option F64) : Prop :=
  (SliderPath.calculatePath ⟨cps, e, true⟩).1.size < 2^62 ∧
  (SliderPath.ofControlPoints cps e true).cumulativeLength.size < 2^61 ∧
  (SliderPath.ofControlPoints cps e true).calculatedPath.size < 2^62

/-- Size side condition of the generator mods on one hit object: its slider path is in the machine
ranges, and so is every path rebuilt from its control points moved by any map (the repositioning
rotates/flips sliders a data-dependent number of times). -/
def GenOk (h : OsuHitObject) : Prop :=
  ∀ s, h.kind = .slider s → s.path.cumulativeLength.size < 2^61 ∧ s.path.calculatedPath.size < 2^62 ∧
    s.path.spec.controlPoints.size < 2^32 ∧
    ∀ ψ, GenPB (genMapPos ψ s.path.spec.controlPoints) s.path.spec.expectedDistance

theorem gen_calcLength_spec (sp : SliderPathSpec) (p : Array Vec2) (ol : F64) :
    (SliderPath.calculateLength sp p ol).spec = sp := by
  unfold SliderPath.calculateLength
  simp only [Id.run]
  split
  · rfl
  · generalize (forIn (m := Id) [:p.size - 1] (ol, (#[0] : _root_.Array F64)) _) = s
    dsimp only [Bind.bind]
    split_ifs <;> rfl

theorem gen_ocp_spec (cps : Array PathControlPoint) (e : Option F64) (oc : Bool) :
    (SliderPath.ofControlPoints cps e oc).spec = ⟨cps, e, oc⟩ := by
  unfold SliderPath.ofControlPoints SliderPath.compute
  exact gen_calcLength_spec _ _ _

/-- the position map `Mods.modifySlider f` applies to each control point -/
def genMsMap (f : Vec2 → Vec2) (q : Vec2) : Vec2 :=
  Mods.newControlPointPos (Mods.setControlPointPos (Mods.newControlPointPos q) (f (Mods.newControlPointPos q)))

theorem gen_msCps (f : Vec2 → Vec2) (cps : Array PathControlPoint) : msCps f cps = genMapPos (genMsMap f) cps := by
  simp only [msCps, genMapPos, Array.map_map]
  rfl

theorem gen_mapPos_mapPos (ψ φ : Vec2 → Vec2) (cps : Array PathControlPoint) :
    genMapPos ψ (genMapPos φ cps) = genMapPos (ψ ∘ φ) cps := by
  simp only [genMapPos, Array.map_map]; rfl

theorem gen_ms_ok (f : Vec2 → Vec2) (h : OsuHitObject) (hg : GenOk h) : MsOk f h := by
  intro s hs
  obtain ⟨-, -, hn, hψ⟩ := hg s hs
  obtain ⟨a, b, c⟩ := hψ (genMsMap f)
  refine ⟨hn, ?_, ?_, ?_⟩
  · simp only [msSpec, gen_msCps]; exact a
  · rw [gen_msCps]; exact b
  · rw [gen_msCps]; exact c

theorem gen_unp_kind (h : OsuHitObject) : (updateNestedPositions h).kind = h.kind := msr_unp_kind h

theorem gen_ok_setpos (h : OsuHitObject) (p : Vec2) : GenOk (Mods.setPosition h p) ↔ GenOk h := by
  unfold GenOk Mods.setPosition; rw [gen_unp_kind]

theorem gen_ok_modify (f : Vec2 → Vec2) (h : OsuHitObject) (hg : GenOk h) : GenOk (Mods.modifySlider f h) := by
  unfold Mods.modifySlider
  split
  · next s hs =>
    intro s' hs'
    rw [gen_unp_kind] at hs'
    simp only at hs'
    cases hs'
    obtain ⟨-, -, hn, hψ⟩ := hg s hs
    have e := gen_ocp_spec (genMapPos (genMsMap f) s.path.spec.controlPoints) s.path.spec.expectedDistance true
    have e2 : (s.path.spec.controlPoints.map fun p =>
          { p with position := Mods.setControlPointPos (Mods.newControlPointPos p.position) (f (Mods.newControlPointPos p.position)) }).map
        (fun p => { p with position := Mods.newControlPointPos p.position }) = genMapPos (genMsMap f) s.path.spec.controlPoints := by
      rw [← gen_msCps]; rfl
    simp only [e2, e]
    obtain ⟨a, b, c⟩ := hψ (genMsMap f)
    refine ⟨b, c, by simpa [genMapPos] using hn, ?_⟩
    intro ψ
    rw [gen_mapPos_mapPos]; exact hψ _
  · exact hg

theorem gen_paths_ok (h : beatmap.objects.OsuHitObject) (hg : GenOk (abs h)) :
    ∀ s, h.kind = .Slider s → obPathOk s.path :=
  msr_paths_ok h (fun s hs => by obtain ⟨a, b, -⟩ := hg s hs; exact ⟨a, b⟩)

theorem gen_ok_nonslider (h : OsuHitObject) (hs : h.isSlider = false) : GenOk h := by
  intro s hk; simp [OsuHitObject.isSlider, hk] at hs

/-! ## rotate / flip -/

theorem beatmap.mod_random.rotate_slider_refines (h : beatmap.objects.OsuHitObject) (r : F32)
    (hg : GenOk (abs h)) (h64 : System.Platform.numBits = 64) :
    ∃ o, beatmap.mod_random.rotate_slider h r = ok o ∧ Mods.Reposition.rotateSlider (abs h) r = abs o := by
  obtain ⟨o, ho, hov⟩ := beatmap.mods.modify_slider_refines (.Rotate r) h (gen_ms_ok _ _ hg) h64
  exact ⟨o, ho, hov⟩

theorem beatmap.mod_random.flip_slider_in_place_horizontally_refines (h : beatmap.objects.OsuHitObject)
    (hg : GenOk (abs h)) (h64 : System.Platform.numBits = 64) :
    ∃ o, beatmap.mod_random.flip_slider_in_place_horizontally h = ok o ∧
      Mods.Reposition.flipSliderInPlaceHorizontally (abs h) = abs o := by
  obtain ⟨o, ho, hov⟩ := beatmap.mods.modify_slider_refines .NegX h (gen_ms_ok _ _ hg) h64
  exact ⟨o, ho, hov⟩

theorem gen_ok_rotate (h : OsuHitObject) (r : F32) (hg : GenOk h) : GenOk (Mods.Reposition.rotateSlider h r) :=
  gen_ok_modify _ _ hg
theorem gen_ok_flip (h : OsuHitObject) (hg : GenOk h) : GenOk (Mods.Reposition.flipSliderInPlaceHorizontally h) :=
  gen_ok_modify _ _ hg

/-! ## centre of mass -/

theorem gen_u64_add_one (i : U64) (h : i.val + 1 ≤ U64.max) :
    ∃ z, i + 1#u64 = ok z ∧ z.val = i.val + 1 := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (U64.add_spec (x := i) (y := 1#u64) (by simpa using h))
  exact ⟨z, hz, by simpa using hv⟩

/-- `Reposition.centreOfMass` on a given path (its body, `path := P`) -/
def gen_comP (path : SliderPath) : Vec2 := Id.run do
  let sampleStep : F64 := 50
  if path.distance ≤ sampleStep then
    let e := path.positionAt 1
    return ⟨e.x / 2, e.y / 2⟩
  let mut count : Nat := 0
  let mut sum : Vec2 := Vec2.zero
  let pathDistance := path.distance
  let mut i : F64 := 0
  for _ in [0:100000000] do
    if !(i < pathDistance) then break
    sum := sum + path.positionAt (i / pathDistance)
    count := count + 1
    i := i + sampleStep
  let c := F32.ofInt count
  return ⟨sum.x / c, sum.y / c⟩

theorem gen_com_eq (h : OsuHitObject) : Mods.Reposition.centreOfMass h = gen_comP (Mods.Reposition.sliderPath h) := rfl

def gen_comF (P : SliderPath) (pd : F64) (_ : Nat) (s : Nat × Vec2 × F64) : ForInStep (Nat × Vec2 × F64) :=
  if !(s.2.2 < pd) then .done s else .yield (s.1 + 1, s.2.1 + P.positionAt (s.2.2 / pd), s.2.2 + 50)

theorem gen_com_loop (p : beatmap.slider_path.SliderPath) (hp : obPathOk p) (h64 : System.Platform.numBits = 64)
    (pd : F64) (sum : net.osutk.Vector2) :
    ∃ y, beatmap.mod_random.centre_of_mass_path_loop p 50 0#u64 sum pd 0 0#u64 = ok y ∧
      y.1.val = (iterR (gen_comF (spS p) pd) 0 100000000 (0, bv2S sum, 0)).1 ∧
      bv2S y.2 = (iterR (gen_comF (spS p) pd) 0 100000000 (0, bv2S sum, 0)).2.1 := by
  have := loop_iterR (fun t : U64 × net.osutk.Vector2 × F64 × U64 =>
      beatmap.mod_random.centre_of_mass_path_loop.body p 50 pd t.1 t.2.1 t.2.2.1 t.2.2.2)
    (gen_comF (spS p) pd) 100000000 (fun t => t.2.2.2.val)
    (fun t s => t.1.val = s.1 ∧ bv2S t.2.1 = s.2.1 ∧ t.2.2.1 = s.2.2 ∧ t.1.val = t.2.2.2.val)
    (fun y s => y.1.val = s.1 ∧ bv2S y.2 = s.2.1)
    (by
      rintro ⟨c, sm, i, fu⟩ ⟨sc, ss, si⟩ ⟨h1, h2, h3, h4⟩ hlt
      simp only at h1 h2 h3 h4 hlt ⊢
      subst h3
      constructor
      · intro s' hs'
        unfold gen_comF at hs'
        split at hs'
        · cases hs'
        · cases hs'
          next hc =>
          have hc' : i < pd := by simpa using hc
          obtain ⟨c1, hc1, hc1v⟩ := gen_u64_add_one c (by scalar_tac)
          obtain ⟨f1, hf1, hf1v⟩ := gen_u64_add_one fu (by scalar_tac)
          refine ⟨(c1, bv2I (Vec2.add (bv2S sm) (SliderPath.positionAt (spS p) (i / pd))), i + 50, f1), ?_, ?_, ?_⟩
          · simp only [beatmap.mod_random.centre_of_mass_path_loop.body, float.F64.lt, hc', decide_true, if_true,
              show fu < 100000000#u64 by scalar_tac, float.F64.div, bind_ok,
              beatmap.slider_path.position_at_refines p _ hp.1 hp.2 h64, beatmap.vector2.add_refines, hc1, float.F64.add, hf1]
            rfl
          · simp only; omega
          · refine ⟨by simp only; omega, ?_, rfl, by simp only; omega⟩
            simp only [bv2S_I]; rw [h2]; rfl
      · intro s' hs'
        unfold gen_comF at hs'
        split at hs'
        · cases hs'
          next hc =>
          have hc' : ¬ i < pd := by simpa using hc
          refine ⟨(c, sm), Or.inl ?_, h1, h2⟩
          simp only [beatmap.mod_random.centre_of_mass_path_loop.body, float.F64.lt, hc', decide_false, bind_ok]
          rfl
        · cases hs')
    (by
      rintro ⟨c, sm, i, fu⟩ ⟨sc, ss, si⟩ ⟨h1, h2, h3, h4⟩ hge
      simp only at h1 h2 h3 h4 hge ⊢
      refine ⟨(c, sm), ?_, h1, h2⟩
      simp only [beatmap.mod_random.centre_of_mass_path_loop.body, float.F64.lt, bind_ok,
        show ¬ fu < 100000000#u64 by scalar_tac]
      split <;> rfl)
    (0#u64, sum, 0, 0#u64) (0, bv2S sum, 0) ⟨rfl, rfl, rfl, rfl⟩ (by simp)
  obtain ⟨y, hl, hq1, hq2⟩ := this
  exact ⟨y, by unfold beatmap.mod_random.centre_of_mass_path_loop; exact hl, hq1, hq2⟩

theorem beatmap.mod_random.centre_of_mass_path_refines (p : beatmap.slider_path.SliderPath) (hp : obPathOk p)
    (h64 : System.Platform.numBits = 64) :
    beatmap.mod_random.centre_of_mass_path p = ok (bv2I (gen_comP (spS p))) := by
  unfold beatmap.mod_random.centre_of_mass_path gen_comP
  simp only [Id.run, cst_beatmap_mod_random_D50, beatmap.slider_path.distance_refines, float.F64.le, bind_ok]
  by_cases hd : (spS p).distance ≤ 50
  · simp only [hd, decide_true, if_true, cst_beatmap_mod_random_D1, beatmap.slider_path.position_at_refines p _ hp.1 hp.2 h64,
      cst_beatmap_mod_random_F2, float.F32.div, bind_ok, bv2I]
    rfl
  · have h0 : float.F64.from_bits 0#u64 = ok (0 : F64) := by
      unfold float.F64.from_bits; first | rfl | decide | (simp; decide)
    simp only [hd, decide_false, Bool.false_eq_true, if_false, ite_false, bm_vector2_ZERO, h0, bind_ok]
    obtain ⟨y, hl, hy1, hy2⟩ := gen_com_loop p hp h64 (spS p).distance (bv2I Vec2.zero)
    rw [hl]
    rw [forIn_range_iterR]
    have hF : (fun (x : Nat) (r : Nat × Vec2 × F64) =>
        (if (!decide (r.2.2 < (spS p).distance)) = true then (pure (ForInStep.done (r.1, r.2.1, r.2.2)) : Id _)
         else pure (ForInStep.yield (r.1 + 1, r.2.1 + (spS p).positionAt (r.2.2 / (spS p).distance), r.2.2 + 50)))) =
        gen_comF (spS p) (spS p).distance := by
      funext x r; unfold gen_comF; split <;> rfl
    rw [hF]
    simp only [bind_ok, float.F32.from_u64, float.F32.div, bv2I]
    obtain ⟨c, sm⟩ := y
    simp only [bv2S_I] at hy1 hy2
    simp only [Nat.sub_zero]
    generalize iterR (gen_comF (spS p) (spS p).distance) 0 100000000 (0, Vec2.zero, 0) = S at hy1 hy2 ⊢
    obtain ⟨S1, S2, S3⟩ := S
    simp only at hy1 hy2
    subst hy1 hy2
    rfl

theorem beatmap.mod_random.centre_of_mass_refines (h : beatmap.objects.OsuHitObject)
    (hp : ∀ s, h.kind = .Slider s → obPathOk s.path) (h64 : System.Platform.numBits = 64) :
    beatmap.mod_random.centre_of_mass h = ok (bv2I (Mods.Reposition.centreOfMass (abs h))) := by
  obtain ⟨ep, hep, hep2, hep3⟩ := mr2_empty_path
  rw [gen_com_eq]
  unfold beatmap.mod_random.centre_of_mass Mods.Reposition.sliderPath
  rw [ob_kind_abs]
  cases hk : h.kind with
  | Circle => simp [hep, beatmap.mod_random.centre_of_mass_path_refines ep hep3 h64, hep2]
  | Spinner sp => simp [hep, beatmap.mod_random.centre_of_mass_path_refines ep hep3 h64, hep2]
  | Slider sd =>
    have e : (abs sd : SliderData).path = spS sd.path := ob_abs_sliderPath sd.path
    simp only [ob_abs_slider, e]
    exact beatmap.mod_random.centre_of_mass_path_refines _ (hp sd hk) h64
/-! ## combo started -/

/-- `shouldStartNewSection` / `shouldApplyFlowChange`'s "combo started" condition (spec `RandomMod.apply`) -/
def gen_csS (hos : Array OsuHitObject) (i : Nat) : Bool :=
  hos[if i ≥ 2 then i - 2 else 0]!.indexInCurrentCombo > 1 && hos[i - 1]!.newCombo

theorem beatmap.mod_random.combo_started_refines (hos : Slice beatmap.objects.OsuHitObject) (i : Usize)
    (h1 : 1 ≤ i.val) (h2 : i.val < hos.val.length) :
    beatmap.mod_random.combo_started hos i = ok (gen_csS (hos.val.map (abs : _ → OsuHitObject)).toArray i.val) := by
  unfold beatmap.mod_random.combo_started gen_csS
  have hj : (if i.val ≥ 2 then i.val - 2 else 0) < hos.val.length := by split <;> omega
  obtain ⟨j, hj1, hj2⟩ : ∃ j : Usize, (if i ≥ 2#usize then i - 2#usize else ok 0#usize) = ok j ∧
      j.val = if i.val ≥ 2 then i.val - 2 else 0 := by
    by_cases hi : i.val ≥ 2
    · have : i ≥ 2#usize := by scalar_tac
      obtain ⟨z, hz, hzv⟩ : ∃ z, i - 2#usize = ok z ∧ z.val = i.val - 2 := by
        have := Usize.sub_spec (x := i) (y := 2#usize) (by scalar_tac)
        obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec this
        exact ⟨z, hz, by simp at hzv; omega⟩
      exact ⟨z, by simp [this, hz], by simp [hi, hzv]⟩
    · have : ¬ i ≥ 2#usize := by scalar_tac
      exact ⟨0#usize, by simp [this], by simp [hi]⟩
  obtain ⟨k, hk1, hk2⟩ : ∃ k : Usize, i - 1#usize = ok k ∧ k.val = i.val - 1 := by
    have := Usize.sub_spec (x := i) (y := 1#usize) (by scalar_tac)
    obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec this
    exact ⟨z, hz, by simp at hzv; omega⟩
  rw [hj1, bind_ok, slice_index_ok hos j (by omega)]
  simp only [bind_ok]
  rw [← hj2]
  have e1 : ((hos.val.map (abs : _ → OsuHitObject)).toArray)[j.val]! = abs (hos.val[j.val]'(by omega)) := by
    simp [getElem!_pos, hj2 ▸ hj]
  have e2 : ((hos.val.map (abs : _ → OsuHitObject)).toArray)[i.val - 1]! = abs (hos.val[i.val - 1]'(by omega)) := by
    simp [getElem!_pos, show i.val - 1 < hos.val.length by omega]
  rw [e1, e2]
  have hg : ∀ x : I32, (i32S x > (1 : Int32)) ↔ x > 1#i32 := by
    intro x
    have e : (1 : Int32) = i32S 1#i32 := by decide
    rw [gt_iff_lt, e, abs_i32S_lt_iff]; rfl
  by_cases hc : (hos.val[j.val]'(by omega)).index_in_current_combo > 1#i32
  · have hc' := (hg _).mpr hc
    simp only [hc, if_true, hk1, bind_ok, slice_index_ok hos k (by omega), hk2]
    show _ = ok (decide (i32S _ > 1) && _)
    simp [hc']
  · have hc' : ¬ (i32S (hos.val[j.val]'(by omega)).index_in_current_combo > 1) := fun h => hc ((hg _).mp h)
    simp only [hc, if_false]
    show _ = ok (decide (i32S _ > 1) && _)
    simp [hc']
end OsuProofs
