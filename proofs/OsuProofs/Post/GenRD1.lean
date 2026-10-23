/-
Generator mods, part 2 (gen agent): `beatmap::mod_random::generate_position_infos`, `compute_modified_position`.
-/
import OsuProofs.Post.GenBase
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

/-- one step of `Reposition.generatePositionInfos` (state: infos, previous position, previous angle) -/
def gen_gpiG (hos : Array OsuHitObject) (j : Nat) (acc : Array Mods.Reposition.PositionInfo × Vec2 × F32) :
    Array Mods.Reposition.PositionInfo × Vec2 × F32 :=
  let h := hos[j]!
  let rel := h.position - acc.2.1
  let a := Mods.Reposition.atan2f rel.y rel.x
  let info : Mods.Reposition.PositionInfo := { relativeAngle := a - acc.2.2, distanceFromPrevious := rel.length }
  if h.isSlider then
    (acc.1.push { info with rotation := Mods.Reposition.sliderRotation h - a }, h.endPosition,
      Mods.Reposition.sliderRotation h)
  else (acc.1.push info, h.endPosition, a)

theorem gen_gpi_spec (hos : Array OsuHitObject) :
    Mods.Reposition.generatePositionInfos hos =
      (iterR (fun j s => .yield (gen_gpiG hos j s)) 0 hos.size (#[], Mods.Reposition.centre, 0)).1 := by
  unfold Mods.Reposition.generatePositionInfos
  simp only [Id.run]
  rw [forIn_array_iterR]
  refine congrArg (fun F => (iterR F 0 hos.size (#[], Mods.Reposition.centre, 0)).1) ?_
  funext j acc
  unfold gen_gpiG
  by_cases hs : hos[j]!.isSlider <;> simp only [hs, ite_true, ite_false, Bool.false_eq_true] <;> rfl

/-- every slider path of a list of hit objects is in the machine ranges -/
def GenPaths (l : List beatmap.objects.OsuHitObject) : Prop :=
  ∀ h ∈ l, ∀ s, h.kind = .Slider s → obPathOk s.path

theorem gen_abs_vpush {α β} [AbsTo α β] (v : alloc.vec.Vec α) (x : α) (h : v.val.length < Usize.max) :
    (abs (vpush v x h) : Array β) = (abs v : Array β).push (abs x) := by
  simp [abs]

theorem beatmap.mod_random.generate_position_infos_refines (hos : Slice beatmap.objects.OsuHitObject)
    (hp : GenPaths hos.val) (h64 : System.Platform.numBits = 64) :
    ∃ v, beatmap.mod_random.generate_position_infos hos = ok v ∧
      (abs v : Array Mods.Reposition.PositionInfo) =
        Mods.Reposition.generatePositionInfos (abs hos : Array OsuHitObject) := by
  rw [gen_gpi_spec]
  have hS : (abs hos : Array OsuHitObject).size = hos.val.length := by simp [abs]
  obtain ⟨y, hl, hy⟩ := loop_fold_gen'
    (fun x : alloc.vec.Vec beatmap.mod_random.PositionInfo × net.osutk.Vector2 × F32 × Usize =>
      beatmap.mod_random.generate_position_infos_loop.body 0 hos x.1 x.2.1 x.2.2.1 x.2.2.2) (·.2.2.2)
    hos.val.length (by have := hos.property; omega)
    (fun x => x.1.val.length = x.2.2.2.val)
    (fun x => ((abs x.1 : Array Mods.Reposition.PositionInfo), bv2S x.2.1, x.2.2.1))
    (gen_gpiG (abs hos)) (fun y s => (abs y : Array Mods.Reposition.PositionInfo) = s.1)
    (by
      rintro ⟨out, pp, pa, i⟩ hI hlt j1 hj1 hj1v
      simp only at hI hlt hj1 hj1v ⊢
      have hi : i.val < hos.val.length := hlt
      have hpi := hp _ (List.getElem_mem hi)
      have hgi : (abs hos : Array OsuHitObject)[i.val]! = abs (hos.val[i.val]'hi) := by
        simp [abs, getElem!_pos, hi]
      have hpush : out.val.length < Usize.max := by have := hos.property; omega
      simp only [beatmap.mod_random.generate_position_infos_loop.body, slice_lt_len_iff, hi, if_true,
        slice_index_ok _ _ hi, bind_ok, beatmap.vector2.sub_refines, beatmap.mod_random.atan2f_refines,
        float.F32.sub, beatmap.vector2.length_refines, is_slider_ok,
        beatmap.mod_random.slider_rotation_refines _ hpi h64, beatmap.objects.end_position_refines _ hpi h64, hj1]
      by_cases hs : (abs (hos.val[i.val]'hi) : OsuHitObject).isSlider
      · simp only [hs, if_true, bind_ok, vec_push_ok _ _ hpush]
        refine ⟨_, rfl, rfl, ?_, by simp [hI, hj1v]⟩
        simp only [gen_gpiG, hgi, hs, if_true]
        rw [gen_abs_vpush]; rfl
      · simp only [hs, Bool.false_eq_true, if_false, bind_ok, vec_push_ok _ _ hpush]
        refine ⟨_, rfl, rfl, ?_, by simp [hI, hj1v]⟩
        simp only [gen_gpiG, hgi, hs, Bool.false_eq_true, if_false]
        rw [gen_abs_vpush]; rfl)
    (by
      rintro ⟨out, pp, pa, i⟩ hI hge
      simp only at hI hge ⊢
      have : ¬ i < Slice.len hos := by rw [slice_lt_len_iff]; omega
      exact ⟨out, by simp [beatmap.mod_random.generate_position_infos_loop.body, this], rfl⟩)
    (alloc.vec.Vec.with_capacity _ (Slice.len hos), bv2I Mods.Reposition.centre, 0, 0#usize)
    (by simp [alloc.vec.Vec.with_capacity]) (by simp)
  refine ⟨y, ?_, ?_⟩
  · unfold beatmap.mod_random.generate_position_infos beatmap.mod_random.generate_position_infos_loop
    simp only [mr2_CENTRE, cst_beatmap_mod_random_F0, bind_ok]
    exact hl
  · rw [hy, hS]; simp [alloc.vec.Vec.with_capacity, abs]
/-! ## computeModifiedPosition -/
open Mods.Reposition in
/-- `previousAbsoluteAngle` of `computeModifiedPosition` -/
def gen_paaS (hos : Array OsuHitObject) (prev beforePrev : Option Nat) : F32 :=
  match prev with
  | none => 0
  | some p =>
    if hos[p]!.isSlider then sliderRotation hos[p]!
    else
      let earliest := match beforePrev with | some b => hos[b]!.endPosition | none => centre
      let rel := hos[p]!.position - earliest
      atan2f rel.y rel.x

theorem gen_bool_contra {a b : Bool} (h1 : ¬ a = true) (h2 : ¬ ((!b) = true)) (h : a = b) : False := by
  subst h; cases a <;> simp_all
theorem gen_bool_contra2 {a b : Bool} (h1 : a = true) (h2 : (!b) = true) (h : a = b) : False := by
  subst h; cases a <;> simp_all

open Classical in
noncomputable def gen_rotR (h : beatmap.objects.OsuHitObject) (r : F32) : beatmap.objects.OsuHitObject :=
  if hc : ∃ o, beatmap.mod_random.rotate_slider h r = ok o then hc.choose else h

theorem gen_rot_ok (h : beatmap.objects.OsuHitObject) (hg : GenOk (abs h)) (h64 : System.Platform.numBits = 64) (r : F32) :
    beatmap.mod_random.rotate_slider h r = ok (gen_rotR h r) ∧
      (abs (gen_rotR h r) : OsuHitObject) = Mods.Reposition.rotateSlider (abs h) r := by
  obtain ⟨o, ho, hov⟩ := beatmap.mod_random.rotate_slider_refines h r hg h64
  have hc : ∃ o, beatmap.mod_random.rotate_slider h r = ok o := ⟨o, ho⟩
  have e : gen_rotR h r = o := by
    unfold gen_rotR; rw [dif_pos hc]
    have h1 := hc.choose_spec
    have h2 : ok hc.choose = ok o := h1.symm.trans ho
    exact Result.ok_injective h2
  rw [e]; exact ⟨ho, hov.symm⟩

theorem gen_rot_eq (h : beatmap.objects.OsuHitObject) (hg : GenOk (abs h)) (h64 : System.Platform.numBits = 64) (r : F32) :
    beatmap.mod_random.rotate_slider h r = ok (gen_rotR h r) := (gen_rot_ok h hg h64 r).1

def gen_leS (ws : Array Mods.Reposition.Working) (prev : Option Nat) : Vec2 :=
  match prev with | some p => ws[p]!.endPositionModified | none => Mods.Reposition.centre

open Mods.Reposition in
/-- normal form of `Reposition.computeModifiedPosition` -/
def gen_cmpS (hos : Array OsuHitObject) (ws : Array Working) (infos : Array PositionInfo)
    (i : Nat) (prev : Option Nat) (beforePrev : Option Nat) : Array OsuHitObject × Vec2 :=
  let info := infos[i]!
  let absoluteAngle := gen_paaS hos prev beforePrev + info.relativeAngle
  let posRel0 : Vec2 := ⟨info.distanceFromPrevious * F32.cos absoluteAngle, info.distanceFromPrevious * F32.sin absoluteAngle⟩
  let lastEnd := gen_leS ws prev
  let posRel := rotateAwayFromEdge lastEnd posRel0
  let pm := lastEnd + posRel
  let h := hos[i]!
  if h.isSlider then
    let co := centreOfMass h
    let cm := rotateAwayFromEdge pm (rotateVector co (info.rotation + atan2f posRel.y posRel.x - sliderRotation h))
    let rr := atan2f cm.y cm.x - atan2f co.y co.x
    if !Precision.almostEqualsF32 rr 0 then (hos.set! i (rotateSlider h rr), pm) else (hos, pm)
  else (hos, pm)

theorem gen_cmp_spec (hos : Array OsuHitObject) (ws : Array Mods.Reposition.Working)
    (infos : Array Mods.Reposition.PositionInfo) (i : Nat) (prev bp : Option Nat) :
    Mods.Reposition.computeModifiedPosition hos ws infos i prev bp = gen_cmpS hos ws infos i prev bp := by
  unfold Mods.Reposition.computeModifiedPosition gen_cmpS gen_paaS gen_leS
  cases prev <;> cases bp <;> simp only [Id.run] <;>
    by_cases hs : hos[i]!.isSlider <;> simp only [hs, Bool.not_true, Bool.not_false, Bool.false_eq_true, if_false, if_true] <;>
    (try split_ifs) <;> rfl

theorem gen_abs_get {α β} [AbsTo α β] [Inhabited β] (v : alloc.vec.Vec α) (k : Nat) (h : k < v.val.length) :
    (abs v : Array β)[k]! = abs (v.val[k]'h) := by
  simp [abs, getElem!_pos, h]
theorem gen_abs_sget {α β} [AbsTo α β] [Inhabited β] (v : Slice α) (k : Nat) (h : k < v.val.length) :
    (abs v : Array β)[k]! = abs (v.val[k]'h) := by
  simp [abs, getElem!_pos, h]
theorem gen_abs_set {α β} [AbsTo α β] (v : alloc.vec.Vec α) (i : Usize) (x : α) :
    (abs (alloc.vec.Vec.set v i x) : Array β) = (abs v : Array β).set! i.val (abs x) := by
  simp [abs, List.map_set, Array.set!_eq_setIfInBounds]

def GenOkL (l : List beatmap.objects.OsuHitObject) : Prop := ∀ h ∈ l, GenOk (abs h)

theorem gen_okl_get (l : List beatmap.objects.OsuHitObject) (hg : GenOkL l) (k : Nat) (hk : k < l.length) :
    GenOk (abs (l[k]'hk)) := hg _ (List.getElem_mem hk)
theorem gen_okl_paths (l : List beatmap.objects.OsuHitObject) (hg : GenOkL l) (k : Nat) (hk : k < l.length) :
    ∀ s, (l[k]'hk).kind = .Slider s → obPathOk s.path := gen_paths_ok _ (gen_okl_get l hg k hk)
theorem gen_okl_set (l : List beatmap.objects.OsuHitObject) (hg : GenOkL l) (k : Nat) (x : beatmap.objects.OsuHitObject)
    (hx : GenOk (abs x)) : GenOkL (l.set k x) := by
  intro h hm
  rcases List.mem_or_eq_of_mem_set hm with h1 | h1
  · exact hg _ h1
  · subst h1; exact hx

theorem beatmap.mod_random.compute_modified_position_refines (hos : alloc.vec.Vec beatmap.objects.OsuHitObject)
    (ws : Slice beatmap.mod_random.Working) (infos : Slice beatmap.mod_random.PositionInfo) (i : Usize)
    (prev bp : Option Usize) (hi : i.val < hos.val.length) (hii : i.val < infos.val.length)
    (hp : ∀ p, prev = some p → p.val < hos.val.length ∧ p.val < ws.val.length)
    (hb : ∀ b, bp = some b → b.val < hos.val.length)
    (hg : GenOkL hos.val) (h64 : System.Platform.numBits = 64) :
    ∃ pm hos', beatmap.mod_random.compute_modified_position hos ws infos i prev bp = ok (pm, hos') ∧
      Mods.Reposition.computeModifiedPosition (abs hos) (abs ws) (abs infos) i.val (prev.map (·.val)) (bp.map (·.val)) =
        (abs hos', bv2S pm) ∧ GenOkL hos'.val ∧ hos'.val.length = hos.val.length := by
  rw [gen_cmp_spec]
  unfold beatmap.mod_random.compute_modified_position gen_cmpS
  simp only [cst_beatmap_mod_random_F0, bind_ok]
  have hgi := gen_okl_get _ hg _ hi
  have hpi := gen_okl_paths _ hg _ hi
  have tail : ∀ (M : Result F32) (L : Result net.osutk.Vector2) (paa : F32) (le : net.osutk.Vector2), M = ok paa →
      L = ok le → gen_paaS (abs hos) (prev.map (·.val)) (bp.map (·.val)) = paa →
      gen_leS (abs ws) (prev.map (·.val)) = bv2S le →
      ∃ pm hos', (do
          let previous_absolute_angle1 ← M
          let info ← Slice.index_usize infos i
          let absolute_angle ← float.F32.add previous_absolute_angle1 info.relative_angle
          let f ← float.F32.cos absolute_angle
          let f1 ← float.F32.mul info.distance_from_previous f
          let f2 ← float.F32.sin absolute_angle
          let f3 ← float.F32.mul info.distance_from_previous f2
          let last_end ← L
          let f4 ← beatmap.mod_random.F_HALF
          let pos_rel ← beatmap.mod_random.rotate_away_from_edge last_end { x := f1, y := f3 } f4
          let position_modified ← beatmap.vector2.add last_end pos_rel
          let oho ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice beatmap.objects.OsuHitObject) hos i
          let b ← beatmap.objects.is_slider oho
          if b then
            let absolute_angle2 ← beatmap.mod_random.atan2f pos_rel.y pos_rel.x
            let com_original ← beatmap.mod_random.centre_of_mass oho
            let f5 ← float.F32.add info.rotation absolute_angle2
            let f6 ← beatmap.mod_random.slider_rotation oho
            let f7 ← float.F32.sub f5 f6
            let com_modified0 ← beatmap.mod_random.rotate_vector com_original f7
            let com_modified ← beatmap.mod_random.rotate_away_from_edge position_modified com_modified0 f4
            let f8 ← beatmap.mod_random.atan2f com_modified.y com_modified.x
            let f9 ← beatmap.mod_random.atan2f com_original.y com_original.x
            let relative_rotation ← float.F32.sub f8 f9
            let b1 ← beatmap.vector2.almost_equals_f32 relative_rotation 0
            if b1 then ok (position_modified, hos)
            else
              let (oho1, index_mut_back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
                beatmap.objects.OsuHitObject) hos i
              let oho2 ← beatmap.mod_random.rotate_slider oho1 relative_rotation
              let hos1 := index_mut_back oho2
              ok (position_modified, hos1)
          else ok (position_modified, hos)) = ok (pm, hos') ∧
        gen_cmpS (abs hos) (abs ws) (abs infos) i.val (prev.map (·.val)) (bp.map (·.val)) = (abs hos', bv2S pm) ∧
        GenOkL hos'.val ∧ hos'.val.length = hos.val.length := by
    intro M L paa le hM hL hpaa hle
    subst hM hL
    unfold gen_cmpS
    simp only [hpaa, hle]
    simp only [bind_ok, slice_index_ok _ _ hii, float.F32.add, float.F32.cos, float.F32.mul, float.F32.sin,
      cst_beatmap_mod_random_F_HALF, beatmap.mod_random.rotate_away_from_edge_refines, beatmap.vector2.add_refines,
      vec_index_eq _ _ hi, is_slider_ok, gen_abs_sget infos i.val hii, gen_abs_get hos i.val hi]
    by_cases hs : (abs (hos.val[i.val]'hi) : OsuHitObject).isSlider
    · simp only [hs, if_true, beatmap.mod_random.atan2f_refines, beatmap.mod_random.centre_of_mass_refines _ hpi h64,
        beatmap.mod_random.slider_rotation_refines _ hpi h64, bind_ok, float.F32.add, float.F32.sub,
        beatmap.mod_random.rotate_vector_refines, beatmap.mod_random.rotate_away_from_edge_refines,
        beatmap.vector2.almost_equals_f32_refines]
      split
      · next ha =>
        split
        · next hb =>
          exact (gen_bool_contra2 ha hb rfl).elim
        · exact ⟨_, _, rfl, rfl, hg, rfl⟩
      · next ha =>
        rw [vec_index_mut_eq _ _ hi]
        simp only [bind_ok]
        simp only [uncurry_apply_pair]
        simp only [gen_rot_eq _ hgi h64, bind_ok]
        split
        · next hb =>
          refine ⟨_, _, rfl, ?_, ?_, by simp [vec_set_val']⟩
          · rw [gen_abs_set, (gen_rot_ok _ hgi h64 _).2]; rfl
          · rw [vec_set_val']; exact gen_okl_set _ hg _ _ (by rw [(gen_rot_ok _ hgi h64 _).2]; exact gen_ok_rotate _ _ hgi)
        · next hb => exact (gen_bool_contra ha hb rfl).elim
    · simp only [hs, Bool.false_eq_true, if_false]
      exact ⟨_, _, rfl, rfl, hg, rfl⟩
  refine tail _ _ (gen_paaS (abs hos) (prev.map (·.val)) (bp.map (·.val))) (bv2I (gen_leS (abs ws) (prev.map (·.val))))
    ?_ ?_ rfl rfl
  · rcases prev with _ | p
    · rfl
    · have hp1 := (hp p rfl).1
      have hpp := gen_okl_paths _ hg _ hp1
      simp only [vec_index_eq _ _ hp1, bind_ok, is_slider_ok, gen_paaS, Option.map_some, gen_abs_get hos p.val hp1]
      by_cases hsp : (abs (hos.val[p.val]'hp1) : OsuHitObject).isSlider
      · simp only [hsp, if_true, beatmap.mod_random.slider_rotation_refines _ hpp h64]
      · simp only [hsp, Bool.false_eq_true, if_false]
        rcases bp with _ | b
        · simp only [mr2_CENTRE, bind_ok, beatmap.vector2.sub_refines, beatmap.mod_random.atan2f_refines]; rfl
        · have hb1 := hb b rfl
          simp only [vec_index_eq _ _ hb1, bind_ok, beatmap.objects.end_position_refines _ (gen_okl_paths _ hg _ hb1) h64,
            beatmap.vector2.sub_refines, beatmap.mod_random.atan2f_refines, Option.map_some, gen_abs_get hos b.val hb1]
          rfl
  · rcases prev with _ | p
    · exact mr2_CENTRE
    · have hp2 := (hp p rfl).2
      simp only [slice_index_ok _ _ hp2, bind_ok, gen_leS, Option.map_some, gen_abs_sget ws p.val hp2]
      rfl
end OsuProofs
