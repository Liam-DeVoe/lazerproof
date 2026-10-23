/-
`beatmap::playable` (Rust) refines `OsuModel.Beatmap` (`Playable.lean`).
-/
import OsuProofs.Post.Stacking
import OsuProofs.Beatmap.HitObjectParser4
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

/-- the nested-object update of `updateNestedPositions` (Rust side) -/
def unpG (s : beatmap.objects.SliderData) (pos endp : net.osutk.Vector2) (no : beatmap.objects.NestedObject) :
    beatmap.objects.NestedObject :=
  match no.kind with
  | .Head => { no with position := pos }
  | .Tick => { no with position := bv2I (Vec2.add (bv2S pos) (SliderPath.positionAt (spS s.path) no.path_progress)) }
  | .Repeat => { no with position := bv2I (Vec2.add (bv2S pos) (SliderPath.positionAt (spS s.path) no.path_progress)) }
  | .Tail => { no with position := endp }
  | _ => no

theorem vec_set_self {α} (v : alloc.vec.Vec α) (i : Usize) (h : i.val < v.val.length) :
    alloc.vec.Vec.set v i (v.val[i.val]'h) = v := by
  unfold alloc.vec.Vec.set; simp

theorem unp_loop (s : beatmap.objects.SliderData) (pos endp : net.osutk.Vector2) (hp : obPathOk s.path)
    (h64 : System.Platform.numBits = 64) :
    ∀ (v : alloc.vec.Vec beatmap.objects.NestedObject) (i : Usize), i.val ≤ v.val.length → ∃ w,
      beatmap.playable.update_nested_positions_loop s v pos endp i = ok (s, w) ∧
      w.val = v.val.take i.val ++ (v.val.drop i.val).map (unpG s pos endp) := by
  intro v i
  induction hk : v.val.length - i.val using Nat.strong_induction_on generalizing v i with
  | _ k ih =>
    intro hle
    unfold beatmap.playable.update_nested_positions_loop
    rw [loop_unfold]
    by_cases hlt : i.val < v.val.length
    · have hl : i < alloc.vec.Vec.len v := by rw [vec_lt_len_iff]; exact hlt
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := v.property; omega)
      let v' := alloc.vec.Vec.set v i (unpG s pos endp (v.val[i.val]'hlt))
      have hb : beatmap.playable.update_nested_positions_loop.body pos endp s v i = ok (.cont (s, v', i1)) := by
        simp only [beatmap.playable.update_nested_positions_loop.body, hl, if_true, vec_index_eq _ _ hlt, bind_ok]
        unfold v' unpG
        cases hkd : (v.val[i.val]'hlt).kind <;>
          simp [hkd, vec_index_mut_eq _ _ hlt, hi1, beatmap.slider_path.position_at_refines s.path _ hp.1 hp.2 h64,
            beatmap.vector2.add_refines, vec_set_self]
      have hlen : v'.val.length = v.val.length := by simp [v', vec_set_val']
      obtain ⟨w, hw1, hw2⟩ := ih (v'.val.length - i1.val) (by omega) v' i1 rfl (by omega)
      refine ⟨w, ?_, ?_⟩
      · dsimp only; rw [hb]; simp only [bind_ok]
        unfold beatmap.playable.update_nested_positions_loop at hw1; exact hw1
      · rw [hw2, hi1v]; simp only [v', vec_set_val']
        exact take_set_drop _ _ hlt _
    · have hl : ¬ i < alloc.vec.Vec.len v := by rw [vec_lt_len_iff]; exact hlt
      refine ⟨v, by dsimp only; simp [beatmap.playable.update_nested_positions_loop.body, hl], ?_⟩
      simp [List.take_of_length_le (show v.val.length ≤ i.val by omega),
        List.drop_eq_nil_of_le (show v.val.length ≤ i.val by omega)]

theorem beatmap.playable.update_nested_positions_refines (h : beatmap.objects.OsuHitObject)
    (hp : ∀ s, h.kind = .Slider s → obPathOk s.path) (h64 : System.Platform.numBits = 64) :
    ∃ r, beatmap.playable.update_nested_positions h = ok r ∧ updateNestedPositions (abs h) = abs r := by
  have hep := beatmap.objects.end_position_refines h hp h64
  unfold beatmap.playable.update_nested_positions updateNestedPositions
  rw [hep]; simp only [bind_ok]
  cases hk : h.kind with
  | Circle =>
    refine ⟨h, rfl, ?_⟩
    have : (abs h : OsuHitObject).kind = .circle := by show (abs h.kind : ObjectKind) = _; rw [hk]; rfl
    simp only [this]
  | Spinner sp =>
    refine ⟨h, rfl, ?_⟩
    have : (abs h : OsuHitObject).kind = .spinner (abs sp) := by show (abs h.kind : ObjectKind) = _; rw [hk]; rfl
    simp only [this]
  | Slider sd =>
    obtain ⟨w, hw, hwv⟩ := unp_loop sd h.position (bv2I (OsuHitObject.endPosition (abs h))) (hp sd hk) h64 h.nested
      0#usize (by simp)
    refine ⟨{ h with kind := .Slider sd, nested := w }, by simp only [hw, bind_ok]; rfl, ?_⟩
    have hks : (abs h : OsuHitObject).kind = .slider (abs sd) := by show (abs h.kind : ObjectKind) = _; rw [hk]; rfl
    simp only [hks]
    simp only [List.take_zero, List.drop_zero, List.nil_append, show (0#usize : Usize).val = 0 from rfl] at hwv
    have hkind : (abs ({ h with kind := .Slider sd, nested := w } : beatmap.objects.OsuHitObject) : OsuHitObject).kind =
        (abs h : OsuHitObject).kind := by
      show (abs (beatmap.objects.ObjectKind.Slider sd) : ObjectKind) = (abs h.kind : ObjectKind); rw [hk]
    have hnest : (abs ({ h with kind := .Slider sd, nested := w } : beatmap.objects.OsuHitObject) : OsuHitObject).nested =
        (abs h : OsuHitObject).nested.map (fun n => match n.kind with
          | .head => { n with position := (abs h : OsuHitObject).position }
          | .tail => { n with position := (abs h : OsuHitObject).endPosition }
          | .repeat | .tick => { n with position := (abs h : OsuHitObject).position + (abs sd : SliderData).path.positionAt n.pathProgress }
          | _ => n) := by
      show ((w.val.map abs).toArray : Array NestedObject) = ((h.nested.val.map abs).toArray).map _
      rw [hwv]
      apply Array.ext'
      simp only [List.map_map, Array.toList_map, List.toList_toArray]
      apply List.map_congr_left
      intro no _
      simp only [Function.comp_apply, unpG]
      rw [show (abs sd : SliderData).path = abs sd.path from rfl, ob_abs_sliderPath]
      cases hn : no.kind <;> simp [hn, abs] <;> rfl
    have habs : (abs ({ h with kind := .Slider sd, nested := w } : beatmap.objects.OsuHitObject) : OsuHitObject) =
        { (abs h : OsuHitObject) with
          kind := (abs ({ h with kind := .Slider sd, nested := w } : beatmap.objects.OsuHitObject) : OsuHitObject).kind,
          nested := (abs ({ h with kind := .Slider sd, nested := w } : beatmap.objects.OsuHitObject) : OsuHitObject).nested } :=
      rfl
    rw [habs, hkind, hks, hnest]
    rfl

@[step] theorem beatmap.playable.update_nested_positions_step (h : beatmap.objects.OsuHitObject)
    (hp : ∀ s, h.kind = .Slider s → obPathOk s.path) (h64 : System.Platform.numBits = 64) :
    beatmap.playable.update_nested_positions h ⦃ r => updateNestedPositions (abs h) = abs r ⦄ :=
  spec_of_ex (beatmap.playable.update_nested_positions_refines h hp h64)

theorem cpi_abs (cpi : beatmap.control_points.ControlPointInfo) : (abs cpi : ControlPointInfo) = cpS cpi := by
  simp [abs, cpS, tpS, dpS, epS]

theorem pcps_abs (cps : alloc.vec.Vec beatmap.types.PathControlPoint) :
    (abs cps : Array PathControlPoint) = pcpsS cps.val := by
  simp [abs, pcpsS, pcpS]
  intro a _
  cases a.ptype with
  | none => rfl
  | some t => cases t <;> rfl

theorem beatmap.playable.convert_hit_object_refines (fv : I32) (cpi : beatmap.control_points.ControlPointInfo)
    (o : beatmap.types.ConvertHitObject) (hdp : cpi.difficulty_points.val.length < 2^31)
    (h64 : System.Platform.numBits = 64)
    (hsl : ∀ cps d r, o.kind = .Slider cps d r → cps.val.length < 2^32 ∧
      (SliderPath.calculatePath { controlPoints := pcpsS cps.val, expectedDistance := d, optimiseCatmull := true }).1.size < 2^62) :
    ∃ r, beatmap.playable.convert_hit_object fv cpi o = ok r ∧
      convertHitObject (abs fv) (abs cpi) (abs o) = abs r := by
  rw [cpi_abs]
  unfold beatmap.playable.convert_hit_object convertHitObject
  cases hk : o.kind with
  | Circle =>
    obtain ⟨h, hh, hhv⟩ := beatmap.objects.object_default_refines .Circle o.start_time o.position
    refine ⟨{ h with new_combo := o.new_combo, combo_offset := o.combo_offset }, by simp [hh], ?_⟩
    have hka : (abs o : ConvertHitObject).kind = .circle := by show (abs o.kind : ConvertKind) = _; rw [hk]; rfl
    simp only [hka]
    rw [show (abs ({ h with new_combo := o.new_combo, combo_offset := o.combo_offset } : beatmap.objects.OsuHitObject) :
        OsuHitObject) = { (abs h : OsuHitObject) with newCombo := o.new_combo, comboOffset := i32S o.combo_offset } from rfl,
      ← hhv]
    rfl
  | Slider cps d rc =>
    obtain ⟨hn, hsz⟩ := hsl cps d rc hk
    obtain ⟨p, hp, hpv⟩ := beatmap.slider_path.of_control_points_refines cps d true h64 hn hsz
    have hd1 : beatmap.playable.D1 = ok (1 : F64) := by
      unfold beatmap.playable.D1; simp [float.F64.from_bits] <;> decide
    have hf1 : float.F32.from_bits 1065353216#u32 = ok (1 : F32) := by simp [float.F32.from_bits] <;> decide
    have hone : (Float32.ofBits 1065353216 : F32) = 1 := by decide
    have hz : float.F64.from_bits 0#u64 = ok (0 : F64) := by simp [float.F64.from_bits] <;> decide
    let tdm : F64 := if i32S fv < 8 then F32.toF64 1 / ((cpS cpi).difficultyPointAt o.start_time).sliderVelocity else 1
    have htdm : (if fv < 8#i32 then do
          let f ← float.F32.from_bits 1065353216#u32
          let f1 ← float.F32.to_f64 f
          let dp ← beatmap.control_points.difficulty_point_at cpi o.start_time
          float.F64.div f1 dp.slider_velocity
        else beatmap.playable.D1) = ok tdm := by
      by_cases hfv : fv < 8#i32
      · have : i32S fv < 8 := by
          rw [show (8 : Int32) = i32S 8#i32 from rfl, abs_i32S_lt_iff]; exact hfv
        simp [hfv, hf1, float.F32.to_f64, beatmap.control_points.difficulty_point_at_refines cpi o.start_time hdp,
          float.F64.div, tdm, this, dpI, hone]
      · have : ¬ i32S fv < 8 := by
          rw [show (8 : Int32) = i32S 8#i32 from rfl, abs_i32S_lt_iff]; exact hfv
        simp [hfv, hd1, tdm, this]
    let sd : beatmap.objects.SliderData :=
      ⟨p, rc, 0, 0, tdm, clampSV o.slider_velocity_multiplier, o.generate_ticks, false, false⟩
    obtain ⟨h, hh, hhv⟩ := beatmap.objects.object_default_refines (.Slider sd) o.start_time o.position
    refine ⟨{ h with new_combo := o.new_combo, combo_offset := o.combo_offset }, ?_, ?_⟩
    · simp only [hop_pcp_clone, hp, bind_ok, htdm, hz, beatmap.control_points.clamp_sv_refines]
      simp only [sd] at hh
      simp [hh]
    · have hka : (abs o : ConvertHitObject).kind = .slider (abs cps) (abs d) (abs rc) := by
        show (abs o.kind : ConvertKind) = _; rw [hk]; rfl
      simp only [hka]
      rw [show (abs ({ h with new_combo := o.new_combo, combo_offset := o.combo_offset } : beatmap.objects.OsuHitObject) :
          OsuHitObject) = { (abs h : OsuHitObject) with newCombo := o.new_combo, comboOffset := i32S o.combo_offset } from rfl,
        ← hhv]
      have hpa : (abs p : SliderPath) = SliderPath.ofControlPoints (pcpsS cps.val) d true := by
        rw [ob_abs_sliderPath, hpv]
      rw [pcps_abs]
      have hsd : (abs sd : SliderData) =
          ({ path := abs p, repeatCount := i32S rc, tickDistanceMultiplier := tdm,
             sliderVelocityMultiplier := clampSV o.slider_velocity_multiplier,
             generateTicks := o.generate_ticks } : SliderData) := rfl
      have hks : (abs (beatmap.objects.ObjectKind.Slider sd) : ObjectKind) = .slider (abs sd) := rfl
      have hd : (abs d : Option F64) = d := by cases d <;> rfl
      rw [hks, hsd, hpa, hd]
      rfl
  | Spinner du =>
    obtain ⟨h, hh, hhv⟩ := beatmap.objects.object_default_refines
      (.Spinner { duration := o.start_time + du - o.start_time, spins_required := 1#i32, maximum_bonus_spins := 1#i32 })
      o.start_time o.position
    refine ⟨{ h with new_combo := o.new_combo, combo_offset := o.combo_offset }, by simp [float.F64.add, float.F64.sub, hh], ?_⟩
    have hka : (abs o : ConvertHitObject).kind = .spinner du := by show (abs o.kind : ConvertKind) = _; rw [hk]; rfl
    simp only [hka]
    rw [show (abs ({ h with new_combo := o.new_combo, combo_offset := o.combo_offset } : beatmap.objects.OsuHitObject) :
        OsuHitObject) = { (abs h : OsuHitObject) with newCombo := o.new_combo, comboOffset := i32S o.combo_offset } from rfl,
      ← hhv]
    rfl
  | Hold du =>
    obtain ⟨h, hh, hhv⟩ := beatmap.objects.object_default_refines
      (.Spinner { duration := o.start_time + du - o.start_time, spins_required := 1#i32, maximum_bonus_spins := 1#i32 })
      o.start_time o.position
    refine ⟨{ h with new_combo := o.new_combo, combo_offset := o.combo_offset }, by simp [float.F64.add, float.F64.sub, hh], ?_⟩
    have hka : (abs o : ConvertHitObject).kind = .hold du := by show (abs o.kind : ConvertKind) = _; rw [hk]; rfl
    simp only [hka]
    rw [show (abs ({ h with new_combo := o.new_combo, combo_offset := o.combo_offset } : beatmap.objects.OsuHitObject) :
        OsuHitObject) = { (abs h : OsuHitObject) with newCombo := o.new_combo, comboOffset := i32S o.combo_offset } from rfl,
      ← hhv]
    rfl

@[step] theorem beatmap.playable.convert_hit_object_step (fv : I32) (cpi : beatmap.control_points.ControlPointInfo)
    (o : beatmap.types.ConvertHitObject) (hdp : cpi.difficulty_points.val.length < 2^31)
    (h64 : System.Platform.numBits = 64)
    (hsl : ∀ cps d r, o.kind = .Slider cps d r → cps.val.length < 2^32 ∧
      (SliderPath.calculatePath { controlPoints := pcpsS cps.val, expectedDistance := d, optimiseCatmull := true }).1.size < 2^62) :
    beatmap.playable.convert_hit_object fv cpi o ⦃ r => convertHitObject (abs fv) (abs cpi) (abs o) = abs r ⦄ :=
  spec_of_ex (beatmap.playable.convert_hit_object_refines fv cpi o hdp h64 hsl)


theorem vec_clone_id {α} (cl : core.clone.Clone α) (hcl : ∀ x, cl.clone x = ok x) (v : alloc.vec.Vec α) :
    alloc.vec.CloneVec.clone cl v = ok v := by
  obtain ⟨s, hs, hsv⟩ := eq_ok_of_spec (Slice.clone_spec (clone := cl.clone) (s := v.slice) (by intro x _; exact hcl x))
  simp only [alloc.vec.CloneVec.clone, hs, bind_ok, ← hsv]
  rw [bind_tc_ok]

theorem pl_opt_clone (o : Option F64) :
    core.option.Option.Insts.CoreCloneClone.clone float.F64.Insts.CoreCloneClone o = ok o := by
  cases o <;> simp [core.option.Option.Insts.CoreCloneClone.clone, float.F64.Insts.CoreCloneClone.clone]

theorem pl_hw_clone (o : Option beatmap.objects.HitWindows) :
    core.option.Option.Insts.CoreCloneClone.clone beatmap.objects.HitWindows.Insts.CoreCloneClone o = ok o := by
  cases o <;> simp [core.option.Option.Insts.CoreCloneClone.clone, beatmap.objects.HitWindows.Insts.CoreCloneClone.clone]

theorem pl_path_clone (p : beatmap.slider_path.SliderPath) :
    beatmap.slider_path.SliderPath.Insts.CoreCloneClone.clone p = ok p := by
  simp [beatmap.slider_path.SliderPath.Insts.CoreCloneClone.clone,
    beatmap.slider_path.SliderPathSpec.Insts.CoreCloneClone.clone, hop_pcp_clone, pl_opt_clone, lift,
    vec_clone_id net.osutk.Vector2.Insts.CoreCloneClone (fun _ => rfl),
    vec_clone_id float.F64.Insts.CoreCloneClone (fun _ => rfl), float.F64.Insts.CoreCloneClone.clone,
    core.clone.impls.CloneBool.clone]

theorem pl_kind_clone (k : beatmap.objects.ObjectKind) :
    beatmap.objects.ObjectKind.Insts.CoreCloneClone.clone k = ok k := by
  cases k <;> simp [beatmap.objects.ObjectKind.Insts.CoreCloneClone.clone,
    beatmap.objects.SliderData.Insts.CoreCloneClone.clone, beatmap.objects.SpinnerData.Insts.CoreCloneClone.clone,
    pl_path_clone, lift, float.F64.Insts.CoreCloneClone.clone, core.clone.impls.CloneBool.clone,
    core.clone.impls.CloneI32.clone]

theorem pl_ho_clone (h : beatmap.objects.OsuHitObject) :
    beatmap.objects.OsuHitObject.Insts.CoreCloneClone.clone h = ok h := by
  simp [beatmap.objects.OsuHitObject.Insts.CoreCloneClone.clone, pl_kind_clone, lift,
    float.F64.Insts.CoreCloneClone.clone, float.F32.Insts.CoreCloneClone.clone,
    net.osutk.Vector2.Insts.CoreCloneClone.clone, core.clone.impls.CloneBool.clone, core.clone.impls.CloneI32.clone,
    vec_clone_id beatmap.objects.NestedObject.Insts.CoreCloneClone (fun _ => rfl),
    pl_hw_clone]



theorem ssb_merge_map {α β : Type} (f : α → β) (key : β → F64) :
    ∀ (fuel : Nat) (xs ys : List α), stableSortBy.merge key (xs.map f) (ys.map f) fuel =
      (stableSortBy.merge (key ∘ f) xs ys fuel).map f := by
  intro fuel
  induction fuel with
  | zero => intro xs ys; simp [stableSortBy.merge]
  | succ k ih =>
    intro xs ys
    cases xs with
    | nil => simp [stableSortBy.merge]
    | cons x xs' =>
      cases ys with
      | nil => simp [stableSortBy.merge]
      | cons y ys' =>
        simp only [List.map_cons, stableSortBy.merge, Function.comp_apply]
        split
        · rw [← List.map_cons, ih]; rfl
        · rw [← List.map_cons, ih]; rfl

theorem ssb_sort_map {α β : Type} (f : α → β) (key : β → F64) :
    ∀ (fuel : Nat) (xs : List α), stableSortBy.sort key (xs.map f) fuel = (stableSortBy.sort (key ∘ f) xs fuel).map f := by
  intro fuel
  induction fuel with
  | zero => intro xs; simp [stableSortBy.sort]
  | succ k ih =>
    intro xs
    simp only [stableSortBy.sort, List.length_map]
    split
    · rfl
    · rw [← List.map_take, ← List.map_drop, ih, ih, ssb_merge_map]

theorem stableSortBy_map {α β : Type} (f : α → β) (key : β → F64) (a : Array α) :
    stableSortBy key (a.map f) = (stableSortBy (key ∘ f) a).map f := by
  unfold stableSortBy
  simp only [Array.toList_map, Array.size_map, ssb_sort_map]
  apply Array.ext'; simp



theorem foldl_diff_const {β : Type} (f : ControlPointInfo → β → ControlPointInfo)
    (hf : ∀ c b, (f c b).difficultyPoints = c.difficultyPoints) :
    ∀ (l : List β) (c : ControlPointInfo), (l.foldl f c).difficultyPoints = c.difficultyPoints := by
  intro l; induction l with
  | nil => intro c; rfl
  | cons b t ih => intro c; simp only [List.foldl_cons]; rw [ih, hf]

theorem foldl_addDiff_size :
    ∀ (l : List DifficultyPoint) (c : ControlPointInfo),
      (l.foldl ControlPointInfo.addDifficulty c).difficultyPoints.size ≤ c.difficultyPoints.size + l.length := by
  intro l; induction l with
  | nil => intro c; simp
  | cons b t ih =>
    intro c; simp only [List.foldl_cons, List.length_cons]
    have h1 := ih (ControlPointInfo.addDifficulty c b)
    have h2 : (ControlPointInfo.addDifficulty c b).difficultyPoints.size ≤ c.difficultyPoints.size + 1 := by
      unfold ControlPointInfo.addDifficulty; split
      · omega
      · exact insertSorted_size_le _ _ _ _
    omega

theorem deepClone_diff_size (c : ControlPointInfo) :
    c.deepClone.difficultyPoints.size ≤ c.difficultyPoints.size := by
  unfold ControlPointInfo.deepClone
  simp only
  rw [← Array.foldl_toList, foldl_diff_const ControlPointInfo.addEffect (by
    intro c b; unfold ControlPointInfo.addEffect; split <;> rfl)]
  rw [← Array.foldl_toList]
  have := foldl_addDiff_size c.difficultyPoints.toList (c.timingPoints.foldl ControlPointInfo.addTiming {})
  rw [← Array.foldl_toList, foldl_diff_const ControlPointInfo.addTiming (by intro c b; rfl)] at this
  simpa using this



def choSlOk (o : beatmap.types.ConvertHitObject) : Prop :=
  ∀ cps d r, o.kind = .Slider cps d r → cps.val.length < 2^32 ∧
    (SliderPath.calculatePath { controlPoints := pcpsS cps.val, expectedDistance := d, optimiseCatmull := true }).1.size < 2^62

theorem cb_loop (fv : I32) (v : alloc.vec.Vec beatmap.types.ConvertHitObject) (cpi : beatmap.control_points.ControlPointInfo)
    (hdp : cpi.difficulty_points.val.length < 2^31) (h64 : System.Platform.numBits = 64)
    (hall : ∀ o ∈ v.val, choSlOk o) :
    ∃ r, beatmap.playable.convert_beatmap_loop fv v cpi
        (alloc.vec.Vec.with_capacity _ (alloc.vec.Vec.len v)) 0#usize = ok r ∧
      r.val.map (abs : _ → OsuHitObject) = (v.val.map (abs : _ → ConvertHitObject)).map (convertHitObject (abs fv) (abs cpi)) ∧
      r.val.length = v.val.length := by
  have hmax : v.val.length ≤ Usize.max := by have := v.property; omega
  obtain ⟨y, hl, hy⟩ := loop_fold_gen' (fun x => beatmap.playable.convert_beatmap_loop.body fv v cpi x.1 x.2) (·.2)
    v.val.length hmax (fun x => x.1.val.length = x.2.val ∧ x.2.val ≤ v.val.length) (fun x => x.1.val.map (abs : _ → OsuHitObject))
    (fun k L => L ++ [convertHitObject (abs fv) (abs cpi) ((v.val.map (abs : _ → ConvertHitObject))[k]!)])
    (fun y L => y.val.map abs = L ∧ y.val.length = v.val.length)
    (by
      intro t hI hlt j1 hj1 hj1v
      have hlt' : t.2.val < v.val.length := hlt
      have hc : t.2 < alloc.vec.Vec.len v := by rw [vec_lt_len_iff]; exact hlt'
      obtain ⟨r, hr, hrv⟩ := beatmap.playable.convert_hit_object_refines fv cpi (v.val[t.2.val]'hlt') hdp h64
        (hall _ (List.getElem_mem _))
      have hpl : t.1.val.length < Usize.max := by have := hI.1; omega
      refine ⟨(vpush t.1 r hpl, j1), ?_, rfl, ?_, ?_⟩
      · simp [beatmap.playable.convert_beatmap_loop.body, hc, vec_index_eq _ _ hlt', hr, vec_push_ok _ _ hpl, hj1]
      · simp only [vpush_val, List.map_append, List.map_cons, List.map_nil]
        congr 2
        rw [getElem!_pos _ _ (by simpa using hlt')]; simp only [List.getElem_map]; exact hrv.symm
      · exact ⟨by simp only [vpush_val, List.length_append, List.length_singleton, hI.1, hj1v], by simp only [hj1v]; omega⟩)
    (by
      intro t hI hge
      have hc : ¬ t.2 < alloc.vec.Vec.len v := by rw [vec_lt_len_iff]; omega
      refine ⟨t.1, by simp [beatmap.playable.convert_beatmap_loop.body, hc], rfl, by have := hI.1; have := hI.2; omega⟩)
    (alloc.vec.Vec.with_capacity _ (alloc.vec.Vec.len v), 0#usize)
    ⟨by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new], by simp⟩ (by simp)
  refine ⟨y, by unfold beatmap.playable.convert_beatmap_loop; exact hl, ?_, hy.2⟩
  rw [hy.1]
  have := map_iterR (v.val.map (abs : _ → ConvertHitObject)) (convertHitObject (abs fv) (abs cpi))
  simp only [List.length_map] at this
  rw [this]; rfl



theorem beatmap.playable.convert_beatmap_refines (d : beatmap.types.DecodedBeatmap)
    (h1 : d.control_points.timing_points.val.length < 2^31) (h2 : d.control_points.difficulty_points.val.length < 2^31)
    (h3 : d.control_points.effect_points.val.length < 2^31) (hN : d.hit_objects.val.length < 2^31)
    (h64 : System.Platform.numBits = 64) (hall : ∀ o ∈ d.hit_objects.val, choSlOk o) :
    ∃ r, beatmap.playable.convert_beatmap d = ok r ∧ convertBeatmap (abs d) = abs r := by
  obtain ⟨cpi, hcpi, hcpiv⟩ := beatmap.control_points.deep_clone_refines d.control_points h1 h2 h3
  have hdp : cpi.difficulty_points.val.length < 2^31 := by
    have := deepClone_diff_size (cpS d.control_points)
    rw [← hcpiv] at this
    simp [cpS] at this; omega
  obtain ⟨hos1, hl1, hv1, hlen1⟩ := cb_loop d.format_version d.hit_objects cpi hdp h64 hall
  obtain ⟨hos2, hs2, hv2⟩ := beatmap.dotnet.stable_sort_by_refines beatmap.objects.OsuHitObject.Insts.CoreCloneClone
    pl_ho_clone beatmap.objects.OsuHitObject.Insts.Osu_eval_coreBeatmapDotnetSortKey (·.start_time) (fun _ => rfl)
    hos1 (by omega)
  have hbr := vec_clone_id beatmap.types.BreakPeriod.Insts.CoreCloneClone (fun _ => rfl) d.breaks
  refine ⟨beatmap.playable.PlayableBeatmap.mk d.format_version d.difficulty d.difficulty d.stack_leniency
    d.audio_lead_in cpi d.breaks hos2 0#usize (alloc.vec.Vec.new (Usize × beatmap.playable.ModState)), ?_, ?_⟩
  · simp only [beatmap.playable.convert_beatmap, hcpi, bind_ok, hl1, hs2, hbr]
  · unfold convertBeatmap
    have hcp : (abs d : DecodedBeatmap).controlPoints.deepClone = (abs cpi : ControlPointInfo) := by
      rw [cpi_abs, hcpiv]; show (abs d.control_points : ControlPointInfo).deepClone = _; rw [cpi_abs]
    have hho : stableSortBy (·.startTime) ((abs d : DecodedBeatmap).hitObjects.map
        (convertHitObject (abs d : DecodedBeatmap).formatVersion (abs d : DecodedBeatmap).controlPoints.deepClone)) =
        (abs hos2 : Array OsuHitObject) := by
      rw [hcp]
      have e1 : (abs d : DecodedBeatmap).hitObjects.map (convertHitObject (abs d.format_version) (abs cpi)) =
          hos1.val.toArray.map (abs : _ → OsuHitObject) := by
        apply Array.ext'; simp only [Array.toList_map]
        show (List.map _ (d.hit_objects.val.map abs)) = _
        rw [← hv1]
      rw [show (abs d : DecodedBeatmap).formatVersion = abs d.format_version from rfl, e1, stableSortBy_map]
      rw [show ((·.startTime) ∘ (abs : beatmap.objects.OsuHitObject → OsuHitObject)) = (·.start_time) from rfl, ← hv2]
      apply Array.ext'; simp [abs]
    dsimp only
    rw [hho, hcp]
    rfl


end OsuProofs
