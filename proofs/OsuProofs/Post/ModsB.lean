/-
`beatmap::mods` (Rust) refines `OsuModel.Beatmap.Mods` / `ModConfig.hooks` (mods proof agent;
abs-style, uses the Auto lemmas). Continues Post/Mods.lean.
-/
import OsuProofs.Post.Mods
import OsuProofs.Post.TargetPractice
import OsuProofs.Beatmap.Objects
import OsuProofs.Beatmap.ModSettings5
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

theorem mods_F10 : beatmap.mods.F10 = ok (10 : F32) := by
  unfold beatmap.mods.F10; simp only [float.F32.from_bits]; congr 1

theorem beatmap.mods.hard_rock_difficulty_refines (d : beatmap.types.Difficulty) :
    ∃ r, beatmap.mods.hard_rock_difficulty d = ok r ∧ Mods.hardRockDifficulty (abs d) = abs r := by
  have h1 : beatmap.mods.HR_RATIO = ok Mods.HR_RATIO := by
    unfold beatmap.mods.HR_RATIO; simp only [float.F32.from_bits]; congr 1
  have h2 : beatmap.mods.HR_CS_RATIO = ok Mods.HR_CS_RATIO := by
    unfold beatmap.mods.HR_CS_RATIO; simp only [float.F32.from_bits]; congr 1
  unfold beatmap.mods.hard_rock_difficulty
  simp only [h1, h2, mods_F10, bind_ok, float.F32.mul, net.mathops.f32_min_refines]
  exact ⟨_, rfl, rfl⟩

/-- `acronym` holds Unicode scalar values (as produced by the decoders). -/
def AcrOk (m : beatmap.mod_settings.ModConfig) : Prop := ValidStr (alloc.vec.Vec.deref m.acronym)

theorem mods_acr (m : beatmap.mod_settings.ModConfig) (hv : AcrOk m) (a b : U8) (p) (s : String)
    (hs : ∀ acr : Slice U32, ValidStr acr → ∀ p, beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [a, b] p)) =
      ok (decide (String.ofList (strS acr) = s))) :
    beatmap.mods.acr_is m (Array.to_slice (Array.make 2#usize [a, b] p)) = ok (m.known && decide ((mcS m).acronym = s)) := by
  unfold beatmap.mods.acr_is
  cases hk : m.known
  · simp
  · simp only [if_true]; rw [hs _ hv]; simp [mcS, vstrS, strS, alloc.vec.Vec.deref]
    first | rfl | (congr 1)

theorem beatmap.mods.has_apply_to_hit_object_refines (m : beatmap.mod_settings.ModConfig) (hv : AcrOk m) :
    beatmap.mods.has_apply_to_hit_object m = ok ((mcS m).hooks.applyToHitObject.isSome) := by
  unfold beatmap.mods.has_apply_to_hit_object
  simp only [lift, bind_ok, mods_acr m hv _ _ _ _ se_HR, mods_acr m hv _ _ _ _ se_MR, mods_acr m hv _ _ _ _ se_CL]
  unfold ModConfig.hooks
  simp only [mcS]
  by_cases hk : m.known = true
  · simp only [hk, Bool.not_true, Bool.false_eq_true, if_false, Bool.true_and]
    by_cases a1 : vstrS m.acronym = "HR"
    · simp [a1]
    by_cases a2 : vstrS m.acronym = "MR"
    · simp [a2]
    by_cases a3 : vstrS m.acronym = "CL"
    · simp [a3]
    simp only [a1, a2, a3, decide_false, if_false, Bool.false_eq_true]
    split <;> simp_all
  · simp [hk]

/-- `IApplicableToDifficulty` dispatch = the `applyToDifficulty` hook of `ModConfig.hooks`. -/
theorem beatmap.mods.apply_to_difficulty_refines (m : beatmap.mod_settings.ModConfig) (hv : AcrOk m)
    (hk : KeysOk m.settings.val) (d : beatmap.types.Difficulty) :
    ∃ r, beatmap.mods.apply_to_difficulty m d = ok r ∧
      ((mcS m).hooks.applyToDifficulty.getD id) (abs d) = abs r := by
  unfold beatmap.mods.apply_to_difficulty
  simp only [lift, bind_ok, mods_acr m hv _ _ _ _ se_EZ, mods_acr m hv _ _ _ _ se_HR,
    mods_acr m hv _ _ _ _ se_DA, mods_acr m hv _ _ _ _ se_TP]
  unfold ModConfig.hooks
  by_cases hkn : m.known = true
  · simp only [hkn, Bool.not_true, Bool.false_eq_true, if_false, Bool.true_and]
    simp only [mcS] at *
    by_cases a1 : vstrS m.acronym = "EZ"
    · simpa [a1, hkn] using beatmap.mods.easy_difficulty_refines d
    by_cases a2 : vstrS m.acronym = "HR"
    · simpa [a2, hkn] using beatmap.mods.hard_rock_difficulty_refines d
    by_cases a3 : vstrS m.acronym = "DA"
    · simp only [a3, decide_true, if_true, a1, a2, decide_false, Bool.false_eq_true, if_false]
      obtain ⟨r, h1, h2⟩ := beatmap.mods.difficulty_adjust_refines m hk d
      refine ⟨r, h1, ?_⟩
      rw [← h2]; simp [mcS, a3, hkn]
    by_cases a4 : vstrS m.acronym = "TP"
    · simp only [a4, decide_true, if_true, a1, a2, a3, decide_false, Bool.false_eq_true, if_false]
      simp [float.F32.mul, abs, hkn]
    simp only [a1, a2, a3, a4, decide_false, if_false, Bool.false_eq_true]
    refine ⟨d, rfl, ?_⟩
    simp only [hkn, Bool.not_true, Bool.false_eq_true, if_false]
    split <;> simp_all
  · have : m.known = false := by simpa using hkn
    simp [this, mcS]

/-- Classic's nested-object update (Rust representation). -/
def chN (val : Bool) (n : beatmap.objects.NestedObject) : beatmap.objects.NestedObject :=
  match n.kind with
  | .Head | .Tail => { n with classic_slider_behaviour := val }
  | _ => n

theorem beatmap.mods.classic_hit_object_refines (val : Bool) (h : beatmap.objects.OsuHitObject) :
    ∃ r, beatmap.mods.classic_hit_object val h = ok r ∧ Mods.classicHitObject (abs val) (abs h) = abs r := by
  obtain ⟨v, hl, hv⟩ := loop_fold_gen' (fun x => beatmap.mods.classic_hit_object_loop.body val x.1 x.2) (·.2)
    h.nested.val.length (by have := h.nested.property; omega)
    (fun x => x.1.val.length = h.nested.val.length) (fun x => x.1.val)
    (fun k L => L.modify k (chN val)) (fun y L => y.val = L)
    (by
      intro t hI hlt j1 hj1 hj1v
      have hl : t.2.val < t.1.val.length := by omega
      have hm : t.1.val.modify t.2.val (chN val) = t.1.val.set t.2.val (chN val (t.1.val[t.2.val]'hl)) :=
        list_modify_set _ _ hl _
      cases hk : (t.1.val[t.2.val]'hl).kind
      case Head | Tail =>
        refine ⟨(alloc.vec.Vec.set t.1 t.2 (chN val (t.1.val[t.2.val]'hl)), j1), ?_, rfl, ?_, ?_⟩
        · simp [beatmap.mods.classic_hit_object_loop.body, vec_lt_len_iff, hl, hk, hj1, chN,
            vec_index_eq _ _ hl, vec_index_mut_eq _ _ hl]
        · simp [vec_set_val', hm]
        · simp [vec_set_val', hI]
      all_goals
        refine ⟨(t.1, j1), ?_, rfl, ?_, hI⟩
        · simp [beatmap.mods.classic_hit_object_loop.body, vec_lt_len_iff, hl, hk, hj1, vec_index_eq _ _ hl]
        · simp only [hm, chN, hk]; simp)
    (by loop_end [beatmap.mods.classic_hit_object_loop.body])
    (h.nested, 0#usize) rfl (by simp)
  simp only at hl hv
  rw [show (0#usize : Usize).val = 0 from rfl, iterR_modify_map] at hv
  have hloop : beatmap.mods.classic_hit_object_loop val h.nested 0#usize = ok v := by
    unfold beatmap.mods.classic_hit_object_loop; exact hl
  unfold beatmap.mods.classic_hit_object Mods.classicHitObject
  cases hk : h.kind with
  | Slider sd =>
    refine ⟨{ h with kind := .Slider { sd with classic_slider_behaviour := val }, nested := v }, ?_, ?_⟩
    · simp [hk, hloop]
    · simp only [abs, hk, hv]
      simp [abs, List.map_map, Function.comp_def, chN]
      intro a _
      cases hka : a.kind <;> simp [hka, abs]
  | Circle => exact ⟨{ h with kind := .Circle }, by simp [hk], by simp [abs, hk]⟩
  | Spinner sp => exact ⟨{ h with kind := .Spinner sp }, by simp [hk], by simp [abs, hk]⟩

/-- first `some` of `g x k` over a list with running index `k` -/
def fsi {X R : Type} (g : X → Nat → Option R) : List X → Nat → Option R
  | [], _ => none
  | x :: t, k => match g x k with | some r => some r | none => fsi g t (k + 1)

theorem forIn_fsi {X R : Type} (g : X → Nat → Option R)
    (F : X → Option R × Nat → Id (ForInStep (Option R × Nat)))
    (hF : ∀ x k, F x (none, k) = (g x k).elim (.yield (none, k + 1)) (fun r => .done (some r, k))) :
    ∀ (l : List X) (k : Nat), (forIn (m := Id) l (none, k) F).1 = fsi g l k := by
  intro l
  induction l with
  | nil => intro k; rfl
  | cons x t ih =>
    intro k
    rw [List.forIn_cons, hF]
    simp only [fsi]
    cases g x k with
    | some r => rfl
    | none => exact ih (k + 1)


/-- spec: whether nested object `n` may be the first adjustable one -/
def faNS (b : Bool) (n : NestedObject) : Bool :=
  !(b && match n.kind with | .spinnerTick => true | .spinnerBonusTick => true | _ => false)

def faNG (b : Bool) (i ep : Nat) (n : NestedObject) (j : Nat) : Option (Option ObjRef) :=
  if faNS b n then some (some { index := i, nested := some j, epoch := ep }) else none

def faOG (b : Bool) (ep : Nat) (h : OsuHitObject) (i : Nat) : Option (Option ObjRef) :=
  if (!(b && h.isSpinner)) = true then some (some { index := i, epoch := ep })
  else fsi (faNG b i ep) h.nested.toList 0

theorem mods_fao_spec (pb : PlayableBeatmap) (b : Bool) :
    Mods.firstAdjustableObject pb b = (fsi (faOG b pb.epoch) pb.hitObjects.toList 0).join := by
  unfold Mods.firstAdjustableObject
  simp only [Id.run]
  rw [← Array.forIn_toList, id_bind_eq]
  split
  all_goals rename_i heq
  all_goals rw [forIn_fsi (faOG b pb.epoch) _ ?_ pb.hitObjects.toList 0] at heq
  all_goals (try (rw [heq]; rfl))
  all_goals
    intro h k
    simp only [faOG]
    split
    · rfl
    · rw [← Array.forIn_toList, id_bind_eq]
      split
      all_goals rename_i heq2
      all_goals rw [forIn_fsi (faNG b k pb.epoch) _ ?_ h.nested.toList 0] at heq2
      all_goals (try (rw [heq2]; rfl))
      all_goals (intro n j; simp only [faNG, faNS]; split <;> cases b <;> simp_all <;> rfl)

theorem fsi_faNG_some (b : Bool) (i ep : Nat) : ∀ (l : List NestedObject) k r,
    fsi (faNG b i ep) l k = some r → r.isSome := by
  intro l
  induction l with
  | nil => intro k r h; simp [fsi] at h
  | cons x t ih =>
    intro k r h
    simp only [fsi] at h
    cases hg : faNG b i ep x k with
    | some r' =>
      rw [hg] at h; cases h; unfold faNG at hg
      split at hg
      · cases hg; rfl
      · cases hg
    | none => rw [hg] at h; exact ih _ _ h

theorem mods_fan_body (v : alloc.vec.Vec beatmap.objects.OsuHitObject) (ep i : Usize) (b : Bool)
    (hi : i.val < v.val.length) (j j1 : Usize) (hlt : j.val < (v.val[i.val]'hi).nested.val.length)
    (hj1 : j + 1#usize = ok j1) :
    beatmap.mods.first_adjustable_nested_loop.body v ep i b (alloc.vec.Vec.len (v.val[i.val]'hi).nested) none j =
      ok (.cont (if faNS b (abs ((v.val[i.val]'hi).nested.val[j.val]'hlt) : NestedObject) then
        some ({ index := i, nested := some j, epoch := ep } : beatmap.playable.ObjRef) else none, j1)) := by
  have hl' : j < alloc.vec.Vec.len (v.val[i.val]'hi).nested := by
    show j.val < (alloc.vec.Vec.len _).val; simpa using hlt
  simp only [beatmap.mods.first_adjustable_nested_loop.body, core.option.Option.is_none, Option.isNone_none,
    if_true, hl', vec_index_eq _ _ hi, vec_index_eq _ _ hlt, bind_ok, hj1]
  cases hk : ((v.val[i.val]'hi).nested.val[j.val]'hlt).kind <;> cases b <;>
    simp [hk, beatmap.objects.NestedKind.Insts.CoreCmpPartialEqNestedKind.eq, faNS, abs,
      beatmap.objects.NestedKind.read_discriminant] <;> decide

theorem mods_fan_loop (v : alloc.vec.Vec beatmap.objects.OsuHitObject) (ep i : Usize) (b : Bool)
    (hi : i.val < v.val.length) :
    ∀ j : Usize, j.val ≤ (v.val[i.val]'hi).nested.val.length →
      ∃ r, beatmap.mods.first_adjustable_nested_loop v ep i b (alloc.vec.Vec.len (v.val[i.val]'hi).nested) none j = ok r ∧
        (abs r : Option ObjRef) = (fsi (faNG b i.val ep.val) (((v.val[i.val]'hi).nested.val.map abs).drop j.val) j.val).join := by
  intro j
  induction hk : (v.val[i.val]'hi).nested.val.length - j.val using Nat.strong_induction_on generalizing j with
  | _ k ih =>
    intro hle
    unfold beatmap.mods.first_adjustable_nested_loop
    rw [loop_unfold]
    by_cases hlt : j.val < (v.val[i.val]'hi).nested.val.length
    · have hl' : j < alloc.vec.Vec.len (v.val[i.val]'hi).nested := by
        show j.val < (alloc.vec.Vec.len _).val; simpa using hlt
      obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := (v.val[i.val]'hi).nested.property; omega)
      have hdrop : ((v.val[i.val]'hi).nested.val.map abs).drop j.val =
          (abs ((v.val[i.val]'hi).nested.val[j.val]'hlt) : NestedObject) ::
            ((v.val[i.val]'hi).nested.val.map abs).drop (j.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hlt)]; simp
      rw [hdrop]; simp only [fsi]
      by_cases hc : faNS b (abs ((v.val[i.val]'hi).nested.val[j.val]'hlt) : NestedObject) = true
      · have hg : faNG b i.val ep.val (abs ((v.val[i.val]'hi).nested.val[j.val]'hlt) : NestedObject) j.val =
            some (some { index := i.val, nested := some j.val, epoch := ep.val }) := by simp [faNG, hc]
        rw [hg]
        refine ⟨some { index := i, nested := some j, epoch := ep }, ?_, rfl⟩
        rw [mods_fan_body v ep i b hi j j1 hlt hj1]; simp only [hc, if_true, bind_ok]
        rw [loop_unfold]; simp [beatmap.mods.first_adjustable_nested_loop.body, core.option.Option.is_none]
      · have hg : faNG b i.val ep.val (abs ((v.val[i.val]'hi).nested.val[j.val]'hlt) : NestedObject) j.val = none := by
          simp [faNG, hc]
        rw [hg]; simp only
        obtain ⟨r, hr, hr2⟩ := ih ((v.val[i.val]'hi).nested.val.length - j1.val) (by omega) j1 rfl (by omega)
        refine ⟨r, ?_, by rw [hr2, hj1v]⟩
        rw [mods_fan_body v ep i b hi j j1 hlt hj1]; simp only [hc, if_false, Bool.false_eq_true, bind_ok]
        unfold beatmap.mods.first_adjustable_nested_loop at hr; exact hr
    · have hl' : ¬ j < alloc.vec.Vec.len (v.val[i.val]'hi).nested := by
        show ¬ j.val < (alloc.vec.Vec.len _).val; simpa using hlt
      refine ⟨none, ?_, ?_⟩
      · simp [beatmap.mods.first_adjustable_nested_loop.body, core.option.Option.is_none, hl']
      · rw [List.drop_eq_nil_of_le (by simp; omega)]; rfl

/-- nested part of `getFirstAdjustableObjectRecursive` for object `i` -/
theorem beatmap.mods.first_adjustable_nested_refines (pb : beatmap.playable.PlayableBeatmap) (i : Usize) (b : Bool)
    (hi : i.val < pb.hit_objects.val.length) :
    ∃ r, beatmap.mods.first_adjustable_nested pb i b = ok r ∧
      (abs r : Option ObjRef) = (fsi (faNG b i.val pb.epoch.val)
        (abs (pb.hit_objects.val[i.val]'hi) : OsuHitObject).nested.toList 0).join := by
  obtain ⟨r, hr, hr2⟩ := mods_fan_loop pb.hit_objects pb.epoch i b hi 0#usize (by simp)
  refine ⟨r, ?_, by simpa [abs] using hr2⟩
  unfold beatmap.mods.first_adjustable_nested
  simp only [vec_index_eq _ _ hi, bind_ok]; exact hr

theorem mods_join_iff (o : Option (Option ObjRef)) (h : ∀ r, o = some r → r.isSome)
    (rn : Option beatmap.playable.ObjRef) (he : (abs rn : Option ObjRef) = o.join) : (rn.isNone ↔ o = none) := by
  cases o with
  | none => cases rn <;> simp_all [abs]
  | some r =>
    have := h r rfl
    cases r with
    | none => simp at this
    | some r => cases rn <;> simp_all [abs]

theorem mods_fao_body (pb : beatmap.playable.PlayableBeatmap) (b : Bool) (i i1 : Usize)
    (hi : i.val < pb.hit_objects.val.length) (hi1 : i + 1#usize = ok i1) :
    ∃ r1, beatmap.mods.first_adjustable_object_loop.body pb b none i = ok (.cont (r1, i1)) ∧
      (abs r1 : Option ObjRef) = (faOG b pb.epoch.val (abs (pb.hit_objects.val[i.val]'hi)) i.val).join ∧
      (r1.isNone ↔ faOG b pb.epoch.val (abs (pb.hit_objects.val[i.val]'hi)) i.val = none) := by
  have hl' : i < alloc.vec.Vec.len pb.hit_objects := by show i.val < (alloc.vec.Vec.len _).val; simpa using hi
  by_cases hs : (b && (abs (pb.hit_objects.val[i.val]'hi) : OsuHitObject).isSpinner) = true
  · simp only [Bool.and_eq_true] at hs
    obtain ⟨rfl, hsp⟩ := hs
    obtain ⟨rn, hrn, hrn2⟩ := beatmap.mods.first_adjustable_nested_refines pb i true hi
    have hfo : faOG true pb.epoch.val (abs (pb.hit_objects.val[i.val]'hi)) i.val =
        fsi (faNG true i.val pb.epoch.val) (abs (pb.hit_objects.val[i.val]'hi) : OsuHitObject).nested.toList 0 := by
      simp [faOG, hsp]
    refine ⟨rn, ?_, by rw [hfo, hrn2], ?_⟩
    · have hsp' : beatmap.objects.is_spinner (pb.hit_objects.val[i.val]'hi) = ok true := by rw [is_spinner_ok, hsp]
      simp only [beatmap.mods.first_adjustable_object_loop.body, core.option.Option.is_none, Option.isNone_none,
        if_true, hl', vec_index_eq _ _ hi, bind_ok, hsp', hrn, hi1]
    · rw [hfo]; exact mods_join_iff _ (fsi_faNG_some _ _ _ _ _) rn hrn2
  · have hfo : faOG b pb.epoch.val (abs (pb.hit_objects.val[i.val]'hi)) i.val =
        some (some { index := i.val, epoch := pb.epoch.val }) := by simp [faOG, hs]
    refine ⟨some { index := i, nested := none, epoch := pb.epoch }, ?_, by rw [hfo]; rfl, by rw [hfo]; simp⟩
    cases b
    · simp [beatmap.mods.first_adjustable_object_loop.body, core.option.Option.is_none, hl', hi1]
    · have hsp : (abs (pb.hit_objects.val[i.val]'hi) : OsuHitObject).isSpinner = false := by simpa using hs
      have hsp' : beatmap.objects.is_spinner (pb.hit_objects.val[i.val]'hi) = ok false := by rw [is_spinner_ok, hsp]
      simp only [beatmap.mods.first_adjustable_object_loop.body, core.option.Option.is_none, Option.isNone_none,
        if_true, hl', vec_index_eq _ _ hi, bind_ok, hsp', hi1, Bool.false_eq_true, if_false]

theorem mods_fao_loop (pb : beatmap.playable.PlayableBeatmap) (b : Bool) :
    ∀ i : Usize, i.val ≤ pb.hit_objects.val.length →
      ∃ r, beatmap.mods.first_adjustable_object_loop pb b none i = ok r ∧
        (abs r : Option ObjRef) = (fsi (faOG b pb.epoch.val) ((pb.hit_objects.val.map abs).drop i.val) i.val).join := by
  intro i
  induction hk : pb.hit_objects.val.length - i.val using Nat.strong_induction_on generalizing i with
  | _ k ih =>
    intro hle
    unfold beatmap.mods.first_adjustable_object_loop
    rw [loop_unfold]
    by_cases hlt : i.val < pb.hit_objects.val.length
    · obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := pb.hit_objects.property; omega)
      obtain ⟨r1, hb, hr1, hn⟩ := mods_fao_body pb b i i1 hlt hi1
      have hdrop : (pb.hit_objects.val.map abs).drop i.val =
          (abs (pb.hit_objects.val[i.val]'hlt) : OsuHitObject) :: (pb.hit_objects.val.map abs).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hlt)]; simp
      rw [hdrop]; simp only [hb, fsi, bind_ok]
      cases r1 with
      | none =>
        have hf := hn.mp rfl
        rw [hf]; simp only
        obtain ⟨r, hr, hr2⟩ := ih (pb.hit_objects.val.length - i1.val) (by omega) i1 rfl (by omega)
        refine ⟨r, ?_, by rw [hr2, hi1v]⟩
        unfold beatmap.mods.first_adjustable_object_loop at hr; exact hr
      | some x =>
        have hf : faOG b pb.epoch.val (abs (pb.hit_objects.val[i.val]'hlt)) i.val ≠ none := by
          intro h; simpa using hn.mpr h
        cases hg : faOG b pb.epoch.val (abs (pb.hit_objects.val[i.val]'hlt)) i.val with
        | none => exact absurd hg hf
        | some y =>
          refine ⟨some x, ?_, ?_⟩
          · rw [loop_unfold]; simp [beatmap.mods.first_adjustable_object_loop.body, core.option.Option.is_none]
          · rw [hr1, hg]
    · have hl' : ¬ i < alloc.vec.Vec.len pb.hit_objects := by show ¬ i.val < (alloc.vec.Vec.len _).val; simpa using hlt
      refine ⟨none, ?_, ?_⟩
      · simp [beatmap.mods.first_adjustable_object_loop.body, core.option.Option.is_none, hl']
      · rw [List.drop_eq_nil_of_le (by simp; omega)]; rfl

/-- `getFirstAdjustableObjectRecursive` -/
theorem beatmap.mods.first_adjustable_object_refines (pb : beatmap.playable.PlayableBeatmap) (b : Bool) :
    ∃ r, beatmap.mods.first_adjustable_object pb b = ok r ∧
      Mods.firstAdjustableObject (abs pb) b = abs r := by
  obtain ⟨r, hr, hr2⟩ := mods_fao_loop pb b 0#usize (by simp)
  refine ⟨r, by unfold beatmap.mods.first_adjustable_object; exact hr, ?_⟩
  rw [mods_fao_spec, hr2]; simp [abs]

theorem beatmap.mods.record_first_object_refines (b : Bool) (idx : Usize) (pb : beatmap.playable.PlayableBeatmap)
    (hm : pb.mod_states.val.length < Usize.max) :
    ∃ r, beatmap.mods.record_first_object b idx pb = ok r ∧
      Mods.recordFirstObject b (abs idx) (abs pb) = abs r := by
  obtain ⟨r, hr, hr2⟩ := beatmap.mods.first_adjustable_object_refines pb b
  obtain ⟨w, hw, hwv⟩ := push_eq pb.mod_states (idx, beatmap.playable.ModState.FirstObject r) hm
  refine ⟨{ pb with mod_states := w }, ?_, ?_⟩
  · simp [beatmap.mods.record_first_object, hr, hw]
  · simp only [Mods.recordFirstObject, hr2]
    simp [abs, hwv]

theorem mods_lot_loop (v : alloc.vec.Vec beatmap.objects.OsuHitObject) :
    ∃ r, beatmap.mods.last_object_time_loop v (alloc.vec.Vec.with_capacity F64 (alloc.vec.Vec.len v)) 0#usize = ok r ∧
      r.val = v.val.map (fun h => (abs h : OsuHitObject).endTime) := by
  have := loop_push_map (fun (x : alloc.vec.Vec F64 × Usize) => beatmap.mods.last_object_time_loop.body v x.1 x.2)
    v.val.length (fun i => ((v.val.map (abs : _ → OsuHitObject))[i]!).endTime)
    (by
      intro ts i hi hmax
      have hil : i < alloc.vec.Vec.len v := by show i.val < (alloc.vec.Vec.len v).val; simpa using hi
      obtain ⟨w, hw, hwv⟩ := push_eq ts ((abs (v.val[i.val]'hi) : OsuHitObject).endTime) (by omega)
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := v.property; omega)
      refine ⟨w, i1, ?_, by rw [hwv, getElem!_pos _ i.val (by simpa using hi)]; simp, hi1v⟩
      simp only [beatmap.mods.last_object_time_loop.body, hil, if_true, vec_index_eq v i hi, bind_ok,
        beatmap.objects.end_time_refines, hw, hi1])
    (by
      intro ts i hi
      have hil : ¬ i < alloc.vec.Vec.len v := by show ¬ i.val < (alloc.vec.Vec.len v).val; simp; omega
      simp [beatmap.mods.last_object_time_loop.body, hil])
    (alloc.vec.Vec.with_capacity _ (alloc.vec.Vec.len v)) 0#usize (by simp)
    (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new])
  obtain ⟨r, hl, hr⟩ := this
  refine ⟨r, by unfold beatmap.mods.last_object_time_loop; exact hl, ?_⟩
  rw [hr]; simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
  apply List.ext_getElem (by simp)
  intro k h1 h2; simp at h2; simp [List.getElem?_eq_getElem h2]

/-- `GetLastObjectTime()` (LINQ `Max` throws on an empty beatmap; the callers guard). -/
theorem beatmap.mods.last_object_time_refines (pb : beatmap.playable.PlayableBeatmap)
    (h : 0 < pb.hit_objects.val.length) :
    ∃ r, beatmap.mods.last_object_time pb = ok r ∧ Mods.lastObjectTime (abs pb) = abs r := by
  obtain ⟨r, hr, hrv⟩ := mods_lot_loop pb.hit_objects
  refine ⟨Mods.lastObjectTime (abs pb), ?_, rfl⟩
  unfold beatmap.mods.last_object_time
  simp only [hr, bind_ok]
  rw [beatmap.mods.linq_max_f64_refines _ (by simp [alloc.vec.Vec.deref, hrv]; exact h)]
  unfold Mods.lastObjectTime
  congr 2
  simp [alloc.vec.Vec.deref, hrv, abs]

theorem beatmap.mods.time_ramp_refines (idx : Usize) (pb : beatmap.playable.PlayableBeatmap)
    (hm : pb.mod_states.val.length < Usize.max) :
    ∃ r, beatmap.mods.time_ramp idx pb = ok r ∧ Mods.timeRamp (abs idx) (abs pb) = abs r := by
  have hfr : beatmap.mods.FINAL_RATE_PROGRESS = ok Mods.FINAL_RATE_PROGRESS := by
    unfold beatmap.mods.FINAL_RATE_PROGRESS; simp only [float.F32.from_bits]; congr 1
  have hz : float.F64.from_bits 0#u64 = ok (0 : F64) := by simp [float.F64.from_bits]; decide
  by_cases hn : 0 < pb.hit_objects.val.length
  · obtain ⟨lt, hlt, hlt2⟩ := beatmap.mods.last_object_time_refines pb hn
    have hn' : alloc.vec.Vec.len pb.hit_objects > 0#usize := by show (0#usize).val < _; simpa using hn
    obtain ⟨w, hw, hwv⟩ := push_eq pb.mod_states (idx, beatmap.playable.ModState.TimeRamp
      (pb.hit_objects.val[0]'hn).start_time ((pb.hit_objects.val[0]'hn).start_time +
        F32.toF64 Mods.FINAL_RATE_PROGRESS * (lt - (pb.hit_objects.val[0]'hn).start_time))) hm
    refine ⟨{ pb with mod_states := w }, ?_, ?_⟩
    · simp [beatmap.mods.time_ramp, hn', vec_index_eq _ 0#usize hn, hlt, hfr, float.F32.to_f64, float.F64.sub,
        float.F64.mul, float.F64.add, Mods.FINAL_RATE_PROGRESS] at hw ⊢
      rw [hw]; simp only [bind_ok]
    · simp only [Mods.timeRamp, hlt2]
      simp [abs, hn, hwv, Mods.FINAL_RATE_PROGRESS]
  · have hn0 : pb.hit_objects.val.length = 0 := by omega
    have hn' : ¬ alloc.vec.Vec.len pb.hit_objects > 0#usize := by show ¬ (0#usize).val < _; simp [hn0]
    obtain ⟨w, hw, hwv⟩ := push_eq pb.mod_states (idx, beatmap.playable.ModState.TimeRamp 0
      (0 + F32.toF64 Mods.FINAL_RATE_PROGRESS * (0 - 0))) hm
    refine ⟨{ pb with mod_states := w }, ?_, ?_⟩
    · simp only [beatmap.mods.time_ramp, hn', hz, hfr, if_false, bind_ok, float.F32.to_f64, float.F64.sub,
        float.F64.mul, float.F64.add]
      rw [hw]; simp only [bind_ok]
    · simp only [Mods.timeRamp]
      simp [abs, hn0, hwv, Mods.FINAL_RATE_PROGRESS]

/-- `m.known && acronym == lit` (no spec def: the spec matches `ModConfig.acronym` on literals). -/
theorem beatmap.mods.acr_is_refines (m : beatmap.mod_settings.ModConfig) (hv : AcrOk m) (lit : Slice U8) :
    beatmap.mods.acr_is m lit = ok (m.known && decide (strS (alloc.vec.Vec.deref m.acronym) = litS lit)) := by
  unfold beatmap.mods.acr_is
  cases m.known
  · simp
  · simp only [if_true, Bool.true_and]; exact beatmap.dotnet.str_eq_refines _ hv lit

theorem forIn_yield_foldl {X S : Type} (G : X → S → Id (ForInStep S)) (g : S → X → S)
    (hG : ∀ x s, G x s = .yield (g s x)) : ∀ (l : List X) (s : S), forIn (m := Id) l s G = l.foldl g s := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons x t ih => intro s; rw [List.forIn_cons, hG]; exact ih _

/-- FreezeFrame's nested step (spec types) -/
def ffNS (lnc : F64) (s : Nat × Array NestedObject) (n : NestedObject) : Nat × Array NestedObject :=
  match n.kind with
  | .tick => (s.1, s.2.push n)
  | .repeat => if s.1 > 2 then (s.1, s.2.push n)
      else (s.1 + 1, s.2.push { n with timePreempt := n.timePreempt + (n.startTime - lnc) })
  | _ => (s.1, s.2.push { n with timePreempt := n.timePreempt + (n.startTime - lnc) })

/-- FreezeFrame's object step (spec types) -/
def ffHS (s : F64 × Array OsuHitObject) (h : OsuHitObject) : F64 × Array OsuHitObject :=
  let lnc := if h.newCombo then h.startTime else s.1
  let h' := if h.isSpinner then h else { h with timePreempt := h.timePreempt + (h.startTime - lnc) }
  (lnc, s.2.push { h' with nested := (h'.nested.toList.foldl (ffNS lnc) (0, #[])).2 })

theorem mods_ff_spec (pb : PlayableBeatmap) :
    Mods.freezeFrame pb = { pb with hitObjects := (pb.hitObjects.toList.foldl ffHS (0, #[])).2 } := by
  unfold Mods.freezeFrame
  simp only [Id.run]
  rw [← Array.forIn_toList, forIn_yield_foldl _ ffHS]
  · rfl
  · intro h s
    simp only [ffHS]
    split
    all_goals
      rename_i hnc
      rw [← Array.forIn_toList, id_bind_eq]
      rw [forIn_yield_foldl _ (ffNS _)]
      · simp only [hnc, if_true, if_false, Bool.false_eq_true]; rfl
      · intro n s; simp only [ffNS]; split <;> (try split) <;> simp_all <;> rfl

theorem mods_ff_push (lnc : F64) : ∀ (l : List NestedObject) (rc : Nat) (acc : Array NestedObject),
    (l.foldl (ffNS lnc) (rc, acc)).2 = acc ++ (l.foldl (ffNS lnc) (rc, #[])).2 := by
  intro l
  induction l with
  | nil => intro rc acc; simp
  | cons x t ih =>
    intro rc acc
    simp only [List.foldl_cons]
    have e1 : ∀ acc', ffNS lnc (rc, acc') x = ((ffNS lnc (rc, #[]) x).1, acc' ++ (ffNS lnc (rc, #[]) x).2) := by
      intro acc'; simp only [ffNS]; split <;> (try split) <;> simp
    rw [e1 acc, e1 #[], ih _ (acc ++ _), ih _ (#[] ++ _)]
    simp [Array.append_assoc]

theorem mods_ff_body (lnc : F64) (v : alloc.vec.Vec beatmap.objects.NestedObject) (rc j j1 : Usize)
    (hj : j.val < v.val.length) (hrc : rc.val ≤ 3) (hj1 : j + 1#usize = ok j1) :
    ∃ rc1 : Usize, ∃ n1, beatmap.mods.freeze_frame_loop0_loop0.body lnc v rc j = ok (.cont (alloc.vec.Vec.set v j n1, rc1, j1)) ∧
      rc1.val ≤ 3 ∧ ffNS lnc (rc.val, #[]) (abs (v.val[j.val]'hj)) = (rc1.val, #[abs n1]) := by
  have hl : j < alloc.vec.Vec.len v := by show j.val < (alloc.vec.Vec.len v).val; simpa using hj
  cases hk : (v.val[j.val]'hj).kind
  case Repeat =>
    by_cases hr : rc.val > 2
    · have hr' : rc > 2#usize := by show (2#usize).val < rc.val; simpa using hr
      refine ⟨rc, { v.val[j.val]'hj with kind := .Repeat, time_preempt := (v.val[j.val]'hj).time_preempt }, ?_, hrc, ?_⟩
      · simp [beatmap.mods.freeze_frame_loop0_loop0.body, hl, vec_index_mut_eq _ _ hj, hk, hr', hj1]
      · simp [ffNS, abs, hk, hr]
    · have hr' : ¬ rc > 2#usize := by show ¬ (2#usize).val < rc.val; simpa using hr
      obtain ⟨rc1, hrc1, hrc1v⟩ := usize_add_one rc (by have := Usize.bounds_eq; simp [U32.max_eq, U64.max_eq] at this; omega)
      refine ⟨rc1, { v.val[j.val]'hj with kind := .Repeat, time_preempt := (v.val[j.val]'hj).time_preempt +
        ((v.val[j.val]'hj).start_time - lnc) }, ?_, by omega, ?_⟩
      · simp [beatmap.mods.freeze_frame_loop0_loop0.body, hl, vec_index_mut_eq _ _ hj, hk, hr', hj1, hrc1,
          float.F64.sub, float.F64.add]
      · simp [ffNS, abs, hk, hr, hrc1v]
  case Tick =>
    refine ⟨rc, { v.val[j.val]'hj with kind := .Tick, time_preempt := (v.val[j.val]'hj).time_preempt }, ?_, hrc, ?_⟩
    · simp [beatmap.mods.freeze_frame_loop0_loop0.body, hl, vec_index_mut_eq _ _ hj, hk, hj1]
    · simp [ffNS, abs, hk]
  all_goals
    refine ⟨rc, { v.val[j.val]'hj with kind := (v.val[j.val]'hj).kind, time_preempt := (v.val[j.val]'hj).time_preempt +
        ((v.val[j.val]'hj).start_time - lnc) }, ?_, hrc, ?_⟩
    · simp [beatmap.mods.freeze_frame_loop0_loop0.body, hl, vec_index_mut_eq _ _ hj, hk, hj1, float.F64.sub, float.F64.add]
    · simp [ffNS, abs, hk]

theorem mods_ff_inner (lnc : F64) : ∀ (v : alloc.vec.Vec beatmap.objects.NestedObject) (rc j : Usize),
    j.val ≤ v.val.length → rc.val ≤ 3 →
    ∃ v', beatmap.mods.freeze_frame_loop0_loop0 lnc v rc j = ok v' ∧
      v'.val.map abs = (v.val.map abs).take j.val ++ (((v.val.map abs).drop j.val).foldl (ffNS lnc) (rc.val, #[])).2.toList := by
  intro v rc j
  induction hk : v.val.length - j.val using Nat.strong_induction_on generalizing v rc j with
  | _ k ih =>
    intro hle hrc
    unfold beatmap.mods.freeze_frame_loop0_loop0
    rw [loop_unfold]
    by_cases hlt : j.val < v.val.length
    · obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := v.property; omega)
      obtain ⟨rc1, n1, hb, hrc1, hst⟩ := mods_ff_body lnc v rc j j1 hlt hrc hj1
      have hlen : (alloc.vec.Vec.set v j n1).val.length = v.val.length := by simp [vec_set_val']
      obtain ⟨v', hv', hv'v⟩ := ih ((alloc.vec.Vec.set v j n1).val.length - j1.val) (by omega) _ rc1 j1 rfl
        (by omega) hrc1
      refine ⟨v', ?_, ?_⟩
      · simp only [hb, bind_ok]; unfold beatmap.mods.freeze_frame_loop0_loop0 at hv'; exact hv'
      · rw [hv'v, hj1v]
        have hd : (v.val.map abs).drop j.val = (abs (v.val[j.val]'hlt) : NestedObject) :: (v.val.map abs).drop (j.val + 1) := by
          rw [List.drop_eq_getElem_cons (by simpa using hlt)]; simp
        rw [hd, List.foldl_cons, hst, mods_ff_push]
        simp [vec_set_val', List.take_succ, List.drop_set, List.take_set, hlt, List.map_set]
        rw [List.set_eq_of_length_le (by simp), mods_ff_push lnc _ _ #[abs n1]]; simp
    · have hl' : ¬ j < alloc.vec.Vec.len v := by show ¬ j.val < (alloc.vec.Vec.len v).val; simpa using hlt
      refine ⟨v, by simp [beatmap.mods.freeze_frame_loop0_loop0.body, hl'], ?_⟩
      rw [List.drop_eq_nil_of_le (by simp; omega), List.take_of_length_le (by simp; omega)]; simp

theorem mods_ffh_push : ∀ (l : List OsuHitObject) (lnc : F64) (acc : Array OsuHitObject),
    (l.foldl ffHS (lnc, acc)).2 = acc ++ (l.foldl ffHS (lnc, #[])).2 := by
  intro l
  induction l with
  | nil => intro lnc acc; simp
  | cons x t ih =>
    intro lnc acc
    simp only [List.foldl_cons]
    have e1 : ∀ acc', ffHS (lnc, acc') x = ((ffHS (lnc, #[]) x).1, acc' ++ (ffHS (lnc, #[]) x).2) := by
      intro acc'; simp [ffHS]
    rw [e1 acc, e1 #[], ih _ (acc ++ _), ih _ (#[] ++ _)]
    simp [Array.append_assoc]

theorem mods_ff_obody (pb : beatmap.playable.PlayableBeatmap) (lnc : F64) (i i1 : Usize)
    (hi : i.val < pb.hit_objects.val.length) (hi1 : i + 1#usize = ok i1) :
    ∃ h1, beatmap.mods.freeze_frame_loop0.body pb lnc i =
        ok (.cont ({ pb with hit_objects := alloc.vec.Vec.set pb.hit_objects i h1 },
          (ffHS (lnc, #[]) (abs (pb.hit_objects.val[i.val]'hi))).1, i1)) ∧
      ffHS (lnc, #[]) (abs (pb.hit_objects.val[i.val]'hi)) = ((ffHS (lnc, #[]) (abs (pb.hit_objects.val[i.val]'hi))).1, #[abs h1]) := by
  have hl : i < alloc.vec.Vec.len pb.hit_objects := by show i.val < (alloc.vec.Vec.len _).val; simpa using hi
  have hb0 := vec_index_mut_eq _ _ hi
  generalize hh : pb.hit_objects.val[i.val]'hi = h at hb0 ⊢
  have hsp := is_spinner_ok h
  have hnc' : (abs h : OsuHitObject).newCombo = h.new_combo := rfl
  have hst' : (abs h : OsuHitObject).startTime = h.start_time := rfl
  have htp' : (abs h : OsuHitObject).timePreempt = h.time_preempt := rfl
  have hns' : (abs h : OsuHitObject).nested.toList = h.nested.val.map abs := by simp [abs]
  cases hnc : h.new_combo <;> cases hs : (abs h : OsuHitObject).isSpinner
  all_goals
    obtain ⟨v, hv, hvv⟩ := mods_ff_inner (if h.new_combo then h.start_time else lnc) h.nested 0#usize 0#usize (by simp) (by simp)
    have hvv' : (v.val.map abs).toArray =
        ((h.nested.val.map abs).foldl (ffNS (if h.new_combo then h.start_time else lnc)) (0, #[])).2 := by
      rw [hvv]; simp
    simp only [hnc, if_true, if_false, Bool.false_eq_true] at hv hvv hvv'
  · refine ⟨{ h with time_preempt := h.time_preempt + (h.start_time - lnc), nested := v }, ?_, ?_⟩
    · simp [beatmap.mods.freeze_frame_loop0.body, hl, hb0, hnc, hsp, hs, hv, hi1, float.F64.sub, float.F64.add, ffHS,
        hnc', hst']
    · simp only [ffHS, hnc', hnc, hs, Prod.mk.injEq, true_and, hns', ite_true, ite_false, Bool.false_eq_true]
      rw [← hvv']; simp [abs]
  · refine ⟨{ h with time_preempt := h.time_preempt, nested := v }, ?_, ?_⟩
    · simp [beatmap.mods.freeze_frame_loop0.body, hl, hb0, hnc, hsp, hs, hv, hi1, ffHS, hnc', hst']
    · simp only [ffHS, hnc', hnc, hs, Prod.mk.injEq, true_and, hns', ite_true, ite_false, Bool.false_eq_true]
      rw [← hvv']; simp [abs]
  · refine ⟨{ h with time_preempt := h.time_preempt + (h.start_time - h.start_time), nested := v }, ?_, ?_⟩
    · simp [beatmap.mods.freeze_frame_loop0.body, hl, hb0, hnc, hsp, hs, hv, hi1, float.F64.sub, float.F64.add, ffHS,
        hnc', hst']
    · simp only [ffHS, hnc', hnc, hs, Prod.mk.injEq, true_and, hns', hst', ite_true, ite_false, Bool.false_eq_true]
      rw [← hvv']; simp [abs]
  · refine ⟨{ h with time_preempt := h.time_preempt, nested := v }, ?_, ?_⟩
    · simp [beatmap.mods.freeze_frame_loop0.body, hl, hb0, hnc, hsp, hs, hv, hi1, ffHS, hnc', hst']
    · simp only [ffHS, hnc', hnc, hs, Prod.mk.injEq, true_and, hns', hst', ite_true, ite_false, Bool.false_eq_true]
      rw [← hvv']; simp [abs]

theorem mods_ff_outer (pb0 : beatmap.playable.PlayableBeatmap) :
    ∀ (ho : alloc.vec.Vec beatmap.objects.OsuHitObject) (lnc : F64) (i : Usize), i.val ≤ ho.val.length →
    ∃ H : alloc.vec.Vec beatmap.objects.OsuHitObject,
      beatmap.mods.freeze_frame_loop0 { pb0 with hit_objects := ho } lnc i =
        ok (pb0.format_version, pb0.difficulty, pb0.base_difficulty, pb0.stack_leniency, pb0.audio_lead_in,
          pb0.control_points, pb0.breaks, H, pb0.epoch, pb0.mod_states) ∧
      H.val.map abs = (ho.val.map abs).take i.val ++ (((ho.val.map abs).drop i.val).foldl ffHS (lnc, #[])).2.toList := by
  intro ho lnc i
  induction hk : ho.val.length - i.val using Nat.strong_induction_on generalizing ho lnc i with
  | _ k ih =>
    intro hle
    unfold beatmap.mods.freeze_frame_loop0
    rw [loop_unfold]
    by_cases hlt : i.val < ho.val.length
    · obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := ho.property; omega)
      obtain ⟨h1, hb, hst⟩ := mods_ff_obody { pb0 with hit_objects := ho } lnc i i1 hlt hi1
      have hlen : (alloc.vec.Vec.set ho i h1).val.length = ho.val.length := by simp [vec_set_val']
      obtain ⟨H, hH, hHv⟩ := ih ((alloc.vec.Vec.set ho i h1).val.length - i1.val) (by omega) _ _ i1 rfl (by omega)
      refine ⟨H, ?_, ?_⟩
      · simp only [hb, bind_ok]; unfold beatmap.mods.freeze_frame_loop0 at hH; exact hH
      · rw [hHv, hi1v]
        have hd : (ho.val.map abs).drop i.val = (abs (ho.val[i.val]'hlt) : OsuHitObject) :: (ho.val.map abs).drop (i.val + 1) := by
          rw [List.drop_eq_getElem_cons (by simpa using hlt)]; simp
        rw [hd, List.foldl_cons]
        simp only at hst
        rw [hst]
        simp [vec_set_val', List.take_succ, List.drop_set, List.take_set, hlt, List.map_set]
        rw [List.set_eq_of_length_le (by simp), mods_ffh_push _ _ #[abs h1]]; simp
    · have hl' : ¬ i < alloc.vec.Vec.len ho := by show ¬ i.val < (alloc.vec.Vec.len ho).val; simpa using hlt
      refine ⟨ho, by simp [beatmap.mods.freeze_frame_loop0.body, hl'], ?_⟩
      rw [List.drop_eq_nil_of_le (by simp; omega), List.take_of_length_le (by simp; omega)]; simp

/-- `OsuModFreezeFrame.ApplyToBeatmap` -/
theorem beatmap.mods.freeze_frame_refines (pb : beatmap.playable.PlayableBeatmap) :
    ∃ r, beatmap.mods.freeze_frame pb = ok r ∧ Mods.freezeFrame (abs pb) = abs r := by
  obtain ⟨H, hH, hHv⟩ := mods_ff_outer pb pb.hit_objects 0 0#usize (by simp)
  refine ⟨{ pb with hit_objects := H }, ?_, ?_⟩
  · unfold beatmap.mods.freeze_frame
    have hz : float.F64.from_bits 0#u64 = ok (0 : F64) := by simp [float.F64.from_bits]; decide
    simp only [hz, bind_ok]
    rw [show ({ pb with hit_objects := pb.hit_objects } : beatmap.playable.PlayableBeatmap) = pb from rfl] at hH
    rw [hH]; simp only [bind_ok]; rfl
  · rw [mods_ff_spec]
    have : (abs pb : PlayableBeatmap).hitObjects.toList = pb.hit_objects.val.map abs := by simp [abs]
    rw [this]
    have key : (H.val.map abs).toArray = ((pb.hit_objects.val.map abs).foldl ffHS (0, #[])).2 := by
      rw [hHv]; simp
    rw [← key]; rfl

end OsuProofs
