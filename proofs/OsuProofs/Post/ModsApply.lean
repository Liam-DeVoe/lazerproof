/-
`beatmap::mods::apply_to_beatmap` (Rust) refines `ModConfig.allHooks`'s `applyToBeatmap` (mods proof agent;
abs-style). The Random / Target Practice generators are taken as hypotheses (`hRD`, `hTP`: their own
refinements, `mod_random.apply` / `mod_target_practice.apply`).
-/
import OsuProofs.Post.ModsAS
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

theorem mapl_kSEED : keyName beatmap.names.K_SEED.val = "seed" := by
  simp [beatmap.names.K_SEED, keyName, keyNames]
theorem mapl_kANG : keyName beatmap.names.K_ANGLE_SHARPNESS.val = "angle_sharpness" := by
  simp [beatmap.names.K_ANGLE_SHARPNESS, keyName, keyNames]

/-- the Hidden loop: `hidden_fade_in` on every hit object -/
theorem mapl_hd_loop (pb : beatmap.playable.PlayableBeatmap) :
    ∃ v, beatmap.mods.apply_to_beatmap_loop pb 0#usize = ok (pb.format_version, pb.difficulty, pb.base_difficulty,
        pb.stack_leniency, pb.audio_lead_in, pb.control_points, pb.breaks, v, pb.epoch, pb.mod_states) ∧
      v.val.map (abs : _ → OsuHitObject) = (pb.hit_objects.val.map abs).map Mods.hiddenFadeIn := by
  obtain ⟨y, hl, hv⟩ := loop_fold_gen' (fun x => beatmap.mods.apply_to_beatmap_loop.body x.1 x.2) (·.2)
    pb.hit_objects.val.length (by have := pb.hit_objects.property; omega)
    (fun x => x.1 = { pb with hit_objects := x.1.hit_objects } ∧ x.1.hit_objects.val.length = pb.hit_objects.val.length)
    (fun x => x.1.hit_objects.val.map (abs : _ → OsuHitObject))
    (fun k L => L.modify k Mods.hiddenFadeIn)
    (fun y L => y = (pb.format_version, pb.difficulty, pb.base_difficulty, pb.stack_leniency, pb.audio_lead_in,
      pb.control_points, pb.breaks, y.2.2.2.2.2.2.2.1, pb.epoch, pb.mod_states) ∧ y.2.2.2.2.2.2.2.1.val.map abs = L)
    (by
      rintro ⟨q, k⟩ ⟨hq, hI⟩ hlt j1 hj1 hj1v
      simp only at hq hI hlt ⊢
      have hl : k.val < q.hit_objects.val.length := by omega
      obtain ⟨o1, ho1, ho1v⟩ := beatmap.mods.hidden_fade_in_refines (q.hit_objects.val[k.val]'hl)
      refine ⟨({ q with hit_objects := alloc.vec.Vec.set q.hit_objects k o1 }, j1), ?_, rfl, ?_, ?_⟩
      · simp [beatmap.mods.apply_to_beatmap_loop.body, vec_lt_len_iff, hl, hj1, vec_index_mut_eq _ _ hl, ho1,
          uncurry_apply_pair]
      · have hm := list_modify_set (q.hit_objects.val.map (abs : _ → OsuHitObject)) k.val (by simpa using hl)
          Mods.hiddenFadeIn
        simp only at hm ⊢
        rw [hm]; simp [vec_set_val', List.map_set, ho1v]
      · exact ⟨by rw [hq], by simp [vec_set_val', hI]⟩)
    (by
      rintro ⟨q, k⟩ ⟨hq, hI⟩ hle
      simp only at hq hI hle ⊢
      have hl : ¬ k < alloc.vec.Vec.len q.hit_objects := by
        show ¬ k.val < (alloc.vec.Vec.len q.hit_objects).val; simp; omega
      refine ⟨(q.format_version, q.difficulty, q.base_difficulty, q.stack_leniency, q.audio_lead_in, q.control_points,
          q.breaks, q.hit_objects, q.epoch, q.mod_states),
        by simp only [beatmap.mods.apply_to_beatmap_loop.body, hl, if_false], ?_, rfl⟩
      rw [hq])
    (pb, 0#usize) ⟨rfl, rfl⟩ (by simp)
  simp only at hl hv
  obtain ⟨hy1, hy2⟩ := hv
  have := iterR_modify_map Mods.hiddenFadeIn (pb.hit_objects.val.map (abs : _ → OsuHitObject))
  simp only [List.length_map] at this
  rw [show (0#usize : Usize).val = 0 from rfl, this] at hy2
  refine ⟨y.2.2.2.2.2.2.2.1, ?_, hy2⟩
  unfold beatmap.mods.apply_to_beatmap_loop
  rw [hl, hy1]

theorem beatmap.mods.apply_to_beatmap_refines (m : beatmap.mod_settings.ModConfig) (hv : AcrOk m)
    (hk : KeysOk m.settings.val) (i : Usize) (pb : beatmap.playable.PlayableBeatmap)
    (hm : pb.mod_states.val.length < Usize.max) (hC : asCnt pb.hit_objects.val < 2^31)
    (hRD : ∀ (s : I32) (f : F32), ∃ e r, beatmap.mod_random.apply s f pb = ok (e, r) ∧
      hRel (fun _ => (abs r : PlayableBeatmap)) e (Mods.RandomMod.apply (i32S s) f (abs pb)))
    (hTP : ∀ (s : I32), ∃ e r, beatmap.mod_target_practice.apply s i pb = ok (e, r) ∧
      hRel (fun _ => (abs r : PlayableBeatmap)) e (Mods.TargetPractice.apply (i32S s) (abs i) (abs pb))) :
    ∃ e r, beatmap.mods.apply_to_beatmap m i pb = ok (e, r) ∧
      hRel (fun _ => (abs r : PlayableBeatmap)) e
        (((mcS m).allHooks.applyToBeatmap.getD (fun _ pb => pure pb)) (abs i) (abs pb)) := by
  unfold beatmap.mods.apply_to_beatmap
  simp only [lift, bind_ok, mods_acr m hv _ _ _ _ se_HD, mods_acr m hv _ _ _ _ se_TC, mods_acr m hv _ _ _ _ se_GR,
    mods_acr m hv _ _ _ _ se_DF, mods_acr m hv _ _ _ _ se_SI, mods_acr m hv _ _ _ _ se_TR, mods_acr m hv _ _ _ _ se_WG,
    mods_acr m hv _ _ _ _ se_DP, mods_acr m hv _ _ _ _ se_FR, mods_acr m hv _ _ _ _ se_WU, mods_acr m hv _ _ _ _ se_WD,
    mods_acr m hv _ _ _ _ se_AS, mods_acr m hv _ _ _ _ se_RD, mods_acr m hv _ _ _ _ se_TP]
  unfold ModConfig.allHooks ModConfig.hooks
  have rfo : ∀ b, ∃ r, beatmap.mods.record_first_object b i pb = ok r ∧
      Mods.recordFirstObject b (abs i) (abs pb) = abs r := fun b => beatmap.mods.record_first_object_refines b i pb hm
  by_cases hkn : m.known = true
  · simp only [hkn, Bool.not_true, Bool.false_eq_true, if_false, Bool.true_and]
    have hmk : (mcS m).known = true := hkn
    simp only [hmk, Bool.not_true, Bool.false_eq_true, if_false]
    have hacr : (mcS m).acronym = vstrS m.acronym := rfl
    rw [hacr]
    generalize hA : vstrS m.acronym = A
    by_cases a_HD : A = "HD"
    · subst a_HD
      obtain ⟨p1, hp1, hp1v⟩ := rfo true
      obtain ⟨v, hl, hlv⟩ := mapl_hd_loop p1
      refine ⟨.Ok (), { p1 with hit_objects := v }, by simp only [decide_true, if_true, hp1, bind_ok, hl,
        uncurry_apply_pair], ?_⟩
      show (abs ({ p1 with hit_objects := v } : beatmap.playable.PlayableBeatmap) : PlayableBeatmap) =
        { Mods.recordFirstObject true (abs i) (abs pb) with hitObjects := (abs pb : PlayableBeatmap).hitObjects.map Mods.hiddenFadeIn }
      have hho : (abs pb : PlayableBeatmap).hitObjects = (p1.hit_objects.val.map (abs : _ → OsuHitObject)).toArray := by
        have := congrArg PlayableBeatmap.hitObjects hp1v
        simp only [Mods.recordFirstObject] at this
        rw [this]; rfl
      have e : (abs ({ p1 with hit_objects := v } : beatmap.playable.PlayableBeatmap) : PlayableBeatmap) =
          { (abs p1 : PlayableBeatmap) with hitObjects := (v.val.map (abs : _ → OsuHitObject)).toArray } := rfl
      rw [e, hlv, hho, hp1v]; simp
    by_cases a_TC : A = "TC"
    · subst a_TC
      obtain ⟨p1, hp1, hp1v⟩ := rfo true
      exact ⟨.Ok (), p1, by simp [hp1], hp1v.symm⟩
    by_cases a_GR : A = "GR"
    · subst a_GR
      obtain ⟨p1, hp1, hp1v⟩ := rfo false
      exact ⟨.Ok (), p1, by simp [hp1], hp1v.symm⟩
    by_cases a_DF : A = "DF"
    · subst a_DF
      obtain ⟨p1, hp1, hp1v⟩ := rfo false
      exact ⟨.Ok (), p1, by simp [hp1], hp1v.symm⟩
    by_cases a_SI : A = "SI"
    · subst a_SI
      obtain ⟨p1, hp1, hp1v⟩ := rfo false
      exact ⟨.Ok (), p1, by simp [hp1], hp1v.symm⟩
    by_cases a_TR : A = "TR"
    · subst a_TR
      obtain ⟨p1, hp1, hp1v⟩ := rfo false
      exact ⟨.Ok (), p1, by simp [hp1], hp1v.symm⟩
    by_cases a_WG : A = "WG"
    · subst a_WG
      obtain ⟨p1, hp1, hp1v⟩ := rfo false
      exact ⟨.Ok (), p1, by simp [hp1], hp1v.symm⟩
    by_cases a_DP : A = "DP"
    · subst a_DP
      obtain ⟨p1, hp1, hp1v⟩ := rfo false
      exact ⟨.Ok (), p1, by simp [hp1], hp1v.symm⟩
    by_cases a_FR : A = "FR"
    · subst a_FR
      obtain ⟨p1, hp1, hp1v⟩ := beatmap.mods.freeze_frame_refines pb
      exact ⟨.Ok (), p1, by simp [hp1], hp1v.symm⟩
    by_cases a_WU : A = "WU"
    · subst a_WU
      obtain ⟨p1, hp1, hp1v⟩ := beatmap.mods.time_ramp_refines i pb hm
      exact ⟨.Ok (), p1, by simp [hp1], hp1v.symm⟩
    by_cases a_WD : A = "WD"
    · subst a_WD
      obtain ⟨p1, hp1, hp1v⟩ := beatmap.mods.time_ramp_refines i pb hm
      exact ⟨.Ok (), p1, by simp [hp1], hp1v.symm⟩
    by_cases a_AS : A = "AS"
    · subst a_AS
      obtain ⟨p1, hp1, hp1v⟩ := beatmap.mods.adaptive_speed_refines i pb hm hC
      exact ⟨.Ok (), p1, by simp [hp1], hp1v.symm⟩
    by_cases a_RD : A = "RD"
    · subst a_RD
      obtain ⟨o, ho, hov⟩ := beatmap.mod_settings.get_opt_int_refines m hk beatmap.names.K_SEED
      rw [mapl_kSEED] at hov
      cases o with
      | none =>
        refine ⟨.Err (.Msg beatmap.errors.M_RANDOM_WITHOUT_A_SEED_IS_NOT_REPRODUCIBL), pb, by simp [ho], ?_⟩
        simp only [Option.map_none] at hov
        show hRel _ _ (match (mcS m).getOptInt "seed" with
          | some s => Mods.RandomMod.apply s ((mcS m).getFloat "angle_sharpness") (abs pb) | none => throw "Random without a seed is not reproducible")
        rw [← hov]; trivial
      | some sd =>
        simp only [Option.map_some] at hov
        obtain ⟨e, r, hr, hrel⟩ := hRD sd ((mcS m).getFloat (keyName beatmap.names.K_ANGLE_SHARPNESS.val))
        refine ⟨e, r, by simp [ho, beatmap.mod_settings.get_float_refines m hk, hr], ?_⟩
        show hRel _ _ (match (mcS m).getOptInt "seed" with
          | some s => Mods.RandomMod.apply s ((mcS m).getFloat "angle_sharpness") (abs pb) | none => throw "Random without a seed is not reproducible")
        rw [← hov]
        rw [mapl_kANG] at hrel; exact hrel
    by_cases a_TP : A = "TP"
    · subst a_TP
      obtain ⟨o, ho, hov⟩ := beatmap.mod_settings.get_opt_int_refines m hk beatmap.names.K_SEED
      rw [mapl_kSEED] at hov
      cases o with
      | none =>
        refine ⟨.Err (.Msg beatmap.errors.M_TARGET_PRACTICE_WITHOUT_A_SEED_IS_NOT_RE), pb, by simp [ho], ?_⟩
        simp only [Option.map_none] at hov
        show hRel _ _ (match (mcS m).getOptInt "seed" with
          | some s => Mods.TargetPractice.apply s (abs i) (abs pb) | none => throw "Target Practice without a seed is not reproducible")
        rw [← hov]; trivial
      | some sd =>
        simp only [Option.map_some] at hov
        obtain ⟨e, r, hr, hrel⟩ := hTP sd
        refine ⟨e, r, by simp [ho, beatmap.mod_settings.get_float_refines m hk, hr], ?_⟩
        show hRel _ _ (match (mcS m).getOptInt "seed" with
          | some s => Mods.TargetPractice.apply s (abs i) (abs pb) | none => throw "Target Practice without a seed is not reproducible")
        rw [← hov]
        exact hrel
    refine ⟨.Ok (), pb, by simp [a_HD, a_TC, a_GR, a_DF, a_SI, a_TR, a_WG, a_DP, a_FR, a_WU, a_WD, a_AS, a_RD, a_TP], ?_⟩
    split
    all_goals first | contradiction | (split <;> first | contradiction | rfl)

  · have : m.known = false := by simpa using hkn
    have hmk : (mcS m).known = false := this
    simp only [this, Bool.false_and, Bool.false_eq_true, if_false, hmk, Bool.not_false, if_true]
    exact ⟨_, _, rfl, rfl⟩

end OsuProofs
