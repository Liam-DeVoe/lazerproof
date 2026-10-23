/-
`beatmap::mod_target_practice` (Rust) refines `OsuModel.Beatmap.Mods.TargetPractice`.
Index loops via `LoopsR.loop_iterR` (template for `any` / `findIdx?` loops).
`OsuProofs/Post/*`: hand proofs that use the generated `Auto/*` lemmas (imported after Auto.Gen,
skipped by gen_steps.py; add their `@[step]` wrappers by hand).
-/
import OsuProofs.Auto.Gen
set_option maxHeartbeats 400000  -- as in the REPL (scripts/Repl.lean)
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

theorem tp_ab (a b : F64) : beatmap.mod_target_practice.almost_bigger a b = ok (Mods.TargetPractice.almostBigger a b) := by
  obtain ⟨r, h, hr⟩ := beatmap.mod_target_practice.almost_bigger_refines a b
  rw [h]; simp only [abs_id] at hr; rw [hr]
theorem tp_db (a b : F64) : beatmap.mod_target_practice.definitely_bigger a b = ok (Mods.TargetPractice.definitelyBigger a b) := by
  obtain ⟨r, h, hr⟩ := beatmap.mod_target_practice.definitely_bigger_refines a b
  rw [h]; simp only [abs_id] at hr; rw [hr]

/-- The inner `find` loop: first object index after the break end. -/
theorem ib_inner (orig : Slice beatmap.objects.OsuHitObject) (b : beatmap.types.BreakPeriod) :
    ∃ r, beatmap.mod_target_practice.inside_break_loop0_loop0 orig b none 0#usize = ok (b, r) ∧
      r.map (·.val) = (orig.val.map (abs : _ → OsuHitObject)).findIdx?
        (fun o => Mods.TargetPractice.almostBigger o.startTime b.end_time) := by
  let L := orig.val.map (abs : _ → OsuHitObject)
  let p := fun o : OsuHitObject => Mods.TargetPractice.almostBigger o.startTime b.end_time
  have hL : L.length = orig.val.length := by simp [L]
  have := loop_iterR (fun (x : Option Usize × Usize) =>
      beatmap.mod_target_practice.inside_break_loop0_loop0.body orig b x.1 x.2)
    (fun j acc => if p L[j]! then .done (some j) else .yield acc) L.length (fun x => x.2.val)
    (fun x s => x.1 = none ∧ s = none ∧ x.2.val ≤ L.length)
    (fun y s => y.1 = b ∧ y.2.map (·.val) = s)
    (by
      rintro ⟨fa, j⟩ s ⟨h1, h2, h3⟩ hj
      simp only at h1 h2 h3 hj ⊢
      subst h1 h2
      have hjl : j.val < orig.val.length := by omega
      have hjl' : j < Slice.len orig := by show j.val < (Slice.len orig).val; simpa using hjl
      obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := orig.property; omega)
      have hget : L[j.val]! = abs (orig.val[j.val]'hjl) := by
        rw [getElem!_pos L j.val (by omega)]; simp [L]
      constructor
      · intro s' hs'
        by_cases hp : p L[j.val]! = true
        · rw [if_pos hp] at hs'; cases hs'
        · rw [if_neg hp] at hs'; cases hs'
          refine ⟨(none, j1), ?_, by simp [hj1v], rfl, rfl, by simp only; omega⟩
          rw [hget] at hp
          simp only [p] at hp
          simp [beatmap.mod_target_practice.inside_break_loop0_loop0.body, hjl', index_eq orig j hjl, tp_ab, hj1,
            show Mods.TargetPractice.almostBigger (orig.val[j.val]'hjl).start_time b.end_time = false by
              simpa [abs] using hp]
      · intro s' hs'
        by_cases hp : p L[j.val]! = true
        · rw [if_pos hp] at hs'; cases hs'
          refine ⟨(b, some j), Or.inr ⟨(some j, j1), ?_, ?_⟩, rfl, rfl⟩
          · rw [hget] at hp
            simp only [p] at hp
            simp [beatmap.mod_target_practice.inside_break_loop0_loop0.body, hjl', index_eq orig j hjl, tp_ab, hj1,
              show Mods.TargetPractice.almostBigger (orig.val[j.val]'hjl).start_time b.end_time = true by
                simpa [abs] using hp]
          · simp [beatmap.mod_target_practice.inside_break_loop0_loop0.body]
        · rw [if_neg hp] at hs'; cases hs')
    (by
      rintro ⟨fa, j⟩ s ⟨h1, h2, h3⟩ hj
      simp only at h1 h2 h3 hj ⊢
      subst h1 h2
      have hjl' : ¬ j < Slice.len orig := by show ¬ j.val < (Slice.len orig).val; simp; omega
      exact ⟨(b, none), by simp [beatmap.mod_target_practice.inside_break_loop0_loop0.body, hjl'], rfl, rfl⟩)
    (none, 0#usize) none ⟨rfl, rfl, by simp⟩ (by simp)
  obtain ⟨⟨b', r⟩, hl, hb, hr⟩ := this
  simp only at hb hr; subst hb
  refine ⟨r, by unfold beatmap.mod_target_practice.inside_break_loop0_loop0; exact hl, ?_⟩
  rw [hr, findIdx_iterR]; simp [L, p]

theorem find?_eq_findIdx? {X : Type} [Inhabited X] (l : List X) (p : X → Bool) :
    l.find? p = (l.findIdx? p).map (fun i => l[i]!) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases h : p a
    · simp [List.findIdx?_cons, h, ih, Option.map_map, Function.comp_def]
    · simp [List.findIdx?_cons, h]

theorem findIdx?_lt {X : Type} (l : List X) (p : X → Bool) (i : Nat) (h : l.findIdx? p = some i) :
    i < l.length := by
  induction l generalizing i with
  | nil => simp at h
  | cons a t ih =>
    cases hp : p a
    · simp [List.findIdx?_cons, hp] at h
      obtain ⟨k, hk, rfl⟩ := h
      simpa using ih k hk
    · simp [List.findIdx?_cons, hp] at h; subst h; simp

/-- The inner loop, with its result as a `find?`. -/
theorem ib_ok2 (orig : Slice beatmap.objects.OsuHitObject) (b : beatmap.types.BreakPeriod) :
    ∃ fa, beatmap.mod_target_practice.inside_break_loop0_loop0 orig b none 0#usize = ok (b, fa) ∧
      ((fa = none ∧ (orig.val.map (abs : _ → OsuHitObject)).find?
          (fun o => Mods.TargetPractice.almostBigger o.startTime b.end_time) = none) ∨
       ∃ o : Usize, ∃ h : o.val < orig.val.length, fa = some o ∧ (orig.val.map (abs : _ → OsuHitObject)).find?
          (fun o => Mods.TargetPractice.almostBigger o.startTime b.end_time) = some (abs (orig.val[o.val]'h))) := by
  obtain ⟨r, hl, hr⟩ := ib_inner orig b
  rw [find?_eq_findIdx?, ← hr]
  cases r with
  | none => exact ⟨none, hl, Or.inl ⟨rfl, rfl⟩⟩
  | some o =>
    have ho : o.val < orig.val.length := by
      have := findIdx?_lt _ _ o.val hr.symm; simpa using this
    refine ⟨some o, hl, Or.inr ⟨o, ho, rfl, ?_⟩⟩
    simp only [Option.map_some]
    rw [getElem!_pos _ _ (by simpa using ho)]; simp

theorem beatmap.mod_target_practice.inside_break_refines (orig : Slice beatmap.objects.OsuHitObject)
    (breaks : Slice beatmap.types.BreakPeriod) (time : F64) :
    ∃ r, beatmap.mod_target_practice.inside_break orig breaks time = ok r ∧
      Mods.TargetPractice.insideBreak (abs orig) (abs breaks) (abs time) = abs r := by
  let B := breaks.val.map (abs : _ → BreakPeriod)
  let pr := fun bp : BreakPeriod =>
    let firstAfter := (orig.val.map (abs : _ → OsuHitObject)).find? fun o => Mods.TargetPractice.almostBigger o.startTime bp.endTime
    Mods.TargetPractice.almostBigger time bp.startTime &&
      (match firstAfter with | none => true | some o => Mods.TargetPractice.definitelyBigger o.startTime time)
  have hspec : Mods.TargetPractice.insideBreak (abs orig) (abs breaks) (abs time) = B.any pr := by
    unfold Mods.TargetPractice.insideBreak
    rw [show (abs breaks : Array BreakPeriod) = B.toArray from rfl, List.any_toArray,
      show (abs orig : Array OsuHitObject) = (orig.val.map abs).toArray from rfl]
    congr 1; funext bp; simp only [pr, List.find?_toArray, abs_id]; rfl
  have := loop_iterR (fun (x : Bool × Usize) =>
      beatmap.mod_target_practice.inside_break_loop0.body orig breaks time x.1 x.2)
    (fun j acc => if pr B[j]! then .done true else .yield acc) B.length (fun x => x.2.val)
    (fun x s => x.1 = false ∧ s = false ∧ x.2.val ≤ B.length)
    (fun y s => y = s)
    (by
      rintro ⟨an, k⟩ s ⟨h1, h2, h3⟩ hk
      simp only at h1 h2 h3 hk ⊢
      subst h1 h2
      have hkl : k.val < breaks.val.length := by simpa [B] using hk
      have hkl' : k < Slice.len breaks := by show k.val < (Slice.len breaks).val; simpa using hkl
      obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := breaks.property; omega)
      have hget : B[k.val]! = abs (breaks.val[k.val]'hkl) := by
        rw [getElem!_pos B k.val (by simpa [B] using hkl)]; simp [B]
      obtain ⟨fa, hin, hfa⟩ := ib_ok2 orig (breaks.val[k.val]'hkl)
      have hbody : beatmap.mod_target_practice.inside_break_loop0.body orig breaks time false k =
          ok (.cont (pr B[k.val]!, k1)) := by
        rw [hget]
        rcases hfa with ⟨rfl, hf⟩ | ⟨o, ho, rfl, hf⟩
        · have hf' : (orig.val.map (abs : _ → OsuHitObject)).find?
              (fun o => Mods.TargetPractice.almostBigger o.startTime (abs (breaks.val[k.val]'hkl) : BreakPeriod).endTime) = none := by
            simpa [abs] using hf
          simp only [pr, hf']
          cases hab : Mods.TargetPractice.almostBigger time (breaks.val[k.val]'hkl).start_time <;>
            simp [beatmap.mod_target_practice.inside_break_loop0.body, hkl', index_eq breaks k hkl, hin,
              tp_ab, hk1, hab, abs]
        · have hf' : (orig.val.map (abs : _ → OsuHitObject)).find?
              (fun o => Mods.TargetPractice.almostBigger o.startTime (abs (breaks.val[k.val]'hkl) : BreakPeriod).endTime) =
              some (abs (orig.val[o.val]'ho)) := by
            simpa [abs] using hf
          simp only [pr, hf']
          cases hab : Mods.TargetPractice.almostBigger time (breaks.val[k.val]'hkl).start_time <;>
          cases hdb : Mods.TargetPractice.definitelyBigger (orig.val[o.val]'ho).start_time time <;>
            simp [beatmap.mod_target_practice.inside_break_loop0.body, hkl', index_eq breaks k hkl, hin,
              index_eq orig o ho, tp_ab, tp_db, hk1, hab, hdb, abs]
      constructor
      · intro s' hs'
        by_cases hp : pr B[k.val]! = true
        · rw [if_pos hp] at hs'; cases hs'
        · rw [if_neg hp] at hs'; cases hs'
          exact ⟨(false, k1), by rw [hbody]; simpa using hp, by simp [hk1v], rfl, rfl, by simp only; omega⟩
      · intro s' hs'
        by_cases hp : pr B[k.val]! = true
        · rw [if_pos hp] at hs'; cases hs'
          exact ⟨true, Or.inr ⟨(true, k1), by rw [hbody, hp],
            by simp [beatmap.mod_target_practice.inside_break_loop0.body]⟩, rfl⟩
        · rw [if_neg hp] at hs'; cases hs')
    (by
      rintro ⟨an, k⟩ s ⟨h1, h2, h3⟩ hk
      simp only at h1 h2 h3 hk ⊢
      subst h1 h2
      have hkl' : ¬ k < Slice.len breaks := by show ¬ k.val < (Slice.len breaks).val; simp [B] at hk; simp; omega
      exact ⟨false, by simp [beatmap.mod_target_practice.inside_break_loop0.body, hkl'], rfl⟩)
    (false, 0#usize) false ⟨rfl, rfl, by simp⟩ (by simp)
  obtain ⟨y, hl, hq⟩ := this
  refine ⟨y, by unfold beatmap.mod_target_practice.inside_break beatmap.mod_target_practice.inside_break_loop0; exact hl, ?_⟩
  rw [hspec, abs_id, hq, any_iterR]; simp

theorem beatmap.mod_random.is_on_beat_refines (cpi : beatmap.control_points.ControlPointInfo)
    (h : beatmap.objects.OsuHitObject) (downbeats_only : Bool) (hn : cpi.timing_points.val.length < 2^31) :
    beatmap.mod_random.is_on_beat cpi h downbeats_only =
      ok (Mods.RandomMod.isOnBeat (cpS cpi) (abs h) downbeats_only) := by
  have hd1 : beatmap.mod_random.D1 = ok (1 : F64) := by
    unfold beatmap.mod_random.D1; simp [float.F64.from_bits] <;> decide
  have hd2 : beatmap.mod_random.D2 = ok (2 : F64) := by
    unfold beatmap.mod_random.D2; simp [float.F64.from_bits] <;> decide
  have hv : ∀ x : Int32, ((i32I x).val : Int) = x.toInt := fun x => by rw [← i32S_toInt, i32S_i32I]
  unfold beatmap.mod_random.is_on_beat Mods.RandomMod.isOnBeat
  rw [beatmap.control_points.timing_point_at_refines cpi h.start_time hn]
  cases downbeats_only <;>
  simp [hd1, hd2, float.F64.sub, float.F64.add, float.F64.abs, float.F64.mul, float.F64.lt, float.F64.from_i64,
    beatmap.dotnet.fmod_f64_refines, lift, abs, tpI, F64.ofInt32, i32S_toInt, i32S_i32I, hv]

theorem beatmap.mods.difficulty_adjust_refines (m : beatmap.mod_settings.ModConfig) (hk : KeysOk m.settings.val)
    (d : beatmap.types.Difficulty) :
    ∃ r, beatmap.mods.difficulty_adjust m d = ok r ∧ Mods.difficultyAdjust (mcS m) (abs d) = abs r := by
  unfold beatmap.mods.difficulty_adjust Mods.difficultyAdjust
  simp only [beatmap.mod_settings.get_opt_float_refines m hk, bind_ok]
  have e1 : keyName beatmap.names.K_DRAIN_RATE.val = "drain_rate" := by simp [beatmap.names.K_DRAIN_RATE, keyName, keyNames]
  have e2 : keyName beatmap.names.K_OVERALL_DIFFICULTY.val = "overall_difficulty" := by
    simp [beatmap.names.K_OVERALL_DIFFICULTY, keyName, keyNames]
  have e3 : keyName beatmap.names.K_CIRCLE_SIZE.val = "circle_size" := by simp [beatmap.names.K_CIRCLE_SIZE, keyName, keyNames]
  have e4 : keyName beatmap.names.K_APPROACH_RATE.val = "approach_rate" := by
    simp [beatmap.names.K_APPROACH_RATE, keyName, keyNames]
  rw [e1, e2, e3, e4]
  cases (mcS m).getOptFloat "drain_rate" <;> cases (mcS m).getOptFloat "overall_difficulty" <;>
  cases (mcS m).getOptFloat "circle_size" <;> cases (mcS m).getOptFloat "approach_rate" <;>
  simp [abs]

@[step] theorem beatmap.mod_target_practice.inside_break_step (orig : Slice beatmap.objects.OsuHitObject)
    (breaks : Slice beatmap.types.BreakPeriod) (time : F64) :
    beatmap.mod_target_practice.inside_break orig breaks time ⦃ r =>
      Mods.TargetPractice.insideBreak (abs orig) (abs breaks) (abs time) = abs r ⦄ :=
  spec_of_ex (beatmap.mod_target_practice.inside_break_refines orig breaks time)

@[step] theorem beatmap.mods.difficulty_adjust_step (m : beatmap.mod_settings.ModConfig) (hk : KeysOk m.settings.val)
    (d : beatmap.types.Difficulty) :
    beatmap.mods.difficulty_adjust m d ⦃ r => Mods.difficultyAdjust (mcS m) (abs d) = abs r ⦄ :=
  spec_of_ex (beatmap.mods.difficulty_adjust_refines m hk d)

end OsuProofs
