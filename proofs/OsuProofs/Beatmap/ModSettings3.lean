/-
`beatmap::mod_settings`, part 3: the setters (`setDouble`, `setFloat`, `initDouble`, `initFloat`,
`setInt`, `setDifficulty`) on top of the `BindableNumber` proofs (`Net/FrameworkB`, `Net/FrameworkC`).
-/
import OsuProofs.Beatmap.ModSettings2
import OsuProofs.Net.FrameworkC
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap OsuModel.Net.Framework

namespace OsuProofs
open OsuImpl

theorem beatmap.mod_settings.set_double_refines (mn mx p old v : F64) :
    beatmap.mod_settings.set_double mn mx p old v = ok (Settings.setDouble mn mx p old v) := by
  unfold beatmap.mod_settings.set_double Settings.setDouble
  obtain ⟨r, hr, hrr⟩ := net.framework.bd_set_value_refines ⟨old, mn, mx, p⟩ v
  rw [hr, bind_ok]
  rcases resRel_cases hrr with ⟨a, b, rfl, he, hab⟩ | ⟨x, rfl, he⟩
  · rw [show bdS ⟨old, mn, mx, p⟩ = { value := old, minV := mn, maxV := mx, prec := p } from rfl] at he
    rw [he, ← hab]; rfl
  · rw [show bdS ⟨old, mn, mx, p⟩ = { value := old, minV := mn, maxV := mx, prec := p } from rfl] at he
    rw [he]

theorem beatmap.mod_settings.set_float_refines (mn mx p old v : F32) :
    beatmap.mod_settings.set_float mn mx p old v = ok (Settings.setFloat mn mx p old v) := by
  unfold beatmap.mod_settings.set_float Settings.setFloat
  obtain ⟨r, hr, hrr⟩ := net.framework.bf_set_value_refines ⟨old, mn, mx, p⟩ v
  rw [hr, bind_ok]
  rcases resRel_cases hrr with ⟨a, b, rfl, he, hab⟩ | ⟨x, rfl, he⟩
  · rw [show bfS ⟨old, mn, mx, p⟩ = { value := old, minV := mn, maxV := mx, prec := p } from rfl] at he
    rw [he, ← hab]; rfl
  · rw [show bfS ⟨old, mn, mx, p⟩ = { value := old, minV := mn, maxV := mx, prec := p } from rfl] at he
    rw [he]

/-- `initDouble`'s `precisionFirst` chain (`create`, `Precision`, `MinValue`, `MaxValue`). -/
theorem beatmap.mod_settings.init_double_pf_refines (d mn mx p : F64) :
    ∃ r, beatmap.mod_settings.init_double_pf d mn mx p = ok r ∧
      resRel bdRel r (do let s ← Bindable.BD.create d; let s ← s.setPrecision p; let s ← s.setMin mn; s.setMax mx) := by
  unfold beatmap.mod_settings.init_double_pf
  obtain ⟨r1, h1, hr1⟩ := net.framework.bd_create_refines d
  rw [h1, bind_ok]
  rcases resRel_cases hr1 with ⟨a, b, rfl, he, hab⟩ | ⟨x, rfl, he⟩
  · rw [he, except_bind_ok, ← show bdS a = b from hab]
    obtain ⟨r2, h2, hr2⟩ := net.framework.bd_set_precision_refines a p
    simp only [h2, bind_ok]
    rcases resRel_cases hr2 with ⟨a2, b2, rfl, he2, hab2⟩ | ⟨x2, rfl, he2⟩
    · rw [he2, except_bind_ok, ← show bdS a2 = b2 from hab2]
      obtain ⟨r3, h3, hr3⟩ := net.framework.bd_set_min_refines a2 mn
      simp only [h3, bind_ok]
      rcases resRel_cases hr3 with ⟨a3, b3, rfl, he3, hab3⟩ | ⟨x3, rfl, he3⟩
      · rw [he3, except_bind_ok, ← show bdS a3 = b3 from hab3]
        exact net.framework.bd_set_max_refines a3 mx
      · exact ⟨_, rfl, by rw [he3]; rfl⟩
    · exact ⟨_, rfl, by rw [he2]; rfl⟩
  · exact ⟨_, rfl, by rw [he]; rfl⟩

theorem beatmap.mod_settings.init_float_pf_refines (d mn mx p : F32) :
    ∃ r, beatmap.mod_settings.init_float_pf d mn mx p = ok r ∧
      resRel bfRel r (do let s ← Bindable.BF.create d; let s ← s.setPrecision p; let s ← s.setMin mn; s.setMax mx) := by
  unfold beatmap.mod_settings.init_float_pf
  obtain ⟨r1, h1, hr1⟩ := net.framework.bf_create_refines d
  rw [h1, bind_ok]
  rcases resRel_cases hr1 with ⟨a, b, rfl, he, hab⟩ | ⟨x, rfl, he⟩
  · rw [he, except_bind_ok, ← show bfS a = b from hab]
    obtain ⟨r2, h2, hr2⟩ := net.framework.bf_set_precision_refines a p
    simp only [h2, bind_ok]
    rcases resRel_cases hr2 with ⟨a2, b2, rfl, he2, hab2⟩ | ⟨x2, rfl, he2⟩
    · rw [he2, except_bind_ok, ← show bfS a2 = b2 from hab2]
      obtain ⟨r3, h3, hr3⟩ := net.framework.bf_set_min_refines a2 mn
      simp only [h3, bind_ok]
      rcases resRel_cases hr3 with ⟨a3, b3, rfl, he3, hab3⟩ | ⟨x3, rfl, he3⟩
      · rw [he3, except_bind_ok, ← show bfS a3 = b3 from hab3]
        exact net.framework.bf_set_max_refines a3 mx
      · exact ⟨_, rfl, by rw [he3]; rfl⟩
    · exact ⟨_, rfl, by rw [he2]; rfl⟩
  · exact ⟨_, rfl, by rw [he]; rfl⟩

theorem beatmap.mod_settings.init_double_refines (d mn mx p : F64) (pf : Bool) :
    beatmap.mod_settings.init_double d mn mx p pf = ok (Settings.initDouble d mn mx p pf) := by
  unfold beatmap.mod_settings.init_double Settings.initDouble
  cases pf
  · obtain ⟨r, hr, hrr⟩ := net.framework.bd_init_refines d mn mx p
    simp only [hr, bind_ok, Bool.false_eq_true, if_false]
    rcases resRel_cases hrr with ⟨a, b, rfl, he, hab⟩ | ⟨x, rfl, he⟩
    · rw [he, ← hab]; rfl
    · rw [he]
  · obtain ⟨r, hr, hrr⟩ := beatmap.mod_settings.init_double_pf_refines d mn mx p
    simp only [hr, bind_ok, if_true]
    rcases resRel_cases hrr with ⟨a, b, rfl, he, hab⟩ | ⟨x, rfl, he⟩
    · rw [he, ← hab]; rfl
    · rw [he]

theorem beatmap.mod_settings.init_float_refines (d mn mx p : F32) (pf : Bool) :
    beatmap.mod_settings.init_float d mn mx p pf = ok (Settings.initFloat d mn mx p pf) := by
  unfold beatmap.mod_settings.init_float Settings.initFloat
  cases pf
  · obtain ⟨r, hr, hrr⟩ := net.framework.bf_init_refines d mn mx p
    simp only [hr, bind_ok, Bool.false_eq_true, if_false]
    rcases resRel_cases hrr with ⟨a, b, rfl, he, hab⟩ | ⟨x, rfl, he⟩
    · rw [he, ← hab]; rfl
    · rw [he]
  · obtain ⟨r, hr, hrr⟩ := beatmap.mod_settings.init_float_pf_refines d mn mx p
    simp only [hr, bind_ok, if_true]
    rcases resRel_cases hrr with ⟨a, b, rfl, he, hab⟩ | ⟨x, rfl, he⟩
    · rw [he, ← hab]; rfl
    · rw [he]

theorem beatmap.mod_settings.set_int_refines (mn mx v : I32) :
    ∃ r, beatmap.mod_settings.set_int mn mx v = ok r ∧ i32S r = Settings.setInt (i32S mn) (i32S mx) (i32S v) := by
  unfold beatmap.mod_settings.set_int Settings.setInt
  by_cases h1 : v < mn
  · have h1' : i32S v < i32S mn := (i32S_lt v mn).mpr h1
    exact ⟨mn, by simp [h1], by simp [h1']⟩
  · have h1' : ¬ i32S v < i32S mn := fun h => h1 ((i32S_lt v mn).mp h)
    by_cases h2 : mx < v
    · have h2' : i32S mx < i32S v := (i32S_lt mx v).mpr h2
      exact ⟨mx, by simp [h1, h2], by simp [h1', h2']⟩
    · have h2' : ¬ i32S mx < i32S v := fun h => h2 ((i32S_lt mx v).mp h)
      exact ⟨v, by simp [h1, h2], by simp [h1', h2']⟩

theorem exceptI_id_ok {α} (X : Except NetExn α) (a : α) : exceptI id X = .Ok a ↔ X = .ok a := by
  cases X <;> simp [exceptI]

theorem exceptI_id_err {α} (X : Except NetExn α) (e : net.basic.NetExn) (h : exceptI id X = .Err e) :
    ∃ e', X = .error e' := by
  cases X <;> simp [exceptI] at h ⊢

theorem beatmap.mod_settings.set_difficulty_refines (mn mx : F32) (emn emx : Option F32) (v : F32) :
    beatmap.mod_settings.set_difficulty mn mx emn emx v = ok (Settings.setDifficulty mn mx emn emx v) := by
  unfold beatmap.mod_settings.set_difficulty Settings.setDifficulty
  have key : ∀ lo hi : F32, (do
      let f ← net.mathops.f32_min mn v
      let cn_min ← net.mathops.f32_clamp f lo mn
      let f1 ← net.mathops.f32_max mx v
      let cn_max ← net.mathops.f32_clamp f1 mx hi
      match cn_min with
        | core.result.Result.Ok a =>
          match cn_max with
          | core.result.Result.Ok b => do
            let r ← net.mathops.f32_clamp v a b
            match r with
              | core.result.Result.Ok r1 => ok r1
              | core.result.Result.Err _ => ok v
          | core.result.Result.Err _ => ok v
        | core.result.Result.Err _ => ok v) =
      ok (match F32.clamp (F32.min mn v) lo mn, F32.clamp (F32.max mx v) mx hi with
        | .ok a, .ok b => match F32.clamp v a b with | .ok r => r | .error _ => v
        | _, _ => v) := by
    intro lo hi
    rw [net.mathops.f32_min_refines, bind_ok, net.mathops.f32_clamp_refines, bind_ok,
      net.mathops.f32_max_refines, bind_ok, net.mathops.f32_clamp_refines, bind_ok]
    cases F32.clamp (F32.min mn v) lo mn <;> cases F32.clamp (F32.max mx v) mx hi <;> simp [exceptI]
    rename_i a b
    rw [net.mathops.f32_clamp_refines]
    cases F32.clamp v a b <;> simp [exceptI]
  cases emn <;> cases emx <;> simp only [bind_ok, Option.getD] <;> exact key _ _

theorem beatmap.mod_settings.is_null_or_empty_refines (j : beatmap.mod_settings.JsonVal) :
    beatmap.mod_settings.is_null_or_empty j =
      ok (match jvS j with | .null => true | .str "" => true | _ => false) := by
  cases j <;> simp [beatmap.mod_settings.is_null_or_empty, jvS]
  rename_i s
  have e : vstrS s = "" ↔ s.val = [] := by
    constructor
    · intro h; have := congrArg String.toList h; simpa [vstrS] using this
    · intro h; simp [vstrS, h]
  by_cases h : s.val = []
  · rw [e.mpr h]; simp [h]; rfl
  · have h' : ¬ vstrS s = "" := fun x => h (e.mp x)
    have hl : s.val.length ≠ 0 := by simpa using h
    rw [decide_eq_false (fun x => hl (by have := congrArg UScalar.val x; simpa using this))]
    split <;> simp_all

end OsuProofs
