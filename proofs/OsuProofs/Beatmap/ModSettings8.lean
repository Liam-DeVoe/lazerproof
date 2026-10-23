/-
`beatmap::mod_settings`, part 8: `Bindable<T>.Parse` + setter (`Settings.parse`).
-/
import OsuProofs.Beatmap.ModSettings7
import OsuProofs.Beatmap.DecoderStr
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap OsuModel.Net.Framework

namespace OsuProofs
open OsuImpl

/-- `JOk` plus a length bound for the enum path (`Enum.TryParse` indexes the string with `usize`) -/
def JOk' (j : beatmap.mod_settings.JsonVal) : Prop :=
  JOk j ∧ (match j with | .Str s => s.val.length < Usize.max | _ => True)

theorem ms8_enum_string_ok (j : beatmap.mod_settings.JsonVal) (hj : JOk' j) :
    ∃ r, beatmap.mod_settings.enum_string j = ok r ∧ r.map vstrS = Settings.enumString (jvS j) ∧
      ∀ w, r = some w → VValid w ∧ w.val.length < Usize.max := by
  obtain ⟨r, hr, hrv, hrok⟩ := beatmap.mod_settings.enum_string_refines j hj.1
  refine ⟨r, hr, hrv, fun w hw => ⟨(hrok w hw).1, ?_⟩⟩
  rcases (hrok w hw).2 with h | h
  · have := usize_ge_32; omega
  · have := hj.2; rw [h] at this; exact this

theorem ms8_exceptI_cases {α β} (f : α → β) (e : Except NetExn α) :
    (∃ a, e = .ok a ∧ exceptI f e = .Ok (f a)) ∨ (∃ x, e = .error x ∧ exceptI f e = .Err (exnI x)) := by
  cases e <;> simp [exceptI]

theorem ms8_isnull (j : beatmap.mod_settings.JsonVal) :
    beatmap.mod_settings.is_null_or_empty j =
      ok (match j with | .Null => true | .Str s => decide (vstrS s = "") | _ => false) := by
  rw [beatmap.mod_settings.is_null_or_empty_refines]
  congr 1
  cases j <;> simp only [jvS]
  rename_i s
  by_cases h : vstrS s = ""
  · rw [h]; simp
  · simp only [h, decide_false]; split <;> simp_all

theorem beatmap.mod_settings.parse_refines (t : beatmap.mod_settings.SettingType)
    (old : beatmap.mod_settings.SettingValue) (j : beatmap.mod_settings.JsonVal) (hj : JOk' j) :
    ∃ r, beatmap.mod_settings.parse t old j = ok r ∧ r.map svS = Settings.parse (styS t) (svS old) (jvS j) := by
  cases t with
  | Bool bb =>
    simp only [beatmap.mod_settings.parse, beatmap.mod_settings.to_bool_refines bb j hj.1, bind_ok, Settings.parse, styS]
    rcases ms8_exceptI_cases id (Settings.toBool bb (jvS j)) with ⟨a, he, hx⟩ | ⟨x, he, hx⟩ <;>
      rw [hx, he] <;> exact ⟨_, rfl, rfl⟩
  | Int mn mx =>
    simp only [beatmap.mod_settings.parse, beatmap.mod_settings.to_int32_refines j hj.1, bind_ok, Settings.parse, styS]
    rcases ms8_exceptI_cases i32I (Settings.toInt32 (jvS j)) with ⟨a, he, hx⟩ | ⟨x, he, hx⟩
    · rw [hx, he]
      obtain ⟨i, hi, hiv⟩ := beatmap.mod_settings.set_int_refines mn mx (i32I a)
      refine ⟨some (.Int i), by simp only [hi, bind_ok], ?_⟩
      simp only [Option.map_some, svS, hiv, i32S_i32I]
    · rw [hx, he]; exact ⟨_, rfl, rfl⟩
  | Double mn mx p =>
    simp only [beatmap.mod_settings.parse, beatmap.mod_settings.to_f64_refines j hj.1, Settings.parse, styS]
    rcases ms8_exceptI_cases id (Settings.toF64 (jvS j)) with ⟨a, he, hx⟩ | ⟨x, he, hx⟩ <;>
      cases old <;> simp only [svS, ms_D0, bind_ok, he, exceptI, id, beatmap.mod_settings.set_double_refines]
    all_goals first
      | exact ⟨_, rfl, rfl⟩
      | (split <;> rename_i heq <;> exact ⟨_, rfl, by rw [heq]; rfl⟩)
  | Float mn mx p =>
    simp only [beatmap.mod_settings.parse, beatmap.mod_settings.to_f32_refines j hj.1, Settings.parse, styS]
    rcases ms8_exceptI_cases id (Settings.toF32 (jvS j)) with ⟨a, he, hx⟩ | ⟨x, he, hx⟩ <;>
      cases old <;> simp only [svS, f32_from_bits_zero, bind_ok, he, exceptI, id, beatmap.mod_settings.set_float_refines]
    all_goals first
      | exact ⟨_, rfl, rfl⟩
      | (split <;> rename_i heq <;> exact ⟨_, rfl, by rw [heq]; rfl⟩)
  | Enum t =>
    obtain ⟨r, hr, hrv, hrok⟩ := ms8_enum_string_ok j hj
    simp only [beatmap.mod_settings.parse, hr, bind_ok, Settings.parse, styS, ← hrv]
    cases r with
    | none => exact ⟨none, rfl, rfl⟩
    | some w =>
      obtain ⟨hv, hl⟩ := hrok w rfl
      obtain ⟨q, hq, hqv⟩ := beatmap.dotnet.enum_try_parse_refines t (alloc.vec.Vec.deref w) (vvalid_deref w hv)
        (by rw [ms_deref_val]; exact hl)
      rw [strS_deref, String.ofList_toList] at hqv
      simp only [hq, bind_ok, Option.map_some]
      rw [← hqv]
      cases q <;> exact ⟨_, rfl, rfl⟩
  | NullableInt =>
    simp only [beatmap.mod_settings.parse, ms8_isnull, bind_ok, Settings.parse, styS,
      beatmap.mod_settings.to_int32_refines j hj.1]
    rcases ms8_exceptI_cases i32I (Settings.toInt32 (jvS j)) with ⟨a, he, hx⟩ | ⟨x, he, hx⟩ <;> rw [hx] <;>
      simp only [he] <;>
      cases j <;> simp only [jvS, Bool.false_eq_true, ite_false] <;> first | exact ⟨_, rfl, rfl⟩ | skip
    all_goals rename_i s
    all_goals by_cases h : vstrS s = ""
    all_goals first
      | (simp only [h]; exact ⟨_, rfl, rfl⟩)
      | (simp only [h, decide_false, Bool.false_eq_true, ite_false]
         refine ⟨_, rfl, ?_⟩
         split <;> simp_all <;> rfl)
  | Difficulty mn mx emn emx =>
    simp only [beatmap.mod_settings.parse, ms8_isnull, bind_ok, Settings.parse, styS,
      beatmap.mod_settings.to_f32_refines j hj.1,
      beatmap.mod_settings.set_difficulty_refines]
    rcases ms8_exceptI_cases id (Settings.toF32 (jvS j)) with ⟨a, he, hx⟩ | ⟨x, he, hx⟩ <;> rw [hx] <;>
      simp only [he, id, bind_ok] <;>
      cases j <;> simp only [jvS, Bool.false_eq_true, ite_false] <;> first | exact ⟨_, rfl, rfl⟩ | skip
    all_goals rename_i s
    all_goals by_cases h : vstrS s = ""
    all_goals first
      | (simp only [h]; exact ⟨_, rfl, rfl⟩)
      | (simp only [h, decide_false, Bool.false_eq_true, ite_false]
         refine ⟨_, rfl, ?_⟩
         split <;> simp_all <;> rfl)

end OsuProofs
