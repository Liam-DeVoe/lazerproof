/-
`beatmap::mod_settings`, part 4: setting constructors (`sBool`, `sInt`, …) and the per-mod setting
tables (`Settings.table`): `table_xx` builds the spec list of mod `XX`.
-/
import OsuProofs.Beatmap.ModSettings3
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap OsuModel.Net.Framework

namespace OsuProofs
open OsuImpl

theorem beatmap.mod_settings.s_bool_refines (key : U32) (d : Bool) :
    ∃ r, beatmap.mod_settings.s_bool key d = ok r ∧ sdS r = Settings.sBool (keyName key.val) d :=
  ⟨_, rfl, rfl⟩

theorem beatmap.mod_settings.s_bool_plain_refines (key : U32) (d : Bool) :
    ∃ r, beatmap.mod_settings.s_bool_plain key d = ok r ∧ sdS r = Settings.sBool (keyName key.val) d false :=
  ⟨_, rfl, rfl⟩

theorem beatmap.mod_settings.s_int_refines (key : U32) (d mn mx : I32) :
    ∃ r, beatmap.mod_settings.s_int key d mn mx = ok r ∧
      sdS r = Settings.sInt (keyName key.val) (i32S d) (i32S mn) (i32S mx) := by
  obtain ⟨i, hi, hiv⟩ := beatmap.mod_settings.set_int_refines mn mx d
  exact ⟨⟨key, .Int mn mx, .Int i⟩, by simp [beatmap.mod_settings.s_int, hi], by simp [sdS, Settings.sInt, styS, svS, hiv]⟩

theorem beatmap.mod_settings.s_double_refines (key : U32) (d mn mx p : F64) :
    ∃ r, beatmap.mod_settings.s_double key d mn mx p = ok r ∧
      sdS r = Settings.sDouble (keyName key.val) d mn mx p :=
  ⟨⟨key, .Double mn mx p, .Double (Settings.initDouble d mn mx p)⟩,
    by simp [beatmap.mod_settings.s_double, beatmap.mod_settings.init_double_refines], rfl⟩

theorem beatmap.mod_settings.s_float_refines (key : U32) (d mn mx p : F32) (pf : Bool) :
    ∃ r, beatmap.mod_settings.s_float key d mn mx p pf = ok r ∧
      sdS r = Settings.sFloat (keyName key.val) d mn mx p pf :=
  ⟨⟨key, .Float mn mx p, .Float (Settings.initFloat d mn mx p pf)⟩,
    by simp [beatmap.mod_settings.s_float, beatmap.mod_settings.init_float_refines], rfl⟩

/-- `s_enum key t d`: an enum setting with member table `t` and default value `d` (the spec writes
`sEnum` for default 0 and the record literal for AD's `style`, default 1). -/
theorem beatmap.mod_settings.s_enum_refines (key t : U32) (d : I32) :
    ∃ r, beatmap.mod_settings.s_enum key t d = ok r ∧
      sdS r = ⟨keyName key.val, .enum (enumTable t.val), .enum (i32S d)⟩ :=
  ⟨_, rfl, rfl⟩

theorem beatmap.mod_settings.s_seed_refines :
    ∃ r, beatmap.mod_settings.s_seed = ok r ∧ sdS r = Settings.sSeed :=
  ⟨_, rfl, by simp [sdS, Settings.sSeed, beatmap.names.K_SEED, keyName, keyNames, styS, svS]⟩

theorem f32_10_bits : float.F32.from_bits 1092616192#u32 = ok (10 : F32) := by
  simp [float.F32.from_bits] <;> decide
theorem f32_11_bits : float.F32.from_bits 1093664768#u32 = ok (11 : F32) := by
  simp [float.F32.from_bits] <;> decide

theorem beatmap.mod_settings.s_diff_refines (key : U32) (emn : Option F32) :
    ∃ r, beatmap.mod_settings.s_diff key emn = ok r ∧ sdS r = Settings.sDiff (keyName key.val) emn :=
  ⟨⟨key, .Difficulty 0 10 emn (some 11), .OptFloat none⟩,
    by simp only [beatmap.mod_settings.s_diff, f32_from_bits_zero, f32_10_bits, f32_11_bits, bind_ok], rfl⟩

/-! ## tables -/

/-- evaluation of a setting table: Rust constructors, spec constructors, then float literals -/
macro "table_tac" : tactic => `(tactic| (
  simp [beatmap.mod_settings.s_double, beatmap.mod_settings.s_bool, beatmap.mod_settings.s_bool_plain,
    beatmap.mod_settings.s_int, beatmap.mod_settings.s_float, beatmap.mod_settings.s_enum,
    beatmap.mod_settings.s_seed, beatmap.mod_settings.s_diff, beatmap.mod_settings.set_int,
    beatmap.mod_settings.init_double_refines, beatmap.mod_settings.init_float_refines,
    beatmap.mod_settings.f32d, float.F32.to_f64,
    alloc.vec.Vec.push, alloc.vec.Vec.new, U32.max_eq]
  simp [alloc.vec.Vec.from, Settings.table, Settings.rateHT, Settings.rateDT, sdS, Settings.sDouble, Settings.sBool, Settings.sInt,
    Settings.sFloat, Settings.sEnum, Settings.sSeed, Settings.sDiff, Settings.f32d, styS, svS, keyName, keyNames,
    enumTable, beatmap.names.K_RETRIES, beatmap.names.K_SPEED_CHANGE, beatmap.names.K_ADJUST_PITCH, beatmap.names.K_FAIL_ON_SLIDER_TAIL, beatmap.names.K_RESTART, beatmap.names.K_ONLY_FADE_APPROACH_CIRCLES, beatmap.names.K_FOLLOW_DELAY, beatmap.names.K_SIZE_MULTIPLIER, beatmap.names.K_COMBO_BASED_SIZE, beatmap.names.K_MINIMUM_ACCURACY, beatmap.names.K_ACCURACY_JUDGE_MODE, beatmap.names.K_SEED, beatmap.names.K_METRONOME, beatmap.names.K_CIRCLE_SIZE, beatmap.names.K_APPROACH_RATE, beatmap.names.K_DRAIN_RATE, beatmap.names.K_OVERALL_DIFFICULTY, beatmap.names.K_EXTENDED_LIMITS, beatmap.names.K_NO_SLIDER_HEAD_ACCURACY, beatmap.names.K_CLASSIC_NOTE_LOCK, beatmap.names.K_ALWAYS_PLAY_TAIL_SAMPLE, beatmap.names.K_FADE_HIT_CIRCLE_EARLY, beatmap.names.K_CLASSIC_HEALTH, beatmap.names.K_ANGLE_SHARPNESS, beatmap.names.K_REFLECTION, beatmap.names.K_STRENGTH, beatmap.names.K_START_SCALE, beatmap.names.K_INITIAL_RATE, beatmap.names.K_FINAL_RATE, beatmap.names.K_SPIN_SPEED, beatmap.names.K_DIRECTION, beatmap.names.K_SCALE, beatmap.names.K_STYLE, beatmap.names.K_INVERSE_MUTING, beatmap.names.K_ENABLE_METRONOME, beatmap.names.K_MUTE_COMBO_COUNT, beatmap.names.K_AFFECTS_HIT_SOUNDS, beatmap.names.K_HIDDEN_COMBO_COUNT, beatmap.names.K_ATTRACTION_STRENGTH, beatmap.names.K_REPULSION_STRENGTH, beatmap.names.K_MAX_DEPTH, beatmap.names.K_SHOW_APPROACH_CIRCLES, beatmap.names.K_MAX_SIZE_COMBO_COUNT, beatmap.names.K_MAX_CURSOR_SIZE, beatmap.names.T_SECTION, beatmap.names.T_EVENT_TYPE, beatmap.names.T_ACCURACY_JUDGE_MODE, beatmap.names.T_REFLECTION, beatmap.names.T_SPIN_DIRECTION, beatmap.names.T_AD_STYLE]
  all_goals (repeat' apply And.intro) <;> first | decide | (congr <;> decide) | rfl))


theorem beatmap.mod_settings.table_ez_refines :
    ∃ r, beatmap.mod_settings.table_ez = ok r ∧ Settings.table "EZ" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_ez
  table_tac

theorem beatmap.mod_settings.table_ht_refines :
    ∃ r, beatmap.mod_settings.table_ht = ok r ∧ Settings.table "HT" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_ht
  table_tac

theorem beatmap.mod_settings.table_dc_refines :
    ∃ r, beatmap.mod_settings.table_dc = ok r ∧ Settings.table "DC" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_dc
  table_tac

theorem beatmap.mod_settings.table_sd_refines :
    ∃ r, beatmap.mod_settings.table_sd = ok r ∧ Settings.table "SD" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_sd
  table_tac

theorem beatmap.mod_settings.table_pf_refines :
    ∃ r, beatmap.mod_settings.table_pf = ok r ∧ Settings.table "PF" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_pf
  table_tac

theorem beatmap.mod_settings.table_dt_refines :
    ∃ r, beatmap.mod_settings.table_dt = ok r ∧ Settings.table "DT" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_dt
  table_tac

theorem beatmap.mod_settings.table_nc_refines :
    ∃ r, beatmap.mod_settings.table_nc = ok r ∧ Settings.table "NC" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_nc
  table_tac

theorem beatmap.mod_settings.table_hd_refines :
    ∃ r, beatmap.mod_settings.table_hd = ok r ∧ Settings.table "HD" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_hd
  table_tac

theorem beatmap.mod_settings.table_fl_refines :
    ∃ r, beatmap.mod_settings.table_fl = ok r ∧ Settings.table "FL" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_fl
  table_tac

theorem beatmap.mod_settings.table_ac_refines :
    ∃ r, beatmap.mod_settings.table_ac = ok r ∧ Settings.table "AC" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_ac
  table_tac

theorem beatmap.mod_settings.table_tp_refines :
    ∃ r, beatmap.mod_settings.table_tp = ok r ∧ Settings.table "TP" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_tp
  table_tac

theorem beatmap.mod_settings.table_da_refines :
    ∃ r, beatmap.mod_settings.table_da = ok r ∧ Settings.table "DA" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_da
  table_tac

theorem beatmap.mod_settings.table_cl_refines :
    ∃ r, beatmap.mod_settings.table_cl = ok r ∧ Settings.table "CL" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_cl
  table_tac

theorem beatmap.mod_settings.table_rd_refines :
    ∃ r, beatmap.mod_settings.table_rd = ok r ∧ Settings.table "RD" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_rd
  table_tac

theorem beatmap.mod_settings.table_mr_refines :
    ∃ r, beatmap.mod_settings.table_mr = ok r ∧ Settings.table "MR" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_mr
  table_tac

theorem beatmap.mod_settings.table_wg_refines :
    ∃ r, beatmap.mod_settings.table_wg = ok r ∧ Settings.table "WG" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_wg
  table_tac

theorem beatmap.mod_settings.table_gr_refines :
    ∃ r, beatmap.mod_settings.table_gr = ok r ∧ Settings.table "GR" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_gr
  table_tac

theorem beatmap.mod_settings.table_df_refines :
    ∃ r, beatmap.mod_settings.table_df = ok r ∧ Settings.table "DF" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_df
  table_tac

theorem beatmap.mod_settings.table_wu_refines :
    ∃ r, beatmap.mod_settings.table_wu = ok r ∧ Settings.table "WU" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_wu
  table_tac

theorem beatmap.mod_settings.table_wd_refines :
    ∃ r, beatmap.mod_settings.table_wd = ok r ∧ Settings.table "WD" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_wd
  table_tac

theorem beatmap.mod_settings.table_br_refines :
    ∃ r, beatmap.mod_settings.table_br = ok r ∧ Settings.table "BR" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_br
  table_tac

theorem beatmap.mod_settings.table_ad_refines :
    ∃ r, beatmap.mod_settings.table_ad = ok r ∧ Settings.table "AD" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_ad
  table_tac

theorem beatmap.mod_settings.table_mu_refines :
    ∃ r, beatmap.mod_settings.table_mu = ok r ∧ Settings.table "MU" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_mu
  table_tac

theorem beatmap.mod_settings.table_ns_refines :
    ∃ r, beatmap.mod_settings.table_ns = ok r ∧ Settings.table "NS" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_ns
  table_tac

theorem beatmap.mod_settings.table_mg_refines :
    ∃ r, beatmap.mod_settings.table_mg = ok r ∧ Settings.table "MG" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_mg
  table_tac

theorem beatmap.mod_settings.table_rp_refines :
    ∃ r, beatmap.mod_settings.table_rp = ok r ∧ Settings.table "RP" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_rp
  table_tac

theorem beatmap.mod_settings.table_as_refines :
    ∃ r, beatmap.mod_settings.table_as = ok r ∧ Settings.table "AS" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_as
  table_tac

theorem beatmap.mod_settings.table_dp_refines :
    ∃ r, beatmap.mod_settings.table_dp = ok r ∧ Settings.table "DP" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_dp
  table_tac

theorem beatmap.mod_settings.table_bm_refines :
    ∃ r, beatmap.mod_settings.table_bm = ok r ∧ Settings.table "BM" = some (r.val.map sdS) := by
  unfold beatmap.mod_settings.table_bm
  table_tac

end OsuProofs
