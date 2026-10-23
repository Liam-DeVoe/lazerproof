/-
`sim::mods` (Rust) refines `OsuModel.Sim` Mods: score multipliers, rate bindables (`Result<_, NetExn>` against
`Except NetExn`: `exceptI` / `resRel` of the Net proofs), `Config.ofMods` pieces. ModConfig ↦ `mcS` with `KeysOk`
(D26).
-/
import OsuProofs.Sim2.Geometry
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl OsuModel.Beatmap

@[simp] theorem s2_mods_F64_ONE : sim.mods.F64_ONE = ok (1 : F64) := by simp [sim.mods.F64_ONE]
@[simp] theorem s2_mods_F64_0 : sim.mods.F64_0 = ok (0 : F64) := by simp [sim.mods.F64_0]

theorem sim.mods.ht_multiplier_refines (s : F64) :
    sim.mods.ht_multiplier s = ok (OsuModel.Sim.htMultiplier s) := by
  simp [sim.mods.ht_multiplier, OsuModel.Sim.htMultiplier, float.F64.mul, float.F64.to_i32_sat, lift,
    float.F64.from_i64, float.F64.div, float.F64.sub, F64.ofInt32]
  rw [show (20.0 : F64) = 20 by decide +kernel]
attribute [simp] sim.mods.ht_multiplier_refines

set_option maxRecDepth 4000 in
theorem sim.mods.dt_multiplier_refines (s : F64) :
    sim.mods.dt_multiplier s = ok (OsuModel.Sim.dtMultiplier s) := by
  simp [sim.mods.dt_multiplier, OsuModel.Sim.dtMultiplier, float.F64.mul, float.F64.to_i32_sat, lift,
    float.F64.from_i64, float.F64.div, float.F64.sub, float.F64.eq, float.F64.add, F64.ofInt32]
  rw [show (10.0 : F64) = 10 by decide +kernel, show (1.0 : F64) = 1 by decide +kernel, show (0.0 : F64) = 0 by decide +kernel]
  split_ifs <;> simp_all
attribute [simp] sim.mods.dt_multiplier_refines

theorem sim.mods.hd_multiplier_refines (m : beatmap.mod_settings.ModConfig) (hk : KeysOk m.settings.val) (o : Bool) :
    sim.mods.hd_multiplier m o = ok (OsuModel.Sim.hdMultiplier (mcS m) o) := by
  simp [sim.mods.hd_multiplier, OsuModel.Sim.hdMultiplier, beatmap.mod_settings.get_bool_refines m hk, Id.run,
    float.F64.sub, keyName, keyNames, beatmap.names.K_ONLY_FADE_APPROACH_CIRCLES]
  cases (mcS m).getBool "only_fade_approach_circles" <;> cases o <;> rfl

theorem sim.mods.fl_multiplier_refines (m : beatmap.mod_settings.ModConfig) (hk : KeysOk m.settings.val) :
    sim.mods.fl_multiplier m = ok (OsuModel.Sim.flMultiplier (mcS m)) := by
  simp [sim.mods.fl_multiplier, OsuModel.Sim.flMultiplier, beatmap.mod_settings.get_bool_refines m hk,
    beatmap.mod_settings.get_float_refines m hk, keyName, keyNames, beatmap.names.K_SIZE_MULTIPLIER,
    beatmap.names.K_COMBO_BASED_SIZE, sim.mods.F32_ONE, float.F32.sub, float.F32.to_f64, float.F64.mul, float.F64.sub,
    float.F64.add, float.F64.div, net.max_refines, net.min_refines]
  rw [show (1.0 : F32) = 1 by decide +kernel]
  cases (mcS m).getBool "combo_based_size" <;> rfl

theorem sim.mods.df_multiplier_refines (m : beatmap.mod_settings.ModConfig) (hk : KeysOk m.settings.val) :
    sim.mods.df_multiplier m = ok (OsuModel.Sim.dfMultiplier (mcS m)) := by
  simp [sim.mods.df_multiplier, OsuModel.Sim.dfMultiplier, beatmap.mod_settings.get_float_refines m hk, keyName, keyNames,
    beatmap.names.K_START_SCALE, sim.mods.F32_TWO, float.F32.sub, float.F32.to_f64, float.F64.mul, float.F64.sub,
    net.max_refines]
  rw [show (2.0 : F32) = 2 by decide +kernel, show (1.0 : F64) = 1 by decide +kernel]

theorem sim.mods.ez_multiplier_refines (m : beatmap.mod_settings.ModConfig) (hk : KeysOk m.settings.val) :
    sim.mods.ez_multiplier m = ok (OsuModel.Sim.ezMultiplier (mcS m)) := by
  obtain ⟨r, hr, er⟩ := beatmap.mod_settings.get_int_refines m hk beatmap.names.K_RETRIES
  simp only [sim.mods.ez_multiplier, hr, bind_ok]
  simp [OsuModel.Sim.ezMultiplier, keyName, keyNames, beatmap.names.K_RETRIES,
    float.F64.mul, float.F64.sub, float.F64.from_i64, lift, net.max_refines] at er ⊢
  rw [← er, F64.ofInt32, Int32.toInt_sub, i32S_toInt]
  rfl

theorem sim.mods.tr_mult_refines (x : F64) :
    sim.mods.tr_mult x = ok (if x < 1 then OsuModel.Sim.htMultiplier x else OsuModel.Sim.dtMultiplier x) := by
  by_cases h : x < 1 <;> simp [sim.mods.tr_mult, float.F64.lt, h]

theorem sim.mods.tr_multiplier_refines (m : beatmap.mod_settings.ModConfig) (hk : KeysOk m.settings.val) :
    sim.mods.tr_multiplier m = ok (OsuModel.Sim.trMultiplier (mcS m)) := by
  simp [sim.mods.tr_multiplier, OsuModel.Sim.trMultiplier, beatmap.mod_settings.get_double_refines m hk, keyName, keyNames,
    beatmap.names.K_INITIAL_RATE, beatmap.names.K_FINAL_RATE, net.max_refines, net.min_refines, sim.mods.tr_mult_refines,
    float.F64.mul, float.F64.add]

theorem sim.mods.legacy_range_refines (b : Bool) :
    sim.mods.legacy_range b = ok (400 - (if b then 200 else 0)) := by
  cases b <;> simp [sim.mods.legacy_range, float.F64.sub]

theorem sim.mods.pitch_prop_refines (m : beatmap.mod_settings.ModConfig) (hk : KeysOk m.settings.val) :
    ∃ r, sim.mods.pitch_prop m = ok r ∧
      (if (mcS m).getBool "adjust_pitch" then OsuModel.Sim.AudioProp.frequency else .tempo) = abs r := by
  simp [sim.mods.pitch_prop, beatmap.mod_settings.get_bool_refines m hk, keyName, keyNames, beatmap.names.K_ADJUST_PITCH]
  cases (mcS m).getBool "adjust_pitch" <;> simp [abs]

theorem sim.mods.vis_mod_skips_spinners_refines (v : sim.mods.VisMod) :
    sim.mods.vis_mod_skips_spinners v = ok (OsuModel.Sim.VisMod.skipsSpinners (abs v)) := by
  cases v <;> rfl

theorem sim.mods.da_sel_refines (m : beatmap.mod_settings.ModConfig) (hk : KeysOk m.settings.val) (key : U32) (b : F32) :
    sim.mods.da_sel m key b = ok (F32.toF64 (((mcS m).getOptFloat (keyName key.val)).getD b)) := by
  simp only [sim.mods.da_sel, beatmap.mod_settings.get_opt_float_refines m hk, bind_ok]
  cases (mcS m).getOptFloat (keyName key.val) <;> simp [float.F32.to_f64]

theorem sim.mods.da_multiplier_refines (m : beatmap.mod_settings.ModConfig) (hk : KeysOk m.settings.val)
    (base : sim.playable.Difficulty) :
    sim.mods.da_multiplier m base = ok (OsuModel.Sim.daMultiplier (mcS m) (abs base)) := by
  simp [sim.mods.da_multiplier, OsuModel.Sim.daMultiplier, sim.mods.da_sel_refines m hk, keyName, keyNames,
    beatmap.names.K_CIRCLE_SIZE, beatmap.names.K_DRAIN_RATE, beatmap.names.K_OVERALL_DIFFICULTY,
    beatmap.names.K_APPROACH_RATE, float.F32.to_f64, float.F64.sub, float.F64.abs, float.F64.mul, net.max_refines, abs]
  rw [show (1.0 : F64) = 1 by decide +kernel]

theorem sim.mods.time_ramp_bindable_refines :
    ∃ r, sim.mods.time_ramp_bindable = ok r ∧ resRel bdRel r OsuModel.Sim.timeRampBindable := by
  obtain ⟨c, hc, ec⟩ := net.framework.bd_create_refines 1
  unfold sim.mods.time_ramp_bindable OsuModel.Sim.timeRampBindable
  simp only [s2_mods_F64_ONE, hc, bind_ok]
  cases c with
  | Ok v =>
    revert ec; cases hcr : Framework.Bindable.BD.create 1 with
    | error e => intro ec; exact absurd ec (by simp [resRel])
    | ok b =>
      intro ec; simp only [resRel, bdRel] at ec; subst ec
      obtain ⟨p, hp, ep⟩ := net.framework.bd_set_precision_refines v 0.01
      refine ⟨p, by simp [core.result.Result.Insts.CoreOpsTry.branch, hp], ?_⟩
      simpa [Bind.bind, Except.bind] using ep
  | Err e =>
    revert ec; cases hcr : Framework.Bindable.BD.create 1 with
    | ok b => intro ec; exact absurd ec (by simp [resRel])
    | error e' =>
      intro ec
      refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], ?_⟩
      simpa [Bind.bind, Except.bind, resRel] using ec

/-- the error branch of a `?` on `Result<_, NetExn>` -/
theorem s2_try_err {α β γ δ : Type} {R : α → β → Prop} (e : net.basic.NetExn) (sx : Except NetExn β)
    (h : resRel R (.Err e) sx) (ks : β → Except NetExn δ) :
    ∃ e', sx >>= ks = .error e' ∧ exnS e = e' := by
  cases sx with
  | ok b => exact absurd h (by simp [resRel])
  | error e' => exact ⟨e', rfl, by simpa [resRel] using h⟩

theorem sim.mods.adaptive_bindable_refines :
    ∃ r, sim.mods.adaptive_bindable = ok r ∧ resRel bdRel r OsuModel.Sim.adaptiveBindable := by
  obtain ⟨c, hc, ec⟩ := net.framework.bd_create_refines 1
  unfold sim.mods.adaptive_bindable OsuModel.Sim.adaptiveBindable
  simp only [s2_mods_F64_ONE, hc, bind_ok]
  cases c with
  | Err e =>
    revert ec; cases hcr : Framework.Bindable.BD.create 1 with
    | ok b => intro ec; exact absurd ec (by simp [resRel])
    | error e' =>
      intro ec
      refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], ?_⟩
      simpa [Bind.bind, Except.bind, resRel] using ec
  | Ok a =>
    revert ec; cases hcr : Framework.Bindable.BD.create 1 with
    | error e => intro ec; exact absurd ec (by simp [resRel])
    | ok b =>
      intro ec; simp only [resRel, bdRel] at ec; subst ec
      obtain ⟨c2, hc2, ec2⟩ := net.framework.bd_set_min_refines a 0.4
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, fb64_4600877379321698714, hc2]
      simp only [Bind.bind, Except.bind]
      cases c2 with
      | Err e2 =>
        revert ec2; cases hcr2 : (bdS a).setMin 0.4 with
        | ok b => intro ec2; exact absurd ec2 (by simp [resRel])
        | error e' =>
          intro ec2
          refine ⟨.Err e2, by simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], ?_⟩
          simpa [resRel] using ec2
      | Ok a2 =>
        revert ec2; cases hcr2 : (bdS a).setMin 0.4 with
        | error e => intro ec2; exact absurd ec2 (by simp [resRel])
        | ok b2 =>
          intro ec2; simp only [resRel, bdRel] at ec2; subst ec2
          obtain ⟨c3, hc3, ec3⟩ := net.framework.bd_set_max_refines a2 2.5
          exact ⟨c3, by simp [hc3], ec3⟩

theorem sim.mods.time_ramp_rate_refines (i f b ft t : F64) :
    sim.mods.time_ramp_rate i f b ft t = ok (exceptI id (OsuModel.Sim.timeRampRate i f b ft t)) := by
  unfold sim.mods.time_ramp_rate OsuModel.Sim.timeRampRate
  simp only [float.F64.sub, s2_mods_F64_ONE, s2_mods_F64_0, net.max_refines, float.F64.div, bind_ok,
    net.mathops.f64_clamp_refines]
  cases hc : F64.clamp ((t - b) / F64.max 1 (ft - b)) 0 1 with
  | error e => simp [exceptI, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Bind.bind, Except.bind]
  | ok c =>
    simp only [exceptI, id, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, float.F64.mul, float.F64.add,
      net.mathops.f64_round_digits_refines]
    have h2 : (2#i64 : I64).val = 2 := rfl
    rw [h2]
    cases hr : F64.roundDigits (i + (f - i) * c) 2 with
    | error e => simp [exceptI, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        Bind.bind, Except.bind, hr]
    | ok v => simp [exceptI, Bind.bind, Except.bind, pure, Except.pure, hr]

set_option hygiene false in
macro "s2_setspeed_tac" hb:ident sb:term : tactic => `(tactic| (
  obtain ⟨c, hc, ec⟩ := $hb
  simp only [hc, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  revert ec
  cases c with
  | Err e =>
    cases hs : ($sb : Except NetExn Framework.Bindable.BD) with
    | ok b => intro ec; exact absurd ec (by simp [resRel])
    | error e' =>
      intro ec; simp only [resRel] at ec
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, exceptI, Bind.bind,
        Except.bind, ← ec, exnI_S]
  | Ok a =>
    cases hs : ($sb : Except NetExn Framework.Bindable.BD) with
    | error e' => intro ec; exact absurd ec (by simp [resRel])
    | ok b =>
      intro ec; simp only [resRel, bdRel] at ec; subst ec
      obtain ⟨c2, hc2, ec2⟩ := net.framework.bd_set_value_refines { a with value := old } v
      simp only [hc2, bind_ok]
      revert ec2
      cases c2 with
      | Err e2 =>
        cases hs2 : (bdS { a with value := old }).setValue v with
        | ok b => intro ec2; exact absurd ec2 (by simp [resRel])
        | error e' =>
          intro ec2; simp only [resRel] at ec2
          have e3 : (bdS { a with value := old }) = { bdS a with value := old } := rfl
          rw [e3] at hs2; dsimp only [bdS] at hs2
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, exceptI, Bind.bind,
            Except.bind, bdS, hs2, ← ec2, exnI_S]
      | Ok a2 =>
        cases hs2 : (bdS { a with value := old }).setValue v with
        | error e' => intro ec2; exact absurd ec2 (by simp [resRel])
        | ok b2 =>
          intro ec2; simp only [resRel, bdRel] at ec2; subst ec2
          have e3 : (bdS { a with value := old }) = { bdS a with value := old } := rfl
          rw [e3] at hs2; dsimp only [bdS] at hs2
          simp [exceptI, Bind.bind, Except.bind, hs2, pure, Except.pure, bdS]))

theorem sim.mods.dyn_rate_set_speed_refines (d : sim.mods.DynRate) (old v : F64) :
    sim.mods.dyn_rate_set_speed d old v = ok (exceptI id (OsuModel.Sim.DynRate.setSpeed (abs d) old v)) := by
  cases d with
  | TimeRamp a b c e =>
    simp only [sim.mods.dyn_rate_set_speed, OsuModel.Sim.DynRate.setSpeed, abs]
    s2_setspeed_tac sim.mods.time_ramp_bindable_refines OsuModel.Sim.timeRampBindable
  | Adaptive a =>
    simp only [sim.mods.dyn_rate_set_speed, OsuModel.Sim.DynRate.setSpeed, abs]
    s2_setspeed_tac sim.mods.adaptive_bindable_refines OsuModel.Sim.adaptiveBindable

theorem sim.mods.dyn_rate_initial_speed_refines (d : sim.mods.DynRate) :
    sim.mods.dyn_rate_initial_speed d = ok (exceptI id (OsuModel.Sim.DynRate.initialSpeed (abs d))) := by
  cases d with
  | TimeRamp i f b ft =>
    simp only [sim.mods.dyn_rate_initial_speed, netx_F64_POS_INF, bind_ok, sim.mods.time_ramp_rate_refines]
    have ea : (abs (sim.mods.DynRate.TimeRamp i f b ft) : OsuModel.Sim.DynRate) = .timeRamp i f b ft := rfl
    rw [ea]
    unfold OsuModel.Sim.DynRate.initialSpeed
    cases hr : OsuModel.Sim.timeRampRate i f b ft F64.posInf with
    | error e => simp [exceptI, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Bind.bind, Except.bind, hr]
    | ok r =>
      simp only [exceptI, id, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, s2_mods_F64_ONE,
        sim.mods.dyn_rate_set_speed_refines]
      simp [Bind.bind, Except.bind, ea, hr]
  | Adaptive i =>
    simp [sim.mods.dyn_rate_initial_speed, sim.mods.dyn_rate_set_speed_refines, OsuModel.Sim.DynRate.initialSpeed, abs]

/-- the acronym holds Unicode scalar values (= `AcrOk` of Post/ModsB) -/
def s2_AcrOk (m : beatmap.mod_settings.ModConfig) : Prop := ValidStr (alloc.vec.Vec.deref m.acronym)

theorem s2_acr (m : beatmap.mod_settings.ModConfig) (hv : s2_AcrOk m) (a b : U8) (p) (s : String)
    (hs : ∀ acr : Slice U32, ValidStr acr → ∀ p, beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [a, b] p)) =
      ok (decide (String.ofList (strS acr) = s))) :
    sim.mods.acr_is m (Array.to_slice (Array.make 2#usize [a, b] p)) = ok (decide ((mcS m).acronym = s)) := by
  unfold sim.mods.acr_is
  rw [hs _ hv]; simp [mcS, vstrS, strS, alloc.vec.Vec.deref]
  first | rfl | (congr 1)

theorem sim.mods.acr_is_refines (m : beatmap.mod_settings.ModConfig) (hv : s2_AcrOk m) (lit : Slice U8) :
    sim.mods.acr_is m lit = ok (decide (strS (alloc.vec.Vec.deref m.acronym) = litS lit)) := by
  unfold sim.mods.acr_is; exact beatmap.dotnet.str_eq_refines _ hv lit

@[simp] theorem s2_kn_speed : keyName beatmap.names.K_SPEED_CHANGE.val = "speed_change" := by simp [keyName, keyNames, beatmap.names.K_SPEED_CHANGE]
@[simp] theorem s2_kn_cnl : keyName beatmap.names.K_CLASSIC_NOTE_LOCK.val = "classic_note_lock" := by
  simp [keyName, keyNames, beatmap.names.K_CLASSIC_NOTE_LOCK]
@[simp] theorem s2_kn_attr : keyName beatmap.names.K_ATTRACTION_STRENGTH.val = "attraction_strength" := by
  simp [keyName, keyNames, beatmap.names.K_ATTRACTION_STRENGTH]

theorem s2_ite_ok {α : Type} {c : Prop} [Decidable c] (a b : Result α) (x y : α) (ha : a = ok x) (hb : b = ok y) :
    (if c then a else b) = ok (if c then x else y) := by
  split <;> assumption

theorem sim.mods.single_multiplier_refines (m : beatmap.mod_settings.ModConfig) (hk : KeysOk m.settings.val) (hv : s2_AcrOk m)
    (base : sim.playable.Difficulty) :
    sim.mods.single_multiplier m base = ok (OsuModel.Sim.singleMultiplier (mcS m) (abs base)) := by
  unfold sim.mods.single_multiplier
  simp only [lift, bind_ok, s2_acr m hv _ _ _ _ se_EZ, s2_acr m hv _ _ _ _ se_NF, s2_acr m hv _ _ _ _ se_HT,
    s2_acr m hv _ _ _ _ se_DC, s2_acr m hv _ _ _ _ se_HR, s2_acr m hv _ _ _ _ se_DT, s2_acr m hv _ _ _ _ se_NC,
    s2_acr m hv _ _ _ _ se_HD, s2_acr m hv _ _ _ _ se_TC, s2_acr m hv _ _ _ _ se_FL, s2_acr m hv _ _ _ _ se_BL,
    s2_acr m hv _ _ _ _ se_TP, s2_acr m hv _ _ _ _ se_DA, s2_acr m hv _ _ _ _ se_CL, s2_acr m hv _ _ _ _ se_RD,
    s2_acr m hv _ _ _ _ se_RX, s2_acr m hv _ _ _ _ se_AP, s2_acr m hv _ _ _ _ se_SO, s2_acr m hv _ _ _ _ se_DF,
    s2_acr m hv _ _ _ _ se_WU, s2_acr m hv _ _ _ _ se_WD, s2_acr m hv _ _ _ _ se_AD, s2_acr m hv _ _ _ _ se_MG,
    s2_acr m hv _ _ _ _ se_AS, s2_acr m hv _ _ _ _ se_SY]
  simp only [sim.mods.ez_multiplier_refines m hk, sim.mods.hd_multiplier_refines m hk, sim.mods.fl_multiplier_refines m hk,
    sim.mods.da_multiplier_refines m hk, sim.mods.df_multiplier_refines m hk, sim.mods.tr_multiplier_refines m hk,
    beatmap.mod_settings.get_double_refines m hk, beatmap.mod_settings.get_float_refines m hk,
    beatmap.mod_settings.get_bool_refines m hk, sim.mods.ht_multiplier_refines, sim.mods.dt_multiplier_refines,
    bind_ok, float.F32.to_f64, float.F64.mul, float.F64.sub]
  simp only [s2_kn_speed, s2_kn_cnl, s2_kn_attr]
  unfold OsuModel.Sim.singleMultiplier
  generalize (mcS m).acronym = A
  unfold OsuModel.Sim.singleMultiplier.match_1
  simp only [decide_eq_true_eq, Eq.ndrec_symm, Eq.ndrec, eq_rec_constant, dite_eq_ite]
  repeat (refine s2_ite_ok _ _ _ _ (by first | rfl | (split <;> rfl) | (simp; done) | (split <;> simp_all; done) |
    (simp; rw [show Float.ofBits 4603579539098121011 = (0.6 : F64) by decide +kernel])) ?_)
  rfl

theorem sim.mods.combo_multiplier_refines (k : Usize) (ma mb : beatmap.mod_settings.ModConfig)
    (ha : KeysOk ma.settings.val) (hb : KeysOk mb.settings.val) (hk : k.val < 8) :
    sim.mods.combo_multiplier k ma mb =
      ok ((OsuModel.Sim.combinations.getD k.val ("", "", fun _ _ => 0)).2.2 (mcS ma) (mcS mb)) := by
  have : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 ∨ k.val = 4 ∨ k.val = 5 ∨ k.val = 6 ∨ k.val = 7 := by omega
  rcases this with h | h | h | h | h | h | h | h <;>
  · simp [sim.mods.combo_multiplier, h, OsuModel.Sim.combinations, sim.mods.hd_multiplier_refines ma ha,
      sim.mods.df_multiplier_refines mb hb, sim.mods.fl_multiplier_refines ma ha, float.F64.mul, float.F64.add,
      float.F64.sub, float.F64.div, UScalar.eq_equiv]
    try (first | rfl | (rw [show (2.0 : F64) = 2 by decide +kernel]))

/-- the `while i < len && r.is_none() { if p(l[i]) { r = Some(i) } i += 1 }` search loops -/
theorem s2_find_loop {X : Type} (l : Slice X) (P : X → Bool)
    (body : Usize × Option Usize → Result (ControlFlow (Usize × Option Usize) (Option Usize)))
    (hstep : ∀ (i : Usize) (h : i.val < l.val.length), ∃ i1 : Usize, i1.val = i.val + 1 ∧
      body (i, none) = ok (.cont (i1, if P (l.val[i.val]'h) then some i else none)))
    (hsome : ∀ (i j : Usize), body (i, some j) = ok (.done (some j)))
    (hend : ∀ (i : Usize) r, l.val.length ≤ i.val → body (i, r) = ok (.done r)) :
    ∀ (n : Nat) (i : Usize), l.val.length - i.val = n → i.val ≤ l.val.length →
      ∃ r, loop body (i, none) = ok r ∧ r.map (·.val) = ((l.val.drop i.val).findIdx? P).map (· + i.val) := by
  intro n
  induction n with
  | zero =>
    intro i hn hi
    refine ⟨none, by rw [loop_unfold, hend i none (by omega)]; simp, ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]; simp
  | succ n ih =>
    intro i hn hi
    have hlt : i.val < l.val.length := by omega
    obtain ⟨i1, hi1, hb⟩ := hstep i hlt
    rw [List.drop_eq_getElem_cons hlt, List.findIdx?_cons]
    by_cases hp : P (l.val[i.val]'hlt) = true
    · refine ⟨some i, ?_, by simp [hp]⟩
      rw [loop_unfold, hb]; simp only [hp, ite_true, bind_ok]
      rw [loop_unfold, hsome i1 i]; simp
    · obtain ⟨r, hr, er⟩ := ih i1 (by omega) (by omega)
      refine ⟨r, ?_, ?_⟩
      · rw [loop_unfold, hb]; simp only [hp, Bool.false_eq_true, ite_false, bind_ok]; exact hr
      · rw [er, hi1]; simp [hp]
        cases (List.drop (i.val + 1) l.val).findIdx? P <;> simp; omega

theorem sim.mods.find_by_lit_refines (by_type : Slice beatmap.mod_settings.ModConfig) (a : Slice U8)
    (hv : ∀ m ∈ by_type.val, s2_AcrOk m) :
    ∃ r, sim.mods.find_by_lit by_type a = ok r ∧
      r.map (·.val) = by_type.val.findIdx? (fun m => decide (strS (alloc.vec.Vec.deref m.acronym) = litS a)) := by
  obtain ⟨r, hr, er⟩ := s2_find_loop by_type (fun m => decide (strS (alloc.vec.Vec.deref m.acronym) = litS a))
    (fun x => sim.mods.find_by_lit_loop.body by_type a x.1 x.2)
    (by intro i h
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := by_type.property; omega)
        refine ⟨i1, hi1v, ?_⟩
        have hv' := hv _ (List.getElem_mem h)
        simp [sim.mods.find_by_lit_loop.body, slice_lt_len_iff, h, slice_index_ok _ _ h,
          sim.mods.acr_is_refines _ hv', hi1])
    (by intro i j; simp [sim.mods.find_by_lit_loop.body])
    (by intro i r h; simp [sim.mods.find_by_lit_loop.body, slice_lt_len_iff, Nat.not_lt.mpr h])
    by_type.val.length 0#usize (by simp) (by simp)
  refine ⟨r, by unfold sim.mods.find_by_lit sim.mods.find_by_lit_loop; exact hr, ?_⟩
  rw [er]; simp

theorem sim.mods.acr_eq_refines (m : beatmap.mod_settings.ModConfig) (a : Slice U32) :
    sim.mods.acr_eq m a = ok (decide (m.acronym.val = a.val)) := by
  simp [sim.mods.acr_eq, beatmap.dotnet.str_eq2_refines, alloc.vec.Vec.deref]

theorem sim.mods.find_by_acr_refines (by_type : Slice beatmap.mod_settings.ModConfig) (a : Slice U32) :
    ∃ r, sim.mods.find_by_acr by_type a = ok r ∧
      r.map (·.val) = by_type.val.findIdx? (fun m => decide (m.acronym.val = a.val)) := by
  obtain ⟨r, hr, er⟩ := s2_find_loop by_type (fun m => decide (m.acronym.val = a.val))
    (fun x => sim.mods.find_by_acr_loop.body by_type a x.1 x.2)
    (by intro i h
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := by_type.property; omega)
        refine ⟨i1, hi1v, ?_⟩
        simp [sim.mods.find_by_acr_loop.body, slice_lt_len_iff, h, slice_index_ok _ _ h,
          sim.mods.acr_eq_refines, hi1])
    (by intro i j; simp [sim.mods.find_by_acr_loop.body])
    (by intro i r h; simp [sim.mods.find_by_acr_loop.body, slice_lt_len_iff, Nat.not_lt.mpr h])
    by_type.val.length 0#usize (by simp) (by simp)
  refine ⟨r, by unfold sim.mods.find_by_acr sim.mods.find_by_acr_loop; exact hr, ?_⟩
  rw [er]; simp

theorem sim.mods.by_type_has_refines (by_type : Slice beatmap.mod_settings.ModConfig) (m : beatmap.mod_settings.ModConfig) :
    sim.mods.by_type_has by_type m = ok (by_type.val.any (fun x => decide (x.acronym.val = m.acronym.val))) := by
  obtain ⟨r, hr, er⟩ := sim.mods.find_by_acr_refines by_type (alloc.vec.Vec.deref m.acronym)
  simp only [sim.mods.by_type_has, hr, bind_ok]
  congr 1
  have : r.isSome = (by_type.val.findIdx? (fun x => decide (x.acronym.val = (alloc.vec.Vec.deref m.acronym).val))).isSome := by
    rw [← er]; cases r <;> rfl
  simp only [core.option.Option.is_some]
  rw [this, List.findIdx?_isSome]; simp [alloc.vec.Vec.deref]

theorem sim.mods.rem_contains_refines (rem : Slice Bool) (by_type : Slice beatmap.mod_settings.ModConfig) (a : Slice U8)
    (hv : ∀ m ∈ by_type.val, s2_AcrOk m) (hl : rem.val.length = by_type.val.length) :
    sim.mods.rem_contains rem by_type a =
      ok (match by_type.val.findIdx? (fun m => decide (strS (alloc.vec.Vec.deref m.acronym) = litS a)) with
          | some i => rem.val.getD i false
          | none => false) := by
  obtain ⟨r, hr, er⟩ := sim.mods.find_by_lit_refines by_type a hv
  simp only [sim.mods.rem_contains, hr, bind_ok]
  rw [← er]
  cases r with
  | none => rfl
  | some i =>
    have hi : i.val < by_type.val.length := by
      exact (List.findIdx?_eq_some_iff_findIdx_eq.mp er.symm).1
    simp [slice_index_ok _ _ (by omega : i.val < rem.val.length), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i.val < rem.val.length)]

@[simp] theorem s2_audio_eq (a b : sim.mods.AudioProp) :
    sim.mods.AudioProp.Insts.CoreCmpPartialEqAudioProp.eq a b =
      ok ((abs a : OsuModel.Sim.AudioProp) == abs b) := by
  cases a <;> cases b <;> simp [sim.mods.AudioProp.Insts.CoreCmpPartialEqAudioProp.eq, read_discriminant,
    sim.mods.AudioProp.read_discriminant, abs] <;> decide

/-- value of a rate source given the dynamic speeds -/
def s2_rvS (speed : List F64) : OsuModel.Sim.RateVal → F64
  | .const x => x
  | .dyn k => speed.getD k 0

def s2_aggStep (p : OsuModel.Sim.AudioProp) (speed : List F64) (acc : F64) (s : OsuModel.Sim.AudioProp × OsuModel.Sim.RateVal) : F64 :=
  if (s.1 == p) = true then acc * s2_rvS speed s.2 else acc

theorem s2_filter_map_prod (p : OsuModel.Sim.AudioProp) (speed : List F64) :
    ∀ (l : List (OsuModel.Sim.AudioProp × OsuModel.Sim.RateVal)) (a : F64),
      ((l.filter (·.1 == p)).map (fun s => s2_rvS speed s.2)).foldl (· * ·) a = l.foldl (s2_aggStep p speed) a := by
  intro l
  induction l with
  | nil => intro a; rfl
  | cons s t ih =>
    intro a
    by_cases h : (s.1 == p) = true
    · simp [List.filter_cons, h, s2_aggStep, ih]
    · simp [List.filter_cons, h, s2_aggStep, ih]

theorem sim.mods.aggregate_refines (c : sim.mods.Config) (speed : Slice F64) (prop : sim.mods.AudioProp)
    (hd : ∀ s ∈ c.rate_sources.val, ∀ k, s.val = .Dyn k → k.val < speed.val.length) :
    sim.mods.aggregate c speed prop =
      ok (OsuModel.Sim.aggregate ((((abs c : OsuModel.Sim.Config).rateSources.toList).filter (·.1 == abs prop)).map
        (fun s => s2_rvS speed.val s.2))) := by
  have hmax := c.rate_sources.property
  let L : List (OsuModel.Sim.AudioProp × OsuModel.Sim.RateVal) := c.rate_sources.val.map (fun s => abs s)
  obtain ⟨y, hl, hv⟩ := loop_fold_gen' (fun x => sim.mods.aggregate_loop.body c speed prop x.1 x.2) (·.2)
    c.rate_sources.val.length (by omega)
    (fun _ => True) (fun t => t.1) (fun k a => s2_aggStep (abs prop) speed.val a (L[k]!)) (fun y a => y = a)
    (by
      intro t _ hlt j1 hj1 hj1v
      obtain ⟨acc, i⟩ := t
      simp only at hlt hj1 hj1v ⊢
      have hi : i.val < c.rate_sources.val.length := hlt
      refine ⟨(s2_aggStep (abs prop) speed.val acc (L[i.val]!), j1), ?_, rfl, rfl, trivial⟩
      have hL : L[i.val]! = abs (c.rate_sources.val[i.val]'hi) := by
        rw [getElem!_pos L i.val (by simp [L]; exact hi)]; simp [L]
      rw [hL]
      have hmem := List.getElem_mem hi
      have hsrc : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.mods.RateSource) c.rate_sources i =
          ok (c.rate_sources.val[i.val]'hi) := by simp [vec_index_usize_ok _ _ hi]
      rcases hs : c.rate_sources.val[i.val]'hi with ⟨sp, sv⟩
      rw [hs] at hsrc hmem
      cases sv with
      | Const x =>
        cases hb : ((abs sp : OsuModel.Sim.AudioProp) == abs prop) <;>
          simp [sim.mods.aggregate_loop.body, vec_lt_len_iff, hi, hsrc, hj1, hb, s2_aggStep, abs, s2_rvS, float.F64.mul]
      | Dyn k =>
        have hk := hd _ hmem k rfl
        cases hb : ((abs sp : OsuModel.Sim.AudioProp) == abs prop) <;>
          simp [sim.mods.aggregate_loop.body, vec_lt_len_iff, hi, hsrc, hj1, hb, s2_aggStep, abs, s2_rvS, float.F64.mul,
            slice_index_ok _ _ hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk])
    (by
      intro t _ hge
      obtain ⟨acc, i⟩ := t
      refine ⟨acc, ?_, rfl⟩
      simp [sim.mods.aggregate_loop.body, vec_lt_len_iff, Nat.not_lt.mpr hge])
    (1 * 1, 0#usize) trivial (by simp)
  unfold sim.mods.aggregate
  simp only [s2_mods_F64_ONE, float.F64.mul, bind_ok]
  unfold sim.mods.aggregate_loop
  rw [hl, hv]
  unfold OsuModel.Sim.aggregate
  rw [s2_filter_map_prod, foldl_iterR]
  have eL : ((abs c : OsuModel.Sim.Config).rateSources.toList) = L := by simp [abs, configS, L]
  rw [eL]; simp [L]

theorem s2_mapM_val (speed : _root_.Array F64) (val : OsuModel.Sim.AudioProp × OsuModel.Sim.RateVal → Except String F64)
    (hval : ∀ v, (∀ k, v.2 = .dyn k → k < speed.size) → val v = .ok (s2_rvS speed.toList v.2)) :
    ∀ (l : List (OsuModel.Sim.AudioProp × OsuModel.Sim.RateVal)), (∀ s ∈ l, ∀ k, s.2 = .dyn k → k < speed.size) →
      l.mapM val = .ok (l.map (fun s => s2_rvS speed.toList s.2)) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons s t ih =>
    intro h
    rw [List.mapM_cons, hval s (h s (by simp)), ih (fun s' hs => h s' (by simp [hs]))]
    rfl

theorem sim.mods.true_rate_refines (c : sim.mods.Config) (speed : Slice F64)
    (hd : ∀ s ∈ c.rate_sources.val, ∀ k, s.val = .Dyn k → k.val < speed.val.length) :
    ∃ r, sim.mods.true_rate c speed = ok r ∧
      OsuModel.Sim.Config.trueRate (abs c) (abs speed) = .ok r := by
  refine ⟨_, by simp only [sim.mods.true_rate, sim.mods.aggregate_refines c speed _ hd, s2_mods_F64_ONE, bind_ok,
    float.F64.mul]; rfl, ?_⟩
  unfold OsuModel.Sim.Config.trueRate
  dsimp only
  have hS : (abs speed : _root_.Array F64).toList = speed.val := by simp [abs]
  have hl : ∀ s ∈ (abs c : OsuModel.Sim.Config).rateSources.toList, ∀ k, s.2 = .dyn k → k < (abs speed : _root_.Array F64).size := by
    intro s hs k hk
    simp [abs, configS] at hs
    obtain ⟨s0, hs0, rfl⟩ := hs
    rcases s0 with ⟨p0, v0⟩
    cases v0 with
    | Const x => simp [abs] at hk
    | Dyn k0 => simp [abs] at hk; subst hk; simpa [abs] using hd _ hs0 k0 rfl
  rw [s2_mapM_val _ _ ?hv _ (fun s hs k hk => hl s (List.mem_of_mem_filter hs) k hk),
    s2_mapM_val _ _ ?hv _ (fun s hs k hk => hl s (List.mem_of_mem_filter hs) k hk)]
  · simp [Bind.bind, Except.bind, pure, Except.pure, hS, abs]
  case hv =>
    intro v hv
    obtain ⟨p, v⟩ := v
    cases v with
    | const x => rfl
    | dyn k =>
      have := hv k rfl
      simp [List.getD_eq_getElem?_getD, s2_rvS, this, pure, Except.pure]

def s2_lmStep (x : F64) (s : Option F64 × F64) : ForInStep (Option F64 × F64) :=
  if s.2 < x then .yield (none, x) else if x.isNaN = true then .done (some x, s.2) else .yield (none, s.2)

theorem sim.mods.linq_max_refines (xs : Slice F64) (h : 0 < xs.val.length) :
    sim.mods.linq_max xs = ok ((OsuModel.Sim.linqMax (abs xs)).getD 0) := by
  have hmax := xs.property
  have hA : (abs xs : _root_.Array F64) = xs.val.toArray := by simp [abs]
  have h0 : (0#usize).val < xs.val.length := by simpa using h
  by_cases hnan : (xs.val[0]).isNaN = true
  · have hb : sim.mods.linq_max_loop.body xs (xs.val[0]) true 1#usize = ok (.done (xs.val[0])) := by
      simp [sim.mods.linq_max_loop.body]
    unfold sim.mods.linq_max OsuModel.Sim.linqMax
    simp only [slice_index_ok _ _ h0, float.F64.is_nan, bind_ok, hA, List.size_toArray, h, _root_.dite_true]
    simp only [show (0#usize : Usize).val = 0 from rfl, hnan]
    unfold sim.mods.linq_max_loop; rw [loop_unfold]; simp [hb, Id.run, List.getElem_toArray]
    rw [if_pos hnan]; rfl
  let L := xs.val.drop 1
  obtain ⟨y, hl, hv⟩ := loop_iterR (fun t => sim.mods.linq_max_loop.body xs t.1 t.2.1 t.2.2)
    (fun j s => s2_lmStep (L[j]!) s) L.length (fun t => t.2.2.val - 1)
    (fun t s => t.1 = s.2 ∧ t.2.1 = false ∧ 1 ≤ t.2.2.val ∧ t.2.2.val ≤ xs.val.length ∧ s.1 = none)
    (fun y s => y = match s.1 with | some r => r | none => s.2)
    (by
      intro t s hR hlt
      obtain ⟨v, d, i⟩ := t
      obtain ⟨h1, h2, h3, h4, h5⟩ := hR
      simp only at h1 h2 h3 h4 h5 hlt ⊢; subst h1 h2
      have hi : i.val < xs.val.length := by simp [L] at hlt; omega
      have hLi : L[i.val - 1]! = xs.val[i.val]'hi := by
        rw [getElem!_pos L _ (by simp [L]; omega)]; simp [L]; congr 1; omega
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
      have hlt' : i < Slice.len xs := by rw [slice_lt_len_iff]; exact hi
      constructor
      · intro s' hs'
        simp only [hLi, s2_lmStep] at hs'
        split at hs'
        · rename_i hc; cases hs'
          refine ⟨(xs.val[i.val]'hi, false, i1), ?_, by simp [hi1v]; omega, rfl, rfl, by simp [hi1v], by simp [hi1v]; omega, rfl⟩
          simp [sim.mods.linq_max_loop.body, hlt', slice_index_ok _ _ hi, float.F64.lt, hc, hi1]
        · rename_i hc; split at hs'
          · cases hs'
          · rename_i hn; cases hs'
            refine ⟨(s.2, false, i1), ?_, by simp [hi1v]; omega, rfl, rfl, by simp [hi1v], by simp [hi1v]; omega, rfl⟩
            simp [sim.mods.linq_max_loop.body, hlt', slice_index_ok _ _ hi, float.F64.lt, hc, hn, float.F64.is_nan, hi1]
      · intro s' hs'
        simp only [hLi, s2_lmStep] at hs'
        split at hs'
        · cases hs'
        · rename_i hc; split at hs'
          · rename_i hn; cases hs'
            refine ⟨xs.val[i.val]'hi, Or.inr ⟨(xs.val[i.val]'hi, true, i1), ?_, ?_⟩, rfl⟩
            · simp [sim.mods.linq_max_loop.body, hlt', slice_index_ok _ _ hi, float.F64.lt, hc, hn, float.F64.is_nan, hi1]
            · by_cases hlt2 : i1.val < xs.val.length
              · have : i1 < Slice.len xs := by rw [slice_lt_len_iff]; exact hlt2
                simp [sim.mods.linq_max_loop.body, this]
              · have : ¬ i1 < Slice.len xs := by rw [slice_lt_len_iff]; exact hlt2
                simp [sim.mods.linq_max_loop.body, this]
          · cases hs')
    (by
      intro t s hR hge
      obtain ⟨v, d, i⟩ := t
      obtain ⟨h1, h2, h3, h4, h5⟩ := hR
      simp only at h1 h2 h3 h4 h5 hge ⊢
      have : ¬ i < Slice.len xs := by rw [slice_lt_len_iff]; simp [L] at hge; omega
      exact ⟨v, by simp [sim.mods.linq_max_loop.body, this], by simp [h1, h5]⟩)
    (xs.val[0], false, 1#usize) (none, xs.val[0]) ⟨rfl, rfl, by simp, by simp; omega, rfl⟩ (by simp [L])
  unfold sim.mods.linq_max OsuModel.Sim.linqMax
  simp only [slice_index_ok _ _ h0, float.F64.is_nan, bind_ok, hA, List.size_toArray, h, _root_.dite_true]
  simp only [show (0#usize : Usize).val = 0 from rfl, hnan]
  unfold sim.mods.linq_max_loop; rw [hl]
  simp only [Option.getD_some, List.getElem_toArray, Id.run]
  rw [if_neg hnan, Subarray.forIn_eq_forIn_toList]
  have eT : Std.Slice.toList ((abs xs : _root_.Array F64).toSubarray 1 xs.val.length) = L := by
    rw [hA, Subarray.toList_eq_drop_take]
    simp [Array.start_toSubarray, Array.stop_toSubarray, Array.array_toSubarray, L,
      Nat.min_eq_left (show 1 ≤ xs.val.length by omega)]
  simp only [eT]
  rw [forIn_list_iterR, hv]
  have e1 : (1#usize : Usize).val - 1 = 0 := rfl
  simp only [e1, Nat.sub_zero]
  have hfun : (fun j s => s2_lmStep L[j]! s) = (fun (j : Nat) (acc : Option F64 × F64) =>
      (if acc.2 < L[j]! then pure (ForInStep.yield (none, L[j]!)) else if L[j]!.isNaN = true then
        pure (ForInStep.done (some L[j]!, acc.2)) else pure (ForInStep.yield (none, acc.2)) : Id _)) := by
    funext j acc; simp only [s2_lmStep]; split <;> (try split) <;> rfl
  rw [hfun]
  generalize iterR (fun (j : Nat) (acc : Option F64 × F64) =>
      (if acc.2 < L[j]! then pure (ForInStep.yield (none, L[j]!)) else if L[j]!.isNaN = true then
        pure (ForInStep.done (some L[j]!, acc.2)) else pure (ForInStep.yield (none, acc.2)) : Id _)) 0 L.length (none, xs.val[0]) = R
  obtain ⟨a, b⟩ := R
  cases a <;> rfl

theorem sim.mods.time_ramp_times_refines (pb : sim.playable.Playable) :
    ∃ r, sim.mods.time_ramp_times pb = ok r ∧ OsuModel.Sim.timeRampTimes (abs pb) = abs r := by
  have hmax := pb.objects.property
  obtain ⟨ends, hl, hr⟩ := loop_push_map (fun x => sim.mods.time_ramp_times_loop.body pb.objects (alloc.vec.Vec.len pb.objects) x.1 x.2)
    pb.objects.val.length (fun i => (pb.objects.val.map (·.h.end_time))[i]!)
    (by
      intro ts i hi hb
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
      have hp : ts.val.length < Usize.max := by omega
      refine ⟨vpush ts (pb.objects.val[i.val]'hi).h.end_time hp, i1, ?_, by simp [s2_getElem!_map _ _ _ hi], hi1v⟩
      simp [sim.mods.time_ramp_times_loop.body, vec_lt_len_iff, hi, vec_index_usize_ok _ _ hi, vec_push_ok _ _ hp, hi1])
    (by intro ts i hi; simp [sim.mods.time_ramp_times_loop.body, vec_lt_len_iff, Nat.not_lt.mpr hi])
    (alloc.vec.Vec.new _) 0#usize (by simp) (by simpa using hmax)
  have e := s2_range_map_getElem! (pb.objects.val.map (·.h.end_time))
  simp only [List.length_map] at e
  simp only [show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero, e, alloc.vec.Vec.new, List.nil_append] at hr
  unfold sim.mods.time_ramp_times OsuModel.Sim.timeRampTimes
  by_cases h0 : pb.objects.val.length = 0
  · have h0' : ¬ (alloc.vec.Vec.len pb.objects > 0#usize) := by scalar_tac
    have e0 : pb.objects.val = [] := List.eq_nil_of_length_eq_zero h0
    refine ⟨(0, 0 + 0.75 * (0 - 0)), by simp [h0', s2_mods_F64_0, float.F64.sub, float.F64.mul, float.F64.add], ?_⟩
    simp [abs, playableS, e0, OsuModel.Sim.linqMax]
  · have h0' : alloc.vec.Vec.len pb.objects > 0#usize := by scalar_tac
    have hp : 0 < pb.objects.val.length := by omega
    have hlen : 0 < (alloc.vec.Vec.deref ends).val.length := by simp [alloc.vec.Vec.deref, hr]; omega
    have hlm := sim.mods.linq_max_refines (alloc.vec.Vec.deref ends) hlen
    let st := (pb.objects.val[0]'hp).h.start
    refine ⟨(st, st + 0.75 * ((OsuModel.Sim.linqMax (abs (alloc.vec.Vec.deref ends))).getD 0 - st)), by
      simp only [h0', ite_true, bind_ok]
      rw [show sim.mods.time_ramp_times_loop pb.objects (alloc.vec.Vec.len pb.objects) (alloc.vec.Vec.new _) 0#usize = ok ends by
        unfold sim.mods.time_ramp_times_loop; exact hl]
      simp [hlm, float.F64.sub, float.F64.mul, float.F64.add, vec_index_usize_ok _ _ (show (0#usize).val < pb.objects.val.length by simpa using hp), st], ?_⟩
    have ea : (abs (alloc.vec.Vec.deref ends) : _root_.Array F64) = ((abs pb : OsuModel.Sim.Playable).objects.map (·.h.endTime)) := by
      simp [abs, alloc.vec.Vec.deref, hr, playableS, topS, hobjS]
    rw [ea]
    simp [abs, playableS, List.getElem?_eq_getElem hp, topS, hobjS]
    exact ⟨rfl, rfl⟩

theorem s2_u64f0 : UInt64.toFloat 0 = (0 : OsuModel.Net.F64) := by decide
theorem s2_u64f32_0 : UInt64.toFloat32 0 = (0 : OsuModel.Net.F32) := by decide
theorem s2_type_default_val : sim.playable.TYPE_DEFAULT.val = 0 := by simp [sim.playable.TYPE_DEFAULT]
/-- `hobj_default` is the spec's derived `default : HObj` (`TYPE_DEFAULT` ↦ the empty class name). -/
theorem sim.playable.hobj_default_refines (tn : Nat → String) (h0 : tn 0 = "") :
    ∃ h, sim.playable.hobj_default = ok h ∧ hobjS tn h = (default : OsuModel.Sim.HObj) := by
  refine ⟨_, by simp only [sim.playable.hobj_default, fb64_0, fb32_0, sim_basic_VEC2_ZERO, bind_ok]; rfl, ?_⟩
  simp only [hobjS, h0, s2_type_default_val]
  show _ = OsuModel.Sim.instInhabitedHObj.default
  simp only [OsuModel.Sim.instInhabitedHObj.default]
  congr 1

end OsuProofs
