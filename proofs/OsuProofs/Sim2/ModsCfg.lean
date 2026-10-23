/-
`sim::mods` configuration: `config_add_mod` (+ `_b`, `_c`) refines one step of `OsuModel.Sim.Config.ofMods`' loop
(`s2_ofBody`, the loop body restated by `rfl`), `config_of_mods` refines `Config.ofMods` (with `lazerReplay`).
The 34-way acronym `match` is peeled in lockstep with the Rust `acr_is` chain (`s2_ite_rel`), one leaf per acronym
(`s2leaf`).
-/
import OsuProofs.Sim2.Mods
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result


namespace OsuProofs
open OsuModel.Net OsuModel.Beatmap OsuModel.Sim

/-- the loop body of `Config.ofMods` (one known mod) -/
def s2_ofBody (known : List ModConfig) (hasAP : Bool) (rb rf : F64) (m : ModConfig) (c0 : Config) :
    Id (ForInStep Config) := do
  let mut c := c0
  match m.acronym with
  | "CL" =>
    -- IApplicableToDrawableRuleset (each CL in list order; the last one wins for the policy)
    if m.getBool "classic_note_lock" then
      c := { c with policy := .legacy (400 - (if hasAP then 200 else 0)), classicHeadBlock := true }
    -- `usingHiddenFading = Mods.OfType<OsuModHidden>().SingleOrDefault()?.OnlyFadeApproachCircles.Value == false`
    let hiddenFading := match known.find? (·.acronym == "HD") with
      | some hd => !hd.getBool "only_fade_approach_circles"
      | none => false
    if m.getBool "fade_hit_circle_early" && !hiddenFading then
      c := { c with visMods := c.visMods.push .classicEarlyFade }
  | "NF" | "CN" => c := { c with failOverrides := c.failOverrides.push .veto }
  | "EZ" =>
    c := { c with failOverrides := c.failOverrides.push (.easy c.easyRetries.size)
                  easyRetries := c.easyRetries.push (m.getInt "retries").toInt.toNat }
  | "SD" => c := { c with failOverrides := c.failOverrides.push .allow
                          failConds := c.failConds.push (.suddenDeath (m.getBool "fail_on_slider_tail")) }
  | "PF" => c := { c with failOverrides := c.failOverrides.push .allow, failConds := c.failConds.push .perfect }
  | "AC" => c := { c with failOverrides := c.failOverrides.push .allow
                          accChallenges := c.accChallenges.push (m.getDouble "minimum_accuracy", m.getInt "accuracy_judge_mode" == 1) }
  | "TP" => c := { c with failConds := c.failConds.push .targetPractice, visMods := c.visMods.push .targetPractice }
  | "HD" => c := { c with rankAdjust := true, visMods := c.visMods.push (.hidden (m.getBool "only_fade_approach_circles")) }
  | "FL" => c := { c with rankAdjust := true }
  | "HT" | "DT" =>
    let p := if m.getBool "adjust_pitch" then AudioProp.frequency else .tempo
    c := { c with rateSources := c.rateSources.push (p, .const (m.getDouble "speed_change"))
                  rateMods := c.rateMods.push (.speed (m.getDouble "speed_change")) }
  | "NC" | "DC" =>
    let d : F64 := if m.acronym == "NC" then 1.5 else 0.75
    c := { c with rateSources := (c.rateSources.push (.frequency, .const d)).push (.tempo, .const (m.getDouble "speed_change" / d))
                  rateMods := c.rateMods.push (.speed (m.getDouble "speed_change")) }
  | "WU" | "WD" =>
    let p := if m.getBool "adjust_pitch" then AudioProp.frequency else .tempo
    c := { c with rateSources := c.rateSources.push (p, .dyn c.dynRates.size)
                  updatables := c.updatables.push (.dynRate c.dynRates.size)
                  rateMods := c.rateMods.push (.timeRamp (m.getDouble "initial_rate") (m.getDouble "final_rate") rb rf)
                  dynRates := c.dynRates.push (.timeRamp (m.getDouble "initial_rate") (m.getDouble "final_rate") rb rf) }
  | "AS" =>
    let p := if m.getBool "adjust_pitch" then AudioProp.frequency else .tempo
    c := { c with rateSources := c.rateSources.push (p, .dyn c.dynRates.size)
                  updatables := c.updatables.push (.dynRate c.dynRates.size)
                  rateMods := c.rateMods.push (.adaptive (m.getDouble "initial_rate"))
                  dynRates := c.dynRates.push (.adaptive (m.getDouble "initial_rate")) }
  | "RX" => c := { c with updatables := c.updatables.push .relax }
  | "AP" => c := { c with updatables := c.updatables.push .autopilot }
  | "AL" | "SG" =>
    c := { c with updatables := c.updatables.push (.inputBlock c.inputBlockers.size),
                  inputBlockers := c.inputBlockers.push (m.acronym == "AL") }
  | "SO" => c := { c with spunOut := true }
  | "GR" | "DF" => c := { c with visMods := c.visMods.push (.scaleTween (m.getFloat "start_scale")) }
  | "SI" => c := { c with visMods := c.visMods.push .spinIn }
  | "TR" => c := { c with visMods := c.visMods.push .transform }
  | "WG" => c := { c with visMods := c.visMods.push (.wiggle (m.getDouble "strength")) }
  | "TC" | "AD" => c := { c with visMods := c.visMods.push .inert }
  | "DP" => c := { c with visMods := c.visMods.push .inert, updatables := c.updatables.push .depth, depthMax := m.getFloat "max_depth" }
  | "BR" => c := { c with updatables := c.updatables.push .barrelRoll, barrelRoll := some (m.getDouble "spin_speed", m.getInt "direction" == 1) }
  | "MG" => c := { c with updatables := c.updatables.push .magnetised, magnetStrength := m.getFloat "attraction_strength" }
  | "RP" => c := { c with updatables := c.updatables.push .repel, repelStrength := m.getFloat "repulsion_strength" }
  | "ST" => c := { c with strictTracking := true }
  | _ => pure ()
  return .yield c

def s2_ofInit (mods : List ModConfig) (pb : Playable) : Config :=
  let known := mods.filter (·.known)
  let c : Config := { mods := known.map (·.acronym), scoreMultiplier := scoreMultiplierV2 mods pb.baseDifficulty }
  match known.find? (·.acronym == "CL") with
  | some cl => { c with legacyHealth := cl.getBool "classic_health" }
  | none => c

theorem s2_ofMods_eq (mods : List ModConfig) (pb : Playable) (rb rf : F64) (h : timeRampTimes pb = (rb, rf)) :
    Config.ofMods mods pb = Id.run (forIn (mods.filter (·.known)) (s2_ofInit mods pb)
      (s2_ofBody (mods.filter (·.known)) ((mods.filter (·.known)).any (·.acronym == "AP")) rb rf)) := by
  unfold Config.ofMods s2_ofInit
  simp only [h]
  cases (mods.filter (·.known)).find? (·.acronym == "CL") <;> rfl
end OsuProofs

namespace OsuProofs
open OsuImpl
@[simp] theorem s2_kk_start_scale : keyName beatmap.names.K_START_SCALE.val = "start_scale" := by simp [keyName, keyNames, beatmap.names.K_START_SCALE]
@[simp] theorem s2_kk_strength : keyName beatmap.names.K_STRENGTH.val = "strength" := by simp [keyName, keyNames, beatmap.names.K_STRENGTH]
@[simp] theorem s2_kk_max_depth : keyName beatmap.names.K_MAX_DEPTH.val = "max_depth" := by simp [keyName, keyNames, beatmap.names.K_MAX_DEPTH]
@[simp] theorem s2_kk_spin_speed : keyName beatmap.names.K_SPIN_SPEED.val = "spin_speed" := by simp [keyName, keyNames, beatmap.names.K_SPIN_SPEED]
@[simp] theorem s2_kk_direction : keyName beatmap.names.K_DIRECTION.val = "direction" := by simp [keyName, keyNames, beatmap.names.K_DIRECTION]
@[simp] theorem s2_kk_attraction_strength : keyName beatmap.names.K_ATTRACTION_STRENGTH.val = "attraction_strength" := by simp [keyName, keyNames, beatmap.names.K_ATTRACTION_STRENGTH]
@[simp] theorem s2_kk_repulsion_strength : keyName beatmap.names.K_REPULSION_STRENGTH.val = "repulsion_strength" := by simp [keyName, keyNames, beatmap.names.K_REPULSION_STRENGTH]
@[simp] theorem s2_kk_initial_rate : keyName beatmap.names.K_INITIAL_RATE.val = "initial_rate" := by simp [keyName, keyNames, beatmap.names.K_INITIAL_RATE]
@[simp] theorem s2_kk_final_rate : keyName beatmap.names.K_FINAL_RATE.val = "final_rate" := by simp [keyName, keyNames, beatmap.names.K_FINAL_RATE]
@[simp] theorem s2_kk_adjust_pitch : keyName beatmap.names.K_ADJUST_PITCH.val = "adjust_pitch" := by simp [keyName, keyNames, beatmap.names.K_ADJUST_PITCH]
@[simp] theorem s2_kk_retries : keyName beatmap.names.K_RETRIES.val = "retries" := by simp [keyName, keyNames, beatmap.names.K_RETRIES]
@[simp] theorem s2_kk_fail_on_slider_tail : keyName beatmap.names.K_FAIL_ON_SLIDER_TAIL.val = "fail_on_slider_tail" := by simp [keyName, keyNames, beatmap.names.K_FAIL_ON_SLIDER_TAIL]
@[simp] theorem s2_kk_minimum_accuracy : keyName beatmap.names.K_MINIMUM_ACCURACY.val = "minimum_accuracy" := by simp [keyName, keyNames, beatmap.names.K_MINIMUM_ACCURACY]
@[simp] theorem s2_kk_accuracy_judge_mode : keyName beatmap.names.K_ACCURACY_JUDGE_MODE.val = "accuracy_judge_mode" := by simp [keyName, keyNames, beatmap.names.K_ACCURACY_JUDGE_MODE]
@[simp] theorem s2_kk_only_fade_approach_circles : keyName beatmap.names.K_ONLY_FADE_APPROACH_CIRCLES.val = "only_fade_approach_circles" := by simp [keyName, keyNames, beatmap.names.K_ONLY_FADE_APPROACH_CIRCLES]
@[simp] theorem s2_kk_classic_note_lock : keyName beatmap.names.K_CLASSIC_NOTE_LOCK.val = "classic_note_lock" := by simp [keyName, keyNames, beatmap.names.K_CLASSIC_NOTE_LOCK]
@[simp] theorem s2_kk_fade_hit_circle_early : keyName beatmap.names.K_FADE_HIT_CIRCLE_EARLY.val = "fade_hit_circle_early" := by simp [keyName, keyNames, beatmap.names.K_FADE_HIT_CIRCLE_EARLY]
@[simp] theorem s2_kk_classic_health : keyName beatmap.names.K_CLASSIC_HEALTH.val = "classic_health" := by simp [keyName, keyNames, beatmap.names.K_CLASSIC_HEALTH]
@[simp] theorem s2_kk_speed_change : keyName beatmap.names.K_SPEED_CHANGE.val = "speed_change" := by simp [keyName, keyNames, beatmap.names.K_SPEED_CHANGE]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

def s2_cfgB (L : Nat) (c : sim.mods.Config) : Prop :=
  c.fail_overrides.val.length ≤ L ∧ c.easy_retries.val.length ≤ L ∧ c.fail_conds.val.length ≤ L ∧
  c.acc_challenges.val.length ≤ L ∧ c.rate_sources.val.length ≤ L ∧ c.dyn_rates.val.length ≤ L ∧
  c.updatables.val.length ≤ L ∧ c.input_blockers.val.length ≤ L ∧ c.rate_mods.val.length ≤ L ∧
  c.vis_mods.val.length ≤ L

/-- relational `if` peeling -/
theorem s2_ite_rel {α β : Type} (R : α → β → Prop) {c : Prop} [Decidable c] (a b : α) (a' b' : β)
    (ha : c → R a a') (hb : ¬ c → R b b') : R (if c then a else b) (if c then a' else b') := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_abs_vpush {α β : Type} [AbsTo α β] (v : alloc.vec.Vec α) (x : α) (h : v.val.length < Usize.max) :
    (abs (vpush v x h) : Array β) = (abs v : Array β).push (abs x) := by
  show ((vpush v x h).val.map abs).toArray = (v.val.map abs).toArray.push (abs x)
  simp [vpush_val]

theorem s2_cfg_sizes (c : sim.mods.Config) : (configS c).dynRates.size = c.dyn_rates.val.length ∧
    (configS c).inputBlockers.size = c.input_blockers.val.length ∧ (configS c).easyRetries.size = c.easy_retries.val.length := by
  refine ⟨?_, ?_, ?_⟩ <;> (show (List.map _ _).toArray.size = _; simp)

theorem s2_ite_okk {α : Type} (c : Prop) [Decidable c] (x y : α) :
    (if c then (ok x : Result α) else ok y) = ok (if c then x else y) := by split <;> rfl

theorem s2_fb15 : float.F64.from_bits 4609434218613702656#u64 = ok (1.5 : F64) := by
  simp only [float.F64.from_bits]; congr 1 <;> decide +kernel
theorem s2_fb075 : float.F64.from_bits 4604930618986332160#u64 = ok (0.75 : F64) := by
  simp only [float.F64.from_bits]; congr 1 <;> decide +kernel

@[simp] theorem s2_abs_vsize {α β : Type} [AbsTo α β] (v : alloc.vec.Vec α) : (abs v : Array β).size = v.val.length := by
  show (v.val.map abs).toArray.size = _; simp

theorem s2_i32_beq1 (r : I32) : (i32S r == 1) = decide (r = 1#i32) := by
  by_cases h : r = 1#i32
  · subst h; decide
  · have : i32S r ≠ 1 := by
      intro e; apply h; apply IScalar.eq_of_val_eq
      have := congrArg Int32.toInt e; rw [i32S_toInt] at this; simpa using this
    simp [this, h]

/-- one leaf of the `config_add_mod` / `Config.ofMods` lockstep -/
syntax "s2leaf" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| s2leaf [$ls,*]) => `(tactic| ((try simp (disch := first | omega | (simp [vpush_val]; omega)) only [vec_push_ok, bind_ok, s2_fb15, s2_fb075, s2_ite_okk, float.F64.div]); refine ⟨_, rfl, ?_, ?_, rfl⟩; (first | (simp only [configS]; rfl) | (simp only [configS, s2_abs_vpush, s2_abs_vsize, decide_eq_true_eq, s2_i32_beq1, s2_kk_start_scale, s2_kk_strength, s2_kk_max_depth, s2_kk_spin_speed, s2_kk_direction, s2_kk_attraction_strength, s2_kk_repulsion_strength, s2_kk_initial_rate, s2_kk_final_rate, s2_kk_adjust_pitch, s2_kk_retries, s2_kk_fail_on_slider_tail, s2_kk_minimum_accuracy, s2_kk_accuracy_judge_mode, s2_kk_only_fade_approach_circles, s2_kk_classic_note_lock, s2_kk_fade_hit_circle_early, s2_kk_classic_health, s2_kk_speed_change, $ls,*]; rfl)); (simp only [s2_cfgB]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [vpush_val, List.length_append, List.length_cons, List.length_nil]) <;> omega)))

def s2_camR (X : List String) (lz : Bool) (L : Nat) (lr0 : Bool) (r : Result sim.mods.Config)
    (s : Id (ForInStep OsuModel.Sim.Config)) : Prop :=
  ∃ c', r = ok c' ∧ s = ForInStep.yield { configS c' with mods := X, lazerReplay := lz } ∧ s2_cfgB L c' ∧
    c'.lazer_replay = lr0

open Lean Meta Elab Tactic in
/-- unfold every matcher with more than 8 alternatives occurring in the goal (the 34-way acronym `match`;
its auxiliary name differs between REPL and `lake build` because matchers are shared) -/
elab "s2_unfold_big_match" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  for c in tgt.getUsedConstants do
    if let some info ← getMatcherInfo? c then
      if info.numAlts > 8 then
        evalTactic (← `(tactic| unfold $(mkCIdent c):ident))

theorem s2_cam (c : sim.mods.Config) (m : beatmap.mod_settings.ModConfig) (hk : KeysOk m.settings.val)
    (hv : s2_AcrOk m) (L : Nat) (hB : s2_cfgB L c) (hL : L + 2 < Usize.max)
    (known : List OsuModel.Beatmap.ModConfig) (hasAP hf : Bool) (rb rf : F64)
    (hHF : hf = match known.find? (·.acronym == "HD") with
      | some hd => !hd.getBool "only_fade_approach_circles" | none => false) (X : List String) (lz : Bool) :
    s2_camR X lz (L + 2) c.lazer_replay (sim.mods.config_add_mod c m hasAP hf rb rf)
      (s2_ofBody known hasAP rb rf (mcS m) { configS c with mods := X, lazerReplay := lz }) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := hB
  obtain ⟨ri, hri, eri⟩ := beatmap.mod_settings.get_int_refines m hk beatmap.names.K_RETRIES
  obtain ⟨rj, hrj, erj⟩ := beatmap.mod_settings.get_int_refines m hk beatmap.names.K_ACCURACY_JUDGE_MODE
  obtain ⟨rd, hrd, erd⟩ := beatmap.mod_settings.get_int_refines m hk beatmap.names.K_DIRECTION
  obtain ⟨pp, hpp, epp⟩ := sim.mods.pitch_prop_refines m hk
  unfold sim.mods.config_add_mod sim.mods.config_add_mod_b sim.mods.config_add_mod_c
  simp only [lift, bind_ok, s2_acr m hv _ _ _ _ se_CL, s2_acr m hv _ _ _ _ se_NF, s2_acr m hv _ _ _ _ se_CN,
    s2_acr m hv _ _ _ _ se_EZ, s2_acr m hv _ _ _ _ se_SD, s2_acr m hv _ _ _ _ se_PF, s2_acr m hv _ _ _ _ se_AC,
    s2_acr m hv _ _ _ _ se_TP, s2_acr m hv _ _ _ _ se_HD, s2_acr m hv _ _ _ _ se_FL, s2_acr m hv _ _ _ _ se_HT,
    s2_acr m hv _ _ _ _ se_DT, s2_acr m hv _ _ _ _ se_NC, s2_acr m hv _ _ _ _ se_DC, s2_acr m hv _ _ _ _ se_WU,
    s2_acr m hv _ _ _ _ se_WD, s2_acr m hv _ _ _ _ se_AS, s2_acr m hv _ _ _ _ se_RX, s2_acr m hv _ _ _ _ se_AP,
    s2_acr m hv _ _ _ _ se_AL, s2_acr m hv _ _ _ _ se_SG, s2_acr m hv _ _ _ _ se_SO,
    s2_acr m hv _ _ _ _ se_GR, s2_acr m hv _ _ _ _ se_DF, s2_acr m hv _ _ _ _ se_SI,
    s2_acr m hv _ _ _ _ se_TR, s2_acr m hv _ _ _ _ se_WG, s2_acr m hv _ _ _ _ se_TC, s2_acr m hv _ _ _ _ se_AD,
    s2_acr m hv _ _ _ _ se_DP, s2_acr m hv _ _ _ _ se_BR, s2_acr m hv _ _ _ _ se_MG, s2_acr m hv _ _ _ _ se_RP,
    s2_acr m hv _ _ _ _ se_ST, beatmap.mod_settings.get_float_refines m hk, beatmap.mod_settings.get_double_refines m hk,
    beatmap.mod_settings.get_bool_refines m hk, hri, hrj, hrd, sim.mods.legacy_range_refines,
    hpp]
  unfold s2_ofBody
  generalize (mcS m).acronym = A
  s2_unfold_big_match
  simp only [decide_eq_true_eq, Eq.ndrec_symm, Eq.ndrec, eq_rec_constant, dite_eq_ite]
  simp only [s2_kk_retries, s2_kk_accuracy_judge_mode, s2_kk_direction] at eri erj erd
  have hbeq : ∀ s : String, (A == s) = decide (A = s) := fun s => by by_cases h : A = s <;> simp [h]
  obtain ⟨hsz1, hsz2, hsz3⟩ := s2_cfg_sizes c
  repeat' (refine s2_ite_rel _ _ _ _ _ (fun _ => ?_) (fun _ => ?_))
  all_goals (try s2leaf [hsz1, hsz2, hsz3, hbeq, ← eri, ← erj, ← erd, epp])
  -- remaining explicit branches (EZ, CL): robust to how many the generic leaf closed
  all_goals first
    | (
        by_cases hr : ri < 0#i32
        · have hz : (i32S ri).toInt.toNat = (0#u64 : U64).val := by rw [i32S_toInt]; scalar_tac
          simp only [hr, ite_true]
          s2leaf [hsz1, hsz2, hsz3, hbeq, ← eri, ← erj, ← erd, epp, hz]
        · have hz : (i32S ri).toInt.toNat = (IScalar.hcast .U64 ri).val := by
            rw [i32S_toInt, IScalar.hcast_val_eq]; scalar_tac
          simp only [hr, ite_false]
          s2leaf [hsz1, hsz2, hsz3, hbeq, ← eri, ← erj, ← erd, epp, hz]
        done)
    | (
        subst hHF
        rw [← s2_kk_classic_note_lock, ← s2_kk_fade_hit_circle_early]
        cases h1 : (mcS m).getBool (keyName ↑beatmap.names.K_CLASSIC_NOTE_LOCK) <;>
        cases h2 : (mcS m).getBool (keyName ↑beatmap.names.K_FADE_HIT_CIRCLE_EARLY) <;>
        cases h3 : (match List.find? (fun x => x.acronym == "HD") known with
          | some hd => !hd.getBool "only_fade_approach_circles" | none => false) <;>
        simp only [h1, h2, h3, ite_true, ite_false, Bool.false_eq_true, bind_ok, Bool.and_true, Bool.and_false, Bool.not_true,
          Bool.not_false] <;>
        s2leaf [hsz1, hsz2, hsz3, hbeq, epp]
        done)
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_com_loop3 (mods : Slice beatmap.mod_settings.ModConfig)
    (hok : ∀ m ∈ mods.val, KeysOk m.settings.val ∧ s2_AcrOk m) (hasAP hf : Bool) (rb rf : F64)
    (known : List OsuModel.Beatmap.ModConfig)
    (hHF : hf = match known.find? (·.acronym == "HD") with
      | some hd => !hd.getBool "only_fade_approach_circles" | none => false) (X : List String) (lz : Bool)
    (hlen : 2 * mods.val.length + 2 < Usize.max) :
    ∀ (n : Nat) (k : Usize) (c : sim.mods.Config), mods.val.length - k.val = n → k.val ≤ mods.val.length →
      s2_cfgB (2 * k.val) c →
      ∃ c', sim.mods.config_of_mods_loop3 mods c hasAP hf rb rf k = ok c' ∧ s2_cfgB (2 * mods.val.length) c' ∧
        c'.lazer_replay = c.lazer_replay ∧
        Id.run (forIn (((mods.val.drop k.val).map mcS).filter (·.known)) { configS c with mods := X, lazerReplay := lz }
          (s2_ofBody known hasAP rb rf)) = { configS c' with mods := X, lazerReplay := lz } := by
  have hmax := mods.property
  intro n
  induction n with
  | zero =>
    intro k c hn hk hB
    refine ⟨c, ?_, ?_, rfl, ?_⟩
    · unfold sim.mods.config_of_mods_loop3; rw [loop_unfold]
      simp [sim.mods.config_of_mods_loop3.body, slice_lt_len_iff, show ¬ k.val < mods.val.length by omega]
    · have : k.val = mods.val.length := by omega
      rw [← this]; exact hB
    · rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | succ n ih =>
    intro k c hn hk hB
    have hl : k.val < mods.val.length := by omega
    obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by omega)
    have hm : mods.val[k.val]'hl ∈ mods.val := List.getElem_mem _
    obtain ⟨hkk, hav⟩ := hok _ hm
    rw [List.drop_eq_getElem_cons hl, List.map_cons]
    by_cases hkn : (mods.val[k.val]'hl).known = true
    · obtain ⟨c1, hc1, e1, b1, z1⟩ := s2_cam c (mods.val[k.val]'hl) hkk hav (2 * k.val) hB (by omega) known hasAP hf rb rf hHF X lz
      obtain ⟨c2, h2, b2, z2, e2⟩ := ih k1 c1 (by omega) (by omega) (by rw [hk1v]; have := b1; unfold s2_cfgB at this ⊢; omega)
      refine ⟨c2, ?_, b2, by rw [z2, z1], ?_⟩
      · have hb : sim.mods.config_of_mods_loop3.body mods hasAP hf rb rf c k = ok (.cont (c1, k1)) := by
          simp [sim.mods.config_of_mods_loop3.body, slice_lt_len_iff, hl, index_eq mods k hl, hkn, hc1, hk1]
        unfold sim.mods.config_of_mods_loop3; rw [loop_unfold]; simp only [hb, bind_ok]
        unfold sim.mods.config_of_mods_loop3 at h2; exact h2
      · have hkn' : (mcS (mods.val[k.val]'hl)).known = true := hkn
        rw [List.filter_cons_of_pos hkn']
        simp only [Id.run, List.forIn_cons, e1]
        rw [hk1v] at e2; exact e2
    · obtain ⟨c2, h2, b2, z2, e2⟩ := ih k1 c (by omega) (by omega) (by rw [hk1v]; unfold s2_cfgB at hB ⊢; omega)
      refine ⟨c2, ?_, b2, z2, ?_⟩
      · have hb : sim.mods.config_of_mods_loop3.body mods hasAP hf rb rf c k = ok (.cont (c, k1)) := by
          simp [sim.mods.config_of_mods_loop3.body, slice_lt_len_iff, hl, index_eq mods k hl, hkn, hk1]
        unfold sim.mods.config_of_mods_loop3; rw [loop_unfold]; simp only [hb, bind_ok]
        unfold sim.mods.config_of_mods_loop3 at h2; exact h2
      · have hkn' : ¬ (mcS (mods.val[k.val]'hl)).known = true := hkn
        rw [List.filter_cons_of_neg hkn']
        rw [hk1v] at e2; exact e2
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_dec_beq (s t : String) : decide (s = t) = (s == t) := by
  by_cases h : s = t <;> simp [h]

theorem s2_com_loop0 (mods : Slice beatmap.mod_settings.ModConfig) (hok : ∀ m ∈ mods.val, s2_AcrOk m) :
    ∀ (n : Nat) (i : Usize) (h : Bool), mods.val.length - i.val = n → i.val ≤ mods.val.length →
      sim.mods.config_of_mods_loop0 mods h i =
        ok (h || ((mods.val.drop i.val).map mcS).any (fun m => m.known && m.acronym == "AP")) := by
  have hmax := mods.property
  intro n
  induction n with
  | zero =>
    intro i h hn hi
    unfold sim.mods.config_of_mods_loop0; rw [loop_unfold]
    simp [sim.mods.config_of_mods_loop0.body, slice_lt_len_iff, show ¬ i.val < mods.val.length by omega,
      List.drop_eq_nil_of_le (show mods.val.length ≤ i.val by omega)]
  | succ n ih =>
    intro i h hn hi
    have hl : i.val < mods.val.length := by omega
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
    have hav := hok _ (List.getElem_mem hl)
    have hb : sim.mods.config_of_mods_loop0.body mods h i =
        ok (.cont (h || ((mods.val[i.val]'hl).known && decide ((mcS (mods.val[i.val]'hl)).acronym = "AP")), i1)) := by
      simp only [sim.mods.config_of_mods_loop0.body, slice_lt_len_iff, hl, if_true, index_eq mods i hl, bind_ok, lift,
        s2_acr (mods.val[i.val]'hl) hav _ _ _ _ se_AP, hi1]
      cases (mods.val[i.val]'hl).known <;> cases h <;> simp
    unfold sim.mods.config_of_mods_loop0; rw [loop_unfold]; simp only [hb, bind_ok]
    have := ih i1 (h || ((mods.val[i.val]'hl).known && decide ((mcS (mods.val[i.val]'hl)).acronym = "AP"))) (by omega) (by omega)
    unfold sim.mods.config_of_mods_loop0 at this; rw [this, hi1v, List.drop_eq_getElem_cons hl]
    simp only [List.map_cons, List.any_cons]
    have hk : (mcS (mods.val[i.val]'hl)).known = (mods.val[i.val]'hl).known := rfl
    rw [hk]
    cases h <;> cases (mods.val[i.val]'hl).known <;> simp [s2_dec_beq]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_com_loop1 (mods : Slice beatmap.mod_settings.ModConfig)
    (hok : ∀ m ∈ mods.val, KeysOk m.settings.val ∧ s2_AcrOk m) :
    ∀ (n : Nat) (j : Usize) (b : Bool), mods.val.length - j.val = n → j.val ≤ mods.val.length →
      sim.mods.config_of_mods_loop1 mods b j false =
        ok (match ((mods.val.drop j.val).map mcS).find? (fun m => m.known && m.acronym == "CL") with
          | some cl => cl.getBool "classic_health" | none => b) := by
  have hmax := mods.property
  intro n
  induction n with
  | zero =>
    intro j b hn hj
    unfold sim.mods.config_of_mods_loop1; rw [loop_unfold]
    simp [sim.mods.config_of_mods_loop1.body, slice_lt_len_iff, show ¬ j.val < mods.val.length by omega,
      List.drop_eq_nil_of_le (show mods.val.length ≤ j.val by omega)]
  | succ n ih =>
    intro j b hn hj
    have hl : j.val < mods.val.length := by omega
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by omega)
    obtain ⟨hkk, hav⟩ := hok _ (List.getElem_mem hl)
    rw [List.drop_eq_getElem_cons hl, List.map_cons, List.find?_cons]
    have hk : (mcS (mods.val[j.val]'hl)).known = (mods.val[j.val]'hl).known := rfl
    by_cases hc : ((mods.val[j.val]'hl).known && decide ((mcS (mods.val[j.val]'hl)).acronym = "CL")) = true
    · have hc' : ((mcS (mods.val[j.val]'hl)).known && (mcS (mods.val[j.val]'hl)).acronym == "CL") = true := by
        rw [hk, ← s2_dec_beq]; exact hc
      rw [hc']
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have hb : sim.mods.config_of_mods_loop1.body mods b j false =
          ok (.cont ((mcS (mods.val[j.val]'hl)).getBool "classic_health", j1, true)) := by
        simp [sim.mods.config_of_mods_loop1.body, slice_lt_len_iff, hl, index_eq mods j hl, lift,
          s2_acr (mods.val[j.val]'hl) hav _ _ _ _ se_CL, hc, beatmap.mod_settings.get_bool_refines _ hkk, hj1]
      unfold sim.mods.config_of_mods_loop1; rw [loop_unfold]; simp only [hb, bind_ok]
      rw [loop_unfold]
      by_cases hj2 : j1.val < mods.val.length
      · simp [sim.mods.config_of_mods_loop1.body, slice_lt_len_iff, hj2]
      · simp [sim.mods.config_of_mods_loop1.body, slice_lt_len_iff, hj2]
    · have hc' : ((mcS (mods.val[j.val]'hl)).known && (mcS (mods.val[j.val]'hl)).acronym == "CL") = false := by
        rw [hk, ← s2_dec_beq]; simpa using hc
      rw [hc']
      have hb : sim.mods.config_of_mods_loop1.body mods b j false = ok (.cont (b, j1, false)) := by
        by_cases hkn : (mods.val[j.val]'hl).known = true
        · have : ¬ (mcS (mods.val[j.val]'hl)).acronym = "CL" := by simpa [hkn] using hc
          simp [sim.mods.config_of_mods_loop1.body, slice_lt_len_iff, hl, index_eq mods j hl, lift,
            s2_acr (mods.val[j.val]'hl) hav _ _ _ _ se_CL, hkn, this, hj1]
        · simp [sim.mods.config_of_mods_loop1.body, slice_lt_len_iff, hl, index_eq mods j hl, hkn, hj1]
      unfold sim.mods.config_of_mods_loop1; rw [loop_unfold]; simp only [hb, bind_ok]
      have := ih j1 b (by omega) (by omega)
      unfold sim.mods.config_of_mods_loop1 at this; rw [this, hj1v]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_com_loop2 (mods : Slice beatmap.mod_settings.ModConfig)
    (hok : ∀ m ∈ mods.val, KeysOk m.settings.val ∧ s2_AcrOk m) :
    ∀ (n : Nat) (j : Usize) (b : Bool), mods.val.length - j.val = n → j.val ≤ mods.val.length →
      sim.mods.config_of_mods_loop2 mods b j false =
        ok (match ((mods.val.drop j.val).map mcS).find? (fun m => m.known && m.acronym == "HD") with
          | some cl => !cl.getBool "only_fade_approach_circles" | none => b) := by
  have hmax := mods.property
  intro n
  induction n with
  | zero =>
    intro j b hn hj
    unfold sim.mods.config_of_mods_loop2; rw [loop_unfold]
    simp [sim.mods.config_of_mods_loop2.body, slice_lt_len_iff, show ¬ j.val < mods.val.length by omega,
      List.drop_eq_nil_of_le (show mods.val.length ≤ j.val by omega)]
  | succ n ih =>
    intro j b hn hj
    have hl : j.val < mods.val.length := by omega
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by omega)
    obtain ⟨hkk, hav⟩ := hok _ (List.getElem_mem hl)
    rw [List.drop_eq_getElem_cons hl, List.map_cons, List.find?_cons]
    have hk : (mcS (mods.val[j.val]'hl)).known = (mods.val[j.val]'hl).known := rfl
    by_cases hc : ((mods.val[j.val]'hl).known && decide ((mcS (mods.val[j.val]'hl)).acronym = "HD")) = true
    · have hc' : ((mcS (mods.val[j.val]'hl)).known && (mcS (mods.val[j.val]'hl)).acronym == "HD") = true := by
        rw [hk, ← s2_dec_beq]; exact hc
      rw [hc']
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have hb : sim.mods.config_of_mods_loop2.body mods b j false =
          ok (.cont (!(mcS (mods.val[j.val]'hl)).getBool "only_fade_approach_circles", j1, true)) := by
        simp [sim.mods.config_of_mods_loop2.body, slice_lt_len_iff, hl, index_eq mods j hl, lift,
          s2_acr (mods.val[j.val]'hl) hav _ _ _ _ se_HD, hc, beatmap.mod_settings.get_bool_refines _ hkk, hj1]
      unfold sim.mods.config_of_mods_loop2; rw [loop_unfold]; simp only [hb, bind_ok]
      rw [loop_unfold]
      by_cases hj2 : j1.val < mods.val.length
      · simp [sim.mods.config_of_mods_loop2.body, slice_lt_len_iff, hj2]
      · simp [sim.mods.config_of_mods_loop2.body, slice_lt_len_iff, hj2]
    · have hc' : ((mcS (mods.val[j.val]'hl)).known && (mcS (mods.val[j.val]'hl)).acronym == "HD") = false := by
        rw [hk, ← s2_dec_beq]; simpa using hc
      rw [hc']
      have hb : sim.mods.config_of_mods_loop2.body mods b j false = ok (.cont (b, j1, false)) := by
        by_cases hkn : (mods.val[j.val]'hl).known = true
        · have : ¬ (mcS (mods.val[j.val]'hl)).acronym = "HD" := by simpa [hkn] using hc
          simp [sim.mods.config_of_mods_loop2.body, slice_lt_len_iff, hl, index_eq mods j hl, lift,
            s2_acr (mods.val[j.val]'hl) hav _ _ _ _ se_HD, hkn, this, hj1]
        · simp [sim.mods.config_of_mods_loop2.body, slice_lt_len_iff, hl, index_eq mods j hl, hkn, hj1]
      unfold sim.mods.config_of_mods_loop2; rw [loop_unfold]; simp only [hb, bind_ok]
      have := ih j1 b (by omega) (by omega)
      unfold sim.mods.config_of_mods_loop2 at this; rw [this, hj1v]
end OsuProofs

namespace OsuProofs
open OsuModel.Net OsuModel.Beatmap OsuModel.Sim

def s2_btStep (bt : Array ModConfig) (m : ModConfig) : Array ModConfig :=
  if m.known && !(bt.any (·.acronym == m.acronym)) then bt.push m else bt

def s2_comboStep (st : Array ModConfig × F64) (x : String × String × (ModConfig → ModConfig → F64)) :
    Array ModConfig × F64 :=
  match st.1.find? (·.acronym == x.1), st.1.find? (·.acronym == x.2.1) with
  | some ma, some mb => (st.1.filter (fun y => y.acronym != x.1 && y.acronym != x.2.1), st.2 * x.2.2 ma mb)
  | _, _ => st

theorem s2_fiyf {X S : Type} (G : X → S → Id (ForInStep S)) (g : S → X → S)
    (hG : ∀ x s, G x s = .yield (g s x)) : ∀ (l : List X) (s : S), forIn (m := Id) l s G = l.foldl g s := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons x t ih => intro s; rw [List.forIn_cons, hG]; exact ih _

theorem s2_fiyfA {X S : Type} (G : X → S → Id (ForInStep S)) (g : S → X → S)
    (hG : ∀ x s, G x s = .yield (g s x)) (a : Array X) (s : S) : forIn (m := Id) a s G = a.foldl g s := by
  rw [← Array.forIn_toList, s2_fiyf G g hG, Array.foldl_toList]

def s2_singleStep (base : OsuModel.Sim.Difficulty) (r : F64) (m : ModConfig) : F64 :=
  match singleMultiplier m base with
  | some v => r * v
  | none => r

theorem s2_smv2_eq (mods : List ModConfig) (base : OsuModel.Sim.Difficulty) :
    scoreMultiplierV2 mods base =
      (let bt := mods.foldl s2_btStep #[]
       let count := bt.size + (mods.filter (!·.known)).length
       if count = 0 then 1 else
         let st := if count > 1 then combinations.foldl s2_comboStep (bt, 1) else (bt, 1)
         st.1.foldl (s2_singleStep base) st.2) := by
  unfold scoreMultiplierV2
  simp only [Id.run]
  rw [s2_fiyf _ s2_btStep (by intro m s; unfold s2_btStep; split <;> rfl)]
  rw [show ∀ (x : Id (Array ModConfig)) (f : Array ModConfig → Id F64), x >>= f = f x from fun _ _ => rfl]
  generalize List.foldl s2_btStep #[] mods = bt
  by_cases h0 : bt.size + (List.filter (fun x => !x.known) mods).length = 0
  · simp only [h0, beq_self_eq_true, if_true]; rfl
  · simp only [h0, if_false, beq_iff_eq, Bool.false_eq_true]
    by_cases h1 : bt.size + (List.filter (fun x => !x.known) mods).length > 1
    · simp only [h1, if_true]
      rw [s2_fiyf _ s2_comboStep ?hc]
      · rw [show ∀ (x : Id (Array ModConfig × F64)) (f : Array ModConfig × F64 → Id F64), x >>= f = f x from fun _ _ => rfl]
        rw [s2_fiyfA _ (s2_singleStep base) ?hs]
        · rfl
        · intro m s; unfold s2_singleStep; cases singleMultiplier m base <;> rfl
      · intro x s; unfold s2_comboStep
        cases s.1.find? (·.acronym == x.1) <;> cases s.1.find? (·.acronym == x.2.1) <;> rfl
    · simp only [h1, if_false]
      rw [s2_fiyfA _ (s2_singleStep base) ?hs2]
      · rfl
      · intro m s; unfold s2_singleStep; cases singleMultiplier m base <;> rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_map_chOf_inj : ∀ (a b : List U32), (∀ u ∈ a, u.val.isValidChar) → (∀ u ∈ b, u.val.isValidChar) →
    a.map chOf = b.map chOf → a = b := by
  intro a
  induction a with
  | nil => intro b _ _ h; cases b <;> simp_all
  | cons x xs ih =>
    intro b ha hb h
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have hx := chOf_toNat x (ha x (by simp))
      have hy := chOf_toNat y (hb y (by simp))
      have : x = y := UScalar.eq_of_val_eq (by rw [← hx, ← hy, h1])
      rw [this, ih ys (fun u hu => ha u (by simp [hu])) (fun u hu => hb u (by simp [hu])) h2]

theorem s2_vstr_beq (a b : alloc.vec.Vec U32) (ha : VValid a) (hb : VValid b) :
    (vstrS a == vstrS b) = decide (a.val = b.val) := by
  by_cases h : a.val = b.val
  · have : vstrS a = vstrS b := by simp [vstrS, h]
    simp [this, h]
  · have : vstrS a ≠ vstrS b := by
      intro e; apply h
      have := congrArg String.toList e
      simp [vstrS] at this
      exact s2_map_chOf_inj _ _ ha hb this
    simp [this, h]

theorem s2_cloneV {T : Type} (inst : core.clone.Clone T) (h : ∀ x, inst.clone x = ok x) (v : alloc.vec.Vec T) :
    alloc.vec.CloneVec.clone inst v = ok v := by
  obtain ⟨s', hs, hss⟩ := eq_ok_of_spec (Slice.clone_spec (clone := inst.clone) (s := v.slice) (by intro x _; exact h x))
  rw [alloc.vec.CloneVec.clone, hs, ← hss]; simp

theorem s2_mc_clone (m : beatmap.mod_settings.ModConfig) :
    beatmap.mod_settings.ModConfig.Insts.CoreCloneClone.clone m = ok m := by
  simp [beatmap.mod_settings.ModConfig.Insts.CoreCloneClone.clone, s2_cloneV core.clone.CloneU32 (fun _ => rfl),
    s2_cloneV (BuiltinClone _) (fun _ => rfl), lift, core.clone.impls.CloneBool.clone]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_smv_loop0' (mods : Slice beatmap.mod_settings.ModConfig) (hok : ∀ m ∈ mods.val, KeysOk m.settings.val ∧ VValid m.acronym) :
    ∀ (n : Nat) (i : Usize) (bt : alloc.vec.Vec beatmap.mod_settings.ModConfig) (u : Usize),
      mods.val.length - i.val = n → i.val ≤ mods.val.length → bt.val.length + u.val + (mods.val.length - i.val) ≤ mods.val.length →
      (∀ x ∈ bt.val, KeysOk x.settings.val ∧ VValid x.acronym) →
      ∃ bt' u', sim.mods.score_multiplier_v2_loop0 mods bt u i = ok (bt', u') ∧
        (bt'.val.map mcS).toArray = ((mods.val.drop i.val).map mcS).foldl s2_btStep (bt.val.map mcS).toArray ∧
        u'.val = u.val + (((mods.val.drop i.val).map mcS).filter (!·.known)).length ∧
        bt'.val.length + u'.val ≤ mods.val.length ∧ (∀ x ∈ bt'.val, KeysOk x.settings.val ∧ VValid x.acronym) := by
  have hmax := mods.property
  intro n
  induction n with
  | zero =>
    intro i bt u hn hi hb hv
    refine ⟨bt, u, ?_, ?_, ?_, ?_, hv⟩
    · unfold sim.mods.score_multiplier_v2_loop0; rw [loop_unfold]
      simp [sim.mods.score_multiplier_v2_loop0.body, slice_lt_len_iff, show ¬ i.val < mods.val.length by omega]
    · rw [List.drop_eq_nil_of_le (by omega)]; rfl
    · rw [List.drop_eq_nil_of_le (by omega)]; simp
    · omega
  | succ n ih =>
    intro i bt u hn hi hb hv
    have hl : i.val < mods.val.length := by omega
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
    have hmv := hok _ (List.getElem_mem hl)
    rw [List.drop_eq_getElem_cons hl, List.map_cons, List.foldl_cons]
    have hk : (mcS (mods.val[i.val]'hl)).known = (mods.val[i.val]'hl).known := rfl
    by_cases hkn : (mods.val[i.val]'hl).known = true
    · have hany : (bt.val.map mcS).toArray.any (·.acronym == (mcS (mods.val[i.val]'hl)).acronym) =
          bt.val.any (fun x => decide (x.acronym.val = (mods.val[i.val]'hl).acronym.val)) := by
        simp only [List.any_toArray, List.any_map]
        have : ∀ l : List beatmap.mod_settings.ModConfig, (∀ x ∈ l, KeysOk x.settings.val ∧ VValid x.acronym) →
            l.any ((fun x => x.acronym == (mcS (mods.val[i.val]'hl)).acronym) ∘ mcS) =
            l.any (fun x => decide (x.acronym.val = (mods.val[i.val]'hl).acronym.val)) := by
          intro l
          induction l with
          | nil => intro _; rfl
          | cons y ys ih2 =>
            intro hy
            simp only [List.any_cons, Function.comp_apply]
            rw [ih2 (fun z hz => hy z (by simp [hz]))]
            congr 1
            exact s2_vstr_beq _ _ (hy y (by simp)).2 hmv.2
        exact this _ hv
      by_cases hhas : bt.val.any (fun x => decide (x.acronym.val = (mods.val[i.val]'hl).acronym.val)) = true
      · have hhas' : ∃ x ∈ bt.val, x.acronym.val = (mods.val[i.val]'hl).acronym.val := by simpa using hhas
        obtain ⟨bt', u', h1, h2, h3, h4, h5⟩ := ih i1 bt u (by omega) (by omega) (by omega) hv
        refine ⟨bt', u', ?_, ?_, ?_, h4, h5⟩
        · have hb0 : sim.mods.score_multiplier_v2_loop0.body mods bt u i = ok (.cont (bt, u, i1)) := by
            simp [sim.mods.score_multiplier_v2_loop0.body, slice_lt_len_iff, hl, index_eq mods i hl, hkn,
              sim.mods.by_type_has_refines, ms_deref_val, hhas', hi1]
          unfold sim.mods.score_multiplier_v2_loop0; rw [loop_unfold]; simp only [hb0, bind_ok]
          unfold sim.mods.score_multiplier_v2_loop0 at h1; exact h1
        · rw [h2, hi1v]; unfold s2_btStep; rw [hk, hany]; simp [hkn, hhas]
        · rw [h3, hi1v]; simp [hk, hkn]
      · have hhas' : ¬ ∃ x ∈ bt.val, x.acronym.val = (mods.val[i.val]'hl).acronym.val := by simpa using hhas
        have hp : bt.val.length < Usize.max := by omega
        obtain ⟨bt', u', h1, h2, h3, h4, h5⟩ := ih i1 (vpush bt (mods.val[i.val]'hl) hp) u (by omega) (by omega)
          (by simp [vpush_val]; omega) (by intro x hx; simp [vpush_val] at hx; rcases hx with hx | hx; exact hv x hx; rw [hx]; exact hmv)
        refine ⟨bt', u', ?_, ?_, ?_, h4, h5⟩
        · have hb0 : sim.mods.score_multiplier_v2_loop0.body mods bt u i = ok (.cont (vpush bt (mods.val[i.val]'hl) hp, u, i1)) := by
            simp [sim.mods.score_multiplier_v2_loop0.body, slice_lt_len_iff, hl, index_eq mods i hl, hkn,
              sim.mods.by_type_has_refines, ms_deref_val, hhas', hi1, s2_mc_clone, vec_push_ok _ _ hp]
          unfold sim.mods.score_multiplier_v2_loop0; rw [loop_unfold]; simp only [hb0, bind_ok]
          unfold sim.mods.score_multiplier_v2_loop0 at h1; exact h1
        · rw [h2, hi1v]; unfold s2_btStep; rw [hk, hany]; simp [hkn, hhas, vpush_val]
        · rw [h3, hi1v]; simp [hk, hkn]
    · obtain ⟨u1, hu1, hu1v⟩ := usize_add_one u (by omega)
      obtain ⟨bt', u', h1, h2, h3, h4, h5⟩ := ih i1 bt u1 (by omega) (by omega) (by omega) hv
      refine ⟨bt', u', ?_, ?_, ?_, h4, h5⟩
      · have hb0 : sim.mods.score_multiplier_v2_loop0.body mods bt u i = ok (.cont (bt, u1, i1)) := by
          simp [sim.mods.score_multiplier_v2_loop0.body, slice_lt_len_iff, hl, index_eq mods i hl, hkn, hu1, hi1]
        unfold sim.mods.score_multiplier_v2_loop0; rw [loop_unfold]; simp only [hb0, bind_ok]
        unfold sim.mods.score_multiplier_v2_loop0 at h1; exact h1
      · rw [h2, hi1v]; unfold s2_btStep; rw [hk]; simp [hkn]
      · rw [h3, hi1v, hu1v]; simp [hk, hkn]; omega
end OsuProofs

namespace OsuProofs

/-- the flagged sublist -/
def s2_rem {α : Type} : List α → List Bool → List α
  | x :: xs, f :: fs => if f then x :: s2_rem xs fs else s2_rem xs fs
  | _, _ => []

theorem s2_rem_filter {α : Type} (p : α → Bool) : ∀ (l : List α) (fl : List Bool),
    s2_rem l (List.zipWith (fun x f => f && p x) l fl) = (s2_rem l fl).filter p := by
  intro l
  induction l with
  | nil => intro fl; simp [s2_rem]
  | cons x xs ih =>
    intro fl
    cases fl with
    | nil => simp [s2_rem]
    | cons f fs =>
      simp only [List.zipWith_cons_cons, s2_rem]
      cases f <;> cases hp : p x <;> simp [ih, hp, List.filter_cons]

theorem s2_rem_find {α : Type} (key : α → String) (A : String) : ∀ (l : List α) (fl : List Bool),
    (l.map key).Nodup → l.length = fl.length →
    (s2_rem l fl).find? (fun x => key x == A) =
      match l.findIdx? (fun x => key x == A) with
      | some i => if fl.getD i false then l[i]? else none
      | none => none := by
  intro l
  induction l with
  | nil => intro fl _ _; simp [s2_rem]
  | cons x xs ih =>
    intro fl hnd hlen
    cases fl with
    | nil => simp at hlen
    | cons f fs =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      by_cases hx : key x = A
      · have hnone : xs.findIdx? (fun x => key x == A) = none ∨ True := Or.inr trivial
        have hno : ∀ y ∈ xs, key y ≠ A := by
          intro y hy e; apply hnd.1; rw [hx, ← e]; exact List.mem_map_of_mem hy
        have hrem : (s2_rem xs fs).find? (fun x => key x == A) = none := by
          rw [ih fs hnd.2 hlen]
          have : xs.findIdx? (fun x => key x == A) = none := by
            simp [List.findIdx?_eq_none_iff]; intro y hy; exact hno y hy
          rw [this]
        cases f <;> simp [s2_rem, hx, List.findIdx?_cons, hrem]
      · have hx' : (key x == A) = false := by simpa using hx
        cases f <;> simp only [s2_rem, List.find?_cons, hx', List.findIdx?_cons, ite_true, ite_false, Bool.false_eq_true] <;>
          rw [ih fs hnd.2 hlen] <;> cases List.findIdx? (fun x => key x == A) xs <;> simp
end OsuProofs

namespace OsuProofs

theorem s2_key_uniq {α : Type} (key : α → String) (l : List α) (hnd : (l.map key).Nodup) (i j : Nat)
    (hi : i < l.length) (hj : j < l.length) (h : key l[i] = key l[j]) : i = j := by
  have := (List.Nodup.getElem_inj_iff hnd (i := i) (j := j) (hi := by simpa using hi) (hj := by simpa using hj)).mp
  simp at this; exact this h

theorem s2_flags_clear {α : Type} (key : α → String) (A B : String) (l : List α) (fl : List Bool)
    (hnd : (l.map key).Nodup) (hlen : l.length = fl.length) (ia ib : Nat)
    (ha : l.findIdx? (fun x => key x == A) = some ia) (hb : l.findIdx? (fun x => key x == B) = some ib) :
    (fl.set ia false).set ib false = List.zipWith (fun x f => f && (!(key x == A) && !(key x == B))) l fl := by
  obtain ⟨hia, hka, _⟩ := List.findIdx?_eq_some_iff_getElem.mp ha
  obtain ⟨hib, hkb, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hb
  simp only [beq_iff_eq] at hka hkb
  apply List.ext_getElem (by simp [hlen])
  intro j h1 h2
  simp only [List.getElem_set, List.getElem_zipWith]
  have hjl : j < l.length := by simp at h2; omega
  by_cases hjb : ib = j
  · subst hjb; simp [hkb]
  · by_cases hja : ia = j
    · subst hja; simp [hjb, hka]
    · have nA : key l[j] ≠ A := by
        intro e; apply hja; exact s2_key_uniq key l hnd ia j hia hjl (by rw [hka, e])
      have nB : key l[j] ≠ B := by
        intro e; apply hjb; exact s2_key_uniq key l hnd ib j hib hjl (by rw [hkb, e])
      simp [hjb, hja, nA, nB]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

def s2_key (m : beatmap.mod_settings.ModConfig) : String := (mcS m).acronym

theorem s2_lit_key (m : beatmap.mod_settings.ModConfig) (a : Slice U8) (A : String) (hA : litS a = A.toList) :
    decide (strS (alloc.vec.Vec.deref m.acronym) = litS a) = (s2_key m == A) := by
  rw [hA]
  have e : s2_key m = String.ofList (strS (alloc.vec.Vec.deref m.acronym)) := by
    simp [s2_key, mcS, vstrS, strS, ms_deref_val]
  rw [e]
  by_cases h : strS (alloc.vec.Vec.deref m.acronym) = A.toList
  · simp [h]
  · have : String.ofList (strS (alloc.vec.Vec.deref m.acronym)) ≠ A := by
      intro e2; apply h; rw [← e2]; simp
    simp [h, this]

theorem s2_remS_find (bt : List beatmap.mod_settings.ModConfig) (fl : List Bool) (A : String)
    (hnd : (bt.map s2_key).Nodup) (hl : bt.length = fl.length) :
    (((s2_rem bt fl).map mcS).toArray).find? (·.acronym == A) =
      (match bt.findIdx? (fun x => s2_key x == A) with
       | some i => if fl.getD i false then bt[i]? else none
       | none => none).map mcS := by
  rw [List.find?_toArray, List.find?_map]
  rw [← s2_rem_find s2_key A bt fl hnd hl]
  rfl

theorem s2_remS_filter (bt : List beatmap.mod_settings.ModConfig) (fl : List Bool) (A B : String) :
    (((s2_rem bt fl).map mcS).toArray).filter (fun y => y.acronym != A && y.acronym != B) =
      ((s2_rem bt (List.zipWith (fun x f => f && (!(s2_key x == A) && !(s2_key x == B))) bt fl)).map mcS).toArray := by
  rw [s2_rem_filter (fun x => !(s2_key x == A) && !(s2_key x == B))]
  rw [List.filter_toArray, List.filter_map]
  rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_apply_combo (k : Usize) (hk : k.val < 8) (a b : Slice U8) (A B : String)
    (hA : litS a = A.toList) (hB : litS b = B.toList) (hAB : A ≠ B)
    (f : OsuModel.Beatmap.ModConfig → OsuModel.Beatmap.ModConfig → F64)
    (hcomb : (OsuModel.Sim.combinations.getD k.val ("", "", fun _ _ => 0)) = (A, B, f))
    (bt : alloc.vec.Vec beatmap.mod_settings.ModConfig) (hv : ∀ m ∈ bt.val, s2_AcrOk m)
    (hks : ∀ m ∈ bt.val, KeysOk m.settings.val) (hnd : (bt.val.map s2_key).Nodup)
    (fl : alloc.vec.Vec Bool) (hl : fl.val.length = bt.val.length) (r : F64) :
    ∃ r' fl', sim.mods.apply_combo k a b (alloc.vec.Vec.deref bt) fl r = ok (r', fl') ∧
      s2_comboStep (((s2_rem bt.val fl.val).map mcS).toArray, r) (A, B, f) =
        (((s2_rem bt.val fl'.val).map mcS).toArray, r') ∧ fl'.val.length = bt.val.length := by
  have hvd : ∀ m ∈ (alloc.vec.Vec.deref bt).val, s2_AcrOk m := by simpa [ms_deref_val] using hv
  have hld : (alloc.vec.Vec.deref fl).val.length = (alloc.vec.Vec.deref bt).val.length := by simpa [ms_deref_val] using hl
  have hfA : ∀ (p : Slice U8) (P : String), litS p = P.toList →
      (bt.val.findIdx? (fun m => decide (strS (alloc.vec.Vec.deref m.acronym) = litS p))) =
        bt.val.findIdx? (fun x => s2_key x == P) := by
    intro p P hP; congr 1; funext m; exact s2_lit_key m p P hP
  obtain ⟨oa, hoa, eoa⟩ := sim.mods.find_by_lit_refines (alloc.vec.Vec.deref bt) a hvd
  obtain ⟨ob, hob, eob⟩ := sim.mods.find_by_lit_refines (alloc.vec.Vec.deref bt) b hvd
  simp only [ms_deref_val] at eoa eob
  rw [hfA a A hA] at eoa; rw [hfA b B hB] at eob
  have hra := sim.mods.rem_contains_refines (alloc.vec.Vec.deref fl) (alloc.vec.Vec.deref bt) a hvd hld
  have hrb := sim.mods.rem_contains_refines (alloc.vec.Vec.deref fl) (alloc.vec.Vec.deref bt) b hvd hld
  simp only [ms_deref_val] at hra hrb
  rw [hfA a A hA] at hra; rw [hfA b B hB] at hrb
  unfold s2_comboStep
  simp only [s2_remS_find bt.val fl.val A hnd hl.symm, s2_remS_find bt.val fl.val B hnd hl.symm]
  unfold sim.mods.apply_combo
  simp only [hra, hrb, bind_ok]
  have triv : ∃ r' fl', (ok (r, fl) : Result (F64 × alloc.vec.Vec Bool)) = ok (r', fl') ∧
      (((s2_rem bt.val fl.val).map mcS).toArray, r) = (((s2_rem bt.val fl'.val).map mcS).toArray, r') ∧
      fl'.val.length = bt.val.length := ⟨r, fl, rfl, rfl, hl⟩
  cases hia : bt.val.findIdx? (fun x => s2_key x == A) with
  | none => exact ⟨r, fl, by simp, by simp, hl⟩
  | some ia =>
    by_cases hfa : (fl.val[ia]?).getD false = true
    · cases hib : bt.val.findIdx? (fun x => s2_key x == B) with
      | none => exact ⟨r, fl, by simp [hfa], by simp [hfa], hl⟩
      | some ib =>
        by_cases hfb : (fl.val[ib]?).getD false = true
        · obtain ⟨hia1, hka, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hia
          obtain ⟨hib1, hkb, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hib
          rw [hia] at eoa; rw [hib] at eob
          obtain ⟨ia', rfl, hia'⟩ : ∃ x, oa = some x ∧ x.val = ia := by
            cases oa with
            | none => simp at eoa
            | some x => exact ⟨x, rfl, by simpa using eoa⟩
          obtain ⟨ib', rfl, hib'⟩ : ∃ x, ob = some x ∧ x.val = ib := by
            cases ob with
            | none => simp at eob
            | some x => exact ⟨x, rfl, by simpa using eob⟩
          subst hia' hib'
          have hfa' : fl.val.getD ia'.val false = true := by simpa [List.getD_eq_getElem?_getD] using hfa
          have hfb' : fl.val.getD ib'.val false = true := by simpa [List.getD_eq_getElem?_getD] using hfb
          have hda : (alloc.vec.Vec.deref bt).val.length = bt.val.length := by simp [ms_deref_val]
          have ea := index_eq (alloc.vec.Vec.deref bt) ia' (by rw [hda]; exact hia1)
          have eb := index_eq (alloc.vec.Vec.deref bt) ib' (by rw [hda]; exact hib1)
          have hka' : (alloc.vec.Vec.deref bt).val[ia'.val]'(by rw [hda]; exact hia1) = bt.val[ia'.val]'hia1 := by
            simp [ms_deref_val]
          have hkb' : (alloc.vec.Vec.deref bt).val[ib'.val]'(by rw [hda]; exact hib1) = bt.val[ib'.val]'hib1 := by
            simp [ms_deref_val]
          rw [hka'] at ea; rw [hkb'] at eb
          have hcm := sim.mods.combo_multiplier_refines k (bt.val[ia'.val]'hia1) (bt.val[ib'.val]'hib1)
            (hks _ (List.getElem_mem _)) (hks _ (List.getElem_mem _)) hk
          rw [hcomb] at hcm
          have m1 := vec_index_mut_eq fl ia' (by omega)
          let fl1 := alloc.vec.Vec.set fl ia' false
          have m2 := vec_index_mut_eq fl1 ib' (by simp [fl1, vec_set_val']; omega)
          refine ⟨r * f (mcS (bt.val[ia'.val]'hia1)) (mcS (bt.val[ib'.val]'hib1)), alloc.vec.Vec.set fl1 ib' false, ?_, ?_, ?_⟩
          · simp only [fl1] at m2
            have u1 := vec_index_mut_usize_ok fl ia' (by omega)
            have u2 := vec_index_mut_usize_ok (alloc.vec.Vec.set fl ia' false) ib' (by simp [vec_set_val']; omega)
            simp [hfa, hfb, hoa, hob, ea, eb, hcm, float.F64.mul, m1, m2, u1, u2]; rfl
          · simp only [hfa', hfb', ite_true, List.getElem?_eq_getElem hia1, List.getElem?_eq_getElem hib1, Option.map_some]
            rw [s2_remS_filter]
            congr 2
            simp only [fl1, vec_set_val']
            rw [s2_flags_clear s2_key A B bt.val fl.val hnd hl.symm ia'.val ib'.val hia hib]
          · simp [fl1, vec_set_val', hl]
        · exact ⟨r, fl, by simp [hfa, hfb], by simp [hfa, hfb], hl⟩
    · exact ⟨r, fl, by simp [hfa], by simp [hfa], hl⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_smv_loop1 (bt : alloc.vec.Vec beatmap.mod_settings.ModConfig) :
    ∀ (n : Nat) (fl : alloc.vec.Vec Bool) (k : Usize), bt.val.length - k.val = n → k.val ≤ bt.val.length →
      fl.val.length = k.val →
      ∃ fl', sim.mods.score_multiplier_v2_loop1 bt fl k = ok fl' ∧ fl'.val = fl.val ++ List.replicate (bt.val.length - k.val) true := by
  have hmax := bt.property
  intro n
  induction n with
  | zero =>
    intro fl k hn hk hf
    refine ⟨fl, ?_, by simp [show bt.val.length - k.val = 0 by omega]⟩
    unfold sim.mods.score_multiplier_v2_loop1; rw [loop_unfold]
    simp [sim.mods.score_multiplier_v2_loop1.body, vec_lt_len_iff, show ¬ k.val < bt.val.length by omega]
  | succ n ih =>
    intro fl k hn hk hf
    obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by omega)
    have hp : fl.val.length < Usize.max := by omega
    obtain ⟨fl', h1, h2⟩ := ih (vpush fl true hp) k1 (by omega) (by omega) (by simp [vpush_val]; omega)
    refine ⟨fl', ?_, ?_⟩
    · have hb : sim.mods.score_multiplier_v2_loop1.body bt fl k = ok (.cont (vpush fl true hp, k1)) := by
        simp [sim.mods.score_multiplier_v2_loop1.body, vec_lt_len_iff, show k.val < bt.val.length by omega,
          vec_push_ok _ _ hp, hk1]
      unfold sim.mods.score_multiplier_v2_loop1; rw [loop_unfold]; simp only [hb, bind_ok]
      unfold sim.mods.score_multiplier_v2_loop1 at h1; exact h1
    · rw [h2, vpush_val, hk1v, List.append_assoc]
      congr 1
      rw [show bt.val.length - k.val = (bt.val.length - (k.val + 1)) + 1 by omega, List.replicate_succ]; rfl

theorem s2_rem_true {α : Type} : ∀ (l : List α), s2_rem l (List.replicate l.length true) = l := by
  intro l; induction l with
  | nil => rfl
  | cons x xs ih => simp [s2_rem, List.replicate_succ, ih]

theorem s2_rem_len {α : Type} : ∀ (l : List α) (fl : List Bool), (s2_rem l fl).length ≤ l.length := by
  intro l; induction l with
  | nil => intro fl; simp [s2_rem]
  | cons x xs ih => intro fl; cases fl with
    | nil => simp [s2_rem]
    | cons f fs => cases f <;> simp [s2_rem] <;> have := ih fs <;> omega
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_smv_loop2 (base : sim.playable.Difficulty) (bt : alloc.vec.Vec beatmap.mod_settings.ModConfig)
    (fl : alloc.vec.Vec Bool) (hl : fl.val.length = bt.val.length)
    (hok : ∀ m ∈ bt.val, KeysOk m.settings.val ∧ s2_AcrOk m) :
    ∀ (n : Nat) (r : F64) (t : Usize), bt.val.length - t.val = n → t.val ≤ bt.val.length →
      sim.mods.score_multiplier_v2_loop2 base bt fl r t =
        ok (((s2_rem (bt.val.drop t.val) (fl.val.drop t.val)).map mcS).foldl (s2_singleStep (abs base)) r) := by
  have hmax := bt.property
  intro n
  induction n with
  | zero =>
    intro r t hn ht
    unfold sim.mods.score_multiplier_v2_loop2; rw [loop_unfold]
    simp [sim.mods.score_multiplier_v2_loop2.body, vec_lt_len_iff, show ¬ t.val < bt.val.length by omega,
      List.drop_eq_nil_of_le (show bt.val.length ≤ t.val by omega), s2_rem]
  | succ n ih =>
    intro r t hn ht
    have hlt : t.val < bt.val.length := by omega
    have hlf : t.val < fl.val.length := by omega
    obtain ⟨t1, ht1, ht1v⟩ := usize_add_one t (by omega)
    obtain ⟨hkk, hav⟩ := hok _ (List.getElem_mem hlt)
    rw [List.drop_eq_getElem_cons hlt, List.drop_eq_getElem_cons hlf]
    have hsm := sim.mods.single_multiplier_refines (bt.val[t.val]'hlt) hkk hav base
    let r1 := if fl.val[t.val]'hlf then s2_singleStep (abs base) r (mcS (bt.val[t.val]'hlt)) else r
    have hb : sim.mods.score_multiplier_v2_loop2.body base bt fl r t = ok (.cont (r1, t1)) := by
      cases hf : fl.val[t.val]'hlf
      · simp [sim.mods.score_multiplier_v2_loop2.body, vec_lt_len_iff, hlt, vec_index_eq fl t hlf, hf, ht1, r1]
      · simp only [sim.mods.score_multiplier_v2_loop2.body, vec_lt_len_iff, hlt, if_true, vec_index_eq fl t hlf, hf,
          bind_ok, vec_index_eq bt t hlt, hsm, ht1, r1, s2_singleStep, if_true]
        cases OsuModel.Sim.singleMultiplier (mcS (bt.val[t.val]'hlt)) (abs base) <;> simp [float.F64.mul]
    unfold sim.mods.score_multiplier_v2_loop2; rw [loop_unfold]; simp only [hb, bind_ok]
    have := ih r1 t1 (by omega) (by omega)
    unfold sim.mods.score_multiplier_v2_loop2 at this; rw [this, ht1v]
    cases hf : fl.val[t.val]'hlf <;> simp [s2_rem, hf, r1]
end OsuProofs

namespace OsuProofs
open OsuModel.Net OsuModel.Beatmap OsuModel.Sim

theorem s2_bt_nodup : ∀ (l : List ModConfig) (acc : Array ModConfig), (acc.toList.map (·.acronym)).Nodup →
    ((l.foldl s2_btStep acc).toList.map (·.acronym)).Nodup := by
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons m ms ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    unfold s2_btStep
    split
    · rename_i hc
      obtain ⟨accl⟩ := acc
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_toArray, List.any_eq_false] at hc
      simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨h, by simp, ?_⟩
      intro a ha b hb
      simp at hb; subst hb
      simp only [List.mem_map] at ha
      obtain ⟨x, hx, rfl⟩ := ha
      have := hc.2 x (by simpa using hx)
      simpa using this
    · exact h
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

def s2_smvTail (by_type : alloc.vec.Vec beatmap.mod_settings.ModConfig) (unknown : Usize) (base : sim.playable.Difficulty) :
    Result F64 := do
  let i := alloc.vec.Vec.len by_type
  let count ← i + unknown
  if count = 0#usize
  then sim.mods.F64_ONE
  else
    let remaining ←
      sim.mods.score_multiplier_v2_loop1 by_type (alloc.vec.Vec.new Bool)
        0#usize
    let r ← sim.mods.F64_ONE
    let (remaining1, r1) ←
      if count > 1#usize
      then
        do
        let s ← lift (Array.to_slice (Array.make 2#usize [ 72#u8, 68#u8 ]))
        let s1 ← lift (Array.to_slice (Array.make 2#usize [ 66#u8, 76#u8 ]))
        let s2 := alloc.vec.Vec.deref by_type
        let (r2, remaining2) ←
          sim.mods.apply_combo 0#usize s s1 s2 remaining r
        let s3 ← lift (Array.to_slice (Array.make 2#usize [ 72#u8, 68#u8 ]))
        let s4 ← lift (Array.to_slice (Array.make 2#usize [ 87#u8, 71#u8 ]))
        let s5 := alloc.vec.Vec.deref by_type
        let (r3, remaining3) ←
          sim.mods.apply_combo 1#usize s3 s4 s5 remaining2 r2
        let s6 ← lift (Array.to_slice (Array.make 2#usize [ 72#u8, 68#u8 ]))
        let s7 ← lift (Array.to_slice (Array.make 2#usize [ 71#u8, 82#u8 ]))
        let s8 := alloc.vec.Vec.deref by_type
        let (r4, remaining4) ←
          sim.mods.apply_combo 2#usize s6 s7 s8 remaining3 r3
        let s9 ← lift (Array.to_slice (Array.make 2#usize [ 72#u8, 68#u8 ]))
        let s10 ← lift (Array.to_slice (Array.make 2#usize [ 68#u8, 70#u8 ]))
        let s11 := alloc.vec.Vec.deref by_type
        let (r5, remaining5) ←
          sim.mods.apply_combo 3#usize s9 s10 s11 remaining4 r4
        let s12 ← lift (Array.to_slice (Array.make 2#usize [ 72#u8, 68#u8 ]))
        let s13 ← lift (Array.to_slice (Array.make 2#usize [ 82#u8, 80#u8 ]))
        let s14 := alloc.vec.Vec.deref by_type
        let (r6, remaining6) ←
          sim.mods.apply_combo 4#usize s12 s13 s14 remaining5 r5
        let s15 ← lift (Array.to_slice (Array.make 2#usize [ 72#u8, 68#u8 ]))
        let s16 ← lift (Array.to_slice (Array.make 2#usize [ 68#u8, 80#u8 ]))
        let s17 := alloc.vec.Vec.deref by_type
        let (r7, remaining7) ←
          sim.mods.apply_combo 5#usize s15 s16 s17 remaining6 r6
        let s18 ← lift (Array.to_slice (Array.make 2#usize [ 84#u8, 67#u8 ]))
        let s19 ← lift (Array.to_slice (Array.make 2#usize [ 66#u8, 76#u8 ]))
        let s20 := alloc.vec.Vec.deref by_type
        let (r8, remaining8) ←
          sim.mods.apply_combo 6#usize s18 s19 s20 remaining7 r7
        let s21 ← lift (Array.to_slice (Array.make 2#usize [ 70#u8, 76#u8 ]))
        let s22 ← lift (Array.to_slice (Array.make 2#usize [ 70#u8, 82#u8 ]))
        let s23 := alloc.vec.Vec.deref by_type
        let (r9, remaining9) ←
          sim.mods.apply_combo 7#usize s21 s22 s23 remaining8 r8
        ok (remaining9, r9)
      else ok (remaining, r)
    sim.mods.score_multiplier_v2_loop2 base by_type remaining1 r1 0#usize

theorem s2_smv_unfold (mods : Slice beatmap.mod_settings.ModConfig) (base : sim.playable.Difficulty) :
    sim.mods.score_multiplier_v2 mods base = (do
      let p ← sim.mods.score_multiplier_v2_loop0 mods (alloc.vec.Vec.new beatmap.mod_settings.ModConfig) 0#usize 0#usize
      s2_smvTail p.1 p.2 base) := by
  unfold sim.mods.score_multiplier_v2 s2_smvTail
  rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_acrok_of (m : beatmap.mod_settings.ModConfig) (h : VValid m.acronym) : s2_AcrOk m := by
  intro u hu; simp [ms_deref_val] at hu; exact h u hu

theorem sim.mods.score_multiplier_v2_refines (mods : Slice beatmap.mod_settings.ModConfig) (base : sim.playable.Difficulty)
    (hok : ∀ m ∈ mods.val, KeysOk m.settings.val ∧ VValid m.acronym) :
    sim.mods.score_multiplier_v2 mods base = ok (OsuModel.Sim.scoreMultiplierV2 (mods.val.map mcS) (abs base)) := by
  have hmax := mods.property
  obtain ⟨bt, u, h0, e0, eu, hbu, hbv⟩ := s2_smv_loop0' mods hok _ 0#usize (alloc.vec.Vec.new _) 0#usize rfl (by simp)
    (by simp) (by simp)
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, alloc.vec.Vec.new, Nat.zero_add] at e0 eu
  have hbtmax := bt.property
  obtain ⟨cnt, hcnt, hcntv⟩ : ∃ z, alloc.vec.Vec.len bt + u = ok z ∧ z.val = bt.val.length + u.val := by
    obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (Usize.add_spec (x := alloc.vec.Vec.len bt) (y := u) (by simp; omega))
    exact ⟨z, hz, by simpa using hv⟩
  have hbtS : (bt.val.map mcS).toArray = (mods.val.map mcS).foldl s2_btStep #[] := by
    rw [e0]; rfl
  have hnd : (bt.val.map s2_key).Nodup := by
    have := s2_bt_nodup (mods.val.map mcS) #[] (by simp)
    rw [← hbtS] at this
    simp [Function.comp_def] at this
    exact this
  have hcount : ((mods.val.map mcS).foldl s2_btStep #[]).size + ((mods.val.map mcS).filter (!·.known)).length = cnt.val := by
    rw [← hbtS, hcntv, eu]; simp
  rw [s2_smv2_eq]
  simp only [hcount]
  rw [s2_smv_unfold, h0, bind_ok]
  unfold s2_smvTail
  simp only [hcnt, bind_ok, ← hbtS]
  have hv' : ∀ m ∈ bt.val, s2_AcrOk m := fun m h => s2_acrok_of m (hbv m h).2
  have hks : ∀ m ∈ bt.val, KeysOk m.settings.val := fun m h => (hbv m h).1
  by_cases hz : cnt.val = 0
  · have : cnt = 0#usize := UScalar.eq_of_val_eq (by simp [hz])
    simp [this, hz]
  · have hz' : ¬ cnt = 0#usize := fun e => hz (by simp [e])
    obtain ⟨fl, hfl, efl⟩ := s2_smv_loop1 bt _ (alloc.vec.Vec.new Bool) 0#usize rfl (by simp) (by simp)
    simp only [show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero] at efl
    have efl' : fl.val = List.replicate bt.val.length true := by rw [efl]; rfl
    have hfl1 : fl.val.length = bt.val.length := by simp [efl']
    have hrem0 : (bt.val.map mcS).toArray = ((s2_rem bt.val fl.val).map mcS).toArray := by
      rw [efl', s2_rem_true]
    simp only [hz', if_false, hfl, bind_ok, s2_mods_F64_ONE, hz, if_false]
    rw [hrem0]
    by_cases h1 : cnt.val > 1
    · have h1' : cnt > 1#usize := by
        first | (show (1#usize : Usize) < cnt; exact (UScalar.lt_equiv _ _).mpr (by simpa using h1)) | (simp; omega) | scalar_tac
      obtain ⟨r1, fl1, ha1, e1, l1⟩ := s2_apply_combo 0#usize (by simp)
        (Array.to_slice (Array.make 2#usize [72#u8, 68#u8] (by simp))) (Array.to_slice (Array.make 2#usize [66#u8, 76#u8] (by simp)))
        "HD" "BL" (by simp [litS, Array.to_slice, Array.make]) (by simp [litS, Array.to_slice, Array.make]) (by decide)
        (fun _ _ => 1.24) rfl bt hv' hks hnd fl hfl1 1
      obtain ⟨r2, fl2, ha2, e2, l2⟩ := s2_apply_combo 1#usize (by simp)
        (Array.to_slice (Array.make 2#usize [72#u8, 68#u8] (by simp))) (Array.to_slice (Array.make 2#usize [87#u8, 71#u8] (by simp)))
        "HD" "WG" (by simp [litS, Array.to_slice, Array.make]) (by simp [litS, Array.to_slice, Array.make]) (by decide)
        (fun h _ => OsuModel.Sim.hdMultiplier h true) rfl bt hv' hks hnd fl1 l1 r1
      obtain ⟨r3, fl3, ha3, e3, l3⟩ := s2_apply_combo 2#usize (by simp)
        (Array.to_slice (Array.make 2#usize [72#u8, 68#u8] (by simp))) (Array.to_slice (Array.make 2#usize [71#u8, 82#u8] (by simp)))
        "HD" "GR" (by simp [litS, Array.to_slice, Array.make]) (by simp [litS, Array.to_slice, Array.make]) (by decide)
        (fun h _ => OsuModel.Sim.hdMultiplier h true) rfl bt hv' hks hnd fl2 l2 r2
      obtain ⟨r4, fl4, ha4, e4, l4⟩ := s2_apply_combo 3#usize (by simp)
        (Array.to_slice (Array.make 2#usize [72#u8, 68#u8] (by simp))) (Array.to_slice (Array.make 2#usize [68#u8, 70#u8] (by simp)))
        "HD" "DF" (by simp [litS, Array.to_slice, Array.make]) (by simp [litS, Array.to_slice, Array.make]) (by decide)
        (fun h d => OsuModel.Sim.hdMultiplier h true * OsuModel.Sim.dfMultiplier d) rfl bt hv' hks hnd fl3 l3 r3
      obtain ⟨r5, fl5, ha5, e5, l5⟩ := s2_apply_combo 4#usize (by simp)
        (Array.to_slice (Array.make 2#usize [72#u8, 68#u8] (by simp))) (Array.to_slice (Array.make 2#usize [82#u8, 80#u8] (by simp)))
        "HD" "RP" (by simp [litS, Array.to_slice, Array.make]) (by simp [litS, Array.to_slice, Array.make]) (by decide)
        (fun h _ => OsuModel.Sim.hdMultiplier h true) rfl bt hv' hks hnd fl4 l4 r4
      obtain ⟨r6, fl6, ha6, e6, l6⟩ := s2_apply_combo 5#usize (by simp)
        (Array.to_slice (Array.make 2#usize [72#u8, 68#u8] (by simp))) (Array.to_slice (Array.make 2#usize [68#u8, 80#u8] (by simp)))
        "HD" "DP" (by simp [litS, Array.to_slice, Array.make]) (by simp [litS, Array.to_slice, Array.make]) (by decide)
        (fun h _ => OsuModel.Sim.hdMultiplier h true) rfl bt hv' hks hnd fl5 l5 r5
      obtain ⟨r7, fl7, ha7, e7, l7⟩ := s2_apply_combo 6#usize (by simp)
        (Array.to_slice (Array.make 2#usize [84#u8, 67#u8] (by simp))) (Array.to_slice (Array.make 2#usize [66#u8, 76#u8] (by simp)))
        "TC" "BL" (by simp [litS, Array.to_slice, Array.make]) (by simp [litS, Array.to_slice, Array.make]) (by decide)
        (fun _ _ => 1.24) rfl bt hv' hks hnd fl6 l6 r6
      obtain ⟨r8, fl8, ha8, e8, l8⟩ := s2_apply_combo 7#usize (by simp)
        (Array.to_slice (Array.make 2#usize [70#u8, 76#u8] (by simp))) (Array.to_slice (Array.make 2#usize [70#u8, 82#u8] (by simp)))
        "FL" "FR" (by simp [litS, Array.to_slice, Array.make]) (by simp [litS, Array.to_slice, Array.make]) (by decide)
        (fun f _ => 1 + (OsuModel.Sim.flMultiplier f - 1) / 2) rfl bt hv' hks hnd fl7 l7 r7
      simp only [OsuModel.Sim.combinations, List.foldl_cons, List.foldl_nil]
      rw [e1, e2, e3, e4, e5, e6, e7, e8]
      simp [h1', lift, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8,
        s2_smv_loop2 base bt fl8 l8 (fun m h => ⟨hks m h, hv' m h⟩) _ r8 0#usize rfl (by simp)]
      simp [show 1 < cnt.val from h1]
    · simp only [h1, if_false]
      have h1' : ¬ cnt > 1#usize := by
        first | (intro h; apply h1; have := (UScalar.lt_equiv _ _).mp h; simpa using this) | (simp; omega) | scalar_tac
      simp only [h1', if_false, bind_ok]
      simp [s2_smv_loop2 base bt fl hfl1 (fun m h => ⟨hks m h, hv' m h⟩) _ 1 0#usize rfl (by simp)]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_any_filter {α} (p q : α → Bool) : ∀ l : List α, (l.filter p).any q = l.any (fun a => p a && q a)
  | [] => rfl
  | a :: l => by
    rw [List.filter_cons]; cases hp : p a <;> simp [hp, s2_any_filter p q l]

theorem s2_find_filter {α} (p q : α → Bool) : ∀ l : List α, (l.filter p).find? q = l.find? (fun a => p a && q a)
  | [] => rfl
  | a :: l => by
    rw [List.filter_cons]; cases hp : p a <;> simp [hp, List.find?_cons, s2_find_filter p q l]

theorem s2_trt_tn (tn : Nat → String) (pb : sim.playable.Playable) :
    OsuModel.Sim.timeRampTimes (playableS tn pb) = OsuModel.Sim.timeRampTimes (abs pb) := by
  show _ = OsuModel.Sim.timeRampTimes (playableS simTnDefault pb)
  simp [OsuModel.Sim.timeRampTimes, playableS, topS, hobjS, Function.comp_def]
  cases (pb.objects.val)[0]? <;> simp [topS, hobjS]

theorem s2_fb100 : float.F32.from_bits 1120403456#u32 = ok (100 : F32) := by
  simp only [float.F32.from_bits]; congr 1 <;> decide +kernel
theorem s2_fbHalf : float.F32.from_bits 1056964608#u32 = ok (0.5 : F32) := by
  simp only [float.F32.from_bits]; congr 1 <;> decide +kernel
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

def s2_cfg0 (b lr : Bool) (f : F64) : sim.mods.Config :=
  {
    policy := sim.mods.PolicyKind.StartTimeOrdered,
    classic_head_block := false,
    legacy_health := b,
    fail_overrides := (alloc.vec.Vec.new sim.mods.FailOverride),
    easy_retries := (alloc.vec.Vec.new Std.U64),
    fail_conds := (alloc.vec.Vec.new sim.mods.FailCond),
    acc_challenges := (alloc.vec.Vec.new sim.mods.AccChallenge),
    rank_adjust := false,
    rate_sources := (alloc.vec.Vec.new sim.mods.RateSource),
    dyn_rates := (alloc.vec.Vec.new sim.mods.DynRate),
    score_multiplier := f,
    updatables := (alloc.vec.Vec.new sim.mods.Updatable),
    input_blockers := (alloc.vec.Vec.new Bool),
    spun_out := false,
    strict_tracking := false,
    lazer_replay := lr,
    rate_mods := (alloc.vec.Vec.new sim.mods.RateMod),
    vis_mods := (alloc.vec.Vec.new sim.mods.VisMod),
    depth_max := 100,
    magnet_strength := 0.5,
    repel_strength := 0.5,
    barrel_roll := none
  }

theorem sim.mods.config_of_mods_refines (tn : Nat → String) (ms : Slice beatmap.mod_settings.ModConfig)
    (pb : sim.playable.Playable) (lr : Bool)
    (hok : ∀ m ∈ ms.val, KeysOk m.settings.val ∧ VValid m.acronym) (hlen : 2 * ms.val.length + 2 < Usize.max) :
    ∃ c, sim.mods.config_of_mods ms pb lr = ok c ∧
      configS c = { { OsuModel.Sim.Config.ofMods (ms.val.map mcS) (playableS tn pb) with lazerReplay := lr } with
        mods := [], traceObj := none, dbgNoPresence := false } := by
  have hok' : ∀ m ∈ ms.val, KeysOk m.settings.val ∧ s2_AcrOk m :=
    fun m h => ⟨(hok m h).1, s2_acrok_of m (hok m h).2⟩
  have hA : ∀ m ∈ ms.val, s2_AcrOk m := fun m h => (hok' m h).2
  obtain ⟨⟨rb, rf⟩, htr, htrS⟩ := sim.mods.time_ramp_times_refines pb
  have htr' : OsuModel.Sim.timeRampTimes (playableS tn pb) = (rb, rf) := by rw [s2_trt_tn, htrS]; rfl
  have h0 := s2_com_loop0 ms hA _ 0#usize false rfl (by simp)
  have h1 := s2_com_loop1 ms hok' _ 0#usize false rfl (by simp)
  have h2 := s2_com_loop2 ms hok' _ 0#usize false rfl (by simp)
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, Bool.false_or] at h0 h1 h2
  rw [← s2_any_filter] at h0
  rw [← s2_find_filter] at h1 h2
  let L := ms.val.map mcS
  let known := L.filter (·.known)
  let c0 := s2_cfg0 (match known.find? (·.acronym == "CL") with | some cl => cl.getBool "classic_health" | none => false)
    lr (OsuModel.Sim.scoreMultiplierV2 L (abs pb.base_difficulty))
  have hB : s2_cfgB (2 * (0#usize : Usize).val) c0 := by
    simp only [s2_cfgB, c0, s2_cfg0, alloc.vec.Vec.new]; simp
  obtain ⟨c', hc', _, hlr, hfor⟩ := s2_com_loop3 ms hok' (known.any (·.acronym == "AP"))
    (match known.find? (·.acronym == "HD") with | some cl => !cl.getBool "only_fade_approach_circles" | none => false)
    rb rf known rfl (known.map (·.acronym)) false hlen _ 0#usize c0 rfl (by simp) hB
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at hfor
  refine ⟨c', ?_, ?_⟩
  · unfold sim.mods.config_of_mods
    rw [sim.mods.score_multiplier_v2_refines ms _ hok]
    simp only [bind_ok, s2_fb100, s2_fbHalf, h0, h1, h2, htr]
    exact hc'
  · rw [s2_ofMods_eq _ _ rb rf htr']
    have hinit : s2_ofInit L (playableS tn pb) = { configS c0 with mods := known.map (·.acronym), lazerReplay := false } := by
      simp only [s2_ofInit, c0, known, L]
      generalize List.find? _ _ = F
      cases F <;> rfl
    rw [hinit]
    show configS c' = { { Id.run (forIn known { configS c0 with mods := known.map (·.acronym), lazerReplay := false }
      (s2_ofBody known (known.any (·.acronym == "AP")) rb rf)) with lazerReplay := lr } with
        mods := [], traceObj := none, dbgNoPresence := false }
    rw [hfor]
    have : lr = c'.lazer_replay := hlr.symm
    rw [this]; rfl
end OsuProofs

namespace OsuProofs
open OsuModel.Net OsuModel.Beatmap OsuModel.Sim

/-- rate-source well-formedness: every `dyn k` source indexes `dynRates` -/
def s2_dynWF (c : Config) : Prop := ∀ x ∈ c.rateSources, ∀ k, x.2 = .dyn k → k < c.dynRates.size

theorem s2_ofBody_wf (known : List ModConfig) (hasAP : Bool) (rb rf : F64) (m : ModConfig) (c : Config)
    (h : s2_dynWF c) : ∃ c', s2_ofBody known hasAP rb rf m c = .yield c' ∧ s2_dynWF c' := by
  simp only [s2_ofBody]
  repeat' split
  all_goals refine ⟨_, rfl, ?_⟩
  all_goals
    intro x hx k hk
    (try simp only [Array.mem_push, Array.size_push] at hx ⊢)
    first
      | exact h x hx k hk
      | (have := h x hx k hk; omega)
      | (cases hx with
          | inl hx =>
            first
              | exact h x hx k hk
              | (have := h x hx k hk; omega)
              | (cases hx with
                  | inl hx => have := h x hx k hk; omega
                  | inr hx => subst hx; simp at hk <;> omega)
          | inr hx => subst hx; simp at hk <;> omega)
theorem s2_forIn_wf (known : List ModConfig) (hasAP : Bool) (rb rf : F64) :
    ∀ (l : List ModConfig) (c : Config), s2_dynWF c → s2_dynWF (Id.run (forIn l c (s2_ofBody known hasAP rb rf)))
  | [], c, h => h
  | m :: l, c, h => by
    obtain ⟨c', e, h'⟩ := s2_ofBody_wf known hasAP rb rf m c h
    have : Id.run (forIn (m :: l) c (s2_ofBody known hasAP rb rf)) = Id.run (forIn l c' (s2_ofBody known hasAP rb rf)) := by
      simp only [List.forIn_cons, e]; rfl
    rw [this]; exact s2_forIn_wf known hasAP rb rf l c' h'

theorem s2_ofMods_wf (mods : List ModConfig) (pb : Playable) : s2_dynWF (Config.ofMods mods pb) := by
  rw [s2_ofMods_eq mods pb (timeRampTimes pb).1 (timeRampTimes pb).2 rfl]
  apply s2_forIn_wf
  unfold s2_ofInit
  dsimp only
  split <;> (intro x hx; simp at hx)
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- `config_of_mods_refines` + rate-source well-formedness (every `Dyn k` indexes `dyn_rates`) -/
theorem sim.mods.config_of_mods_refines_wf (tn : Nat → String) (ms : Slice beatmap.mod_settings.ModConfig)
    (pb : sim.playable.Playable) (lr : Bool)
    (hok : ∀ m ∈ ms.val, KeysOk m.settings.val ∧ VValid m.acronym) (hlen : 2 * ms.val.length + 2 < Usize.max) :
    ∃ c, sim.mods.config_of_mods ms pb lr = ok c ∧
      configS c = { { OsuModel.Sim.Config.ofMods (ms.val.map mcS) (playableS tn pb) with lazerReplay := lr } with
        mods := [], traceObj := none, dbgNoPresence := false } ∧
      ∀ s ∈ c.rate_sources.val, ∀ k, s.val = .Dyn k → k.val < c.dyn_rates.val.length := by
  obtain ⟨c, h1, h2⟩ := sim.mods.config_of_mods_refines tn ms pb lr hok hlen
  refine ⟨c, h1, h2, ?_⟩
  intro s hs k hk
  have wf := s2_ofMods_wf (ms.val.map mcS) (playableS tn pb)
  have hmem : ((abs s.prop, abs s.val) : OsuModel.Sim.AudioProp × OsuModel.Sim.RateVal) ∈ (configS c).rateSources := by
    show _ ∈ (List.map _ c.rate_sources.val).toArray
    simp only [List.mem_toArray, List.mem_map]
    exact ⟨s, hs, rfl⟩
  have hsz : (configS c).dynRates.size = c.dyn_rates.val.length := (s2_cfg_sizes c).1
  rw [h2] at hmem hsz
  have := wf _ hmem k.val (by rw [hk]; rfl)
  simp only at hsz
  omega
/-- FRAGMENT-OF: sim.mods.config_of_mods (one step of `Config.ofMods`' loop, `s2_ofBody`; `config_add_mod_b`/`_c` are
unfolded inside it) -/
theorem sim.mods.config_add_mod_refines : type_of% @s2_cam := @s2_cam
end OsuProofs
