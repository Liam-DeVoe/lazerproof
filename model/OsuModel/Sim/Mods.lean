import OsuModel.Sim.Playable
import OsuModel.Beatmap.ModSettings

/-!
# Sim-side mod configuration (M5: rate, fail/health, score multiplier, rank, Classic)

The mod list is the ordered list of decoded mods (`APIMod.ToMod`, `OsuModel.Beatmap.Settings.toMod`), in the
order `Player` sees them (`Player.cs:229-249`; no compatibility check, so any combination in any order).
`Config.ofMods` derives everything the drawable/processor layer needs:

* **Rate** (`GetTrueGameplayRate`, `osu.Game/Screens/Play/GameplayClockExtensions.cs:14-22`):
  `sign(Rate) * AggregateFrequency * AggregateTempo` of `AdjustmentsFromMods`. Each `IApplicableToTrack` mod adds its
  bindables in mod-list order (`Player.cs:1148-1155`); `AggregateBindable.recalculateAggregate`
  (`osu.Framework/Bindables/AggregateBindable.cs`) folds `initial (1) * own property (1) * source_1 * …` left to
  right. Sources: HT/DT `SpeedChange` on Frequency (adjust_pitch) or Tempo (`RateAdjustModHelper.cs:35-62`);
  NC/DC `freqAdjust = Default` on Frequency, then `tempoAdjust = s / Default` on Tempo (`ModNightcore.cs:41-59`,
  `ModDaycore.cs:31-49`); WU/WD/AS `SpeedChange` (time-varying, `ModTimeRamp.cs:53-108`, `ModAdaptiveSpeed.cs`).
* **Fail** (`Player.CheckModsAllowFailure` = `Mods.OfType<IApplicableFailOverride>().All(m => m.PerformFail())`):
  NF/CN veto, EZ extra lives (`ModEasyWithExtraLives.cs:53-63`), `ModFailCondition` allows (SD/PF/AC).
  Fail conditions (`HealthProcessor.FailConditions`): SD (`ModSuddenDeath.cs:26-28`, `OsuModSuddenDeath.cs:25-34`),
  PF (`ModPerfect.cs:31-35`), TP (`OsuModTargetPractice.cs:106-112`). AC triggers from the ScoreProcessor's
  `Accuracy`/`MaximumAccuracy` ValueChanged (`ModAccuracyChallenge.cs:69-89`).
* **Rank**: `IApplicableToScoreProcessor.AdjustRank` (HD/FL: X→XH, S→SH; `ModHidden.cs:23-36`, `ModFlashlight.cs:64-77`).
* **Score multiplier**: `OsuScoreMultiplierCalculatorV2` + `ScoreMultiplierCalculator.CalculateFor`.
* **Classic**: `OsuModClassic.cs:52-117` (note lock → `LegacyHitPolicy(400 - (AP ? 200 : 0))`, head `CanBeHit`,
  `ClassicHealth` → `OsuLegacyHealthProcessor`); `NoSliderHeadAccuracy` is beatmap-side (playable `classic`).
-/

namespace OsuModel.Sim
open OsuModel.Net
open OsuModel.Beatmap (ModConfig)


inductive AudioProp where
  | frequency | tempo
deriving Inhabited, BEq, DecidableEq

/-- The current value of a rate-source bindable. -/
inductive RateVal where
  | const (v : F64)
  /-- `SpeedChange` of the k-th time-varying rate mod (`Config.dynRates`) -/
  | dyn (k : Nat)
deriving Inhabited

/-- `IUpdatableByPlayfield` rate mods. -/
inductive DynRate where
  /-- `ModTimeRamp` (WU/WD): InitialRate, FinalRate, beginRampTime, finalRateTime (`ApplyToBeatmap`, `:80-89`). -/
  | timeRamp (initial final begin finalTime : F64)
  /-- `ModAdaptiveSpeed`: InitialRate. -/
  | adaptive (initial : F64)
deriving Inhabited

inductive FailOverride where
  /-- NF, CN: `PerformFail() => false` -/
  | veto
  /-- k-th EZ (`ModEasyWithExtraLives`) -/
  | easy (k : Nat)
  /-- `ModFailCondition.PerformFail() => true` -/
  | allow
deriving Inhabited

inductive FailCond where
  | suddenDeath (failOnSliderTail : Bool)
  | perfect
  | targetPractice
deriving Inhabited

/-- `IApplicableToRate` mods (mod-list order), as used by `OsuAutoGeneratorBase.ApplyModsToRate/TimeDelta`. -/
inductive RateMod where
  /-- `ModRateAdjust.ApplyToRate => rate * SpeedChange.Value` (`ModRateAdjust.cs:26`) -/
  | speed (s : F64)
  /-- `ModTimeRamp.ApplyToRate` (`ModTimeRamp.cs:91-98`) -/
  | timeRamp (initial final begin finalTime : F64)
  /-- `ModAdaptiveSpeed.ApplyToRate => rate * InitialRate.Value` (`:160`) -/
  | adaptive (initial : F64)
deriving Inhabited

/-- `IUpdatableByPlayfield` mods, run in `Playfield.Update` in mod-list order (`Playfield.cs:262-273`). -/
inductive Updatable where
  | dynRate (k : Nat)
  | depth
  | magnetised
  | repel
  /-- `ModBarrelRoll.Update` -/
  | barrelRoll
  | relax
  | autopilot
  /-- k-th `InputBlockingMod` (AL/SG) -/
  | inputBlock (k : Nat)
deriving Inhabited

/-- `ApplyCustomUpdateState` handlers of drawable-transform mods (M7), in mod-list (subscription) order. -/
inductive VisMod where
  /-- `OsuModObjectScaleTween` (GR/DF): `StartScale` -/
  | scaleTween (startScale : F32)
  | spinIn
  | transform
  /-- `OsuModWiggle`: `Strength` -/
  | wiggle (strength : F64)
  | targetPractice
  /-- `OsuModHidden`: `OnlyFadeApproachCircles` -/
  | hidden (onlyApproach : Bool)
  /-- any other `ModWithVisibilityAdjustment` without judgement-relevant transforms (TC, DP, AD, …): first-object rule only -/
  | inert
  /-- `OsuModClassic.applyEarlyFading` (subscribed on circles and slider heads only) -/
  | classicEarlyFade
deriving Inhabited

/-- `IsFirstAdjustableObject` skips spinners (and spinner ticks) for HD/TC. -/
def VisMod.skipsSpinners : VisMod → Bool
  | .hidden _ => true
  | _ => false

inductive PolicyKind where
  | startTimeOrdered
  /-- `LegacyHitPolicy(hittableRange)` -/
  | legacy (hittableRange : F64)
deriving Inhabited

/-- Mod-derived configuration of the simulation. -/
structure Config where
  policy : PolicyKind := .startTimeOrdered
  /-- `OsuModClassic.ClassicNoteLock`: `blockInputToObjectsUnderSliderHead` (head `CanBeHit = !slider.AllJudged`). -/
  classicHeadBlock : Bool := false
  /-- `OsuModClassic.ClassicHealth` → `OsuLegacyHealthProcessor` (first `IApplicableHealthProcessor`). -/
  legacyHealth : Bool := false
  /-- `IApplicableFailOverride`s in mod-list order. -/
  failOverrides : Array FailOverride := #[]
  /-- initial lives of each EZ (`Retries.Value`, captured by `ApplyToPlayer`). -/
  easyRetries : Array Nat := #[]
  failConds : Array FailCond := #[]
  /-- AC: (`MinimumAccuracy`, `AccuracyJudgeMode == Standard`), in `ApplyToScoreProcessor` (mod-list) order. -/
  accChallenges : Array (F64 × Bool) := #[]
  /-- any HD/FL (`AdjustRank` X→XH, S→SH). -/
  rankAdjust : Bool := false
  rateSources : Array (AudioProp × RateVal) := #[]
  dynRates : Array DynRate := #[]
  scoreMultiplier : F64 := 1
  updatables : Array Updatable := #[]
  /-- `InputBlockingMod`s in mod order: `true` = Alternate (`LastAcceptedAction != a`), `false` = SingleTap. -/
  inputBlockers : Array Bool := #[]
  /-- `OsuModSpunOut` -/
  spunOut : Bool := false
  /-- `OsuModStrictTracking` (runtime part: tail miss on tracking loss) -/
  strictTracking : Bool := false
  /-- `ScoreInfo.IsLegacyScore` is false (lazer replay): Relax's `Update` is a no-op (`OsuModRelax.cs:75-76`). -/
  lazerReplay : Bool := false
  rateMods : Array RateMod := #[]
  /-- drawable-transform handlers (mod order) with the HD/TC first-object rule flag -/
  visMods : Array VisMod := #[]
  /-- `IUpdatableByPlayfield` position mods are in `updatables`; their settings: -/
  depthMax : F32 := 100
  magnetStrength : F32 := 0.5
  repelStrength : F32 := 0.5
  /-- BarrelRoll: `SpinSpeed`, `Direction == Counterclockwise` -/
  barrelRoll : Option (F64 × Bool) := none
  /-- debugging: per-step trace of one object (simtest `--trace-obj`) -/
  traceObj : Option Nat := none
  /-- debugging: treat every DHO as present -/
  dbgNoPresence : Bool := false
  /-- Mod acronyms in mod-list order. -/
  mods : List String := []
deriving Inhabited

/-! ## Rate -/

/-- `AggregateBindable.recalculateAggregate` for one property: `initial(1) * own(1) * v1 * v2 …`. -/
def aggregate (vals : List F64) : F64 := vals.foldl (· * ·) ((1 : F64) * 1)

/-- `GetTrueGameplayRate()` for forward playback (`Math.Sign(Rate) = 1`): `1 * AggregateFrequency * AggregateTempo`. -/
def Config.trueRate (c : Config) (speed : Array F64) : Except String F64 := do
  let val (v : RateVal) : Except String F64 := match v with
    | .const x => pure x
    | .dyn k => match speed[k]? with
      | some x => pure x
      | none => throw s!"internal: rate source {k} out of range (size {speed.size})"
  let src := c.rateSources.toList
  let f := aggregate (← (src.filter (·.1 == .frequency)).mapM (val ·.2))
  let t := aggregate (← (src.filter (·.1 == .tempo)).mapM (val ·.2))
  return (1 : F64) * f * t




/-- `ModTimeRamp.SpeedChange = new BindableDouble(1) { Precision = 0.01 }` (`ModTimeRamp.cs:53-56`). -/
def timeRampBindable : Except NetExn Framework.Bindable.BD := do
  let s ← Framework.Bindable.BD.create 1; s.setPrecision 0.01
/-- `ModAdaptiveSpeed.SpeedChange = new BindableDouble(1) { MinValue = 0.4, MaxValue = 2.5 }` (`:56-60`). -/
def adaptiveBindable : Except NetExn Framework.Bindable.BD := do
  let s ← Framework.Bindable.BD.create 1; let s ← s.setMin 0.4; s.setMax 2.5

/-- `ModTimeRamp.ApplyToRate(time)` (`:91-98`). -/
def timeRampRate (initial final begin finalTime time : F64) : Except NetExn F64 := do
  let amount := (time - begin) / F64.max 1 (finalTime - begin)
  let ramp := initial + (final - initial) * (← F64.clamp amount 0 1)
  return (1 : F64) * (← F64.roundDigits ramp 2)

/-- `SpeedChange.Value = v` for the k-th dynamic rate mod (bindable semantics: snapping / clamping / Equals). -/
def DynRate.setSpeed (d : DynRate) (old v : F64) : Except NetExn F64 := do
  let b ← match d with | .timeRamp .. => timeRampBindable | .adaptive _ => adaptiveBindable
  return (← { b with value := old }.setValue v).value

/-- Initial `SpeedChange` after `ApplyToBeatmap` + `ApplyToTrack`: TimeRamp `FinalRate.TriggerChange()` →
`ApplyToRate(+∞)` (`:66-73`); AS `InitialRate.TriggerChange()` → `SpeedChange = InitialRate` (`:134-148`). -/
def DynRate.initialSpeed : DynRate → Except NetExn F64
  | .timeRamp i f b ft => do DynRate.setSpeed (.timeRamp i f b ft) 1 (← timeRampRate i f b ft F64.posInf)
  | .adaptive i => DynRate.setSpeed (.adaptive i) 1 i

/-! ## Score multiplier (`OsuScoreMultiplierCalculatorV2.cs`, `ScoreMultiplierCalculator.cs:59-90`) -/

/-- `halfTimeMultiplier` (`:121-126`): `(int)(s * 20) / 20.0 * 1.4 - 0.5`. -/
def htMultiplier (s : F64) : F64 := F64.ofInt32 (F64.toInt32 (s * 20)) / 20.0 * 1.4 - 0.5

/-- `doubleTimeMultiplier` (`:128-139`). -/
def dtMultiplier (s : F64) : F64 :=
  let v := F64.ofInt32 (F64.toInt32 (s * 10)) / 10.0
  let penalty : F64 := if !(v == 1.5) && !(v == 1.0) then 0.01 else 0.0
  (v - 1) * 0.46 + 1 - penalty

/-- `hiddenMultiplier` (`:141-152`). -/
def hdMultiplier (m : ModConfig) (otherTiming : Bool) : F64 := Id.run do
  let mut v : F64 := 1.04
  if m.getBool "only_fade_approach_circles" then v := v - 0.02
  if otherTiming then v := v - 0.02
  return v

/-- `flashlightMultiplier` (`:154-163`); `SizeMultiplier` is a `BindableFloat` (`Value - 1` in float). -/
def flMultiplier (m : ModConfig) : F64 :=
  let size := m.getFloat "size_multiplier"
  let v := F64.max 1.02 (F64.min 1.2 (1.2 - 0.2 * F32.toF64 (size - 1)))
  if !m.getBool "combo_based_size" then 1 + (v - 1) / 5 else v

/-- `deflateMultiplier` (`:197-198`); `StartScale` is a `BindableFloat` with `Default = 2`. -/
def dfMultiplier (m : ModConfig) : F64 :=
  1.0 - F64.max 0 (0.02 * F32.toF64 (m.getFloat "start_scale" - 2))

/-- `easyMultiplier` (`:112-119`); `Retries.Default = 2`. -/
def ezMultiplier (m : ModConfig) : F64 :=
  let v := 0.8 - F64.max 0 (0.1 * F64.ofInt32 (m.getInt "retries" - 2))
  F64.max 0.4 v

/-- `difficultyAdjustMultiplier` (`:165-184`) with the unmodded `BeatmapInfo.Difficulty`. -/
def daMultiplier (m : ModConfig) (base : Difficulty) : F64 :=
  let sel (k : String) (b : F32) : F64 := F32.toF64 ((m.getOptFloat k).getD b)
  let cs := F64.abs (sel "circle_size" base.cs - F32.toF64 base.cs)
  let hp := F64.abs (sel "drain_rate" base.hp - F32.toF64 base.hp)
  let od := F64.abs (sel "overall_difficulty" base.od - F32.toF64 base.od)
  let ar := F64.abs (sel "approach_rate" base.ar - F32.toF64 base.ar)
  let mc := F64.max 0.1 (1.0 - cs * 0.5)
  let mh := F64.max 0.1 (1.0 - hp * 0.5)
  let mo := F64.max 0.1 (1.0 - od * 0.5)
  let ma := F64.max 0.1 (1.0 - ar * 0.5)
  F64.max 0.1 (mc * mh * mo * ma)

/-- `timeRampMultiplier` (`:186-195`). -/
def trMultiplier (m : ModConfig) : F64 :=
  let i := m.getDouble "initial_rate"
  let f := m.getDouble "final_rate"
  let mn := F64.min i f
  let mx := F64.max i f
  let mult (x : F64) := if x < 1 then htMultiplier x else dtMultiplier x
  0.8 * mult mn + 0.2 * mult mx

/-- Single multipliers by mod type (acronym = exact runtime type for the osu! ruleset). -/
def singleMultiplier (m : ModConfig) (base : Difficulty) : Option F64 :=
  match m.acronym with
  | "EZ" => some (ezMultiplier m)
  | "NF" => some 0.5
  | "HT" | "DC" => some (htMultiplier (m.getDouble "speed_change"))
  | "HR" => some 1.09
  | "DT" | "NC" => some (dtMultiplier (m.getDouble "speed_change"))
  | "HD" => some (hdMultiplier m false)
  | "TC" => some 1.02
  | "FL" => some (flMultiplier m)
  | "BL" => some 1.24
  | "TP" => some 0.01
  | "DA" => some (daMultiplier m base)
  | "CL" => some (if m.getBool "classic_note_lock" then 0.985 else 0.96)
  | "RD" => some 0.7
  | "RX" | "AP" => some 0.1
  | "SO" => some 0.95
  | "DF" => some (dfMultiplier m)
  | "WU" | "WD" => some (trMultiplier m)
  | "AD" => some 0.7
  | "MG" => some (0.7 - F32.toF64 (m.getFloat "attraction_strength") * 0.6)
  | "AS" => some 0.1
  | "SY" => some 0.99
  | _ => none

/-- Combination multipliers in registration order (`:36-49`). -/
def combinations : List (String × String × (ModConfig → ModConfig → F64)) :=
  [("HD", "BL", fun _ _ => 1.24),
   ("HD", "WG", fun h _ => hdMultiplier h true),
   ("HD", "GR", fun h _ => hdMultiplier h true),
   ("HD", "DF", fun h d => hdMultiplier h true * dfMultiplier d),
   ("HD", "RP", fun h _ => hdMultiplier h true),
   ("HD", "DP", fun h _ => hdMultiplier h true),
   ("TC", "BL", fun _ _ => 1.24),
   ("FL", "FR", fun f _ => 1 + (flMultiplier f - 1) / 2)]

/-- `ScoreMultiplierCalculator.CalculateFor(mods)`: `ToDictionary(GetType())` (a duplicate type throws in lazer;
here the first instance is kept), combinations first, then singles of the remaining types in list order
(`HashSet` enumeration = insertion order; only removals happen). -/
def scoreMultiplierV2 (mods : List ModConfig) (base : Difficulty) : F64 := Id.run do
  let mut byType : Array ModConfig := #[]
  for m in mods do
    if m.known && !(byType.any (·.acronym == m.acronym)) then byType := byType.push m
  -- UnknownMod instances are keys too (no multiplier); they never take part in a combination.
  let count := byType.size + (mods.filter (!·.known)).length
  if count == 0 then return 1
  -- `remaining` holds the ModConfigs themselves (order = `byType` order), so no lookup can fail.
  let mut remaining := byType
  let mut r : F64 := 1
  if count > 1 then
    for (a, b, f) in combinations do
      match remaining.find? (·.acronym == a), remaining.find? (·.acronym == b) with
      | some ma, some mb =>
        r := r * f ma mb
        remaining := remaining.filter (fun x => x.acronym != a && x.acronym != b)
      | _, _ => pure ()
  for m in remaining do
    if let some v := singleMultiplier m base then r := r * v
  return r

/-! ## Building the configuration -/

/-- LINQ `Max` over doubles (`Enumerable.Max`: NaN propagates). -/
def linqMax (xs : Array F64) : Option F64 :=
  if h : 0 < xs.size then some (Id.run do
    let mut v := xs[0]
    if v.isNaN then return v
    for x in xs[1:] do
      if v < x then v := x
      else if x.isNaN then return x
    return v)
  else none

/-- `ModTimeRamp.ApplyToBeatmap` (`ModTimeRamp.cs:80-89`): top-level objects; `GetLastObjectTime` = max `GetEndTime()`;
`FINAL_RATE_PROGRESS = 0.75f` as double. -/
def timeRampTimes (pb : Playable) : F64 × F64 :=
  let first := match pb.objects[0]? with | some o => o.h.start | none => 0
  let lastEnd := (linqMax (pb.objects.map (·.h.endTime))).getD 0
  (first, first + 0.75 * (lastEnd - first))

def Config.ofMods (mods : List ModConfig) (pb : Playable) : Config := Id.run do
  let known := mods.filter (·.known)
  let mut c : Config := { mods := known.map (·.acronym), scoreMultiplier := scoreMultiplierV2 mods pb.baseDifficulty }
  let hasAP := known.any (·.acronym == "AP")
  -- first IApplicableHealthProcessor (only CL)
  match known.find? (·.acronym == "CL") with
  | some cl => c := { c with legacyHealth := cl.getBool "classic_health" }
  | none => pure ()
  let (rb, rf) := timeRampTimes pb
  for m in known do
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
  return c

end OsuModel.Sim
