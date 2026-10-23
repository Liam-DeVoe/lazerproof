import OsuModel.Beatmap.Decoder
import OsuModel.Beatmap.Processor

/-!
# Conversion and `WorkingBeatmap.GetPlayableBeatmap` (osu! ruleset)

* `OsuBeatmapConverter.ConvertHitObject` (`O/Beatmaps/OsuBeatmapConverter.cs:27-75`) and
  `BeatmapConverter<T>.Convert` (`G/Beatmaps/BeatmapConverter.cs:44-122`).
* `WorkingBeatmap.GetPlayableBeatmap(ruleset, mods, token)` (`G/Beatmaps/WorkingBeatmap.cs:276-352`).

Mods are represented by `Mod` records whose optional fields are exactly the hook interfaces
that `GetPlayableBeatmap` consults, in the order it consults them. The osu! mods fill them in
`Mods.lean` (`ModConfig.hooks`).
-/

namespace OsuModel.Beatmap
open OsuModel.Net

/-- A reference to a (top-level or nested) hit object of the playable beatmap, by position;
`epoch` is the beatmap's `epoch` when the reference was taken. -/
structure ObjRef where
  index : Nat
  nested : Option Nat := none
  epoch : Nat
deriving Inhabited, Repr

/-- Beatmap-derived state left in a mod instance by `GetPlayableBeatmap`. -/
inductive ModState where
  /-- `ModWithVisibilityAdjustment.FirstObject` (`ModWithVisibilityAdjustment.cs:56-74`) -/
  | firstObject (ref : Option ObjRef)
  /-- `ModTimeRamp.beginRampTime`, `finalRateTime` (`ModTimeRamp.cs:80-89`) -/
  | timeRamp (beginRampTime finalRateTime : F64)
  /-- `ModAdaptiveSpeed.precedingEndTimes`, in insertion order (`ModAdaptiveSpeed.cs:190-204`) -/
  | precedingEndTimes (entries : Array (ObjRef × F64))
deriving Inhabited, Repr

/-- The playable osu! beatmap (`IBeatmap` returned by `GetPlayableBeatmap`). -/
structure PlayableBeatmap where
  /-- `BeatmapVersion` -/
  formatVersion : Int32
  /-- `Beatmap.Difficulty` (after `IApplicableToDifficulty` mods) -/
  difficulty : Difficulty
  /-- `BeatmapInfo.Difficulty` (decoded, never modified by mods) -/
  baseDifficulty : Difficulty
  stackLeniency : F32
  /-- `AudioLeadIn` (used by `MasterGameplayClockContainer` for the gameplay start time) -/
  audioLeadIn : F64
  controlPoints : ControlPointInfo
  breaks : Array BreakPeriod
  hitObjects : Array OsuHitObject
  /-- Incremented whenever a mod replaces the hit object *list* by new objects (Target Practice),
  so that object references taken earlier (`ObjRef`) can be recognised as stale. -/
  epoch : Nat := 0
  /-- Beatmap-derived state that `IApplicableToBeatmap` mods keep in their instances, with the mod's
  index in the mod list. -/
  modStates : Array (Nat × ModState) := #[]
deriving Inhabited, Repr

/-- Hook points of `GetPlayableBeatmap` (one field per interface; `none` = the mod does not
implement it). -/
structure Mod where
  acronym : String
  /-- `IApplicableAfterBeatmapConversion.ApplyToBeatmap(converted)` -/
  applyAfterConversion : Option (PlayableBeatmap → PlayableBeatmap) := none
  /-- `IApplicableToDifficulty.ApplyToDifficulty(converted.Difficulty)` -/
  applyToDifficulty : Option (Difficulty → Difficulty) := none
  /-- `IApplicableToHitObject.ApplyToHitObject(obj)` (after `ApplyDefaults`, before stacking).
  An implementation that moves a slider or replaces its path must also recompute nested
  positions as `Slider.updateNestedPositions` does (`Slider.cs:229-254`); see `updateNestedPositions`. -/
  applyToHitObject : Option (OsuHitObject → OsuHitObject) := none
  /-- `IApplicableToBeatmap.ApplyToBeatmap(converted)` (after stacking); the argument is the mod's
  index in the mod list (for `PlayableBeatmap.modStates`). -/
  applyToBeatmap : Option (Nat → PlayableBeatmap → DecodeM PlayableBeatmap) := none

/-- `Slider.updateNestedPositions()` (`Slider.cs:229-254`), for mods that change `Position`/`Path`. -/
def updateNestedPositions (h : OsuHitObject) : OsuHitObject :=
  match h.kind with
  | .slider s =>
    { h with nested := h.nested.map fun n =>
        match n.kind with
        | .head => { n with position := h.position }
        | .tail => { n with position := h.endPosition }
        | .repeat | .tick => { n with position := h.position + s.path.positionAt n.pathProgress }
        | _ => n }
  | _ => h

/-- `OsuBeatmapConverter.ConvertHitObject(original, beatmap)` (`OsuBeatmapConverter.cs:27-75`).
`cpi` is the (deep-cloned) control point info of the beatmap being converted. -/
def convertHitObject (formatVersion : Int32) (cpi : ControlPointInfo) (o : ConvertHitObject) : OsuHitObject :=
  match o.kind with
  | .slider cps expected repeatCount =>
    -- `Slider.Path` setter copies the control points into a path with `OptimiseCatmull = true`
    let path := SliderPath.ofControlPoints cps expected true
    let tdm : F64 :=
      if formatVersion < 8 then F32.toF64 1 / (cpi.difficultyPointAt o.startTime).sliderVelocity else 1
    { kind := .slider { path, repeatCount, tickDistanceMultiplier := tdm, generateTicks := o.generateTicks,
                        sliderVelocityMultiplier := clampSV o.sliderVelocityMultiplier },
      startTime := o.startTime, position := o.position, newCombo := o.newCombo, comboOffset := o.comboOffset }
  | .spinner duration | .hold duration =>
    -- `new Spinner { StartTime = ..., EndTime = endTimeData.EndTime }`: `EndTime` setter stores
    -- `Duration = value - StartTime` with `value = StartTime + Duration` of the convert object.
    let endTime := o.startTime + duration
    { kind := .spinner { duration := endTime - o.startTime }, startTime := o.startTime, position := o.position,
      newCombo := o.newCombo, comboOffset := o.comboOffset }
  | .circle =>
    { kind := .circle, startTime := o.startTime, position := o.position, newCombo := o.newCombo,
      comboOffset := o.comboOffset }

/-- `BeatmapConverter<T>.Convert()`: clone (`ControlPointInfo.DeepClone()`), convert each object,
stable sort by `StartTime` (`BeatmapConverter.cs:73`). -/
def convertBeatmap (d : DecodedBeatmap) : PlayableBeatmap :=
  let cpi := d.controlPoints.deepClone
  let hos := stableSortBy (·.startTime) (d.hitObjects.map (convertHitObject d.formatVersion cpi))
  { formatVersion := d.formatVersion, difficulty := d.difficulty, baseDifficulty := d.difficulty,
    stackLeniency := d.stackLeniency, audioLeadIn := d.audioLeadIn, controlPoints := cpi, breaks := d.breaks, hitObjects := hos }

/-- `WorkingBeatmap.GetPlayableBeatmap(osu ruleset, mods)` (`WorkingBeatmap.cs:276-352`). -/
def getPlayableBeatmap (d : DecodedBeatmap) (mods : List Mod) : DecodeM PlayableBeatmap := do
  -- (`CanConvert()` holds: every Convert* object has a position. No osu! mod implements
  -- `IApplicableToBeatmapConverter`.)
  let mut bm := convertBeatmap d
  for m in mods do
    if let some f := m.applyAfterConversion then bm := f bm
  for m in mods do
    if let some f := m.applyToDifficulty then bm := { bm with difficulty := f bm.difficulty }
  -- processor.PreProcess()
  bm := { bm with hitObjects := OsuBeatmapProcessor.preProcess bm.hitObjects }
  -- ApplyDefaults
  let mut hos : Array OsuHitObject := #[]
  for h in bm.hitObjects do
    hos := hos.push (← applyDefaults bm.controlPoints bm.difficulty h)
  bm := { bm with hitObjects := hos }
  for m in mods do
    if let some f := m.applyToHitObject then bm := { bm with hitObjects := bm.hitObjects.map f }
  -- processor.PostProcess() → ApplyStacking
  bm := { bm with hitObjects := OsuBeatmapProcessor.applyStackingAll bm.formatVersion bm.stackLeniency bm.hitObjects }
  let mut i := 0
  for m in mods do
    if let some f := m.applyToBeatmap then bm ← f i bm
    i := i + 1
  -- a slider path computed on the way ran out of B-spline subdivision fuel: lazer would not have finished (D72)
  if bm.hitObjects.any (fun h => match h.kind with | .slider s => s.path.fuelOut | _ => false) then
    throw pathFuelMsg
  return bm

/-- The full pipeline `.osu` bytes → playable beatmap (or the decoded ruleset id if it is not osu!). -/
inductive LoadResult where
  | decodeError (msg : String)
  | otherRuleset (id : Int32)
  | playableError (msg : String)
  | ok (pb : PlayableBeatmap)

def load (bytes : ByteArray) (mods : List Mod := []) : LoadResult :=
  match LegacyBeatmapDecoder.decode bytes with
  | .error e => .decodeError e
  | .ok d =>
    if d.rulesetId != 0 then .otherRuleset d.rulesetId
    else match getPlayableBeatmap d mods with
      | .error e => .playableError e
      | .ok pb => .ok pb

end OsuModel.Beatmap
