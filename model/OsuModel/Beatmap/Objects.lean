import OsuModel.Beatmap.SliderEventGenerator

/-!
# osu! hit objects and `ApplyDefaults`

Mirrors `osu.Game.Rulesets.Osu/Objects/*.cs` and `osu.Game/Rulesets/Objects/HitObject.cs`.
A C# `OsuHitObject` with its bindables/caches is represented by an immutable record holding the
*stored* state; derived properties (`EndTime`, `EndPosition`, `StackOffset`, `Radius`, …) are
functions with the same formulas as the C# getters.
-/

namespace OsuModel.Beatmap
open OsuModel.Net

/-! ## Difficulty ranges (`osu.Game/Beatmaps/IBeatmapDifficultyInfo.cs:25-46`) -/

/-- `IBeatmapDifficultyInfo.DifficultyRange(double difficulty)` = `(difficulty - 5) / 5` -/
def difficultyRange1 (d : F64) : F64 := (d - 5) / 5

/-- `IBeatmapDifficultyInfo.DifficultyRange(difficulty, min, mid, max)` -/
def difficultyRange (d min mid max : F64) : F64 :=
  if (5 : F64) < d then mid + (max - mid) * difficultyRange1 d
  else if d < 5 then mid + (mid - min) * difficultyRange1 d
  else mid

/-- `CalculateScaleFromCircleSize(circleSize, applyFudge)` (`LegacyRulesetExtensions.cs:46-59`):
`(float)(1.0f - 0.7f * DifficultyRange(circleSize)) / 2 * (applyFudge ? 1.00041f : 1)`. -/
def calculateScaleFromCircleSize (cs : F32) (applyFudge : Bool := false) : F32 :=
  let inner : F64 := F32.toF64 1.0 - F32.toF64 0.7 * difficultyRange1 (F32.toF64 cs)
  inner.toF32 / 2 * (if applyFudge then (1.00041 : F32) else 1)

/-! ## Hit windows -/

/-- The hit windows of an object: `HitWindows.Empty` or `OsuHitWindows` after
`SetDifficulty(OD)` (`O/Scoring/OsuHitWindows.cs:36-41`). -/
inductive HitWindows where
  | empty
  | osu (great ok meh : F64)
deriving Inhabited, Repr

/-- `OsuHitWindows.MISS_WINDOW` -/
def MISS_WINDOW : F64 := 400

/-- `OsuHitWindows.SetDifficulty(difficulty)`:
`great = Math.Floor(DifficultyRange(od, 80, 50, 20)) - 0.5` etc. -/
def osuHitWindows (od : F64) : HitWindows :=
  .osu (F64.floor (difficultyRange od 80 50 20) - 0.5)
       (F64.floor (difficultyRange od 140 100 60) - 0.5)
       (F64.floor (difficultyRange od 200 150 100) - 0.5)

/-- `HitWindows.WindowFor(HitResult.Miss)` -/
def HitWindows.missWindow : HitWindows → F64
  | .empty => 0
  | .osu .. => MISS_WINDOW

/-! ## Object records -/

/-- Kinds of nested objects. -/
inductive NestedKind where
  /-- `SliderHeadCircle` -/
  | head
  /-- `SliderTick` -/
  | tick
  /-- `SliderRepeat` -/
  | repeat
  /-- `SliderTailCircle` -/
  | tail
  /-- `SpinnerTick` -/
  | spinnerTick
  /-- `SpinnerBonusTick` -/
  | spinnerBonusTick
deriving Inhabited, Repr, BEq

/-- A nested `OsuHitObject` (all kinds share one record; unused fields keep their defaults). -/
structure NestedObject where
  kind : NestedKind
  startTime : F64
  position : Vec2 := Vec2.zero
  stackHeight : Int32 := 0
  scale : F32 := 1
  timePreempt : F64 := 600
  timeFadeIn : F64 := 400
  hitWindows : HitWindows := .empty
  /-- `SliderTick.PathProgress` / `SliderRepeat.PathProgress` -/
  pathProgress : F64 := 0
  /-- `SliderTick.SpanIndex` -/
  spanIndex : Int32 := 0
  /-- `SliderTick.SpanStartTime` -/
  spanStartTime : F64 := 0
  /-- `SliderEndCircle.RepeatIndex` -/
  repeatIndex : Int32 := 0
  /-- `SpinnerTick.SpinnerDuration` -/
  spinnerDuration : F64 := 0
  /-- `SliderHeadCircle/SliderTailCircle.ClassicSliderBehaviour` -/
  classicSliderBehaviour : Bool := false
  /-- `HitObject.Kiai` -/
  kiai : Bool := false
  /-- the tail is a `StrictTrackingSliderTailCircle` (`OsuModStrictTracking.cs:81-94`) -/
  strictTrackingTail : Bool := false
deriving Inhabited, Repr

/-- Slider-specific state (`O/Objects/Slider.cs`). -/
structure SliderData where
  /-- `Slider.Path` (`OptimiseCatmull = true`) with its computed cache. -/
  path : SliderPath
  repeatCount : Int32
  velocity : F64 := 0
  tickDistance : F64 := 0
  tickDistanceMultiplier : F64 := 1
  /-- `SliderVelocityMultiplierBindable` (clamped to [0.1, 10]) -/
  sliderVelocityMultiplier : F64 := 1
  generateTicks : Bool := true
  classicSliderBehaviour : Bool := false
  /-- a `StrictTrackingSlider` (`OsuModStrictTracking.cs:101-172`): its tail is a
  `StrictTrackingSliderTailCircle` -/
  strictTracking : Bool := false
deriving Inhabited, Repr

/-- Spinner-specific state (`O/Objects/Spinner.cs`). -/
structure SpinnerData where
  duration : F64
  spinsRequired : Int32 := 1
  maximumBonusSpins : Int32 := 1
deriving Inhabited, Repr

inductive ObjectKind where
  | circle
  | slider (s : SliderData)
  | spinner (s : SpinnerData)
deriving Inhabited, Repr

/-- A top-level `OsuHitObject` (`HitCircle`, `Slider` or `Spinner`). Defaults are the C# field
initialisers (`TimePreempt = 600`, `TimeFadeIn = 400`, `Scale = 1`). -/
structure OsuHitObject where
  kind : ObjectKind
  startTime : F64
  position : Vec2
  stackHeight : Int32 := 0
  scale : F32 := 1
  timePreempt : F64 := 600
  timeFadeIn : F64 := 400
  newCombo : Bool := false
  comboOffset : Int32 := 0
  comboIndex : Int32 := 0
  comboIndexWithOffsets : Int32 := 0
  indexInCurrentCombo : Int32 := 0
  lastInCombo : Bool := false
  /-- `HitObject.Kiai` (`EffectPointAt(StartTime + 1).KiaiMode`, set by `ApplyDefaults`) -/
  kiai : Bool := false
  /-- `null` before the first `ApplyDefaults` -/
  hitWindows : Option HitWindows := none
  nested : Array NestedObject := #[]
deriving Inhabited, Repr

/-- `OsuHitObject.OBJECT_RADIUS = 64f` -/
def OBJECT_RADIUS : F32 := 64
/-- `OsuHitObject.BASE_SCORING_DISTANCE = 100f` -/
def BASE_SCORING_DISTANCE : F32 := 100

namespace SliderData
/-- `IHasRepeats.SpanCount() => RepeatCount + 1` -/
def spanCount (s : SliderData) : Int32 := s.repeatCount + 1
/-- `ProgressAt(progress)` (`IHasPathWithRepeats.cs:24-38`) -/
def progressAt (s : SliderData) (progress : F64) : F64 :=
  let p := fmod1 (progress * F64.ofInt32 s.spanCount)
  let spanAt := F64.toInt32 (progress * F64.ofInt32 s.spanCount)
  if spanAt % 2 == 1 then 1 - p else p
/-- `CurvePositionAt(progress) => Path.PositionAt(ProgressAt(progress))` -/
def curvePositionAt (s : SliderData) (progress : F64) : Vec2 := s.path.positionAt (s.progressAt progress)
end SliderData

namespace OsuHitObject

/-- `HitObjectExtensions.GetEndTime()`: `Slider.EndTime => StartTime + SpanCount * Path.Distance / Velocity`
(`Slider.cs:28`), `Spinner.EndTime => StartTime + Duration`, otherwise `StartTime`. -/
def endTime (h : OsuHitObject) : F64 :=
  match h.kind with
  | .slider s => h.startTime + F64.ofInt32 s.spanCount * s.path.distance / s.velocity
  | .spinner s => h.startTime + s.duration
  | .circle => h.startTime

/-- `Slider.Duration => EndTime - StartTime` / `Spinner.Duration` -/
def duration (h : OsuHitObject) : F64 :=
  match h.kind with
  | .spinner s => s.duration
  | _ => h.endTime - h.startTime

/-- `Slider.SpanDuration => Duration / SpanCount` -/
def spanDuration (h : OsuHitObject) : F64 :=
  match h.kind with
  | .slider s => h.duration / F64.ofInt32 s.spanCount
  | _ => h.duration

/-- `EndPosition`: `Slider.EndPosition => Position + CurvePositionAt(1)` (`Slider.cs:41`). -/
def endPosition (h : OsuHitObject) : Vec2 :=
  match h.kind with
  | .slider s => h.position + s.curvePositionAt 1
  | _ => h.position

/-- `StackOffset => new Vector2(StackHeight * Scale * -6.4f)`; zero for spinners (`Spinner.cs:59`). -/
def stackOffset (h : OsuHitObject) : Vec2 :=
  match h.kind with
  | .spinner _ => Vec2.zero
  | _ => Vec2.splat (F32.ofInt32 h.stackHeight * h.scale * (-6.4 : F32))

def stackedPosition (h : OsuHitObject) : Vec2 := h.position + h.stackOffset
def stackedEndPosition (h : OsuHitObject) : Vec2 := h.endPosition + h.stackOffset
/-- `Radius => OBJECT_RADIUS * Scale` (float product, widened to double) -/
def radius (h : OsuHitObject) : F64 := F32.toF64 (OBJECT_RADIUS * h.scale)
def isSpinner (h : OsuHitObject) : Bool := match h.kind with | .spinner _ => true | _ => false
def isSlider (h : OsuHitObject) : Bool := match h.kind with | .slider _ => true | _ => false
def isCircle (h : OsuHitObject) : Bool := match h.kind with | .circle => true | _ => false

/-- `MaximumJudgementOffset => HitWindows?.WindowFor(HitResult.Miss) ?? 0` -/
def maximumJudgementOffset (h : OsuHitObject) : F64 := (h.hitWindows.map (·.missWindow)).getD 0

/-- Setting `StackHeight` propagates to nested objects (`OsuHitObject.cs:158-168`). -/
def setStackHeight (h : OsuHitObject) (v : Int32) : OsuHitObject :=
  { h with stackHeight := v, nested := h.nested.map fun n => { n with stackHeight := v } }

end OsuHitObject

namespace NestedObject
def stackOffset (n : NestedObject) : Vec2 := Vec2.splat (F32.ofInt32 n.stackHeight * n.scale * (-6.4 : F32))
def stackedPosition (n : NestedObject) : Vec2 := n.position + n.stackOffset
def radius (n : NestedObject) : F64 := F32.toF64 (OBJECT_RADIUS * n.scale)
/-- `SpinnerTick.MaximumJudgementOffset => SpinnerDuration`; otherwise the miss window. -/
def maximumJudgementOffset (n : NestedObject) : F64 :=
  match n.kind with
  | .spinnerTick | .spinnerBonusTick => n.spinnerDuration
  | _ => n.hitWindows.missWindow
end NestedObject

/-! ## `ApplyDefaults` -/

/-- `OsuHitObject.PREEMPT_RANGE = (1800, 1200, 450)` → `TimePreempt = (int)DifficultyRange(AR, 1800, 1200, 450)`. -/
def timePreemptFor (ar : F32) : F64 := F64.ofInt32 (F64.toInt32 (difficultyRange (F32.toF64 ar) 1800 1200 450))

/-- `TimeFadeIn = 400 * Math.Min(1, TimePreempt / PREEMPT_MIN)` -/
def timeFadeInFor (preempt : F64) : F64 := 400 * F64.min 1 (preempt / 450)

/-- The common part of `OsuHitObject.ApplyDefaultsToSelf` (`O/Objects/OsuHitObject.cs:170-183`)
plus `HitObject.ApplyDefaultsToSelf` (`HitWindows ??= CreateHitWindows(); SetDifficulty(OD)`). -/
structure CommonDefaults where
  timePreempt : F64
  timeFadeIn : F64
  scale : F32
deriving Inhabited

def commonDefaults (d : Difficulty) : CommonDefaults :=
  let p := timePreemptFor d.approachRate
  { timePreempt := p, timeFadeIn := timeFadeInFor p, scale := calculateScaleFromCircleSize d.circleSize true }

/-- `LegacyRulesetExtensions.GetPrecisionAdjustedBeatLength(hasSliderVelocity, timingControlPoint, "osu")`
(`LegacyRulesetExtensions.cs:17-41`). -/
def getPrecisionAdjustedBeatLength (sliderVelocityMultiplier : F64) (tp : TimingPoint) : F64 :=
  let sliderVelocityAsBeatLength : F64 := -100 / sliderVelocityMultiplier
  let bpmMultiplier : F64 :=
    if sliderVelocityAsBeatLength < 0 then
      let v : F32 := (-sliderVelocityAsBeatLength).toF32
      let c : F32 := if v < 10 then 10 else if (1000 : F32) < v then 1000 else v
      F32.toF64 c / 100.0
    else 1
  tp.beatLength * bpmMultiplier

/-- `ApplyDefaults` of a nested object (no grandchildren): `OsuHitObject.ApplyDefaultsToSelf`
followed by the kind-specific override. `sliderStart`/`spanDuration` are the parent's. -/
def applyNestedDefaults (cpi : ControlPointInfo) (d : Difficulty) (sliderStart spanDuration : F64) (n : NestedObject) : NestedObject :=
  let c := commonDefaults d
  let n := { n with timePreempt := c.timePreempt, timeFadeIn := c.timeFadeIn, scale := c.scale,
                    kiai := (cpi.effectPointAt (n.startTime + 1)).kiai }
  match n.kind with
  | .head =>
    -- `SliderHeadCircle : HitCircle`: `OsuHitWindows`
    { n with hitWindows := osuHitWindows (F32.toF64 d.overallDifficulty) }
  | .repeat | .tail =>
    -- `SliderEndCircle.ApplyDefaultsToSelf` (`SliderEndCircle.cs:28-45`), `HitWindows.Empty`
    if n.repeatIndex > 0 then { n with timeFadeIn := 0, timePreempt := spanDuration * 2 }
    else { n with timePreempt := n.timePreempt + (n.startTime - sliderStart) }
  | .tick =>
    -- `SliderTick.ApplyDefaultsToSelf` (`SliderTick.cs:18-32`)
    let offset : F64 := if n.spanIndex > 0 then 200 else n.timePreempt * F32.toF64 (0.66 : F32)
    { n with timePreempt := (n.startTime - n.spanStartTime) / 2 + offset }
  | .spinnerTick | .spinnerBonusTick => n

/-- `nestedHitObjects.Sort((h1, h2) => h1.StartTime.CompareTo(h2.StartTime))` (`HitObject.cs:130`). -/
def sortNested (ns : Array NestedObject) : Array NestedObject :=
  listSort (fun a b => compareF64 a.startTime b.startTime) ns

/-- `Slider.CreateNestedHitObjects` (`Slider.cs:170-227`); `h` has had `ApplyDefaultsToSelf`. -/
def sliderNested (h : OsuHitObject) (s : SliderData) : DecodeM (Array NestedObject) := do
  let events ← SliderEventGenerator.generate h.startTime h.spanDuration s.velocity s.tickDistance s.path.distance s.spanCount
  let mut out : Array NestedObject := #[]
  for e in events do
    match e.type with
    | .tick =>
      out := out.push { kind := .tick, spanIndex := e.spanIndex, spanStartTime := e.spanStartTime, startTime := e.time,
                        position := h.position + s.path.positionAt e.pathProgress, pathProgress := e.pathProgress,
                        stackHeight := h.stackHeight }
    | .head =>
      out := out.push { kind := .head, startTime := e.time, position := h.position, stackHeight := h.stackHeight,
                        classicSliderBehaviour := s.classicSliderBehaviour }
    | .tail =>
      out := out.push { kind := .tail, repeatIndex := e.spanIndex, startTime := e.time, position := h.endPosition,
                        stackHeight := h.stackHeight, classicSliderBehaviour := s.classicSliderBehaviour,
                        strictTrackingTail := s.strictTracking }
    | .repeat =>
      out := out.push { kind := .repeat, repeatIndex := e.spanIndex,
                        startTime := h.startTime + F64.ofInt32 (e.spanIndex + 1) * h.spanDuration,
                        position := h.position + s.path.positionAt e.pathProgress, stackHeight := h.stackHeight,
                        pathProgress := e.pathProgress }
    | .legacyLastTick => pure ()   -- ignored by `Slider`
  return out

/-- `Spinner.ApplyDefaultsToSelf` (`Spinner.cs:61-80`) -/
def spinnerDefaults (d : Difficulty) (s : SpinnerData) : SpinnerData :=
  let od := F32.toF64 d.overallDifficulty
  let minRps := difficultyRange od 90 150 225 / 60
  let maxRps := difficultyRange od 250 380 430 / 60
  let secondsDuration := s.duration / 1000
  let duration_error : F64 := 0.0001
  let spinsRequired := F64.toInt32 (minRps * secondsDuration + duration_error)
  let bonus := F64.toInt32 (maxRps * secondsDuration + duration_error) - spinsRequired - 2
  { s with spinsRequired, maximumBonusSpins := if bonus < 0 then 0 else bonus }

/-- `Spinner.CreateNestedHitObjects` (`Spinner.cs:82-96`) -/
def spinnerNested (h : OsuHitObject) (s : SpinnerData) : Array NestedObject := Id.run do
  let totalSpins : Int32 := s.maximumBonusSpins + s.spinsRequired + 2
  let mut out := #[]
  for iN in [0:totalSpins.toNatClampNeg] do
    let i : Int32 := Int32.ofNat iN
    let startTime := h.startTime + F32.toF64 (F32.ofInt32 (i + 1) / F32.ofInt32 totalSpins) * s.duration
    let kind := if i < s.spinsRequired + 2 then NestedKind.spinnerTick else .spinnerBonusTick
    out := out.push { kind, startTime, spinnerDuration := s.duration }
  return out

/-- `HitObject.ApplyDefaults(controlPointInfo, difficulty)` for a top-level osu! object
(`HitObject.cs:105-148`): self defaults, nested creation, combo binding, nested sort, nested defaults. -/
def applyDefaults (cpi : ControlPointInfo) (d : Difficulty) (h0 : OsuHitObject) : DecodeM OsuHitObject := do
  let c := commonDefaults d
  let hw : HitWindows := match h0.hitWindows with
    | some w => w
    | none => match h0.kind with
      | .circle => osuHitWindows (F32.toF64 d.overallDifficulty)
      | _ => .empty
  -- `HitWindows?.SetDifficulty(OD)` recomputes OsuHitWindows
  let hw := match hw with | .osu .. => osuHitWindows (F32.toF64 d.overallDifficulty) | w => w
  -- `Kiai = controlPointInfo.EffectPointAt(StartTime + control_point_leniency).KiaiMode` (`HitObject.cs:158`)
  let h : OsuHitObject := { h0 with timePreempt := c.timePreempt, timeFadeIn := c.timeFadeIn, scale := c.scale,
                                    hitWindows := some hw, kiai := (cpi.effectPointAt (h0.startTime + 1)).kiai }
  -- kind-specific ApplyDefaultsToSelf
  let h ← match h.kind with
    | .circle => pure h
    | .spinner s => pure { h with kind := .spinner (spinnerDefaults d s) }
    | .slider s =>
      -- `Slider.ApplyDefaultsToSelf` (`Slider.cs:156-168`)
      let tp := cpi.timingPointAt h.startTime
      let velocity := F32.toF64 BASE_SCORING_DISTANCE * d.sliderMultiplier / getPrecisionAdjustedBeatLength s.sliderVelocityMultiplier tp
      let scoringDistance := velocity * tp.beatLength
      let tickDistance := if s.generateTicks then scoringDistance / d.sliderTickRate * s.tickDistanceMultiplier else F64.posInf
      pure { h with kind := .slider { s with velocity, tickDistance } }
  -- CreateNestedHitObjects
  let nested ← match h.kind with
    | .circle => pure #[]
    | .spinner s => pure (spinnerNested h s)
    | .slider s => sliderNested h s
  let nested := sortNested nested
  let nested := nested.map (applyNestedDefaults cpi d h.startTime h.spanDuration)
  return { h with nested }

end OsuModel.Beatmap
