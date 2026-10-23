import OsuModel.Beatmap.Vector2
import OsuModel.Beatmap.ControlPoints

/-!
# Data types shared by the decoder and the converter
-/

namespace OsuModel.Beatmap
open OsuModel.Net

/-- `SplineType` + `PathType.Degree` (`osu.Game/Rulesets/Objects/Types/PathType.cs`).
`bspline none` is `PathType.BEZIER`, `bspline (some n)` is `PathType.BSpline(n)`. -/
inductive PathType where
  | catmull
  | bspline (degree : Option Int32)
  | linear
  | perfectCurve
deriving Inhabited, Repr, BEq

/-- `PathControlPoint` (position relative to the slider head, optional segment type). -/
structure PathControlPoint where
  position : Vec2
  type : Option PathType := none
deriving Inhabited, Repr

/-- `BeatmapDifficulty` (`osu.Game/Beatmaps/BeatmapDifficulty.cs`): HP/CS/OD/AR are `float`,
slider multiplier / tick rate `double`. Defaults: 5, 5, 5, 5, 1.4, 1. -/
structure Difficulty where
  drainRate : F32 := 5
  circleSize : F32 := 5
  overallDifficulty : F32 := 5
  approachRate : F32 := 5
  sliderMultiplier : F64 := 1.4
  sliderTickRate : F64 := 1
deriving Inhabited, Repr

/-- The legacy (`Convert*`) hit object kinds produced by `ConvertHitObjectParser`
(`osu.Game/Rulesets/Objects/Legacy/Convert*.cs`). -/
inductive ConvertKind where
  /-- `ConvertHitCircle` -/
  | circle
  /-- `ConvertSlider`: control points, `SliderPath.ExpectedDistance`, `RepeatCount`. -/
  | slider (controlPoints : Array PathControlPoint) (expectedDistance : Option F64) (repeatCount : Int32)
  /-- `ConvertSpinner` (`Duration`) -/
  | spinner (duration : F64)
  /-- `ConvertHold` (`Duration`; only produced for mania hold bits, converted to a `Spinner`) -/
  | hold (duration : F64)
deriving Inhabited, Repr

/-- `ConvertHitObject` as stored in the decoded beatmap. -/
structure ConvertHitObject where
  startTime : F64
  position : Vec2
  newCombo : Bool
  comboOffset : Int32
  kind : ConvertKind
  /-- `IHasGenerateTicks.GenerateTicks` (sliders; set by the decoder's `applyDefaults`). -/
  generateTicks : Bool := true
  /-- `IHasSliderVelocity.SliderVelocityMultiplier` (sliders; unclamped bindable in `ConvertSlider`). -/
  sliderVelocityMultiplier : F64 := 1
deriving Inhabited, Repr

/-- `BreakPeriod(start, end)` -/
structure BreakPeriod where
  startTime : F64
  endTime : F64
deriving Inhabited, Repr

/-- The decoded `Beatmap` (the parts relevant to osu! gameplay). -/
structure DecodedBeatmap where
  /-- `BeatmapVersion` (= format version) -/
  formatVersion : Int32
  /-- `BeatmapInfo.Ruleset.OnlineID` -/
  rulesetId : Int32 := 0
  difficulty : Difficulty := {}
  stackLeniency : F32 := 0.7
  /-- `Beatmap.AudioLeadIn` (`AudioLeadIn:` in `[General]`, an `int` widened to `double`) -/
  audioLeadIn : F64 := 0
  controlPoints : ControlPointInfo := {}
  breaks : Array BreakPeriod := #[]
  hitObjects : Array ConvertHitObject := #[]
deriving Inhabited, Repr

end OsuModel.Beatmap
