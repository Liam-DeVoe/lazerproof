import OsuModel.Beatmap.Playable
import OsuModel.Beatmap.ModSettings

/-!
# Beatmap-pipeline effects of the osu! mods

`ModConfig.hooks` maps a decoded mod (`ModSettings.lean`) to the `GetPlayableBeatmap` hooks it
implements (`Playable.lean`). Only mods with an effect on the playable beatmap (or on
beatmap-derived mod state) have hooks; every other mod acts only during gameplay.

| mod | hook | source |
|---|---|---|
| ST | after conversion: sliders → `StrictTrackingSlider` | `O/Mods/OsuModStrictTracking.cs:56-74,101-172` |
| EZ | difficulty ×0.5 | `G/Rulesets/Mods/ModEasy.cs:22-28`, `O/Mods/OsuModEasy.cs` |
| HR | difficulty (×1.4 / CS ×1.3, capped at 10); vertical reflection | `G/Rulesets/Mods/ModHardRock.cs:27-30`, `O/Mods/OsuModHardRock.cs:19-32` |
| DA | difficulty overrides | `G/Rulesets/Mods/ModDifficultyAdjust.cs:116-126`, `O/Mods/OsuModDifficultyAdjust.cs:78-84` |
| TP | AR ×0.5; beatmap regeneration (`TargetPractice.lean`) | `O/Mods/OsuModTargetPractice.cs:118-191` |
| MR | reflection | `O/Mods/OsuModMirror.cs:23-42` |
| CL | `ClassicSliderBehaviour` | `O/Mods/OsuModClassic.cs:42-50` |
| HD | `FirstObject`; `TimeFadeIn` | `O/Mods/OsuModHidden.cs:33-51` |
| TC GR DF SI TR WG DP | `FirstObject` | `G/Rulesets/Mods/ModWithVisibilityAdjustment.cs:56-74` |
| FR | `TimePreempt` | `O/Mods/OsuModFreezeFrame.cs:38-87` |
| RD | repositioning (`Random.lean`) | `O/Mods/OsuModRandom.cs` |
| WU WD | ramp bounds | `G/Rulesets/Mods/ModTimeRamp.cs:80-89` |
| AS | preceding end times | `G/Rulesets/Mods/ModAdaptiveSpeed.cs:190-215` |

DT/NC/HT/DC (rate only), NF/SD/PF/AC (fail), RX/AP/AL/SG/SO/MG/RP/BR/BU/BL/FL/AD/MU/NS/SY/BM/TD/SV2
have no beatmap-side effect (NS/SY implement `IApplicableToBeatmap` but only capture visual state).
-/

namespace OsuModel.Beatmap
open OsuModel.Net

namespace Mods

/-! ## Reflections (`O/Utils/OsuHitObjectGenerationUtils.cs:112-170`) -/

/-- `OsuPlayfield.BASE_SIZE` -/
def BASE_W : F32 := 512
def BASE_H : F32 := 384

/-- `PathControlPoint.Position` setter: `if (value == position) return;` (float `==`, so `±0`
differences are ignored and the old bits are kept). -/
def setControlPointPos (old new : Vec2) : Vec2 := if new.eq old then old else new

/-- `new PathControlPoint(position, type)`: the field starts at `(+0, +0)` and is then assigned
through the setter. -/
def newControlPointPos (p : Vec2) : Vec2 := setControlPointPos Vec2.zero p

/-- `modifySlider(slider, f)`: copy the control points (position, type), apply `f`, and assign
`slider.Path = new SliderPath(points, slider.Path.ExpectedDistance.Value)`; the `Path` setter copies
them (`new PathControlPoint(c.Position, c.Type)`) into the slider's own path (`OptimiseCatmull = true`) and `Path.Version` triggers
`updateNestedPositions`. Nested times are not regenerated. -/
def modifySlider (f : Vec2 → Vec2) (h : OsuHitObject) : OsuHitObject :=
  match h.kind with
  | .slider s =>
    let cps := s.path.spec.controlPoints.map fun p =>
      let c := newControlPointPos p.position
      { p with position := setControlPointPos c (f c) }
    let cps := cps.map fun p => { p with position := newControlPointPos p.position }
    let path := SliderPath.ofControlPoints cps s.path.spec.expectedDistance true
    -- the old path's fuel flag is kept: lazer would not have got past computing it (D72)
    let path := { path with fuelOut := path.fuelOut || s.path.fuelOut }
    updateNestedPositions { h with kind := .slider { s with path } }
  | _ => h

/-- `OsuHitObject.Position` setter (the `Slider` override updates nested positions). -/
def setPosition (h : OsuHitObject) (p : Vec2) : OsuHitObject :=
  updateNestedPositions { h with position := p }

/-- `ReflectHorizontallyAlongPlayfield` (`O/Utils/OsuHitObjectGenerationUtils.cs:112-122`) -/
def reflectHorizontally (h : OsuHitObject) : OsuHitObject :=
  let h := setPosition h ⟨BASE_W - h.position.x, h.position.y⟩
  modifySlider (fun p => ⟨-p.x, p.y⟩) h

/-- `ReflectVerticallyAlongPlayfield` (`O/Utils/OsuHitObjectGenerationUtils.cs:128-138`) -/
def reflectVertically (h : OsuHitObject) : OsuHitObject :=
  let h := setPosition h ⟨h.position.x, BASE_H - h.position.y⟩
  modifySlider (fun p => ⟨p.x, -p.y⟩) h

/-! ## Difficulty mods -/

/-- `ModEasy.ApplyToDifficulty` (`G/Rulesets/Mods/ModEasy.cs:21-28`: CS, AR, HP `*= 0.5f`) then
`OsuModEasy.ApplyToDifficulty` (`O/Mods/OsuModEasy.cs:14-19`: OD `*= 0.5f`). -/
def easyDifficulty (d : Difficulty) : Difficulty :=
  { d with circleSize := d.circleSize * 0.5, approachRate := d.approachRate * 0.5,
           drainRate := d.drainRate * 0.5, overallDifficulty := d.overallDifficulty * 0.5 }

/-- `ModHardRock.ADJUST_RATIO = 1.4f` -/
def HR_RATIO : F32 := 1.4
def HR_CS_RATIO : F32 := 1.3

/-- `ModHardRock.ApplyToDifficulty` (`G/Rulesets/Mods/ModHardRock.cs:25-28`, HP) then
`OsuModHardRock.ApplyToDifficulty` (`O/Mods/OsuModHardRock.cs:25-32`, OD, CS ×1.3f, AR):
`Math.Min(x * ratio, 10.0f)`. -/
def hardRockDifficulty (d : Difficulty) : Difficulty :=
  let hp := F32.min (d.drainRate * HR_RATIO) 10
  let od := F32.min (d.overallDifficulty * HR_RATIO) 10
  let cs := F32.min (d.circleSize * HR_CS_RATIO) 10
  let ar := F32.min (d.approachRate * HR_RATIO) 10
  { d with drainRate := hp, overallDifficulty := od, circleSize := cs, approachRate := ar }

/-- `OsuModDifficultyAdjust.ApplySettings` (`O/Mods/OsuModDifficultyAdjust.cs:78-84`) after
`ModDifficultyAdjust.ApplySettings` (`G/Rulesets/Mods/ModDifficultyAdjust.cs:122-126`): HP, OD, then CS, AR. -/
def difficultyAdjust (m : ModConfig) (d : Difficulty) : Difficulty :=
  let d := match m.getOptFloat "drain_rate" with | some v => { d with drainRate := v } | none => d
  let d := match m.getOptFloat "overall_difficulty" with | some v => { d with overallDifficulty := v } | none => d
  let d := match m.getOptFloat "circle_size" with | some v => { d with circleSize := v } | none => d
  match m.getOptFloat "approach_rate" with | some v => { d with approachRate := v } | none => d

/-! ## Strict Tracking -/

/-- `new StrictTrackingSlider(original)`: a fresh `Slider` that copies `StartTime`, `Path`,
`RepeatCount`, `Position`, `NewCombo`, `ComboOffset`, `TickDistanceMultiplier` and
`SliderVelocityMultiplier`. `GenerateTicks` is **not** copied (default `true`), and its tail is a
`StrictTrackingSliderTailCircle`. The `Path` setter rebuilds the same control points and expected
distance into the new slider's path (`OptimiseCatmull = true`, as the original's). -/
def strictTrackingSlider (h : OsuHitObject) : OsuHitObject :=
  match h.kind with
  | .slider s =>
    { kind := .slider { path := SliderPath.compute s.path.spec, repeatCount := s.repeatCount,
                        tickDistanceMultiplier := s.tickDistanceMultiplier,
                        sliderVelocityMultiplier := s.sliderVelocityMultiplier,
                        strictTracking := true },
      startTime := h.startTime, position := h.position, newCombo := h.newCombo, comboOffset := h.comboOffset }
  | _ => h

def strictTracking (pb : PlayableBeatmap) : PlayableBeatmap :=
  if pb.hitObjects.size == 0 then pb else { pb with hitObjects := pb.hitObjects.map strictTrackingSlider }

/-! ## Classic -/

/-- `OsuModClassic.ApplyToHitObject` (`O/Mods/OsuModClassic.cs:42-50`):
`slider.ClassicSliderBehaviour = NoSliderHeadAccuracy.Value`, whose setter also sets `HeadCircle` and
`TailCircle` (`O/Objects/Slider.cs:113-121`). -/
def classicHitObject (v : Bool) (h : OsuHitObject) : OsuHitObject :=
  match h.kind with
  | .slider s =>
    { h with kind := .slider { s with classicSliderBehaviour := v },
             nested := h.nested.map fun n => match n.kind with
               | .head | .tail => { n with classicSliderBehaviour := v }
               | _ => n }
  | _ => h

/-! ## Mirror -/

/-- `OsuModMirror.ApplyToHitObject` (`O/Mods/OsuModMirror.cs:23-42`); undefined enum values hit no case. -/
def mirror (reflection : Int32) (h : OsuHitObject) : OsuHitObject :=
  match reflection with
  | 0 => reflectHorizontally h
  | 1 => reflectVertically h
  | 2 => reflectVertically (reflectHorizontally h)
  | _ => h

/-! ## `ModWithVisibilityAdjustment.ApplyToBeatmap`: `FirstObject` -/

/-- `getFirstAdjustableObjectRecursive(beatmap.HitObjects)` (`G/Rulesets/Mods/ModWithVisibilityAdjustment.cs:56-74`;
HD/TC override at `O/Mods/OsuModHidden.cs:33`, `O/Mods/OsuModTraceable.cs:30`). `skipSpinners` is the HD/TC override
`IsFirstAdjustableObject(h) => !(h is Spinner || h is SpinnerTick)` (`SpinnerBonusTick` derives
from `SpinnerTick`). -/
def firstAdjustableObject (pb : PlayableBeatmap) (skipSpinners : Bool) : Option ObjRef := Id.run do
  let mut i := 0
  for h in pb.hitObjects do
    if !(skipSpinners && h.isSpinner) then return some { index := i, epoch := pb.epoch }
    let mut j := 0
    for n in h.nested do
      let isSpinTick := match n.kind with | .spinnerTick | .spinnerBonusTick => true | _ => false
      if !(skipSpinners && isSpinTick) then return some { index := i, nested := some j, epoch := pb.epoch }
      j := j + 1
    i := i + 1
  return none

def recordFirstObject (skipSpinners : Bool) (idx : Nat) (pb : PlayableBeatmap) : PlayableBeatmap :=
  { pb with modStates := pb.modStates.push (idx, .firstObject (firstAdjustableObject pb skipSpinners)) }

/-! ## Hidden -/

/-- `OsuModHidden.FADE_IN_DURATION_MULTIPLIER` -/
def FADE_IN_DURATION_MULTIPLIER : F64 := 0.4

/-- `OsuModHidden.ApplyToBeatmap` / `applyFadeInAdjustment` (`O/Mods/OsuModHidden.cs:35-51`): non-sliders (including every nested object) get
`TimeFadeIn = TimePreempt * 0.4`. -/
def hiddenFadeIn (h : OsuHitObject) : OsuHitObject :=
  let h := if h.isSlider then h else { h with timeFadeIn := h.timePreempt * FADE_IN_DURATION_MULTIPLIER }
  { h with nested := h.nested.map fun n => { n with timeFadeIn := n.timePreempt * FADE_IN_DURATION_MULTIPLIER } }

/-! ## Freeze Frame -/

/-- `OsuModFreezeFrame.ApplyToBeatmap`: `TimePreempt += StartTime - lastNewComboTime` for every
non-spinner, recursively into nested objects except slider ticks and all but the first three
repeats. (Does nothing if there are no objects.) -/
def freezeFrame (pb : PlayableBeatmap) : PlayableBeatmap := Id.run do
  let mut lastNC : F64 := 0
  let mut out : Array OsuHitObject := #[]
  for h in pb.hitObjects do
    if h.newCombo then lastNC := h.startTime
    let h := if h.isSpinner then h else { h with timePreempt := h.timePreempt + (h.startTime - lastNC) }
    let mut repeatCount : Nat := 0
    let mut ns : Array NestedObject := #[]
    for n in h.nested do
      match n.kind with
      | .tick => ns := ns.push n
      | .repeat =>
        if repeatCount > 2 then ns := ns.push n
        else
          ns := ns.push { n with timePreempt := n.timePreempt + (n.startTime - lastNC) }
          repeatCount := repeatCount + 1
      | _ => ns := ns.push { n with timePreempt := n.timePreempt + (n.startTime - lastNC) }
    out := out.push { h with nested := ns }
  return { pb with hitObjects := out }

/-! ## Time ramp / adaptive speed state -/

/-- `Enumerable.Max(selector)` over doubles (System.Linq 10.0, `MaxFloat`; BCL, no checkout: NaN is ordered
below every other value, ties keep the first). Requires a non-empty array. Only NaN end times
(not produced by the decoder) depend on the NaN rule. -/
def linqMaxF64 (xs : Array F64) : F64 := Id.run do
  let mut i := 0
  let mut v : F64 := xs[0]!
  while v.isNaN && i + 1 < xs.size do
    i := i + 1
    v := xs[i]!
  for j in [i+1:xs.size] do
    if v < xs[j]! then v := xs[j]!
  return v

/-- `IBeatmap.GetLastObjectTime()` = `HitObjects.Max(h => h.GetEndTime())` (`G/Beatmaps/IBeatmap.cs:179`) -/
def lastObjectTime (pb : PlayableBeatmap) : F64 := linqMaxF64 (pb.hitObjects.map (·.endTime))

/-- `ModTimeRamp.FINAL_RATE_PROGRESS = 0.75f` -/
def FINAL_RATE_PROGRESS : F32 := 0.75

/-- `ModTimeRamp.ApplyToBeatmap` (`G/Rulesets/Mods/ModTimeRamp.cs:80-89`); `FINAL_RATE_PROGRESS` is the
double constant `0.75f` (`:22`). -/
def timeRamp (idx : Nat) (pb : PlayableBeatmap) : PlayableBeatmap :=
  let first := if h : 0 < pb.hitObjects.size then pb.hitObjects[0].startTime else 0
  let lastEnd := if pb.hitObjects.size > 0 then lastObjectTime pb else 0
  let fin := first + F32.toF64 FINAL_RATE_PROGRESS * (lastEnd - first)
  { pb with modStates := pb.modStates.push (idx, .timeRamp first fin) }

/-- `ModAdaptiveSpeed.ApplyToBeatmap` (`G/Rulesets/Mods/ModAdaptiveSpeed.cs:190-215`): objects (pre-order, nested included) whose `HitWindows`
is not `HitWindows.Empty` (circles and slider heads), `endTimes` = sorted distinct end times
(`Order().Distinct()`), and for each object the end time preceding its own (`BinarySearch`). -/
def adaptiveSpeed (idx : Nat) (pb : PlayableBeatmap) : PlayableBeatmap := Id.run do
  let mut objs : Array (ObjRef × F64) := #[]
  let mut i := 0
  for h in pb.hitObjects do
    let hasWindows := match h.hitWindows with | some .empty => false | _ => true
    if hasWindows then objs := objs.push ({ index := i, epoch := pb.epoch }, h.endTime)
    let mut j := 0
    for n in h.nested do
      let hasW := match n.hitWindows with | .empty => false | _ => true
      -- nested objects are not IHasDuration: GetEndTime() = StartTime
      if hasW then objs := objs.push ({ index := i, nested := some j, epoch := pb.epoch }, n.startTime)
      j := j + 1
    i := i + 1
  let sorted := stableSortBy id (objs.map (·.2))
  let mut endTimes : Array F64 := #[]
  for t in sorted do
    if endTimes.size == 0 || compareF64 endTimes.back! t != 0 then endTimes := endTimes.push t
  let mut entries : Array (ObjRef × F64) := #[]
  for (r, t) in objs do
    let b := binarySearchF64 endTimes t
    let index := (if b < 0 then -b - 1 else b) - 1
    if index ≥ 0 then entries := entries.push (r, endTimes[index.toNat]!)
  return { pb with modStates := pb.modStates.push (idx, .precedingEndTimes entries) }

end Mods

open Mods in
/-- The `GetPlayableBeatmap` hooks of a decoded osu! mod. -/
def ModConfig.hooks (m : ModConfig) : Mod :=
  if !m.known then { acronym := m.acronym } else
  match m.acronym with
  | "EZ" => { acronym := "EZ", applyToDifficulty := some easyDifficulty }
  | "HR" => { acronym := "HR", applyToDifficulty := some hardRockDifficulty, applyToHitObject := some reflectVertically }
  | "DA" => { acronym := "DA", applyToDifficulty := some (difficultyAdjust m) }
  | "ST" => { acronym := "ST", applyAfterConversion := some strictTracking }
  | "MR" => { acronym := "MR", applyToHitObject := some (mirror (m.getInt "reflection")) }
  | "CL" => { acronym := "CL", applyToHitObject := some (classicHitObject (m.getBool "no_slider_head_accuracy")) }
  | "HD" => { acronym := "HD", applyToBeatmap := some fun i pb =>
                pure { (recordFirstObject true i pb) with hitObjects := pb.hitObjects.map hiddenFadeIn } }
  | "TC" => { acronym := "TC", applyToBeatmap := some fun i pb => pure (recordFirstObject true i pb) }
  | "GR" | "DF" | "SI" | "TR" | "WG" | "DP" =>
    { acronym := m.acronym, applyToBeatmap := some fun i pb => pure (recordFirstObject false i pb) }
  | "FR" => { acronym := "FR", applyToBeatmap := some fun _ pb => pure (freezeFrame pb) }
  | "WU" | "WD" => { acronym := m.acronym, applyToBeatmap := some fun i pb => pure (timeRamp i pb) }
  | "AS" => { acronym := "AS", applyToBeatmap := some fun i pb => pure (adaptiveSpeed i pb) }
  | "TP" => { acronym := "TP", applyToDifficulty := some fun d => { d with approachRate := d.approachRate * 0.5 } }
  | _ => { acronym := m.acronym }

end OsuModel.Beatmap
