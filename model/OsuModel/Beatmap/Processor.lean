import OsuModel.Beatmap.Objects

/-!
# `OsuBeatmapProcessor` (`osu.Game.Rulesets.Osu/Beatmaps/OsuBeatmapProcessor.cs`) and
`BeatmapProcessor` (`osu.Game/Beatmaps/BeatmapProcessor.cs`): combo information and stacking.
-/

namespace OsuModel.Beatmap
open OsuModel.Net

namespace OsuBeatmapProcessor

/-- `OsuBeatmapProcessor.STACK_DISTANCE = 3` (compared as `float`) -/
def STACK_DISTANCE : F32 := 3

/-- `OsuHitObject.UpdateComboInformation(lastObj)` (`O/Objects/OsuHitObject.cs:185-208`).
Returns the updated previous object (its `LastInCombo` may be set) and the updated object. -/
def updateComboInformation (lastObj : Option OsuHitObject) (h : OsuHitObject) : Option OsuHitObject × OsuHitObject :=
  let index : Int32 := (lastObj.map (·.comboIndex)).getD 0
  let indexWithOffsets : Int32 := (lastObj.map (·.comboIndexWithOffsets)).getD 0
  let inCurrentCombo : Int32 := (lastObj.map (·.indexInCurrentCombo + 1)).getD 0
  let lastIsSpinner := (lastObj.map (·.isSpinner)).getD false
  if !h.isSpinner && (h.newCombo || lastObj.isNone || lastIsSpinner) then
    (lastObj.map fun l => { l with lastInCombo := true },
     { h with comboIndex := index + 1, comboIndexWithOffsets := indexWithOffsets + h.comboOffset + 1,
              indexInCurrentCombo := 0 })
  else
    (lastObj, { h with comboIndex := index, comboIndexWithOffsets := indexWithOffsets, indexInCurrentCombo := inCurrentCombo })

/-- `OsuBeatmapProcessor.PreProcess()` (`:25-39`) then `BeatmapProcessor.PreProcess()` (`:19-28`). -/
def preProcess (hos : Array OsuHitObject) : Array OsuHitObject := Id.run do
  -- force NewCombo on the first object and on the first object after a spinner
  let mut objs := hos
  for i in [0:objs.size] do
    let o := objs[i]!
    if !o.isSpinner && (i == 0 || objs[i - 1]!.isSpinner) then
      objs := objs.set! i { o with newCombo := true }
  -- UpdateComboInformation
  for i in [0:objs.size] do
    let lastObj := if i == 0 then none else some objs[i - 1]!
    let (l, h) := updateComboInformation lastObj objs[i]!
    if let some l := l then objs := objs.set! (i - 1) l
    objs := objs.set! i h
  return objs

/-- `calculateStackThreshold(beatmap, hitObject) => (int)hitObject.TimePreempt * beatmap.StackLeniency`
(float product). -/
def stackThreshold (stackLeniency : F32) (h : OsuHitObject) : F32 :=
  F32.ofInt32 (F64.toInt32 h.timePreempt) * stackLeniency

/-- `Vector2Extensions.Distance(a, b) < STACK_DISTANCE` -/
def near (a b : Vec2) : Bool := Vec2.distanceFw a b < STACK_DISTANCE

/-- `applyStacking(beatmap, hitObjects, 0, hitObjects.Count - 1)` (`:69-222`), version ≥ 6. -/
def applyStacking (sl : F32) (hos0 : Array OsuHitObject) : Array OsuHitObject := Id.run do
  let mut hos := hos0
  let n := hos.size
  let startIndex := 0
  let endIndex := n - 1
  let mut extendedEndIndex := endIndex
  -- `if (endIndex < hitObjects.Count - 1)`: never true for the full-range call, the forward
  -- extension pass is skipped.
  -- Reverse pass for stack calculation.
  let mut extendedStartIndex := startIndex
  let mut i := extendedEndIndex
  for _ in [0:n] do
    if i ≤ startIndex then break
    let mut objectI := hos[i]!
    let mut objectIIdx := i
    if objectI.stackHeight != 0 || objectI.isSpinner then
      i := i - 1
      continue
    let threshold := stackThreshold sl objectI
    if objectI.isCircle then
      let mut nn : Int := i
      for _ in [0:n + 1] do
        nn := nn - 1
        if nn < 0 then break
        let k := nn.toNat
        let objectN := hos[k]!
        if objectN.isSpinner then continue
        let endTime := objectN.endTime
        -- `(int)objectI.StartTime - (int)endTime > stackThreshold` (int subtraction, compared as float)
        if threshold < F32.ofInt32 (F64.toInt32 objectI.startTime - F64.toInt32 endTime) then break
        if k < extendedStartIndex then
          hos := hos.set! k (hos[k]!.setStackHeight 0)
          extendedStartIndex := k
        let objectN := hos[k]!
        objectI := hos[objectIIdx]!
        if objectN.isSlider && near objectN.endPosition objectI.position then
          let offset : Int32 := objectI.stackHeight - objectN.stackHeight + 1
          for j in [k + 1:i + 1] do
            let objectJ := hos[j]!
            if near objectN.endPosition objectJ.position then
              hos := hos.set! j (objectJ.setStackHeight (objectJ.stackHeight - offset))
          break
        if near objectN.position objectI.position then
          hos := hos.set! k (objectN.setStackHeight (objectI.stackHeight + 1))
          objectIIdx := k
          objectI := hos[k]!
    else if objectI.isSlider then
      let mut nn : Int := i
      for _ in [0:n + 1] do
        nn := nn - 1
        if nn < startIndex then break
        let k := nn.toNat
        let objectN := hos[k]!
        if objectN.isSpinner then continue
        objectI := hos[objectIIdx]!
        if F32.toF64 threshold < objectI.startTime - objectN.startTime then break
        if near objectN.endPosition objectI.position then
          hos := hos.set! k (objectN.setStackHeight (objectI.stackHeight + 1))
          objectIIdx := k
          objectI := hos[k]!
    i := i - 1
  return hos

/-- `applyStackingOld(beatmap, hitObjects)` (`:224-269`), version < 6. -/
def applyStackingOld (sl : F32) (hos0 : Array OsuHitObject) : Array OsuHitObject := Id.run do
  let mut hos := hos0
  let n := hos.size
  for i in [0:n] do
    let curr := hos[i]!
    if curr.stackHeight != 0 && !curr.isSlider then continue
    let mut startTime := curr.endTime
    let mut sliderStack : Int32 := 0
    for j in [i + 1:n] do
      let currHitObject := hos[i]!
      let threshold := stackThreshold sl currHitObject
      if startTime < hos[j]!.startTime - F32.toF64 threshold then break
      -- position2: slider end via `Position + Path.PositionAt(1)` (not CurvePositionAt)
      let position2 := match currHitObject.kind with
        | .slider s => currHitObject.position + s.path.positionAt 1
        | _ => currHitObject.position
      if near hos[j]!.position currHitObject.position then
        hos := hos.set! i (currHitObject.setStackHeight (currHitObject.stackHeight + 1))
        startTime := hos[j]!.startTime
      else if near hos[j]!.position position2 then
        sliderStack := sliderStack + 1
        hos := hos.set! j (hos[j]!.setStackHeight (hos[j]!.stackHeight - sliderStack))
        startTime := hos[j]!.startTime
  return hos

/-- `OsuBeatmapProcessor.ApplyStacking(beatmap)` (`:45-67`) -/
def applyStackingAll (formatVersion : Int32) (sl : F32) (hos : Array OsuHitObject) : Array OsuHitObject :=
  if hos.size == 0 then hos
  else
    let hos := hos.map (·.setStackHeight 0)
    if formatVersion ≥ 6 then applyStacking sl hos else applyStackingOld sl hos

end OsuBeatmapProcessor
end OsuModel.Beatmap
