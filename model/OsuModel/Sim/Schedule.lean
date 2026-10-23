import OsuModel.Sim.Playable
import OsuModel.Replay.Frames

/-!
# Step schedule: FrameStabilityContainer + FramedReplayInputHandler (DECISIONS D9)

Mirrors `oracle/Schedule.cs` (`ScheduleSpec.Create`, `StepSimulator.Simulate`), which re-implements
`FrameStabilityContainer.updateClock/applyFrameStability` (`osu.Game/Rulesets/UI/FrameStabilityContainer.cs:127-279`)
and `FramedReplayInputHandler.SetFrameFromTime` (`osu.Game/Rulesets/Replays/FramedReplayInputHandler.cs:127-165`,
FrameAccuratePlayback off, all frames received). Each step records the frame-stable time and the replay
handler's frame index after `SetFrameFromTime`.
-/

namespace OsuModel.Sim
open OsuModel.Net OsuModel.Replay

inductive ScheduleKind where
  | catchup | perframe | dense1ms
deriving Inhabited, Repr, DecidableEq

def ScheduleKind.ofString? : String → Option ScheduleKind
  | "catchup" => some .catchup | "perframe" => some .perframe | "dense1ms" => some .dense1ms
  | _ => none

/-- One frame-stable step: the time, and `currentFrameIndex` of the replay handler (-1 = before the first frame). -/
structure Step where
  time : F64
  frameIndex : Int
deriving Inhabited, Repr

/-- `DrawableOsuRuleset.GameplayStartTime` (`osu.Game.Rulesets.Osu/UI/DrawableOsuRuleset.cs:82-91`). -/
def gameplayStartTime (pb : Playable) : F64 :=
  match pb.objects[0]? with
  | some o => o.h.start - F64.max 2000 o.h.preempt
  | none => 0

/-- `MasterGameplayClockContainer.findEarliestStartTime` without storyboard (as the oracle):
`min(0, gst)`, then `min(time, firstObject.StartTime - AudioLeadIn)` if `AudioLeadIn > 0`. -/
def referenceStart (pb : Playable) : F64 :=
  let t := F64.min 0 (gameplayStartTime pb)
  match pb.objects[0]? with
  | some o => if 0 < pb.audioLeadIn then F64.min t (o.h.start - pb.audioLeadIn) else t
  | none => t

/-- Oracle `end` = latest end time of any (nested) object + 1000. Uses `Math.Max` from -∞. -/
def referenceEnd (pb : Playable) : F64 := Id.run do
  let mut m := F64.negInf
  for o in pb.objects do
    m := F64.max m o.h.endTime
    for n in o.nested do
      m := F64.max m n.endTime
  return m + 1000

/-- Reference-time sequences (`ScheduleSpec.Create`). `dense1ms` is generated lazily by `steps`. -/
def references (kind : ScheduleKind) (r0 endT : F64) (frameTimes : Array F64) : Except String (Array F64) :=
  match kind with
  | .catchup => pure #[r0, F64.max r0 endT]
  | .perframe => Id.run do
    -- `last` is the last element of `l`
    let mut l : Array F64 := #[r0]
    let mut last := r0
    for f in frameTimes do
      if last < f then
        l := l.push f
        last := f
    if last < endT then l := l.push endT
    return pure l
  | .dense1ms => do
    -- r0, then floor(cur)+1 while cur < end (`DenseSchedule`).
    let mut l : Array F64 := #[r0]
    let mut cur := r0
    let mut fuel := 100000000
    while cur < endT && fuel > 0 do
      fuel := fuel - 1
      cur := F64.floor cur + 1
      l := l.push cur
    if cur < endT then throw "schedule: dense reference list exceeds 1e8 entries"
    return l

/-- `1000.0 / 60` -/
def sixtyFrameTime : F64 := 1000.0 / 60
/-- `sixty_frame_time * 1.2f` (the float is widened to double). -/
def catchupThreshold : F64 := sixtyFrameTime * F32.toF64 (1.2 : F32)

/-- `StepSimulator.Simulate` (`oracle/Schedule.cs`). Each reference is held until the FSC reaches it,
with at least one step per reference. -/
def simulateSteps (refs : Array F64) (frames : Array F64) (gst : F64) : Except String (Array Step) := do
  let frameTime (i : Int) : F64 :=
    if i < 0 then F64.negInf else match frames[i.toNat]? with | some t => t | none => F64.posInf
  let mut steps : Array Step := #[]
  let mut first := true
  let mut manual : F64 := 0
  let mut idx : Int := -1
  let mut handlerTime : F64 := F64.negInf
  for r in refs do
    let mut fuel := 100000000
    while fuel > 0 do
      fuel := fuel - 1
      let mut proposed := r
      if first then
        manual := proposed
        first := false
      else if manual < gst then
        proposed := F64.min gst proposed
        manual := proposed
      else if catchupThreshold < F64.abs (manual - proposed) then
        proposed := if manual < proposed then F64.min proposed (manual + sixtyFrameTime)
          else F64.max proposed (manual - sixtyFrameTime)
      if frames.size == 0 then
        handlerTime := proposed
      else
        let fs := frameTime idx
        let fe := frameTime (idx + 1)
        if fe ≤ proposed then
          proposed := fe
          idx := idx + 1
        else if proposed < fs && handlerTime == fs then
          idx := idx - 1
        let fs := frameTime idx
        let fe := frameTime (idx + 1)
        -- `Math.Clamp(time, frames[idx].Time, frames[idx+1].Time)` throws on out-of-order frames
        handlerTime ← match F64.clamp proposed fs fe with
          | .ok v => pure v
          | .error e => throw s!"lazer would throw: Math.Clamp {repr e} (frame times out of order at {idx})"
      proposed := handlerTime
      manual := proposed
      steps := steps.push { time := manual, frameIndex := idx }
      if proposed == r then break
    if fuel == 0 then throw "schedule: step fuel exhausted"
  return steps

/-- All steps for a playable beatmap + decoded frames under a schedule kind. -/
def steps (kind : ScheduleKind) (pb : Playable) (frames : Array Frame) : Except String (Array Step) := do
  let ft := frames.map (·.time)
  simulateSteps (← references kind (referenceStart pb) (referenceEnd pb) ft) ft (gameplayStartTime pb)

end OsuModel.Sim
