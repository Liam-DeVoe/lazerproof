import OsuModel.Beatmap.HitObjectParser

/-!
# `SliderEventGenerator.Generate` (`osu.Game/Rulesets/Objects/SliderEventGenerator.cs:26-161`)
-/

namespace OsuModel.Beatmap
open OsuModel.Net

/-- `SliderEventType` -/
inductive SliderEventType where
  | tick | legacyLastTick | head | repeat | tail
deriving Inhabited, Repr, BEq

/-- `SliderEventDescriptor` -/
structure SliderEventDescriptor where
  type : SliderEventType
  time : F64
  spanIndex : Int32
  spanStartTime : F64
  pathProgress : F64
deriving Inhabited, Repr

namespace SliderEventGenerator

/-- `TAIL_LENIENCY = -36` -/
def TAIL_LENIENCY : F64 := -36

/-- `generateTicks(...)` (`:138-161`): ticks of one span, in increasing distance order. -/
def generateTicks (spanIndex : Int32) (spanStartTime spanDuration : F64) (reversed : Bool) (length tickDistance
    minDistanceFromEnd : F64) : Array SliderEventDescriptor := Id.run do
  let mut out := #[]
  let mut d := tickDistance
  -- `for (double d = tickDistance; d <= length; d += tickDistance)`; terminates since
  -- `tickDistance > 0` here (the caller skips `tickDistance == 0`; NaN fails `d <= length`).
  -- Fuel: `length ≤ 100000` and `tickDistance` is bounded below for real sliders; the bound
  -- 10^7 is never reached on the corpus.
  for _ in [0:10000000] do
    if !(d ≤ length) then break
    if length - minDistanceFromEnd ≤ d then break
    let pathProgress := d / length
    let timeProgress := if reversed then 1 - pathProgress else pathProgress
    out := out.push { type := .tick, spanIndex, spanStartTime, time := spanStartTime + timeProgress * spanDuration,
                      pathProgress }
    d := d + tickDistance
  return out

/-- `Generate(startTime, spanDuration, velocity, tickDistance, totalDistance, spanCount)` (`:26-124`). -/
def generate (startTime spanDuration velocity tickDistance0 totalDistance : F64) (spanCount : Int32) :
    DecodeM (Array SliderEventDescriptor) := do
  let max_length : F64 := 100000
  let length := F64.min max_length totalDistance
  let tickDistance ← liftNet "Math.Clamp(tickDistance, 0, length)" (F64.clamp tickDistance0 0 length)
  let minDistanceFromEnd := velocity * 10
  let mut out : Array SliderEventDescriptor :=
    #[{ type := .head, spanIndex := 0, spanStartTime := startTime, time := startTime, pathProgress := 0 }]
  for spanN in [0:spanCount.toNatClampNeg] do
    let span : Int32 := Int32.ofNat spanN
    let spanStartTime := startTime + F64.ofInt32 span * spanDuration
    let reversed := span % 2 == 1
    if !(tickDistance == 0) then
      let ticks := generateTicks span spanStartTime spanDuration reversed length tickDistance minDistanceFromEnd
      out := out ++ (if reversed then ticks.reverse else ticks)
    if span < spanCount - 1 then
      out := out.push { type := .repeat, spanIndex := span, spanStartTime := startTime + F64.ofInt32 span * spanDuration,
                        time := spanStartTime + spanDuration, pathProgress := F64.ofInt32 ((span + 1) % 2) }
  let totalDuration := F64.ofInt32 spanCount * spanDuration
  let finalSpanIndex := spanCount - 1
  let finalSpanStartTime := startTime + F64.ofInt32 finalSpanIndex * spanDuration
  let legacyLastTickTime := F64.max (startTime + totalDuration / 2) ((finalSpanStartTime + spanDuration) + TAIL_LENIENCY)
  let mut legacyLastTickProgress := (legacyLastTickTime - finalSpanStartTime) / spanDuration
  if spanCount % 2 == 0 then legacyLastTickProgress := 1 - legacyLastTickProgress
  out := out.push { type := .legacyLastTick, spanIndex := finalSpanIndex, spanStartTime := finalSpanStartTime,
                    time := legacyLastTickTime, pathProgress := legacyLastTickProgress }
  out := out.push { type := .tail, spanIndex := finalSpanIndex, spanStartTime := startTime + F64.ofInt32 (spanCount - 1) * spanDuration,
                    time := startTime + totalDuration, pathProgress := F64.ofInt32 (spanCount % 2) }
  return out

end SliderEventGenerator
end OsuModel.Beatmap
