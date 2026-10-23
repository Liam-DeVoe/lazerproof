import OsuModel.Beatmap.ModRandom

/-!
# Target Practice beatmap generation (`O/Mods/OsuModTargetPractice.cs:160-326,341-497`)

`IApplicableToBeatmap`: the whole object list is replaced by hit circles on the beats of the
timing points (`generateBeats`), combo information copied from the original objects
(`fixComboInfo`), and positions from `new System.Random(Seed)` (`randomizeCirclePos`).
The new circles get `ApplyDefaults` while their `StartTime` is still 0 (so `Kiai` is
`EffectPointAt(1)`), after stacking: `StackHeight = 0`, no HR/MR reflection.
-/

namespace OsuModel.Beatmap
open OsuModel.Net

namespace Mods
namespace TargetPractice
open Reposition

/-- `timing_precision = 1` (`O/Mods/OsuModTargetPractice.cs:90`; helpers :492-500) -/
def TIMING_PRECISION : F64 := 1
/-- `Precision.AlmostBigger(a, b, 1) = a > b - 1` -/
def almostBigger (a b : F64) : Bool := b - TIMING_PRECISION < a
/-- `Precision.DefinitelyBigger(a, b, 1) = a - 1 > b` -/
def definitelyBigger (a b : F64) : Bool := b < a - TIMING_PRECISION

/-- Index of `ControlPointInfo.TimingPointAt(time)` in `TimingPoints` (reference identity),
`none` for `TimingControlPoint.DEFAULT`. -/
def timingPointIndexAt (cpi : ControlPointInfo) (time : F64) : Option Nat :=
  match binarySearchIdx cpi.timingPoints (·.time) time with
  | some i => some i
  | none => if cpi.timingPoints.size > 0 then some 0 else none

/-- `isInsideBreakPeriod(originalHitObjects, breaks, time)` (`O/Mods/OsuModTargetPractice.cs:352-363`) -/
def insideBreak (orig : Array OsuHitObject) (breaks : Array BreakPeriod) (time : F64) : Bool :=
  breaks.any fun b =>
    let firstAfter := orig.find? fun o => almostBigger o.startTime b.endTime
    almostBigger time b.startTime && (match firstAfter with | none => true | some o => definitelyBigger o.startTime time)

/-- `generateBeats(beatmap, originalHitObjects)` (`O/Mods/OsuModTargetPractice.cs:193-219`; `getBeatsForTimingPoint` :365-379) -/
def generateBeats (pb : PlayableBeatmap) (orig : Array OsuHitObject) : Array F64 := Id.run do
  let cpi := pb.controlPoints
  let startTime := pb.hitObjects[0]!.startTime
  let endTime := lastObjectTime pb
  let mut beats : Array F64 := #[]
  let mut ti := 0
  for tp in cpi.timingPoints do
    if !definitelyBigger tp.time endTime then
      -- getBeatsForTimingPoint
      let mut i : Int32 := 0
      let mut cur := tp.time
      for _ in [0:1000000000] do
        if definitelyBigger cur endTime || timingPointIndexAt cpi cur != some ti then break
        beats := beats.push (F64.floor cur)
        i := i + 1
        cur := tp.time + F64.ofInt32 i * tp.beatLength
    ti := ti + 1
  beats := beats.filter fun b => almostBigger b startTime
  beats := beats.filter fun b => !insideBreak orig pb.breaks b
  -- remove beats that are too close to the next one (backwards, `RemoveAt(i)`)
  if beats.size < 2 then return beats
  let mut kept : List F64 := [beats.back!]
  for k in [0:beats.size - 1] do
    let i := beats.size - 2 - k
    let beat := beats[i]!
    let next := kept.head!
    if definitelyBigger (next - beat) ((cpi.timingPointAt beat).beatLength / 2) then kept := beat :: kept
  return kept.toArray

/-- `fixComboInfo(hitObjects, originalHitObjects)` (`O/Mods/OsuModTargetPractice.cs:233-265`) -/
def fixComboInfo (hos : Array OsuHitObject) (orig : Array OsuHitObject) : Array OsuHitObject := Id.run do
  let hos := hos.map fun h =>
    let closest := orig.reverse.find? fun y => almostBigger h.startTime y.startTime
    { h with comboIndex := (closest.map (·.comboIndex)).getD 0 }
  -- `GroupBy(x => x.ComboIndex)`: groups in order of first appearance
  let mut keys : Array Int32 := #[]
  for h in hos do
    if !keys.contains h.comboIndex then keys := keys.push h.comboIndex
  let mut out := hos
  let mut g : Int32 := 0
  for key in keys do
    let idxs := (List.range hos.size).filter fun j => hos[j]!.comboIndex == key
    let mut j : Int32 := 0
    for k in idxs do
      out := out.set! k { out[k]! with comboIndex := g, indexInCurrentCombo := j }
      j := j + 1
    let first := idxs.head!
    let last := idxs.getLast!
    out := out.set! first { out[first]! with newCombo := true }
    out := out.set! last { out[last]! with lastInCombo := true }
    g := g + 1
  return out

/-- `nodeIndexFromTime(curve, timeSinceStart)` (`O/Mods/OsuModTargetPractice.cs:440-449`):
`(int)Math.Round(t / spanDuration)` if within 1 of its rounding, else -1. -/
def nodeIndexFromTime (h : OsuHitObject) (timeSinceStart : F64) : Int32 :=
  let spanCount : Int32 := match h.kind with | .slider s => s.spanCount | _ => 1
  let spanDuration := h.duration / F64.ofInt32 spanCount
  let nodeIndex := timeSinceStart / spanDuration
  if F64.abs (nodeIndex - F64.round nodeIndex) ≤ 1 then F64.toInt32 (F64.round nodeIndex) else -1

/-- `addHitSamples(hitObjects, originalHitObjects)` (`O/Mods/OsuModTargetPractice.cs:221-231`,
`getSamplesAtTime` :402-429, `getClosestHitObject` :381-391). Samples are audio-only, but the
lookups can throw `ArgumentOutOfRangeException` (list indexers), which fails `GetPlayableBeatmap`:
`NodeSamples[i]` with `i ∉ [0, RepeatCount + 1]`, and `hitObjects[-1]` when no sample object exists and
no original object starts before the beat. -/
def checkHitSamples (orig : Array OsuHitObject) (beats : Array F64) : DecodeM Unit := do
  for t in beats do
    let pred (o : OsuHitObject) : Bool :=
      if F64.abs (t - o.startTime) ≤ TIMING_PRECISION then true
      else if !o.isSlider then false
      else if !almostBigger t o.startTime || !almostBigger o.endTime t then false
      else nodeIndexFromTime o (t - o.startTime) != -1
    match orig.find? pred with
    | some o =>
      match o.kind with
      | .slider s =>
        let i := nodeIndexFromTime o (t - o.startTime)
        if i < 0 || i > s.repeatCount + 1 then throw "ArgumentOutOfRangeException (NodeSamples)"
      | _ => pure ()
    | none =>
      -- `FindLastIndex(h => h.StartTime < time)`
      let precedingIndex : Int := match (orig.toList.reverse.findIdx? fun h => h.startTime < t) with
        | some k => (orig.size - 1 - k : Nat)
        | none => -1
      if precedingIndex != (orig.size : Int) - 1 && precedingIndex == -1 then
        throw "ArgumentOutOfRangeException (getClosestHitObject)"

def MAX_BASE_DISTANCE : F32 := 333
def DISTANCE_CAP : F32 := 380
def EDGE_ROTATION_MULTIPLIER : F32 := 0.75
def OVERLAP_CHECK_COUNT : Nat := 5

/-- `clampToPlayfield(obj)` (`O/Mods/OsuModTargetPractice.cs:460-476`) -/
def clampToPlayfield (p : Vec2) (radius : F32) : Vec2 :=
  let y := if p.y < radius then radius else if BASE_SIZE.y - radius < p.y then BASE_SIZE.y - radius else p.y
  let x := if p.x < radius then radius else if BASE_SIZE.x - radius < p.x then BASE_SIZE.x - radius else p.x
  ⟨x, y⟩

/-- `mapRange(value, fromLow, fromHigh, toLow, toHigh)` (`O/Mods/OsuModTargetPractice.cs:487-490`) -/
def mapRange (value fromLow fromHigh toLow toHigh : F32) : F32 :=
  (value - fromLow) * (toHigh - toLow) / (fromHigh - fromLow) + toLow

/-- `randomizeCirclePos(hitObjects, rng)` (`O/Mods/OsuModTargetPractice.cs:267-326`; `checkForOverlap` :451-454) -/
def randomizeCirclePos (hos0 : Array OsuHitObject) (rng0 : NetRandom.State) : Array OsuHitObject := Id.run do
  if hos0.size == 0 then return hos0
  let mut hos := hos0
  let mut rng := rng0
  let nextSingle (r : NetRandom.State) : F32 × NetRandom.State :=
    let (d, r) := NetRandom.nextDouble r
    (F64.toF32 (d * F32.toF64 1), r)
  let (ns, r) := nextSingle rng
  rng := r
  let mut direction : F32 := TWO_PI * ns
  let maxComboIndex := hos.back!.comboIndex
  for i in [0:hos.size] do
    let obj := hos[i]!
    let lastPos := if i == 0 then centre else hos[i - 1]!.position
    let radius := F64.toF32 obj.radius
    let mut distance : F32 :=
      if maxComboIndex == 0 then radius
      else mapRange (F32.ofInt32 obj.comboIndex) 0 (F32.ofInt32 maxComboIndex) radius MAX_BASE_DISTANCE
    if obj.newCombo then distance := distance * 1.5
    if obj.kiai then distance := distance * 1.2
    distance := F32.min DISTANCE_CAP distance
    let preceding := (hos.extract (if i ≥ OVERLAP_CHECK_COUNT then i - OVERLAP_CHECK_COUNT else 0) i).map (·.position)
    let mut tryCount : Nat := 0
    let mut pos := obj.position
    -- do { ... } while (distance >= Radius * 2 && checkForOverlap(...)); distance shrinks by 0.9 every 10 tries
    for _ in [0:100000] do
      if tryCount > 0 then
        let (ns, r) := nextSingle rng
        rng := r
        direction := TWO_PI * ns
      let rel0 : Vec2 := ⟨distance * F32.cos direction, distance * F32.sin direction⟩
      let rel := rotateAwayFromEdge lastPos rel0 EDGE_ROTATION_MULTIPLIER
      direction := atan2f rel.y rel.x
      pos := clampToPlayfield (lastPos + rel) radius
      tryCount := tryCount + 1
      if tryCount % 10 == 0 then distance := distance * 0.9
      let overlap := preceding.any fun p => F32.toF64 (Vec2.distance p pos) < obj.radius * 2
      if !(obj.radius * 2 ≤ F32.toF64 distance && overlap) then break
    hos := hos.set! i { obj with position := pos }
    if obj.lastInCombo then
      let (ns, r) := nextSingle rng
      rng := r
      direction := TWO_PI * ns
    else
      let (ns, r) := nextSingle rng
      rng := r
      direction := direction + distance / DISTANCE_CAP * (ns * TWO_PI - PI)
  return hos

/-- `OsuModTargetPractice.ApplyToBeatmap` (`O/Mods/OsuModTargetPractice.cs:160-191`) (including `base.ApplyToBeatmap`: `FirstObject`). -/
def apply (seed : Int32) (idx : Nat) (pb : PlayableBeatmap) : DecodeM PlayableBeatmap := do
  let rng := NetRandom.create seed
  if pb.hitObjects.size == 0 then
    return { pb with modStates := pb.modStates.push (idx, .firstObject none) }
  let orig := stableSortBy (·.startTime) pb.hitObjects
  let beats := generateBeats pb orig
  let mut hos : Array OsuHitObject := #[]
  for b in beats do
    let c ← applyDefaults pb.controlPoints pb.difficulty { kind := .circle, startTime := 0, position := Vec2.zero }
    hos := hos.push { c with startTime := b }
  checkHitSamples orig beats
  let fixed := fixComboInfo hos orig
  let placed := randomizeCirclePos fixed rng
  let pb := { pb with hitObjects := placed, epoch := pb.epoch + 1 }
  return recordFirstObject false idx pb

end TargetPractice
end Mods

open Mods in
/-- `ModConfig.hooks` extended with the generator mods (Random, Target Practice). -/
def ModConfig.allHooks (m : ModConfig) : Mod :=
  if !m.known then m.hooks else
  match m.acronym with
  | "RD" => { acronym := "RD", applyToBeatmap := some fun _ pb =>
      match m.getOptInt "seed" with
      | some s => RandomMod.apply s (m.getFloat "angle_sharpness") pb
      | none => throw "Random without a seed is not reproducible" }
  | "TP" =>
    let base := m.hooks
    { base with applyToBeatmap := some fun i pb =>
      match m.getOptInt "seed" with
      | some s => TargetPractice.apply s i pb
      | none => throw "Target Practice without a seed is not reproducible" }
  | _ => m.hooks

end OsuModel.Beatmap
