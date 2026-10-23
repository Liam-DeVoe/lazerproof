import OsuModel.Beatmap.Mods

/-!
# Random (`O/Mods/OsuModRandom.cs:42-162`) and the repositioning utilities
(`O/Utils/OsuHitObjectGenerationUtils.cs`, `OsuHitObjectGenerationUtils.Reposition.cs`)

`IApplicableToBeatmap`, after stacking: the objects keep their identity, stack heights and
times; positions, slider paths (flips and rotations) and nested positions change.
RNG: `new System.Random((int)Seed)` (`OsuModel.Net.NetRandom`), `NextDouble` only.
All vector arithmetic is binary32 in source order; `MathF.Atan2/Cos/Sin` are glibc `atan2f/cosf/sinf`,
`Math.Exp/Log/Sin` glibc double.
-/

namespace OsuModel.Beatmap
open OsuModel.Net

namespace Mods
namespace Reposition

def BASE_SIZE : Vec2 := ⟨512, 384⟩
/-- `OsuPlayfield.BASE_SIZE / 2` -/
def centre : Vec2 := ⟨256, 192⟩
/-- `playfield_edge_ratio = 0.375f`; `border_distance_x/y = BASE_SIZE.X/Y * ratio` -/
def edgeRatio : F32 := 0.375
def borderX : F32 := 512 * edgeRatio
def borderY : F32 := 384 * edgeRatio
/-- `MathF.PI` -/
def PI : F32 := Float32.ofBits 0x40490FDB
/-- `2 * MathF.PI` / `MathF.PI * 2` (constant-folded binary32 product) -/
def TWO_PI : F32 := 2 * PI

def atan2f (y x : F32) : F32 := F32.atan2 y x

/-- `RotateVectorTowardsVector(initial, destination, rotationRatio)` (`O/Utils/OsuHitObjectGenerationUtils.cs:89-106`) -/
def rotateVectorTowardsVector (initial destination : Vec2) (rotationRatio : F32) : Vec2 := Id.run do
  let initialAngle := atan2f initial.y initial.x
  let destAngle := atan2f destination.y destination.x
  let mut diff := destAngle - initialAngle
  -- `while (diff < -π) diff += 2π; while (diff > π) diff -= 2π;` (atan2 differences are within (-2π, 2π])
  for _ in [0:4] do
    if diff < -PI then diff := diff + TWO_PI
  for _ in [0:4] do
    if PI < diff then diff := diff - TWO_PI
  let finalAngle := initialAngle + rotationRatio * diff
  return ⟨initial.length * F32.cos finalAngle, initial.length * F32.sin finalAngle⟩

/-- `RotateAwayFromEdge(prevObjectPos, posRelativeToPrev, rotationRatio = 0.5f)` (`O/Utils/OsuHitObjectGenerationUtils.cs:41-80`) -/
def rotateAwayFromEdge (prev rel : Vec2) (rotationRatio : F32 := 0.5) : Vec2 :=
  let r : F32 := 0
  let r := if prev.x < centre.x then F32.max ((borderX - prev.x) / borderX) r
           else F32.max ((prev.x - (BASE_SIZE.x - borderX)) / borderX) r
  let r := if prev.y < centre.y then F32.max ((borderY - prev.y) / borderY) r
           else F32.max ((prev.y - (BASE_SIZE.y - borderY)) / borderY) r
  rotateVectorTowardsVector rel (centre - prev) (F32.min 1 (r * rotationRatio))

/-- `rotateVector(vector, rotation)` (`O/Utils/OsuHitObjectGenerationUtils.cs:178-186`) -/
def rotateVector (v : Vec2) (rotation : F32) : Vec2 :=
  let angle := atan2f v.y v.x + rotation
  let length := v.length
  ⟨length * F32.cos angle, length * F32.sin angle⟩

def sliderPath (h : OsuHitObject) : SliderPath :=
  match h.kind with | .slider s => s.path | _ => default

/-- `getSliderRotation(slider)` (`O/Utils/OsuHitObjectGenerationUtils.Reposition.cs:352-356`): `atan2f` of `Path.PositionAt(1)`. -/
def sliderRotation (h : OsuHitObject) : F32 :=
  let e := (sliderPath h).positionAt 1
  atan2f e.y e.x

/-- `getAngleDifference(a1, a2)` (`O/Utils/OsuHitObjectGenerationUtils.Reposition.cs:364-368`): `diff = |a1 - a2| % 2π; min(diff, 2π - diff)` -/
def angleDifference (a1 a2 : F32) : F32 :=
  let diff := fmodF32 (F32.abs (a1 - a2)) TWO_PI
  F32.min diff (TWO_PI - diff)

/-- `RotateSlider(slider, rotation)` (`O/Utils/OsuHitObjectGenerationUtils.cs:156-161`) -/
def rotateSlider (h : OsuHitObject) (rotation : F32) : OsuHitObject :=
  modifySlider (fun p => rotateVector p rotation) h

/-- `FlipSliderInPlaceHorizontally(slider)` (`O/Utils/OsuHitObjectGenerationUtils.cs:144-149`) -/
def flipSliderInPlaceHorizontally (h : OsuHitObject) : OsuHitObject :=
  modifySlider (fun p => ⟨-p.x, p.y⟩) h

/-- `RectangleF(x, y, width, height)`; `Right => X + Width`, `Bottom => Y + Height`. -/
structure RectF where
  x : F32
  y : F32
  w : F32
  h : F32

def RectF.right (r : RectF) : F32 := r.x + r.w
def RectF.bottom (r : RectF) : F32 := r.y + r.h

/-- `CalculatePossibleMovementBounds(slider)` (`O/Utils/OsuHitObjectGenerationUtils.Reposition.cs:266-305`) -/
def possibleMovementBounds (h : OsuHitObject) : RectF := Id.run do
  let mut minX : F32 := F32.posInf
  let mut maxX : F32 := -F32.posInf
  let mut minY : F32 := F32.posInf
  let mut maxY : F32 := -F32.posInf
  for p in (sliderPath h).calculatedPath do
    minX := F32.min minX p.x
    maxX := F32.max maxX p.x
    minY := F32.min minY p.y
    maxY := F32.max maxY p.y
  let radius := F64.toF32 h.radius
  minX := minX - radius
  minY := minY - radius
  maxX := maxX + radius
  maxY := maxY + radius
  let left := -minX
  let right := BASE_SIZE.x - maxX
  let top := -minY
  let bottom := BASE_SIZE.y - maxY
  return ⟨left, top, right - left, bottom - top⟩

/-- `clampToPlayfieldWithPadding(position, padding)` (`O/Utils/OsuHitObjectGenerationUtils.Reposition.cs:311-317`) (`Math.Clamp`, which throws if `min > max`). -/
def clampWithPadding (p : Vec2) (padding : F32) : DecodeM Vec2 := do
  let x ← liftNet "Math.Clamp" (F32.clamp p.x padding (BASE_SIZE.x - padding))
  let y ← liftNet "Math.Clamp" (F32.clamp p.y padding (BASE_SIZE.y - padding))
  return ⟨x, y⟩

/-- `calculateCentreOfMass(slider)` (`O/Utils/OsuHitObjectGenerationUtils.Reposition.cs:324-345`) -/
def centreOfMass (h : OsuHitObject) : Vec2 := Id.run do
  let path := sliderPath h
  let sampleStep : F64 := 50
  if path.distance ≤ sampleStep then
    let e := path.positionAt 1
    return ⟨e.x / 2, e.y / 2⟩
  let mut count : Nat := 0
  let mut sum : Vec2 := Vec2.zero
  let pathDistance := path.distance
  let mut i : F64 := 0
  -- `for (double i = 0; i < pathDistance; i += 50)` (fuel far beyond any finite path)
  for _ in [0:100000000] do
    if !(i < pathDistance) then break
    sum := sum + path.positionAt (i / pathDistance)
    count := count + 1
    i := i + sampleStep
  let c := F32.ofInt count
  return ⟨sum.x / c, sum.y / c⟩

/-- `ObjectPositionInfo` -/
structure PositionInfo where
  relativeAngle : F32 := 0
  distanceFromPrevious : F32 := 0
  rotation : F32 := 0
deriving Inhabited

/-- `GeneratePositionInfos(hitObjects)` (`O/Utils/OsuHitObjectGenerationUtils.Reposition.cs:30-61`) -/
def generatePositionInfos (hos : Array OsuHitObject) : Array PositionInfo := Id.run do
  let mut out := #[]
  let mut previousPosition := centre
  let mut previousAngle : F32 := 0
  for h in hos do
    let rel := h.position - previousPosition
    let mut absoluteAngle := atan2f rel.y rel.x
    let mut info : PositionInfo := { relativeAngle := absoluteAngle - previousAngle, distanceFromPrevious := rel.length }
    if h.isSlider then
      let absoluteRotation := sliderRotation h
      info := { info with rotation := absoluteRotation - absoluteAngle }
      absoluteAngle := absoluteRotation
    out := out.push info
    previousPosition := h.endPosition
    previousAngle := absoluteAngle
  return out

/-- `WorkingObject` (the hit object itself lives in the array being repositioned). -/
structure Working where
  rotationOriginal : F32
  positionModified : Vec2
  endPositionModified : Vec2
deriving Inhabited

/-- `computeModifiedPosition(current, previous, beforePrevious)` (`O/Utils/OsuHitObjectGenerationUtils.Reposition.cs:128-171`); returns the updated objects
(only `current`'s slider path may change) and `current`'s `PositionModified`. -/
def computeModifiedPosition (hos : Array OsuHitObject) (ws : Array Working) (infos : Array PositionInfo)
    (i : Nat) (prev : Option Nat) (beforePrev : Option Nat) : Array OsuHitObject × Vec2 := Id.run do
  let mut previousAbsoluteAngle : F32 := 0
  if let some p := prev then
    let ph := hos[p]!
    if ph.isSlider then previousAbsoluteAngle := sliderRotation ph
    else
      let earliest := match beforePrev with | some b => hos[b]!.endPosition | none => centre
      let rel := ph.position - earliest
      previousAbsoluteAngle := atan2f rel.y rel.x
  let info := infos[i]!
  let absoluteAngle := previousAbsoluteAngle + info.relativeAngle
  let posRel0 : Vec2 := ⟨info.distanceFromPrevious * F32.cos absoluteAngle, info.distanceFromPrevious * F32.sin absoluteAngle⟩
  let lastEnd := match prev with | some p => ws[p]!.endPositionModified | none => centre
  let posRel := rotateAwayFromEdge lastEnd posRel0
  let positionModified := lastEnd + posRel
  let h := hos[i]!
  if !h.isSlider then return (hos, positionModified)
  let absoluteAngle := atan2f posRel.y posRel.x
  let comOriginal := centreOfMass h
  let comModified := rotateVector comOriginal (info.rotation + absoluteAngle - sliderRotation h)
  let comModified := rotateAwayFromEdge positionModified comModified
  let relativeRotation := atan2f comModified.y comModified.x - atan2f comOriginal.y comOriginal.x
  -- `Precision.AlmostEquals(float, float)` with `FLOAT_EPSILON`
  if !Precision.almostEqualsF32 relativeRotation 0 then
    return (hos.set! i (rotateSlider h relativeRotation), positionModified)
  return (hos, positionModified)

/-- `clampSliderToPlayfield(workingObject)` (`O/Utils/OsuHitObjectGenerationUtils.Reposition.cs:194-236`): returns the slider, the working object and the shift. -/
def clampSliderToPlayfield (h0 : OsuHitObject) (w : Working) : DecodeM (OsuHitObject × Working × Vec2) := do
  let mut h := h0
  let mut bounds := possibleMovementBounds h
  if bounds.w < 0 || bounds.h < 0 then
    let currentRotation := sliderRotation h
    let diff1 := angleDifference w.rotationOriginal currentRotation
    let diff2 := angleDifference (w.rotationOriginal + PI) currentRotation
    if diff1 < diff2 then h := rotateSlider h (w.rotationOriginal - sliderRotation h)
    else h := rotateSlider h (w.rotationOriginal + PI - sliderRotation h)
    bounds := possibleMovementBounds h
  let previousPosition := w.positionModified
  let newX ← if bounds.w < 0 then liftNet "Math.Clamp" (F32.clamp bounds.x 0 BASE_SIZE.x)
             else liftNet "Math.Clamp" (F32.clamp previousPosition.x bounds.x bounds.right)
  let newY ← if bounds.h < 0 then liftNet "Math.Clamp" (F32.clamp bounds.y 0 BASE_SIZE.y)
             else liftNet "Math.Clamp" (F32.clamp previousPosition.y bounds.y bounds.bottom)
  let p : Vec2 := ⟨newX, newY⟩
  h := setPosition h p
  return (h, { w with positionModified := p, endPositionModified := h.endPosition }, p - previousPosition)

/-- `RepositionHitObjects(objectPositionInfos)` (`O/Utils/OsuHitObjectGenerationUtils.Reposition.cs:68-120`; `applyDecreasingShift` :244-255) -/
def repositionHitObjects (hos0 : Array OsuHitObject) (infos : Array PositionInfo) : DecodeM (Array OsuHitObject) := do
  let mut hos := hos0
  let mut ws : Array Working := hos.map fun h =>
    { rotationOriginal := if h.isSlider then sliderRotation h else 0,
      positionModified := h.position, endPositionModified := h.endPosition }
  let mut previous : Option Nat := none
  for i in [0:hos.size] do
    if hos[i]!.isSpinner then
      previous := some i
      continue
    let (hos', pm) := computeModifiedPosition hos ws infos i previous (if i > 1 then some (i - 2) else none)
    hos := hos'
    ws := ws.set! i { ws[i]! with positionModified := pm }
    let mut shift := Vec2.zero
    let h := hos[i]!
    match h.kind with
    | .circle =>
      let w := ws[i]!
      let previousPosition := w.positionModified
      let p ← clampWithPadding w.positionModified (F64.toF32 h.radius)
      ws := ws.set! i { w with positionModified := p, endPositionModified := p }
      hos := hos.set! i (setPosition h p)
      shift := p - previousPosition
    | .slider _ =>
      let (h', w', s) ← clampSliderToPlayfield h ws[i]!
      hos := hos.set! i h'
      ws := ws.set! i w'
      shift := s
    | .spinner _ => pure ()
    if !shift.eq Vec2.zero then
      -- `preceding_hitobjects_to_shift = 10` consecutive preceding hit circles, nearest first
      let mut toBeShifted : Array Nat := #[]
      for k in [1:11] do
        if k > i then break
        if !hos[i - k]!.isCircle then break
        toBeShifted := toBeShifted.push (i - k)
      -- `applyDecreasingShift`
      let count := toBeShifted.size
      for idx in [0:count] do
        let j := toBeShifted[idx]!
        let hj := hos[j]!
        let f : F32 := F32.ofInt (count - idx : Nat) / F32.ofInt (count + 1 : Nat)
        let position := hj.position + ⟨shift.x * f, shift.y * f⟩
        let p ← clampWithPadding position (F64.toF32 hj.radius)
        hos := hos.set! j (setPosition hj p)
    previous := some i
  return hos

end Reposition

namespace RandomMod
open Reposition

/-- `IsHitObjectOnBeat(beatmap, hitObject, downbeatsOnly)` (`O/Utils/OsuHitObjectGenerationUtils.cs:193-206`):
`Math.Abs(timeSinceTimingPoint + 1) % beatLength < 2`. -/
def isOnBeat (cpi : ControlPointInfo) (h : OsuHitObject) (downbeatsOnly : Bool) : Bool :=
  let tp := cpi.timingPointAt h.startTime
  let timeSince := h.startTime - tp.time
  let beatLength := if downbeatsOnly then tp.beatLength * F64.ofInt32 tp.timeSignature else tp.beatLength
  fmodF64 (F64.abs (timeSince + 1)) beatLength < 2

/-- `playfield_diagonal = OsuPlayfield.BASE_SIZE.LengthFast` -/
def playfieldDiagonal : F32 := 1 / OsuTK.MathHelper.inverseSqrtFast (512 * 512 + 384 * 384)

def SIX_TENTHS_F : F64 := F32.toF64 0.6
def FOUR_TENTHS_F : F64 := F32.toF64 0.4

abbrev RM := StateM NetRandom.State

def nextDouble : RM F64 := modifyGet fun s => NetRandom.nextDouble s

/-- `OsuHitObjectGenerationUtils.RandomGaussian(rng, 0, stdDev)` (`O/Utils/OsuHitObjectGenerationUtils.cs:211-220`) -/
def randomGaussian (stdDev : F32) : RM F32 := do
  let x1 := 1 - (← nextDouble)
  let x2 := 1 - (← nextDouble)
  let stdNormal := F64.sqrt (-2 * F64.log x1) * F64.sin (2 * Float.ofBits 0x400921FB54442D18 * x2)
  return 0 + stdDev * F64.toF32 stdNormal

/-- `getRandomOffset(stdDev)` (`O/Mods/OsuModRandom.cs:104-112`): `customMultiplier = (1.5f * MaxValue - Value) / (1.5f * MaxValue - Default)` -/
def randomOffset (sharpness : F32) (stdDev : F32) : RM F32 :=
  let mult : F32 := ((1.5 : F32) * 10 - sharpness) / ((1.5 : F32) * 10 - 7)
  randomGaussian (stdDev * mult)

/-- `getRelativeTargetAngle(targetDistance, offset, flowDirection)` (`O/Mods/OsuModRandom.cs:116-134`) -/
def relativeTargetAngle (sharpness : F32) (targetDistance0 offset : F32) (flow : Bool) : F32 :=
  let angleSharpness := sharpness / 10
  let angleWideness := 1 - angleSharpness
  let customOffsetX := angleSharpness * 100 - 70
  let customOffsetY := angleWideness * (0.25 : F32) - (0.075 : F32)
  let targetDistance := targetDistance0 + customOffsetX
  let inner : F32 := targetDistance - 310 + customOffsetX
  let angle : F32 := F64.toF32 (2.16 / (1 + 200 * F64.exp (0.036 * F32.toF64 inner)) + 0.5)
  let angle := angle + (offset + customOffsetY)
  let relativeAngle := PI - angle
  if flow then -relativeAngle else relativeAngle

/-- `OsuModRandom.ApplyToBeatmap` (`O/Mods/OsuModRandom.cs:42-96`; `shouldStartNewSection` :138-152,
`shouldApplyFlowChange` :155-162) -/
def apply (seed : Int32) (sharpness : F32) (pb : PlayableBeatmap) : DecodeM PlayableBeatmap := do
  let mut rng := NetRandom.create seed
  let mut hos := pb.hitObjects
  let mut infos := generatePositionInfos hos
  let mut sectionOffset : F32 := 0
  let mut flow := false
  for i in [0:infos.size] do
    -- shouldStartNewSection
    let newSection ← if i == 0 then pure true else do
      let started := hos[if i ≥ 2 then i - 2 else 0]!.indexInCurrentCombo > 1 && hos[i - 1]!.newCombo
      let downbeat := isOnBeat pb.controlPoints hos[i - 1]! true
      let onBeat := isOnBeat pb.controlPoints hos[i - 1]! false
      let mut r := false
      if started then
        let (d, s) := NetRandom.nextDouble rng
        rng := s
        r := d < SIX_TENTHS_F
      if !r then r := downbeat
      if !r && onBeat then
        let (d, s) := NetRandom.nextDouble rng
        rng := s
        r := d < FOUR_TENTHS_F
      pure r
    if newSection then
      let (o, s) := (randomOffset sharpness 0.0008).run rng
      rng := s
      sectionOffset := o
      flow := !flow
    if hos[i]!.isSlider then
      let (d, s) := NetRandom.nextDouble rng
      rng := s
      if d < 0.5 then hos := hos.set! i (flipSliderInPlaceHorizontally hos[i]!)
    if i == 0 then
      let (d1, s) := NetRandom.nextDouble rng
      let (d2, s) := NetRandom.nextDouble s
      rng := s
      infos := infos.set! 0 { infos[0]! with
        distanceFromPrevious := F64.toF32 (d1 * F32.toF64 384 / 2),
        relativeAngle := F64.toF32 (d2 * 2 * Float.ofBits 0x400921FB54442D18 - Float.ofBits 0x400921FB54442D18) }
    else
      let mut flowChangeOffset : F32 := 0
      let (oneTime, s) := (randomOffset sharpness 0.002).run rng
      rng := s
      -- shouldApplyFlowChange
      let started := hos[if i ≥ 2 then i - 2 else 0]!.indexInCurrentCombo > 1 && hos[i - 1]!.newCombo
      let mut apply := false
      if started then
        let (d, s) := NetRandom.nextDouble rng
        rng := s
        apply := d < SIX_TENTHS_F
      if apply then
        let (o, s) := (randomOffset sharpness 0.002).run rng
        rng := s
        flowChangeOffset := o
        flow := !flow
      let dist := infos[i]!.distanceFromPrevious
      let totalOffset := (sectionOffset + oneTime) * dist + flowChangeOffset * (playfieldDiagonal - dist)
      infos := infos.set! i { infos[i]! with relativeAngle := relativeTargetAngle sharpness dist totalOffset flow }
  let out ← repositionHitObjects hos infos
  return { pb with hitObjects := out }

end RandomMod
end Mods
end OsuModel.Beatmap
