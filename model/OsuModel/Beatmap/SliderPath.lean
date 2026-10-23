import OsuModel.Beatmap.PathApproximator
import OsuModel.Beatmap.Types

/-!
# `osu.Game.Rulesets.Objects.SliderPath` (`osu.Game/Rulesets/Objects/SliderPath.cs`)

The C# class is a lazily recomputed cache over `ControlPoints` + `ExpectedDistance` (+
`OptimiseCatmull`). The model computes the cache contents (`calculatedPath`, `cumulativeLength`,
`calculatedLength`) eagerly with `SliderPath.compute`; queries (`PositionAt`, `Distance`) are
functions of that result.
-/

namespace OsuModel.Beatmap
open OsuModel.Net

/-- The persistent part of a `SliderPath`. -/
structure SliderPathSpec where
  controlPoints : Array PathControlPoint
  expectedDistance : Option F64
  /-- `OptimiseCatmull` (true for `Slider.Path`, `Slider.cs:45`; false for `ConvertSlider`). -/
  optimiseCatmull : Bool
deriving Inhabited, Repr

/-- The cached state after `ensureValid()` (`calculatePath(); calculateLength();`, `SliderPath.cs:276-285`). -/
structure SliderPath where
  spec : SliderPathSpec
  calculatedPath : Array Vec2
  cumulativeLength : Array F64
  /-- `calculatedLength` (= `CalculatedDistance`) -/
  calculatedLength : F64
  /-- a B-spline subdivision of this path (or of an earlier path of the same slider, `Mods.modifySlider`) ran out
  of fuel (`bSplineToPiecewiseLinear`); the beatmap pipeline rejects such a slider (D72) -/
  fuelOut : Bool := false
deriving Inhabited, Repr

/-- The rejection for a slider path whose B-spline subdivision ran out of fuel (`SliderPath.fuelOut`, D72). -/
def pathFuelMsg : String := "slider path approximation fuel exhausted (more than 10^8 B-spline subdivisions)"

namespace SliderPath

/-- The Catmull "6px" optimisation in `calculateSubPath` (`SliderPath.cs:371-420`).
Returns the optimised path and the increase of `optimisedLength`. -/
def optimiseCatmullPath (subPath : Array Vec2) : Array Vec2 × F64 := Id.run do
  let mut optimisedPath : Array Vec2 := #[]
  let mut optimisedLength : F64 := 0
  let mut lastStart : Option Vec2 := none
  let mut lengthRemovedSinceStart : F64 := 0
  for i in [0:subPath.size] do
    match lastStart with
    | none =>
      optimisedPath := optimisedPath.push subPath[i]!
      lastStart := some subPath[i]!
    | some ls =>
      let distFromStart : F64 := F32.toF64 (Vec2.distance ls subPath[i]!)
      lengthRemovedSinceStart := lengthRemovedSinceStart + F32.toF64 (Vec2.distance subPath[i - 1]! subPath[i]!)
      -- catmull_segment_length = catmull_detail * 2 = 100
      if (6 : F64) < distFromStart || (i + 1) % 100 == 0 || i == subPath.size - 1 then
        optimisedPath := optimisedPath.push subPath[i]!
        optimisedLength := optimisedLength + (lengthRemovedSinceStart - distFromStart)
        lastStart := none
        lengthRemovedSinceStart := 0
  return (optimisedPath, optimisedLength)

/-- `calculateSubPath(subControlPoints, type)` (`SliderPath.cs:336-424`). Returns the sub-path,
the `optimisedLength` contribution and the B-spline fuel flag. -/
def calculateSubPath (sub : Array Vec2) (type : PathType) (optimiseCatmull : Bool) : Array Vec2 × F64 × Bool :=
  let bspline (degree : Option Int32) : Array Vec2 × F64 × Bool :=
    -- `PathApproximator.BSplineToPiecewiseLinear(subControlPoints, type.Degree ?? subControlPoints.Length)`
    let d : Nat := match degree with | some d => d.toNatClampNeg | none => sub.size
    let (p, fo) := PathApproximator.bSplineToPiecewiseLinear sub d
    (p, 0, fo)
  match type with
  | .linear => (PathApproximator.linearToPiecewiseLinear sub, 0, false)
  | .perfectCurve =>
    if sub.size != 3 then bspline none
    else
      let pr := PathApproximator.circularArcProperties sub
      if !pr.isValid then bspline none
      else
        let subPoints := PathApproximator.arcPointCount pr
        if subPoints ≥ 1000 then bspline none
        else
          let subPath := PathApproximator.circularArcToPiecewiseLinear sub
          if subPath.size == 0 then bspline none else (subPath, 0, false)
  | .catmull =>
    let subPath := PathApproximator.catmullToPiecewiseLinear sub
    if !optimiseCatmull then (subPath, 0, false) else
      let (p, ol) := optimiseCatmullPath subPath
      (p, ol, false)
  | .bspline d => bspline d

/-- `calculatePath()` (`SliderPath.cs:287-334`): the piecewise-linear path, `optimisedLength` and whether a
B-spline sub-path ran out of fuel. -/
def calculatePath (spec : SliderPathSpec) : Array Vec2 × F64 × Bool := Id.run do
  let cps := spec.controlPoints
  let mut path : Array Vec2 := #[]
  let mut optimisedLength : F64 := 0
  let mut fuelOut := false
  if cps.size == 0 then return (path, optimisedLength, fuelOut)
  let vertices := cps.map (·.position)
  let mut start := 0
  for i in [0:cps.size] do
    if cps[i]!.type.isNone && i < cps.size - 1 then continue
    let segmentVertices := vertices.extract start (i + 1)
    let segmentType := cps[start]!.type.getD .linear
    if segmentVertices.size == 1 then
      path := path.push segmentVertices[0]!
    else if segmentVertices.size > 1 then
      let (subPath, ol, fo) := calculateSubPath segmentVertices segmentType spec.optimiseCatmull
      optimisedLength := optimisedLength + ol
      fuelOut := fuelOut || fo
      let skipFirst := path.size > 0 && subPath.size > 0 && Vec2.eq path.back! subPath[0]!
      for j in [(if skipFirst then 1 else 0):subPath.size] do
        path := path.push subPath[j]!
    start := i
  return (path, optimisedLength, fuelOut)

/-- `calculateLength()` (`SliderPath.cs:426-485`), given the output of `calculatePath`. -/
def calculateLength (spec : SliderPathSpec) (path0 : Array Vec2) (optimisedLength : F64) : SliderPath := Id.run do
  let mut path := path0
  let mut calculatedLength : F64 := optimisedLength
  let mut cumulativeLength : Array F64 := #[0]
  for i in [0:path.size - 1] do
    let diff := path[i + 1]! - path[i]!
    calculatedLength := calculatedLength + F32.toF64 diff.length
    cumulativeLength := cumulativeLength.push calculatedLength
  let mk (p : Array Vec2) (c : Array F64) : SliderPath :=
    { spec, calculatedPath := p, cumulativeLength := c, calculatedLength }
  match spec.expectedDistance with
  | none => return mk path cumulativeLength
  | some expectedDistance =>
    if calculatedLength == expectedDistance then return mk path cumulativeLength
    -- In osu-stable, if the last two path points of a slider are equal, extension is not performed.
    if path.size ≥ 2 && Vec2.eq path[path.size - 1]! path[path.size - 2]! && calculatedLength < expectedDistance then
      return mk path (cumulativeLength.push calculatedLength)
    -- The last length is always incorrect
    cumulativeLength := cumulativeLength.pop
    let mut pathEndIndex : Int := path.size - 1
    if expectedDistance < calculatedLength then
      for _ in [0:path.size + 1] do
        if cumulativeLength.size > 0 && expectedDistance ≤ cumulativeLength.back! then
          cumulativeLength := cumulativeLength.pop
          path := path.pop  -- calculatedPath.RemoveAt(pathEndIndex--), pathEndIndex = path.Count - 1
          pathEndIndex := pathEndIndex - 1
    if pathEndIndex ≤ 0 then
      return mk path (cumulativeLength.push 0)
    let e := pathEndIndex.toNat
    let dir := (path[e]! - path[e - 1]!).normalized
    path := path.set! e (path[e - 1]! + dir * (expectedDistance - cumulativeLength.back!).toF32)
    return mk path (cumulativeLength.push expectedDistance)

/-- `ensureValid()`: the full cache for a path specification. -/
def compute (spec : SliderPathSpec) : SliderPath :=
  let (p, ol, fo) := calculatePath spec
  { calculateLength spec p ol with fuelOut := fo }

/-- `new SliderPath(controlPoints, expectedDistance)` with `OptimiseCatmull` as given. -/
def ofControlPoints (cps : Array PathControlPoint) (expected : Option F64) (optimiseCatmull : Bool) : SliderPath :=
  compute { controlPoints := cps, expectedDistance := expected, optimiseCatmull }

/-- `Distance => cumulativeLength.Count == 0 ? 0 : cumulativeLength[^1]` (`:119-126`). -/
def distance (p : SliderPath) : F64 :=
  if p.cumulativeLength.size == 0 then 0 else p.cumulativeLength.back!

/-- `CalculatedDistance` -/
def calculatedDistance (p : SliderPath) : F64 := p.calculatedLength

/-- `indexOfDistance(d)` (`:487-493`) -/
def indexOfDistance (p : SliderPath) (d : F64) : Int :=
  let i := binarySearchF64 p.cumulativeLength d
  if i < 0 then -i - 1 else i

/-- `progressToDistance(progress) => Math.Clamp(progress, 0, 1) * Distance` (`:495-498`) -/
def progressToDistance (p : SliderPath) (progress : F64) : F64 :=
  let c : F64 := if progress < 0 then 0 else if (1 : F64) < progress then 1 else progress
  c * p.distance

/-- `interpolateVertices(i, d)` (`:500-522`) -/
def interpolateVertices (p : SliderPath) (i : Int) (d : F64) : Vec2 :=
  let cp := p.calculatedPath
  if cp.size == 0 then Vec2.zero
  else if i ≤ 0 then cp[0]!
  else if i ≥ cp.size then cp.back!
  else
    let i := i.toNat
    let p0 := cp[i - 1]!
    let p1 := cp[i]!
    let d0 := p.cumulativeLength[i - 1]!
    let d1 := p.cumulativeLength[i]!
    if Precision.almostEqualsF64 d0 d1 then p0
    else
      let w := (d - d0) / (d1 - d0)
      p0 + (p1 - p0) * w.toF32

/-- `PositionAt(progress)` (`:205-211`) -/
def positionAt (p : SliderPath) (progress : F64) : Vec2 :=
  let d := p.progressToDistance progress
  p.interpolateVertices (p.indexOfDistance d) d

end SliderPath
end OsuModel.Beatmap
