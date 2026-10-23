import OsuModel.Beatmap.Vector2

/-!
# `osu.Framework.Utils.PathApproximator` and `CircularArcProperties` (float32 geometry)

Transcribed from osu-framework 2026.921.1 (`osu.Framework/Utils/PathApproximator.cs`,
`osu.Framework/Utils/CircularArcProperties.cs`; the shipped `ppy.osu.Framework` NuGet DLL was
decompiled and spot-checked against this source). Every `Vector2` operation is float32 in source
order; `int` factors are converted to `float`; the arc uses `double` `Math.Atan2/Cos/Sin/Acos`
(glibc, see `OsuModel/Net/Libm.lean`).

The stack-based DFS of `BSplineToPiecewiseLinear` (`:79-144`) is modelled with an explicit stack;
its buffer reuse (`freeBuffers`, the aliasing of `subdivisionBuffer1` as both `midpoints` and `r`
in `bezierApproximate`) is value-transparent (each aliased cell is read before it is overwritten).
-/

namespace OsuModel.Beatmap
open OsuModel.Net

namespace PathApproximator

/-- `BEZIER_TOLERANCE = 0.25f` -/
def BEZIER_TOLERANCE : F32 := 0.25
/-- `catmull_detail = 50` -/
def catmull_detail : Nat := 50
/-- `circular_arc_tolerance = 0.1f` -/
def circular_arc_tolerance : F32 := 0.1

/-! Hoisted float constants (compiled Lean evaluates float literals at runtime, see
`docs/proof-pipeline.md` "Lean perf rules"); top-level constants are computed once. -/
def k0_25 : F32 := 0.25
def k0_5 : F32 := 0.5
def k2 : F32 := 2
def k3 : F32 := 3
def k4 : F32 := 4
def k5 : F32 := 5
def kFlat : F32 := BEZIER_TOLERANCE * BEZIER_TOLERANCE * 4
def kCatmullDetail : F32 := F32.ofInt catmull_detail

/-- `bSplineToBezierInternal(controlPoints, ref degree)` (`PathApproximator.cs:774-821`).
Returns the Bezier segments in processing order (the C# code reverses the stack so that the
first segment is on top). -/
def bSplineToBezierInternal (controlPoints : Array Vec2) (degree0 : Nat) : Array (Array Vec2) × Nat := Id.run do
  let degree := min degree0 (controlPoints.size - 1)
  let pointCount := controlPoints.size - 1
  let mut points := controlPoints
  if degree == pointCount then
    return (#[points], degree)
  let mut result : Array (Array Vec2) := #[]
  for i in [0:pointCount - degree] do
    let mut subBezier : Array Vec2 := Array.replicate (degree + 1) Vec2.zero
    subBezier := subBezier.set! 0 points[i]!
    for j in [0:degree - 1] do
      subBezier := subBezier.set! (j + 1) points[i + 1]!
      for k in [1:degree - j] do
        let l : Nat := min k (pointCount - degree - i)
        -- points[i + k] = (l * points[i + k] + points[i + k + 1]) / (l + 1);
        let lf := F32.ofInt l
        points := points.set! (i + k) (((points[i + k]! * lf) + points[i + k + 1]!) / F32.ofInt (l + 1))
    subBezier := subBezier.set! degree points[i + 1]!
    result := result.push subBezier
  result := result.push (points.extract (pointCount - degree) points.size)
  return (result, degree)

/-- `bezierIsFlatEnough` (`:831-840`). -/
def bezierIsFlatEnough (cp : Array Vec2) : Bool := Id.run do
  for i in [1:cp.size - 1] do
    if kFlat < (cp[i - 1]! - k2 * cp[i]! + cp[i + 1]!).lengthSquared then
      return false
  return true

/-- `bezierSubdivide(controlPoints, l, r, subdivisionBuffer, count)` (`:852-867`): returns `(l, r)`. -/
def bezierSubdivide (cp : Array Vec2) (count : Nat) : Array Vec2 × Array Vec2 := Id.run do
  let mut midpoints := cp.extract 0 count
  let mut l : Array Vec2 := Array.replicate count Vec2.zero
  let mut r : Array Vec2 := Array.replicate count Vec2.zero
  for i in [0:count] do
    l := l.set! i midpoints[0]!
    r := r.set! (count - i - 1) midpoints[count - i - 1]!
    for j in [0:count - i - 1] do
      midpoints := midpoints.set! j ((midpoints[j]! + midpoints[j + 1]!) / k2)
  return (l, r)

/-- `bezierApproximate(controlPoints, output, ..., count)` (`:878-896`): appends to `output`. -/
def bezierApproximate (cp : Array Vec2) (output : Array Vec2) (count : Nat) : Array Vec2 := Id.run do
  let (l0, r) := bezierSubdivide cp count
  let mut l := l0 ++ Array.replicate (count - 1) Vec2.zero
  for i in [0:count - 1] do
    l := l.set! (count + i) r[i + 1]!
  let mut out := output.push cp[0]!
  for i in [1:count - 1] do
    let index := 2 * i
    let p := k0_25 * (l[index - 1]! + k2 * l[index]! + l[index + 1]!)
    out := out.push p
  return out

/-- `BSplineToPiecewiseLinear(controlPoints, degree)` (`:79-144`). `degree ≥ 1` is a precondition
(lazer only passes `Degree > 0` or the point count). The second component is `true` iff the subdivision fuel ran out
(`toFlatten` still non-empty): lazer has no bound, so the model rejects such a path (D72, D71(5); the callers turn the
flag into a rejection) instead of using the truncated output. -/
def bSplineToPiecewiseLinear (controlPoints : Array Vec2) (degree0 : Nat) : Array Vec2 × Bool := Id.run do
  if controlPoints.size < 2 then
    return (if controlPoints.size == 0 then #[] else #[controlPoints[0]!], false)
  let degree := min degree0 (controlPoints.size - 1)
  let pointCount := controlPoints.size - 1
  let (segs, degree) := bSplineToBezierInternal controlPoints degree
  -- stack: top = last element of the array
  let mut toFlatten : Array (Array Vec2) := segs.reverse
  let mut output : Array Vec2 := #[]
  -- Termination: each subdivision halves the control polygon's second differences; in float32
  -- arithmetic it terminates for all finite inputs (lazer relies on this too). The fuel bound is
  -- generous and never reached on the corpus (docs/fidelity-evidence.md §2.1-10: only a B-spline segment with
  -- ≳ 25k zigzag control points can exhaust it); exhaustion is reported in the flag.
  for _ in [0:100000000] do
    if toFlatten.size == 0 then break
    let parent := toFlatten.back!
    toFlatten := toFlatten.pop
    if bezierIsFlatEnough parent then
      output := bezierApproximate parent output (degree + 1)
    else
      let (leftChild, rightChild) := bezierSubdivide parent (degree + 1)
      toFlatten := toFlatten.push rightChild
      toFlatten := toFlatten.push (leftChild.extract 0 (degree + 1))
  output := output.push controlPoints[pointCount]!
  return (output, toFlatten.size != 0)

/-- `BezierToPiecewiseLinear(controlPoints)` = `BSplineToPiecewiseLinear(cp, Math.Max(1, cp.Length - 1))`.
The fuel flag is dropped: the only caller is `circularArcToPiecewiseLinear`'s invalid-arc branch, which
`calculateSubPath` never reaches (it tests `circularArcProperties … |>.isValid` on the same points first). -/
def bezierToPiecewiseLinear (controlPoints : Array Vec2) : Array Vec2 :=
  (bSplineToPiecewiseLinear controlPoints (max 1 (controlPoints.size - 1))).1

/-- `catmullFindPoint(ref v1, ref v2, ref v3, ref v4, t)` (`:907-917`). -/
def catmullFindPoint (v1 v2 v3 v4 : Vec2) (t : F32) : Vec2 :=
  let t2 := t * t
  let t3 := t * t2
  let x := k0_5 * (k2 * v2.x + (-v1.x + v3.x) * t
      + (k2 * v1.x - k5 * v2.x + k4 * v3.x - v4.x) * t2
      + (-v1.x + k3 * v2.x - k3 * v3.x + v4.x) * t3)
  let y := k0_5 * (k2 * v2.y + (-v1.y + v3.y) * t
      + (k2 * v1.y - k5 * v2.y + k4 * v3.y - v4.y) * t2
      + (-v1.y + k3 * v2.y - k3 * v3.y + v4.y) * t3)
  ⟨x, y⟩

/-- `CatmullToPiecewiseLinear(controlPoints)` (`:150-169`): 50 steps per segment, two points per step. -/
def catmullToPiecewiseLinear (cp : Array Vec2) : Array Vec2 := Id.run do
  let mut result : Array Vec2 := #[]
  for i in [0:cp.size - 1] do
    let v1 := if i > 0 then cp[i - 1]! else cp[i]!
    let v2 := cp[i]!
    let v3 := if i < cp.size - 1 then cp[i + 1]! else v2 + v2 - v1
    let v4 := if i + 2 < cp.size then cp[i + 2]! else v3 + v3 - v2
    for c in [0:catmull_detail] do
      result := result.push (catmullFindPoint v1 v2 v3 v4 (F32.ofInt c / kCatmullDetail))
      result := result.push (catmullFindPoint v1 v2 v3 v4 (F32.ofInt (c + 1) / kCatmullDetail))
  return result

/-- `LinearToPiecewiseLinear(controlPoints)` (`:255-263`): the input. -/
def linearToPiecewiseLinear (cp : Array Vec2) : Array Vec2 := cp

/-- `Math.PI` -/
def PI : F64 := F64.ofBitsN 0x400921FB54442D18

/-- `CircularArcProperties` (`CircularArcProperties.cs`). -/
structure CircularArcProperties where
  isValid : Bool
  thetaStart : F64 := 0
  thetaRange : F64 := 0
  direction : F64 := 0
  radius : F32 := 0
  centre : Vec2 := Vec2.zero
deriving Inhabited, Repr

/-- `new CircularArcProperties(ReadOnlySpan<Vector2> controlPoints)` (`CircularArcProperties.cs:34-87`). -/
def circularArcProperties (cp : Array Vec2) : CircularArcProperties := Id.run do
  let a := cp[0]!
  let b := cp[1]!
  let c := cp[2]!
  if Precision.almostEqualsF32 0 ((b.y - a.y) * (c.x - a.x) - (b.x - a.x) * (c.y - a.y)) then
    return { isValid := false }
  let d : F32 := k2 * (a.x * (b - c).y + b.x * (c - a).y + c.x * (a - b).y)
  let aSq := a.lengthSquared
  let bSq := b.lengthSquared
  let cSq := c.lengthSquared
  let centre : Vec2 := (Vec2.mk (aSq * (b - c).y + bSq * (c - a).y + cSq * (a - b).y)
                                (aSq * (c - b).x + bSq * (a - c).x + cSq * (b - a).x)) / d
  let dA := a - centre
  let dC := c - centre
  let radius := dA.length
  let thetaStart := F64.atan2 (F32.toF64 dA.y) (F32.toF64 dA.x)
  let mut thetaEnd := F64.atan2 (F32.toF64 dC.y) (F32.toF64 dC.x)
  -- `while (thetaEnd < ThetaStart) thetaEnd += 2 * Math.PI;` — atan2 ∈ [-π, π]: at most 2 steps
  for _ in [0:4] do
    if thetaEnd < thetaStart then thetaEnd := thetaEnd + PI * 2
  let mut direction : F64 := 1
  let mut thetaRange := thetaEnd - thetaStart
  let ortho0 := c - a
  let orthoAtoC : Vec2 := ⟨ortho0.y, -ortho0.x⟩
  if Vec2.dot orthoAtoC (b - a) < 0 then
    direction := -direction
    thetaRange := PI * 2 - thetaRange
  return { isValid := true, thetaStart, thetaRange, direction, radius, centre }

/-- The number of arc points: `2 * Radius <= 0.1f ? 2 : Math.Max(2, (int)Math.Ceiling(ThetaRange /
(2 * Math.Acos(1 - 0.1f / Radius))))` (`PathApproximator.cs:186`; identical expression at
`SliderPath.cs:355`). -/
def arcPointCount (pr : CircularArcProperties) : Int32 :=
  if k2 * pr.radius ≤ circular_arc_tolerance then 2
  else
    let inner : F32 := 1 - circular_arc_tolerance / pr.radius
    let n := F64.toInt32 (F64.ceiling (pr.thetaRange / ((2 : F64) * F64.acos (F32.toF64 inner))))
    if n < 2 then 2 else n

/-- `CircularArcToPiecewiseLinear(controlPoints)` (`:175-199`). -/
def circularArcToPiecewiseLinear (cp : Array Vec2) : Array Vec2 := Id.run do
  let pr := circularArcProperties cp
  if !pr.isValid then return bezierToPiecewiseLinear cp
  let amountPoints := arcPointCount pr
  let mut output : Array Vec2 := #[]
  for i in [0:amountPoints.toNatClampNeg] do
    let fract : F64 := F64.ofInt i / F64.ofInt (amountPoints.toInt - 1)
    let theta := pr.thetaStart + pr.direction * fract * pr.thetaRange
    let o : Vec2 := (Vec2.mk (F64.cos theta).toF32 (F64.sin theta).toF32) * pr.radius
    output := output.push (pr.centre + o)
  return output

end PathApproximator
end OsuModel.Beatmap
