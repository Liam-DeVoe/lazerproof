import OsuModel.Sim.Playable

/-!
# Screen-space geometry of the hit tests (float32, bit-exact)

* `Env`: the `HitObjectContainer` DrawInfo (screen ↔ gamefield), which is data of the fixed
  environment (D10, 1024x768, default config; dumped by `oracle --dump-env`), and the argon skin's
  slider path radius constant.
* The `DrawInfo` chain HitObjectContainer → DHO → scaleContainer → HitReceptor
  (`osu.Game.Rulesets.Osu/Objects/Drawables/DrawableHitCircle.cs:60-104, 266-275`) and
  HitObjectContainer → DrawableSlider → headContainer → DrawableSliderHead → … (`DrawableSlider.cs:96-128, 257-285`),
  following `Drawable.computeDrawInfo` (`osu.Framework/Graphics/Drawable.cs:1603-1616`).
* `CompositeDrawable.Contains` with corner radius (`osu.Framework/Graphics/Containers/CompositeDrawable.cs:1404-1414`).
* `SliderPath.PositionAt` / `CurvePositionAt` (`osu.Game/Rulesets/Objects/SliderPath.cs:205-211, 487-522`,
  `Types/IHasPathWithRepeats.cs:24-48`).
* `SliderInputManager.IsMouseInFollowArea` (`osu.Game.Rulesets.Osu/Objects/Drawables/SliderInputManager.cs:184-205`).
-/

namespace OsuModel.Sim
open OsuModel.Net

/-- One ancestor of the HitObjectContainer: `computeDrawInfo` inputs (`Drawable.cs:1603-1616`): `DrawPosition +
AnchorPosition + Parent.ChildOffset`, `DrawScale`, `Rotation`, `OriginPosition` (shear is 0 throughout). -/
structure ChainNode where
  typeName : String
  pos : Vec2
  scale : Vec2
  rot : F32
  origin : Vec2
deriving Inhabited

structure Env where
  /-- HitObjectContainer DrawInfo used by the input handler in the very first frame-stable step
  (before `OsuPlayfieldAdjustmentContainer.ScalingContainer.Update` first sets its scale). -/
  hocFirst : DrawInfo
  /-- HitObjectContainer DrawInfo from the second step on (constant). -/
  hoc : DrawInfo
  /-- `ArgonSliderBody.path_radius = ArgonMainCirclePiece.OUTER_GRADIENT_SIZE / 2` (compile-time float constant). -/
  argonPathRadius : F32
  /-- `HitObjectContainer.DrawSize` (= its `ChildSize`; relative children such as `DrawableSpinner` size from it). -/
  hocSize : Vec2
  /-- the HitObjectContainer's ancestor chain (root first, HOC last) in the first step and in steady state (BarrelRoll) -/
  chainFirst : Array ChainNode := #[]
  chain : Array ChainNode := #[]
deriving Inhabited

/-- Recompose a DrawInfo chain from the root (`new DrawInfo(null)` = identity), optionally overriding the rotation and
scale of the node named `OsuPlayfieldAdjustmentContainer` (BarrelRoll). -/
def composeChain (nodes : Array ChainNode) (pacRotScale : Option (F32 × Vec2) := none) : DrawInfo := Id.run do
  let mut di : DrawInfo := ⟨Mat3.identity, Mat3.identity⟩
  for n in nodes do
    let (rot, sc) := match pacRotScale with
      | some (r, s) => if n.typeName == "OsuPlayfieldAdjustmentContainer" then (r, s) else (n.rot, n.scale)
      | none => (n.rot, n.scale)
    di := di.applyTransformR n.pos sc rot n.origin
  return di

/-- `OsuHitObject.OBJECT_RADIUS` -/
def objectRadius : F32 := 64
/-- `OsuHitObject.OBJECT_DIMENSIONS` = (128, 128) -/
def objectDimensions : Vec2 := ⟨128, 128⟩

/-- `Drawable.computeAnchorPosition(size, Centre)` = `(size.X / 2f, size.Y / 2f)`. -/
def centreOf (size : Vec2) : Vec2 := ⟨size.x / 2, size.y / 2⟩

/-- `computeDrawInfo` for a child: `pos = DrawPosition + AnchorPosition (+ Parent.ChildOffset = 0)`,
then `ApplyTransform(pos, DrawScale, 0, 0, OriginPosition)`. `OriginPosition` subtracts the margin (0). -/
def childDrawInfo (parent : DrawInfo) (drawPosition anchorPosition scale origin : Vec2) : DrawInfo :=
  let pos := (drawPosition + anchorPosition) + Vec2.zero
  parent.applyTransform pos scale (origin - Vec2.zero)

/-- DHO (circle-like) → scaleContainer → HitReceptor, given the DHO's parent DrawInfo,
the DHO's position and anchor position, and `HitObject.Scale`. -/
def receptorFromDho (parent : DrawInfo) (dhoPos dhoAnchor : Vec2) (scale : F32) : DrawInfo :=
  -- DrawableHitCircle: Origin = Centre, Size = HitArea.DrawSize = OBJECT_DIMENSIONS, Scale 1.
  let dho := childDrawInfo parent dhoPos dhoAnchor ⟨1, 1⟩ (centreOf objectDimensions)
  -- scaleContainer: RelativeSizeAxes.Both (DrawSize = 1 * 128), Anchor/Origin Centre, Scale = HitObject.Scale.
  let scSize : Vec2 := ⟨1 * objectDimensions.x, 1 * objectDimensions.y⟩
  let sc := childDrawInfo dho Vec2.zero (Vec2.mul ⟨0.5, 0.5⟩ objectDimensions) ⟨scale, scale⟩ (centreOf scSize)
  -- HitReceptor: Size = OBJECT_DIMENSIONS, Anchor/Origin Centre.
  childDrawInfo sc Vec2.zero (Vec2.mul ⟨0.5, 0.5⟩ scSize) ⟨1, 1⟩ (centreOf objectDimensions)

/-- HitReceptor of a `DrawableHitCircle` (Position = StackedPosition, Anchor TopLeft). -/
def circleReceptor (env : Env) (h : HObj) : DrawInfo :=
  receptorFromDho env.hoc h.stacked Vec2.zero h.scale

/-- Slider body geometry from `SnakingSliderBody.Refresh` (`osu.Game.Rulesets.Osu/Skinning/SnakingSliderBody.cs`)
with the full calculated path: `Size = Path.Size` (= vertexBounds size) and
`PathOffset = Path.PositionInBoundingBox(Vertices[0]) = v0 - vertexBounds.TopLeft`
(`osu.Framework/Graphics/Lines/Path.cs:175-218`). The bounds start at 0 (`minX = 0` …). -/
structure SliderGeom where
  pathRadius : F32
  size : Vec2
  origin : Vec2
  drawInfo : DrawInfo
  headReceptor : DrawInfo
deriving Inhabited

/-- `SliderBody.PathOffset => path.PositionInBoundingBox(path.Vertices[0])` (`SliderBody.cs:32`,
`SnakingSliderBody.cs:119`) indexes an empty vertex list → `ArgumentOutOfRangeException`. -/
def emptyPathMsg : String := "lazer would throw: Path.Vertices[0] on an empty slider path (SnakingSliderBody.cs:119)"

def sliderGeom (env : Env) (h : HObj) (sd : SliderData) : Except String SliderGeom := do
  -- ArgonSliderBody: PathRadius = path_radius * scale (`ArgonSliderBody.cs:23`).
  let r : F32 := env.argonPathRadius * h.scale
  let mut minX : F32 := 0
  let mut minY : F32 := 0
  let mut maxX : F32 := 0
  let mut maxY : F32 := 0
  for v in sd.path do
    minX := F32.min minX (v.x - r)
    minY := F32.min minY (v.y - r)
    maxX := F32.max maxX (v.x + r)
    maxY := F32.max maxY (v.y + r)
  let size : Vec2 := if sd.path.size > 0 then ⟨maxX - minX, maxY - minY⟩ else Vec2.zero
  let tl : Vec2 := if sd.path.size > 0 then ⟨minX, minY⟩ else Vec2.zero
  let some v0 := sd.path[0]? | throw emptyPathMsg
  let origin := v0 - tl
  -- DrawableSlider: Position = StackedPosition, Anchor TopLeft, Scale 1, custom OriginPosition, Size = body size.
  let di := childDrawInfo env.hoc h.stacked Vec2.zero ⟨1, 1⟩ origin
  -- headContainer: RelativeSizeAxes.Both, at (0,0), Origin TopLeft → DrawInfo unchanged; DrawSize = (1*W, 1*H).
  let hcSize : Vec2 := ⟨1 * size.x, 1 * size.y⟩
  let hc := childDrawInfo di Vec2.zero (Vec2.mul Vec2.zero size) ⟨1, 1⟩ Vec2.zero
  -- DrawableSliderHead: Position (0,0); RelativeAnchorPosition = OriginPosition / DrawSize (`DrawableSlider.cs:277-283`),
  -- AnchorPosition = RelativeAnchorPosition * headContainer.ChildSize.
  let relAnchor := Vec2.cdiv origin size
  let head := receptorFromDho hc Vec2.zero (Vec2.mul relAnchor hcSize) h.scale
  return { pathRadius := r, size, origin, drawInfo := di, headReceptor := head }

/-! ### Geometry with transformable DHO state (M7: mods move/scale/rotate DHOs; pooled sliders keep stale body geometry) -/

/-- A DHO's `Position`, `Scale`, `Rotation`. -/
structure Placement where
  pos : Vec2
  scale : Vec2 := ⟨1, 1⟩
  rot : F32 := 0
deriving Inhabited

def childDrawInfoR (parent : DrawInfo) (drawPosition anchorPosition scale : Vec2) (rot : F32) (origin : Vec2) : DrawInfo :=
  let pos := (drawPosition + anchorPosition) + Vec2.zero
  parent.applyTransformR pos scale rot (origin - Vec2.zero)

/-- DHO (circle-like, Origin Centre, Size 128) → scaleContainer → HitReceptor with the DHO's own placement. -/
def receptorFromPlacement (parent : DrawInfo) (pl : Placement) (dhoAnchor : Vec2) (scale : F32) : DrawInfo :=
  let dho := childDrawInfoR parent pl.pos dhoAnchor pl.scale pl.rot (centreOf objectDimensions)
  let scSize : Vec2 := ⟨1 * objectDimensions.x, 1 * objectDimensions.y⟩
  let sc := childDrawInfo dho Vec2.zero (Vec2.mul ⟨0.5, 0.5⟩ objectDimensions) ⟨scale, scale⟩ (centreOf scSize)
  childDrawInfo sc Vec2.zero (Vec2.mul ⟨0.5, 0.5⟩ scSize) ⟨1, 1⟩ (centreOf objectDimensions)

/-- `SnakingSliderBody.Refresh` for the body's current `PathRadius`: `(Size, PathOffset)`. -/
def bodyRefresh (sd : SliderData) (r : F32) : Except String (Vec2 × Vec2) := do
  let mut minX : F32 := 0
  let mut minY : F32 := 0
  let mut maxX : F32 := 0
  let mut maxY : F32 := 0
  for v in sd.path do
    minX := F32.min minX (v.x - r)
    minY := F32.min minY (v.y - r)
    maxX := F32.max maxX (v.x + r)
    maxY := F32.max maxY (v.y + r)
  let size : Vec2 := if sd.path.size > 0 then ⟨maxX - minX, maxY - minY⟩ else Vec2.zero
  let tl : Vec2 := if sd.path.size > 0 then ⟨minX, minY⟩ else Vec2.zero
  let some v0 := sd.path[0]? | throw emptyPathMsg
  return (size, v0 - tl)

/-- Slider geometry from the DrawableSlider's current state: placement, `Size`, `OriginPosition`, the head's
`RelativeAnchorPosition` and the head DHO's own placement (`DrawableSlider.cs:257-285`). -/
def sliderGeomP (env : Env) (h : HObj) (pl : Placement) (size origin relAnchor : Vec2) (headPl : Placement) : SliderGeom :=
  let di := childDrawInfoR env.hoc pl.pos Vec2.zero pl.scale pl.rot origin
  let hcSize : Vec2 := ⟨1 * size.x, 1 * size.y⟩
  let hc := childDrawInfo di Vec2.zero (Vec2.mul Vec2.zero size) ⟨1, 1⟩ Vec2.zero
  let head := receptorFromPlacement hc headPl (Vec2.mul relAnchor hcSize) h.scale
  { pathRadius := env.argonPathRadius * h.scale, size, origin, drawInfo := di, headReceptor := head }

/-- `CompositeDrawable.Contains` for the HitReceptor (`CornerRadius = 64`, `CornerExponent = 2`,
`DrawRectangle = (0, 0, 128, 128)`): `DrawRectangle.Shrink(cR).DistanceExponentiated(ToLocalSpace(p), cE) <= Math.Pow(cR, cE)`. -/
/- Hoisted constants (closed terms are initialised once; float literals compile to runtime
`ofScientific` calls in Lean 4.35 — see docs/proof-pipeline.md). -/
def receptorCornerExponent : F32 := 2
/-- effectiveCornerRadius = CornerRadius * 0.8f * CornerExponent / 2 + 0.2f * CornerRadius -/
def receptorEffectiveCornerRadius : F32 :=
  objectRadius * (0.8 : F32) * receptorCornerExponent / 2 + (0.2 : F32) * objectRadius
/-- `Math.Pow(cR, cE)` (double) -/
def receptorCornerRadiusPow : F64 := F64.pow (F32.toF64 receptorEffectiveCornerRadius) (F32.toF64 receptorCornerExponent)
def f32zero : F32 := 0
def f32one : F32 := 1
def f32_128 : F32 := 128
def f32_2_4 : F32 := 2.4
def f64zero : F64 := 0
def f64one : F64 := 1

def receptorContains (di : DrawInfo) (screen : Vec2) : Bool :=
  let cornerExponent : F32 := receptorCornerExponent
  let cR : F32 := receptorEffectiveCornerRadius
  if cR == f32zero then
    -- base.Contains: DrawRectangle.Contains(local) (not reached: cR = 64)
    let l := di.toLocal screen
    0 ≤ l.x && l.x ≤ 128 && 0 ≤ l.y && l.y ≤ 128
  else
    let l := di.toLocal screen
    -- RectangleF.Inflate(-(cR)): X - (-cR), Y - (-cR), W + (-cR + -cR), H + (-cR + -cR)
    let rx : F32 := f32zero - (-cR)
    let ry : F32 := f32zero - (-cR)
    let rw : F32 := f32_128 + ((-cR) + (-cR))
    let rh : F32 := f32_128 + ((-cR) + (-cR))
    let right := rx + rw
    let bottom := ry + rh
    let distX := F32.max f32zero (F32.max (l.x - right) (rx - l.x))
    let distY := F32.max f32zero (F32.max (l.y - bottom) (ry - l.y))
    let lhs : F32 := F32.pow distX cornerExponent + F32.pow distY cornerExponent
    F32.toF64 lhs ≤ receptorCornerRadiusPow

/-- Spinner geometry: `DrawableSpinner` (RelativeSizeAxes.Both, Origin Centre, Position = HitObject.Position)
→ `AspectContainer` (RelativeSizeAxes.Y, Anchor/Origin Centre, `Width = DrawHeight` in `Update`)
→ `SpinnerRotationTracker` (RelativeSizeAxes.Both) (`DrawableSpinner.cs:96-110`, `Screens/Ranking/AspectContainer.cs`).
`aspect` is the DrawInfo used by `SpinnerRotationTracker.OnMouseMove` (`Parent!.ToLocalSpace`), `trackerSize` its `DrawSize`. -/
structure SpinnerGeom where
  aspect : DrawInfo
  trackerSize : Vec2
deriving Inhabited

def spinnerGeomP (env : Env) (pl : Placement) : SpinnerGeom :=
  -- DrawableSpinner: DrawSize = (1 * W, 1 * H) of the HitObjectContainer's ChildSize (RelativeToAbsoluteFactor = ChildSize / (1,1)).
  let conv : Vec2 := ⟨env.hocSize.x / 1, env.hocSize.y / 1⟩
  let sSize : Vec2 := ⟨1 * conv.x, 1 * conv.y⟩
  let sp := childDrawInfoR env.hoc pl.pos Vec2.zero pl.scale pl.rot (centreOf sSize)
  -- AspectContainer: RelativeSizeAxes.Y → DrawSize = (Width, 1 * H'), Width = DrawHeight.
  let sConv : Vec2 := ⟨sSize.x / 1, sSize.y / 1⟩
  let aH : F32 := 1 * sConv.y
  let aSize : Vec2 := ⟨aH, aH⟩
  let aspect := childDrawInfo sp Vec2.zero (Vec2.mul ⟨0.5, 0.5⟩ sSize) ⟨1, 1⟩ (centreOf aSize)
  let aConv : Vec2 := ⟨aSize.x / 1, aSize.y / 1⟩
  { aspect, trackerSize := ⟨1 * aConv.x, 1 * aConv.y⟩ }

def spinnerGeom (env : Env) (h : HObj) : SpinnerGeom := spinnerGeomP env { pos := h.pos }

/-- `float.RadiansToDegrees(x) = (x * 180f) / float.Pi` (checked bit-exact on .NET 10 for 2M inputs). -/
def f32_180 : F32 := 180
def radiansToDegrees (x : F32) : F32 := (x * f32_180) / Float32.ofBits 0x40490FDB

/-! ## Slider path -/

/-- `double.CompareTo(double)` (`Comparer<double>.Default`): NaN is smallest, NaN == NaN. -/
def compareD (a b : F64) : Int :=
  if a < b then -1 else if b < a then 1 else if a == b then 0
  else if a.isNaN then (if b.isNaN then 0 else -1) else 1

/-- `List<double>.BinarySearch` with the default comparer (`Array.BinarySearch` / `ArraySortHelper`). -/
def binarySearchD (a : Array F64) (v : F64) : Int := bsearch a (compareD · v)

/-- `SliderPath.Distance` = last cumulative length (0 if empty). -/
def SliderData.distance (sd : SliderData) : F64 := sd.cumLen.back?.getD 0

/-- `SliderPath.PositionAt(progress)` -/
def SliderData.positionAt (sd : SliderData) (progress : F64) : Except String Vec2 := do
  -- `Math.Clamp(progress, 0, 1)`: literal bounds, never throws
  let clamped := if progress < f64zero then f64zero else if f64one < progress then f64one else progress
  let d := clamped * sd.distance
  let i0 := binarySearchD sd.cumLen d
  let i := if i0 < 0 then -i0 - 1 else i0   -- `~i`
  -- `interpolateVertices(i, d)` (`SliderPath.cs`)
  if h0 : sd.path.size = 0 then return Vec2.zero
  else if h1 : i ≤ 0 then return sd.path[0]
  else if h2 : i ≥ sd.path.size then return sd.path[sd.path.size - 1]
  else
    let k := (i - 1).toNat
    have hk : k + 1 < sd.path.size := by omega
    let p0 := sd.path[k]
    let p1 := sd.path[k + 1]
    -- `cumulativeLength[i-1]`, `cumulativeLength[i]`: lazer keeps one length per path vertex
    let some d0 := sd.cumLen[k]? | throw s!"lazer would throw: cumulativeLength[{k}] out of range"
    let some d1 := sd.cumLen[k + 1]? | throw s!"lazer would throw: cumulativeLength[{k+1}] out of range"
    if almostEqualsD d0 d1 then return p0
    else
      let w := (d - d0) / (d1 - d0)
      return p0 + Vec2.scale (p1 - p0) (F64.toF32 w)

/-- `SpanAt(progress) = (int)(progress * SpanCount)` -/
def SliderData.spanAt (sd : SliderData) (progress : F64) : Int32 :=
  F64.toInt32 (progress * F64.ofInt sd.spanCount)

/-- `ProgressAt(progress)`: `p = progress * SpanCount % 1; if (SpanAt(progress) % 2 == 1) p = 1 - p`. -/
def SliderData.progressAt (sd : SliderData) (progress : F64) : F64 :=
  let p := fmod1 (progress * F64.ofInt sd.spanCount)
  if (sd.spanAt progress).toInt % 2 == 1 then 1 - p else p

/-- `CurvePositionAt(progress) = Path.PositionAt(ProgressAt(progress))` (relative to the head, unstacked). -/
def SliderData.curvePositionAt (sd : SliderData) (progress : F64) : Except String Vec2 :=
  sd.positionAt (sd.progressAt progress)

/-- `SliderInputManager.getFollowRadius(expanded)`: `(float)slider.Radius`, `* DrawableSliderBall.FOLLOW_AREA (2.4f)`. -/
def followRadius (h : HObj) (expanded : Bool) : F32 :=
  let r := F64.toF32 h.radius
  if expanded then r * f32_2_4 else r

/-- Mouse position in the slider's coordinate system: `slider.ToLocalSpace(pos) - slider.OriginPosition`. -/
def mouseInSlider (g : SliderGeom) (screen : Vec2) : Vec2 := g.drawInfo.toLocal screen - g.origin

/-- `IsMouseInFollowArea(expanded)` at time `t` (mouse = `screenSpaceMousePosition`, none → false). -/
def isMouseInFollowArea (h : HObj) (sd : SliderData) (g : SliderGeom) (mouse : Option Vec2) (t : F64)
    (expanded : Bool) : Except String Bool :=
  match mouse with
  | none => pure false
  | some pos => do
    let radius := followRadius h expanded
    let fp0 := (t - h.start) / sd.duration
    -- `Math.Clamp(…, 0, 1)`: literal bounds, never throws
    let followProgress := if fp0 < f64zero then f64zero else if f64one < fp0 then f64one else fp0
    let follow ← sd.curvePositionAt followProgress
    let m := mouseInSlider g pos
    return (m - follow).lengthSquared ≤ radius * radius

end OsuModel.Sim
