# Mods that move, rescale or rotate objects or the playfield (lazer 2026.1005.0-lazer)

Scope: every osu! mod that changes where a hit object is, or how large or rotated it is in screen space, and so can
change a hit test (circle/head hover, slider follow area, spinner angle). Covered: Mirror (and HR's flip), Random,
Target Practice, Freeze Frame, Grow, Deflate, Spin In, Transform, Wiggle, Depth, Magnetised, Repel, Barrel Roll.
Hidden, Traceable, Flashlight, Bubbles, Approach Different, No Scope, Bloom, Blinds and Synesthesia are checked and
confirmed visual-only, with one exception for Hidden (§8.1). It also covers the framework machinery these mods depend
on: the transform system, easing, `DrawInfo` matrices, presence and hover timing.

Paths: `L/` = `~/lazerproof/lazer`, `F/` = `~/lazerproof/osu-framework/osu.Framework`, `G/` = `L/osu.Game`,
`O/` = `L/osu.Game.Rulesets.Osu`. Line numbers match the pinned checkouts (`LAZER_COMMIT`, framework 2026.921.1).
Types: `float` = binary32, `double` = binary64. RyuJIT does `float` ops in binary32, does not contract to FMA, and
evaluates left to right. `MathF.*` = glibc `*f`, `Math.*` = glibc double libm (trust boundary, glibc 2.39). osuTK is
`ppy.osuTK.NS20 1.0.211` (no source in the tree).
**[verify]** marked facts taken from dotnet/runtime or OpenTK source knowledge. All are now **[verified]** against
the decompiled binaries and by `nettest` differential tests that call the real `osuTK.dll` / `osu.Framework.dll` /
.NET 10.0.13 (op numbers below; `docs/net-float.md` "Library primitives"; Lean in `model/OsuModel/Net/{OsuTK,
Framework,Random,Decimal,SysMisc}.lean`).

Companion docs: `docs/lazer-map.md` §3.1 (step phases), §5, §6; `docs/mods/difficulty-rate-fail.md` §1
(application order), §2 (mod-setting JSON and `BindableNumber` decimal rounding, used by every setting below).

---------------------------------------------------------------------------------------------------

## 0. Summary for modellers

| Mod | Where it acts | Affects hit tests through | Determinism inputs |
|---|---|---|---|
| MR Mirror, HR | `IApplicableToHitObject` (playable step 7, before stacking) | `HitObject.Position`, path control points | none |
| RD Random | `IApplicableToBeatmap` (step 9, **after** stacking) | `Position`, path rotation and flips | `Seed` (int), `System.Random`, glibc `atan2f/cosf/sinf/exp/log/sqrt/sin` |
| TP Target Practice | step 9: replaces all objects with circles; AR×0.5 | new positions; DHO `Scale` 0.5→1 linear | `Seed`, `System.Random` |
| FR Freeze Frame | step 9: `TimePreempt +=` | lifetime start, and every preempt-based transform | none |
| GR/DF | DHO state transform `Scale` | circle and slider DHO scale, OutSine over preempt | `StartScale` |
| SI Spin In | DHO state transforms `Rotation`, `Scale` | circles: rot 360→0, scale (2,0)→1; sliders: scale 0→1; InOutSine; **slider heads too** | none |
| TR Transform | DHO state transform `Position` | circles, sliders, **spinners**; InOutSine | the mod's mutable `theta` (depends on the global order of state updates) |
| WG Wiggle | DHO state transforms `Position` | circles, sliders, **slider heads**, spinners; linear 100 ms segments | `System.Random((int)StartTime)`, `Strength` |
| DP Depth | `IUpdatableByPlayfield`, every step | DHO `Position` and `Scale` from time | `MaxDepth` |
| MG/RP | `IUpdatableByPlayfield`, every step | DHO `Position`, damped by `ElapsedFrameTime` | strength, step schedule, cursor |
| BR Barrel Roll | `IUpdatableByPlayfield` rotates the playfield adjustment container; constant scale | **only float rounding** (replay positions are in gamefield space), plus forced hover recompute (§2.6) | `SpinSpeed`, `Direction` |
| HD | visual (DHO input ignores alpha, §1.7/§8.1); fades only gate `Update` of judged DHOs | — | — |
| TC FL BU AD NS BM BL SY MU | visual only | — | — |

Hard requirements that follow:
1. The model needs a faithful **transform tracker** (§1). Closed forms per mod are not enough. Transforms are
   re-created on every state change (judgements included), start values are read lazily, adding a transform can
   apply it immediately, and some mods are dispatched twice to slider heads (§1.6).
2. Transform start times are `fl(C + fl(S − C))`, where `C` is the clock time when the state is applied, not `S` (§1.2).
3. A hit test in the input phase of step *k* sees drawable state from the end of step *k−1* (transforms evaluated at
   `t_{k−1}`, and `IUpdatableByPlayfield` positions from step *k−1*). Transforms added during step *k* can apply
   immediately (§1.4).
4. `DrawInfo` composition must support rotation and non-uniform scale, with the FLOAT_EPSILON scale clamp (§2.1).
   For BR the whole ancestor chain is needed per step, and it has to be dumped from the oracle, because a static
   derivation does not reproduce the dumped matrix bits (§2.5).

---------------------------------------------------------------------------------------------------

## 1. Framework transform system (exact semantics)

### 1.1 Objects and ordering
- Every `DrawableHitObject` is a `PoolableDrawableWithLifetime` with **`RemoveCompletedTransforms => false`**
  (`G/Rulesets/Objects/Pooling/PoolableDrawableWithLifetime.cs:72`). Completed transforms stay in the list, and the
  rewind branches of the tracker are live.
- Transforms are grouped per target member (`Scale`, `Position`, `Rotation`, `Alpha`, … each in its own
  `TargetGroupingTransformTracker`; `TransformCustom` grouping = member name). Each tracker keeps a `SortedList` ordered
  by `(StartTime, TransformID)` (`F/Graphics/Transforms/Transform.cs:70-85`). `TransformID` is a per-tracker
  counter `++currentTransformID` on add (`TargetGroupingTransformTracker.cs:225-252`).
- **`AddTransform` removes every later transform (in sort order) with the same member** (`:242-251`). A new transform
  always has the highest ID, so this removes the same-member transforms with a *strictly greater StartTime*.

### 1.2 Start/end times (`Transformable.cs`, `TransformSequence.cs`, `TransformableExtensions.cs`)
```
TransformStartTime        = Clock.CurrentTime + TransformDelay                    (Transformable.cs:35)
BeginAbsoluteSequence(S):   TransformDelay := S − Clock.CurrentTime                (:335-340; restored on Dispose)
  (CompositeDrawable recursive=true does the same for the whole subtree; CompositeDrawable.cs:1317-1331)
PopulateTransform:          t.StartTime = TransformStartTime; t.EndTime = t.StartTime + duration   (TransformableExtensions.cs:143-165)
new TransformSequence:      startTime = currentTime = lastEndTime = TransformStartTime              (TransformSequence.cs:54)
seq.X(...) (chained):       Append: BeginAbsoluteSequence(currentTime, false) then o.X(...)          (:128-150)
seq.Add(t):                 if last == null || t.EndTime > lastEndTime: lastEndTime = t.EndTime     (:96-104)
.Then():                    currentTime = max(currentTime, lastEndTime); Delay(0)                    (:367-375, :386-390)
```
So with `C = Clock.CurrentTime` (the frame-stable time of the step during which the state update runs; DHOs use the
FSC clock), a transform requested at absolute time `S` gets `StartTime = fl(C + fl(S − C))`. Every chained or
`Then()` transform re-rounds once more through the same expression with the sequence's `currentTime`. This equals `S`
exactly when `S − C` is exact, which holds by Sterbenz when `C/2 ≤ S ≤ 2C` (positive, same sign). Near time 0
(small or negative `S`, `C`) it can be off by an ulp. The model should compute the expression literally.

### 1.3 Value of one transform at time `t` (`TransformCustom.cs:174-179`, `Interpolation.cs:329-362`)
```
valueAt(t) = t <  StartTime ? StartValue
           : t >= EndTime   ? EndValue
           : Interpolation.ValueAt(t, StartValue, EndValue, StartTime, EndTime, easing)
```
- `float` members (`Rotation`, `Alpha`): `(float) ValueAt_double(t, (double)v1, (double)v2, s, e)`, where
  ```
  if v1 == v2 return v1; cur = t − s; dur = e − s; if cur == 0 return v1; if dur == 0 return v2;
  k = ease(cur / dur) (double); return v1 + k * (v2 − v1)        // all double
  ```
- `Vector2` members (`Scale`, `Position`):
  ```
  cur = (float)(t − s); dur = (float)(e − s); if dur == 0 || cur == 0 return v1;
  k = (float) ease( (double)(cur / dur) )        // float division, then widened
  return v1 + k * (v2 − v1)                        // componentwise float: (v2−v1), k*that, v1+that
  ```
- `ScaleTo(float x)` is `ScaleTo(new Vector2(x))` (`TransformableExtensions.cs:594-597`). Scale is always `Vector2`.
- `MoveToOffset(offset)` is a `PositionOffsetTransform` (`:695-698`, `:800-823`): its `ReadIntoStartValue` sets
  `StartValue = Position; EndValue = Position + offset` (float add) **when it is first applied**.
- Easing (`F/Graphics/Transforms/DefaultEasingFunction.cs:39-184`), double:
  `None: x`; `OutSine: Math.Sin(x * Math.PI * .5)` (evaluated as `(x*π)*0.5`); `InOutSine: .5 − .5 * Math.Cos(Math.PI * x)`;
  `Out/OutQuad: x*(2−x)`; `InBack: x*x*((1.70158+1)*x − 1.70158)` (AD only, visual).

### 1.4 When transforms are evaluated
- `Drawable.UpdateSubTree` → `UpdateTransforms()` → `updateTransforms(Time.Current)` at the start of each DHO's
  subtree update (`F/Graphics/Drawable.cs:469-498`, `Transformable.cs:91-98`). For DHOs that is phase 5 of the step
  (lazer-map §3.1). `rewinding = lastUpdateTransformsTime > time`. That is false in forward play, except as below.
- **Immediate application on add** (`Transformable.cs:381-416`): if `t.StartTime < Time.Current || t.EndTime <=
  Time.Current`, then `updateTransforms(Time.Current, forceRewind = (!RemoveCompletedTransforms && t.StartTime <=
  Time.Current))`. For DHOs that is `rewinding = true`. State updates normally run at `C ≥ S0` (`S0 = Start − preempt`),
  so the first transform of each mod sequence takes effect **in the same step**, during whichever phase triggered the
  state update (phase 2 for a judgement by a press, phase 5 for auto-misses and lifetime/`LoadComplete`). A later
  press in the same step's input phase sees the new value.
- Tracker algorithm (`TargetGroupingTransformTracker.UpdateTransforms`, `:63-200`). The model must implement it
  verbatim. Fields per transform: `Applied`, `AppliedToEnd`, `HasStartValue`.
  ```
  if rewinding (and !RemoveCompleted):
     reset lastApplied cache; clear appliedToEndReverts
     for i = n-1 downto 0 (applied, rewindable only):
        if time >= t.StartTime: if member not yet in reverts: t.AppliedToEnd = false; add member
        else: t.Apply(time); t.Applied = false; t.AppliedToEnd = false        // writes StartValue
  for i = lastAppliedIndex .. n-1:
     if time < t.StartTime: break
     if !t.Applied:  for each earlier u (same member, j ≥ lastAppliedIndex(member)):
                        if !u.AppliedToEnd: u.Apply(t.StartTime)
                        (DHO: u.AppliedToEnd = true; nothing is removed)
     if !t.HasStartValue: t.ReadIntoStartValue() (reads the CURRENT member value); HasStartValue = true
     if !t.AppliedToEnd: t.Apply(time); t.AppliedToEnd = time >= t.EndTime
     (Apply sets Applied = true)
  ```
  Consequence: the start value of a transform is the member's value at the moment it first applies. After an earlier
  same-member transform has been re-applied at the new transform's `StartTime`, that is the earlier one's value at that
  `StartTime`.

### 1.5 State updates (`G/Rulesets/Objects/Drawables/DrawableHitObject.cs`)
`UpdateState(newState, force)` (:467-499), with `C` = clock time now:
1. `clearExistingStateTransforms()` (:501-507): `ApplyTransformsAt(double.MinValue, true)`, a rewind to −∞. Every
   applied transform writes `Apply(−∞) = StartValue`, from last to first, so each member ends at the **StartValue of
   its earliest applied transform** (the value from before any mod transform). Then `ClearTransformsAfter(MinValue)`
   removes all transforms. Nested DHOs are untouched (their overrides are no-ops, :546-554).
2. `BeginAbsoluteSequence(Start − InitialLifetimeOffset)` → `UpdateInitialTransforms()` (`InitialLifetimeOffset =
   TimePreempt` for osu! DHOs, `O/Objects/Drawables/DrawableOsuHitObject.cs:124`): `FadeInFromZero()` (alpha 1),
   circle-piece fades, and so on.
3. `UpdateStartTimeStateTransforms()` at `StartTime`, then `UpdateHitStateTransforms(state)` at `HitStateUpdateTime =
   Result.TimeAbsolute ?? EndTime`.
4. `state.Value = newState`; `LifetimeEnd` logic; then **`ApplyCustomUpdateState?.Invoke(this, newState)`**. All mod
   transforms are created here.

`UpdateState` call sites: `updateStateFromResult()` from `OnApply` when the DHO `IsLoaded` (:316-319), otherwise from
`LoadComplete` (:225-240, the DHO's first `UpdateSubTree`). Also from `ApplyResult` (→ Hit/Miss) and from revert
(rewind only). **Every judgement re-runs every mod's state handler for that DHO**, with the new `C`.

### 1.6 Who receives `ApplyCustomUpdateState`, and in what order
- Mods are attached once per pooled DHO instance, in **mod-list order**, the first time the instance is used
  (`G/Rulesets/UI/Playfield.cs:395-428`: `!dho.IsInitialized` → `ApplyToDrawableHitObject` for each
  `IApplicableToDrawableHitObject`). In osu! **every** DHO, nested ones included, is pooled
  (`O/UI/OsuPlayfield.cs:141-164`). `ModWithVisibilityAdjustment.ApplyToDrawableHitObject`
  (`G/Rulesets/Mods/ModWithVisibilityAdjustment.cs:76-86`) subscribes `(o, state) => (IncreaseFirstObjectVisibility &&
  o.HitObject ∈ FirstObject-subtree) ? ApplyIncreasedVisibilityState(o, state) : ApplyNormalVisibilityState(o, state)`.
- The parent forwards nested events. In the parent's `OnApply`, after `pool.Get(...)` (which already calls
  `nested.Apply(entry)`), it does `nested.ApplyCustomUpdateState += onApplyCustomUpdateState` (:281), which re-invokes
  the **parent's** `ApplyCustomUpdateState(nestedDrawable, state)`. The parent's list holds the same mods' handlers. So
  for a nested DHO `n` each state update runs:
  `[mod handlers on n (o=n)] … then via forwarder [mod handlers on parent (o=n)]`, which is **two passes** of every
  mod over `n`. Then `applyDimToDrawableHitObject` (colour only, :88-94).
- Exception: a **reused** pooled nested DHO (one that was loaded before) runs its initial `UpdateState` inside
  `Apply`, *before* the forwarder is attached, so the initial state gets one pass only. A **fresh** one (never updated:
  the pool's prewarmed instances and newly constructed ones, `F/Graphics/Pooling/DrawablePool.cs:58-65,112-140`) runs
  it from `LoadComplete`, after the forwarder exists, so it gets two passes. The pool is a LIFO stack (returned
  instances are popped before prewarmed ones). Judgement-time state updates always get two passes.
- Two passes are harmless for transforms with absolute targets (Scale/Rotation tweens, fades). They are idempotent:
  the second sequence supersedes the first at equal start times, and both read the same start values. They matter only
  for mods that **read the current `Position`** as their origin: **Wiggle on `DrawableSliderHead`** (§6.4).
  (Transform excludes heads.)

### 1.7 Presence and input
- `Drawable.IsPresent = AlwaysPresent || (Alpha > 0.0001f && DrawScale.X != 0 && DrawScale.Y != 0)`
  (`F/Graphics/Drawable.cs:1336-1342`). DHO override: `base.IsPresent || (State == Idle && Clock.CurrentTime >=
  LifetimeStart)` (`DrawableHitObject.cs:144`). **Idle DHOs are always present.** Judged (Hit/Miss) DHOs need alpha
  > 1e-4 and nonzero scale.
- **Input ignores presence for DHOs.** The framework rule is `PropagatePositionalInputSubTree => IsPresent &&
  RequestsPositionalInputSubTree && !IsMaskedAway` and `PropagateNonPositionalInputSubTree => IsPresent && …`
  (`F/Graphics/Drawable.cs:2445,2450`), but `DrawableHitObject` overrides both with `=> HandleUserInput`
  (`G/Rulesets/Objects/Drawables/DrawableHitObject.cs:76,78`; `HandleUserInput` is true unless SpunOut clears it on
  spinners). The HitReceptor and its scale container keep alpha 1. So a faded (alpha 0) DHO, judged or not, stays in
  the positional and key-binding queues while alive: a judged Classic slider head keeps being hovered and consuming
  presses until its lifetime ends, with or without HD. (Earlier versions of this doc claimed the opposite; confirmed with
  the oracle's `ORACLE_DHO_STATES` dump: an alpha-0 judged head was still hovered, docs/model-sim.md M7.)
- Presence does matter for **updates**: `Drawable.UpdateSubTree` returns after `UpdateTransforms()` when `!IsPresent`
  (`F/Graphics/Drawable.cs:469-498`; `CompositeDrawable.cs:907-950` skips children and `UpdateAfterChildren`). A judged,
  faded slider therefore stops updating its nested objects (e.g. an unjudged StrictTracking head).
- `IsMaskedAway` (`F/Graphics/Drawable.cs:522-543`) is recomputed only in `GameHost` frames (`F/Platform/GameHost.cs:484`),
  not per FSC sub-step. It is `!AlmostIntersects(maskingBounds = screen AABB, ScreenSpaceDrawQuad.AABBFloat)`. It can
  only matter when an object is entirely off-screen *and* the cursor is off-screen too, for example with Transform's
  large appear offsets (`appearDistance` up to (1800−400)/2 = 700 px at AR0). **Open item:** the oracle should record
  whether any receptor was masked away while being hovered. Until that is checked, assume it never happens.

---------------------------------------------------------------------------------------------------

## 2. Screen-space hit-test pipeline (float32, bit-exact)

### 2.1 `DrawInfo` (`F/Graphics/DrawInfo.cs:31-73`, `F/Extensions/MatrixExtensions/MatrixExtensions.cs`)
`Matrix3` is row-major: `Row0 = (M11,M12,M13)`, `Row1 = (M21,M22,M23)`, `Row2 = (M31,M32,M33)`. A point transforms as
`x' = M11*x + M21*y + M31`, `y' = M12*x + M22*y + M32` (`F/Graphics/Vector2Extensions.cs:27-31`; evaluated
`(a*x + b*y) + c`). `ToScreenSpace(p) = p·Matrix`, `ToLocalSpace(p) = p·MatrixInverse`, and the inverse is **never
recomputed** but accumulated alongside (`DrawInfo.cs:68-72` comment).

`ApplyTransform(T, S, r, shear, O)`, in this order. Each step is skipped when its guard fails (`T != 0`, `r != 0`,
`shear != 0`, `S != (1,1)`, `O != 0`; float compares, so `-0 == 0`):
```
1. TranslateFromLeft(M, T):  Row2 = Row2 + (Row0*T.x + Row1*T.y)             // per component: M3k + ((M1k*Tx) + (M2k*Ty))
   TranslateFromRight(I, −T): for each row R: R.c1 += R.c3*(−Tx); R.c2 += R.c3*(−Ty)   // M11+=M13*(−Tx) … M32+=M33*(−Ty)
2. rad = float.DegreesToRadians(r) = (r * float.Pi) / 180f          [verified op 220; whole ApplyTransform: op 143]
   RotateFromLeft(M, rad):  c = MathF.Cos(rad), s = MathF.Sin(rad)
        Row0' = Row0*c + Row1*s ; Row1' = Row1*c − Row0*s           // componentwise, products rounded, then sum
   RotateFromRight(I, −rad): c = cosf(−rad), s = sinf(−rad)
        for each row: m1 = M1*c − M2*s ; M2 = M2*c + M1*s ; M1 = m1   // (M11,M12), (M21,M22), (M31,M32)
3. shear: never nonzero in the gameplay tree (skip).
4. if |S.x| < 1e-3f: S.x = Sign(S.x == 0 ? 1 : S.x) * 1e-3f; same for y          (Precision.FLOAT_EPSILON = 1e-3f)
   ScaleFromLeft(M, S): Row0 *= S.x ; Row1 *= S.y
   ScaleFromRight(I, (1f/S.x, 1f/S.y)): M11*=ix, M21*=ix, M31*=ix ; M12*=iy, M22*=iy, M32*=iy
5. TranslateFromLeft(M, −O); TranslateFromRight(I, +O)
```
The scale clamp matters. Grow `StartScale = 0`, SpinIn's circle scale `(2, 0)`, SpinIn's slider scale 0, and every
interpolated scale component below 0.001 become ±0.001 in the matrices, while `Scale` itself (which `IsPresent` reads)
stays 0.

### 2.2 `computeDrawInfo` (`F/Graphics/Drawable.cs:1603-1616`)
`di = Parent.DrawInfo; pos = DrawPosition + AnchorPosition (+ Parent.ChildOffset, 0 here); di.ApplyTransform(pos,
DrawScale (= Scale, :1059), Rotation, Shear, OriginPosition)`. `AnchorPosition = RelativeAnchorPosition *
Parent.ChildSize` (:1261). `OriginPosition = Origin==Custom ? custom : computeAnchorPosition(LayoutSize, Origin)` minus
the margin (:1159-1172). The result is cached and invalidated by any change to Position, Scale, Rotation, Size or an
ancestor. The model can recompute it whenever it is needed, because the inputs fully determine it.

### 2.3 Chains (extend `model/OsuModel/Sim/Geometry.lean`)
Let `H` = HitObjectContainer `DrawInfo` (Env; `difftest/env-1024x768.json`, 1.6× scale, `M31 = 0x42cccccc`,
`M32 = 0x42b33334`; first step `hocFirst`). The mod-generalised links:
- **Circle receptor:** `DHO = H ⊕ (pos = dho.Position, anchor 0, scale = dho.Scale (mod; Vector2), rot = dho.Rotation
  (mod; float deg), origin = (64,64))` → `scaleContainer` (`anchor (64,64)`, scale `(HitObject.Scale, same)`, origin
  `(64,64)`) → `HitReceptor` (`anchor (64,64)`, origin `(64,64)`) (`O/Objects/Drawables/DrawableHitCircle.cs:62-104`).
  `dho.Position` is `StackedPosition` unless a mod moved it. The ShakeContainer is a sibling of the receptor, so shakes
  do not move it. `CirclePiece` rotation (BR) is a sibling too, so it is visual only.
- **Slider:** `DS = H ⊕ (pos = ds.Position, anchor 0, scale = ds.Scale, rot = ds.Rotation, origin = OriginPosition
  (PathOffset))`. Head: `headContainer` (identity) → `DrawableSliderHead` (Position = **its own `Position`**, normally
  (0,0) (`DrawableSliderHead.cs:39-42`), but Wiggle moves it; anchor = `RelativeAnchorPosition·ChildSize`; scale =
  head `Scale` (SpinIn); rot = head `Rotation` (SpinIn); origin (64,64)) → scaleContainer → HitReceptor. Follow area
  (`SliderInputManager.cs:184-196`): `slider.ToLocalSpace(screen) − OriginPosition` uses `DS.MatrixInverse`. **The DHO
  scale and rotation therefore scale and rotate the follow circle** (Depth during the body; Grow/Deflate/SpinIn only
  before `StartTime`).
- **Spinner:** `DSP = H ⊕ (pos = dsp.Position (Transform/Wiggle move it), anchor 0, scale 1, origin = centre of
  hocSize)` → AspectContainer → tracker (`O/Objects/Drawables/DrawableSpinner.cs:90-125`). The tracker angle uses
  `Parent.ToLocalSpace(mouse)` (`O/Skinning/Default/SpinnerRotationTracker.cs:59,69`). Moving the spinner before
  `StartTime` changes `lastAngle` and hence the first tracked delta.
- **Cursor** (Magnetised/Repel/Depth inputs): `CursorContainer` is RelativeSizeAxes.Both at (0,0) in the playfield
  (`F/Graphics/Cursor/CursorContainer.cs:26-29`), so its DrawInfo is the playfield's, which is the same matrix as `H`.
  It is `IRequireHighFrequencyMousePosition`, so it gets `OnMouseMove` **every** input phase:
  `ActiveCursor.Position = e.MousePosition = H⁻¹·screenMouse` (:71-75). `ActiveCursor.DrawPosition` = that Position
  (no relative axes).

### 2.4 Replay position path
`OsuFramedReplayInputHandler.CollectReplayInputs` (`O/Replays/OsuFramedReplayInputHandler.cs:22-27`): `screen =
H_prev·lerp(frames)` with `GamefieldToScreenSpace = HitObjectContainer.ToScreenSpace` (`G/Rulesets/UI/Playfield.cs:55`),
evaluated in the input phase, so it uses the `H` left by the previous step. Every receptor test then applies
`receptor.MatrixInverse` composed from the same `H_prev`. **Any playfield-level transform (BR) cancels in exact
arithmetic.** It remains as float rounding in the composed matrices.

### 2.5 Barrel Roll and the ancestor chain
BR sets `OsuPlayfieldAdjustmentContainer.Rotation` (and once, `Scale`) (`G/Rulesets/Mods/ModBarrelRoll.cs:57-73`).
That container is `Anchor/Origin Centre`, `Size = 0.8` relative (`O/UI/OsuPlayfieldAdjustmentContainer.cs:27-44`) → 4:3
Fit container → inner ScalingContainer (`Scale = ChildSize.X/512`, `Position.y = 8*Scale.X` because DrawableOsuRuleset
sets `AlignWithStoryboard`, `Size = 1/Scale`, :53-72) → OsuPlayfield → HitObjectContainer. With rotation, `H` is a
float product through every ancestor, so the model needs each ancestor's `(pos+anchor, scale, rotation, origin)`.
**Do not derive these by hand.** The naive chain (identity parent, 1024×768, `0.8f` sizes) gives `M32 = 0x42999998`
for the first-step matrix, but the oracle dumped `0x4299999c`. The real chain has more (or different) float steps.
Action: extend `oracle --dump-env` to print, for every ancestor of the HitObjectContainer, `DrawPosition`,
`AnchorPosition`, `ChildOffset`, `Scale`, `Rotation`, `Shear`, `OriginPosition`, `DrawSize` (bits) for both the first
step and steady state. The model then recomposes and checks it reproduces `H` bit-exactly with `r = 0`. With BR, the
BR container's `r` and `s` replace the dumped ones.
- `s = minSide / maxSide` of `Playfield.DrawSize` at `ApplyToDrawableRuleset` time, i.e. during `DrawableRuleset.load`
  (`G/Rulesets/UI/DrawableRuleset.cs:174-204, 368-377`), before any layout update. All plausible sizes, (512, 384),
  (819.2f, 614.4f) and relative-only, give `0.75f` (`0x3f400000`), but this must be dumped.
- `r = (float)((ccw ? −1 : 1) * 360) * (float)(Time.Current / 60000 * SpinSpeed)` (double inside, one float cast;
  then int×int → float × float) (`ModBarrelRoll.cs:60`). It is set in phase 3 of step *k* and used by the input phase
  of step *k+1*. In step 1 it is 0. `Direction` default `Clockwise` (+1) (`F/Graphics/Drawable.cs:2798-2805`).
  `SpinSpeed` double 0.5, [0.02, 12], precision 0.01.
- `OsuModBarrelRoll` also rotates `CirclePiece` and the cursor sprite (`O/Mods/OsuModBarrelRoll.cs:19-39`). Both are visual.

### 2.6 Hover timing (who sees moved objects when)
`InputManager.Update` (`F/Input/InputManager.cs:459-505`): pending inputs are applied in order.
`MousePositionAbsoluteInput.Apply` fires a change **only if the screen position differs**
(`F/Input/StateChanges/MousePositionAbsoluteInput.cs:24-36`). A change runs `updateHoverEvents` immediately, before the
button state. Otherwise hover is recomputed only at the end of the input phase, after presses. So with a **stationary
cursor, presses use hover from the previous step's input phase**, even though objects moved (TR/WG/MG/RP/DP) or grew
(GR/DF/SI/TP). Already modelled in `Sim/Step.lean:718-734`. **BR makes the screen position change every step**
(rotation changes `H`), so hover is always fresh before presses. This is a real behavioural difference from non-BR
play, not just rounding.

---------------------------------------------------------------------------------------------------

## 3. Settings (ranges, defaults, precision)

Deserialisation and `BindableNumber` rounding: `docs/mods/difficulty-rate-fail.md` §2 (decimal, round-half-even).

| Mod.setting | type | default | min | max | precision | notes |
|---|---|---|---|---|---|---|
| GR `StartScale` | float | 0.5 | 0 | 0.99 | 0.01f | `O/Mods/OsuModGrow.cs:21-26`; EndScale 1 |
| DF `StartScale` | float | 2 | 1 | 25 | 0.1f | `OsuModDeflate.cs:21-26` |
| WG `Strength` | **double** | 1 | 0.1f→double | 2 | **0.1f→double** | `OsuModWiggle.cs:31-36`, see below |
| RD `Seed` | int? | null → `RNG.Next()` | | | | `G/Rulesets/Mods/ModRandom.cs:19-20` |
| RD `AngleSharpness` | float | 7 | 1 | 10 | 0.1f | `OsuModRandom.cs:31-36` |
| TP `Seed` | int? | null → `RNG.Next()` | | | | `OsuModTargetPractice.cs:54-55`; `Metronome` bool true (audio) |
| MR `Reflection` | enum | Horizontal | | | | {Horizontal, Vertical, Both} `OsuModMirror.cs:20-49` |
| DP `MaxDepth` | float | 100 | 50 | 200 | 10 | `OsuModDepth.cs:34-39`; `ShowApproachCircles` bool true (visual) |
| MG `AttractionStrength` | float | 0.5 | 0.05 | 1 | 0.05f | `OsuModMagnetised.cs:33-38` |
| RP `RepulsionStrength` | float | 0.5 | 0.05 | 1 | 0.05f | `OsuModRepel.cs:34-39` |
| BR `SpinSpeed` | double | 0.5 | 0.02 | 12 | 0.01 | `G/Rulesets/Mods/ModBarrelRoll.cs:29-34` |
| BR `Direction` | enum | Clockwise | | | | |
| AD `Scale`, `Style` | float/enum | 4 / … | | | | visual |

- **Wiggle Strength quirk.** `Precision = 0.1f` is the double 0.100000001490116119…, and `(decimal)` of that is
  `0.100000001490116m` (15 significant digits). The initialiser re-applies the value (`MinValue`, `MaxValue`,
  `Precision` in written order), so the default becomes `round(1 / 0.100000001490116) * 0.100000001490116 =
  1.00000001490116m` → double `1.00000001490116`, **not 1.0**. Any JSON value `v` becomes
  `(double)(round_half_even((decimal)v / 0.100000001490116m) * 0.100000001490116m)`. The decimal division is not
  exact here; use the full decimal division algorithm **[verified: decimal `/` op 117; real `APIMod.ToMod`
  (`nettest lazer`): default `1.00000001490116` (0x3FF0000003FFFFFB), JSON 1.5 → `1.50000002235174`]**. The float settings (precision `0.01f`, `0.1f`,
  `0.05f` → `(decimal)` 7 digits = 0.01m, 0.1m, 0.05m) snap to the double nearest `k·p` and then go to float
  (double rounding, see companion §2.3).
- Seeds: lazer replays carry the seed in the mod settings JSON. If it is absent, the run is not reproducible
  (`RNG.Next()`), so reject the replay.

---------------------------------------------------------------------------------------------------

## 4. `System.Random(int seed)` (legacy-seeded `CompatSeedImpl`) [verified op 110: 10k seeds incl. 0, ±1, int.MinValue/MaxValue, 735k calls]

`new Random(seed)` with `GetType() == typeof(Random)` → `CompatSeedImpl` (.NET 10 name; formerly `Net5CompatSeedImpl`) →
`CompatPrng` (Knuth subtractive, the .NET Framework algorithm). `NextDouble()` = `Sample()`. Lean: `Net/Random.lean`
(`NetRandom.create/nextDouble/next/nextMax/nextRange/nextSingle`). `Next(max) = ConvertToIntegerNative<int>(Sample()
* max)`, `Next(min, max)` uses `GetSampleForLargeRange` when `max - min > int.MaxValue`, `NextSingle` retries while
`(float)Sample() == 1f`; all verified. Unseeded `new Random()`/`RNG` is Xoshiro from OS entropy (not modelled).
```
MBIG = int.MaxValue (2147483647), MSEED = 161803398
ctor(seed):
  int[] a = new int[56]
  sub = (seed == int.MinValue) ? int.MaxValue : Math.Abs(seed)
  mj = MSEED − sub;  a[55] = mj;  mk = 1;  ii = 0
  for i = 1..54:  ii += 21; if ii >= 55: ii −= 55          // ii = 21*i mod 55
                  a[ii] = mk;  mk = mj − mk;  if mk < 0: mk += MBIG;  mj = a[ii]
  for k = 1..4: for i = 1..55:  n = i + 30; if n >= 55: n −= 55
                                a[i] −= a[1 + n];  if a[i] < 0: a[i] += MBIG
  inext = 0; inextp = 21
InternalSample():
  inext  = inext+1  >= 56 ? 1 : inext+1
  inextp = inextp+1 >= 56 ? 1 : inextp+1
  r = a[inext] − a[inextp];  if r == MBIG: r−−;  if r < 0: r += MBIG
  a[inext] = r;  return r
NextDouble() = Sample() = InternalSample() * (1.0 / int.MaxValue)      // double multiply by the rounded constant
```
All int arithmetic is 32-bit wrapping (unchecked); none of the subtractions above can actually overflow. The
`(int)` casts of seeds are .NET saturating `double→int` (`net-float.md`). Only `NextDouble` is used by these mods.

---------------------------------------------------------------------------------------------------

## 5. Beatmap-level positional mods

Application points (lazer-map §1.2): **step 7** `IApplicableToHitObject` (HR, MR: per object, mod-list order, before
stacking); **step 9** `IApplicableToBeatmap` (mod-list order, after stacking): HD (`TimeFadeIn`), FR, RD, TP, and
every `ModWithVisibilityAdjustment` records `FirstObject`.

### 5.1 Mirror / HR flip (`O/Mods/OsuModMirror.cs:23-42`, `O/Utils/OsuHitObjectGenerationUtils.cs:112-170`)
- Horizontal: `Position = (512f − X, Y)`. Vertical (and HR): `Position = (X, 384f − Y)` (float subtraction). Both:
  horizontal, then vertical.
- Sliders: `modifySlider` copies the control points `(Position, Type)`, negates x (or y) of each relative control
  point, and assigns `slider.Path = new SliderPath(points, ExpectedDistance.Value)`. The `Slider.Path` setter
  (`O/Objects/Slider.cs:47-57`) replaces the control points and sets the same expected distance. That triggers path
  recalculation and `updateNestedPositions`. The nested times are unchanged. The `Position` setter (:61-69) also
  updates nested objects.
- Stacking (step 8) runs afterwards on the reflected positions.

### 5.2 Random (`O/Mods/OsuModRandom.cs:42-162`, `O/Utils/OsuHitObjectGenerationUtils.Reposition.cs`)
Runs at step 9, **after stacking**: `StackHeight` keeps the value from the original layout, and `StackedPosition = new
Position + StackOffset(old StackHeight)`. Constants: `BASE_SIZE = (512,384)`, centre `(256,192)`.
`playfield_diagonal = BASE_SIZE.LengthFast = 1f / InverseSqrtFast(409600f)` with OpenTK's
`InverseSqrtFast(x) { xh = 0.5f*x; i = 0x5f375a86 − (bits(x) >> 1); y = asfloat(i); return y*(1.5f − (xh*y)*y); }`
≈ **640.99506f (0x44203faf)**, not 640 **[verified: decompiled `MathHelper.InverseSqrtFast` is exactly
`x *= 1.5f - (0.5f*x)*x*x` with `1597463174 - (bits >> 1)` (arithmetic shift); op 131/122/132; `nettest probe` prints
`new Vector2(512,384).LengthFast = 640.99506 (44203FAF)`; kernel fact in `Net/LibChecks.lean`]**. `Vector2.Length = (float)Math.Sqrt(x*x + y*y)` (float products and sum).

Algorithm (`random` = `new Random((int)Seed)`; every `NextDouble` is listed in call order):
```
infos = GeneratePositionInfos(objects)            // Reposition.cs:30-61, for ALL objects incl. spinners
   prevPos = (256,192); prevAngle = 0f
   for h: rel = h.Position − prevPos; abs = atan2f(rel.Y, rel.X); RelativeAngle = abs − prevAngle; Dist = rel.Length
          if Slider: rot = getSliderRotation(h) = atan2f(PositionAt(1).Y, .X); info.Rotation = rot − abs; abs = rot
          prevPos = h.EndPosition; prevAngle = abs
sectionOffset = 0f; flow = false
for i:
  A. if shouldStartNewSection(i):                        // i==0 → true, no RNG
         sectionOffset = getRandomOffset(0.0008f); flow = !flow
     shouldStartNewSection(i>0), short-circuit, in this order:
         startedCombo = infos[max(0,i−2)].IndexInCurrentCombo > 1 && infos[i−1].NewCombo
         (startedCombo && NextDouble() < 0.6f(as double)) || onBeat(prev, downbeat) || (onBeat(prev) && NextDouble() < 0.4f)
  B. if Slider && NextDouble() < 0.5: FlipSliderInPlaceHorizontally (negate control-point x; §5.1 path rebuild)
  C. if i == 0: Dist  = (float)(NextDouble() * 384f / 2)              // (double*double)/2
                Angle = (float)(NextDouble() * 2 * Math.PI − Math.PI)
     else:      oneTime = getRandomOffset(0.002f)
                flowChange = 0f; if (startedCombo && NextDouble() < 0.6f): flowChange = getRandomOffset(0.002f); flow = !flow
                total = (sectionOffset + oneTime) * Dist + flowChange * (diag − Dist)          // float
                Angle = getRelativeTargetAngle(Dist, total, flow)
getRandomOffset(sd): mult = (1.5f*10 − AS) / (1.5f*10 − 7)  (float); return RandomGaussian(random, 0, sd*mult)
RandomGaussian: x1 = 1 − NextDouble(); x2 = 1 − NextDouble();
                n = Math.Sqrt(−2*Math.Log(x1)) * Math.Sin(2*Math.PI*x2); return 0f + sd*(float)n     (GenerationUtils.cs:211-220)
getRelativeTargetAngle(d, off, flow):  s = AS/10f; w = 1 − s; cx = s*100 − 70; cy = w*0.25f − 0.075f
                d += cx; a = (float)(2.16 / (1 + 200*Math.Exp(0.036*(double)((d − 310) + cx))) + 0.5)
                a = a + (off + cy)                               // C# `angle += offset + customOffsetY`, float
                rel = (float)Math.PI − a; return flow ? −rel : rel
onBeat(h, down): tp = TimingPointAt(h.StartTime); bl = tp.BeatLength * (down ? tp.TimeSignature.Numerator : 1);
                 Math.Abs((h.StartTime − tp.Time) + 1) % bl < 2          (double fmod; GenerationUtils.cs:193-206)
objects = RepositionHitObjects(infos)              // Reposition.cs:68-120
```
`RepositionHitObjects`: working objects capture `RotationOriginal` (slider rotation, else 0), `PositionModified =
Position`, `EndPositionModified = EndPosition` at construction. For each `i`: a spinner just becomes `previous` (its
end position stays `(256,192)`, or wherever it is). Otherwise:
```
computeModifiedPosition(cur, prev, i>1 ? w[i−2] : null):                       (:128-171)
   prevAbs = 0f; if prev: prevAbs = prev is Slider ? getSliderRotation(prev)
                                   : atan2f of (prev.Position − (beforePrev?.EndPosition ?? centre))   // ORIGINAL objects' current fields
   abs = prevAbs + info.RelativeAngle
   rel = (Dist*cosf(abs), Dist*sinf(abs))
   last = prev?.EndPositionModified ?? centre
   rel = RotateAwayFromEdge(last, rel, 0.5f); cur.PositionModified = last + rel
   if Slider: abs = atan2f(rel.Y, rel.X); com = centreOfMass(slider)
              comMod = rotateVector(com, info.Rotation + abs − getSliderRotation(slider))     // float sum left-to-right
              comMod = RotateAwayFromEdge(cur.PositionModified, comMod, 0.5f)
              rr = atan2f(comMod) − atan2f(com); if !Precision.AlmostEquals(rr, 0) (float eps 1e-3): RotateSlider(slider, rr)
then clamp: HitCircle → pos = clamp(PositionModified, r, 512−r / r, 384−r) (Math.Clamp float; r=(float)Radius);
                        Position = EndPositionModified = PositionModified = pos; shift = pos − old
            Slider    → clampSliderToPlayfield (:194-236; rotation fallback to RotationOriginal or +π when the bounds
                        are negative; Math.Clamp; slider.Position = PositionModified; EndPositionModified = slider.EndPosition)
if shift != 0: shift the preceding ≤10 consecutive HitCircles (stop at the first non-circle), j = i−1 downward:
     pos_j += shift * ((count − idx)/(float)(count + 1)); clamp with padding        (:244-255)
```
`prevAbs` reads the hit objects' *current* fields: `prev.HitObject.Position`, `beforePrev.HitObject.EndPosition`, and
the current (possibly flipped or rotated) path for `getSliderRotation`. Earlier iterations have already overwritten
these with modified values: circles via the clamp (`HitObject.Position = PositionModified`), sliders via
`slider.Position = …` and `RotateSlider`, and circles again by later `applyDecreasingShift`. `PositionModified` and
`EndPositionModified` are separate working fields. The model must mutate in exactly this order. Helpers:
`RotateAwayFromEdge` (`GenerationUtils.cs:41-80`; border 0.375×size; `Math.Min(1, ratio*rot)`),
`RotateVectorTowardsVector` (:89-106; angle wrap with `2*MathF.PI` loops), `rotateVector` (:178-186:
`atan2f + rot`, length, `cos/sin`), `calculateCentreOfMass` (:324-345: `Distance <= 50` → `PositionAt(1)/2`, else
the mean of `PositionAt(i/d)` for `i = 0, 50, …` while `< d`, float sums, `sum / count`), `getAngleDifference`
(:364-368, `MathF.Abs(a−b) % (2π)`). Slider modifications go through §5.1's path rebuild (nested positions follow).

### 5.3 Target Practice (`O/Mods/OsuModTargetPractice.cs`)
- `ApplyToDifficulty`: `AR *= 0.5f` (:118-122, step 4). Sudden-death fail condition (:106-112). It is a
  `ModWithVisibilityAdjustment`.
- `ApplyToBeatmap` (:160-191), step 9: `Seed ??= RNG.Next(); rng = new Random(Seed)`. If there are no objects, return
  (and FirstObject stays unset!). Otherwise `controlPointInfo = beatmap.ControlPointInfo`; `orig` = objects stably
  ordered by StartTime.
  1. **Beats** (:193-219): `start = HitObjects.First().StartTime`, `end = max over objects of GetEndTime()`. For each
     `TimingPoints` entry (list order) with `!DefinitelyBigger(tp.Time, end, 1)`: `t_i = tp.Time + i*BeatLength`
     (double, `i` int), emit `Math.Floor(t_i)` while `!DefinitelyBigger(t_i, end, 1) && TimingPointAt(t_i) is tp`
     (reference equality). Keep beats with `AlmostBigger(beat, start, 1)` that are not in a break (:352-363: `beat ≥~
     break.Start` and the first original object with `StartTime ≥~ break.End` is null or `> beat` definitively).
     Then for `i = n−2 … 0`: remove `beats[i]` unless `DefinitelyBigger(beats[i+1] − beats[i],
     TimingPointAt(beats[i]).BeatLength / 2, 1)`. (`Precision.AlmostBigger(a,b,e) = a > b − e`; `DefinitelyBigger(a,b,e)
     = a − e > b`; `AlmostEquals = |a−b| <= e`, `F/Utils/Precision.cs`.)
  2. Each beat → `new HitCircle(); ApplyDefaults(cpi, Difficulty); StartTime = beat`. **`ApplyDefaults` runs while
     `StartTime == 0`.** So `Kiai = EffectPointAt(0 + 1).KiaiMode` for every TP circle (`G/Rulesets/Objects/HitObject.cs:37,
     ApplyDefaultsToSelf`). `TimePreempt`, `TimeFadeIn`, `Scale`, `HitWindows` come from the (AR-halved) difficulty.
     `StackHeight = 0` (stacking already ran), `Position = (0,0)` until step 4.
  3. Samples (:221-231; audio only).
  4. Combo (:233-265): `ComboIndex` = that of the last original object with `AlmostBigger(newT, orig.StartTime, 1)`, or
     0. Group by ComboIndex (first-appearance order). In each group: first `NewCombo = true`, last `LastInCombo = true`,
     `ComboIndex = group#`, `IndexInCurrentCombo = j`.
  5. Positions (:267-326), all float:
     ```
     nextSingle(max=1f) = (float)(rng.NextDouble() * max)
     direction = 2π_f * nextSingle(); maxCombo = last.ComboIndex
     for i: last = i==0 ? (256,192) : objs[i−1].Position
            dist = maxCombo == 0 ? (float)Radius : (C − 0f)*(333f − rad)/(maxCombo − 0f) + rad     // mapRange, C=(float)ComboIndex
            if NewCombo: dist *= 1.5f;  if Kiai: dist *= 1.2f;  dist = Math.Min(380f, dist)
            prec = objs[max(0,i−5) .. i−1]; try = 0
            do { if try > 0: direction = 2π_f * nextSingle()
                 rel = (dist*cosf(direction), dist*sinf(direction)); rel = RotateAwayFromEdge(last, rel, 0.75f)
                 direction = atan2f(rel.Y, rel.X); obj.Position = last + rel; clampToPlayfield(obj)   // Y first, then X: [r, 384−r], [r, 512−r]
                 try++; if try % 10 == 0: dist *= 0.9f
            } while ((double)dist >= Radius*2 && any(prec, Distance(p.Position, obj.Position) < Radius*2))   // float dist vs double
            if LastInCombo: direction = 2π_f * nextSingle()
            else direction += dist / 380f * (nextSingle() * 2π_f − MathF.PI)
     ```
     `2π_f = MathF.PI * 2`. `Vector2.Distance = (float)Math.Sqrt(dx*dx + dy*dy)` with `dx = v2.X − v1.X` **[verified
     op 123 (osuTK, double sqrt); note the framework's `Vector2Extensions.Distance` uses `MathF.Sqrt` instead, op 141]**.
  6. `HitObjects = generated`; `base.ApplyToBeatmap` sets `FirstObject` = the first generated circle.
- DHO transform (`ApplyNormalVisibilityState`, :132-154; `ApplyIncreasedVisibilityState` is empty, so the **first
  circle keeps scale 1**): at `S0 = Start − preempt`: `circle.ScaleTo(0.5f)` (duration 0), then a separate sequence
  `circle.ScaleTo(1f, preempt)` (Easing.None, same `S0`). Both are `Scale` transforms. The 0→ one applies first, the
  second reads start (0.5, 0.5) → linear to (1, 1) at `S0 + preempt` (Vector2 math, §1.3). It also matches
  `DrawableSliderHead` by type, but TP maps contain no sliders.
- Mod-list order with Grow/Deflate: same member, same start time. The later handler's transforms win (§1.1, §1.4).

### 5.4 Freeze Frame (`O/Mods/OsuModFreezeFrame.cs:38-87`)
Step 9: `lastNC = 0`; for each top-level object in list order: `if NewCombo: lastNC = StartTime`. Then
`adjust(obj)`: if not Spinner, `TimePreempt += StartTime − lastNC` (the object's **own** StartTime, so nested heads,
tails and repeats get `+= nested.StartTime − lastNC`). Recurse into nested objects: ticks are skipped, only the first
3 repeats are adjusted (`repeatCount > 2 → skip`), everything else is adjusted (head, tail, spinner ticks). Stacking
already ran with the original preempt. Effects: `LifetimeStart = Start − TimePreempt` (earlier alive), and every
transform mod that reads `TimePreempt` at state time (GR/DF/SI/WG amount; TR, DP, HD are incompatible). The approach
circle scale `4*(float)(preempt/originalPreempt)` is visual.

---------------------------------------------------------------------------------------------------

## 6. DHO state-transform mods

All are `ModWithVisibilityAdjustment`. All transforms are created in `ApplyCustomUpdateState` (§1.5-1.6) on every
state update. `h` = the DHO's `OsuHitObject`, `p = h.TimePreempt` (double), `S0 = h.StartTime − p`. "BAS(x)" =
`BeginAbsoluteSequence(x)` (start-time rounding §1.2).

### 6.1 Grow / Deflate (`O/Mods/OsuModObjectScaleTween.cs:29-68`)
For `DrawableHitCircle` and `DrawableSlider` only. Heads, tails and spinners are skipped. Note that
`DrawableSliderHead`/`Tail` cases come first, so heads are excluded despite being `DrawableHitCircle`.
```
BAS(S0): DHO.ScaleTo(StartScale) [dur 0] .Then() .ScaleTo(1f, p, OutSine)
```
Scale `(σ, σ)`, `σ(t) = StartScale + k*(1 − StartScale)`, `k = (float)sin((double)(cur/dur) * π * .5)` (float
`cur`, `dur`, §1.3). It is constant 1 for `t ≥ S0'' + p`. Increased visibility (first object, default config):
**no-op**, scale stays 1 (`:29-31`). Hit radius in gamefield = `64 * HitObject.Scale * σ` (plus rounding). For
sliders, `σ` also scales the follow area and head before `StartTime`.

### 6.2 Spin In (`O/Mods/OsuModSpinIn.cs:38-74`)
Spinners are skipped. `DrawableHitCircle` (**including `DrawableSliderHead`**, which derives from it):
```
BAS(S0): RotateTo(360f) [0] .Then() .RotateTo(0f, p, InOutSine)          // float member, double interpolation
         ScaleTo((2f, 0f)) [0] .Then() .ScaleTo((1,1), p, InOutSine)     // Vector2
         (FadeIn if Idle)
```
`DrawableSlider`: `BAS(S0): ScaleTo(0) [0] .Then() .ScaleTo(1, p, InOutSine)`. For a head the effective head transform
is slider scale ∘ head rotation/scale (non-uniform). The y scale near `S0` falls under the 1e-3 clamp (§2.1).
Increased visibility: no-op (first object, including its nested head, unrotated and unscaled).

### 6.3 Transform (`O/Mods/OsuModTransform.cs:27-65`)
Mod field `float theta = 0` is **shared across all DHOs and mutated per call**. For every drawable except
head/tail/tick/repeat (so circles, sliders **and spinners**), for both increased and normal visibility:
```
appearDistance = (float)(p − h.TimeFadeIn) / 2                       // double diff → float, /2 float
orig = drawable.Position                                             // after the §1.5 rewind = StackedPosition (spinner: Position)
off  = (cosf(theta), sinf(theta)) * appearDistance                   // Vector2 * float
appearTime = h.StartTime − p − 1;  moveDuration = p + 1
BAS(appearTime): MoveToOffset(off) [0] .MoveTo(orig, moveDuration, InOutSine)   // NOT Then: same start time
theta += (float)h.TimeFadeIn / 1000                                  // float
```
Evaluation: the offset transform first applies at `C ≥ appearTime` (immediately, §1.4) with `StartValue = Position,
EndValue = Position + off`. The MoveTo then reads `Position + off` as its start. Position = `(orig+off) + k*(orig −
(orig+off))`, which reaches `orig` at `appearTime' + moveDuration ≈ StartTime`. `theta` advances once per
`ApplyCustomUpdateState` call on a non-nested DHO. That means once per state update (initial Idle at apply time and
again on its judgement), in the **global chronological order of those calls**. The model must keep `theta` as
global mod state, updated in the exact order of state updates (DHO apply order, then judgements in result order).
`TimeFadeIn` depends on HD (`0.4·preempt` for non-sliders) and AR (`400*min(1, p/450)`).

### 6.4 Wiggle (`O/Mods/OsuModWiggle.cs:42-81`)
For every DHO except those whose hit object is `SliderRepeat` or `SliderTailCircle`: circles, sliders, **slider heads
(and ticks)**, spinners (and spinner ticks); increased and normal visibility alike.
```
origin = drawable.Position                       // read at call time (see §1.6 double pass)
rng = new Random((int)h.StartTime)                // fresh each call → same sequence each call
wiggle(): ang  = (float)(rng.NextDouble() * 2 * Math.PI)
          dist = (float)(rng.NextDouble() * Strength * 7)
          MoveTo(((float)(dist*Math.Cos(ang) + origin.X), (float)(dist*Math.Sin(ang) + origin.Y)), 100)   // double math, Easing.None
n1 = ((int)p) / 100          (int division)
for i in 0..n1−1:  BAS(h.StartTime − p + i*100): wiggle()
if h is IHasDuration (slider, spinner): n2 = (int)(Duration / 100)
   for i in 0..n2−1: BAS(h.StartTime + i*100): wiggle()
```
Each segment interpolates linearly from the value at its first application (normally the previous target) to its
target. Successive segments are back to back. The first starts at `origin` (or the current position, see below).
- **Slider head:** its `Position` is normally (0,0), relative to the slider anchor. It uses the same seed as the
  slider (same StartTime), so the head moves by the same offsets *in addition to* the slider's own wiggle (total ≈ 2×).
- **Double pass on heads (§1.6):** pass 1 at time `C` (origin O) applies segment 0 immediately when `C > S0'`. That
  moves Position to `P1 = O + ((float)(C−S0')/100f)·(target0 − O)`. Pass 2 then reads `origin = P1`, and its segments
  replace pass 1's from segment 1 on, with segment 0 restarting from O (§1.4: the old segment 0 is re-applied at the new
  one's start time before the new start value is read). Net: **the head's wiggle centre is shifted by `P1 − O`**. When
  the head is judged (two passes always), the centre is shifted by the head's pass-1 displacement at the judgement
  time, which matters for Classic heads that still consume presses. With `C == S0'` exactly, nothing applies
  immediately, both passes read O, and there is no shift. For a reused pooled head the initial state gets one pass, so
  no shift (pool LIFO state needed). Implement it generically (tracker plus dispatch lists). **Validate with an oracle
  dump of head positions under WG.**

### 6.5 Approach-only effects (visual)
`ApproachCircle` scale and alpha transforms (GR/DF/SI/TP/HD hide it, AD's scale/easing, FR's 4× scale) are inside the
`shakeContainer`, which is a sibling of `HitReceptor`. They never affect a hit test.

---------------------------------------------------------------------------------------------------

## 7. Per-step (`IUpdatableByPlayfield`) mods

They run in `Playfield.Update` (phase 3), in mod-list order (`G/Rulesets/UI/Playfield.cs:263-287`), over
`HitObjectContainer.AliveEntries`. That is the alive set *before* this step's lifetime update (phase 4), so a DHO
that becomes alive at step *k* is first moved at step *k+1*. Its first hittable input phase (step *k+1*) therefore
sees it **unmoved and unscaled** (StackedPosition, scale 1). The values they write are read by hit tests in the next
step's input phase. `cursorPos = playfield.Cursor.ActiveCursor.DrawPosition` = this step's `H⁻¹·screenMouse` (§2.3).
`Clock.ElapsedFrameTime` = FSC current − previous frame time (double).

### 7.1 Magnetised (`O/Mods/OsuModMagnetised.cs:47-81`)
```
half = Interpolation.Lerp(3000, 40, (double)Strength) = 3000 + (40 − 3000)*s
circle: dest = cursorPos
slider: dest = head.Result.HasResult ? cursorPos − slider.Ball.DrawPosition : cursorPos
        (Ball.Position = CurvePositionAt(progress) set in the slider's UpdateAfterChildren of the previous step)
x = (float)DampContinuously((double)X, (double)dest.X, half, elapsed); y likewise; Position = (x, y)
DampContinuously(c, g, half, e) = c + (g − c) * (1 − Math.Pow(0.5, e / half))        (F/Utils/Interpolation.cs:18-50)
```
Spinners are not moved. Judged objects are still moved while alive. Schedule-dependent (D9).

### 7.2 Repel (`O/Mods/OsuModRepel.cs:48-95`)
```
dest = Vector2.Clamp(2f*Position − cursorPos, (0,0), (512,384))        // osuTK Clamp: x<min?min:(x>max?max:x) [verified op 128]
if Slider: b = CalculatePossibleMovementBounds(slider) (GenerationUtils.Reposition.cs:266-303, float, CalculatedPath + radius)
           dest = Vector2.Clamp(dest, (b.Left, b.Top), (b.Right, b.Bottom))   // Right = X + Width, Bottom = Y + Height (float adds)
circle: easeTo(dest);  slider: easeTo(head judged ? dest − Ball.DrawPosition : dest)
easeTo: half = (double)Vector2.Distance(Position, cursorPos) / (0.04 * (double)Strength + 0.04)
        x = (float)DampContinuously(X, dest.X, half, elapsed) …
```
Edge: `half == 0` (cursor exactly on the object) gives `e/0 = +∞` → `Pow(0.5, ∞) = 0` → a jump to `dest`. With
`elapsed == 0` as well, `0/0 = NaN` → the position becomes NaN → `Drawable.Position` setter throws (`!IsFinite`), and
the oracle would crash. The model should flag it.

### 7.3 Depth (`O/Mods/OsuModDepth.cs:73-161`)
Constants: `cam = (256f, 192f, −200f)`; `scaleForDepth(z) = 200f / Math.Max(1f, z + 200f)` (computed as `−cam.Z /
Math.Max(1f, z − cam.Z)`); `sliderMinDepth = depthForScale(1.5f) = 200f/1.5f + (−200f)`;
`toPlayfield(s, P) = (P − cam.xy) * s + cam.xy` (Vector2 float). `t = playfield.Time.Current`.
```
circle (processHitObject): speed = (double)MaxDepth / p; appear = Start − p
       z = MaxDepth − (float)((max(t, appear) − appear) * speed)        // no clamp after StartTime: z < 0, scale > 1 late
       s = scaleForDepth(z); Position = toPlayfield(s, StackedPosition); Scale = (s, s)
slider: zEnd = MaxDepth − (float)((max(Start + Duration, appear) − appear) * baseSpeed)
       if zEnd > sliderMinDepth: as circle
       else: off = Duration + 500; slow = min(−sliderMinDepth / off, baseSpeed); decT = p*0.2
             decD = (float)(decT * (baseSpeed + slow) * 0.5)
             t < Start − decT : z = (decD + (float)(baseSpeed*(p − decT))) − (float)((max(t,appear) − appear)*baseSpeed)
             t < Start        : to = t − (Start − decT); dec = (slow − baseSpeed)/decT
                                z = decD − (float)(baseSpeed*to + dec*to*to*0.5)
             else             : z = −(float)((min(t, Start + off) − Start) * slow)
             Position/Scale as above
```
The slider scale changes **during the body**, so the follow radius is scaled (§2.3). It is a
`ModWithVisibilityAdjustment` that is incompatible with every other one. `ShowApproachCircles` is visual.

### 7.4 Barrel Roll
See §2.5. Effects on judgement: float rounding in all matrices, and hover always refreshed before presses (§2.6).
No positional change in gamefield space.

---------------------------------------------------------------------------------------------------

## 8. Mods confirmed visual-only (and the exceptions)

### 8.1 Hidden (`O/Mods/OsuModHidden.cs`)
- Step 9: `TimeFadeIn = 0.4·preempt` for non-sliders, recursively (sliders keep theirs; their heads are changed).
  `TimeFadeIn` feeds **Transform** (§6.3) and the circle-piece fade. FL/TR otherwise don't read it.
- DHO alpha fades: circles (and **slider heads**) `FadeOut(0.3·p)` from `Start − p + TimeFadeIn` (so alpha 0 by about
  `Start − 0.3p`). Sliders fade the body only; ticks, tails and spinners fade too. While Idle a DHO is present anyway
  (§1.7), so **unjudged objects are unaffected**.
- **No exception for judged heads.** DHO input propagation ignores presence (§1.7, `DrawableHitObject.cs:76,78`), so the
  HD fade of a judged Classic head does not stop it consuming hovered presses; it consumes them until its lifetime ends
  (hit: `Delay(800).FadeOut()` + `Expire`, miss: `FadeOut(100)`, `DrawableHitCircle.cs:209-235`). HD is judgement-
  irrelevant apart from update gating of judged DHOs (§1.7).
- `OnlyFadeApproachCircles` → approach circles only (visual). HD `IsFirstAdjustableObject` skips spinners and spinner
  ticks.

### 8.2 Others
- **Traceable**: hides `CirclePiece` (child) of circles/heads/repeats and the whole `DrawableSliderTail` DHO (alpha 0,
  but Idle so present; tail position is irrelevant). Visual.
- **Flashlight**: overlay drawable. `OnMouseMove` returns base (false), so it does not block the high-frequency
  MouseMove chain (`O/Mods/OsuModFlashlight.cs:74-84`). Slider dim is visual.
- **Bubbles**: adds bubble drawables in a separate `PlayfieldAdjustmentContainer` in `Overlays`, with no input
  handling. It hides judgements (`DisplayJudgements`, visual) (`O/Mods/OsuModBubbles.cs:63-117`).
- **Approach Different / Freeze Frame (approach part)**: approach circle only. FR's preempt change is §5.4.
- No Scope, Bloom (cursor alpha/scale; `ActiveCursor.DrawPosition` is unaffected by its scale), Blinds,
  Synesthesia, Muted: visual or audio.

---------------------------------------------------------------------------------------------------

## 9. IncreaseFirstObjectVisibility (default true in the oracle config)

`FirstObject` = first object (recursively into nested ones) passing `IsFirstAdjustableObject` (default true; HD/TC:
not spinner or spinner tick), computed in each mod's `ApplyToBeatmap` at step 9, in mod-list order (TP computes it
*after* regenerating) (`ModWithVisibilityAdjustment.cs:56-74`). The check is "`o.HitObject` is FirstObject or nested
in it" (:94-109), so a first slider's head counts.

| Mod | increased-visibility state | effect on first object |
|---|---|---|
| GR, DF | empty | scale 1 throughout |
| SI | empty | no rotation or scale |
| TP | empty | scale 1 (no 0.5→1 tween) |
| TR, WG, DP | same as normal | affected normally (TR still advances `theta`) |
| HD | CirclePiece-only fade | DHO alpha stays 1 → judged Classic head stays present |
| TC | empty | visual |

---------------------------------------------------------------------------------------------------

## 10. Verification checklist (to do before relying on this)
1. `nettest`: `System.Random(seed).NextDouble()` sequences (seeds 0, ±1, int.MinValue, int.MaxValue, random);
   `float.DegreesToRadians`; `MathF.Cos/Sin` symmetry `f(−x)`; decimal round-trip of `Strength` values.
2. Decompile osuTK 1.0.211 (`ilspycmd`, run when the machine is idle): `Vector2.LengthFast`/`InverseSqrtFast`,
   `Vector2.Length`, `Distance`, `Clamp`, operator order.
3. Oracle `--dump-env` with full ancestor chain parameters (§2.5) and BR scale `s`.
4. Oracle per-step dumps of DHO `Position/Scale/Rotation` under each P-class mod (especially WG slider heads, TR
   `theta` progression, TP+GR order) to diff the transform-tracker model.
5. Masking-away check (§1.7).
