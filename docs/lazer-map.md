# osu!lazer (2026.1005.0-lazer) osu!standard replay evaluation — code map

Scope: everything that turns `.osu` + `.osr` + mods(+settings) into per-object `HitResult`s, statistics,
max combo, accuracy, total score and pass/fail, in the pinned lazer release.

Path conventions:
- `L/...` = `/home/exedev/lazerproof/lazer/...` (commit in `LAZER_COMMIT`)
- `F/...` = `/home/exedev/lazerproof/osu-framework/...` = shallow clone of osu-framework at tag **2026.921.1**,
  which is the version `osu.Game.csproj:41` references (`ppy.osu.Framework 2026.921.1`). It is gitignored and only
  there to be read (PathApproximator, input, clocks, BindableNumber, and so on).
- `O/...` = `L/osu.Game.Rulesets.Osu/...`, `G/...` = `L/osu.Game/...`

Line numbers are from these exact checkouts.

---------------------------------------------------------------------------------------------------

## 0. Executive summary (the facts that matter most for a formal model)

1. **Judgement does not come from a pure function.** It comes from the drawable tree: `DrawableHitObject`s
   (DHOs) inside a `FrameStabilityContainer` (FSC), with input routed through an osu-framework
   `InputManager`/`KeyBindingContainer`. Hit tests run in screen space through float32 4x4 matrices
   (`ToScreenSpace`/`ToLocalSpace`). In exact arithmetic these reduce to "distance in osu!pixels <= radius".
2. **Evaluation happens at discrete times.** One FSC sub-frame runs per time step. The step times are every replay
   frame time (each frame is visited exactly once, in order) plus intermediate times. The intermediate times depend
   on the reference (audio/gameplay) clock, capped to at most `1000/60` ms per step when the gap is larger than
   `1.2f*1000/60` (about 20.000000 ms). **This makes lazer's own replay playback depend on frame timing.** Slider
   tracking, spinner rotation, health drain and several mods are sampled per step, and the cursor position is
   **linearly interpolated** between frames. A canonical step schedule has to be fixed (see §6/§7).
3. Per step, the order is: FrameStableComponents (ScoreProcessor, HealthProcessor drain, BreakTracker) →
   RulesetInputManager (apply interpolated mouse position → hover recompute → key releases → key presses → hits)
   → Playfield.Update (mods `IUpdatableByPlayfield`, rewind) → HitObjectContainer lifetime (objects become alive)
   → each DHO subtree (transforms, then Update, then children, then `UpdateAfterChildren` → `UpdateResult(false)`:
   auto-misses, ticks, tails, spinner end).
4. Notelock: `StartTimeOrderedHitPolicy` by default. `LegacyHitPolicy` is used when `OsuModClassic.ClassicNoteLock`
   is on, and **every stable (.osr version < 30000000) replay gets `OsuModClassic` with default settings
   automatically** (`G/Scoring/Legacy/LegacyScoreDecoder.cs:91-92`).
5. Score: standardised `500000*acc*comboProgress + 500000*acc^5*accProgress + bonus`, times a multiplier from
   `OsuScoreMultiplierCalculatorV2` (new in this version; the old per-mod `ScoreMultiplier` is gone).
6. **`ReplayPlayer` suppresses failing until the last replay frame** (`G/Screens/Play/ReplayPlayer.cs:55-68`).
   Live-play pass/fail has to be emulated explicitly.

---------------------------------------------------------------------------------------------------

## 1. Beatmap pipeline

### 1.1 Decoding `.osu` — `G/Beatmaps/Formats/LegacyBeatmapDecoder.cs`, `LegacyDecoder.cs`, `Parsing.cs`

- Version header `osu file format vN` (`LegacyBeatmapDecoder.cs:55`). Version < 5 → `offset = 24` ms
  (`EARLY_VERSION_TIMING_OFFSET`, :30, :75). The offset is added to hit-object times, timing points, breaks and
  preview time. The replay decoder also adds it to frame times (§2.1).
- Line loop (`LegacyDecoder.cs:38-79`): skip blank lines and lines starting with `//` (:81). Strip `//` comments
  except in `[Metadata]` (:101-108: only if index > 0). `TrimEnd`. `[Section]` headers. **Any exception while
  parsing a line is caught and logged, and the line is dropped** (:67-77). The model must reproduce this
  per-line failure behaviour (e.g. an unparsable hit object line simply disappears).
- `Parsing.ParseFloat/ParseDouble/ParseInt` (`Parsing.cs:18-50`): `float.Parse`/`double.Parse`/`int.Parse` with
  InvariantCulture. Limit ±int.MaxValue by default, ±131072 (`MAX_COORDINATE_VALUE`) for coordinates. NaN is
  rejected unless `allowNaN`. .NET float parsing is correctly rounded (IEEE round-to-nearest from the decimal
  string). Note that `float.Parse` accepts things like exponents and leading/trailing whitespace (NumberStyles.Float|AllowThousands).
- `[Difficulty]` (`:401-436`): HP/CS/OD/AR are **float**, SliderMultiplier/SliderTickRate are **double**. If no
  `ApproachRate` key appears before/after, AR = OD (AR is overwritten by OD only while `!hasApproachRate`, i.e.
  order-dependent: `OverallDifficulty` after `ApproachRate` keeps AR).
- `applyDifficultyRestrictions` (`:118-132`): clamp HP, CS, OD, AR to [0,10] (CS mania differs), SliderMultiplier
  [0.4,3.6], TickRate [0.5,8].
- Timing points (`handleTimingPoint` :484-574): `time` double (+offset). `beatLength` double, NaN allowed.
  `speedMultiplier = beatLength < 0 ? 100.0 / -beatLength : 1`. Uninherited (`split[6][0]=='1'` or missing) →
  `TimingControlPoint{BeatLength}` (BeatLength is a `BindableDouble` with **MinValue 6, MaxValue 60000**:
  `G/Beatmaps/ControlPoints/TimingControlPoint.cs:64-68`, so it is clamped). Every line also adds
  `DifficultyControlPoint{GenerateTicks = !NaN(beatLength), SliderVelocity = speedMultiplier}`. SliderVelocity is
  a BindableDouble clamped to **[0.1, 10]** (`DifficultyControlPoint.cs:24-28`). Points at the same time are
  buffered and flushed (`addControlPoint`/`flushPendingPoints` :576-603). Inherited lines (added last) override
  uninherited ones of the same type at the same time. Redundant points are dropped by `ControlPointInfo.Add`
  (`CheckAlreadyExisting`, `ControlPointInfo.cs:120-127, 348-363`; `LegacyControlPointInfo.cs:50-64`).
- Lookups: `TimingPointAt(t)` = last timing point with `Time <= t`, else the **first** timing point
  (`ControlPointInfo.cs:75`, binary search :246-340). `DifficultyPointAt(t)` = last ≤ t else DEFAULT (SV 1,
  ticks on) (`LegacyControlPointInfo.cs:41`).
- Breaks (`handleEvent`, type 2/`Break`): start/end + offset, `end = max(start, end)`.
- After parsing (`ParseStreamInto` :85-111): hit objects are **stably** sorted by StartTime (`OrderBy`, :103).
  `postProcessBreaks` (:137-153) forces NewCombo on the first object after each break. Then per object
  `applyDefaults` (:155-166) sets `GenerateTicks` and `SliderVelocityMultiplier` from `DifficultyPointAt(StartTime)`.
  This decode-time ApplyDefaults is irrelevant for gameplay (redone later).
- Hit object lines — `G/Rulesets/Objects/Legacy/ConvertHitObjectParser.cs`:
  - pos (:56-59): for format version < 128 (`FIRST_LAZER_VERSION`, `LegacyBeatmapEncoder.cs:25`) coordinates are
    **truncated to int** `(int)ParseFloat(...)`. For ≥128 they are kept as floats.
  - `startTime = ParseDouble(split[2]) + offset` (:61). type bits: combo offset `(type & 0x70) >> 4`, NewCombo bit.
  - Circle (:76). Slider (:83-154): `repeatCount = max(0, slides - 1)` (>9000 throws), `length = max(0,
    ParseDouble(split[7]))`, `0 → null` (no expected distance). Path string (:280-348): letter tokens start
    segments, first segment is prefixed with a (0,0) point; points are relative to the head position
    (`pos -= startPos`, int-truncated for v<128). `convertPathType` (:237-257): `C`/default → Catmull, `B[n]` →
    BSpline(n) or Bezier, `L` linear, `P` perfect. `convertPoints` (:357-427): for v<128, P with ≠3 points →
    Bezier; colinear P (`Precision.AlmostEquals(0, cross)` float eps 1e-3) → Linear. For v≥128, P with >3 points →
    Bezier. Consecutive duplicate points split implicit segments (not for legacy Catmull).
  - **Zero-length slider fix** (:491-495): if `Precision.AlmostEquals(path.Distance, 0)` (double eps 1e-7) then
    repeatCount = 0.
  - Spinner (:155-163): position forced to (256,192); `duration = max(0, end + offset - start)`.
  - NewCombo: `firstObject || lastObject is ConvertSpinner || newCombo` for circles/sliders (:460, :500).
    Spinners keep their own flag.

### 1.2 Playable beatmap — `G/Beatmaps/WorkingBeatmap.cs:277-352` (`GetPlayableBeatmap`)

The order matters:
1. `converter = ruleset.CreateBeatmapConverter`; mods `IApplicableToBeatmapConverter` (none in osu!).
2. `converter.Convert()` (`G/Beatmaps/BeatmapConverter.cs:44-90`): clones the beatmap/BeatmapInfo/ControlPointInfo.
   Hit objects are converted then **stably** re-sorted by StartTime (:73). `Beatmap.Difficulty` is a *clone* of
   `BeatmapInfo.Difficulty` (`G/Beatmaps/Beatmap.cs:22-44`), so mods mutate `Difficulty` only and
   `BeatmapInfo.Difficulty` stays unmodded. The score multiplier context uses `BeatmapInfo.Difficulty` (§4.2).
   `OsuBeatmapConverter` (`O/Beatmaps/OsuBeatmapConverter.cs:27-75`): `IHasPathWithRepeats` → Slider (copies
   Path, NodeSamples, RepeatCount, Position, NewCombo, ComboOffset, GenerateTicks, SV multiplier,
   **`TickDistanceMultiplier = BeatmapVersion < 8 ? 1f / DifficultyPointAt(StartTime).SliderVelocity : 1`**
   (:49, double division)). `IHasDuration` → Spinner (EndTime). Otherwise HitCircle.
3. Mods `IApplicableAfterBeatmapConversion` (osu!: StrictTracking replaces Sliders with `StrictTrackingSlider`).
4. If any `IApplicableToDifficulty`: each such mod's `ApplyToDifficulty(converted.Difficulty)` in mod-list order.
5. `OsuBeatmapProcessor.PreProcess()` (`O/Beatmaps/OsuBeatmapProcessor.cs:29-43`): force NewCombo on the first
   object and the first object after a spinner. Then base `BeatmapProcessor.PreProcess` (`G/Beatmaps/BeatmapProcessor.cs:21-30`)
   → `UpdateComboInformation` (`O/Objects/OsuHitObject.cs:185-208`): sets ComboIndex, IndexInCurrentCombo, and
   **`lastObj.LastInCombo = true`** when a new combo starts (spinners never start a combo; the last object of
   the map is never `LastInCombo`).
6. `obj.ApplyDefaults(controlPoints, converted.Difficulty)` for each top-level object (§1.3).
7. Mods `IApplicableToHitObject` (each mod over all objects): HR (vertical flip), Mirror, Classic
   (`ClassicSliderBehaviour`). Flipping replaces `slider.Path`, which fires `updateNestedPositions`
   (`O/Objects/Slider.cs:229-254`) so nested objects follow. The Slider `Position` setter also updates nested.
8. `OsuBeatmapProcessor.PostProcess()` → **`ApplyStacking`** (§1.5). It runs after ApplyDefaults, so
   `TimePreempt` includes AR mods.
9. Mods `IApplicableToBeatmap` (Hidden fade-in, FreezeFrame preempt, Random, TargetPractice, TimeRamp,
   AdaptiveSpeed, Synesthesia, NoScope, every `ModWithVisibilityAdjustment` which records `FirstObject`, …).

### 1.3 ApplyDefaults — `G/Rulesets/Objects/HitObject.cs:105-162`

`ApplyDefaultsToSelf` → clear nested → `CreateNestedHitObjects` → bind nested combo bindables →
**`nestedHitObjects.Sort(by StartTime)` — `List.Sort`, which is UNSTABLE introsort** (:130). Equal nested start
times can reorder (e.g. tick at the same time as a repeat; not normally possible). Then the nested objects'
ApplyDefaults. Base self defaults: `HitWindows ??= CreateHitWindows(); HitWindows.SetDifficulty(OD)` (:156-162).
`MaximumJudgementOffset = HitWindows.WindowFor(Miss)` (:203). `GetEndTime` (:258).

`OsuHitObject.ApplyDefaultsToSelf` (`O/Objects/OsuHitObject.cs:170-183`):
- `TimePreempt = (int)DifficultyRange(AR, 1800, 1200, 450)` (int truncation; `IBeatmapDifficultyInfo.cs:57-72, 120-121`:
  `DifficultyRange(d,min,mid,max) = d>5 ? mid+(max-mid)*((d-5)/5) : d<5 ? mid+(mid-min)*((d-5)/5) : mid`, all double, d from float; NOTE grouping: divide first — fixed after sim found 1-ulp health diffs).
- `TimeFadeIn = 400 * min(1, TimePreempt / 450)`.
- `Scale = CalculateScaleFromCircleSize(CS, true)` (`G/Rulesets/Objects/Legacy/LegacyRulesetExtensions.cs:46-59`):
  `(float)(1.0f - 0.7f * ((cs-5)/5)) / 2 * 1.00041f`. The inner part is double, then cast to float, then float
  `/2` and `* 1.00041f`.
- `Radius = 64 * Scale` (double, :94). `StackOffset = new Vector2(StackHeight * Scale * -6.4f)` (float, :92).
  `StackedPosition = Position + StackOffset` (:76). Spinner `StackOffset = 0` (`Spinner.cs:59`).

`OsuHitWindows` (`O/Scoring/OsuHitWindows.cs`): `great = floor(DR(OD,80,50,20)) - 0.5`, `ok = floor(DR(OD,140,100,60)) - 0.5`,
`meh = floor(DR(OD,200,150,100)) - 0.5`, `miss = 400` (:12-19, :39-44). Allowed results Great/Ok/Meh/Miss.
`HitWindows.ResultFor(off)` (`G/Rulesets/Scoring/HitWindows.cs:299-310`): `|off| <= great → Great`, then Ok, Meh,
`|off| <= 400 → Miss`, else None. `CanBeHit(off) = off <= meh` (:326). Empty windows (ticks/tails/spinners/slider body)
give `WindowFor = 0`, so MaximumJudgementOffset = 0 (spinner ticks override it to SpinnerDuration).

Slider (`O/Objects/Slider.cs`):
- `ApplyDefaultsToSelf` (:156-168): `tp = TimingPointAt(StartTime)`;
  `Velocity = 100 * SliderMultiplier / GetPrecisionAdjustedBeatLength(this, tp, "osu")`;
  `scoringDistance = Velocity * tp.BeatLength` (intentionally not simplified);
  `TickDistance = GenerateTicks ? scoringDistance / SliderTickRate * TickDistanceMultiplier : +inf`.
  `GetPrecisionAdjustedBeatLength` (`LegacyRulesetExtensions.cs:17-41`): `svAsBeatLength = -100 / SV`;
  `bpmMultiplier = svAsBeatLength < 0 ? Math.Clamp((float)-svAsBeatLength, 10, 1000) / 100.0 : 1`
  (float clamp, then double division); returns `tp.BeatLength * bpmMultiplier`.
- `EndTime = StartTime + SpanCount * Path.Distance / Velocity` (:28). `SpanDuration = Duration / SpanCount` (:91).
  `EndPosition = Position + CurvePositionAt(1)` (:41).
- `CreateNestedHitObjects` (:170-227) consumes `SliderEventGenerator.Generate(StartTime, SpanDuration, Velocity,
  TickDistance, Path.Distance, SpanCount)` (`G/Rulesets/Objects/SliderEventGenerator.cs:26-124`):
  - `length = min(100000, totalDistance)`, `tickDistance = clamp(tickDistance, 0, length)`,
    `minDistanceFromEnd = velocity * 10`.
  - Head at StartTime. Per span: if tickDistance ≠ 0, ticks `for (d = tickDistance; d <= length; d += tickDistance)`
    (accumulating double addition!), `break if d >= length - minDistanceFromEnd`. `pathProgress = d/length`,
    `time = spanStart + (reversed ? 1-p : p) * spanDuration` (:138-161). Reversed spans yield ticks reversed.
    Repeat at `spanStart + spanDuration` for span < last, PathProgress `(span+1)%2`.
  - LegacyLastTick (time `max(start + total/2, finalSpanStart + spanDuration - 36)`) is generated, but **`Slider`
    ignores it** (there is no case for it). Tail at `startTime + totalDuration`.
  - Slider creates: `SliderTick{SpanIndex, SpanStartTime, StartTime=e.Time, Position = Position + Path.PositionAt(p)}`,
    `SliderHeadCircle{StartTime, Position}`, `SliderTailCircle{RepeatIndex = e.SpanIndex, StartTime = e.Time,
    Position = EndPosition}`, `SliderRepeat{RepeatIndex, StartTime = StartTime + (SpanIndex+1)*SpanDuration}`
    (recomputed, not e.Time).
- Nested preempts (lifetime only): `SliderEndCircle` (`SliderEndCircle.cs:28-45`) repeat index>0 → `2*SpanDuration`,
  else `+= StartTime - Slider.StartTime`. `SliderTick` (`SliderTick.cs:18-32`) `(StartTime-SpanStartTime)/2 +
  (SpanIndex>0 ? 200 : TimePreempt*0.66f)`.
- Judgements: Slider `ClassicSliderBehaviour ? OsuJudgement(Great) : OsuIgnoreJudgement(IgnoreHit)` (:289-293).
  Head `Classic ? SliderTickJudgement(LargeTickHit) : OsuJudgement(Great)` (`SliderHeadCircle.cs:17`).
  Tail `Classic ? LegacyTailJudgement(SmallTickHit) : TailJudgement(SliderTailHit)` (`SliderTailCircle.cs:23-33`).
  Repeat `SliderEndJudgement(LargeTickHit)`. Tick `SliderTickJudgement(LargeTickHit)`.
  Min results (`G/Rulesets/Judgements/Judgement.cs:61-85`): LargeTickHit→LargeTickMiss, SmallTickHit→SmallTickMiss,
  **SliderTailHit→IgnoreMiss**, SmallBonus/LargeBonus/IgnoreHit→IgnoreMiss, otherwise Miss.

Spinner (`O/Objects/Spinner.cs:61-96`): `minRps = DR(OD,90,150,225)/60`, `maxRps = DR(OD,250,380,430)/60`,
`SpinsRequired = (int)(minRps*dur/1000 + 0.0001)`, `MaximumBonusSpins = max(0, (int)(maxRps*dur/1000 + 0.0001) -
SpinsRequired - 2)`. `totalSpins = MaxBonus + Required + 2` ticks at `StartTime + (float)(i+1)/totalSpins * Duration`
(the fraction is computed in **float**). The first `SpinsRequired+2` are `SpinnerTick` (SmallBonus, 10 pts), the
rest `SpinnerBonusTick` (LargeBonus, 50 pts). Spinner judgement is `OsuJudgement` (Great).

### 1.4 SliderPath / PathApproximator (float32 geometry)

`G/Rulesets/Objects/SliderPath.cs` (control points are float `Vector2`, osuTK):
- `calculatePath` (:287-334): split at typed control points. Segment type defaults to LINEAR. 1-vertex segment →
  that vertex. Skip the first vertex of a subpath if it equals the last emitted one (exact float ==).
  `segmentEnds` recorded.
- `calculateSubPath` (:336-424): Linear → points as-is (`F/.../PathApproximator.cs:255-263`). PerfectCurve: needs
  exactly 3 points and `CircularArcProperties.IsValid`. If `subPoints >= 1000` (computed with mixed float/double,
  :355) or the arc output is empty → fall through to BSpline. Catmull → `CatmullToPiecewiseLinear` then (since
  `Slider.Path` has `OptimiseCatmull = true`, `Slider.cs:45`) the 6px optimisation (:385-419) which accumulates
  `optimisedLength` (double). Default/Bezier → `BSplineToPiecewiseLinear(points, type.Degree ?? count)`.
- `calculateLength` (:426-485): `calculatedLength = optimisedLength` + Σ `(float Vector2 diff).Length` (float
  length added to a **double** accumulator); cumulativeLength double. If ExpectedDistance is set and differs: if
  the last two points are equal and expected > calculated → no extension (stable quirk). Otherwise trim points with
  cumulative ≥ expected, then set the last point to `prev + dir.Normalized() * (float)(expected - cum[^1])`, and
  the last cumulative = expected (exact).
- `PositionAt(p)` (:205-211): `d = clamp(p,0,1) * Distance`; `i = cumulativeLength.BinarySearch(d)` (`~i` if
  missing); `interpolateVertices` (:500-522): if `AlmostEquals(d0,d1)` (1e-7) → p0, else `p0 + (p1-p0) * (float)((d-d0)/(d1-d0))`.
- `ProgressAt/CurvePositionAt` (`G/Rulesets/Objects/Types/IHasPathWithRepeats.cs:24-48`):
  `p = progress*SpanCount % 1; if ((int)(progress*SpanCount) % 2 == 1) p = 1-p`.

`F/osu.Framework/Utils/PathApproximator.cs` (all float `Vector2` arithmetic; .NET does not contract into FMA):
- `BezierToPiecewiseLinear` (:33) = BSpline with degree `count-1`. `BSplineToPiecewiseLinear` (:79-148):
  `bSplineToBezierInternal` (:774-830, Boehm knot insertion, int/float mixed `(l*p + q)/(l+1)`), then an iterative
  DFS subdivision stack: `bezierIsFlatEnough` (:831-850: `|p[i-1] - 2p[i] + p[i+1]|² > 0.25²*4` → not flat),
  `bezierSubdivide` (:852-876, midpoint `/2`), `bezierApproximate` (:878-905, `0.25f*(l[2i-1] + 2*l[2i] + l[2i+1])`).
  The final control point is appended.
- `CatmullToPiecewiseLinear` (:150-170): per segment 50 steps, **2 points per step** (`t=c/50` and `(c+1)/50`,
  float). `catmullFindPoint` (:907-918) uses the explicit float polynomial.
- `CircularArcToPiecewiseLinear` (:175-200) and `CircularArcProperties` (`F/.../CircularArcProperties.cs:34-88`):
  degeneracy test `AlmostEquals(0, cross)` (float, 1e-3); float centre/radius; `Math.Atan2` in double;
  `amountPoints = 2r <= 0.1 ? 2 : max(2, ceil(thetaRange / (2*acos(1 - 0.1/r))))`; points
  `centre + (float)cos θ, (float)sin θ * radius` with **double `Math.Cos/Sin/Atan2/Acos`**.
- **Platform libm dependence.** .NET's `Math.Sin/Cos/Atan2/Acos/Pow/Log` and the `MathF` variants call the CRT/libm
  (glibc on Linux). They are not correctly rounded, so bit-exact replication needs the same libm (or a proven
  equivalent). `Math.Sqrt`/`MathF.Sqrt` are exact.

### 1.5 Stacking — `O/Beatmaps/OsuBeatmapProcessor.cs:52-281`

- Reset all StackHeight to 0. `BeatmapVersion >= 6` → `applyStacking` (:69-222), else `applyStackingOld` (:224-269).
- `STACK_DISTANCE = 3` (:22). Distances use `Vector2Extensions.Distance` = `MathF.Sqrt(dx²+dy²)` (float,
  `F/osu.Framework/Graphics/Vector2Extensions.cs:39-54`) with `< 3`.
- `stackThreshold = (int)TimePreempt * StackLeniency` (float; :280-281). StackLeniency is float from `[General]`.
- New algorithm: forward extension pass (:77-117, uses `objectN.StartTime - endTime > threshold`, double vs float);
  reverse pass (:122-221). Circle case: `(int)objectI.StartTime - (int)endTime > threshold` (int truncation to match
  stable, :157); negative stacking under slider ends (:173-188). Slider case (:200-220) uses
  `objectI.StartTime - objectN.StartTime`.
- Setting `StackHeight` propagates to nested objects (`OsuHitObject.cs:158-168`). Stacking is applied *before*
  `IApplicableToBeatmap` mods (Random/TargetPractice reposition after stacking. TP's new circles have StackHeight 0).

### 1.6 Difficulty-affecting mods (CS → radius, OD → windows/spinner rpm, AR → preempt/stacking/lifetime, HP → health)

| Mod | Effect (file) |
|---|---|
| HR | HP×1.4f, OD×1.4f, AR×1.4f (each `min(..,10f)`), CS×1.3f min 10 (float) (`G/Rulesets/Mods/ModHardRock.cs:23-28`, `O/Mods/OsuModHardRock.cs:25-32`). `ApplyToHitObject`: `ReflectVerticallyAlongPlayfield` (y → 384 - y, control points y → -y, `O/Utils/OsuHitObjectGenerationUtils.cs:128-170`). |
| EZ | CS, AR, HP ×0.5f; OD ×0.5f (`ModEasy.cs:23-28`, `OsuModEasy.cs:14-19`). Extra lives: `PerformFail` refills health and decrements `Retries` (default 2, 0..10) (`ModEasyWithExtraLives.cs:41-70`). |
| DA | Overrides CS/AR/OD/HP when non-null. `DifficultyBindable` precision 0.1, range [0,10], extended [0,11] (AR [-10,11]) (`OsuModDifficultyAdjust.cs:21-40,78-84`, `ModDifficultyAdjust.cs:38-60,122-126`). |
| TP | AR ×0.5f (`OsuModTargetPractice.cs:118-122`). |
| Mirror | Horizontal/Vertical/Both reflection (`OsuModMirror.cs:23-42`). |

Mod setting values go through `BindableNumber.setValue` (`F/osu.Framework/Bindables/BindableNumber.cs:75-90`): clamp,
then **round via `decimal`** to `Precision`, then convert back to T. Deserialised settings (from the `.osr` JSON) must
be normalised this way.

---------------------------------------------------------------------------------------------------

## 2. Replay pipeline

### 2.1 `.osr` decoding — `G/Scoring/Legacy/LegacyScoreDecoder.cs`

- Header (:48-118): ruleset byte, `int version`. `IsLegacyScore = version < 30000000` (`FIRST_LAZER_VERSION`,
  `LegacyScoreEncoder.cs:74`; LATEST 30000019 :69). Then beatmap MD5, username, replay MD5, counts 300/100/50/geki/katu/miss
  (ushort), int total score, ushort max combo, bool perfect, int legacy mods, HP graph string, DateTime ticks,
  `byte[]` LZMA replay. If version ≥ 20140721 an int64 online id (≥ 20121008 an int32). If version ≥ 30000001, an
  LZMA JSON `LegacyReplaySoloScoreInfo` (statistics, maximum statistics, **full mods with settings**, rank, total
  score without mods, pauses, client version).
- Mods (:88-94, :134): `ConvertFromLegacyMods` (`O/OsuRuleset.cs:96-148`: NC implies DT, PF implies SD, etc.).
  **Stable replays get `ModClassic` (defaults: all options true) appended.** For lazer replays the JSON mod list
  replaces them (`m.ToMod(ruleset)` → bindable settings).
- `beatmapOffset = BeatmapVersion < 5 ? 24 : 0` (:98), added to every frame time (frame times start at `lastTime = beatmapOffset`).
- Frames (`readLegacyReplay` :268-352): text `w|x|y|z,` per frame. Fewer than 4 fields → skip. **`w == "-12345"` (RNG
  seed frame) → skip without adding its delta.** `diff = int.TryParse(w) ? int : (int)Math.Round(ParseFloat(w))`
  (Math.Round = banker's rounding). x, y = float (x limit 131072). `lastTime += diff` (long). `buttons = ParseInt(z)`.
  - Stable fixups: if `f[1].Time < f[0].Time` → `f[1].Time = f[0].Time; f[0].Time = 0` (:320-324). If
    `f[0].Time > f[2].Time` → `f[0].Time = f[1].Time = f[2].Time` (:327-328). Then remove frame 1 and frame 0
    if their position equals (256,-500) (:333-337).
  - Then **drop any frame whose time is less than the previously kept frame** (:341-351). Equal times are kept.
  - `OsuReplayFrame.FromLegacy` (`O/Replays/OsuReplayFrame.cs:60-66`): Position = (x,y). Actions in this fixed
    order: LeftButton if `Left1|Left2` (bits 1|4), RightButton if `Right1|Right2` (2|8), Smoke if bit 16
    (`G/Replays/Legacy/LegacyReplayFrame.cs:26-50`, `ReplayButtonState.cs`).
- Encoder (for lazer-made replays; `LegacyScoreEncoder.cs:164-181`): frame time `(int)Math.Round(time + offset)`, delta
  encoded, then `-12345|0|0|0`. **A lazer replay's frame times are integer-rounded versions of live-play times**,
  so playback is not live play (`osu.Game.Rulesets.Osu.Tests/TestSceneReplayStability.cs` documents the ±0.5 ms
  effects).

### 2.2 Replay input handler — `G/Rulesets/Replays/FramedReplayInputHandler.cs`, `O/Replays/OsuFramedReplayInputHandler.cs`

- Constructor re-sorts frames stably by Time (:99). `currentFrameIndex = -1`, `CurrentTime = -inf`.
- `SetFrameFromTime(t)` (:127-165): `frameStart = time(idx)`, `frameEnd = time(idx+1)` (−inf/+inf at the ends).
  - If `frameEnd <= t`: **`t = frameEnd; idx++`** (advance exactly one frame and snap time to it).
  - else if `t < frameStart && CurrentTime == frameStart`: idx-- (rewind only).
  - `CurrentTime = clamp(t, frameStart', frameEnd')`. Returns CurrentTime. The "important frame" null-return
    applies only if `FrameAccuratePlayback`, **which nothing in the game sets** (only a unit test), so it is inactive.
- `CollectReplayInputs` (`OsuFramedReplayInputHandler.cs:22-28`):
  - `position = Interpolation.ValueAt(CurrentTime, StartFrame.Position, EndFrame.Position, StartFrame.Time, EndFrame.Time)`
    where StartFrame = `Frames[max(0,idx)]`, EndFrame = `Frames[min(idx+1, last)]`. Vector2 interpolation
    (`F/osu.Framework/Utils/Interpolation.cs:352-362`): `cur = (float)(t - t0)`, `dur = (float)(t1 - t0)`; if dur == 0
    or cur == 0 → val1; `t = (float)(double)(cur/dur)`; `val1 + t*(val2 - val1)` (float).
  - `MousePositionAbsoluteInput{ GamefieldToScreenSpace(position) }` where `GamefieldToScreenSpace =
    HitObjectContainer.ToScreenSpace` (`G/Rulesets/UI/Playfield.cs:55`, set in `DrawableRuleset.SetReplayScore` :306-324).
  - `ReplayState<OsuAction>{ PressedActions = CurrentFrame?.Actions ?? [] }`. CurrentFrame is null before the first frame.
  - If `CurrentFrame.Header != null` (spectator frames only) a `ReplayStatisticsFrameInput` **overwrites
    ScoreProcessor state** (`ScoreProcessor.ResetFromReplayFrame`). Not applicable to .osr.
- `ReplayState.Apply` (`G/Input/Handlers/ReplayInputHandler.cs:43-70`): compares with the last state.
  `released = last.Except(cur)`, `pressed = cur.Except(last)` (or all/none). `RulesetInputManager.HandleInputStateChange`
  (`G/Rulesets/UI/RulesetInputManager.cs:81-101`) runs **all releases first, then presses**, in the frame's action
  order (Left, Right, Smoke).
- Key semantics: K1 and M1 both map to LeftButton. Switching M1↔K1 without a frame where neither is held gives
  **no new press**. Bindings are `SimultaneousBindingMode.Unique` (`O/OsuInputManager.cs:54-57`):
  `PropagatePressed` only fires if the action is not already in `pressedActions`
  (`F/osu.Framework/Input/Bindings/KeyBindingContainer.cs:322-345`). The press is added to `PressedActions`
  **before** propagation, so an action that some handler blocks (e.g. Alternate) still counts as held.

### 2.3 Clock stepping — `G/Rulesets/UI/FrameStabilityContainer.cs`

Tree: `DrawableRuleset` → `FrameStabilityContainer(GameplayStartTime)` → [`FrameStableComponents`
(ScoreProcessor, HealthProcessor, ComboEffects, BreakTracker — added by Player, `G/Screens/Play/Player.cs:461-473`),
`KeyBindingInputManager`(OsuInputManager) → [`PlayfieldAdjustmentContainer` → `OsuPlayfield`, Overlays]]
(`G/Rulesets/UI/DrawableRuleset.cs:172-201`).

- `UpdateSubTree` (:107-125): loop `updateClock(); base.UpdateSubTree()` **while state == RequiresCatchUp and less
  than 10 ms wall-clock has elapsed**. Each iteration is one complete gameplay "step".
- `updateClock` (:127-209): `proposed = referenceClock.CurrentTime`; `applyFrameStability` (:254-279):
  - first ever call: seek directly (`manualClock = proposed`).
  - if `manual < GameplayStartTime`: `manual = proposed = min(GameplayStartTime, proposed)` (jump).
  - else if `|manual - proposed| > (1000/60) * 1.2f` (the double `16.666…` times the float `1.2f`, ≈ 20.0000003 ms):
    `proposed = manual ± 1000/60` (towards proposed).
  - then `updateReplay`: `proposed = ReplayInputHandler.SetFrameFromTime(proposed)` (snaps to the next frame if
    passed, at most one frame per step).
  - `manualClock.CurrentTime = proposed`, `Rate = |ref.Rate| * direction`, `framedClock.ProcessFrame()` → children
    see `Time.Current = proposed`, `Time.Elapsed = proposed - previous`.
  - `RequiresCatchUp` if `proposed != referenceClock.CurrentTime`.
- `DrawableOsuRuleset.GameplayStartTime = first.StartTime - max(2000, first.TimePreempt)` (`O/UI/DrawableOsuRuleset.cs:82-91`).
- **Resulting step-time semantics:** with reference time R and current time c:
  `next = SetFrame(min/max(R, c ± 16.67 if |R-c| > 20))`. Every replay frame time is visited exactly once, in order.
  Between frames, extra steps appear depending on R's trajectory (real-time audio clock in the game, so
  framerate-dependent). Buttons are constant between frames; the cursor is interpolated.
- `GetTrueGameplayRate()` (`G/Screens/Play/GameplayClockExtensions.cs:14-22`) = `sign(rate) * AggregateFrequency *
  AggregateTempo` of `AdjustmentsFromMods` (FSC forwards the parent `GameplayClockContainer`'s, :303). Used by the
  spinner (rotation × rate) and `JudgementResult.GameplayRate`.

---------------------------------------------------------------------------------------------------

## 3. Judgement logic

### 3.1 Per-step update order (framework semantics)

`Drawable.UpdateSubTree` (`F/osu.Framework/Graphics/Drawable.cs:469-498`): `UpdateTransforms()` → scheduler →
`Update()`. `CompositeDrawable.UpdateSubTree` (`F/.../Containers/CompositeDrawable.cs:907-947`): base (above) →
`UpdateChildrenLife()` (lifetime add/remove) → **if `!IsPresent || !RequiresChildrenUpdate` stop** → each alive child
`UpdateSubTree` in child order → `UpdateAfterChildren()`.

`InputManager.Update` (`F/osu.Framework/Input/InputManager.cs:459-513`): apply all pending inputs in order. A mouse
position change calls `HandleMousePositionChange` (:959-975) → `handleMouseMove` (MouseMove to the positional queue)
→ **`updateHoverEvents` immediately** (:657-707). Then the replay state → key releases/presses (hover is already
current). Then high-frequency MouseMove to `IRequireHighFrequencyMousePosition` drawables (SliderInputManager,
SmokeContainer, CursorTrail, …) **every step even without movement**. Then `base.Update()` → children.

So in one FSC step at time t:
1. ScoreProcessor/HealthProcessor `Update`: `DrainingHealthProcessor.Update` drains health
   (`G/Rulesets/Scoring/DrainingHealthProcessor.cs:85-98`). `JudgementProcessor.Update` updates `HasCompleted`.
2. OsuInputManager: position → hover state → MouseMove (`SliderInputManager.screenSpaceMousePosition`,
   `SpinnerRotationTracker.mousePosition`) → releases → presses → `HitReceptor.OnPressed` → `UpdateResult(true)` →
   judgement (and hit-policy side effects) **using drawable state (positions, scales, alive set) from the previous step**,
   because transforms/IUpdatableByPlayfield for t have not run yet.
3. Playfield.Update (`G/Rulesets/UI/Playfield.cs:263-287`): every `IUpdatableByPlayfield` mod `Update(playfield)`, then revert loop (rewind only).
4. HitObjectContainer: `UpdateChildrenLife` adds DHOs whose `LifetimeStart <= t` (`LifetimeStart = StartTime -
   TimePreempt`, `OsuPlayfield.OsuHitObjectLifetimeEntry` `O/UI/OsuPlayfield.cs:225-235`; LifetimeEnd = EndTime + 400
   until judged). **A DHO that becomes alive at step t can't receive input until step t+1.**
5. DHOs in child order (sorted by `HitObjectContainer.Compare`: later start time first, so earlier objects come later
   in the list and get input first; ties by reverse ChildID, `G/Rulesets/UI/HitObjectContainer.cs:179-187`). Each DHO:
   transforms → `Update` → nested children → `UpdateAfterChildren` → `UpdateResult(false)`
   (`G/Rulesets/Objects/Drawables/DrawableHitObject.cs:667-672`). **Nested objects are judged before their parent.**

`DrawableHitObject.UpdateResult` (:758-770): no-op if rewinding or Judged. Otherwise
`CheckForResult(userTriggered, Time.Current - HitObject.GetEndTime())`. `ApplyResult` (:726-751): sets Type, **`RawTime =
Time.Current`**, `GameplayRate`, ArmedState, invokes `OnNewResult`. `DrawableHitObject.IsPresent` override (:144) keeps
Idle objects updating. `OnKilled` (:698-708) also calls `UpdateResult(false)`.

Result propagation and ordering: nested `OnNewResult` → parent → `HitObjectContainer` → `Playfield.onNewResult`
(:481-487, pushes judgedEntries) → `NewResult` handlers in subscription order: (a) `OsuPlayfield.onNewResult`
(`O/UI/OsuPlayfield.cs:189-207`) → `hitPolicy.HandleHit(judged)` (may `MissForcefully` earlier objects, whose results
re-enter this chain **and reach the processors first**), then (b) `DrawableRuleset.NewResult` → Player:
`HealthProcessor.ApplyResult; ScoreProcessor.ApplyResult` (`Player.cs:399-404`). **So the processor sees:
notelock-forced misses of earlier circles, then the hit that caused them.**

### 3.2 Hit circles — `O/Objects/Drawables/DrawableHitCircle.cs`

- Drawable position = `HitObject.StackedPosition` (:130-133), Origin centre. `HitReceptor` 128×128 (`OBJECT_DIMENSIONS`),
  `CornerRadius 64, CornerExponent 2` (:266-275) inside `scaleContainer.Scale = HitObject.Scale` (:107).
- Hover test: `CompositeDrawable.Contains` (`F/.../CompositeDrawable.cs:1404-1414`):
  `DrawRectangle.Shrink(r).DistanceExponentiated(ToLocalSpace(p), 2) <= Math.Pow(r, 2)`. With
  `effectiveCornerRadius = r*0.8f*exp/2 + 0.2f*r = 64.0f` (:1561),
  `DistanceExponentiated = MathF.Pow(dx,2) + MathF.Pow(dy,2)` in local units (`F/.../RectangleF.cs:347-353`).
  In exact arithmetic: **hit iff `|cursor - StackedPosition| <= 64*Scale` (inclusive)**. Actual: the float matrix
  round-trip gamefield→screen (replay handler) and screen→HitReceptor-local (inverse matrix).
- `HitReceptor.OnPressed` (:277-308): only Left/Right. If `!CanBeHit()` (default `!AllJudged`) → not handled. Record
  `ClosestPressPosition`. **If `IsHovered`: call `Hit()` (→ `UpdateResult(true)`), set `HitAction ??= action`, and
  return true (consumes the press even if the hit was rejected).** Otherwise not handled → the press goes on to the
  next drawable in the input queue.
- Press routing: `KeyBindingInputQueue` = non-positional input queue (tree pre-order of alive+loaded drawables)
  **reversed** (`KeyBindingContainer.cs:62-72`; `InputManager.buildNonPositionalInputQueue` :601-626). The first
  handler returning true stops it. Earlier objects get it first (§3.1-5). `InputBlockingMod.InputInterceptor` and
  the cursor sit after the playfield in the tree, so they are queried before the hit objects. The cursor returns
  false; the interceptor returns true to block.
- `CheckForResult` (:137-173):
  - `!userTriggered`: if `!CanBeHit(offset)` (`offset > meh`) → `MinResult` (Miss) at that step's time.
  - userTriggered: `result = ResultFor(offset)` (`|offset| <= 400` and > meh gives **Miss**; > 400 gives None).
    `clickAction = CheckHittable(this, Time.Current, result)`. Shake → shake. If `result == None || clickAction != Hit`
    → nothing. Else apply result.
- `HitResult` values: Great/Ok/Meh/Miss. `CursorPositionAtHit` is only for statistics.

### 3.3 Hit policies (notelock) — `O/UI/*HitPolicy.cs`

- Default: `OsuPlayfield.HitPolicy = new StartTimeOrderedHitPolicy()` (`O/UI/OsuPlayfield.cs:76`). Set into each DHO's
  `CheckHittable` on creation (:106-112). Slider heads delegate to their slider's (`DrawableSliderHead.cs:50`).
- `StartTimeOrderedHitPolicy` (`StartTimeOrderedHitPolicy.cs:26-104`): over `AliveObjects` (**alive DHOs ordered by
  StartTime**, `HitObjectContainer.cs:24`; ties use Dictionary enumeration order, not a defined order) and their
  nested objects with StartTime < target StartTime, find the last `DrawableHitCircle` (includes slider heads).
  `if (!blocking.Judged && time < blocking.StartTime) → Shake`. `result == None → Shake`. Else Hit. `HandleHit(h)` (only
  for circles/heads): miss forcefully every unjudged earlier circle/head (enumeration as above).
- `LegacyHitPolicy(hittableRange = 400 or 200 with Autopilot)` (`LegacyHitPolicy.cs:36-70`): selected by
  `OsuModClassic.ApplyToDrawableRuleset` when `ClassicNoteLock` (`O/Mods/OsuModClassic.cs:52-63`). Over the
  `AliveObjects` list: if the previous alive object has `StackHeight > 0` and is not AllJudged → **Ignore** (no
  shake, nothing). `result == None → Shake`. For each earlier not-AllJudged object: if `testObject.GetEndTime() + 3 <
  hitObject.StartTime` → Shake. Finally `|StartTime - time| < hittableRange ? Hit : Shake`. **No forced misses**
  (`HandleHit` empty). It works at top-level granularity: a slider blocks until all its nested objects are judged.
  Classic also sets the head `CanBeHit = !slider.AllJudged` (:96-99), so the head keeps consuming presses over its
  area until the whole slider is done.
- `AnyOrderHitPolicy` exists (`AnyOrderHitPolicy.cs`) but no osu! mod uses it.

### 3.4 Sliders — `DrawableSlider.cs`, `SliderInputManager.cs`, `DrawableSliderHead/Tail/Tick/Repeat.cs`

Tree (`DrawableSlider.cs:96-128`): `SliderInputManager`, shakeContainer[Body, tail proxy, ticks, repeats, **tail**
(after ticks/repeats)], headContainer, overlay, Ball. Position = StackedPosition (:130-131). `Size`/`OriginPosition`
come from the skin's `SliderBody` (`PathOffset = path.PositionInBoundingBox(vertices[0])`,
`O/Skinning/SliderBody.cs:32`, snaking variant `SnakingSliderBody.cs:44,119`) and are updated every
`UpdateAfterChildren` (:257-285). Nested objects are positioned relative to OriginPosition. **Hit tests depend
numerically (float rounding) on skin path radius and snaking state.**

`SliderInputManager` (`SliderInputManager.cs`):
- `screenSpaceMousePosition` from OnMouseMove (high-frequency, every step) (:66-70).
- `Update` (:72-76, runs as the slider's first child): `updateTracking(IsMouseInFollowArea(Tracking))`.
- `IsMouseInFollowArea(expanded)` (:184-196): `radius = (float)slider.Radius * (expanded ? 2.4f : 1)`
  (`DrawableSliderBall.FOLLOW_AREA = 2.4f`); `followProgress = clamp((t - Start)/Duration, 0, 1)`;
  `followPos = CurvePositionAt(progress)` (unstacked, relative to the head); `mouseInSlider = slider.ToLocalSpace(pos) - OriginPosition`;
  **`(mouse - follow).LengthSquared <= radius²`** (float). Ideal-arithmetic equivalent: `|cursor - (StackedPosition + CurvePositionAt(p))| <= r`.
  Already tracking → test 2.4r; not tracking → test 1r (hysteresis).
- `updateTracking(valid)` (:216-274): `headHitAction = HeadCircle.HitAction` (**set on any hovered press of the head
  even if the hit was rejected (shake) or too early**, `DrawableHitCircle.cs:297-301`; reset only on Idle state). If
  null → `timeToAcceptAnyKeyAfter = null`. If set and `timeToAcceptAnyKeyAfter == null` and the other key was not in
  last step's pressed set → `timeToAcceptAnyKeyAfter = t`. Valid action: if headHitAction and (no accept time or
  `t <= acceptTime`) → only that action, else Left or Right. `Tracking = (!slider.AllJudged || t <= EndTime) && valid &&
  anyValidActionPressed` (PressedActions of the KeyBindingContainer, which includes blocked presses).
  `lastPressedActions` updated. Tracking history pushed (rewind only).
- `TryJudgeNestedObject(nested, offset)` (:142-178), called from each tick/repeat/tail `CheckForResult` (i.e. in
  their `UpdateAfterChildren`, after `SliderInputManager.Update` in the same step):
  repeat/tick need `offset >= 0`; tail needs `offset >= -36` (`TAIL_LENIENCY`) **and the last tick/repeat judged**;
  all need `HeadCircle.Judged`. Then `Tracking ? HitForcefully (MaxResult) : (offset >= 0 ? MissForcefully : wait)`.
  So a tick is judged at the first step t ≥ tick time after the head is judged, using that step's tracking. The tail
  is hit if tracking at any step in [end-36, end], once the head and ticks are done.
- Head (`DrawableSliderHead.cs`): a DrawableHitCircle (same windows). Classic → result
  `IsHit ? LargeTickHit : LargeTickMiss` (:59-73). After its CheckForResult, `PostProcessHeadJudgement`
  (`SliderInputManager.cs:78-140`): if the head was hit and the mouse is within the expanded (2.4r) area, then for every
  unjudged nested object with StartTime ≤ now (in nested order), check if `objectPosition` (from `CurvePositionAt` of
  its time-progress) is within 2.4r of the mouse. If all are, HitForcefully them all, otherwise MissForcefully them
  all (stop at the first out-of-range one). Then `updateTracking(allInRange || IsMouseInFollowArea(false))`.
  If the head misses (auto-miss at `offset > meh`), pending ticks are then judged by current tracking.
- Slider own result (`DrawableSlider.cs:293-326`): once `TailCircle.Judged && t >= EndTime`. Classic: all nested
  hit → Great; none → Miss; fraction ≥ 0.5 → Ok else Meh. Non-classic: any nested hit → IgnoreHit else IgnoreMiss.
- `DrawableSlider.Tracking` (used by StrictTracking/Relax) is copied in `DrawableSlider.Update`, *before* its child
  `SliderInputManager.Update`, **so it lags one step** (:237-241).

Full result list (non-classic / classic):

| object | max | min |
|---|---|---|
| Slider head | Great/Ok/Meh (Miss) | / LargeTickHit (LargeTickMiss) |
| Tick, Repeat | LargeTickHit | LargeTickMiss |
| Tail | SliderTailHit / SmallTickHit | IgnoreMiss / SmallTickMiss (StrictTracking: LargeTickMiss) |
| Slider | IgnoreHit / Great,Ok,Meh | IgnoreMiss / Miss |
| Spinner | Great / Ok (>0.9), Meh (>0.75) | Miss |
| SpinnerTick | SmallBonus | IgnoreMiss |
| SpinnerBonusTick | LargeBonus | IgnoreMiss |

### 3.5 Spinners — `DrawableSpinner.cs`, `O/Skinning/Default/SpinnerRotationTracker.cs`, `SpinnerSpinHistory.cs`

- Spinner DHO is RelativeSizeAxes Both (the 512×384 playfield), Position = spinner position. The tracker is inside an
  `AspectContainer` (RelativeSizeAxes Y, square 384×384, centred). Angle uses `Parent.ToLocalSpace(mouse)`
  (`SpinnerRotationTracker.cs:57-61`).
- `DrawableSpinner.Update` (:279-307): `Tracking = IsSpinnableTime && !HasResult && (Left||Right held)`.
  `IsSpinnableTime = Start <= t < End` (:55).
- Tracker `Update` (:63-84, a later child in the same step): `thisAngle = -RadToDeg(MathF.Atan2(x - W/2, y - H/2))`
  (float), `delta = this - last` (0 for the first sample), normalised by ±360 once to [-180,180]. If Tracking →
  `AddRotation(delta)` (:93-111): `delta = (float)(delta * |GetTrueGameplayRate()|)` (**DT multiplies spin**),
  `History.ReportDelta(t, delta)`. `lastAngle` is updated every step that has a position, even when not tracking.
- `SpinnerSpinHistory.ReportDelta` (:64-120): float accumulators; a spin completes when the max |rotation| in the
  current spin reaches 360 (direction changes don't add). `TotalRotation = 360*completed + currentMax`.
- `UpdateAfterChildren` (:323-336): base → `UpdateResult(false)` → `CheckForResult` (:251-277): if t < Start return;
  record TimeCompleted; if t < End return; **trigger all unjudged ticks as Miss (IgnoreMiss)**, then the spinner result
  by `Progress = TotalRotation/360/SpinsRequired` (SpinsRequired 0 → 1). Then `updateBonusScore` (:340-370):
  `spins = (int)(TotalRotation/360)`. For each new full spin, the first unjudged tick → hit (SmallBonus then LargeBonus).
- **Rotation is sampled per step along the interpolated cursor path.** The total depends on the step schedule
  (float summation, plus ±180 normalisation when the path passes near the centre).
- SpunOut (`O/Mods/OsuModSpunOut.cs`): `HandleUserInput = false`. Per update it adds
  `RadToDeg((float)(elapsed/rate) * (float)(1.01*SpinsRequired/Duration) * MathF.PI * 2)`, which depends on the step schedule.

### 3.6 Input/actions

- `OsuAction` {LeftButton, RightButton, Smoke} (`O/OsuInputManager.cs:108-136`). Smoke is consumed by `SmokeContainer`
  (`O/UI/SmokeContainer.cs:35-47`) and ignored by every judgement path (tracking/spinner only accept L/R).
- Key counters (`RulesetInputManager.Attach`, :175-185) are passive.
- `OsuInputManager.AllowGameplayInputs/AllowUserCursorMovement` (Relax without replay / Autopilot).

---------------------------------------------------------------------------------------------------

## 4. Scoring and health

### 4.1 ScoreProcessor — `G/Rulesets/Scoring/ScoreProcessor.cs`, `O/Scoring/OsuScoreProcessor.cs`

- `ApplyBeatmap` (:225-237; `JudgementProcessor.cs:187-192`): Reset; `SimulateAutoplay` (every object, nested first
  then parent, recursively, `JudgementProcessor.cs:276-316`; result = MaxResult) → stores maxima
  (`maximumBaseScore`, `maximumComboPortion`, `maximumAccuracyJudgementCount`, MaximumResultCounts, MaxHits).
- `ApplyResultInternal` (:239-285): store ComboAtJudgement. **If `FailedAtJudgement && !ApplyNewJudgementsWhenFailed` → ignore.**
  Count `Statistics[type]++`. `IncreasesCombo` (`AffectsCombo && IsHit`: Miss..Perfect, LargeTick*, SliderTailHit,
  ComboBreak) → combo++; `BreaksCombo` → 0 (`HitResult.cs:171-200`). HighestCombo = max. If MaxResult affects
  accuracy: `currentMaxBase += base(Max)`, `accCount++`. If Type affects accuracy: `currentBase += base(Type)`. Bonus →
  `bonusPortion += base(Type)`; else scorable → `comboPortion += base(MaxResult) * ComboAfterJudgement^0.5`.
- Base scores (:346-381): SmallTickHit 10, LargeTickHit 30, SliderTailHit 150, Meh 50, Ok 100, Good 200,
  Great/Perfect 300, SmallBonus 10, LargeBonus 50, others 0. `AffectsAccuracy = IsScorable && !IsBonus`
  (IgnoreHit/IgnoreMiss are not scorable) (`HitResult.cs:208-345`).
- `updateScore` (:391-402): `Accuracy = curMax > 0 ? cur/curMax : 1`; `comboProgress = maxCombo>0 ? curCombo/maxCombo : 1`;
  `accProgress = accCount/maxAccCount`;
  `TotalScoreWithoutMods = (long)Math.Round(500000*Acc*comboProgress + 500000*Acc^5*accProgress + bonus)` (:427-432, Math.Pow);
  **`TotalScore = (long)Math.Round(TotalScoreWithoutMods * multiplier)`** (rounding twice, banker's).
- Rank (:559-573 + `OsuScoreProcessor.cs:19-33`): X if acc == 1, S ≥ .95, A ≥ .9, B ≥ .8, C ≥ .7, else D. S/X with
  any Miss → A. Mods `AdjustRank` (HD/FL → SH/XH). F on fail.
- `PopulateScore` (:480-499): Combo, MaxCombo = HighestCombo, Accuracy, Rank, Statistics (all types), MaximumStatistics,
  TotalScore(WithoutMods).

### 4.2 Mod multiplier — `G/Rulesets/Scoring/ScoreMultiplierCalculator.cs`, `O/Scoring/OsuScoreMultiplierCalculator{V1,V2}.cs`

- Live computation (`ScoreProcessor.updateScoreMultiplier` :418-425): `CreateScoreMultiplierCalculator(new
  ScoreMultiplierContext(Beatmap.BeatmapInfo.Difficulty))`, with no score so **always V2** (`O/OsuRuleset.cs:256-262`; V1 is
  only for stored scores with TotalScoreVersion < 30000017).
- `CalculateFor` (:59-90): mods keyed by concrete type; if >1 mod, apply matching **Combination** rules in
  registration order (removing their types), then **Single** multipliers for the remaining types; unknown mods → ×1.
- V2 values (`OsuScoreMultiplierCalculatorV2.cs:14-198`): EZ `max(0.4, 0.8 - 0.1*max(0, retries-2))`; NF 0.5;
  HT/DC `(int)(s*20)/20.0*1.4 - 0.5`; HR 1.09; DT/NC `v=(int)(s*10)/10.0; (v-1)*0.46 + 1 - (v∉{1.0,1.5} ? 0.01 : 0)`;
  HD+BL / TC+BL → 1.24; HD+{WG,GR,DF,RP,DP} → hidden(timing=true) (×deflate for DF); HD alone `1.04 - 0.02*OnlyFadeApproach -
  0.02*timingInfo`; TC 1.02; FL+FR `1 + (fl-1)/2`; FL `clamp(1.2 - 0.2*(size-1), 1.02, 1.2)`, divided towards 1 by 5 if not
  combo-based; BL 1.24; TP 0.01; DA product of `max(0.1, 1 - |Δ|*0.5)` per CS/HP/OD/AR vs **unmodded difficulty**, min 0.1;
  CL `ClassicNoteLock ? 0.985 : 0.96`; RD 0.7; RX 0.1; AP 0.1; SO 0.95; DF `1 - max(0, 0.02*(start - 2))`;
  WU/WD `0.8*mult(min) + 0.2*mult(max)`; AD 0.7; MG `0.7 - 0.6*strength`; AS 0.1; SY 0.99; everything else 1.
- Classic display score (UI only): `round((n²*32.57 + 100000) * total / 1e6)` with n = max basic judgements
  (`G/Scoring/Legacy/ScoreInfoExtensions.cs:27-57`).

### 4.3 Health and fail — `G/Rulesets/Scoring/HealthProcessor.cs`, `DrainingHealthProcessor.cs`, `O/Scoring/OsuHealthProcessor.cs`, `LegacyDrainingHealthProcessor.cs`, `O/Scoring/OsuLegacyHealthProcessor.cs`

- Selection (`Player.cs:266-268`): first mod implementing `IApplicableHealthProcessor` (only `OsuModClassic` with
  `ClassicHealth`, default **true**) → `OsuLegacyHealthProcessor`, else `OsuHealthProcessor(drainStartTime =
  first object StartTime)`. Both then get `ApplyBeatmap(playable)`.
- `HealthProcessor.ApplyResultInternal` (:389-401): `result.FailedAtJudgement = HasFailed`; if failed return;
  `Health += GetHealthIncreaseFor(result)` (BindableDouble clamped [0,1]); `if (CheckDefaultFailCondition ||
  any FailConditions) TriggerFailure()`. Default fail = `Precision.AlmostBigger(0, Health)` i.e. `0 > Health - 1e-7`
  (:424). Draining: ignore if the judgement max is bonus or the type is IgnoreHit (`DrainingHealthProcessor.cs:145-151`).
  `TriggerFailure` (:380-387): `HasFailed = Failed?.Invoke() != false`.
- **Fail is only checked when a judgement is applied.** Drain alone can hold health at 0 until the next judgement.
- Drain (`DrainingHealthProcessor.Update` :85-98): skipped entirely if `Time.Current` is inside a no-drain period
  (break, from the last object end before the break to the first start after it). Otherwise
  `Health -= DrainRate * (clamp(t, drainStart, lastEnd) - clamp(t - elapsed, drainStart, lastEnd))`. **This depends on the
  step schedule** (whole steps counted or skipped by their end time).
- DrainRate: `OsuHealthProcessor` → `DrainingHealthProcessor.ComputeDrainRate` (:163-213), a binary search over
  simulated health increases (recorded at `EndTime + TimeOffset`) to reach the target minimum
  `DR(HP, 0.99, 0.9, 0.4)` within 0.01. `OsuLegacyHealthProcessor` → `LegacyDrainingHealthProcessor.ComputeDrainRate`
  (:46-158) (stable algorithm with testDrop 0.00025, ×0.96/×0.94, `HpMultiplierNormal *= 1.01`). Nested enumeration
  excludes spinner bonus ticks (`OsuLegacyHealthProcessor.cs:22-38`).
- Increases. Osu (`OsuHealthProcessor.cs:77-126`): SmallTickMiss/LargeTickMiss `DR(HP,-0.02,-0.075,-0.14)`, Miss
  `DR(HP,-0.03,-0.125,-0.2)`, SmallTickHit 0.02, SliderTailHit/LargeTickHit 0.015 (tick) or 0.02 (head/tail/repeat),
  Meh 0.002, Ok 0.011, Great 0.03, SmallBonus 0.0085, LargeBonus 0.01, else `Judgement.HealthIncreaseFor` (IgnoreHit
  → 0). **Combo-end bonus** (:23-69, not during simulation): on objects with combo info (top-level; nested ones have
  NewCombo/LastInCombo false), NewCombo resets the state to Perfect. LargeTickMiss/Ok → Good, Meh/Miss → None, tail
  not hit → Good. If `LastInCombo && Type.IsHit()` → +0.07/+0.05/+0.03. Legacy: same table, positive values ×
  `HpMultiplierNormal`, no combo bonus.
- Fail conditions from mods (`IApplicableToHealthProcessor.ApplyToHealthProcessor`, Player :428-430): SD
  (`AffectsCombo && !IsHit`, plus tail miss if `FailOnSliderTail`), PF (any result ≠ max among accuracy/combo-relevant),
  TP (as SD), AC (triggers on `ScoreProcessor.Accuracy`/`MaximumAccuracy` dropping below the minimum, inside
  ScoreProcessor.ApplyResult, so the triggering judgement is already counted).
- Player fail handling: `HealthProcessor.Failed += onFail` (`Player.cs:957-967`): `CheckModsAllowFailure` = all
  `IApplicableFailOverride.PerformFail()` (NF → false; EZ lives → refill and false; SD/PF/AC → true). Then PerformFail →
  `ScoreProcessor.FailScore` (rank F), scheduled. Every judgement after the fail has `FailedAtJudgement = true` and
  is ignored by ScoreProcessor. Stored statistics are frozen at the fail.
  **`ReplayPlayer.CheckModsAllowFailure` returns false until `GameplayClock.CurrentTime >= lastFrameTime`**
  (`ReplayPlayer.cs:55-68`), so failing replays keep playing in lazer playback. `ReplayPlayer.PerformFail` (:240-245) only marks it.
- Completion: `JudgementProcessor.HasCompleted = JudgedHits == MaxHits && lastResult.TimeAbsolute < now` (:332-341).

---------------------------------------------------------------------------------------------------

## 5. Mods in this version (osu! ruleset: `O/OsuRuleset.cs:179-254`)

Legend: **D** = difficulty/beatmap, **T** = timing rate, **H** = hit-object transform (beatmap level), **P** = runtime
position/scale of drawables (affects hit tests!), **I** = input, **F** = fail, **S** = score multiplier only,
**V** = visual only (no effect on results if the canonical config is used). Randomness is noted where present.

| Mod (class) | Interfaces / effect | Settings | Class |
|---|---|---|---|
| EZ `OsuModEasy` | difficulty ×0.5; extra lives via PerformFail | Retries int 2 [0,10] | D F S |
| NF `OsuModNoFail` | PerformFail false | – | F S |
| HT/DC | rate (`ApplyToTrack`), affects `GetTrueGameplayRate` (spinner) | SpeedChange 0.75 [0.5,0.99] p0.01; HT AdjustPitch | T S |
| HR | difficulty, vertical flip | – | D H S |
| SD | fail condition | FailOnSliderTail bool, Restart | F |
| PF | fail condition | Restart (default true) | F |
| DT/NC | rate 1.5 [1.01,2] p0.01 (DT AdjustPitch). NC adds beat samples | | T S |
| HD | `ApplyToBeatmap` TimeFadeIn = 0.4·preempt (non-sliders); fades DHOs (input unaffected, DHO `PropagatePositionalInputSubTree => HandleUserInput`); AdjustRank | OnlyFadeApproachCircles | V S |
| TC Traceable | visual | – | V S |
| FL | visual; AdjustRank | FollowDelay, SizeMultiplier, ComboBasedSize | V S |
| BL Blinds | visual, reads health | – | V S |
| ST StrictTracking | replaces sliders (`StrictTrackingSlider` **does not copy `GenerateTicks`**, so NaN-SV sliders gain ticks; `O/Mods/OsuModStrictTracking.cs:101-172`); tail min LargeTickMiss; tail missed when `DrawableSlider.Tracking` (lagged) becomes false after StartTime (:34-54) | – | H D |
| AC AccuracyChallenge | fail on accuracy (`G/Rulesets/Mods/ModAccuracyChallenge.cs:69-89`) | MinimumAccuracy 0.9 [0.6,0.999] p0.001; mode Standard/MaximumAchievable; Restart | F |
| TP TargetPractice | AR×0.5; **regenerates the beatmap as circles on beats** (`System.Random(Seed)`, `Seed ??= RNG.Next()`); SD-like fail; circles scale 0.5→1 during preempt (**P**) | Seed int?, Metronome | D H F P S |
| DA | difficulty override | CS/HP/OD/AR (DifficultyBindable p0.1), ExtendedLimits | D S |
| CL Classic | `ClassicSliderBehaviour`, LegacyHitPolicy, head CanBeHit, legacy health, early fade (visual), tail sample (audio) | NoSliderHeadAccuracy, ClassicNoteLock, AlwaysPlayTailSample, FadeHitCircleEarly, ClassicHealth (all true) | H I F S |
| RD Random | repositions objects (`System.Random((int)Seed)`, `OsuHitObjectGenerationUtils`), random slider flips | Seed int?, AngleSharpness float 7 | H S |
| MR Mirror | reflection | Reflection enum | H |
| AL/SG Alternate/SingleTap | `InputBlockingMod`: intercept presses outside non-gameplay periods (`[−∞, first.Start − meh − 1]` and each break up to the next object's valid time); blocked presses still count as held (`O/Mods/InputBlockingMod.cs:43-118`) | – | I |
| AT/CN Autoplay/Cinema | generate a replay (`OsuAutoGenerator`); not for user replays | – | – |
| RX Relax | lazer replay: no-op (presses are in the replay). **Stable replay: synthesises presses in `Playfield.Update`** from hover/tracking (`O/Mods/OsuModRelax.cs:73-156`, `LegacyReplayPressHandler` :186-205, KEY_UP_DELAY from AutoGenerator); needs `ApplyToPlayer` | – | I S |
| AP Autopilot | moves the cursor from generated autoplay frames by proximity (`O/Mods/OsuModAutopilot.cs:43-69`); LegacyHitPolicy range 200 | – | I S |
| SO SpunOut | automatic spin per step | – | I S |
| TR Transform | moves circles/sliders from an offset to the origin during preempt (until StartTime) via transforms (**P**: early hits see moved positions) | – | P |
| WG Wiggle | random moves (`new Random((int)StartTime)`) every 100 ms during preempt **and during slider/spinner duration** (**P**) | Strength 1 [0.1,2] p0.1 | P |
| SI SpinIn | rotation/scale (scale x2→1, y0→1) during preempt (**P**) | – | P |
| GR/DF Grow/Deflate | DHO scale StartScale → 1 over preempt (**P**: hit radius scaled for early hits; slider follow area during preempt) | StartScale (GR 0.5, DF 2) | P S |
| WU/WD | time-varying rate (`ModTimeRamp`, `Update` sets SpeedChange from `Clock.CurrentTime`, rounded 0.01) | InitialRate, FinalRate, AdjustPitch | T S |
| BR BarrelRoll | rotates the playfield adjustment container (`G/Rulesets/Mods/ModBarrelRoll.cs:57-61`), so screen-space transforms change every step. Input positions are computed with the previous step's rotation (**P**, float) | SpinSpeed, Direction | P |
| AD ApproachDifferent | approach circle visuals | Scale, Style | V S |
| MU Muted | audio | | V |
| NS NoScope | cursor alpha | HiddenComboCount | V |
| MG/RP Magnetised/Repel | move DHOs towards/away from the cursor with `DampContinuously(..., ElapsedFrameTime)` in `Update(playfield)` (**P, step-schedule-dependent**) | strength 0.5 [0.05,1] p0.05 | P S |
| AS AdaptiveSpeed | rate adjusts from hit timing, damped per frame (T, schedule-dependent) | InitialRate, AdjustPitch | T S |
| FR FreezeFrame | TimePreempt += time since last new combo (lifetime, approach visuals) | – | D(lifetime) |
| BU Bubbles | visual | – | V |
| SY Synesthesia | colours | – | V S |
| DP Depth | per-step position/scale from a z-model (`O/Mods/OsuModDepth.cs:73-161`) (**P**) | MaxDepth, ShowApproachCircles | P |
| BM Bloom | cursor size | | V |
| TD TouchDevice | marker only (also legacy bit) | – | – |
| SV2 ScoreV2 | marker only (not user playable) | – | – |

Notes:
- `ModWithVisibilityAdjustment` (base of HD/TC/TP/GR/DF/SI/TR/WG/DP) reads **user config
  `IncreaseFirstObjectVisibility` (default true)** and applies "increased visibility" (often a no-op) to the first object
  (`G/Rulesets/Mods/ModWithVisibilityAdjustment.cs:27,51-58,81`). This affects P-class behaviour of the first object.
- `IApplicableToDrawableHitObject` mods are applied per DHO on apply (`Playfield.cs:414-415`, `DrawableRuleset.cs:216-222`).
- Rates do not change hit windows or object times (all gameplay time). Rates do affect spinner rotation, AS dynamics
  and real-time-to-gameplay-time mapping (i.e. the step schedule in live play).

---------------------------------------------------------------------------------------------------

## 6. What must be emulated from the drawable/UI layer (headless fidelity checklist)

1. **Step schedule** (FSC + replay handler + reference clock), including `GameplayStartTime` jumping, one-frame-per-step
   snapping, the 16.67 ms cap, the 20 ms threshold (`1.2f`), and the first-consumption seek. *Not unique in lazer itself.*
2. **Interpolated cursor** between frames (float lerp) at every step. Buttons from the current frame only.
3. **Per-step phase order** (§3.1): processors drain → input (hover, MouseMove, releases, presses) → mods
   `IUpdatableByPlayfield` → lifetime (alive set) → DHO transforms/Update/children/UpdateAfterChildren.
   Hit tests at input time use the previous step's drawable state.
4. **Alive set / lifetimes**: `StartTime - TimePreempt` (AR- and FreezeFrame-dependent). Notelock (`AliveObjects`), the input
   queue and LegacyHitPolicy all operate on alive DHOs. Nested lifetimes (tick/repeat preempt) only need to be ≤ judgement time.
5. **Input queue order and consumption** (earlier object first; ties: reverse ChildID / dictionary order); a hovered
   receptor consumes the press even when the policy shakes/ignores; Classic head `CanBeHit` override.
6. **Screen-space round trips**: replay pos → `HitObjectContainer.ToScreenSpace` (float matrices built from window size,
   `DrawSizePreservingFillContainer`, `ScalingContainer(ScalingMode.Gameplay)` user scaling settings, the
   `OsuPlayfieldAdjustmentContainer` 0.8 size, 4:3 fit, scale `ChildSize.X/512`, `+8*scale` y shift when
   `AlignWithStoryboard` (`O/UI/OsuPlayfieldAdjustmentContainer.cs:115-165`), BarrelRoll rotation) → inverse into
   `HitReceptor`/`DrawableSlider` (+ skin-dependent `OriginPosition`)/spinner `AspectContainer` local spaces. Exact math
   reduces to the ideal formulas. Float rounding only matters at boundaries, but **it depends on window resolution, UI
   scale, skin path radius and snaking settings**.
7. **Transforms** (Grow/Deflate/SpinIn/Transform/Wiggle/TP scale) are evaluated at step times with easing.
   **Update-driven positions** (Magnetised/Repel/Depth) use ElapsedFrameTime damping.
8. **Spinner** sampling and float accumulation. SpunOut uses elapsed time.
9. **Health drain** per step with break check at step end. Fail only at judgements. Live vs ReplayPlayer fail semantics.
10. **Event ordering** of forced misses vs the causing hit (§3.1) and nested-before-parent judgements.
11. **Relax on stable replays** (synthesised presses in Playfield.Update, after input phase → they take effect in the
    *same* step via direct TriggerPressed), **Autopilot** cursor injection.
12. Platform: CoreCLR float/double semantics (IEEE, no FMA contraction), `System.Random` (legacy seeded algorithm),
    glibc libm for transcendental functions, `decimal` rounding in bindables, banker's `Math.Round`.

---------------------------------------------------------------------------------------------------

## 7. How lazer runs replays headlessly; oracle recommendation

### 7.1 Existing infrastructure

- `G/Tests/Visual/ReplayStabilityTestScene.cs` and `LegacyReplayPlaybackTestScene.cs` (`[HeadlessTest]`): push a
  `ReplayPlayer(score)` in a `ScreenTestScene`, subscribe to `GameplayState.ScoreProcessor.NewJudgement`, wait until
  `HasCompleted`. Used by `osu.Game.Rulesets.Osu.Tests/TestSceneReplayStability.cs`, `TestSceneSliderInput.cs`,
  `TestSceneSpinnerInput.cs`, `TestSceneStartTimeOrderedHitPolicy.cs`, `TestSceneLegacyHitPolicy.cs`, etc.
- Test time source: `OsuTestScene.ClockBackedTestWorkingBeatmap` with `TrackVirtualManual` driven by the scene clock
  (`G/Tests/Visual/OsuTestScene.cs:393-520`). The track seek clamps negative times to 0.
  `HeadlessGameHost(realtime: false)` uses a `FastClock` that advances 1000/30 ms per host frame
  (`F/osu.Framework/Platform/HeadlessGameHost.cs:23,73-95,117-170`). FSC catch-up per host frame is bounded by
  **10 ms wall-clock**, so under CPU load the intermediate step times of these tests can vary between runs.
- No headless "replay → score" tool exists in lazer or osu-tools. osu-tools/StandardisedScoreMigrationTools work from
  statistics, not replays.

### 7.2 Recommended oracle harness (minimal deviation, deterministic)

Build a console app (`oracle/`) referencing `osu.Game` + `osu.Game.Rulesets.Osu` at the pinned commit (or the matching
`ppy.osu.Game*` NuGet packages, if version 2026.1005.0 is published, to avoid building lazer). Run inside
`HeadlessGameHost(realtime: false)` with a small `OsuGameBase`-derived game (needed for DI: config, skins, audio
"No sound", rulesets). Don't use `ReplayPlayer`. Reproduce `Player.load` faithfully instead:

1. Decode `.osr` with a `LegacyScoreDecoder` subclass (`GetBeatmap` returns a `FlatWorkingBeatmap`/test working
   beatmap of the `.osu`; `GetRuleset` → `OsuRuleset`). This gives mods (+Classic for stable) and frames exactly
   as lazer. Deep-clone mods as Player does (`m.DeepClone()`, `Player.cs:228`).
2. `playable = working.GetPlayableBeatmap(osuRulesetInfo, mods)`. Then `drawableRuleset =
   ruleset.CreateDrawableRulesetWith(playable, mods)`, `ScoreProcessor` (`Mods.Value = mods; ApplyBeatmap`),
   `HealthProcessor` (IApplicableHealthProcessor first), put them in `drawableRuleset.FrameStableComponents` exactly as
   `Player.createGameplayComponents`. Wire `NewResult` → Health then Score (order!). Apply
   `IApplicableToScoreProcessor`/`IApplicableToHealthProcessor` on their LoadComplete, `IApplicableToPlayer`
   (OsuModRelax and ModEasyWithExtraLives ignore the Player argument; visual ones can be skipped), and
   `drawableRuleset.SetReplayScore(score)` (Player.PrepareReplay).
3. Provide a parent `IGameplayClock` (cached dependency) whose `CurrentTime` we set, `IsPaused=false`, `Rate` = 1 (or
   the mod rate), and `AdjustmentsFromMods` built by applying every `IApplicableToTrack`/`IApplicableToRate` mod (so
   `GetTrueGameplayRate` matches the game), and `StartTime`.
4. **Canonical step schedule (proposal, to be fixed in DECISIONS.md):** set the reference time to the gameplay start for
   the first frame (`min(GameplayStartTime, firstFrameTime)`), then to a target beyond the last frame/object end. The FSC
   then produces the deterministic sequence `t_{k+1} = SetFrame(min(target, t_k + 1000/60 if gap > 20 ms))`, i.e. "next
   replay frame or +16.67 ms, whichever is first". This holds regardless of how host frames split the catch-up loop,
   because the target is fixed. Alternative schedule "reference = each frame time in turn" is also deterministic.
   Implement both plus a dense 1 ms schedule to **measure schedule sensitivity**, and flag judgements that differ.
5. Fixed environment: window/draw size 1024×768 (playfield scale 1.6, keep `AlignWithStoryboard` shift), UI scale 1,
   default `OsuConfigManager`/`OsuRulesetConfigManager` (IncreaseFirstObjectVisibility = true, snaking on), default
   skin. Record these in the oracle output.
6. **Pass/fail:** implement live-Player semantics: `HealthProcessor.Failed += () => mods.OfType<IApplicableFailOverride>()
   .All(m => m.PerformFail())`, so the score freezes at the fail. Also report "ReplayPlayer semantics" (no fail before
   the last frame) for comparison with lazer UI behaviour.
7. Output JSON: per judgement in processor order {top-level index, nested index/type, HitResult, RawTime, TimeAbsolute,
   combo after, health after, failed flag}; final Statistics/MaximumStatistics, MaxCombo, Accuracy,
   TotalScore(WithoutMods), Rank, fail time. Optional debug trace of the step times, per-step tracking and spinner rotation.
8. Run until `ScoreProcessor.HasCompleted` (or fail), with a hard cap past the last object end + 400 ms.

This exercises the real decoder, converter, processors, DHO judgement, input routing and FSC code. The only parts the
harness supplies are the reference clock, the processor wiring, and the fail-override callback, each of which is
small and auditable. The formal model then has to reproduce §3.1's step semantics under the same canonical schedule.
