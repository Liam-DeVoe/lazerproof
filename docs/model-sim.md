# Gameplay simulation model (`model/OsuModel/Sim`, `model/OsuModel/Replay`)

The Lean model of what lazer's drawable/judgement layer and processors do with a playable beatmap, decoded
replay frames, mods and a step schedule (docs/model-architecture.md: `Sim.run env pb rep mods steps`).
All arithmetic uses `OsuModel.Net` (bit-exact .NET float32/float64, same op order as the C#).

## Files

| file | content |
|---|---|
| `Sim/Basic.lean` | `Vec2`, `Mat3` (osuTK), `MatrixExtensions` ops, `DrawInfo.ApplyTransform`, `Vector2Extensions.Transform`, `HitResult` + extension predicates, `Precision.AlmostEquals`, C# `% 1` |
| `Sim/Playable.lean` | `Playable` (the sim's input interface; every field the drawable layer reads) + loader for the oracle's `--dump-playable` JSON (raw bits) |
| `Replay/Frames.lean` | frame text → `OsuReplayFrame`s (`LegacyScoreDecoder.readLegacyReplay`, stable fixups, backwards-frame filter, `FromLegacy`) |
| `Sim/Schedule.lean` | FSC stepping (`applyFrameStability` + `SetFrameFromTime`), reference schedules catchup/perframe/dense1ms; mirrors `oracle/Schedule.cs` |
| `Sim/Geometry.lean` | `Env` (HitObjectContainer DrawInfo, argon path radius, HOC size), DrawInfo chains for HitReceptor / slider head / DrawableSlider / spinner AspectContainer, `CompositeDrawable.Contains` (rounded corners), SliderPath `PositionAt`/`CurvePositionAt`, follow-area test |
| `Sim/State.lean` | per-object and global state, `Config` (mods), `Ctx` |
| `Sim/Step.lean` | the frame-stable step (§3.1): processors → input → lifetimes → DHO updates; judgement application + result chain; hit policies; circles, slider heads/ticks/repeats/tails, sliders, spinners |
| `Sim/Scoring.lean` | ScoreProcessor (combo, statistics, accuracy, standardised score, rank, maxima by simulated autoplay), OsuHealthProcessor / OsuLegacyHealthProcessor (drain-rate searches, per-step drain, break periods, combo-end bonus, fail), score multiplier (NF, CL) |
| `SimTest/Main.lean` | `simtest` executable: (playable dump, frame text, env, mods, schedule) → oracle-like JSON (times/health/accuracy as hex bits) |

Harness: `difftest/sim_diff.py` (oracle batch + simtest + judgement-by-judgement compare), `difftest/osr.py`
(.osr read/write; LZMA = trusted boundary), `difftest/synth.py` (synthetic maps/replays), `difftest/real_jobs.py`
(crawled corpus), `difftest/env-1024x768.json` (environment data from `oracle --dump-env`).
Oracle additions (`oracle/Dump.cs`): `--dump-playable PATH`, `--dump-env PATH` (batch: directories, `<job index>.json`);
default outputs are byte-identical to before (checked on the 5-replay corpus).

## Step semantics (one frame-stable step at time t, `Sim.stepOnce`)

1. **Processors** (FrameStableComponents): `JudgementProcessor.Update` (HasCompleted), `DrainingHealthProcessor.Update`
   (drain `DrainRate * (clamp(t) - clamp(t - Elapsed))` unless in a no-drain period; `Elapsed = t - t_prev`, 0 in step 0).
2. **Input** (`InputManager.Update`): replay position (float lerp of the two frames around the handler time) →
   `HitObjectContainer.ToScreenSpace` (step 0 uses the pre-layout HOC matrix, see Env) → if the position changed:
   MouseMove (sliders' `screenSpaceMousePosition`, spinners' tracker position in AspectContainer space) and hover
   update; then `ReplayState.Apply`: releases, then presses (`KeyBindingContainer` Unique mode: an action already
   held is not re-propagated); presses go to HitReceptors in input-queue order (earliest start first, ties smaller
   ChildID first); a receptor handles the press iff `CanBeHit()` and `IsHovered` (even if the policy rejects the hit);
   high-frequency MouseMove to sliders; hover update if not yet done this step.
3. Playfield mods: none in scope.
4. **Lifetimes** (`LifetimeEntryManager.Update`): future→alive in (LifetimeStart, ChildId) order (DHO apply: Idle state,
   receptor/slider/spinner state reset, Idle lifetime from hit-state transforms), then deaths in activeEntries order
   (`OnKilled` → `UpdateResult(false)`), alive dictionary with .NET `Dictionary` free-list reuse (AliveObjects tie order).
5. **DHO updates** in HitObjectContainer child order (later start first; ties larger ChildID first). Slider subtree:
   SliderInputManager.Update (tracking) → ticks → repeats → tail → head (lifetime check, auto-miss, PostProcessHeadJudgement)
   → slider result. Spinner: Tracking → rotation tracker (atan2f, ±180 normalisation, SpinnerSpinHistory) →
   CheckForResult (end: miss remaining ticks, result by progress) → bonus ticks.

`applyResult` = `DrawableHitObject.ApplyResult`: result + RawTime, lifetime from the hit-state transforms
(`LatestTransformEndTime` formula incl. the `+1`), then the result chain: hit policy `HandleHit` (StartTimeOrdered
forced misses recurse and reach the processors **before** the causing hit) → HealthProcessor → ScoreProcessor.
Both fail semantics (live Player / ReplayPlayer gate `t >= lastFrameTime`) are run side by side.

## Mods (M5, M6) — `Sim/Mods.lean` (`Config.ofMods`), `Sim/AutoGen.lean`, hooks in `Sim/Step.lean`/`Sim/Scoring.lean`

Mod list order is significant everywhere (lazer applies any combination, in list order; the oracle's `--replace-mods`
gives exactly the list). `Config.ofMods` walks the list once and builds:

* **Rate** (`Config.trueRate`): `GetTrueGameplayRate = 1 * AggregateFrequency * AggregateTempo`; each `IApplicableToTrack`
  mod adds its bindables in list order and `AggregateBindable` folds `1 * 1 * v1 * v2 …`. HT/DT add `SpeedChange` to
  Frequency (adjust_pitch) or Tempo; NC/DC add `freqAdjust = Default` (1.5 / 0.75) then `tempoAdjust = s / Default`
  (so NC 1.51 ≠ DT 1.51 in the last bit for some s); WU/WD/AS add a time-varying `SpeedChange`. Used by
  `SpinnerRotationTracker.AddRotation` (`(float)(delta * |rate|)`) and SpunOut.
* **Time-varying rate** (`IUpdatableByPlayfield`, phase P3 = `Playfield.Update`, before lifetimes/DHOs, list order):
  TimeRamp `SpeedChange = BindableDouble{Precision 0.01}.Value = ApplyToRate(t)` (`Math.Round(ramp, 2)`), initial value
  `ApplyToRate(+∞)` (FinalRate.TriggerChange in ApplyToTrack); AdaptiveSpeed `SpeedChange = clamp(DampContinuously(…,
  targetRate, 50, Elapsed))` plus its `OnNewResult` handler (runs **first** in the result chain — mod handlers are
  subscribed when the pooled DHO is created, before the HitObjectContainer's — on circles/heads with a preceding end time;
  `recentRates` window of 8, consistency, `Lerp`).
* **Fail** (`Step.triggerFailure`): `TriggerFailure` → (ReplayPlayer gate) → `All(PerformFail)` over
  `IApplicableFailOverride`s in list order, short-circuit: NF/CN veto, EZ spends a life and refills `Health := MaxValue`
  (the bound bindable), `ModFailCondition` allows. Fail conditions: SD (+ fail_on_slider_tail), PF (relevance rule),
  TP (SD-like). AC: fired from `ScoreProcessor.updateScore` on a *change* of `Accuracy` (Standard, set first) /
  `MaximumAccuracy` below `MinimumAccuracy` — after the result was counted; the recorded health is the value after both
  processors (EZ refill by an AC trigger is visible on that judgement).
* **Rank**: `ScoreProcessor.rank` is only recomputed on `Accuracy.ValueChanged` (an exact change), then
  `AdjustRank` of every `IApplicableToScoreProcessor` (HD/FL: X→XH, S→SH); initial rank = adjusted X.
* **Score multiplier**: `OsuScoreMultiplierCalculatorV2` with `ScoreMultiplierCalculator.CalculateFor` (combinations in
  registration order, then singles of the remaining types in list order; float settings subtract in float
  (`size_multiplier - 1`, `start_scale - 2`); DA uses the unmodded `BeatmapInfo.Difficulty`). Also checked against the
  oracle's `total_score = round(total_score_without_mods * multiplier)` on every job.
* **Classic**: `classic_note_lock` → `LegacyHitPolicy(400 - (AP ? 200 : 0))` + head `CanBeHit = !slider.AllJudged`;
  `classic_health` → legacy health processor; `no_slider_head_accuracy` is beatmap-side; tail sample / early fade visual.
* **Relax** (legacy replays only; `--lazer-replay` makes it a no-op): P3, alive objects by start time, `break` at
  `t < start - 12`, hover flags of this step's P2, `IsMouseInFollowArea(DrawableSlider.Tracking)` — the bindable copied in
  the previous step's `DrawableSlider.Update` (model: `OState.drawableTracking`), presses/releases via the
  KeyBindingContainer (do not touch the replay-state diff).
* **Autopilot**: `OsuAutoGenerator` (literal, including `List<OsuAction>` aliasing: `{ Actions = lastFrame.Actions }` shares
  the list and later `Clear(); Add(a)` mutates every frame sharing it), at most one frame per step injected as
  `MousePositionAbsoluteInput` in P3 (immediate MouseMove + hover); the next P2 re-applies the replay position.
* **Alternate/SingleTap**: interceptors are the last children of the KeyBindingInputManager, so they see every press
  first (last-added first); a blocked action stays in `PressedActions`; `PeriodTracker` state shared by P2 and P3.
* **SpunOut**: spinner `HandleUserInput = false` (no MouseMove to the tracker, no Tracking assignment), `OnUpdate`:
  `Tracking = IsSpinnableTime`, `deg = RadiansToDegrees((float)(Elapsed / Clock.Rate) * (float)(1.01*spins/duration) *
  π * 2)`; `Clock.Rate` is the FSC rate set at step start (before this step's P3), the rotation uses the live rate.
* **StrictTracking** runtime: `DrawableSlider.Tracking` true→false (in `DrawableSlider.Update`, before children) misses the
  strict-tracking tail unless the slider is judged or `t < StartTime`. Found: a slider can then be judged before its
  head, so judged sliders must keep updating their subtree (the head still auto-misses).
* TD, SV2: markers (multiplier 1). AT/CN: rejected by the oracle (they replace the replay) — out of scope.

## M7: drawables, transforms, pools — `Sim/Transforms.lean`, `Inst`/pools in `Sim/State.lean`, `updateState`/`customState`/subtree updates in `Sim/Step.lean`

* **Transform engine** (`Sim/Transforms.lean`): literal `Transformable` + `TargetGroupingTransformTracker` with
  `RemoveCompletedTransforms = false` (DHOs): per-member trackers (Position, Scale, Rotation, Alpha), `(StartTime, ID)`
  order, `AddTransform` drops later same-member transforms and applies immediately when `Start < now || End <= now`
  (forced rewind if `Start <= now`), the rewind branch, `ReadIntoStartValue` on first application, property setters keep
  the old value when equal, `TransformSequence` (`Then`, `Delay`, `Append` re-rounds `now + (currentTime - now)`),
  `LatestTransformEndTime` (+1), `clearExistingStateTransforms` (rewind to `double.MinValue`, then clear).
* **DHO state updates**: `UpdateState` = clear → `UpdateInitialTransforms` at `Start - Preempt` (`FadeInFromZero`, slider
  body `FadeInFromZero(TimeFadeIn)`) → hit-state transforms at `Result.TimeAbsolute ?? EndTime` → `Expire` (lifetime end
  now computed by the engine, not a closed form) → `ApplyCustomUpdateState` handlers: own list, then for a nested head
  the parent's list via the forwarder (two passes). Called from `Apply` only for re-used (loaded) instances, from
  `LoadComplete` on the first `UpdateSubTree` of a *fresh* instance (`LoadState.Ready` at Apply), and on every judgement.
* **Pools** (`OsuPlayfield.cs:141-164`, `DrawablePool.cs`): LIFO stacks of instances (circle 20/100, slider 20/100,
  head 20/100, spinner 2/20 prewarmed/max). Per-instance state survives re-use: members after the free-time clear, bound
  `PositionBindable`/`StackHeightBindable`/`ScaleBindable` copies (their `ValueChanged` fires only on change, e.g.
  `Position = StackedPosition` is not re-applied for an identical position), `LoadComplete` done, and for sliders `Size`,
  `OriginPosition`, `Tracking`, the body's last `Refresh` and its pending scheduled refresh.
* **Presence** (`Drawable.IsPresent`, DHO override `|| (Idle && now >= LifetimeStart)`): a non-present DHO gets
  `UpdateTransforms` but no `Update`/children/`UpdateAfterChildren` (`Drawable.cs:469-498`, `CompositeDrawable.cs:907-950`):
  a judged slider stops updating its (possibly unjudged, StrictTracking) head once faded. **Input is not affected**:
  `DrawableHitObject.PropagatePositionalInputSubTree/PropagateNonPositionalInputSubTree => HandleUserInput`
  (`DrawableHitObject.cs:74-78`) override the framework's `IsPresent &&` rule, so a faded (alpha 0) judged head stays
  hovered and keeps consuming presses (Classic) until its lifetime ends — also under HD. (docs/mods/transform-mods.md
  §1.7/§8.1 claim the opposite; found by a Relax mismatch and confirmed with the oracle's DHO dump: the dead-alpha head
  was still hovered.)
* **G1 (pooled slider geometry)**: on apply the body refresh is scheduled (`pathVersion` change → `Scheduler.AddOnce`), an
  immediate refresh happens only if `ScaleBindable` changed (`PathRadius` setter). The scheduler runs only while the body
  (`SkinnableDrawable`, alpha from `FadeInFromZero(TimeFadeIn)`) is present, i.e. not in a step at exactly the fade start.
  `DrawableSlider.UpdateAfterChildren` copies the body's `Size`/`PathOffset` every step. Observed with the oracle's
  `ORACLE_DHO_STATES` dump: a re-used instance alive at exactly `Start - Preempt` keeps the previous slider's
  `Size`/`OriginPosition` for one step.
* **Mods** (`customState`): GR/DF (`ScaleTo(start).Then().ScaleTo(1, preempt, OutSine)`), SI (rotation 360→0 and scale
  (2,0)→1 InOutSine on circles *and heads*, slider scale 0→1), TP (scale 0.5 → 1 linear), TR (`MoveToOffset` + `MoveTo`,
  global `theta`), WG (`System.Random((int)StartTime)` 100 ms segments from the position read at handler time — the head's
  second pass reads the moved position), HD (DHO alpha fades for circles/heads/spinners, slider body), Classic early fade;
  first-object rule (`IncreaseFirstObjectVisibility`, HD/TC skip spinners). P3: DP (Position/Scale from time), MG/RP
  (damped Position towards/away from the cursor `ActiveCursor.DrawPosition`, slider ball offset after the head result).

### M7 results (catchup; ns1 = 40 synthetic slider maps without spinners, sp4 = with spinners)

| pool | corpus | jobs | sensitivity (`sim_mutate`) |
|---|---|---|---|
| M7gr (GR/DF + CL/NF) | ns1 | 40/40 | GR 22/40, DF 13/22 |
| M7si (SI) | ns1 | 40/40 | 31/40 |
| M7hd (HD) | ns1 | 40/40 | — (no sim effect besides multiplier/rank) |
| M7wg (WG, incl. head double pass) | ns1 | 40/40 | 39/40 |
| M7tr (TR) | ns1 | 40/40 (after the `IsLoaded` fix) | 38/40 |
| M7dp / M7mg / M7rp | ns1 | 40/40 each | 40/40 each |
| M7tp (TP: regenerated beats, scale tween) | ns1 | 40/40 | 23/40 |
| M7tr with spinners | sp4 30 | 30/30 (after spinner-tick DHOs + per-instance ArmedState) | |
| M7br (BR: recomposed ancestor chain) | ns1 | 40/40 | 17/40 |
| M7 mixed (random subsets of all M7 mods + CL/NF/HR/DT) | sp4 30 / ns1 40 perframe | 30/30 / 40/40 | |

G1 check: per-step `Size`/`OriginPosition` of every alive slider equal to the oracle dump (4461 slider-steps incl. the
stale first step of a re-used instance).

Regression after the M7 core (pools, engine lifetimes, G1, presence gating): all M5/M6 corpora above still 100%
(incl. 100 real M5).

Findings: (1) DHO input ignores presence (above); (3) `DrawableHitObject.State` lives on the pooled instance: a
re-used spinner tick that was never loaded keeps `Miss`, so its next miss is a no-op `UpdateState` (no handlers → no
Transform `theta` advance); (2) fresh pool instances are in `LoadState.Ready` (not `IsLoaded`)
at `Apply`, so their first `UpdateState` happens in `LoadComplete` only — reused instances get it in `Apply` (one pass
for nested heads, before the parent forwarder exists); this decides Transform's `theta` sequence.

## Totality (G17, 2026-10-21)

The simulation is total and has no silent defaults: no `xs[i]!`, `get!`, `back!`, `set!`, `insertIdx!`, `getD default`
or `exOr` fallback is left in `Sim/*`, `Replay/{Frames,Osr}`, `Eval.lean` or `SimTest/Main.lean`. Each access is either
proved in bounds (`xs[i]'h`, `for h : i in [0:n]`, `Vector` for transforms, structural `bsearchBy`, the size
invariant `ScoreSt.stat` on statistics) or goes through a rejecting accessor (`getA`/`setA`/`need` in `SimM`).
* `SimM = ReaderT Ctx (StateT St (Except String))`. `mkCtx`, `initState`, `runWith`, `simulate`, `steps`,
  `references`, `simulateSteps`, `mkHealthCfg`, `computeDrainRate`, `periodIsInAny`, `HealthSt.drain`,
  `AutoGen.generate`, `Config.trueRate`, `positionAt`, `curvePositionAt`, `sliderGeom`, `bodyRefresh` and `reportDelta`
  return `Except String`. `simtest` prints `{"error": …}` and `Eval` rejects with stage `"sim"`.
* Error classes: `internal: …` (an invariant violation, which should be unreachable), `malformed …` (the playable
  breaks an interface invariant, e.g. a slider without a head or tail), and `lazer would throw: …` (lazer itself throws
  here, so there is no lazer result):
  * an empty slider path (`Path.Vertices[0]`, SnakingSliderBody.cs:119);
  * `Math.Clamp` with inverted runtime bounds (drain bounds, frame-time interpolation);
  * `Math.Sign(NaN)` (ComputeDrainRate, SpinnerSpinHistory);
  * `new Period(start, end)` with `start >= end`, or `Objects.First(…)` with no match (InputBlockingMod.cs:52,55,
    PeriodTracker.cs:80).

  `Math.Clamp` calls with literal bounds use `clampK`, whose throwing branch is dead.
* No `partial def`s remain (D27, 2026-10-22: the mods-JSON reader `Sim/ModsJson.lean` is structural / nesting-fuel recursion,
  `Settings.assign` uses explicit fuel `assignFuel`).
* Gotcha found during the refactor: a nested `(← e)` inside `a && …` is hoisted before the whole statement, so it is
  evaluated even when `a` is false (`classicHead` evaluated `sliderData` for circles). The old code returned `default`
  there; the total code rejected the input, which exposed it. Use `if a then … else pure false`.
* Performance (2026-10-22): the first version of the refactor was up to 3x slower (evaltest 3.5 s -> 10.3 s on
  `5556876.osu` + `7737962141.osr`, 25k steps). There were two causes. (1) `modifyObj`/`modifyInst` read the state
  with `let s ← st` and wrote it back with `set { s with objs := ← setA s.objs … }`. `s.objs` is then shared with the
  monad state, so every update copied the whole array (O(objects) per update). They now do `checkIdx` (the range check
  of `getA`, same message) and then `modify fun s => { s with objs := s.objs.modify i f }`, which updates in place.
  (2) Without inlining, each `getA`/`ctx`/`st` returned an allocated `Except.ok (x, s)`, and `getA` also allocated an
  `Option`, on every access in the per-step loops over all objects (`updateHover`). The small accessors are now
  `@[inline]`, and `getA` uses `if h : i < a.size`. Meaning and signatures are unchanged. Pattern to avoid in hot
  paths: `let s ← st; … set { s with xs := (update of s.xs) }` for large arrays. Use a check, then `modify`.
* Regression after the refactor: model-only re-runs (`sim_diff --reuse-oracle`) of all 35 M5-M8 corpora (catchup,
  perframe, dense1ms; synthetic and real) gave 1451/1451 jobs and 259,098 judgements, with 0 PANICs and 0 rejections.
  `eval_diff run` on 40 stable replays gave 40/40.

## Correspondence (lazer `L/`, framework `F/`, paths as in docs/lazer-map.md)

| lazer / framework | Lean |
|---|---|
| `F/Extensions/MatrixExtensions/MatrixExtensions.cs` Translate/Scale From Left/Right | `Mat3.translateFromLeft` … `scaleFromRight` |
| `F/Graphics/DrawInfo.cs:31-71` `ApplyTransform` | `DrawInfo.applyTransform` |
| `F/Graphics/Drawable.cs:1603-1616` `computeDrawInfo`, `:1261` AnchorPosition, `:1159` OriginPosition | `childDrawInfo`, `centreOf` |
| `F/Graphics/Vector2Extensions.cs:27-31` Transform | `Mat3.transform` |
| `F/Graphics/Containers/CompositeDrawable.cs:1404-1414` Contains, `:1561` effectiveCornerRadius; `RectangleF.cs:347-353` | `receptorContains` |
| `O/Objects/Drawables/DrawableHitCircle.cs:60-104,266-308` tree, HitReceptor.OnPressed | `receptorFromDho`, `circleReceptor`, `propagatePress` |
| `O/Objects/Drawables/DrawableHitCircle.cs:137-173` CheckForResult; `DrawableSliderHead.cs:52-74` | `circleCheckForResult` |
| `L/osu.Game/Rulesets/Scoring/HitWindows.cs:83-109`, `O/Scoring/OsuHitWindows.cs` | `HitWindows.resultFor/canBeHit` |
| `O/UI/StartTimeOrderedHitPolicy.cs` | `checkHittable` (.startTimeOrdered), `handleHit`, `enumerateUpTo` |
| `O/UI/LegacyHitPolicy.cs:36-70` | `checkHittable` (.legacy) |
| `O/Mods/OsuModClassic.cs:52-99` (LegacyHitPolicy, head CanBeHit) | `Config.policy`, `receptorCanBeHit` |
| `L/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:726-770` ApplyResult/UpdateResult, `:698` OnKilled | `applyResult`, `circleUpdateResult`, `onKilled` |
| `DrawableHitObject.cs:472-495` UpdateState + `DrawableHitCircle.cs:177-205`, `DrawableSlider.cs:351-365`, `DrawableSpinner.cs:158-169`; `F/Graphics/Transforms/Transformable.cs:59-80`, `Drawable.cs:2553` Expire | `circleLifetimeEnd`, `sliderLifetimeEnd`, `latestTransformEndTime`, `seqStart` |
| `L/osu.Game/Rulesets/UI/HitObjectContainer.cs:24,179-187`; `Objects/Pooling/PooledDrawableWithLifetimeContainer.cs`; `F/Graphics/Performance/LifetimeEntryManager.cs` | `aliveObjects`, `inputOrder`, `updateOrder`, `lifetimeUpdate`, `becameAlive/Dead` |
| `O/UI/OsuPlayfield.cs:225-235` OsuHitObjectLifetimeEntry | `initState` lifetimes |
| `F/Input/InputManager.cs:459-513,657-707,959-975`; `MousePositionAbsoluteInput.cs` | `inputPhase`, `updateHover` |
| `L/osu.Game/Input/Handlers/ReplayInputHandler.cs:43-70`; `Rulesets/UI/RulesetInputManager.cs:81-101`; `F/Input/Bindings/KeyBindingContainer.cs:322-417` | `replayStateDiff`, `triggerPressed/Released` |
| `O/Replays/OsuFramedReplayInputHandler.cs:22-28`; `F/Utils/Interpolation.cs:352-362` | `replayPosition`, `interpolate` |
| `L/osu.Game/Rulesets/Replays/FramedReplayInputHandler.cs:127-165`; `Rulesets/UI/FrameStabilityContainer.cs:127-279`; `oracle/Schedule.cs` | `simulateSteps`, `references` |
| `O/UI/DrawableOsuRuleset.cs:82-91` GameplayStartTime | `gameplayStartTime` |
| `O/Objects/Drawables/SliderInputManager.cs` (all) | `updateTracking`, `postProcessHeadJudgement`, `tryJudgeNested`, `mouseInFollowArea` |
| `O/Objects/Drawables/DrawableSlider.cs:96-128,237-326` | `updateSlider`, `sliderCheckForResult`, `sliderGeom` |
| `O/Skinning/SnakingSliderBody.cs` Refresh, `F/Graphics/Lines/Path.cs:175-218`, `O/Skinning/Argon/ArgonSliderBody.cs:18-23` | `sliderGeom` (Size, PathOffset from the full path; snaking does not move them) |
| `L/osu.Game/Rulesets/Objects/SliderPath.cs:205-211,487-522`; `Types/IHasPathWithRepeats.cs:24-48` | `positionAt`, `progressAt`, `spanAt`, `curvePositionAt`, `binarySearchD` |
| `O/Objects/Drawables/DrawableSpinner.cs:203-366`, `Skinning/Default/SpinnerRotationTracker.cs`, `SpinnerSpinHistory.cs` | `updateSpinner`, `reportDelta`, `spinnerProgress`, `updateBonusScore`, `spinnerGeom` |
| `L/osu.Game/Scoring/Legacy/LegacyScoreDecoder.cs:268-352`, `O/Replays/OsuReplayFrame.cs:30-36` | `Replay.parseLegacyFrames`, `fixupFrames`, `convertFrame` |
| `L/osu.Game/Rulesets/Scoring/ScoreProcessor.cs:239-432,559-573`, `O/Scoring/OsuScoreProcessor.cs` | `ScoreSt.apply/updateScore`, `rankFromScore`, `scoreMaxima` |
| `L/osu.Game/Rulesets/Scoring/JudgementProcessor.cs` SimulateAutoplay / HasCompleted | `simulatedJudgements`, `processorsPhase` |
| `HealthProcessor.cs`, `DrainingHealthProcessor.cs`, `O/Scoring/OsuHealthProcessor.cs` | `healthApply`, `HealthSt.increaseFor/drain`, `computeDrainRate`, `noDrainPeriods`, `periodIsInAny` |
| `LegacyDrainingHealthProcessor.cs`, `O/Scoring/OsuLegacyHealthProcessor.cs` | `computeLegacyDrainRate`, `legacyHealthIncrease` |
| `L/osu.Game/Beatmaps/IBeatmapDifficultyInfo.cs:57-72` | `difficultyRange` (note `(max - mid) * ((d - 5) / 5)`) |
| `O/Scoring/OsuScoreMultiplierCalculatorV2.cs`, `G/Rulesets/Scoring/ScoreMultiplierCalculator.cs:59-90` | `scoreMultiplierV2`, `singleMultiplier`, `combinations` |
| `G/Screens/Play/GameplayClockExtensions.cs:14-22`, `F/Bindables/AggregateBindable.cs`, `G/Rulesets/Mods/{RateAdjustModHelper,ModNightcore,ModDaycore}.cs` | `Config.trueRate`, `aggregate` |
| `G/Rulesets/Mods/ModTimeRamp.cs:53-108`, `ModAdaptiveSpeed.cs:41-256` | `timeRampRate`, `dynRateUpdate`, `adaptiveSpeedOnResult`, `precedingEndTimes` |
| `G/Rulesets/Scoring/HealthProcessor.cs:37-103`, `G/Rulesets/Mods/{ModEasyWithExtraLives,ModFailCondition,ModSuddenDeath,ModPerfect,ModAccuracyChallenge}.cs`, `O/Mods/OsuModSuddenDeath.cs`, `O/Mods/OsuModTargetPractice.cs:106-112` | `triggerFailure`, `failCondition`, `healthApply`, `accChallenge` |
| `G/Rulesets/Scoring/ScoreProcessor.cs:206-223,391-416`, `G/Rulesets/Mods/{ModHidden,ModFlashlight}.cs` AdjustRank | `ScoreSt.updateScore` (rank, MaximumAccuracy), `adjustRank` |
| `O/Mods/OsuModRelax.cs:73-205` | `relaxUpdate` |
| `O/Mods/OsuModAutopilot.cs:43-69`, `O/Replays/OsuAutoGenerator.cs`, `OsuAutoGeneratorBase.cs` | `autopilotUpdate`, `AutoGen.generate` |
| `O/Mods/InputBlockingMod.cs`, `OsuModAlternate.cs`, `OsuModSingleTap.cs`, `G/Utils/PeriodTracker.cs` | `interceptPress`, `inputBlockUpdate`, `inputBlockPeriods` |
| `O/Mods/OsuModSpunOut.cs:26-54`, `O/Objects/Drawables/DrawableSpinner.cs:279-284` | `updateSpinner` (SpunOut branch), `spinnerMouseMove` |
| `O/Mods/OsuModStrictTracking.cs:34-54`, `O/Objects/Drawables/DrawableSlider.cs:237-242` | `updateSlider` (Tracking copy + tail miss) |
| `G/Rulesets/UI/Playfield.cs:262-273` | `playfieldUpdate` |

## Assumptions / scope

* Environment = the oracle's (D10): 1024x768, default config, argon skin, snaking on. Env data (HOC DrawInfo before/after
  the first layout pass, HOC size, argon path radius `0x425cb08d`) in `difftest/env-1024x768.json`.
* Mods in scope: all osu! mods (M5-M8 below); AT/CN replace the replay and are rejected. Mods come as the APIMod JSON list (`simtest --mods-json`),
  decoded with `OsuModel.Beatmap.Settings.toMod` (= `APIMod.ToMod`, shared with the beatmap model).
* Beatmap-side mod effects (EZ/HR/DA/MR/RD/TP/FR/ST conversion/CL slider behaviour/HD fade-in/…) are in the playable
  (oracle dump or `OsuModel/Beatmap`); the sim implements only drawable/processor-side effects.
* Not modelled because unobservable here: visual transforms other than those that define lifetimes, samples,
  rewinding, spectator statistics frames, `ClosestPressPosition`/hit-event positions, storyboard start time.
* Frames: decompressed LZMA text is the input; header fields used: beatmap version (offset) from the playable.
* Fuel-bounded loops (`while … fuel`) stand in for C# `while` loops; fuel is far above any reachable count, and
  running out of fuel is a rejection (`Except` error), never a silent truncation (G17).
* NaN payload handling per docs/net-float.md.

## Notable lazer quirks found (relevant for any re-implementation)

* `DifficultyRange` associates as `mid + (max - mid) * ((d - 5) / 5)` (docs/lazer-map.md §1.3 wrote `* (d-5)/5`):
  1-ulp health differences otherwise.
* Hover is recomputed **before** presses only if the cursor moved in that step; otherwise presses see the hover state
  of the previous step (a just-alive object under a static cursor can't be hit in its first input step).
* Input-time state is the previous step's: objects become alive in the lifetime phase after input.
* Classic heads keep consuming presses (`CanBeHit = !slider.AllJudged`) only while the head DHO is alive:
  hit → `RawTime + 800 + 1`, miss → `+ 100 + 1` (hit-state transforms + `LatestTransformEndTime`'s `+1`).
* An unjudged slider/spinner's Idle lifetime ends at `EndTime + 241`, circles `EndTime + 801`.
* `HitAction` is set on any hovered press of the head, even a notelocked one, and before PostProcessHeadJudgement
  runs the head's own `updateTracking` sees `HitAction == null`.
* Within a step, nested judgements come out ticks → repeats → tail → head → slider, and objects later-start-first.
* `AliveObjects` ties use .NET Dictionary enumeration order (free-list reuse); modelled.
* HOC matrix in step 0 is the pre-layout one (scale 1) — only affects the step-0 cursor.
* Spinner rotation tracker only updates its cursor on actual movement; `float.RadiansToDegrees(x) = (x*180f)/MathF.PI`.

## Results (bit-exact judgement lists: object, nested index, type, result, RawTime bits, combo; plus statistics and
max combo; M4 additionally per-judgement health bits + failed flag and all final fields of both fail semantics)

See the table at the end (filled from `results.jsonl` of the runs).

| milestone (mods) | schedule | corpus | jobs matching | judgements |
|---|---|---|---|---|
| M0 (NF) | catchup / perframe / dense1ms | syn2: 150 synthetic circle-only maps+replays | 150/150 each | 6000 each |
| M1 (NF+CL) | catchup / perframe / dense1ms | syn2 | 150/150 each | 6000 each |
| M2/M3 (NF+CL; sliders+spinners) | catchup | 100 real crawled replays (own mods replaced) | 100/100 | 101,132 |
| M2 (NF+CL) | catchup, perframe | syn3 (40 synthetic slider maps), syn4 (60, lazer-format .osr), syn5 (40 synthetic replays on real maps) | all match | 3655 / 6676 / 39709 |
| M2 (NF+CL) | dense1ms | syn3, syn4 | all match | 3655 / 6676 |
| M2nc (NF, no Classic) | catchup | 5 real | 5/5 | 6424 |
| M4 (CL, live fail) / M4nc (no mods) | catchup, perframe | syn3, syn4, syn5 | all match (incl. health bits per judgement, fail time/trigger count, both fail semantics, score, accuracy bits, rank) | as above |
| M4 (CL) | catchup | 5 real | 5/5 | 6424 |

| M2 (NF+CL) | dense1ms | syn5 | 40/40 | 39709 |
| M4 (CL) / M4nc | catchup | 100 real | 100/100 each | 101,132 each |
| M2 (NF+CL) | perframe | 100 real | 100/100 | 101,132 |
| M4 (CL) | dense1ms | 20 further real replays | 20/20 | 20,074 | The only mismatch ever found after the first build was the
`DifficultyRange` association (health 1-ulp), fixed.

### M5/M6 results (random mod subsets in random order with random settings per job, `sim_diff.py --gen-mods POOL`;
full compare: every judgement incl. health bits, both fail semantics, score, accuracy, rank, plus the multiplier check)

| pool (mods) | schedule | corpus | jobs | judgements |
|---|---|---|---|---|
| M5 (EZ NF HT DC DT NC WU WD AS SD PF AC FL CL HR MR DA SV2 TD) | catchup | sp2 (100 synthetic, sliders+spinners) | 100/100 | 10,257 |
| M5 | catchup | 100 real replays (mods replaced) | 100/100 | 79,797 |
| M5 | perframe / dense1ms | sp2 30 / sp4 12 | 30/30, 12/12 | 2,811 / 1,249 |
| M5fail (EZ NF SD PF AC CL HR DA) | perframe | 30 real | 30/30 | 13,146 |
| M6rx (RX legacy + CL/NF/HR/DT) | catchup | sp4 (60, half without key bits), sp3 (60, lazer replays: no-op) | 60/60, 60/60 | 6,316 / 8,285 |
| M6alt / M6so / M6st / M6ap | catchup | sp4 | 60/60 each (ST after the judged-slider fix) | 6,271 each |
| M6 (RX AP AL SG SO ST TD + rate/CL/fail) | catchup / perframe / dense1ms | sp2 30, 30 real / sp4 60 / sp4 12, 5 real | all match | 2,842, 13,145 / 6,237 / 1,239, 2,702 |

Sensitivity (`difftest/sim_mutate.py`: drop the mod from the model only, count jobs whose judgements then differ):
RX 56/60, AP 38/60, AL 38/60, SG 22/34, SO 59/60, ST 38/60 (sp4); rate mods change spinner results in 26/26 rate jobs
(sp1). Found by M5/M6: none beyond the StrictTracking judged-slider case (all other mods matched on the first run).

### M8: all mods together (`--gen-mods ALL`: random subsets of every osu! mod except AT/CN, random order/settings)

| corpus | schedule | jobs | judgements |
|---|---|---|---|
| 60 real (two seeds) | catchup | 60/60 (after the AP→cursor fix) | 40,573 |
| sp4 30 + 60 | catchup / perframe | 30/30, 60/60 | 3,103 / 6,143 |
| ns1 40 ×2 | catchup | 80/80 | 5,814 |
| sp4 12 (M7 pool) | dense1ms | 12/12 | 1,081 |

Found by M8: Autopilot's injected MouseMove (P3) also moves the CursorContainer, which Magnetised/Repel read later in
the same P3.

### M8: visual-only mods (`difftest/visual_diff.py`, oracle only: base mods vs base + one visual mod)

TC, FL, BL, BU, AD, NS, BM, MU, SY, SV2, TD: judgement lists (incl. RawTime, combo, health, failed), statistics, max
combo, accuracy and fail state identical on 30 real + 60 synthetic jobs (90/90). In the sim they are inert apart from
the score multiplier and AdjustRank (FL). RD/MR/FR/DA/EZ/HR act only through the playable. AT/CN replace the replay
(oracle rejects them; not applicable to replay evaluation).

## Source audit (2026-10-21, after the DifficultyRange finding)

Every formula in Sim/* was re-checked against the lazer / osu-framework source (citations in the correspondence
table and doc comments). Items that had initially come from docs/lazer-map.md and were re-verified in source:
`SliderEventGenerator.TAIL_LENIENCY = -36` (`SliderEventGenerator.cs:24`), `DrawableSliderBall.FOLLOW_AREA = 2.4f`
(`DrawableSliderBall.cs:19`), `RectangleF.Right/Bottom = X + Width / Y + Height` (`RectangleF.cs:86-104`),
`MarginPadding` negation/`TotalHorizontal` (`MarginPadding.cs:46,89`), `BindableNumber.ClampValue = T.Clamp`
(`BindableNumber.cs:209`), `DrawRectangle = (0, 0, DrawSize)` (`Drawable.cs:874-880`). The osuTK `Matrix3`/`Vector3`
layout (not in the repo) is checked numerically instead: `simtest --check-env ENV_DUMP` compares the model's DrawInfo
chains with the oracle's `--dump-env` probes. On 5 maps (3 real, 2 synthetic): every circle HitReceptor matrix/inverse,
every slider DrawInfo, OriginPosition, DrawSize and head-receptor matrix sampled while the slider is active is
bit-identical (≈105k checks).

**Known gap found by this check:** at the *first* step after a pooled `DrawableSlider` becomes alive, its
Size/OriginPosition (hence slider and head-receptor matrices) can still be those of the previous slider that used the
drawable: `PlaySliderBody.Refresh` is scheduled (`Scheduler.AddOnce`) and the body's scheduler only runs once the body
`SkinnableDrawable` is present (alpha > 0 after `FadeInFromZero`). The model uses the final geometry from the start.
Algebraically the head position is unchanged (`origin/size*size - origin`), so only float rounding of hover/follow
tests in that first step (≥ preempt before the head time, where no hit is possible; only `HitAction` on a hovered
press could be affected) differs. 133 of ≈105k probe records, all first-records.
