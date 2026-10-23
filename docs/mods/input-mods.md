# Input- and judgement-rule mods (osu! ruleset, lazer 2026.1005.0-lazer)

Status: research spec (read-only study of the pinned sources; nothing here has been diff-tested yet).
Path conventions follow `docs/lazer-map.md`: `L/` = `~/lazerproof/lazer`, `F/` = `~/lazerproof/osu-framework`,
`O/` = `L/osu.Game.Rulesets.Osu`, `G/` = `L/osu.Game`. Line numbers are from these checkouts.

Sibling docs (other agents): `docs/mods/difficulty-rate-fail.md` (difficulty, rate, fail, health, score multiplier, rank),
`docs/mods/transform-mods.md` (beatmap-level and drawable-level object transforms). This doc covers mods that change
**input handling or judgement rules**, plus the cursor and position-feedback mods Magnetised/Repel, Freeze Frame (lifetime),
and the runtime parts of Target Practice.

## 0. Phase notation (refines lazer-map §3.1)

One FSC step at time `t` (previous step time `t'`, `Elapsed = ElapsedFrameTime = t - t'`):

- **P1**: FrameStableComponents (`ScoreProcessor`, `HealthProcessor` drain, ...).
- **P2**: `OsuInputManager.Update` (`F/osu.Framework/Input/InputManager.cs:459-513`). The pending inputs are applied in
  the order the replay handler adds them (`O/Replays/OsuFramedReplayInputHandler.cs:22-28`):
  - **P2a** `MousePositionAbsoluteInput`. If the position changed (`F/.../StateChanges/MousePositionAbsoluteInput.cs:24-35`),
    `HandleMousePositionChange` (`InputManager.cs:959-975`) sends MouseMove to the positional queue (`:989`, it stops at the
    first handler that returns true), then calls `updateHoverEvents`.
  - **P2b** `ReplayState.Apply` (`G/Input/Handlers/ReplayInputHandler.cs:43-70`) → `RulesetInputManager.HandleInputStateChange`
    (`G/Rulesets/UI/RulesetInputManager.cs:81-101`): every release, then every press, through
    `KeyBindingContainer.TriggerReleased/TriggerPressed`.
  - **P2c** High-frequency MouseMove to every `IRequireHighFrequencyMousePosition` in the positional queue (SliderInputManager,
    CursorContainer, flashlight, ...). Then `updateHoverEvents` runs again if P2a did not run it (`InputManager.cs:500-501`).
- **P3**: `Playfield.Update` (`G/Rulesets/UI/Playfield.cs:263-287`): `base.Update()`, then **every `IUpdatableByPlayfield`
  mod in `Mods` list order** (`:267-274`), then the rewind revert loop. `Mods` is the gameplay mod array, so its order is the
  score's mod order (`G/Screens/Play/Player.cs:229,254`). For a legacy `.osr` that means `ConvertFromLegacyMods` order with
  `OsuModClassic` appended (`G/Scoring/Legacy/LegacyScoreDecoder.cs:88-92`). The oracle passes `spec.Mods` in the same order
  (`oracle/Gameplay.cs:178`).
- **P4**: HitObjectContainer lifetime (new DHOs become alive).
- **P5**: DHOs in container order. For each DHO: `UpdateTransforms` → `Update()` → **`OnUpdate` event**
  (`F/osu.Framework/Graphics/Drawable.cs:496-497`) → children → `UpdateAfterChildren` → `UpdateResult(false)`.

Shared facts used throughout:

- **Press dispatch** (`F/osu.Framework/Input/Bindings/KeyBindingContainer.cs`). `TriggerPressed(a)` (:409-417) calls
  `PropagatePressed(KeyBindingInputQueue, …)` (:322-345). The osu! mode is `Unique` (`O/OsuInputManager.cs:54-57`). If `a`
  is already in `pressedActions`, nothing happens. Otherwise `a` is **added to `pressedActions` first**, and then a
  `KeyBindingPressEvent` goes down the queue until a handler returns true. `KeyBindingInputQueue` (:62-71) is rebuilt on
  every call: the non-positional queue in tree order, reversed. `TriggerReleased(a)` (:407, :391-405) removes `a` and sends a
  release event to every handler, but only if `a` is in `pressedActions` and no physical binding holds it. In headless replay
  playback `pressedBindings` is always empty.
- **Hover**: `Drawable.IsHovered` (`F/.../Drawable.cs:2419`) is written only by `updateHoverEvents` (`InputManager.cs:657-707`),
  which runs in P2a and/or P2c, and again whenever a later `MousePositionAbsoluteInput` is applied (Autopilot, P3). It uses the
  drawable geometry at that moment, which during P2 is the geometry from the end of the previous step's P5.
- **HitReceptor consumption** (`O/Objects/Drawables/DrawableHitCircle.cs:277-301`): `if (!CanBeHit()) return false;` for
  L/R it updates `ClosestPressPosition`. Then `if (IsHovered) { Hit(); HitAction ??= e.Action; return true; }`. `CanBeHit`
  defaults to `!AllJudged` (:75). This is **not time-dependent**: an alive, unjudged, hovered circle consumes a press at
  any time and then judges or shakes inside `CheckForResult` (:137-173).
- **Mod settings rounding**: `BindableNumber<T>.Value` setter (`F/osu.Framework/Bindables/BindableNumber.cs:74-90`):
  `v' = (T) (Math.Round((decimal)clamp(v, Min, Max) / (decimal)Precision) * (decimal)Precision)`. `Math.Round(decimal)` is
  banker's rounding. `decimal.CreateTruncating(float)` converts like `(decimal)float`, which rounds to 7 significant digits.
  Exact decimal semantics are still a TODO in `docs/net-float.md`. Every float/double setting below goes through this setter.
- **System.Random**: `new System.Random(int seed)` uses the legacy seeded algorithm (`Net5CompatSeedImpl`, Knuth subtractive).
  `NextDouble() = InternalSample() * (1.0 / int.MaxValue)`. Seeds come from mod settings (`Seed.Value ??= RNG.Next()` happens
  only when the setting is null, which does not happen for a stored score). Only TP and Random use randomness in this doc's
  scope. Wiggle (`new Random((int)StartTime)`) is in transform-mods.md.

---------------------------------------------------------------------------------------------------

## 1. Classification of every mod in `O/OsuRuleset.cs:179-253` (`GetModsFor`)

"Judgement-relevant" means it can change any HitResult, RawTime, judgement order, combo, health, or pass/fail.
"Score-only" means judgements are unaffected but the mod enters the score multiplier
(`O/Scoring/OsuScoreMultiplierCalculatorV2.cs:14-112`, or V1 for `TotalScoreVersion < 30000017`) and/or `AdjustRank`.
Score-only parts belong to difficulty-rate-fail.md.

| Mod | Verdict | Covered in | Why / where |
|---|---|---|---|
| EZ Easy | relevant (difficulty, extra lives) | difficulty-rate-fail | `IApplicableToDifficulty`, `ModEasyWithExtraLives` |
| NF NoFail | relevant (fail) | difficulty-rate-fail | `IApplicableFailOverride`; multiplier 0.5 |
| HT / DC | relevant (rate) | difficulty-rate-fail | `ModRateAdjust` → `GetTrueGameplayRate` (spinner, SO §6) and AP generator timing (§4.3) |
| HR | relevant | difficulty-rate-fail (difficulty) + transform-mods (flip) | |
| SD / PF | relevant (fail) | difficulty-rate-fail | `ModFailCondition` |
| DT / NC | relevant (rate) | difficulty-rate-fail | as HT |
| HD | judgement-irrelevant; score/rank | difficulty-rate-fail (rank XH/SH, multiplier) | fades drawables only. DHO input propagation ignores presence entirely (`PropagatePositionalInputSubTree/PropagateNonPositionalInputSubTree => HandleUserInput`, `G/Rulesets/Objects/Drawables/DrawableHitObject.cs:76,78`), so faded objects (judged or not) still receive input; HitReceptor alpha is untouched |
| TC Traceable | judgement-irrelevant; multiplier 1.02 | – | hides pieces (`O/Mods/OsuModTraceable.cs:72`), same IsPresent argument |
| FL Flashlight | judgement-irrelevant; rank + multiplier | difficulty-rate-fail | §12.2 |
| BL Blinds | judgement-irrelevant; multiplier 1.24 | difficulty-rate-fail | §12.2 |
| ST StrictTracking | **relevant** | **this doc §7** | replaces sliders, forced tail miss |
| AC AccuracyChallenge | relevant (fail) | difficulty-rate-fail | |
| TP TargetPractice | **relevant** | generation: transform-mods; runtime: **this doc §10**; fail/AR: difficulty-rate-fail | |
| DA DifficultyAdjust | relevant | difficulty-rate-fail | |
| CL Classic | **relevant** | core model (M1/M2) + **this doc §8** (settings), health: difficulty-rate-fail | |
| RD Random | relevant (positions) | transform-mods | `System.Random((int)Seed)` (`O/Mods/OsuModRandom.cs:47-49`), §13 |
| MR Mirror | relevant (positions) | transform-mods | `IApplicableToHitObject`, §13 |
| AL Alternate / SG SingleTap | **relevant** | **this doc §5** | `InputBlockingMod` |
| AT Autoplay / CN Cinema | n/a for user replays | **this doc §11** | `ICreateReplayData` |
| RX Relax | **relevant** (legacy replays) | **this doc §3** | |
| AP Autopilot | **relevant** | **this doc §4** | |
| SO SpunOut | **relevant** | **this doc §6** | |
| TR Transform | relevant (P) | transform-mods | |
| WG Wiggle | relevant (P) | transform-mods | |
| SI SpinIn | relevant (P) | transform-mods | |
| GR / DF Grow/Deflate | relevant (P) | transform-mods | |
| WU / WD WindUp/Down | relevant (rate) | difficulty-rate-fail | `ModTimeRamp` is `IUpdatableByPlayfield` |
| BR BarrelRoll | relevant (P) | transform-mods | `IUpdatableByPlayfield`; interacts with RX order (§14) |
| AD ApproachDifferent | judgement-irrelevant; multiplier 0.7 | – | §12.3 |
| MU Muted | judgement-irrelevant | – | §12.4 |
| NS NoScope | judgement-irrelevant | – | §12.5 |
| MG / RP Magnetised/Repel | **relevant** (P, schedule-dependent) | **this doc §9** (transform-mods may cross-reference) | |
| AS AdaptiveSpeed | relevant (rate) | difficulty-rate-fail | |
| FR FreezeFrame | **relevant** (lifetime) | **this doc §12.1** | |
| BU Bubbles | judgement-irrelevant | – | §12.6 |
| SY Synesthesia | judgement-irrelevant; multiplier 0.99 | – | §12.7 |
| DP Depth | relevant (P) | transform-mods | |
| BM Bloom | judgement-irrelevant | – | §12.5 |
| TD TouchDevice | judgement-irrelevant | – | §12.8 |
| SV2 ScoreV2 | judgement-irrelevant (marker) | difficulty-rate-fail if it affects scoring | `G/Rulesets/Mods/ModScoreV2.cs:14` has no interfaces |

How the irrelevant verdicts are argued: a mod can change judgement only if it (a) changes the playable beatmap, (b) moves,
scales, or changes the lifetime of a DHO or its input-receiving ancestors, (c) handles `OsuAction` presses or MouseMove/Hover
and returns `true` (blocking), (d) injects input, or (e) writes processor or DHO judgement state. For each "irrelevant" mod
the interfaces were listed and checked against (a)-(e). Only these `IKeyBindingHandler<OsuAction>` exist in `O/`:
InputBlockingMod interceptor, SmokeContainer (true only for Smoke, `O/UI/SmokeContainer.cs:35-47`), OsuCursorContainer /
CursorRippleVisualiser / LegacyCursorParticles (all return false), DrawableHitCircle.HitReceptor, and OsuResumeOverlay
(pause only).

---------------------------------------------------------------------------------------------------

## 2. Mod interface hooks and when they run

| Hook | When | Mods in scope |
|---|---|---|
| `IApplicableAfterBeatmapConversion` | `WorkingBeatmap.GetPlayableBeatmap` step after `converter.Convert` (`G/Beatmaps/WorkingBeatmap.cs`, lazer-map §1.2) | ST |
| `IApplicableToHitObject` | after ApplyDefaults, before PostProcess | CL (`ClassicSliderBehaviour`), MR, HR |
| `IApplicableToBeatmap` | last, after PostProcess (stacking) | TP, FR, RD, NS, SY, ModWithVisibilityAdjustment base |
| `IApplicableToDrawableRuleset` | `DrawableRuleset.load` → `applyRulesetMods` (`G/Rulesets/UI/DrawableRuleset.cs:174-203,365-376`), after the FSC/input tree is built, before `loadObjects` | RX, AP, AL/SG, ST, CL, MG/RP, TP, BU, BL, FL |
| `IApplicableToDrawableHitObject` | per DHO after load (`DrawableRuleset.cs:216-222`) and for pooled DHOs (`Playfield.cs:414-415`) | SO, ST, CL, FR, TP (via base), AD |
| `IApplicableToPlayer` | `Player.cs:1149` (the oracle: `oracle/Gameplay.cs:309-310`), **after** `SetReplayScore` | RX, NS, BM, CN |
| `IUpdatableByPlayfield` | P3 of every step, in `Mods` order | RX, AP, AL/SG, MG/RP, NS, BM, BR, DP, WU/WD, AS |

---------------------------------------------------------------------------------------------------

## 3. Relax (`O/Mods/OsuModRelax.cs`)

Interfaces: `IUpdatableByPlayfield, IApplicableToDrawableRuleset<OsuHitObject>, IApplicableToPlayer, IHasNoTimedInputs` (:21).
Incompatible: Autoplay (`G/Rulesets/Mods/ModRelax.cs:16`), Autopilot, Magnetised, Alternate, SingleTap (:25-26).
Not incompatible with Repel, BarrelRoll, Depth, Wiggle, or Transform (see §14). No settings.
`IHasNoTimedInputs` only feeds hit-error/offset UI (`G/Configuration/SessionAverageHitErrorTracker.cs:40`), so it is irrelevant here.

### 3.1 Mode selection (`:47-71`)
- `ApplyToDrawableRuleset` stores the ruleset and `osuInputManager = ruleset.KeyBindingInputManager`.
- `ApplyToPlayer`: if `osuInputManager.ReplayInputHandler != null` then `hasReplay = true` and
  `legacyReplay = ruleset.ReplayScore.ScoreInfo.IsLegacyScore`, otherwise live play (`AllowGameplayInputs = false`, which is
  not relevant for us).
- `IsLegacyScore = version < LegacyScoreEncoder.FIRST_LAZER_VERSION (30000000)` (`G/Scoring/Legacy/LegacyScoreDecoder.cs:56`).
- **Lazer replay (`!legacyReplay`)**: `Update` returns immediately (:75-76). Relax is then a pure no-op for judgement,
  because the recorded replay already contains the presses the live PressHandler produced. Only the multiplier remains
  (V2: 0.1, `OsuScoreMultiplierCalculatorV2.cs:74`).
- **Legacy replay**: presses are synthesised by `LegacyReplayPressHandler` (:186-205). The replay's own key bits are still
  processed normally in P2b. Stable RX replays normally have no key bits, but the model must not assume that.
- The oracle has to set the replay handler before `ApplyToPlayer`, which it does (`oracle/Gameplay.cs:309`), and report
  `is_legacy_score` (`oracle/Program.cs:243`).

### 3.2 Mod state (pure model)
```
isDownState : bool = false
wasLeft     : bool = false        -- toggles after every synthesised press
lastStateChangeTime : double = 0  -- default(double)
```
Constants: `RELAX_LENIENCY = 12` (float, :31, compared as double), `AutoGenerator.KEY_UP_DELAY = 50` (double,
`G/Rulesets/Replays/AutoGenerator.cs:17`).

### 3.3 Per-step semantics (P3, legacy replay only) — `Update` (:73-156)
Let `time = playfield.Clock.CurrentTime` (= `t`). Then:
```
requiresHold = false; requiresHit = false
for h in HitObjectContainer.AliveObjects (top-level DHOs, OrderBy StartTime; G/Rulesets/UI/HitObjectContainer.cs:24):
    if time < h.StartTime - 12: break            -- sorted by StartTime, so the rest are later
    if h.IsHit or (h is IHasDuration and time > h.EndTime): continue
    case circle:   handleHitCircle(circle)
    case slider:   if !slider.HeadCircle.IsHit: handleHitCircle(slider.HeadCircle)
                   requiresHold |= slider.SliderInputManager.IsMouseInFollowArea(slider.Tracking.Value)
    case spinner:  requiresHold |= spinner.SpinsRequired > 0
handleHitCircle(c): if c.HitArea.IsHovered: requiresHit |= c.HitWindows.CanBeHit(time - c.StartTime)
if requiresHit: changeState(false); changeState(true)
if requiresHold: changeState(true)
elif isDownState and time - lastStateChangeTime > 50: changeState(false)
changeState(down): if isDownState == down: return
                   isDownState = down; lastStateChangeTime = time
                   if down: TriggerPressed(wasLeft ? Left : Right); wasLeft = !wasLeft
                   else:    TriggerReleased(wasLeft ? Right : Left)
```
Notes:
- Iteration order does not matter, since the results are OR-accumulated and ties in StartTime share the same `break`
  condition. The alive set is the one from **before** this step's P4: objects that become alive at `t` are not seen.
- `IsHit` means judged and hit (`Result.IsHit`). A circle that was **missed** (for example force-missed by notelock) is still
  processed and still produces `requiresHit` while hovered and `CanBeHit` holds.
- `HitWindows.CanBeHit(o) = o <= WindowFor(Meh)` (`G/Rulesets/Scoring/HitWindows.cs:109`). Only the late bound is checked;
  the early bound comes from the `time >= StartTime - 12` gate.
- `IsHovered` is the P2 hover flag of this step (§0). Hover was computed against the previous step's geometry, with the
  interpolated cursor at `t`.
- `IsMouseInFollowArea(expanded)` (`O/Objects/Drawables/SliderInputManager.cs:184-196`) uses `screenSpaceMousePosition`
  from this step's MouseMove and `slider.ToLocalSpace` **at the moment of the call**, which includes changes made earlier
  in P3 by mods listed before RX (§14). `expanded = DrawableSlider.Tracking.Value`, the bindable copied in the previous
  step's P5 (`DrawableSlider.cs:235-242`). Follow radius = `(float)Radius` × `DrawableSliderBall.FOLLOW_AREA` when expanded.
- Key alternation: the first press is **Right** (`wasLeft=false`). After a press, `wasLeft` names the key that was pressed,
  and the release uses `wasLeft ? Right : Left`, so it releases the same key. `requiresHit` while down gives
  release-then-press on the other key, all inside the same P3.
- `TriggerPressed`/`TriggerReleased` run directly on the KeyBindingContainer. They do **not** touch
  `RulesetInputManagerInputState.LastReplayState`, so replay diffs in P2b keep comparing replay frame against replay
  frame. Interference with replay key bits follows the Unique rules (§0): pressing an action the replay already holds is a
  no-op, and a Relax release removes the action even if the replay still holds it. A later replay release of that action
  is then a no-op, and a later replay *press* of it is a fresh press.
- Effects within the same step: the press reaches HitReceptors in queue order, then hit policy, then `UpdateResult(true)`,
  with `RawTime = t`. All of this happens before P4/P5, so `SliderInputManager.Update` and `DrawableSpinner.Update`
  (`correctButtonPressed`, `DrawableSpinner.cs:279-284,309-321`) in P5 already see the new `PressedActions`.
- Stable replays always carry Classic, so RX legacy evaluation uses `LegacyHitPolicy`, and the head `CanBeHit` override
  of §8 is in effect.

---------------------------------------------------------------------------------------------------

## 4. Autopilot (`O/Mods/OsuModAutopilot.cs`)

Interfaces: `IUpdatableByPlayfield, IApplicableToDrawableRuleset` (:19). Incompatible: SpunOut, Relax, Autoplay,
Magnetised, Repel, TouchDevice (:27-35). No settings. Multiplier 0.1.

### 4.1 Setup (`:61-69`)
- `inputManager.AllowUserCursorMovement = false`. This only filters MouseMove/TouchMove UI events that the
  `OsuInputManager` *receives* from a parent (`O/OsuInputManager.cs:66-71`). **It does not block the replay handler's
  `MousePositionAbsoluteInput`**, because those are the input manager's own pending inputs (P2a).
- `replayFrames = new OsuAutoGenerator(drawableRuleset.Beatmap, drawableRuleset.Mods).Generate().Frames`: built from the
  final playable beatmap (all mods applied, stacked) and the gameplay mods. See §4.3.
- Classic interplay: `hittableRange = 400 - 200 = 200` for `LegacyHitPolicy` when AP is present
  (`O/Mods/OsuModClassic.cs:56-60`). This affects every stable AP replay, since Classic is added automatically.

### 4.2 Per-step semantics (P3) — `Update` (:43-59)
State: `currentFrame : int = -1`.
```
if currentFrame == replayFrames.Count - 1: return          -- also covers an empty list (-1 == -1)
time = playfield.Clock.CurrentTime
if currentFrame < 0 or |F[currentFrame+1].Time - time| <= |F[currentFrame].Time - time|:
    currentFrame++
    MousePositionAbsoluteInput{ playfield.ToScreenSpace(F[currentFrame].Position) }.Apply(inputManager.CurrentState, inputManager)
```
- **At most one generated frame per step.** If the generator's 16.67 ms cadence is denser than the step schedule, AP lags
  behind, so the result is schedule-dependent.
- The applied position goes through `OsuPlayfield.ToScreenSpace`, not `HitObjectContainer.ToScreenSpace` (which the
  replay handler uses). The ideal maths are the same, but float rounding may differ (lazer-map §6.6).
- When the position changes, the injection runs `HandleMousePositionChange` **immediately inside P3**: MouseMove reaches
  the positional queue (SliderInputManager `screenSpaceMousePosition`, SpinnerRotationTracker `mousePosition`,
  CursorContainer `ActiveCursor.Position`), and hover is recomputed.
- **With a replay present** (always the case for us), P2a of the *next* step applies the replay's interpolated position
  again, because `CollectReplayInputs` emits it every step (`O/Replays/OsuFramedReplayInputHandler.cs:22-28`) and it differs
  from the AP position. So:
  - presses in P2b are hit-tested at the **replay** position;
  - on steps where AP advances, P5 consumers (slider tracking in `SliderInputManager.Update`, spinner angle in
    `SpinnerRotationTracker.Update`) see the **AP frame position**;
  - on steps where AP does not advance, they see the replay position.
  The spinner tracker therefore receives alternating positions, and each change feeds `lastAngle`/delta
  (`O/Skinning/Default/SpinnerRotationTracker.cs:57-84`). Whether lazer-recorded AP replays already contain AP positions
  makes no difference to the model: it must reproduce this alternation exactly. **Difftest priority: high** (unusual
  behaviour).
- There is no auto-spin (TODO at :58).

### 4.3 OsuAutoGenerator (needed only for AP; also Autoplay)
Files: `O/Replays/OsuAutoGenerator.cs`, `O/Replays/OsuAutoGeneratorBase.cs`. Deterministic, no randomness. It uses
`MathF`/`Math` trig, which go through libm externs (docs/net-float.md). `DelayedMovements` is never set (:34), so
`addDelayedMovements` (:94-142) is dead code. Structure:
- `Generate` (:69-92): if there are no objects, return an empty replay. Otherwise add the frame `(first.StartTime - 1500,
  (256,500))`, then for each object `addHitObjectReplay(h)`.
- `addHitObjectReplay` (:144-183): `startPosition = h.StackedPosition`, `easing = Easing.Out` (`preferredEasing`, :47).
  For a spinner: if `SpinsRequired == 0` return (no frames at all). Otherwise `calcSpinnerStartPosAndDirection(lastFramePos)`
  (:185-230, float maths with `MathF.Asin/Cos/Sin/Sqrt`, `Vector2.Normalize`; note the in-place X update before computing Y,
  :207-208). Use `Easing.In` if the last position is further than `SPIN_RADIUS = 50` from `SPINNER_CENTRE = (256,192)`.
  Then `moveToHitObject` (if any frames) and `addHitObjectClickFrames`.
- `moveToHitObject` (:232-276):
  - `waitTime = h.StartTime - max(0, h.TimePreempt - reaction(h.StartTime - h.TimePreempt))`, with
    `reaction = ApplyModsToRate(t, 100)`. If `waitTime > lastFrame.Time`, insert a wait frame.
  - `timeDifference = ApplyModsToTimeDelta(lastFrame.Time, h.StartTime)`.
  - If it is `>= 0`: if the last frame is a key-up frame (and there was no wait), re-ease its position. Then add frames at
    `time = lastFrame.Time + delay; time < h.StartTime; time += GetFrameDelay(time)` with time **truncated `(int)time`**
    and position `Interpolation.ValueAt(time, lastPos, target, lastFrame.Time, h.StartTime, easing)` (Vector2 overload,
    `F/osu.Framework/Utils/Interpolation.cs:352-362`).
  - `buttonIndex++` if `0 <= timeDifference < 266`, else reset to 0.
- `addHitObjectClickFrames` (:286-397):
  - `action = buttonIndex % 2 == 0 ? Left : Right`. Start frame at `h.StartTime`. Key-up frame at
    `h.GetEndTime() + 50 (+1 for spinners)`.
  - Overlap handling (:298-325): swap the key if the previous frame holds it, delete frames up to the end frame's
    insertion index, rewrite held actions.
  - Spinner: circular frames using `spin_rpm = 0.05f/(2π)*60000` (local `const float`, Roslyn-folded to 477.46484f =
    0x43EEBB80; **[verified]**: lazer's compiled IL is `ldc.r4 171887.34` (= `spin_rpm*360`, 0x4827DBD6, also folded),
    then a runtime `float.DegreesToRadians` and `/ 60000f`, giving `radsPerMillisecond = 0.050000004f` (0x3D4CCCCE);
    kernel fact in `model/OsuModel/Net/LibChecks.lean`),
    `radsPerMillisecond = float.DegreesToRadians(spin_rpm*360)/60000` (float), time-stepped with `GetFrameDelay`, positions from
    `CirclePosition(angle, 50)` (:118 base, double cos/sin cast to float).
  - Slider: frames at `StartTime + j` for `j = delay; j < Duration; j += GetFrameDelay(StartTime + j)` at
    `StackedPositionAt(j / Duration)`, plus the end frame. The key-up frame is added if `last.Time <= endFrame.Time`.
- Base utilities (`OsuAutoGeneratorBase.cs:58-118`):
  - `ApplyModsToTimeDelta`: `delta /= mod.ApplyToRate(startTime)` for each `IApplicableToRate` in mod order.
  - `ApplyModsToRate`: `rate = mod.ApplyToRate(time, rate)`.
  - `GetFrameDelay = ApplyModsToRate(time, 1000.0/60)`.
  - `FindInsertionIndex`: binary search, then skip past equal times, so a new frame goes after existing frames with the
    same time.
  - `ApplyToRate`: rate mods `rate*SpeedChange` (`G/Rulesets/Mods/ModRateAdjust.cs:26`); time ramp
    `rate*Math.Round(ramp, 2)` (`G/Rulesets/Mods/ModTimeRamp.cs:91-98`); AdaptiveSpeed `rate*InitialRate`
    (`G/Rulesets/Mods/ModAdaptiveSpeed.cs:160`).
- The generator reads `TimePreempt` (FR interplay, §12.1) and the post-mod positions (HR/MR/RD/TP).

---------------------------------------------------------------------------------------------------

## 5. Alternate / SingleTap (`O/Mods/InputBlockingMod.cs`, `OsuModAlternate.cs`, `OsuModSingleTap.cs`)

Interfaces: `IApplicableToDrawableRuleset, IUpdatableByPlayfield` (:22). Incompatible: Autoplay, Relax, Cinema (:24), and
each other. No settings. Multiplier 1.0.

### 5.1 Setup (`:43-63`)
- `ruleset.KeyBindingInputManager.Add(new InputInterceptor(this))`. This adds the interceptor to the input manager's
  content **after** `[PlayfieldAdjustmentContainer(Playfield), Overlays]` (`DrawableRuleset.cs:180-187` runs before
  `applyRulesetMods` at :198). The queue is reversed, so the **interceptor sees every press before any DHO**.
- Non-gameplay periods (doubles):
  `P0 = (int.MinValue, V(first) - 1)` and, for every break `b` in `drawableRuleset.Beatmap.Breaks` (playable beatmap),
  `(b.StartTime, V(firstObj with StartTime >= b.EndTime) - 1)`. Here `V(h) = h.StartTime - h.HitWindows.WindowFor(Meh)`.
  - For a circle, `WindowFor(Meh)` comes from OD. For **sliders and spinners `HitWindows.Empty` gives 0**
    (`O/Objects/Slider.cs:295`, `Spinner.cs:100`, `G/Rulesets/Scoring/HitWindows.cs:117`), so `V = StartTime`.
  - `First(...)` throws if a break has no object after it, which would be a load failure (edge case: reject).
  - `Period(start, end)` throws if `start >= end` (`G/Utils/PeriodTracker.cs:80-87`), also a load failure.
- `PeriodTracker` (`G/Utils/PeriodTracker.cs:14-56`): periods are sorted by Start. `IsInAny(t)` is **stateful**
  (`nearestIndex`, walks forward while `t > End`, backward while `t < Start`; inclusive test `Start <= t <= End`). For
  disjoint sorted periods it equals pure membership (proof: the forward walk stops at the first period with `t <= End`,
  the backward walk stops at the first with `t >= Start`). If periods overlap (malformed breaks), model the walk exactly.
- `gameplayClock = drawableRuleset.FrameStableClock`, so `CurrentTime = t` in both P2 and P3.

### 5.2 State and semantics
State: `LastAcceptedAction : OsuAction?` (null) and the tracker index.
- **P2b, on every press that propagates** (that is, a new action under Unique; §0) → `InputInterceptor.OnPressed`
  (:111-113) returns `!checkCorrectAction(a)` (:76-100):
  - if `IsInAny(t)`: accept, **without** recording;
  - else if `a` is not L/R (Smoke): accept;
  - else if `CheckValidNewAction(a)`: `LastAcceptedAction = a`, accept;
  - else: **block** (the handler returns true, so the event does not reach DHOs; the cursor flash is visual).
  - `CheckValidNewAction`: Alternate `LastAcceptedAction != a` (`OsuModAlternate.cs:21`); SingleTap
    `LastAcceptedAction == null || LastAcceptedAction == a` (`OsuModSingleTap.cs:21`).
- **P3** `Update` (:65-72): if `LastAcceptedAction != null && IsInAny(t)`, set it to null (also on rewinding, which does
  not apply to us).
- **A blocked action still counts as held**: it is already in `pressedActions`. So it counts for slider tracking
  (`SliderInputManager.cs:255-260`), spinner `correctButtonPressed`, and later releases (release events go to all handlers;
  HitReceptor ignores them). It does not set any slider head's `HitAction`.
- Several presses in one replay frame are checked one after another in the frame's action order (Left, Right). Relax
  presses never reach this code (RX is incompatible).

---------------------------------------------------------------------------------------------------

## 6. Spun Out (`O/Mods/OsuModSpunOut.cs`)

Interface: `IApplicableToDrawableHitObject` (:16). Incompatible: Autoplay, Autopilot, TargetPractice (:23). No settings.
Multiplier 0.95 (V2).

- Applied to every `DrawableSpinner` (:26-33). It sets `spinner.HandleUserInput = false`, so the DHO stops propagating
  positional and non-positional input (`DrawableHitObject.cs:74-78`). The rotation tracker therefore **never gets
  MouseMove**, its `mousePosition` stays null, and the mouse-angle branch of `SpinnerRotationTracker.Update` never runs
  (`SpinnerRotationTracker.cs:63-80`). `DrawableSpinner.Update` skips its own Tracking assignment
  (`DrawableSpinner.cs:283-284`). It also subscribes `OnUpdate += onSpinnerUpdate`.
- **Timing**: `onSpinnerUpdate` runs in P5 right after `DrawableSpinner.Update()` (OnUpdate, `Drawable.cs:496-497`), before
  the spinner's children (the tracker's own `Update`, ticks) and before `UpdateAfterChildren` (`TimeStarted`, spm,
  `updateBonusScore`, `DrawableSpinner.cs:323-337`) and `UpdateResult`. It runs on every step the spinner DHO is alive and
  present.
- Per step (:35-54), exact types:
  ```
  RotationTracker.Tracking = IsSpinnableTime          -- StartTime <= t < EndTime  (SpinnerRotationTracker.cs:55)
  if |Clock.Rate - 0| <= 1e-7: return                 -- Precision.AlmostEquals(double) DOUBLE_EPSILON (F/.../Utils/Precision.cs:23,86)
  double e   = Clock.ElapsedFrameTime / Clock.Rate    -- FSC framed clock; Rate = |reference.Rate| (FrameStabilityContainer.cs:196)
  float  spd = (float)(1.01 * SpinsRequired / Duration)     -- double maths: (1.01*int)/double, then cast
  float  deg = float.RadiansToDegrees((float)e * spd * MathF.PI * 2.0f)   -- float, left-to-right
  RotationTracker.AddRotation(deg)
  ```
  `AddRotation` (`SpinnerRotationTracker.cs:93-111`) is a no-op outside spinnable time. It initialises `currentRotation` from
  the drawable `Rotation` on first use (0 here), computes `delta = (float)(deg * |GetTrueGameplayRate()|)` (double multiply,
  then cast), `currentRotation += delta`, and calls `History.ReportDelta(t, delta)`.
  - `float.RadiansToDegrees(x)` is .NET's `(x * 180f) / MathF.PI` in float. **Verify against the .NET 10 BCL source**; it is
    not yet in docs/net-float.md.
  - `Debug.Assert(|delta| <= 180)` is compiled out in Release. A huge `ElapsedFrameTime` (for example the first step after
    the `GameplayStartTime` jump, if the spinner is alive then) adds a large delta in one go.
- The rate cancels only approximately: `e` divides by `Clock.Rate`, which is set at step start in `updateClock`, and
  `AddRotation` multiplies by `GetTrueGameplayRate()`, read live in P5. With constant-rate mods the two are equal (oracle:
  `Rate = AggregateFrequency*AggregateTempo`, `oracle/Gameplay.cs:501-502`), so the effective delta is
  `(float)(deg*r)` with `deg` computed from `e = Δt/r`, and float rounding still applies. With WU/WD/AS the two rates can
  differ, because `ModTimeRamp`/AS update SpeedChange in P3 after the FSC clock was set. The rate state model is in
  difficulty-rate-fail.md.
- `HandleUserInput=false` also means presses held during spinners are irrelevant, and Relax's `requiresHold` for spinners
  (§3) does nothing.

---------------------------------------------------------------------------------------------------

## 7. Strict Tracking (`O/Mods/OsuModStrictTracking.cs`)

Interfaces: `IApplicableAfterBeatmapConversion, IApplicableToDrawableHitObject, IApplicableToDrawableRuleset` (:25).
Incompatible: Classic, TargetPractice (:32). Because Classic is incompatible, ST occurs only in lazer replays and
`ClassicSliderBehaviour` is always false. No settings. Multiplier 1.0.

### 7.1 Beatmap replacement (`:56-74, 101-172`)
Right after conversion, before difficulty mods, PreProcess, ApplyDefaults and stacking, every `Slider` is replaced by
`StrictTrackingSlider(original)`. It copies `StartTime, Samples, Path (same object), NodeSamples, RepeatCount, Position,
NewCombo, ComboOffset, TickDistanceMultiplier, SliderVelocityMultiplier`. Differences from the converter's `Slider`
(`O/Beatmaps/OsuBeatmapConverter.cs:37-51`, `O/Objects/Slider.cs:170-238`):
1. **`GenerateTicks` is not copied**, so it keeps the default `true`. Sliders whose decoder set `GenerateTicks = false` (NaN
   beat length, `G/Beatmaps/Formats/LegacyBeatmapDecoder.cs:160,548`) get finite `TickDistance` and **gain ticks**
   (`Slider.cs:167`).
2. Nested creation (:117-172): the same `SliderEventGenerator.Generate` call, with these changes:
   - the tail is `StrictTrackingSliderTailCircle` (judgement `StrictTrackingTailJudgement`: Max `SliderTailHit`,
     **Min `LargeTickMiss`** instead of `IgnoreMiss`, :88-94; compare `Judgement.cs:61-85`);
   - `LastRepeat` is not assigned (used only by the editor);
   - ticks and repeats get `Scale = Scale`, which nested ApplyDefaults overwrites anyway;
   - the head and tail get no `ClassicSliderBehaviour`, which is false anyway.
   `GetType()` differs, but pool lookup falls back to `IsInstanceOfType` (`Playfield.cs:431-449`), so a `DrawableSlider` is used.
   `ApplyToDrawableRuleset` registers the tail pool `StrictTrackingSliderTailCircle → StrictTrackingDrawableSliderTail` (:76-79).

### 7.2 Runtime rule (`:34-54`)
On each `DrawableSlider`, `Tracking.ValueChanged` is subscribed. `DrawableSlider.Tracking` is assigned **in P5 inside
`DrawableSlider.Update`** from `SliderInputManager.Tracking` (`DrawableSlider.cs:237-242`). That value was computed in the
previous step's P5 (`SliderInputManager.Update`, a child that runs after the parent's Update) or in this step's P2/P3 by
`PostProcessHeadJudgement` (`SliderInputManager.cs:78-140`). The handler fires synchronously on a true→false change:
```
if newValue or slider.Judged: return
if slider.Time.Current < slider.StartTime: return
if (slider.Clock as IGameplayClock)?.IsRewinding == true: return    -- never in forward replay
tail = first StrictTrackingDrawableSliderTail nested
if !tail.Judged: tail.MissForcefully()       -- ApplyMinResult → LargeTickMiss, RawTime = t
```
- This happens in P5 before the slider's nested children and `UpdateAfterChildren`. The slider itself (OsuIgnoreJudgement)
  is still judged only once `TailCircle.Judged && t >= EndTime` (`DrawableSlider.cs:293-326`).
- Ticks and repeats that are not yet judged keep their normal per-object judgement.
- Tracking can become true **before** StartTime (any L/R held within the follow area). A true→false change at or after
  StartTime then misses the tail even if the head was never hit.
- Result order: the tail miss enters the normal `OnNewResult` chain (lazer-map §3.1).

---------------------------------------------------------------------------------------------------

## 8. Classic settings (`O/Mods/OsuModClassic.cs`) — input/judgement parts

Defaults are what every stable replay gets (`LegacyScoreDecoder.cs:91-92`). All five settings are `bool`, default `true`
(:25-38). V2 multiplier: `ClassicNoteLock ? 0.985 : 0.96`.

| Setting | Effect | Hook / timing |
|---|---|---|
| `NoSliderHeadAccuracy` | `slider.ClassicSliderBehaviour = value` (:42-50). Runs after ApplyDefaults, so the setter propagates to the existing head and tail (`Slider.cs:113-121`). If true: head judgement `SliderTickJudgement` (LargeTickHit/Miss, `SliderHeadCircle.cs:17`) with `ResultFor` mapped hit→LargeTickHit, else LargeTickMiss (`DrawableSliderHead.cs:59-73`); tail `LegacyTailJudgement` (SmallTickHit, `SliderTailCircle.cs:23-28`); slider `OsuJudgement` with the proportional result (all hit → Great, 0 → Miss, `hit/total >= 0.5` → Ok, else Meh; `DrawableSlider.cs:298-312`) | beatmap level |
| `ClassicNoteLock` | `Playfield.HitPolicy = new LegacyHitPolicy(400 - (AP ? 200 : 0))` (:56-60); and every `DrawableSliderHead.HitArea.CanBeHit = () => !DrawableSlider.AllJudged` (:96-99). An already-hit head keeps consuming presses (hovered) until the whole slider is judged | `ApplyToDrawableRuleset`, `ApplyToDrawableHitObject` |
| `AlwaysPlayTailSample` | `tail.SamplePlaysOnlyOnHit = !value` | audio only |
| `FadeHitCircleEarly` | early fade transforms (alpha only; DHO input ignores presence, `DrawableHitObject.cs:76,78`) | visual |
| `ClassicHealth` | `OsuLegacyHealthProcessor` | difficulty-rate-fail.md |

The behaviour itself (LegacyHitPolicy, classic slider scoring) is core-model content (lazer-map §3.3/§3.4, milestones M1/M2).

---------------------------------------------------------------------------------------------------

## 9. Magnetised / Repel (`O/Mods/OsuModMagnetised.cs`, `O/Mods/OsuModRepel.cs`)

Both are `IUpdatableByPlayfield, IApplicableToDrawableRuleset`. `ApplyToDrawableRuleset` only hides follow points
(visual). They are mutually incompatible.
- MG is incompatible with AP, Wiggle, Transform, Autoplay, **Relax**, Repel, Bubbles, Depth (:30).
- RP is incompatible with AP, Wiggle, Transform, Autoplay, MG, Bubbles, Depth (:31). **RP+Relax is allowed.**

Settings:
- MG `AttractionStrength`: `BindableFloat` 0.5, `[0.05, 1.0]`, precision 0.05 (:32-38).
- RP `RepulsionStrength`: same (:33-39).

Multipliers (V2): MG `0.7 - s*0.6` (float s widened to double); RP 1.0.

### 9.1 Inputs read
- `cursorPos = playfield.Cursor.ActiveCursor.DrawPosition` (Vector2, float). The cursor container
  (`O/UI/OsuPlayfield.cs:49`, added in `G/Rulesets/UI/Playfield.cs:139-146`) has `RelativeSizeAxes = Both`
  (`F/osu.Framework/Graphics/Cursor/CursorContainer.cs:24-31`). It always receives positional input, even when hidden
  (`:66-69`), and is `IRequireHighFrequencyMousePosition`. `OnMouseMove` sets `ActiveCursor.Position = e.MousePosition`
  (`:71-75`), where `MousePosition = Target.Parent.ToLocalSpace(screenPos)` (`F/.../Input/Events/UIEvent.cs:42,52`), that is,
  the **playfield-local (osu!pixel) position**. It is refreshed in P2a (if the position changed) and in P2c (every step).
  So in P3 it is the P2 cursor of this step after a screen→playfield float round trip. `OsuCursor` has no relative position
  axes, so `DrawPosition == Position`.
- `playfield.HitObjectContainer.AliveEntries`: the alive top-level DHOs, before this step's P4 (objects that become alive at
  `t` are moved from `t+1` on). Enumeration is dictionary order, but each object's update depends only on itself and
  `cursorPos`, so **order does not matter**.
- `playfield.Clock.ElapsedFrameTime` = `t - t'` (double, ≥ 0 in forward replay).

### 9.2 Damping primitive (`F/osu.Framework/Utils/Interpolation.cs:18,27-33,47-51`; double only, no float overloads)
```
DampContinuously(cur, target, halfTime, elapsed) = Lerp(cur, target, 1 - Math.Pow(0.5, elapsed / halfTime))
Lerp(a, b, k) = a + (b - a) * k
```
`Damp` throws only for `base ∉ [0,1]`, which cannot happen with 0.5. `Math.Pow` is glibc `pow` (trust boundary).

### 9.3 Magnetised `Update` (:47-81), per alive entry
```
case DrawableHitCircle c:  easeTo(c, cursorPos)
case DrawableSlider s:     easeTo(s, s.HeadCircle.Result.HasResult ? cursorPos - s.Ball.DrawPosition : cursorPos)
(spinners untouched)
easeTo(h, dest):
  double L = Lerp(3000, 40, (double)AttractionStrength)          -- = 3000 + (40-3000)*s
  float x = (float)DampContinuously((double)h.X, (double)dest.X, L, Elapsed)
  float y = (float)DampContinuously((double)h.Y, (double)dest.Y, L, Elapsed)
  h.Position = (x, y)
```
`s.Ball.DrawPosition` is the ball position inside the slider. It is set in the previous step's P5
`DrawableSlider.UpdateAfterChildren` → `Ball.UpdateProgress(clamp((t'-Start)/Duration,0,1))` →
`Position = slider.CurvePositionAt(progress)` (`DrawableSliderBall.cs:64-67`). It is relative to the slider DHO.
`HasResult` covers both hit and miss.

### 9.4 Repel `Update` (:48-95), per alive entry (including spinners for the destination maths)
```
dest = Vector2.Clamp(2 * d.Position - cursorPos, (0,0), (512,384))          -- float ops
if d.HitObject is Slider sl:
    b = CalculatePossibleMovementBounds(sl)          -- O/Utils/OsuHitObjectGenerationUtils.Reposition.cs:266-303
    dest = Vector2.Clamp(dest, (b.Left, b.Top), (b.Right, b.Bottom))
case circle: easeTo(circle, dest)
case slider: easeTo(slider, HeadCircle.Result.HasResult ? dest - Ball.DrawPosition : dest)
easeTo(h, dest):
  double L = Vector2.Distance(h.Position, cursorPos) / (0.04 * (double)RepulsionStrength + 0.04)
  x, y as in MG with halfTime L
```
- `CalculatePossibleMovementBounds`: float min/max over `slider.Path.CalculatedPath` (`MathF.Min/Max`), then
  `radius = (float)slider.Radius`, `minX -= r; minY -= r; maxX += r; maxY += r`, and
  `left = -minX; right = 512 - maxX; top = -minY; bottom = 384 - maxY`. It returns
  `RectangleF(left, top, right-left, bottom-top)`, so `Right = left + (right-left)` and `Bottom = top + (bottom-top)`
  **recomputed in float** (these need not equal `right`/`bottom` bit-for-bit). `Left/Top/Right/Bottom` are `X, Y, X+Width, Y+Height`
  (`F/osu.Framework/Graphics/Primitives/RectangleF.cs:86-104`).
- osuTK `Vector2.Clamp(v, min, max)`: componentwise. `Vector2.Distance`: `(float)Math.Sqrt` of the float sum of squares.
  **Both need confirming from the osuTK assembly** (not in the source tree) before formalising.
- **NaN hazard**: if the cursor equals `h.Position` exactly, `L = 0`. With `Elapsed > 0`: `elapsed/0 = +∞`, `pow(0.5, ∞) = 0`,
  so the object jumps to `dest`. With `Elapsed == 0` (two replay frames with the same time give zero-length steps, lazer-map
  §2.2): `0/0 = NaN`, so the position becomes **NaN** and the object can no longer be hit. The model must reproduce this
  (IEEE semantics).
- MG has no such hazard (`L >= 40`). With `Elapsed == 0` both mods leave positions unchanged (`pow(0.5,0)=1`, `k=0`, so
  `a + (b-a)*0 = a` exactly for finite values).

### 9.5 Consequences and timing
- Positions written in P3 are seen in the same step by P5 consumers (`SliderInputManager.Update` uses `slider.ToLocalSpace`,
  so tracking follows the moved slider) and by the next step's P2 hit tests and hover.
- A DHO keeps its position while alive. `UpdatePosition` resets it only on Position/StackHeight bindable changes
  (`DrawableHitCircle.cs:104-106,132-135`), and pooled re-use re-applies `StackedPosition`.
- Repel's `2*Position - cursor` uses the already-moved position, so it is a feedback loop.
- The result depends on the step schedule (§0, D9). FR makes objects alive earlier, so they move for longer (§12.1).

---------------------------------------------------------------------------------------------------

## 10. Target Practice — runtime parts (`O/Mods/OsuModTargetPractice.cs`)

Interfaces: `ModWithVisibilityAdjustment, IApplicableToDrawableRuleset, IApplicableToHealthProcessor, IApplicableToDifficulty,
IApplicableFailOverride, IHasSeed, IHidesApproachCircles` (:34-35). Incompatible: base + `IRequiresApproachCircles`
(Traceable, AD), Random, SpunOut, StrictTracking, SuddenDeath, Depth, DifficultyAdjust (:43-52). Settings:
`Seed: int?` (null → `RNG.Next()` at :162), `Metronome: bool` true (audio only, :55-56, :335-339). Multiplier 0.01 (V2).

- **AR**: `ApproachRate *= 0.5f` (float, :119-122). Hook in difficulty-rate-fail.md.
- **Fail**: `FailConditions += result.Type.AffectsCombo() && !result.IsHit` (:106-112), `PerformFail` true.
  This is an SD-equivalent, specified in difficulty-rate-fail.md.
- **Beatmap regeneration** (`ApplyToBeatmap`, :160-191; uses `new Random(Seed)` and `NextDouble`): to be specified
  in transform-mods.md. Facts the runtime depends on:
  - New `HitCircle`s get **`ApplyDefaults` before `StartTime` is set** (:175-179). So `Kiai` is evaluated at time 0
    (`G/Rulesets/Objects/HitObject.cs:158`), which matters for the distance multiplier at :289. HitWindows and
    `TimePreempt` do not depend on time.
  - This runs at the `IApplicableToBeatmap` stage, i.e. **after** stacking and `IApplicableToHitObject`. TP circles
    therefore have `StackHeight = 0` and are not flipped by HR or reflected by MR.
  - `FirstObject` (for the visibility rule) is the first TP circle (`base.ApplyToBeatmap` at :190).
- **Scale transform** (`ApplyNormalVisibilityState`, :132-152). On each state update of a `DrawableHitCircle` that is not
  the first object (when `IncreaseFirstObjectVisibility`, default true, `ModWithVisibilityAdjustment.cs:76-85`):
  `BeginAbsoluteSequence(S - P)`: `ScaleTo(0.5f)` instantly, then `ScaleTo(1f, P)` with `Easing.None`. This is the DHO's
  own `Scale`; the CS scale is on the inner `scaleContainer` (`DrawableHitCircle.cs:66-106`). So the **HitReceptor's
  screen-space radius is multiplied** by `0.5 + 0.5*clamp((τ-(S-P))/P, 0, 1)`, where `τ` is the time transforms were last
  updated (previous step's P5 for P2 hit tests). The transform evaluation formula is in transform-mods.md (shared with
  Grow/Deflate). The first object has no transform (`ApplyIncreasedVisibilityState` is empty, :128-130), so it is full size.
  `FadeColour` and `ApproachCircle.Hide` are visual.

---------------------------------------------------------------------------------------------------

## 11. Autoplay / Cinema (note)

`ModAutoplay : ICreateReplayData` (`G/Rulesets/Mods/ModAutoplay.cs:14`). `OsuModAutoplay.CreateReplayData` returns
`new OsuAutoGenerator(beatmap, mods).Generate()` (`O/Mods/OsuModAutoplay.cs`). Cinema additionally hides the drawable ruleset
with `AlwaysPresent = true` (`G/Rulesets/Mods/ModCinema.cs:18-23`), so input is unaffected, and has `PerformFail() = false`.
User `.osr` files never carry AT/CN, because they are not submittable. If one appears, the model can evaluate the generated
replay (§4.3) with the same pipeline. Out of scope for the canonical evaluator; reject or flag it.

---------------------------------------------------------------------------------------------------

## 12. Other mods: judgement relevance arguments

### 12.1 Freeze Frame — RELEVANT (lifetime) (`O/Mods/OsuModFreezeFrame.cs`)
`IApplicableToDrawableHitObject, IApplicableToBeatmap`. Incompatible: AD, Transform, Depth, Hidden (+ base). No settings.
Multiplier 1.0 (with FL: `1 + (fl-1)/2`).
- `ApplyToBeatmap` (:38-85) runs after ApplyDefaults and stacking:
  ```
  lastNewComboTime = 0
  for obj in top-level OsuHitObjects in order:
      if obj.NewCombo: lastNewComboTime = obj.StartTime
      adjust(obj)
  adjust(o): if o is not Spinner: o.TimePreempt += o.StartTime - lastNewComboTime
             nested: skip SliderTick; SliderRepeat only while repeatCount <= 2 (the first 3 repeats); others recurse
  ```
  (double). `OsuBeatmapProcessor.PreProcess` forces `NewCombo` on the first non-spinner and after spinners
  (`O/Beatmaps/OsuBeatmapProcessor.cs:29-42`), so the first object's preempt, and hence `GameplayStartTime`, is unchanged.
  Spinner nested ticks also get adjusted, which does not matter (their lifetimes are spinner-managed).
- Effects on judgement:
  - (a) DHO `LifetimeStart = StartTime - TimePreempt` (`O/UI/OsuPlayfield.cs:225-235`), so objects are alive earlier. They
    consume presses while hovered (§0) and can early-Miss inside the 400 ms miss window whenever the base preempt is below
    400 (AR > 10 via DA extended limits).
  - (b) MG/RP move objects for longer.
  - (c) Grow/Deflate/SpinIn/TP-scale transform durations use `TimePreempt` (transform-mods.md).
  - (d) The AP generator's `waitTime` uses it (§4.3).
  - The approach-circle rescale (:89-104) is visual.
  The StartTimeOrdered/Legacy hit policies only look at objects *earlier* than the one being hit, so extra later alive
  objects do not change them.

### 12.2 Flashlight / Blinds — irrelevant
- FL (`O/Mods/OsuModFlashlight.cs`, `G/Rulesets/Mods/ModFlashlight.cs`): overlay drawable. Its `OnMouseMove` returns
  `base.OnMouseMove(e)` (false), so it does not block (:73-83). No `OnHover` or `OnPressed`. It reads combo and slider
  `Tracking` (OnUpdate, :49-52, :68-72) and only writes its own visual state. Rank: `AdjustRank` gives X→XH, S→SH
  (`ModFlashlight.cs:64-77`). Multiplier is a function of settings (difficulty-rate-fail.md).
- BL (`O/Mods/OsuModBlinds.cs`): overlay boxes with no handlers. `ApplyToHealthProcessor` only *listens* to
  `Health.ValueChanged`. `AdjustRank` is the identity.

### 12.3 Approach Different — irrelevant
Approach-circle scale transforms only (`O/Mods/OsuModApproachDifferent.cs:36-45`; `nameof(Scale)` is the string "Scale").
The ApproachCircle is a visual sibling of the HitReceptor (`DrawableHitCircle.cs:66-98`). Settings: `Scale` float 4
`[1.5,10]` p0.1, `Style` enum (default Gravity). Multiplier 0.7.

### 12.4 Muted — irrelevant
Volume adjustments, metronome in FrameStableComponents (it does not touch processors), combo-driven volume transforms on the
ScoreProcessor drawable (`G/Rulesets/Mods/ModMuted.cs:61-92`). Volume has no effect on rate or clocks.

### 12.5 No Scope / Bloom — irrelevant
- NS (`O/Mods/OsuModNoScope.cs:33-47`) sets `Cursor.Alpha` and `Smoke.Alpha` in P3. The cursor container propagates
  positional input regardless of visibility (`CursorContainer.cs:66-69`; `OsuCursorContainer.cs:127`). Smoke never affects
  judgement. `PeriodTracker(spinner periods)` would throw only for `EndTime <= StartTime - 100`.
- BM (`O/Mods/OsuModBloom.cs:77-85`) sets `OsuCursor.ModScaleAdjust` (visual cursor size).

### 12.6 Bubbles — irrelevant
`DisplayJudgements = false` is checked **after** `hitPolicy.HandleHit` (`O/UI/OsuPlayfield.cs:189-196`). Bubbles are pooled
drawables in Overlays with no input handlers. It only reads results and combo (`O/Mods/OsuModBubbles.cs`).

### 12.7 Synesthesia — irrelevant
Colours on `HitObjectApplied` / `OnUpdate` (`O/Mods/OsuModSynesthesia.cs:24-50`). Multiplier 0.99.

### 12.8 Touch Device — irrelevant
`OsuModTouchDevice : ModTouchDevice` has only the `IApplicableMod` marker (`O/Mods/OsuModTouchDevice.cs`,
`G/Rulesets/Mods/ModTouchDevice.cs:11`). Its uses are the resume overlay type (`O/UI/DrawableOsuRuleset.cs:70-76`, pause
only), difficulty/pp skills, the legacy bit (`O/OsuRuleset.cs:143-144,170-171`), and touch detection in song select/player.
The live `OsuTouchInputMapper` reacts only to real touches (`O/UI/OsuTouchInputMapper.cs:65`). Multiplier 1.0.

---------------------------------------------------------------------------------------------------

## 13. Mirror / Random interplay with input

- Neither mod touches input or replay coordinates: no replay flipping exists anywhere in `G/Scoring/Legacy`, `G/Rulesets/Replays`
  or `O/Replays` for HR or MR. Replays are recorded in the transformed space. Both act purely at beatmap level (MR: `IApplicableToHitObject`, `O/Mods/OsuModMirror.cs:23-41`;
  RD: `IApplicableToBeatmap` with `new Random((int)Seed)`, `O/Mods/OsuModRandom.cs:47-49`). See transform-mods.md.
- Interplay is only through derived consumers:
  - the AP/Autoplay generator uses the transformed playable beatmap;
  - AL/SG periods use transformed objects' times (MR/RD do not change times);
  - Relax reads hover against transformed positions.
- TP circles are generated after MR/HR (§10), so MR has no effect on TP positions.

---------------------------------------------------------------------------------------------------

## 14. Interactions and ordering hazards (P3 is in mod-list order)

| Combination | Hazard |
|---|---|
| RX (legacy) + BR / DP / RP | RX's `IsMouseInFollowArea` (`slider.ToLocalSpace`) runs in P3. Whether BR's container rotation, Depth's per-step position/scale, or Repel's move for `t` has already happened depends on **mod order**. Hover flags (P2) and the press hit test (P3, IsHovered flag) are not affected by order. **Model mod order explicitly.** |
| AP + DP / BR | AP's injection recomputes hover in P3 with the geometry as of that moment (order-dependent). Hover only matters for presses (next step's P2 recomputes it) and RX (incompatible), so it is harmless. MouseMove consumers read the position, not the geometry, so no hazard. |
| AP + replay positions | alternating replay/AP cursor (§4.2) |
| MG/RP + FR | earlier aliveness gives longer movement (§9.5, §12.1) |
| AL/SG + blocked press | still held for tracking and spinner (§5.2) |
| SO + WU/WD/AS | rate ratio is not exactly 1 (§6) |
| ST + NaN-SV sliders | extra ticks (§7.1) |
| CL ClassicNoteLock + AP | hittable range 200 (§4.1, §8) |
| TP + HR/MR | TP positions are unaffected by flip/mirror (§10) |
| Relax + SpunOut | spinner holding irrelevant (§6) |

Independent pairs (no shared state): AL/SG vs any other P3 mod (only `LastAcceptedAction`); NS/BM (visual).

## 15. Difftest checklist (to add to the fuzz/synthetic corpus)
1. Stable RX replays (synthesised presses): 2B sliders, overlapping circles, notelock with Classic.
2. Lazer RX replays: confirm the no-op.
3. AP (stable and lazer) with sliders and spinners: confirm the alternation in §4.2 and the frame-advance lag under the
   catchup vs dense1ms schedules.
4. AL/SG: same-key repeats, breaks, a first object that is a slider/spinner (`V = StartTime`), and blocked-key slider tracking.
5. SO with DT/HT/WU and long first steps.
6. ST with NaN-SV maps; tracking lost before the head is hit.
7. MG/RP: schedule sensitivity; RP with duplicate-time frames and the cursor exactly on an object (NaN path).
8. FR with DA AR>10; FR + MG.
9. TP seeds (generation in transform-mods.md) plus the scale transform for early hits.
10. Mod-order permutations for RX+RP and RX+BR.
