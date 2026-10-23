# Mods: difficulty, rate, fail, Classic, Mirror, score multiplier (lazer 2026.1005.0-lazer)

Scope: EZ, NF, HT, DC, HR, SD, PF, DT, NC, DA, AC, WU, WD, AS, `ModTimeRamp`/`ModRateAdjust` bases, CL, SV2, MR,
AT/CN (only to say they don't matter), and `OsuScoreMultiplierCalculatorV2`. Random, TP, HD, FL and the
input/position mods are covered in other docs.

Paths: `L/` = `~/lazerproof/lazer`, `F/` = `~/lazerproof/osu-framework/osu.Framework`,
`G/` = `L/osu.Game`, `O/` = `L/osu.Game.Rulesets.Osu`. Line numbers match the pinned checkouts.
Types: `float` = IEEE binary32, `double` = binary64, `decimal` = .NET 96-bit decimal. `BeatmapDifficulty` fields
(CS/HP/OD/AR) are `float`.

Items marked **[verify]** were .NET runtime internals taken from dotnet/runtime source knowledge. All of them are now
**[verified]**: each one names the `nettest` op (differential test against .NET 10.0.13 / the real osu-framework and
osuTK binaries, `docs/net-float.md` "Library primitives") or the `nettest lazer` probe (lazer's own `APIMod.ToMod`)
that checks it. The Lean definitions are in `model/OsuModel/Net/{Decimal,Framework,Random,SysMisc}.lean`.

---------------------------------------------------------------------------------------------------

## 0. Summary for modellers

1. **Rates never change hit windows, preempt, object times, health drain or spinner requirements.** All of these are in
   gameplay (track) time. A rate has four effects:
   (a) spinner rotation is multiplied by `|GetTrueGameplayRate()|`;
   (b) the value of `JudgementResult.GameplayRate`, which affects no score or statistic;
   (c) in live or real-time playback, how wall-clock time maps to gameplay time (the step schedule). Canonical oracle
   schedules are already in gameplay time and don't depend on the rate;
   (d) the score multiplier.
   AdaptiveSpeed also has internal dynamics that feed (a).
2. Difficulty mods mutate the `float` `BeatmapDifficulty` fields in **mod-list order**. The order matters only for
   non-commuting pairs (for example HR + TP).
3. Fail mods add `FailConditions` (SD/PF) or call `TriggerFailure` directly (AC). Whether the fail goes through is
   decided by `All(IApplicableFailOverride.PerformFail())` in **mod-list order, short-circuiting**. EZ's extra lives
   live inside that call, so mod order matters for EZ+NF and EZ+SD.
4. Mod settings come from JSON. Doubles/ints go through `BindableNumber.setValue` (clamp, then `decimal` round-half-even
   to `Precision`). DA's `DifficultyBindable` (`float?`) is **only clamped, never precision-snapped**, and its clamp
   always uses the *extended* range, whatever `ExtendedLimits` says.
5. The score multiplier is a product of double factors. Combination rules go first, then single rules in
   **mod-list order** (floating-point product order matters).

---------------------------------------------------------------------------------------------------

## 1. Application order (Player + GetPlayableBeatmap)

`Player.load` (`G/Screens/Play/Player.cs:227-336`):

| # | Step | Where |
|---|---|---|
| 0 | `gameplayMods = Mods.Value.Select(m => m.DeepClone())`. List order is kept. **No compatibility check** (only UnknownMod and ruleset checks), so lazer applies incompatible combos as-is. | `Player.cs:229-249` |
| 1 | `GetPlayableBeatmap(ruleset, gameplayMods)`: | `G/Beatmaps/WorkingBeatmap.cs:277-352` |
| 1a | `IApplicableToBeatmapConverter` (none here) → `Convert` → `IApplicableAfterBeatmapConversion` (ST only) | :291-305 |
| 1b | **`IApplicableToDifficulty.ApplyToDifficulty(converted.Difficulty)`**, each mod in list order: EZ, HR, DA (+TP) | :308-315 |
| 1c | `IApplicableToBeatmapProcessor` (none) → `PreProcess` → `ApplyDefaults` per object (TimePreempt, HitWindows.SetDifficulty(OD), spinner spins, nested objects) | :317-333 |
| 1d | **`IApplicableToHitObject`**: for each mod (list order), for each top-level object: HR (vertical reflect), MR (reflect), CL (`ClassicSliderBehaviour`) | :335-342 |
| 1e | `PostProcess` (stacking: uses reflected positions and AR-modded preempt) | :344 |
| 1f | **`IApplicableToBeatmap`**: WU/WD (`ModTimeRamp.ApplyToBeatmap`: ramp bounds), AS (preceding end times) | :346-350 |
| 2 | `CreateDrawableRulesetWith(playable, gameplayMods)`. `DrawableRuleset.load`: `IApplicableToDrawableRuleset` (CL: LegacyHitPolicy; NC: beat samples; CN: hide) and `IReadFromConfig` (NF: HUD), in list order. Then objects load: `IApplicableToDrawableHitObject` per DHO (CL, AS), for pooled DHOs too, nested included, before `Apply` | `G/Rulesets/UI/DrawableRuleset.cs:198-222,365-374`; `G/Rulesets/UI/Playfield.cs:405-415` |
| 3 | `ScoreProcessor.Mods.Value = gameplayMods; ApplyBeatmap(playable)`, which computes the multiplier (§10) | `Player.cs:260-262`; `G/Rulesets/Scoring/ScoreProcessor.cs:212-221,418-425` |
| 4 | Health processor: the first `IApplicableHealthProcessor` (CL with `ClassicHealth`) → `OsuLegacyHealthProcessor`, else `OsuHealthProcessor`. Both use `drainStartTime = HitObjects[0].StartTime`. Then `ApplyBeatmap` | `Player.cs:266-268` |
| 5 | `DrawableRuleset.NewResult += r => { HealthProcessor.ApplyResult(r); ScoreProcessor.ApplyResult(r); ... }`. **Health first, then score** | `Player.cs:399-404` |
| 6 | `HealthProcessor.Failed += onFail` | `Player.cs:416` |
| 7 | On processor LoadComplete: `IApplicableToScoreProcessor.ApplyToScoreProcessor` (AC), then `IApplicableToHealthProcessor.ApplyToHealthProcessor` (SD/PF/AC/EZ). Fail-condition invocation order = mod-list order | `Player.cs:420-430` |
| 8 | `Player.LoadComplete`: `IApplicableToPlayer` (EZ captures `retries`; CN), `IApplicableToHUD`, **`IApplicableToTrack.ApplyToTrack(GameplayClockContainer.AdjustmentsFromMods)`** (rate mods bind their bindables into the aggregate) | `Player.cs:1148-1155` |
| 9 | Every FSC step: `Playfield.Update` runs each `IUpdatableByPlayfield.Update(playfield)` in mod-list order (WU/WD, AS) **before** any DHO in the same step (children update after the parent's `Update`) | `Playfield.cs:262-273` |
| 10 | Fail: `onFail` → `CheckModsAllowFailure()` = `Mods.OfType<IApplicableFailOverride>().All(m => m.PerformFail())` (LINQ `All` stops at the first `false`) | `Player.cs:178,957-967` |

`ReplayPlayer.CheckModsAllowFailure` returns `false` (and calls no `PerformFail`) until
`GameplayClockContainer.CurrentTime >= lastFrameTime`, unless the mods contain `ModAutoplay`
(`G/Screens/Play/ReplayPlayer.cs:44,55-68`). See §7 for what this means for EZ lives.

Mod-list order in practice:
- Stable `.osr` (version < 30000000): `OsuRuleset.ConvertFromLegacyMods` order is
  NC|DT, PF|SD, AP, CN|AT, EZ, FL, HT, HR, HD, NF, RX, SO, TP, TD, SV2 (`O/OsuRuleset.cs:96-148`).
  The NC bit beats DT and PF beats SD (stable sets both bits).
  Then `OsuModClassic` with defaults is appended (`G/Scoring/Legacy/LegacyScoreDecoder.cs:88-92`).
  No stable mapping exists for DC, MR or any lazer-only mod.
- Lazer `.osr`: `LegacyReplaySoloScoreInfo.Mods` JSON array order (`LegacyScoreDecoder.cs:127-134`), via `APIMod.ToMod`.

---------------------------------------------------------------------------------------------------

## 2. Mod settings: deserialisation and BindableNumber semantics

### 2.1 Path
`APIMod.ToMod` (`G/Online/API/APIMod.cs`): `ruleset.CreateModFromAcronym`. Then for each `[SettingSource]` property in
`GetSettingsSourceProperties()` order (`G/Configuration/SettingSourceAttribute.cs:253-274`), it looks up
`settings[property.Name.ToSnakeCase()]` and calls `Mod.CopyAdjustedSetting(bindable, value)` (`G/Rulesets/Mods/Mod.cs:223-238`)
→ `IParseable.Parse(value, InvariantCulture)`. A missing key leaves the default. An exception is logged and the default
is kept.

The order is `Type.GetProperties` reflection order **[verified: `nettest lazer` prints `GetSettingsSourceProperties()`
for every osu! mod]**. Observed orders: WU/WD `initial_rate, final_rate, adjust_pitch`; HT/DT `speed_change,
adjust_pitch`; AC `minimum_accuracy, accuracy_judge_mode, restart`; DA `circle_size, approach_rate, drain_rate,
overall_difficulty, extended_limits`; CL `no_slider_head_accuracy, classic_note_lock, always_play_tail_sample,
fade_hit_circle_early, classic_health`; RD `angle_sharpness, seed`; FL `follow_delay, size_multiplier,
combo_based_size`. It matters only for the WU/WD cross-constraints (§6.3).

JSON values come from Newtonsoft into `Dictionary<string, object>`: integers become `long`, non-integers `double`,
plus `bool` and `string`. Enums are serialised as integers.

`Bindable<T>.Parse` (`F/Bindables/Bindable.cs:252-302`):
- `input is T` → `Value = t` (a `double` into `BindableDouble`, a `bool` into `BindableBool`).
- `BindableBool`: also accepts the strings `"1"`/`"0"` (`F/Bindables/BindableBool.cs:15-25`).
- otherwise, enum → `Enum.Parse(type, input.ToString())` (so `1` or `"Vertical"` both work).
- otherwise `Convert.ChangeType(input, underlyingType, Invariant)`: `long`→`double` (exact for |n| < 2^53), `long`→`int`
  (overflow throws, so the default is kept), `double`→`float` (round-to-nearest), `double`→`int` (`Convert.ToInt32`
  rounds half-to-even), `string`→`double.Parse`.
- `null` → only nullable types (`DifficultyBindable`): `Value = null`.

Player's `DeepClone` (`Mod.cs:151-175`) copies each setting via `BindTo`+`UnbindFrom`, which re-runs the
Value setter. That is idempotent for all values produced above.

### 2.2 `BindableNumber<T>.Value` setter (`F/Bindables/BindableNumber.cs:69-90`, `RangeConstrainedBindable.cs:45-49,256`)
```
setValue(v):
  decPrecision = decimal.CreateTruncating(Precision)            // [verified op 111/113] = (decimal)Precision except
                                                                //   saturation at ±2^96 and NaN -> 0.0m (scale 1)
  if decPrecision > 0:
      a = decimal.CreateTruncating(T.Clamp(v, MinValue, MaxValue))   // T.Clamp = Min(Max(v, min), max), NOT Math.Clamp
      a = decimal.Round(a / decPrecision) * decPrecision        // decimal division; Round = MidpointRounding.ToEven
      base.Value = T.CreateTruncating(a)                        // decimal -> T, see 2.3
  else
      base.Value = v
  RangeConstrainedBindable: candidate = T.Clamp(that, MinValue, MaxValue)
  Bindable: stored only if !EqualityComparer<T>.Default.Equals(old, candidate)   (else the old value is KEPT)
```
**[verified: ops 146–149 run the real `BindableDouble`/`BindableFloat` (initialiser + `Value =`), 0 failures; Lean
`Framework.Bindable.BD/BF`]**. Corrections found by the test:
- `T.Clamp` is `double.Clamp`/`float.Clamp` = `Min(Max(v, min), max)` with the IEEE-754:2019 `Math.Max/Min`, not
  `Math.Clamp`: `-0` clamped to `[0, x]` gives `+0`; NaN stays NaN; `min > max` throws ArgumentException.
- NaN with a positive precision: `CreateTruncating(NaN) = 0.0m`, so the stored value is `clamp(0)`, not NaN.
- The final `Equals` check keeps the **old** value when the candidate is equal to it: `+0`/`-0` keep the old sign (and
  NaN keeps the old NaN). For example `Value = -0.004` with precision 0.01 snaps to `-0.0`, which is `Equals` to the
  current `+0.0`, so the bindable stays `+0.0`. The model therefore threads the bindable state: constructor
  (`RangeConstrainedBindable` re-applies the default with the type's min/max, `BindableNumber` re-applies it with
  the default precision), then each initialiser setter in written order (`MinValue`/`MaxValue`: no-op if `Equals`,
  else clamp-only re-apply; `Precision`: no-op if `==`, throws if `<= 0`, else snapping re-apply), then `Value = v`.
- Through lazer: `nettest lazer` deserialises random JSON values for all 18 double/float mod settings with the real
  `APIMod.ToMod` and checks each against `BD/BF.init(default, min, max, precision).setValue(v)` (ops 230/231,
  0 failures).
- The default precision for `double` is `double.Epsilon`, and `(decimal)double.Epsilon == 0m`. So a BindableDouble with
  no explicit Precision is **clamped only** (for example AS `SpeedChange`). The `float` default is `float.Epsilon`, which
  also becomes 0. For `int` the precision is 1, so the setter is effectively a clamp.
- The constructor applies the defaults. Object initialisers (`MinValue`, `MaxValue`, `Precision`, `Default`, `Value`)
  re-apply `setValue` in written order.

### 2.3 decimal conversions **[verified]** (decompiled `System.Decimal.DecCalc`, .NET 10.0.13)
`double → decimal` (`VarDecFromR8`, used by `decimal.CreateTruncating(double)` through
`Double.TryConvertToTruncating`, which saturates at `|x| >= 7.922816251426434E+28` (= 2^96) to ±decimal.MaxValue and
maps NaN to `0.0m` — mantissa 0, **scale 1**) **[verified ops 111/112: exact `decimal.GetBits` match]**:
```
exp = biasedExp(x) - 1022; if exp < -94 -> 0m; if exp > 96 -> overflow (saturated before reaching here)
dbl = |x|; power = 14 - ((exp*19728) >> 16)                       // arithmetic shift
if power >= 0: power = min(power, 28); dbl *= 10^power (double mul, rounded)
else if power != -1 || dbl >= 1e15: dbl /= 10^-power (double div) else power = 0
if dbl < 1e14 && power < 28: dbl *= 10; power++
mant = round_half_even(dbl) as uint64      // (long)dbl then compare frac with 0.5; same result as SSE4.1 path
if mant == 0 -> 0m
value = ±mant * 10^-power   (if power < 0: mant * 10^-power, exact)  // trailing-zero stripping changes scale only
```
That is about "15 significant digits, computed in double arithmetic". Examples: `(decimal)1.135 = 1.135m` (the double is
1.13499999999999979…), and `(decimal)0.01 = 0.01m`.

Trailing-zero stripping: at most `min(power, 14)` zeros, greedily 8, 4, 2, 1 (exactly `min(trailing zeros, power, 14)`).

`float → decimal` (`VarDecFromR4`) is the same algorithm with SNGBIAS 126, `power = 6 - ((exp*19728)>>16)`,
thresholds 1e7/1e6, a 7-digit `uint` mantissa and stripping of at most 6 zeros (4, 2, 1). The arithmetic is in
double **[verified ops 113/114]**.

`decimal → double` (`VarR8FromDec`): `((double)lo64 + (double)hi32 * 1.8446744073709552e19) / 10^scale`
(double ops), negated (sign flip, so `-0m → -0.0`) if the sign is set. `decimal → float` = `(float)VarR8FromDec(d)`
(double rounding) **[verified ops 115/116, also via `double/float.CreateTruncating(decimal)`]**.

Decimal `/` (`VarDecDiv`), `*` (`VarDecMul`/`ScaleResult`) and `Math.Round(decimal)` (`InternalRound`, ToEven) are
modelled with their exact control flow (`SearchScale`, `OverflowUnscale`, `Unscale`, sticky half-even rounding,
sign-bit and scale of the result) **[verified ops 117–119: exact `GetBits` match incl. DivideByZero/Overflow]**. For
precisions `10^-k` the quotient is exact; for the Wiggle precision `0.100000001490116m` it is a 28/29-digit rounded
quotient (transform-mods §3).

**Practical consequence (checked by simulating the algorithm above in Python):** for precision 0.01 and 0.001, every
on-grid value `k/100` (double nearest) maps to itself. Off-grid inputs snap with half-even on the 15-digit decimal:
`1.125→1.12`, `1.135→1.14`, `1.145→1.14`, `1.005→1.0`, `1.015→1.02`, `1.2345→1.23`, `0.9095→0.91`.
The result is always the double nearest `k·p` (`k/100` correctly rounded), because `VarR8FromDec` does one exact-operand
division.

### 2.4 `DifficultyBindable` (DA) (`G/Rulesets/Mods/DifficultyBindable.cs`)
It is a `Bindable<float?>`, **not** a BindableNumber. Its `Value` setter (:114-130), for non-null `v`:
```
CN.Min = clamp(min(CN.Min, v), ExtendedMinValue ?? MinValue, MinValue)
CN.Max = clamp(max(CN.Max, v), MaxValue, ExtendedMaxValue ?? MaxValue)
stored = Math.Clamp(v, CN.Min, CN.Max)        // float clamp
```
So stored = `clamp(v, ExtMin ?? Min, ExtMax ?? Max)` **whatever `ExtendedLimits` is set to**, and **no 0.1 precision
snapping happens** (the 0.1f precision lives on the UI-only `CurrentNumber`). JSON `5.3` → `(float)5.3` = 5.30000019….
`null` (or a missing key) means "don't override".

---------------------------------------------------------------------------------------------------

## 3. Difficulty mods

All of them run in step 1b, on `converted.Difficulty` (a clone, so `BeatmapInfo.Difficulty` stays unmodded). The
arithmetic is `float` (RyuJIT does float ops in binary32). `Math.Min(float, float)`.

### 3.1 Easy — `OsuModEasy : ModEasyWithExtraLives : ModEasy`
Interfaces: `IApplicableToDifficulty`, `IApplicableFailOverride`, `IApplicableToPlayer`, `IApplicableToHealthProcessor`.
- `ApplyToDifficulty` (`G/Rulesets/Mods/ModEasy.cs:23-28`, `O/Mods/OsuModEasy.cs:14-19`): `CS *= 0.5f; AR *= 0.5f;
  HP *= 0.5f;` then `OD *= 0.5f`. All are exact (halving).
- Setting `Retries` (`retries`): `BindableInt(2) {Min 0, Max 10}` (`ModEasyWithExtraLives.cs:19-24`).
- `ApplyToPlayer`: `retries = Retries.Value` (:41-51). `ApplyToHealthProcessor`: binds a local `BindableDouble health`
  to `HealthProcessor.Health` (:67-70).
- `PerformFail` (:53-63): `if retries == 0 return true; health.Value = health.MaxValue (=1); retries--; return false`.
  `RestartOnFail = false`.
- Incompatible with HR, DA, AC (`ModEasy.cs:17`, `ModEasyWithExtraLives.cs:35`).
- Model state: `retriesLeft : Nat`.

### 3.2 Hard Rock — `OsuModHardRock : ModHardRock`
Interfaces: `IApplicableToDifficulty`, `IApplicableToHitObject`.
- `ApplyToDifficulty` (`G/Rulesets/Mods/ModHardRock.cs:23-28`, `O/Mods/OsuModHardRock.cs:25-32`), in this order:
  `HP = min(HP*1.4f, 10f); OD = min(OD*1.4f, 10f); CS = min(CS*1.3f, 10f); AR = min(AR*1.4f, 10f)`.
  `1.4f` = 1.39999997615814208984375 and `1.3f` = 1.2999999523162841796875. Products are rounded to float.
- `ApplyToHitObject`: `OsuHitObjectGenerationUtils.ReflectVerticallyAlongPlayfield` (§8).
- Incompatible with EZ, DA, Mirror.

### 3.3 Difficulty Adjust — `OsuModDifficultyAdjust : ModDifficultyAdjust`
Interface: `IApplicableToDifficulty`. `ApplySettings` (`ModDifficultyAdjust.cs:122-126`, `OsuModDifficultyAdjust.cs:78-84`):
`if HP != null: Difficulty.DrainRate = HP; if OD != null: OD; if CS != null: CS; if AR != null: AR`. These are
plain float assignments. Per §2.4 the values are only clamped:

| JSON key | default | Min | Max | ExtMin | ExtMax | file |
|---|---|---|---|---|---|---|
| `circle_size` | null | 0 | 10 | – | 11 | `OsuModDifficultyAdjust.cs:21-29` |
| `drain_rate` | null | 0 | 10 | – | 11 | `ModDifficultyAdjust.cs:38-46` |
| `overall_difficulty` | null | 0 | 10 | – | 11 | `ModDifficultyAdjust.cs:48-56` |
| `approach_rate` | null | 0 | 10 | **−10** | 11 | `OsuModDifficultyAdjust.cs:31-40` |
| `extended_limits` | false | bool | | | | `ModDifficultyAdjust.cs:58-59` (UI only; doesn't affect stored values) |

Downstream ranges the model must support (all in existing formulas, no special cases):
- AR ∈ [−10, 11]: `TimePreempt = (int)DifficultyRange(AR, 1800, 1200, 450)` truncates toward zero. AR −10 gives 3000 and
  AR 11 gives 300. `TimeFadeIn = 400*min(1, preempt/450)` (`O/Objects/OsuHitObject.cs:170-183`). Preempt also sets
  `GameplayStartTime = first.StartTime - max(2000, first.TimePreempt)` (`O/UI/DrawableOsuRuleset.cs:81-89`), the
  stacking threshold and DHO lifetimes.
- OD ∈ [0, 11]: windows `floor(DifficultyRange(OD, …)) - 0.5`. OD 11 gives 300 ±13.5, 100 ±51.5, 50 ±89.5
  (`O/Scoring/OsuHitWindows.cs:39-44`). Spinner RPM ranges extrapolate the same way (`O/Objects/Spinner.cs:66-77`).
- CS ∈ [0, 11]: scale formula only (radius is negative above about CS 17, so it's still positive here).
- HP ∈ [0, 11]: health increase/drain `DifficultyRange` extrapolation.
- Incompatible with EZ, HR, TP. `RequiresConfiguration = true`. Model state: four `Option Float32`.

### 3.4 Non-commuting order note
In this doc's set, only DA (a plain assignment) and HR's `min(…,10)` are order-sensitive with other
`IApplicableToDifficulty` mods. Lazer marks DA incompatible with EZ/HR/TP and HR incompatible with EZ, but doesn't
enforce it at Player. **HR+TP** is allowed. Applied as HR then TP (stable bit order), AR 9 gives `min(12.6,10)*0.5 = 5`.
Applied as TP then HR it gives `4.5*1.4f`. The model must apply in list order.

---------------------------------------------------------------------------------------------------

## 4. No Fail, Sudden Death, Perfect, Accuracy Challenge, Cinema

### 4.1 No Fail — `OsuModNoFail : ModNoFail` (`G/Rulesets/Mods/ModNoFail.cs`)
`IApplicableFailOverride`: `PerformFail() => false` (:30), `RestartOnFail = false`. Also `IApplicableToHUD` and
`IReadFromConfig`, which are UI only. No settings. Incompatible with every `ModFailCondition` (SD/PF/AC) and CN.

### 4.2 `ModFailCondition` base (`G/Rulesets/Mods/ModFailCondition.cs`)
`IApplicableToHealthProcessor` + `IApplicableFailOverride`. Setting `Restart` (`restart`), `BindableBool(false)` (:16-17).
`PerformFail() => true`, `RestartOnFail => Restart.Value` (restart only affects live UX; the evaluator reports "failed").
`ApplyToHealthProcessor`: stores `TriggerFailure` and adds `FailCondition` to `HealthProcessor.FailConditions` (:25-29).

`HealthProcessor.ApplyResultInternal` (`G/Rulesets/Scoring/HealthProcessor.cs:46-58`):
```
result.HealthAtJudgement = Health; result.FailedAtJudgement = HasFailed
if HasFailed: return
Health += GetHealthIncreaseFor(result)            // BindableDouble [0,1] clamp
if (Health.Value <= 0 + 1e-7 … i.e. AlmostBigger(0, Health)) || any FailCondition(this, result): TriggerFailure()
TriggerFailure: if HasFailed return; if Failed?.Invoke() != false: HasFailed = true      (:37-44)
```
(`Failed` = `Player.onFail`, which returns `CheckModsAllowFailure() && …`.) Fail conditions are evaluated in
subscription order and short-circuit (:83-101). Draining processors first ignore bonus or IgnoreHit results
(`DrainingHealthProcessor.cs:145-151`, per lazer-map §4.3).

Because Health runs before Score (§1 #5), the judgement that triggers SD/PF still has `FailedAtJudgement=false`. It is
**counted** by ScoreProcessor, and every later judgement is ignored (`ScoreProcessor.cs:244`).

### 4.3 Sudden Death — `OsuModSuddenDeath : ModSuddenDeath`
- `FailCondition` (`ModSuddenDeath.cs:26-28`, `OsuModSuddenDeath.cs:25-34`):
  `result.Type.AffectsCombo() && !result.IsHit`, **or** (`FailOnSliderTail` && `result.HitObject is SliderTailCircle` && `!result.IsHit`).
  AffectsCombo = {Miss, Meh, Ok, Good, Great, Perfect, LargeTickHit, LargeTickMiss, LegacyComboIncrease, ComboBreak,
  SliderTailHit} (`G/Rulesets/Scoring/HitResult.cs:183-203`). IsHit is false for {None, IgnoreMiss, Miss,
  SmallTickMiss, LargeTickMiss, ComboBreak} (:308-323).
  So SD triggers on Miss and LargeTickMiss (slider ticks/repeats, classic heads, ST tails). A non-classic tail miss is
  IgnoreMiss and a classic tail miss is SmallTickMiss; neither is combo-affecting, so only `FailOnSliderTail` catches them.
- Settings: `fail_on_slider_tail` BindableBool(false), `restart` (false).
- Incompatible with NF, CN, PF, TP.

### 4.4 Perfect — `OsuModPerfect : ModPerfect` (`G/Rulesets/Mods/ModPerfect.cs`)
- `Restart` default **true** (:26-29).
- `FailCondition` (:31-35): `(rel(J.MinResult) || rel(J.MaxResult) || rel(Type)) && Type != J.MaxResult`, where
  `rel(r) = r.AffectsAccuracy() || r.AffectsCombo()`. AffectsAccuracy = scorable and not bonus, excluding
  LegacyComboIncrease and ComboBreak (`HitResult.cs:208-223`).
  Results: any non-max circle, head, tick, repeat or (classic) slider result fails. A non-classic tail (max SliderTailHit)
  missed (IgnoreMiss) fails. A classic tail (max SmallTickHit, accuracy-affecting) missed fails. A non-classic slider
  body (IgnoreHit/IgnoreMiss) never fails. Spinner bonus never fails. A spinner (max Great) at less than Great fails.
- Incompatible with NF, CN, SD, AC.

### 4.5 Accuracy Challenge — `OsuModAccuracyChallenge : ModAccuracyChallenge` (`G/Rulesets/Mods/ModAccuracyChallenge.cs`)
Interfaces: `ModFailCondition` (so `IApplicableToHealthProcessor` and `IApplicableFailOverride`) plus `IApplicableToScoreProcessor`.
- Settings: `minimum_accuracy` `BindableDouble {Min 0.60, Max 0.999, Precision 0.001, Default 0.9}` (:54-62).
  `accuracy_judge_mode` `Bindable<AccuracyMode>()`, where the enum is `MaximumAchievable = 0` (**the default**) and
  `Standard = 1` (:64-65, 95-102). `restart` (false).
- `FailCondition => false` (:93). Instead, `ApplyToScoreProcessor` (:69-89) binds a local `Bindable<double>` to
  `ScoreProcessor.Accuracy` (Standard) or `ScoreProcessor.MaximumAccuracy` (MaximumAchievable), and on **ValueChanged**
  (no initial invocation) does `if (newValue < MinimumAccuracy.Value) TriggerFailure()`.
- `Accuracy = curMax > 0 ? cur/curMax : 1`; `MaximumAccuracy = maxBase > 0 ? (cur + (maxBase - curMax)) / maxBase : 1`
  (`ScoreProcessor.cs:391-396`), with BindableDouble clamp [0,1]. These are updated inside `ScoreProcessor.ApplyResult`
  (after the counts), so **the triggering judgement is already counted**. HealthProcessor processed this result
  first, so its `FailedAtJudgement` is false. The next result is the first one ignored.
- The check fires only when the value **changes** (exact double inequality). If a failure is refused (ReplayPlayer
  before the last frame), the next change re-checks.
- `AdjustRank` is the identity. Incompatible with NF, CN, EZ, PF.
- Model state: none beyond the processors (comparisons use the current accuracy double).

### 4.6 Autoplay / Cinema (not relevant)
`ModAutoplay : ICreateReplayData`, `UserPlayable = false` (`G/Rulesets/Mods/ModAutoplay.cs`). `ModCinema` adds
`PerformFail => false`, HUD/visual hiding (`G/Rulesets/Mods/ModCinema.cs:26-55`). The osu! versions generate an
`OsuAutoGenerator` replay (`O/Mods/OsuModAutoplay.cs`, `OsuModCinema.cs`). User replays never contain them. If they do,
`ReplayPlayer` lets them fail normally (`isAutoplayPlayback`). Multiplier 1.0. **Model: reject.**

---------------------------------------------------------------------------------------------------

## 5. Constant-rate mods

### 5.1 `ModRateAdjust` base (`G/Rulesets/Mods/ModRateAdjust.cs`)
`IApplicableToRate : IApplicableToAudio : IApplicableToTrack, IApplicableToSample`.
`ApplyToRate(time, rate) => rate * SpeedChange.Value` (:26). This is used only by `ModUtils.CalculateRateWithMods`
(UI) and `OsuAutoGenerator`. **Gameplay never calls it.** Incompatible with ModTimeRamp, ModAdaptiveSpeed and other
ModRateAdjust.

| Mod | class | `speed_change` (BindableDouble) | other settings | track binding |
|---|---|---|---|---|
| HT | `OsuModHalfTime : ModHalfTime` | 0.75 [0.5, 0.99] p0.01 (`ModHalfTime.cs:24-30`) | `adjust_pitch` BindableBool(false) (:32-33) | `RateAdjustModHelper`: SpeedChange added as **Tempo** (adjust_pitch false) or **Frequency** (true) (`RateAdjustModHelper.cs:35-62`) |
| DC | `OsuModDaycore : ModDaycore` | 0.75 [0.5, 0.99] p0.01 (`ModDaycore.cs:23-29`) | – | Frequency ← `freqAdjust = 0.75` (Default), Tempo ← `tempoAdjust = s / 0.75` (`ModDaycore.cs:31-49`) |
| DT | `OsuModDoubleTime : ModDoubleTime` | 1.5 [1.01, 2] p0.01 (`ModDoubleTime.cs:24-30`) | `adjust_pitch` false | as HT |
| NC | `OsuModNightcore : ModNightcore<OsuHitObject>` | 1.5 [1.01, 2] p0.01 (`ModNightcore.cs:33-39`) | – | Frequency ← 1.5, Tempo ← `s / 1.5` (:41-59). Also `IApplicableToDrawableRuleset` beat samples, audio only (:62-188) |

The `tempoAdjust`/`freqAdjust` BindableDoubles have default precision, so no snapping. The DC/NC callbacks run with
`runOnceImmediately` and on every SpeedChange change.

### 5.2 True gameplay rate (what spinners and `GameplayRate` see)
`GetTrueGameplayRate(clock) = (clock.Rate == 0 ? 1 : Math.Sign(clock.Rate)) * AggregateFrequency * AggregateTempo`
(`G/Screens/Play/GameplayClockExtensions.cs:14-22`). The clock is the FrameStabilityContainer
(`G/Rulesets/UI/FrameStabilityContainer.cs:104`, `Rate` :289, `manualClock.Rate = |ref.Rate|*direction` :196). Its
`AdjustmentsFromMods` is the master clock's `AudioAdjustments` (:303).

Aggregates (`F/Audio/AudioAdjustments.cs`, `F/Bindables/AggregateBindable.cs`): start at 1, multiplied left to right
by every source in add order. The first source is the component's own `Frequency`/`Tempo` bindable (1.0), then the
mod bindables. Exact values:
- HT/DT (either pitch setting): `1 * (1*1) * (1*s)` = **s** exactly.
- NC/DC: `1 * (1*1*1.5) * (1*1*(s/1.5))` = `1.5 * (s/1.5)` (DC: `0.75 * (s/0.75)`). This **is not always s**. With s =
  k/100 it differs in the last bit for k ∈ {83,84,86,87,89,90,92,93} (DC) and k ∈ {151,155,157,161,166,168,172,174,
  178,180,184,186,189,191,195,197} (NC). This was computed with IEEE doubles. The model must use the product.
- Forward playback has sign +1. Spinners use `Math.Abs(rate)`.

### 5.3 Effects of rate on gameplay quantities
| Quantity | Rate-dependent? | Source |
|---|---|---|
| Hit windows | **No**. `OsuHitWindows.SetDifficulty(OD)` only, compared against gameplay-time offsets | `O/Scoring/OsuHitWindows.cs:39-44`, `G/Rulesets/Objects/HitObject.cs:155-161` |
| TimePreempt / TimeFadeIn / lifetimes / stacking | **No** (AR only) | `O/Objects/OsuHitObject.cs:170-183` |
| Spinner `SpinsRequired` / bonus | **No** (OD and gameplay-ms duration) | `O/Objects/Spinner.cs:62-77` |
| Spinner rotation | **Yes**: `delta = (float)(delta * Math.Abs(GetTrueGameplayRate()))` before `currentRotation += delta` and `History.ReportDelta(Time.Current, delta)` | `O/Skinning/Default/SpinnerRotationTracker.cs:106-110` |
| Health drain | **No**. `Health -= DrainRate * (clamp(t) - clamp(t - elapsed))` in gameplay time; DrainRate from HP | `G/Rulesets/Scoring/DrainingHealthProcessor.cs:85-98` |
| `JudgementResult.GameplayRate` | Yes, `= GetTrueGameplayRate()` at `ApplyResult`. Only feeds `HitEvent` (UR statistics); no score effect | `G/Rulesets/Objects/Drawables/DrawableHitObject.cs:744-745`, `ScoreProcessor.cs:293` |
| FSC step cap (1000/60 ms, 1.2f×) | No. It is in gameplay ms | `FrameStabilityContainer.cs:256-277` |
| Live/real-time step schedule | Yes. Reference gameplay time advances `rate ×` wall time. The oracle's canonical schedules are given in gameplay time, so there is no effect there | `oracle/Schedule.cs` |
| Replay frame times | No (recorded in gameplay time) | |
| Score multiplier | Yes (§10) | |

---------------------------------------------------------------------------------------------------

## 6. Time-varying rate: `ModTimeRamp`, Wind Up, Wind Down

### 6.1 `ModTimeRamp` (`G/Rulesets/Mods/ModTimeRamp.cs`)
Interfaces: `IUpdatableByPlayfield`, `IApplicableToBeatmap`, `IApplicableToRate` (so also track/sample).
- `FINAL_RATE_PROGRESS = 0.75f` stored as double (0.75 exactly) (:22).
- `SpeedChange = BindableDouble(1) { Precision = 0.01 }` (no min/max) (:53-56).
- Constructor (:60-67): helper binds `AdjustPitch` and runs `FinalRate.BindValueChanged(_ => SpeedChange = ApplyToRate(+∞), true)`.
- `ApplyToBeatmap` (:80-89): `SpeedChange.SetDefault()` (1.0).
  `begin = HitObjects.First?.StartTime ?? 0`;
  `lastEnd = Any ? max over top-level objects of GetEndTime() : 0` (`G/Beatmaps/IBeatmap.cs:179`; `GetEndTime` =
  EndTime for IHasDuration, else StartTime).
  `finalRateTime = begin + 0.75 * (lastEnd - begin)`.
- `ApplyToRate(time, rate=1)` (:91-98):
  ```
  amount = (time - begin) / Math.Max(1, finalRateTime - begin)
  ramp   = Initial + (Final - Initial) * Math.Clamp(amount, 0, 1)
  return rate * Math.Round(ramp, 2)        // [verified op 58 (+ ramp-shaped and k/200-tie inputs)]: |ramp| < 1e16:
                                           //   r = ramp*100.0; r = round_half_even(r); r / 100.0  (F64.roundDigits)
  ```
- `ApplyToTrack` (:69-73): SpeedChange becomes **Frequency** (AdjustPitch true, the default) or Tempo. Then
  `FinalRate.TriggerChange()` → SpeedChange = round(Final, 2), so it equals FinalRate until the first playfield update.
- `Update(playfield)` (:100-103): `SpeedChange.Value = ApplyToRate(playfield.Clock.CurrentTime)` (FSC time). This runs
  every FSC step in `Playfield.Update`, **before DHO updates of that step**. So a spinner at step t uses the rate for t.
  SpeedChange then goes through the 0.01 decimal snap (idempotent on `k/100` values).
- True gameplay rate = `1 * SpeedChange` (one source) = SpeedChange exactly.
- Incompatible with ModRateAdjust, ModAdaptiveSpeed.

### 6.2 Settings
| Mod | `initial_rate` | `final_rate` | `adjust_pitch` | file |
|---|---|---|---|---|
| WU `ModWindUp` | 1.0 [0.5, 1.99] p0.01 | 1.5 [0.51, 2] p0.01 | BindableBool(**true**) | `G/Rulesets/Mods/ModWindUp.cs:20-34` |
| WD `ModWindDown` | 1.0 [0.51, 2] p0.01 | 0.75 [0.5, 1.99] p0.01 | true | `ModWindDown.cs:20-34` |

The osu! ruleset registers the base classes `ModWindUp`/`ModWindDown` directly (`O/OsuRuleset.cs:225`). They are
mutually incompatible.

### 6.3 Cross-constraint callbacks (these affect deserialisation)
WU (`ModWindUp.cs:38-51`): on Initial change, `if new >= Final: Final = new + 0.01`. On Final change,
`if new <= Initial: Initial = new - 0.01` (each re-snapped).
WD (`ModWindDown.cs:38-51`): on Initial change, `if new <= Final: Final = new - 0.01`. On Final change,
`if new >= Initial: Initial = new + 0.01`.
Settings are applied in property order (InitialRate, FinalRate, then AdjustPitch, **[verified: `nettest lazer`]**),
starting from the defaults. Observed through the real `APIMod.ToMod`: WU `{final_rate: 0.8}` → (0.79, 0.8);
WU `{initial_rate: 1.6, final_rate: 1.2}` → (1.19, 1.2); WU `{initial_rate: 1.99}` → (1.99, 2); WD `{final_rate: 1.5}`
→ (1.51, 1.5); WD `{initial_rate: 0.6, final_rate: 0.9}` → (0.91, 0.9). Valid lazer-produced pairs round-trip unchanged.

Model state: `begin`, `finalRateTime`, current `SpeedChange : Float64`.

---------------------------------------------------------------------------------------------------

## 7. Adaptive Speed — `ModAdaptiveSpeed` (`G/Rulesets/Mods/ModAdaptiveSpeed.cs`)
Interfaces: `IApplicableToRate`, `IApplicableToDrawableHitObject`, `IApplicableToBeatmap`, `IUpdatableByPlayfield`.
Incompatible with ModRateAdjust, ModTimeRamp, ModAutoplay.
- Settings: `initial_rate` BindableDouble(1) [0.5, 2] p0.01 (:41-47); `adjust_pitch` BindableBool(**true**) (:49-50).
- `SpeedChange = BindableDouble(1) {Min 0.4, Max 2.5}`, default precision, so it is **clamped, not snapped** (:56-60).
  Bound as Frequency or Tempo (true rate = SpeedChange exactly).
- Constants: rate range [0.4, 2.5]; per-hit change [0.9, 1.11]; miss factor 0.95; `recent_rate_count = 8` (:65-82).
- State: `targetRate : double` (init 1, :76); `recentRates : List<double>` of 8 (init 1.0, :111);
  `precedingEndTimes : Dictionary<HitObject,double>`; `ratesForRewinding : Dictionary<HitObject,double>`.
- Constructor: `InitialRate` change → `SpeedChange = v; targetRate = v` (:134-138). `ApplyToTrack` (:141-148):
  `InitialRate.TriggerChange()` (SpeedChange = targetRate = Initial), `recentRates = [Initial]×8`, bind.
- `ApplyToBeatmap` (:190-204): `objs` = depth-first pre-order over top-level and nested objects with
  `HitWindows != HitWindows.Empty`. In osu! these are `HitCircle` and `SliderHeadCircle`; sliders, ticks, repeats,
  tails, spinners and spinner ticks have `Empty` (`O/Objects/*.cs CreateHitWindows`).
  `endTimes` = sorted distinct `GetEndTime()` of `objs`. For each obj, `idx = BinarySearch(endTimes, obj.EndTime)`
  (the complement if absent), minus 1. If `idx >= 0`, `precedingEndTimes[obj] = endTimes[idx]` (the largest end time
  strictly below obj's). The first object(s) have no entry.
- `Update(playfield)` (:155-158), every step before DHOs:
  `SpeedChange = DampContinuously(SpeedChange, targetRate, 50, playfield.Clock.ElapsedFrameTime)`
  = `Lerp(cur, target, 1 - Math.Pow(0.5, elapsed/50))`, with `Lerp(a,b,t) = a + (b-a)*t`
  (`F/Utils/Interpolation.cs:18,27-33,47-51`). Then clamp [0.4, 2.5]. **This depends on the step schedule.**
- `OnNewResult` for every DHO (nested too) (:164-175). Return if `ratesForRewinding` contains the object. Return unless
  `result.Type.AffectsAccuracy()` and `precedingEndTimes` contains the object. Then:
  ```
  ratesForRewinding[obj] = recentRates[0]; recentRates.RemoveAt(0)
  rel = !IsHit ? 0.95 : clamp((obj.EndTime - prev) / (result.TimeAbsolute - prev), 0.9, 1.11)   // ±inf if denom 0 → clamped
  recentRates.Add(clamp(rel * SpeedChange.Value, 0.4, 2.5))
  consistency = Σ_{i=1..7} Math.Sign(r[i] - r[i-1])
  targetRate = Lerp(targetRate, Average(r), |consistency| / 7.0)      // Average = sequential double sum from +0.0, / 8
                                                                     //   [verified op 222: no SIMD for double; SysMisc.averageF64]
  ```
  `TimeAbsolute = min(RawTime, EndTime + MaximumJudgementOffset)` (`G/Rulesets/Judgements/JudgementResult.cs:55`).
  `OnRevertResult` is for rewind only, so it is not needed.
- `ApplyToRate(time, rate) => rate * InitialRate` (:160). Gameplay doesn't use it.
- Judgement effect: only through spinner rotation (and the live schedule). Model state is as listed above. The
  OnNewResult hook runs inside `ApplyResult`, the same call that dispatches to the processors (DHO `OnNewResult`
  ordering vs `Playfield.NewResult`: per-DHO handlers are invoked in subscription order. AS only touches its own state,
  so the order doesn't matter).

---------------------------------------------------------------------------------------------------

## 8. Mirror and HR reflection — `OsuModMirror : ModMirror` (`O/Mods/OsuModMirror.cs`)
`IApplicableToHitObject`. Setting `reflection`: `Bindable<MirrorType>()`, enum `Horizontal = 0` (**default**),
`Vertical = 1`, `Both = 2` (:20-21, 44-49). `Both` does horizontal **then** vertical (:37-40). Incompatible with HR.

Reflection (`O/Utils/OsuHitObjectGenerationUtils.cs:112-170`), with `BASE_SIZE = (512f, 384f)` (`O/UI/OsuPlayfield.cs:47`):
- Horizontal: `Position = (512f - X, Y)` (float subtraction, rounded). For sliders, each control point becomes `(-x, y)`.
- Vertical (also HR): `Position = (X, 384f - Y)`. For sliders, each control point becomes `(x, -y)`.
- Sliders: `modifySlider` copies the control points (keeping `Type`), negates, and sets
  `slider.Path = new SliderPath(points, oldPath.ExpectedDistance.Value)` (:162-169).
  **The path is recomputed from the reflected control points.** Path approximation is not mirror-exact in floating point
  (for example PerfectCurve atan2 under x→−x), so the model must re-run the path pipeline and must not reflect the
  computed points.
- The `Slider.Path` setter fires `updateNestedPositions` (`O/Objects/Slider.cs:229-254`). Head = Position; tail =
  EndPosition; repeats/ticks = `Position + Path.PositionAt(progress)`. **Nested object times, spans and tick
  generation are not regenerated** (ApplyDefaults ran before). `Slider.EndTime` is computed live from the new
  `Path.Distance` (`Slider.cs:28`). It usually equals ExpectedDistance, but can differ in the
  "last two points equal" path-extension edge case.
- Order inside `GetPlayableBeatmap`: after ApplyDefaults and before stacking (§1 #1d, #1e).
- HR's vertical flip is the same function. HR and MR are mutually incompatible but not enforced, so if both are present
  both apply in list order.

---------------------------------------------------------------------------------------------------

## 9. Classic — `OsuModClassic : ModClassic` (`O/Mods/OsuModClassic.cs`)
Interfaces: `IApplicableToHitObject`, `IApplicableToDrawableHitObject`, `IApplicableToDrawableRuleset<OsuHitObject>`,
`IApplicableHealthProcessor`. `Ranked = false`. Incompatible with StrictTracking (:23).
Every stable replay gets CL with all defaults (§1).

| Setting (JSON key) | Default | Effect | Judgement-relevant? |
|---|---|---|---|
| `no_slider_head_accuracy` | true | `ApplyToHitObject` (step 1d): `slider.ClassicSliderBehaviour = v`, which also sets HeadCircle and TailCircle (`Slider.cs:113-121`). Effects: head judgement `SliderTickJudgement` (max **LargeTickHit**), `ResultFor` = base hit → LargeTickHit else LargeTickMiss (`O/Objects/SliderHeadCircle.cs:17`, `DrawableSliderHead.cs:59-71`). Tail `LegacyTailJudgement` (max **SmallTickHit**) (`SliderTailCircle.cs:23-28`). Slider itself `OsuJudgement` (max Great) instead of `OsuIgnoreJudgement` (`Slider.cs:289-293`), judged at `EndTime` after the tail: all nested hit → Great, none → Miss, else `hit/total >= 0.5` (double) → Ok, else Meh (`DrawableSlider.cs:294-313`). Judgements are created lazily (`HitObject.cs:174`), so setting the flag after ApplyDefaults works. This also changes ScoreProcessor maxima (SimulateAutoplay), health increases, and SD/PF/AS relevance | **yes** |
| `classic_note_lock` | true | `ApplyToDrawableRuleset`: `Playfield.HitPolicy = new LegacyHitPolicy(400 - (AP present ? 200 : 0))` (:52-60). `ApplyToDrawableHitObject` on each `DrawableSliderHead`: `HitArea.CanBeHit = () => !DrawableSlider.AllJudged` (:73-74, 96-99) instead of `!head.AllJudged` (`DrawableHitCircle.cs:75`). So a judged head keeps **consuming** presses (`OnPressed` returns true when hovered, `DrawableHitCircle.cs:277-307`) and blocks objects underneath until the whole slider is judged. Also affects `CheckScreenSpaceActionPressJudgeable` (touch only, `O/OsuInputManager.cs:47-52`). Multiplier 0.985 vs 0.96 | **yes** |
| `always_play_tail_sample` | true | `DrawableSliderTail.SamplePlaysOnlyOnHit = !v` (:78-80, `DrawableSlider.cs:332`), audio only | no |
| `fade_hit_circle_early` | true | Unless HD is present with `OnlyFadeApproachCircles == false`: adds a FadeOut (from StartTime+ok to StartTime+meh) for circles and heads in a non-Hit state (:101-115). It is added *after* `LifetimeEnd` is fixed (`DrawableHitObject.cs:491-495`, circle `Expire()` at `DrawableHitCircle.cs:234`), and DHO input propagation ignores alpha (`DrawableHitObject.cs:76-78`). So it is **visual only** **[verified: oracle `--mods '[{"acronym":"CL","settings":{"fade_hit_circle_early":false}}]'` vs
`true` on 3 stable replays with misses (scores 2767715368, 2773329193, 4777843492): identical judgements and score]** | no |
| `classic_health` | true | `CreateHealthProcessor(drainStart) => v ? new OsuLegacyHealthProcessor(drainStart) : null` (:117), which replaces `OsuHealthProcessor` (lazer-map §4.3) | **yes** |

Model state: three booleans (`nsha`, `cnl`, `ch`). The other two are ignorable.

---------------------------------------------------------------------------------------------------

## 10. Score multiplier — `OsuScoreMultiplierCalculatorV2`

Selection: live `ScoreProcessor.updateScoreMultiplier` (`G/Rulesets/Scoring/ScoreProcessor.cs:418-425`) calls
`Ruleset.CreateScoreMultiplierCalculator(new ScoreMultiplierContext(Beatmap.BeatmapInfo.Difficulty))` with no score, so
**V2 always** (`O/OsuRuleset.cs:256-262`; V1 only for stored scores with TotalScoreVersion < 30000017). The context
difficulty is the **unmodded** beatmap difficulty (floats). It is applied as
`TotalScore = (long)Math.Round(TotalScoreWithoutMods * multiplier)` (`ScoreProcessor.cs:401`, banker's rounding).
`Mod.ScoreMultiplier` is obsolete and unused (`G/Rulesets/Mods/Mod.cs:87-88`).

### 10.1 Algorithm (`G/Rulesets/Scoring/ScoreMultiplierCalculator.cs:59-90`)
```
byType = mods.ToDictionary(m => m.GetType())     // exact runtime type; duplicate type → exception (crash)
if empty: return 1
remaining = HashSet(byType.Keys)                  // enumeration = list order (no adds after removals)
result = 1.0
if byType.Count > 1:
  for (types, f) in combinations (registration order):
     if remaining ⊇ types: result *= f(instances); remaining -= types
for t in remaining (list order): if single[t] exists: result *= single[t](mod)
```
Lookup is by exact type: `OsuModNightcore` and `OsuModDoubleTime` are separate keys, and `ModWindUp`/`ModWindDown` are
registered on the base classes the ruleset instantiates.

### 10.2 Rules (`O/Scoring/OsuScoreMultiplierCalculatorV2.cs`)
Combinations, in order (:36-49):
1. HD+BL → 1.24
2. HD+WG → hidden(t=true)
3. HD+GR → hidden(t=true)
4. HD+DF → hidden(t=true) · deflate(DF)
5. HD+RP → hidden(t=true)
6. HD+DP → hidden(t=true)
7. TC+BL → 1.24
8. FL+FR → `1 + (fl(FL) - 1)/2`

Singles (all doubles):

| Mod | Multiplier | line |
|---|---|---|
| EZ | `max(0.4, 0.8 - max(0, 0.1*(Retries - 2)))`. Retries 0..2 → 0.8, 3 → 0.7000000000000001, 4 → 0.6000000000000001, 5 → 0.5, ≥6 → 0.4 | :19, 112-119 |
| NF | 0.5 | :20 |
| HT, DC | `ht(s) = (int)(s*20)/20.0*1.4 - 0.5` (truncation toward zero) | :21-22, 121-126 |
| HR | 1.09 | :28 |
| SD, PF, AC, ST, MR, AL, SG, AT, CN, TR, WG, SI, GR, BR, MU, NS, RP, FR, BU, DP, BM, TD, SV2 | 1 (no entry) | |
| DT, NC | `dt(s)`: `v = (int)(s*10)/10.0; pen = (v != 1.5 && v != 1.0) ? 0.01 : 0; (v-1)*0.46 + 1 - pen` | :31-32, 128-139 |
| HD | `1.04 - (OnlyFadeApproachCircles ? 0.02 : 0)` (t=false) | :44, 141-152 |
| TC | 1.02 | :47 |
| FL | `max(1.02, min(1.2, 1.2 - 0.2*(Size - 1)))`; if `!ComboBasedSize`: `1 + (v-1)/5` | :50, 154-163 |
| BL | 1.24 | :52 |
| TP | 0.01 | :60 |
| DA | `selX = (double)(DA.X ?? base.X)` for CS/HP/OD/AR (float → double); `m_X = max(0.1, 1.0 - |selX - (double)base.X| * 0.5)`; result `max(0.1, mCS*mHP*mOD*mAR)` (product order CS, HP, OD, AR) | :61, 165-184 |
| CL | `ClassicNoteLock ? 0.985 : 0.96` | :62 |
| RD | 0.7 | :63 |
| RX, AP | 0.1 | :74-75 |
| SO | 0.95 | :76 |
| DF | `1.0 - max(0, 0.02*(StartScale - StartScale.Default))` | :86, 197-198 |
| WU, WD | `tr = 0.8*mult(min(I,F)) + 0.2*mult(max(I,F))`, `mult(x) = x < 1 ? ht(x) : dt(x)`. Defaults: WU = 1.046, WD = 0.6399999999999999 | :87-88, 186-195 |
| AD | 0.7 | :90 |
| MG | `0.7 - AttractionStrength*0.6` | :93 |
| AS | 0.1 | :95 |
| SY | 0.99 | :98 |

`hidden(t) = 1.04 - (OFAC ? 0.02 : 0) - (t ? 0.02 : 0)`, evaluated as sequential `-=` on 1.04.

Tabulated (IEEE double; s = k/100 after snapping), with `[a..b]` meaning "all k in range":
- `ht`: [50..54] 0.19999999999999996, [55..59] 0.27, [60..64] 0.33999999999999997, [65..69] 0.4099999999999999,
  [70..74] 0.47999999999999987, [75..79] **0.5499999999999998** (default HT/DC), [80..84] 0.6199999999999999,
  [85..89] 0.69, [90..94] 0.76, [95..99] 0.8299999999999998.
- `dt`: [101..109] 1.0, [110..119] 1.036, [120..129] 1.082, [130..139] 1.1280000000000001, [140..149] 1.174,
  [150..159] **1.23** (default), [160..169] 1.266, [170..179] 1.312, [180..189] 1.358, [190..199] 1.404, 200 1.45.

Example: stable DT HD HR + auto CL gives `((((1*1.23)*1.04)*1.09)*0.985)` = 1.3734130800000002.

---------------------------------------------------------------------------------------------------

## 11. Score V2 / Touch Device
`ModScoreV2` (`G/Rulesets/Mods/ModScoreV2.cs`) is a plain `Mod` marker (`UserPlayable = false`), created from the
legacy ScoreV2 bit. **It has no effect on lazer judgement or scoring.** Multiplier 1. `OsuModTouchDevice` is a marker
(UI resume overlay only, `O/UI/DrawableOsuRuleset.cs:70-76`). Multiplier 1.

---------------------------------------------------------------------------------------------------

## 12. Fail semantics with these mods (combining §4 with ReplayPlayer)
Let `allow(t)` = live: always true. Replay semantics: `t >= lastFrameTime` (`ReplayPlayer.cs:55-68`). When a fail is
triggered at judgement time t (health ≤ 1e-7, an SD/PF condition, or an AC accuracy change):
```
if !allow(t): nothing (HasFailed stays false; retried on next trigger)
else: for m in mods (list order) if m is IApplicableFailOverride:
          r = m.PerformFail()     // NF/CN: false; SD/PF/AC: true; EZ: lives>0 ? (Health := 1; lives--; false) : true
          if !r: break → not failed
      if all true: HasFailed = true → this result counted, later ones FailedAtJudgement → ignored by ScoreProcessor;
                   rank F (ConcludeFailedScore is Scheduled: Player.cs:1000-1006)
```
Consequences:
- [EZ, NF]: lives are consumed and Health is refilled. [NF, EZ]: NF short-circuits, so lives are never touched and
  health stays at 0.
- [SD, EZ] (stable order): a miss under SD consumes a life, refills health, and play continues.
- Under replay semantics, EZ lives are never consumed before the last frame. Health stays clamped at 0, and every
  judgement re-triggers the check. After `lastFrameTime`, the first failing check starts consuming lives.
- The default health check runs only when a judgement is applied (drain alone can't fail).

---------------------------------------------------------------------------------------------------

## 13. Modelling checklist
- [ ] Mod list is an ordered list of (type, settings). Keep lazer/stable order. Stable: `ConvertFromLegacyMods` order + Classic(defaults).
- [ ] JSON setting decode: snake_case keys, Newtonsoft value types, `Convert.ChangeType` rules, enum by int or name; key absent means default.
- [x] `BindableNumber.setValue`: `double.Clamp` → `VarDecFromR8` → decimal half-even round to Precision → `VarR8FromDec` → clamp → `Equals`-guarded store. Done: `Net/Framework.lean` `Bindable.BD/BF` (ops 146–149, 230/231), `Net/Decimal.lean` (ops 111–119), `Math.Round(double,2)` (op 58), `SysMisc.averageF64` (op 222).
- [ ] DA `DifficultyBindable`: double→float, clamp to extended range always, no snapping, `null` = no override.
- [ ] WU/WD cross-constraint callbacks during decode (property order Initial, Final).
- [ ] Difficulty pipeline in list order on float fields: EZ (×0.5f ×4), HR (min(×1.4f,10) HP, OD, CS(×1.3f), AR), DA assign; DA ranges AR [−10,11], others [0,11].
- [ ] Check preempt (int-truncated), windows, spinner, health and stacking for extrapolated AR/OD/CS/HP; also `GameplayStartTime = first.Start - max(2000, preempt)`.
- [ ] HitObject transforms in list order after ApplyDefaults: HR/MR reflections (float `512f-x`, `384f-y`, control-point negation, **path recompute**, nested positions update, nested times unchanged, live `EndTime`), CL `ClassicSliderBehaviour`.
- [ ] Classic: slider/head/tail judgement types and slider proportional result; LegacyHitPolicy(400 or 200 with AP); head `CanBeHit = !slider.AllJudged`; legacy health processor. Ignore tail-sample and early-fade.
- [ ] Rate state: `trueRate(step)` = HT/DT: s; NC: `1.5*(s/1.5)`; DC: `0.75*(s/0.75)`; WU/WD: SpeedChange updated at step start from FSC time; AS: damped SpeedChange. Used only for spinner rotation `(float)(delta*|rate|)`.
- [ ] TimeRamp: begin/finalRateTime from the playable beatmap (top-level objects); `Math.Round(ramp,2)`; update before DHOs each step.
- [ ] AdaptiveSpeed: precedingEndTimes (circles and heads only), per-result queue update on accuracy-affecting results, per-step damping with step elapsed (schedule-dependent). Initial state after ApplyToTrack.
- [ ] Hit windows, preempt, health drain and object times are NOT rate-scaled; replay frame times are gameplay time.
- [ ] Health→Score dispatch order; fail conditions SD (AffectsCombo && !IsHit, + tail option), PF (relevance rule), AC (on Accuracy/MaximumAccuracy change, after counting; default mode MaximumAchievable).
- [ ] Fail override: ordered short-circuit `All(PerformFail)`, EZ lives/refill, NF/CN veto, ReplayPlayer `lastFrameTime` gate (both semantics).
- [ ] Multiplier V2: combinations then singles in list order, exact-type keys, double arithmetic per table; DA uses unmodded BeatmapInfo difficulty; `TotalScore = round_even(TSWM * mult)`.
- [ ] Reject/ignore: AT, CN (unplayable), SV2/TD (markers, ×1), NC beat samples (audio).
- [ ] Oracle cross-checks to add: CL `fade_hit_circle_early` on/off identical; NC 1.51 spinner vs DT 1.51; WU/WD spinner maps; AS on a spinner map; EZ+NF vs NF+EZ health trace; DA AR −10/11 and OD 11; JSON off-grid speed (1.135 → 1.14).
