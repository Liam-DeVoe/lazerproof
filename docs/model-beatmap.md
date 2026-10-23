# Beatmap model: `.osu` → playable osu! beatmap (Lean)

This document covers the Lean model of lazer's osu!standard beatmap pipeline. It lives in
`model/OsuModel/Beatmap/*` (`import OsuModel.Beatmap`).

- Entry point: `OsuModel.Beatmap.load : ByteArray → List Mod → LoadResult`, which runs the
  decoder and then `getPlayableBeatmap`.
- Source mirrored: lazer 2026.1005.0-lazer (`LAZER_COMMIT`), osu-framework 2026.921.1 and
  osuTK 1.0.211. The `file:line` references in every doc comment point into these checkouts.
- Arithmetic: all of it uses `OsuModel.Net` (`docs/net-float.md`), keeping float32 vs double
  exactly as in C# and in the same order. Integer arithmetic uses wrapping `Int32` where C# uses
  `int`.
- Status: see "Test results" below.

## Pipeline and structure

```
bytes ──Text.streamReaderDecode/readLines──▶ lines            (LineBufferedReader / StreamReader)
      ──LegacyBeatmapDecoder.decode────────▶ DecodedBeatmap   (Decoder.GetDecoder<Beatmap> + Decode)
      ──getPlayableBeatmap d mods──────────▶ PlayableBeatmap  (WorkingBeatmap.GetPlayableBeatmap, osu! ruleset)
           convertBeatmap (ControlPointInfo.DeepClone, OsuBeatmapConverter, stable sort)
           mods: applyAfterConversion → applyToDifficulty
           OsuBeatmapProcessor.preProcess (new-combo forcing, UpdateComboInformation)
           applyDefaults (per object: self defaults, nested creation, introsort, nested defaults)
           mods: applyToHitObject
           OsuBeatmapProcessor.applyStackingAll (PostProcess)
           mods: applyToBeatmap
```

| Lean file | Contents |
|---|---|
| `DotNet.lean` | BCL behaviour: `Trim*` (Unicode white space), `Split`, `SplitKeyVal`, `double.CompareTo`, `% 1`, `List<double>.BinarySearch`, `List<T>.Sort` (introsort: insertion sort / heapsort / median-of-three partition, unstable), LINQ `OrderBy` (stable), `Enum.TryParse` |
| `CharTable.lean` | generated `char.IsLetter` table (380 BMP ranges, from `bmtest letters`) |
| `Vector2.lean` | `osuTK.Vector2` float ops (`Length` = `(float)Math.Sqrt(float)`, `Normalized`, osuTK `Distance` vs framework `Vector2Extensions.Distance` = `MathF.Sqrt`), `Precision` |
| `Text.lean` | `StreamReader(UTF8, detectBOM)` decoding (UTF-8 maximal-subpart U+FFFD replacement, UTF-16 LE/BE BOM) and `ReadLine` splitting |
| `ControlPoints.lean` | timing/difficulty control points, bindable clamping, redundancy, `TimingPointAt`/`DifficultyPointAt` binary search, `DeepClone` |
| `Types.lean` | `PathType`, `PathControlPoint`, `Difficulty`, `ConvertHitObject`, `DecodedBeatmap` |
| `PathApproximator.lean` | B-spline/Bezier (Boehm knot insertion + adaptive subdivision DFS), Catmull, circular arc (`CircularArcProperties`), linear |
| `SliderPath.lean` | `calculatePath`, `calculateSubPath` (incl. perfect-curve fallbacks, Catmull 6px optimisation), `calculateLength` (ExpectedDistance shortening/extension, "no extension if last two points equal" quirk), `PositionAt` |
| `HitObjectParser.lean` | `ConvertHitObjectParser.Parse`: coordinates (int truncation < v128), type bits, combo offset, sliders (repeats, length, path string, `convertPathType`, `convertPoints` implicit segments, legacy perfect-curve rules), spinners, holds, which sample-bank parses throw, parser state on failure |
| `Decoder.lean` | `LegacyDecoder` line loop (skip/comment/section rules, `Enum.TryParse` sections, per-line exception dropping), `[General]` (`StackLeniency`, `Mode`), `[Difficulty]` (AR = OD rule), `[Events]` breaks, `[TimingPoints]` (pending-point buffering/flush order, NaN beat length), header and version detection, v<5 +24 ms offset, `applyDifficultyRestrictions`, `postProcessBreaks`, decode-time slider defaults |
| `SliderEventGenerator.lean` | `SliderEventGenerator.Generate` (ticks with accumulating `d += tickDistance`, repeats, legacy last tick, tail) |
| `Objects.lean` | `OsuHitObject`/nested records, derived getters (`EndTime`, `EndPosition`, `StackOffset`, `Radius`, …), `DifficultyRange`, `CalculateScaleFromCircleSize`, `OsuHitWindows`, `ApplyDefaults` for circles/sliders/spinners and all nested kinds |
| `Processor.lean` | `UpdateComboInformation`, `PreProcess`, stacking (`applyStacking` for v≥6, `applyStackingOld` for older versions) |
| `Playable.lean` | `OsuBeatmapConverter`, `BeatmapConverter.Convert`, `GetPlayableBeatmap`, the `Mod` hook record, `updateNestedPositions` |
| `Dump.lean` | canonical text dump (same format as `bmtest`) |

## Correspondence table (lazer → Lean)

| lazer / framework (file:line) | Lean |
|---|---|
| `LineBufferedReader` / `StreamReader.ReadLine` | `Text.streamReaderDecode`, `Text.readLines` |
| `Decoder.GetDecoder<Beatmap>` (`Decoder.cs:54-87`), `LegacyBeatmapDecoder.Register` (`:53-57`) | `LegacyBeatmapDecoder.decode` |
| `LegacyBeatmapDecoder.ParseStreamInto` (`:85-112`) | `LegacyBeatmapDecoder.parseStreamInto` |
| `LegacyDecoder.ParseStreamInto` line loop (`LegacyDecoder.cs:38-79`) | `parseLines` |
| `ShouldSkipLine`, `StripComments`, `SplitKeyVal` | `shouldSkipLine`, `stripComments`, `splitKeyVal` |
| `Enum.TryParse(..., out Section)` / `LegacyEventType` | `enumTryParse sectionNames` / `eventTypeNames` |
| `handleGeneral` (`:244-309`) | `handleGeneral` |
| `handleDifficulty` (`:401-436`) | `handleDifficulty` |
| `handleEvent` (`:438-482`) | `handleEvent`, `insertBreak` |
| `handleTimingPoint` (`:484-569`) | `handleTimingPoint` |
| `addControlPoint` / `flushPendingPoints` (`:576-603`) | `addLinePoints` / `flushPendingPoints` |
| `handleHitObject` (`:605-611`) | `handleHitObject` |
| `applyDifficultyRestrictions` (`:118-132`) | `applyDifficultyRestrictions` |
| `postProcessBreaks` (`:137-153`) | `postProcessBreaks` |
| decoder `applyDefaults` (`:155-166`) | `applyDecodeDefaults` |
| `ConvertHitObjectParser.Parse` (`ConvertHitObjectParser.cs:52-192`) | `ConvertHitObjectParser.parse` |
| `readCustomSampleBanks` (`:194-235`) | `readCustomSampleBanks` (throw/no-throw only) |
| `convertPathType` (`:237-257`) | `convertPathType` |
| `convertPathString` / `readPoint` (`:280-348`) | `convertPathString` / `readPoint` |
| `convertPoints` / `isLinear` (`:357-427`) | `convertPoints` / `isLinear` |
| `createSlider` zero-length fix (`:476-506`) | in `parse` (slider branch) |
| `ControlPointInfo.Add` / `CheckAlreadyExisting` / `GroupAt` / `ControlPointGroup.Add` | `ControlPointInfo.addTiming`, `addDifficulty`, `insertSorted` |
| `ControlPointInfo.BinarySearch` (`ControlPointInfo.cs:212-292`) | `binarySearchIdx` |
| `TimingPointAt` (`:75`), `DifficultyPointAt` (`LegacyControlPointInfo.cs:41`) | `timingPointAt`, `difficultyPointAt` |
| `ControlPointInfo.DeepClone` (`:378-386`) | `ControlPointInfo.deepClone` |
| `BindableDouble` clamping (`TimingControlPoint.cs:64-68`, `DifficultyControlPoint.cs:24-28`, `Slider.cs:126-130`) | `clampBeatLength`, `clampSV` |
| `SliderPath.calculatePath` (`SliderPath.cs:287-334`) | `SliderPath.calculatePath` |
| `SliderPath.calculateSubPath` (`:336-424`) | `SliderPath.calculateSubPath`, `optimiseCatmullPath` |
| `SliderPath.calculateLength` (`:426-485`) | `SliderPath.calculateLength` |
| `SliderPath.PositionAt` / `indexOfDistance` / `interpolateVertices` (`:205-211`, `:487-522`) | `positionAt`, `indexOfDistance`, `interpolateVertices` |
| `PathApproximator.BSplineToPiecewiseLinear` (`PathApproximator.cs:79-144`) | `PathApproximator.bSplineToPiecewiseLinear` |
| `bSplineToBezierInternal`, `bezierIsFlatEnough`, `bezierSubdivide`, `bezierApproximate` (`:774-896`) | same names |
| `CatmullToPiecewiseLinear`, `catmullFindPoint` (`:150-169`, `:907-917`) | same names |
| `CircularArcToPiecewiseLinear` (`:175-199`), `CircularArcProperties` ctor (`CircularArcProperties.cs:34-87`) | `circularArcToPiecewiseLinear`, `circularArcProperties`, `arcPointCount` |
| `IHasPathWithRepeats.ProgressAt/CurvePositionAt` (`IHasPathWithRepeats.cs:15-28`) | `SliderData.progressAt/curvePositionAt` |
| `SliderEventGenerator.Generate/generateTicks` (`SliderEventGenerator.cs:26-161`) | `SliderEventGenerator.generate/generateTicks` |
| `OsuBeatmapConverter.ConvertHitObject` (`OsuBeatmapConverter.cs:27-75`) | `convertHitObject` |
| `BeatmapConverter.Convert/ConvertBeatmap` (`BeatmapConverter.cs:44-92`) | `convertBeatmap` |
| `WorkingBeatmap.GetPlayableBeatmap` (`WorkingBeatmap.cs:276-352`) | `getPlayableBeatmap` |
| `HitObject.ApplyDefaults` (`HitObject.cs:105-148`) | `applyDefaults` |
| `OsuHitObject.ApplyDefaultsToSelf` (`OsuHitObject.cs:170-183`) | `commonDefaults`, `timePreemptFor`, `timeFadeInFor` |
| `IBeatmapDifficultyInfo.DifficultyRange` (`IBeatmapDifficultyInfo.cs:25-46`) | `difficultyRange` |
| `LegacyRulesetExtensions.CalculateScaleFromCircleSize` / `GetPrecisionAdjustedBeatLength` | `calculateScaleFromCircleSize` / `getPrecisionAdjustedBeatLength` |
| `Slider.ApplyDefaultsToSelf` / `CreateNestedHitObjects` (`Slider.cs:156-227`) | in `applyDefaults`, `sliderNested` |
| `Slider.updateNestedPositions` (`Slider.cs:229-254`) | `updateNestedPositions` (for mods) |
| `SliderEndCircle` / `SliderTick` defaults | `applyNestedDefaults` |
| `Spinner.ApplyDefaultsToSelf` / `CreateNestedHitObjects` (`Spinner.cs:61-96`) | `spinnerDefaults`, `spinnerNested` |
| `OsuHitWindows.SetDifficulty` (`OsuHitWindows.cs:36-41`) | `osuHitWindows` |
| `OsuBeatmapProcessor.PreProcess` + `BeatmapProcessor.PreProcess` | `OsuBeatmapProcessor.preProcess` |
| `OsuHitObject.UpdateComboInformation` (`OsuHitObject.cs:185-208`) | `updateComboInformation` |
| `OsuBeatmapProcessor.ApplyStacking/applyStacking/applyStackingOld` (`OsuBeatmapProcessor.cs:45-281`) | `applyStackingAll/applyStacking/applyStackingOld` |

## Mods

Files: `ModSettings.lean` (APIMod decoding), `Mods.lean` (hooks of the simple mods),
`ModRandom.lean` (Random + repositioning utilities), `ModTargetPractice.lean` (TP generation,
`ModConfig.allHooks`). Entry point: `Settings.toMod acronym settings : ModConfig`, then
`load bytes (configs.map ModConfig.allHooks)`.

### Hook points and order

`Mod` (in `Playable.lean`) has one optional field per interface that `GetPlayableBeatmap` consults
(`WorkingBeatmap.cs:276-352`), applied in this order, each phase in mod-list order:

1. `applyAfterConversion` (`IApplicableAfterBeatmapConversion`): ST.
2. `applyToDifficulty`: EZ, HR, DA, TP (AR ×0.5). Float arithmetic, list order (HR+TP ≠ TP+HR).
3. `OsuBeatmapProcessor.PreProcess`, `ApplyDefaults` (with the modded difficulty).
4. `applyToHitObject` (for each mod, for each object): HR (vertical flip), MR, CL (`ClassicSliderBehaviour`).
5. `PostProcess` (stacking, on reflected positions).
6. `applyToBeatmap` (with the mod index): HD (`FirstObject`, `TimeFadeIn = 0.4·preempt` for non-sliders and all
   nested objects), TC/GR/DF/SI/TR/WG/DP (`FirstObject`), FR (`TimePreempt += StartTime − lastNewComboTime`), RD,
   TP (regeneration, then `FirstObject`), WU/WD (`beginRampTime`, `finalRateTime`), AS (`precedingEndTimes`).

`IApplicableToBeatmapConverter` / `IApplicableToBeatmapProcessor` are implemented by no osu! mod. Every other mod
(rate, fail, input, transform-at-runtime, visual) has no beatmap-side effect; NS/SY implement `IApplicableToBeatmap`
but only capture visual state. Lazer enforces no compatibility here: any list (duplicates included) is applied.

Beatmap-derived mod state is returned in `PlayableBeatmap.modStates` (`ModState`: `firstObject`, `timeRamp`,
`precedingEndTimes`), with object references (`ObjRef`) that carry the beatmap `epoch` (bumped when TP replaces
the object list, so an earlier `FirstObject` shows as `gone`). The simulation needs these.

Details that mattered:
- `PathControlPoint.Position` ignores assignments that compare `==` to the current value, and a new control point
  starts at `(+0,+0)`: negating a zero coordinate keeps `+0` (`Mods.setControlPointPos`).
- Reflections/flips/rotations rebuild the path from the modified control points (`new SliderPath(points,
  ExpectedDistance)`), then nested positions follow (`updateNestedPositions`); nested times are not regenerated.
- ST sliders are fresh `Slider`s: `GenerateTicks` resets to `true`, the tail is a `StrictTrackingSliderTailCircle`
  (dump: `st=1`).
- TP circles get `ApplyDefaults` at `StartTime = 0` (`Kiai = EffectPointAt(1)`), hence effect points (kiai) are now
  decoded, and Random's downbeat test needs the time-signature numerator; both are dumped.
- Random's `% beatLength` and `getAngleDifference`'s `% 2π` are exact IEEE `fmod` (`DotNet.fmodF64/fmodF32`).

### Settings (`APIMod.ToMod`)

`Settings.toMod` mirrors `APIMod.ToMod` for the osu! ruleset: case-insensitive acronym lookup (`UnknownMod`
otherwise), settings in `GetSettingsSourceProperties()` order (table checked against `bmtest modinfo`), each
present key parsed with `Bindable<T>.Parse` semantics on the Newtonsoft value (`JsonVal`: long/BigInteger/double/
bool/string/null): `Convert.ChangeType` rules (`Convert.ToInt32(double)` half-even with overflow, `bool.Parse`,
`int/double/float.Parse`, enum via `Enum.Parse(input.ToString())`, `BindableBool`'s `"1"/"0"`), then the setter:
`BindableNumber` clamp + decimal precision snap + equality no-op (`OsuModel.Net.Framework.Bindable`, the single
implementation, diff-tested in nettest), DA's `DifficultyBindable` (extended-range clamp, no snap), nullable seeds;
a failing parse keeps the previous value. WU/WD `ValueChanged` cross-constraints are run. Defaults come from the
initialisers (e.g. WG strength = 1.00000001490116).

### Mod test results (2026-10-21)

`run_corpus.py --mods single:SEED:ACR` (one mod, randomised settings) / `--mods random:SEED` (1-5 mods in random
order, duplicates and incompatible combinations allowed, randomised settings incl. strings/bools/nulls/huge ints/
off-grid and out-of-range numbers, unknown keys/acronyms, lowercase acronyms). Every line of the dump is compared,
including the decoded settings (`mod` lines) and the beatmap-derived mod state (`modstate` lines).

| corpus | mods | maps | bit-identical |
|---|---|---|---|
| real maps (first 400) | each of the 48 osu! acronyms alone | 48 × 400 | **all** (after fixing MU's `MinValue` callback; MU re-run 1000/1000) |
| real maps + test resources | random combos (seeds 11, 14) | 1625 + 1853 | **all** |
| version-rewritten real maps (v3..v13, v128) | random combos ×2 | 1200 | **1200** |
| `fuzz.py` (seed 5) + `gen.py` (seed 9) | random combos (seed 13) | 3000 | **2998**, 2 skipped (resource limit, below) |
| RD alone, TP alone (real maps) | | 150 + 150 (+400 each in singles) | **all** |
| TP alone on fuzzed maps (incl. the 3 that exposed the sample-lookup exceptions) | | 203 | **199** (8 of them both fail with `ArgumentOutOfRangeException`), 4 skipped (resource limit) |

Bugs found by the test and fixed: `PathControlPoint` equality no-op (−0), case-insensitive acronyms,
`MuteComboCount.MinValue` follows `InverseMuting`, TP's sample lookups throwing `ArgumentOutOfRangeException`
on fuzzed maps (`NodeSamples` index / `getClosestHitObject(-1)`), and (before using the Net layer) decimal snapping.

Residuals / not covered:
- **Resource limit.** Maps on which lazer itself exceeds a 640 MB GC heap (`OutOfMemoryException`, e.g. fuzzed maps
  with enormous tick/beat counts; TP on maps with huge end times) are skipped, and the model is not run on them
  (it would need similar memory). Two fuzzed maps hit this even without mods.
- Random/TP without a seed are non-reproducible in lazer (`RNG.Next()`); the model rejects them.
- BCL conversions in settings decoding (`Convert.ToInt32`, `bool.Parse`, `ToString` for enums, Newtonsoft number
  classification) are tested, not transcribed from source. JSON numbers like `1e400` (Newtonsoft overflow) and
  duplicate JSON keys were not generated.
- Acronym lookup is ASCII case-insensitive; `OrdinalIgnoreCase` on non-ASCII letters (e.g. `ı`) is not modelled.

## Trust assumptions / environment

- **Numerics.** These are the `OsuModel.Net` assumptions: glibc 2.39 libm for
  `Math.Atan2/Cos/Sin/Acos`, which only the perfect-curve arc uses, and `F64.sqrt`/`F32.sqrt`
  being correctly rounded.
- **Rulesets.** All four rulesets are available, as in the game. This affects `Mode:` lines.
  `bmtest` registers a `RulesetStore` with ids 0–3 for the same reason. Maps whose final mode is
  not 0 are reported (`mode N`) and not converted.
- **Culture.** Like `oracle/`, `bmtest` runs with `InvariantGlobalization=true`. The only
  culture-sensitive call on this path is the `"osu file format v"` header test
  (`StartsWith(..., InvariantCulture)`, `Decoder.cs:75`). The model uses ordinal comparison,
  which agrees except on files that put ICU-ignorable characters (e.g. a second U+FEFF) before
  the header.
- **Not modelled: JSON beatmaps.** Files starting with `{` (`JsonBeatmapDecoder`) give an error.
- **Not modelled: UTF-32 BOMs and unpaired UTF-16 surrogates.** These also give an error.
- **Not modelled: `GetPlayableBeatmap`'s 10 s timeout.** `bmtest` uses `CancellationToken.None`.
- **Fuel bounds.** The model replaces three potentially unbounded loops with a fixed iteration
  cap ("fuel"). Each cap is far beyond anything lazer can finish within its own 10 s timeout:
  - Bezier subdivision: 10⁸ steps.
  - Slider tick loop: 10⁷ ticks per span.
  - The others are structurally bounded.
- **Pathological pooled-buffer read: harmless.** `convertPathString` reads beyond the point list
  (stale `ArrayPool` memory) only when a later segment is empty. That segment always throws, so
  the line is dropped anyway (argued in the code).
- **Irrelevant state is not modelled.** Samples, colours, metadata, storyboards, kiai and effect
  points have no gameplay effect. Their only influence on the modelled state is whether parsing
  them throws, which drops the whole line. That is modelled wherever such a parse shares a line
  with modelled data: sample banks of hit objects, and the sample/effect fields of timing
  points.

## Differential test

- **`model/bmtest/` (C#).** Has a `ProjectReference` to lazer's `osu.Game.Rulesets.Osu`. Build:
  `dotnet build -c Release -m:1 -p:BuildProjectReferences=false` (lazer's Release build already
  exists).
  - It loads a file exactly like the game: `Decoder.GetDecoder<Beatmap>(LineBufferedReader)`,
    then `.Decode`, then `FlatWorkingBeatmap.GetPlayableBeatmap(osu, mods)`.
  - It dumps every gameplay-relevant field as raw bits:
    - beatmap level: version, difficulty, stack leniency, timing and difficulty points, breaks;
    - per object: kind, start/end time, position, stack height/offset, stacked position, scale,
      radius, preempt, fade-in, combo fields, hit windows, `MaximumJudgementOffset`;
    - per slider: repeats, velocity, tick distance, multipliers, distances, expected distance,
      durations, end positions, all control points with types, every calculated path point and
      every cumulative length (via reflection);
    - per spinner: duration, spins required, bonus spins;
    - per nested object: everything above plus path progress, span index and start, repeat
      index, spinner duration.
- **`bmdump` (Lean, `model/BmDump/Main.lean`).** Prints the same format from the model.
- **`model/bmtest/run_corpus.py`.** Runs both over a corpus and compares line by line. For error
  lines only the stage (`decode` or `playable`) is compared.
- **`model/bmtest/fuzz.py`.** Generates mutated maps aimed at decoder and geometry edge cases:
  - number formats and extreme values;
  - missing and extra fields;
  - path types and degrees, duplicate points, colinear and degenerate perfect curves;
  - section headers, comments, line swaps and duplicates;
  - format versions;
  - CR/CRLF line endings, BOMs, UTF-16 and invalid UTF-8;
  - hold, spinner and odd type bits.
- **`bmtest sorttest N SEED | bmdump sorttest`.** Checks the introsort model against .NET's
  `List<T>.Sort` on arrays with many ties.

## Test results (2026-10-21, NoMod)

(Since the mods work, the dump also has `effect` lines, the time-signature numerator on `timing` lines, `kiai=` on
every object, `classic=` on sliders/heads/tails and `st=` on tails; NoMod re-checked on 300 maps.)

| corpus | maps | bit-identical |
|---|---|---|
| crawled `data/beatmaps` (1500, all v14/v128) + lazer test resources (80 `.osu` + 45 from `.osz/.olz`; 33 non-osu modes compared as `mode N`) | 1625 | **1625** |
| real maps with rewritten format version (v3..v13, v128: +24 ms offset, old stacking, v<8 tick multiplier, int coordinates, legacy perfect/catmull rules) | 1500 | **1500** |
| `fuzz.py` mutations (seeds 1, 2) | 6000 | **6000** (incl. 72 where both sides fail decode/playable at the same stage, 335 non-osu modes) |
| `gen.py` synthetic (seeds 7, 8) | 7000 | **7000** |
| introsort vs `List<T>.Sort` (`sorttest 3000 1`) | 3000 arrays | **3000** |

Residual mismatches: none observed. The test is sensitive: disabling the single "no extension when last two path
points are equal" quirk produced mismatches in 300 synthetic maps. Gaps: real old-format (v<14) maps only via
test resources and header rewriting (the crawler only returned v14); mods not yet tested (hooks only);
ICU culture header comparison (see trust assumptions); decoder error *messages* are not compared, only the stage.

Reproduce:
```
cd model && lake build bmdump && (cd bmtest && dotnet build -c Release -m:1 -p:BuildProjectReferences=false)
python3 -I bmtest/run_corpus.py --work /tmp/bm            # default corpus
python3 -I bmtest/fuzz.py OUT 2000 1 @seeds.txt; python3 -I bmtest/run_corpus.py --work /tmp/fz OUT/*.osu
python3 -I bmtest/gen.py OUT 3000 7;   python3 -I bmtest/reversion.py OUT 3 @list.txt
# mods (wrap in tools/heavy; run_corpus caps the .NET heap and kills any process above ~1 GB RSS)
../tools/heavy python3 -I bmtest/run_corpus.py --work W --mods random:11            # combos
../tools/heavy python3 -I bmtest/run_corpus.py --work W --limit 400 --mods single:1:TP
dotnet bmtest/bin/Release/net10.0/bmtest.dll modinfo                              # settings table
```
