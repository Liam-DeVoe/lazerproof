# Lazer / osu-framework code coverage of the oracle corpora (2026-10-22)

Question: which lazer and osu-framework code does the oracle actually execute on our differential-test corpora?
Which judgement- or score-relevant branches does it never take? Is that logic in the Lean model? And do targeted
inputs that do take those branches agree between the model and the oracle?

**Headline.** The judgement core is 113 files: DHOs, SliderInputManager, spinner tracking, hit policies, hit windows,
score/health/judgement processors, the FSC, the replay input handler, the replay decoder, the gameplay mods, and the
framework's KeyBindingContainer, Interpolation and clocks. On the 2675-job corpus it reaches **80.8% of lines
(4393/5437), 69.7% of branches (1785/2562) and 75.1% of methods**.

The code that makes gameplay decisions is effectively fully covered. Every never-executed line in the core was
classified (§3):

- Only **5 judgement/score-relevant, reachable gaps** were found. All five are modelled in Lean.
- The rest of the uncovered core code is one of:
  - unreachable in `.osr` playback: rewinding, spectator frames, pause or seek, non-frame-stable playback, live input
    devices;
  - unreachable for the osu! ruleset: other rulesets' results and hit windows, invariant `throw`s;
  - not judgement-relevant: UI, samples, settings UI, HUD, skinning.

Targeted generators (`difftest/covfuzz.py`) now hit all 5 gaps, confirmed by re-measuring coverage. They gave
**1200/1200 model-vs-oracle matches** (400 jobs × catchup/perframe/dense1ms, 14k judgements), plus 420 earlier
exploratory jobs, also all matching. **No mismatch was found, so nothing was added to ISSUES.md.**

## 1. Method

- **Tool:** coverlet.console 10.1.0 (IL instrumentation; line and IL-branch coverage), installed with
  `dotnet tool install -g coverlet.console`.
- **Driver:** `difftest/lazer_cov.py` (`run` / `merge` / `report` / `branches`). Each chunk is one
  `tools/heavy coverlet … --target covbin/oracle --targetargs "batch --list …"` call, sized to take ≤ 10 min
  (CHUNK rule). Coverage json is merged by summing hits.
- **Instrumented oracle.** It is a separate plain (non-R2R) Release build of the unchanged `oracle/oracle.csproj`:
  `dotnet build -c Release -m:1 -o data/wip/lazer-coverage/covbin`.
  - It incrementally reuses the existing lazer obj outputs, so the `osu.Game*.dll` files are byte-identical to the
    lazer build outputs, and `osu.Framework.dll` is the nuget dll.
  - The deployed R2R oracle in `oracle/bin/Release/net10.0` and its result cache are never touched or read, except for
    the read-only sanity check below.
  - coverlet rewrites the dlls in covbin in place for the duration of one call and then restores them. If a call is
    killed, covbin must be rebuilt: delete the 3 dlls, then rebuild.
- **osu-framework line info.** This comes from the nuget symbol package (`ppy.osu.framework 2026.921.1 .snupkg`
  → `osu.Framework.pdb`). Its CI paths (`D:\a\osu-framework\osu-framework\…`) are mapped to the local
  `osu-framework/` checkout at the same tag. Instrumented assemblies: `osu.Game`, `osu.Game.Rulesets.Osu`,
  `osu.Framework`.
- **Sanity: instrumentation does not change results.**
  - 391 instrumented job outputs had a deployed-oracle cache entry with the same options, and all 391 are
    byte-identical (`cKKK.check.json`, `cache_equal`).
  - Another 30 stable perframe jobs were re-run on the deployed oracle: 30/30 identical. A further 400/400 covfuzz
    jobs are identical too.
- **Interpreting the data.**
  - Coverlet "branches" are IL conditional-branch arms. `?.`, `??`, `is` patterns, `foreach` and `switch` tables
    generate many arms that have no source-level meaning, so the triage is driven by **never-executed lines inside
    entered methods** (`branches --lines`) and by **never-entered methods**. Branch arms were used only for
    single-line conditions.
  - Known artefact: a `break;` inside a `foreach` (it compiles to `leave`) can be reported as unhit even when the
    preceding lines ran (LegacyDrainingHealthProcessor.cs:88, :105).
  - Generated code (`obj/`, source generators) is excluded.

Reproduce:

```sh
python3 -I difftest/lazer_cov.py run --list data/wip/lazer-coverage/lists/X.txt --name X --chunk 40 -- --schedule catchup [--replace-mods]
python3 -I difftest/lazer_cov.py merge && python3 -I difftest/lazer_cov.py report --md OUT.md
python3 -I difftest/lazer_cov.py branches --lines --files 'SliderInputManager|HitPolicy'    # triage listing
```

Driver script: `data/wip/lazer-coverage/runall.sh`. Raw data: `data/wip/lazer-coverage/runs/*` (json.gz per chunk,
instrumented outputs, checks), `merged_corpus.json.gz` (corpus only), `merged.json.gz` (+covfuzz), and `report_*.json`.

### Corpora measured (2675 jobs, 0 oracle errors)

| run | jobs | schedule | content |
|---|---|---|---|
| syn_cu | 210 | catchup | synthetic synA-D (data/wip/rust-sim; difftest/synth.py: circles/sliders/spinners, edge timing, notelock, frame gaps, stable+lazer format) |
| simmods_cu / _pf / _d | 1310 / 220 / 41 | catchup / perframe / dense1ms | the 37 sim-mods job corpora (`data/wip/rust-sim/simmods/w_*`, modgen_sim pools M4-M8/ALL with settings; real and synthetic maps), `--replace-mods` |
| stable_cu (+_b) | 300 | catchup | random sample (seed 7) of the real stable replays (data/replays, auto-Classic) |
| stable_pf | 60 | perframe | another 60 stable replays |
| v2_cu | 474 | catchup | lazer scores (data/replays_v2): every one of the 374 mod combinations at least once, 3 per combination for the 20 most common |
| v2_pf | 60 | perframe | 60 more lazer scores |
| covfuzz (targeted, §4) | 400 | catchup | `difftest/covfuzz.py` seeds 1 and 2 (seed 2 with random ALL-pool mods) |

## 2. Coverage tables (corpus, before the targeted inputs)

After adding covfuzz, the judgement core goes to 81.0% of lines (4402/5437) and 70.1% of branches (1795/2562). Every
newly hit line is one of the §3 targets, plus `OsuModTargetPractice.cs:215`.

The module totals are low because most of osu.Game is UI, online, database, editor and so on. The per-area rows are
the meaningful ones. In several areas the coverage is dominated by visual or settings code, for example "osu ruleset:
UI" (cursor trails, smoke, follow points) and "framework: input" (keyboard, mouse buttons, touch, tablet, joystick,
focus: replay input bypasses these and injects actions through `ReplayState`).

| scope | lines | branches | methods |
|---|---|---|---|
| **judgement core (113 files)** | 80.8% (4393/5437) | 69.7% (1785/2562) | 75.1% (1065/1419) |
| osu.Framework.dll | 21.1% (8407/39855) | 16.8% (3136/18655) | 22.5% (2249/10012) |
| osu.Game.Rulesets.Osu.dll | 46.4% (6036/13008) | 43.0% (2026/4714) | 53.9% (1165/2162) |
| osu.Game.dll | 5.6% (7776/139354) | 6.7% (2536/37856) | 8.0% (1879/23601) |

### Per area

| area | files | lines | branches | methods |
|---|---|---|---|---|
| osu ruleset: DHOs | 19 | 89.5% (1103/1232) | 78.0% (343/440) | 89.7% |
| osu ruleset: hit objects | 11 | 97.7% (260/266) | 90.8% (69/76) | 95.8% |
| osu ruleset: judgements/scoring | 13 | 84.2% (170/202) | 87.5% (112/128) | 89.7% |
| osu ruleset: mods | 38 | 88.7% (1208/1362) | 86.6% (434/501) | 71.6% |
| osu ruleset: UI (playfield, hit policies, cursor) | 25 | 46.4% (484/1042) | 46.5% (132/284) | 62.6% |
| osu ruleset: replays/input | 5 | 76.8% (169/220) | 52.1% (75/144) | 81.0% |
| osu ruleset: beatmaps | 3 | 71.5% (118/165) | 70.3% (83/118) | 91.7% |
| osu.Game: scoring | 13 | 72.1% (475/659) | 68.2% (272/399) | 72.5% |
| osu.Game: judgements | 6 | 69.4% (102/147) | 63.2% (36/57) | 77.6% |
| osu.Game: DrawableHitObject / pooling | 7 | 80.5% (391/486) | 58.4% (146/250) | 82.4% |
| osu.Game: Rulesets.UI (DrawableRuleset, FSC, playfield, HOC) | 24 | 35.8% (548/1532) | 28.5% (168/589) | 39.5% |
| osu.Game: replays | 6 | 63.8% (83/130) | 50.0% (37/74) | 68.9% |
| osu.Game: mods (base) | 45 | 56.2% (682/1213) | 41.1% (153/372) | 44.8% |
| osu.Game: legacy score decoder | 5 | 54.0% (170/315) | 53.9% (89/165) | 48.9% |
| osu.Game: scoring misc | 3 | 47.7% (71/149) | 47.1% (56/119) | 55.9% |
| osu.Game: beatmaps (control points, decoder) | 15 | 67.4% (696/1032) | 58.1% (320/551) | 66.4% |
| osu.Game: gameplay clocks/breaks | 6 | 50.6% (80/158) | 33.3% (18/54) | 37.9% |
| framework: clocks | 11 | 56.9% (145/255) | 37.8% (37/98) | 62.0% |
| framework: input (queues, states, handlers) | 112 | 23.0% (542/2352) | 19.7% (269/1367) | 26.7% |
| framework: transforms | 9 | 64.2% (423/659) | 63.4% (242/382) | 67.7% |
| framework: lifetime/containers | 11 | 47.3% (868/1836) | 48.3% (432/895) | 62.5% |
| framework: Drawable | 1 | 81.0% (613/757) | 70.9% (368/519) | 79.7% |
| framework: bindables | 25 | 46.4% (463/998) | 38.5% (221/574) | 49.7% |
| framework: utils/math | 24 | 28.4% (367/1291) | 23.7% (161/680) | 33.2% |

### Per file (focus areas; files with >= 1 coverable line)

<details><summary>osu ruleset: DHOs (19 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/Connections/FollowPoint.cs | 100.0% (24/24) | - (0/0) | 3/3 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/Connections/FollowPointConnection.cs | 100.0% (78/78) | 66.7% (4/6) | 5/5 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/Connections/FollowPointLifetimeEntry.cs | 92.7% (38/41) | 92.9% (13/14) | 6/8 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/Connections/FollowPointRenderer.cs | 69.8% (44/63) | 70.0% (7/10) | 6/10 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableHitCircle.cs | 91.2% (146/160) | 86.1% (31/36) | 34/37 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableOsuHitObject.cs | 98.2% (56/57) | 88.9% (16/18) | 19/20 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableOsuJudgement.cs | 81.8% (36/44) | 57.1% (8/14) | 8/10 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSlider.cs | 88.0% (169/192) | 67.4% (62/92) | 31/34 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderBall.cs | 93.3% (28/30) | 100.0% (2/2) | 4/4 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderHead.cs | 92.0% (23/25) | 83.3% (5/6) | 10/11 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderRepeat.cs | 79.8% (67/84) | 84.4% (27/32) | 12/15 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderTail.cs | 77.6% (45/58) | 50.0% (7/14) | 13/16 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderTick.cs | 95.2% (40/42) | 75.0% (3/4) | 7/8 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSpinner.cs | 94.7% (160/169) | 79.8% (67/84) | 30/31 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSpinnerBonusTick.cs | 50.0% (2/4) | - (0/0) | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSpinnerTick.cs | 100.0% (14/14) | 100.0% (2/2) | 5/5 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/SkinnableLighting.cs | 100.0% (13/13) | 100.0% (8/8) | 4/4 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/SliderInputManager.cs | 91.7% (100/109) | 86.4% (76/88) | 15/15 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/SpinnerSpinHistory.cs | 80.0% (20/25) | 50.0% (5/10) | 5/5 |

</details>

<details><summary>osu ruleset: hit objects (11 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| lazer/osu.Game.Rulesets.Osu/Objects/HitCircle.cs | 100.0% (1/1) | - (0/0) | 1/1 |
| lazer/osu.Game.Rulesets.Osu/Objects/OsuHitObject.cs | 94.0% (63/67) | 95.0% (19/20) | 37/41 |
| lazer/osu.Game.Rulesets.Osu/Objects/Slider.cs | 99.2% (121/122) | 88.1% (37/42) | 35/36 |
| lazer/osu.Game.Rulesets.Osu/Objects/SliderEndCircle.cs | 100.0% (14/14) | 100.0% (2/2) | 7/7 |
| lazer/osu.Game.Rulesets.Osu/Objects/SliderHeadCircle.cs | 100.0% (1/1) | 100.0% (2/2) | 1/1 |
| lazer/osu.Game.Rulesets.Osu/Objects/SliderRepeat.cs | 100.0% (3/3) | - (0/0) | 2/2 |
| lazer/osu.Game.Rulesets.Osu/Objects/SliderTailCircle.cs | 100.0% (5/5) | 100.0% (2/2) | 4/4 |
| lazer/osu.Game.Rulesets.Osu/Objects/SliderTick.cs | 100.0% (11/11) | 100.0% (2/2) | 6/6 |
| lazer/osu.Game.Rulesets.Osu/Objects/Spinner.cs | 97.1% (34/35) | 83.3% (5/6) | 14/14 |
| lazer/osu.Game.Rulesets.Osu/Objects/SpinnerBonusTick.cs | 100.0% (2/2) | - (0/0) | 2/2 |
| lazer/osu.Game.Rulesets.Osu/Objects/SpinnerTick.cs | 100.0% (5/5) | - (0/0) | 5/5 |

</details>

<details><summary>osu ruleset: judgements/scoring (13 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| lazer/osu.Game.Rulesets.Osu/Judgements/OsuHitCircleJudgementResult.cs | 66.7% (2/3) | - (0/0) | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Judgements/OsuIgnoreJudgement.cs | 100.0% (1/1) | - (0/0) | 1/1 |
| lazer/osu.Game.Rulesets.Osu/Judgements/OsuJudgement.cs | 100.0% (1/1) | - (0/0) | 1/1 |
| lazer/osu.Game.Rulesets.Osu/Judgements/OsuJudgementResult.cs | 100.0% (2/2) | - (0/0) | 1/1 |
| lazer/osu.Game.Rulesets.Osu/Judgements/OsuSliderJudgementResult.cs | 100.0% (4/4) | - (0/0) | 1/1 |
| lazer/osu.Game.Rulesets.Osu/Judgements/OsuSpinnerJudgementResult.cs | 80.0% (4/5) | - (0/0) | 2/3 |
| lazer/osu.Game.Rulesets.Osu/Judgements/SliderTickJudgement.cs | 100.0% (1/1) | - (0/0) | 1/1 |
| lazer/osu.Game.Rulesets.Osu/Scoring/OsuHealthProcessor.cs | 97.4% (38/39) | 98.0% (48/49) | 5/5 |
| lazer/osu.Game.Rulesets.Osu/Scoring/OsuHitWindows.cs | 92.9% (13/14) | 80.0% (8/10) | 4/4 |
| lazer/osu.Game.Rulesets.Osu/Scoring/OsuLegacyHealthProcessor.cs | 100.0% (27/27) | 88.9% (24/27) | 5/5 |
| lazer/osu.Game.Rulesets.Osu/Scoring/OsuScoreMultiplierCalculatorV1.cs | 0.0% (0/28) | 0.0% (0/10) | 0/2 |
| lazer/osu.Game.Rulesets.Osu/Scoring/OsuScoreMultiplierCalculatorV2.cs | 100.0% (70/70) | 100.0% (24/24) | 10/10 |
| lazer/osu.Game.Rulesets.Osu/Scoring/OsuScoreProcessor.cs | 100.0% (7/7) | 100.0% (8/8) | 3/3 |

</details>

<details><summary>osu ruleset: mods (38 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| lazer/osu.Game.Rulesets.Osu/Mods/InputBlockingMod.cs | 93.8% (30/32) | 94.4% (17/18) | 9/10 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModAlternate.cs | 42.9% (3/7) | - (0/0) | 3/7 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModApproachDifferent.cs | 80.0% (28/35) | 69.2% (9/13) | 7/10 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModAutopilot.cs | 84.0% (21/25) | 100.0% (6/6) | 5/9 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModAutoplay.cs | 0.0% (0/2) | - (0/0) | 0/2 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModBarrelRoll.cs | 100.0% (15/15) | 100.0% (2/2) | 3/3 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModBlinds.cs | 87.8% (72/82) | 83.3% (5/6) | 14/20 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModBloom.cs | 80.6% (29/36) | 100.0% (2/2) | 9/14 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModBubbles.cs | 92.2% (95/103) | 54.2% (13/24) | 15/19 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModCinema.cs | 0.0% (0/2) | - (0/0) | 0/2 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModClassic.cs | 100.0% (40/40) | 100.0% (28/28) | 12/12 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModDeflate.cs | 70.0% (7/10) | - (0/0) | 3/6 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModDepth.cs | 94.0% (63/67) | 94.4% (17/18) | 16/20 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModDifficultyAdjust.cs | 45.5% (20/44) | 16.7% (4/24) | 5/11 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModEasy.cs | 75.0% (3/4) | - (0/0) | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModFlashlight.cs | 100.0% (36/36) | 100.0% (6/6) | 13/13 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModFreezeFrame.cs | 87.8% (36/41) | 94.4% (17/18) | 5/9 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModGrow.cs | 70.0% (7/10) | - (0/0) | 3/6 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModHardRock.cs | 100.0% (9/9) | - (0/0) | 3/3 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModHidden.cs | 92.3% (60/65) | 93.5% (43/46) | 11/12 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModMagnetised.cs | 85.7% (24/28) | 90.0% (9/10) | 7/11 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModMirror.cs | 91.7% (11/12) | 75.0% (3/4) | 3/4 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModNoScope.cs | 93.8% (15/16) | 100.0% (4/4) | 5/6 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModObjectScaleTween.cs | 92.3% (12/13) | 100.0% (12/12) | 5/6 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModRandom.cs | 96.7% (59/61) | 93.8% (30/32) | 9/10 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModRelax.cs | 87.0% (60/69) | 93.5% (43/46) | 10/13 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModRepel.cs | 88.9% (32/36) | 91.7% (11/12) | 7/11 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModSingleTap.cs | 42.9% (3/7) | 100.0% (2/2) | 3/7 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModSpinIn.cs | 83.3% (20/24) | 100.0% (10/10) | 5/9 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModSpunOut.cs | 68.4% (13/19) | 75.0% (3/4) | 4/9 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModStrictTracking.cs | 94.8% (91/96) | 88.5% (23/26) | 11/15 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModSuddenDeath.cs | 100.0% (10/10) | 100.0% (8/8) | 3/3 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModSynesthesia.cs | 100.0% (22/22) | 62.5% (5/8) | 4/4 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTargetPractice.cs | 96.5% (191/198) | 88.8% (71/80) | 27/32 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTouchDevice.cs | 50.0% (1/2) | - (0/0) | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTraceable.cs | 78.6% (22/28) | 92.9% (13/14) | 8/13 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTransform.cs | 81.8% (18/22) | 100.0% (8/8) | 5/9 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModWiggle.cs | 88.2% (30/34) | 100.0% (10/10) | 8/12 |

</details>

<details><summary>osu ruleset: UI (playfield, hit policies, cursor) (25 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| lazer/osu.Game.Rulesets.Osu/UI/AnyOrderHitPolicy.cs | 0.0% (0/3) | - (0/0) | 0/3 |
| lazer/osu.Game.Rulesets.Osu/UI/Cursor/CursorRippleVisualiser.cs | 70.5% (31/44) | 62.5% (5/8) | 7/8 |
| lazer/osu.Game.Rulesets.Osu/UI/Cursor/CursorTrail.cs | 50.3% (93/185) | 40.4% (21/52) | 26/32 |
| lazer/osu.Game.Rulesets.Osu/UI/Cursor/OsuCursor.cs | 38.5% (42/109) | 41.7% (5/12) | 14/16 |
| lazer/osu.Game.Rulesets.Osu/UI/Cursor/OsuCursorContainer.cs | 93.2% (55/59) | 78.6% (11/14) | 14/15 |
| lazer/osu.Game.Rulesets.Osu/UI/Cursor/SkinnableCursor.cs | 100.0% (6/6) | 50.0% (2/4) | 3/3 |
| lazer/osu.Game.Rulesets.Osu/UI/DrawableOsuRuleset.cs | 68.0% (17/25) | 75.0% (6/8) | 12/14 |
| lazer/osu.Game.Rulesets.Osu/UI/LegacyHitPolicy.cs | 95.7% (22/23) | 95.0% (19/20) | 4/4 |
| lazer/osu.Game.Rulesets.Osu/UI/OsuPlayfield.cs | 93.9% (92/98) | 85.0% (17/20) | 19/23 |
| lazer/osu.Game.Rulesets.Osu/UI/OsuPlayfieldAdjustmentContainer.cs | 100.0% (22/22) | 50.0% (1/2) | 5/5 |
| lazer/osu.Game.Rulesets.Osu/UI/OsuReplayRecorder.cs | 0.0% (0/3) | - (0/0) | 0/2 |
| lazer/osu.Game.Rulesets.Osu/UI/OsuResumeOverlay.cs | 51.2% (44/86) | 10.7% (3/28) | 9/20 |
| lazer/osu.Game.Rulesets.Osu/UI/OsuSettingsSubsection.cs | 0.0% (0/41) | - (0/0) | 0/2 |
| lazer/osu.Game.Rulesets.Osu/UI/OsuTouchInputMapper.cs | 12.3% (7/57) | 0.0% (0/32) | 3/9 |
| lazer/osu.Game.Rulesets.Osu/UI/ReplayAnalysis/AnalysisFrameEntry.cs | 0.0% (0/8) | - (0/0) | 0/3 |
| lazer/osu.Game.Rulesets.Osu/UI/ReplayAnalysis/AnalysisMarker.cs | 0.0% (0/6) | - (0/0) | 0/3 |
| lazer/osu.Game.Rulesets.Osu/UI/ReplayAnalysis/ClickMarker.cs | 0.0% (0/56) | - (0/0) | 0/2 |
| lazer/osu.Game.Rulesets.Osu/UI/ReplayAnalysis/ClickMarkerContainer.cs | 0.0% (0/4) | - (0/0) | 0/2 |
| lazer/osu.Game.Rulesets.Osu/UI/ReplayAnalysis/CursorPathContainer.cs | 0.0% (0/27) | 0.0% (0/2) | 0/8 |
| lazer/osu.Game.Rulesets.Osu/UI/ReplayAnalysis/FrameMarker.cs | 0.0% (0/38) | 0.0% (0/4) | 0/2 |
| lazer/osu.Game.Rulesets.Osu/UI/ReplayAnalysis/FrameMarkerContainer.cs | 0.0% (0/4) | - (0/0) | 0/2 |
| lazer/osu.Game.Rulesets.Osu/UI/ReplayAnalysisOverlay.cs | 0.0% (0/60) | 0.0% (0/30) | 0/10 |
| lazer/osu.Game.Rulesets.Osu/UI/ReplayAnalysisSettings.cs | 0.0% (0/21) | - (0/0) | 0/7 |
| lazer/osu.Game.Rulesets.Osu/UI/SmokeContainer.cs | 100.0% (23/23) | 85.7% (12/14) | 11/11 |
| lazer/osu.Game.Rulesets.Osu/UI/StartTimeOrderedHitPolicy.cs | 88.2% (30/34) | 88.2% (30/34) | 5/5 |

</details>

<details><summary>osu ruleset: replays/input (5 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| lazer/osu.Game.Rulesets.Osu/OsuInputManager.cs | 69.6% (16/23) | 40.0% (4/10) | 9/13 |
| lazer/osu.Game.Rulesets.Osu/Replays/OsuAutoGenerator.cs | 76.2% (109/143) | 50.0% (51/102) | 10/11 |
| lazer/osu.Game.Rulesets.Osu/Replays/OsuAutoGeneratorBase.cs | 100.0% (26/26) | 100.0% (10/10) | 10/10 |
| lazer/osu.Game.Rulesets.Osu/Replays/OsuFramedReplayInputHandler.cs | 85.7% (6/7) | 100.0% (4/4) | 2/3 |
| lazer/osu.Game.Rulesets.Osu/Replays/OsuReplayFrame.cs | 57.1% (12/21) | 33.3% (6/18) | 3/5 |

</details>

<details><summary>osu ruleset: beatmaps (3 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| lazer/osu.Game.Rulesets.Osu/Beatmaps/OsuBeatmap.cs | 0.0% (0/28) | - (0/0) | 0/1 |
| lazer/osu.Game.Rulesets.Osu/Beatmaps/OsuBeatmapConverter.cs | 100.0% (41/41) | 60.7% (17/28) | 4/4 |
| lazer/osu.Game.Rulesets.Osu/Beatmaps/OsuBeatmapProcessor.cs | 80.2% (77/96) | 73.3% (66/90) | 7/7 |

</details>

<details><summary>osu.Game: scoring (13 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| lazer/osu.Game/Rulesets/Scoring/AccumulatingHealthProcessor.cs | 0.0% (0/7) | 0.0% (0/2) | 0/3 |
| lazer/osu.Game/Rulesets/Scoring/DefaultHitWindows.cs | 0.0% (0/20) | 0.0% (0/7) | 0/3 |
| lazer/osu.Game/Rulesets/Scoring/DrainingHealthProcessor.cs | 98.6% (73/74) | 88.2% (30/34) | 10/10 |
| lazer/osu.Game/Rulesets/Scoring/HealthProcessor.cs | 85.3% (29/34) | 85.0% (17/20) | 8/9 |
| lazer/osu.Game/Rulesets/Scoring/HitEvent.cs | 100.0% (8/8) | - (0/0) | 2/2 |
| lazer/osu.Game/Rulesets/Scoring/HitEventExtensions.cs | 0.0% (0/28) | 0.0% (0/20) | 0/7 |
| lazer/osu.Game/Rulesets/Scoring/HitResult.cs | 69.4% (34/49) | 74.4% (90/121) | 13/14 |
| lazer/osu.Game/Rulesets/Scoring/HitWindows.cs | 60.9% (14/23) | 57.1% (8/14) | 7/11 |
| lazer/osu.Game/Rulesets/Scoring/JudgementProcessor.cs | 76.8% (43/56) | 58.3% (14/24) | 14/16 |
| lazer/osu.Game/Rulesets/Scoring/Legacy/LegacyBeatmapConversionDifficultyInfo.cs | 56.7% (17/30) | - (0/0) | 8/12 |
| lazer/osu.Game/Rulesets/Scoring/LegacyDrainingHealthProcessor.cs | 91.7% (66/72) | 79.5% (35/44) | 8/8 |
| lazer/osu.Game/Rulesets/Scoring/ScoreMultiplierCalculator.cs | 100.0% (33/33) | 100.0% (14/14) | 9/9 |
| lazer/osu.Game/Rulesets/Scoring/ScoreProcessor.cs | 70.2% (158/225) | 64.6% (64/99) | 24/38 |

</details>

<details><summary>osu.Game: judgements (6 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| lazer/osu.Game/Rulesets/Judgements/DefaultJudgementPiece.cs | 0.0% (0/21) | 0.0% (0/2) | 0/4 |
| lazer/osu.Game/Rulesets/Judgements/DrawableJudgement.cs | 91.4% (64/70) | 79.2% (19/24) | 16/17 |
| lazer/osu.Game/Rulesets/Judgements/IgnoreJudgement.cs | 0.0% (0/1) | - (0/0) | 0/1 |
| lazer/osu.Game/Rulesets/Judgements/Judgement.cs | 34.8% (8/23) | 48.1% (13/27) | 3/6 |
| lazer/osu.Game/Rulesets/Judgements/JudgementResult.cs | 91.3% (21/23) | 100.0% (4/4) | 15/17 |
| lazer/osu.Game/Rulesets/Judgements/TextJudgementPiece.cs | 100.0% (9/9) | - (0/0) | 4/4 |

</details>

<details><summary>osu.Game: DrawableHitObject / pooling (7 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs | 84.8% (217/256) | 64.9% (87/134) | 62/75 |
| lazer/osu.Game/Rulesets/Objects/HitObject.cs | 90.2% (55/61) | 81.2% (26/32) | 19/22 |
| lazer/osu.Game/Rulesets/Objects/HitObjectLifetimeEntry.cs | 75.0% (27/36) | 50.0% (9/18) | 9/12 |
| lazer/osu.Game/Rulesets/Objects/Pooling/HitObjectEntryManager.cs | 36.4% (12/33) | 20.8% (5/24) | 3/6 |
| lazer/osu.Game/Rulesets/Objects/Pooling/PoolableDrawableWithLifetime.cs | 82.1% (46/56) | 53.3% (16/30) | 18/18 |
| lazer/osu.Game/Rulesets/Objects/Pooling/PooledDrawableWithLifetimeContainer.cs | 81.0% (34/42) | 25.0% (3/12) | 11/14 |
| lazer/osu.Game/Rulesets/Objects/SyntheticHitObjectEntry.cs | 0.0% (0/2) | - (0/0) | 0/1 |

</details>

<details><summary>osu.Game: Rulesets.UI (DrawableRuleset, FSC, playfield, HOC) (24 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| lazer/osu.Game/Rulesets/UI/DrawableRuleset.cs | 62.8% (103/164) | 32.1% (27/84) | 30/50 |
| lazer/osu.Game/Rulesets/UI/DrawableRulesetDependencies.cs | 63.9% (46/72) | 42.9% (12/28) | 16/38 |
| lazer/osu.Game/Rulesets/UI/DrawableRulesetDependenciesProvidingContainer.cs | 0.0% (0/9) | 0.0% (0/2) | 0/3 |
| lazer/osu.Game/Rulesets/UI/FrameStabilityContainer.cs | 81.6% (80/98) | 56.8% (42/74) | 19/23 |
| lazer/osu.Game/Rulesets/UI/GameplayCursorContainer.cs | 100.0% (3/3) | - (0/0) | 1/1 |
| lazer/osu.Game/Rulesets/UI/GameplaySampleTriggerSource.cs | 0.0% (0/69) | 0.0% (0/34) | 0/14 |
| lazer/osu.Game/Rulesets/UI/HitObjectContainer.cs | 72.5% (50/69) | 38.2% (13/34) | 16/20 |
| lazer/osu.Game/Rulesets/UI/JudgementContainer.cs | 100.0% (4/4) | - (0/0) | 1/1 |
| lazer/osu.Game/Rulesets/UI/JudgementPooler.cs | 100.0% (21/21) | 83.3% (5/6) | 5/5 |
| lazer/osu.Game/Rulesets/UI/ModIcon.cs | 0.0% (0/156) | 0.0% (0/26) | 0/16 |
| lazer/osu.Game/Rulesets/UI/ModSwitchSmall.cs | 0.0% (0/54) | 0.0% (0/12) | 0/5 |
| lazer/osu.Game/Rulesets/UI/ModSwitchTiny.cs | 0.0% (0/86) | 0.0% (0/18) | 0/7 |
| lazer/osu.Game/Rulesets/UI/ModTooltip.cs | 0.0% (0/86) | 0.0% (0/10) | 0/6 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs | 66.1% (119/180) | 48.9% (43/88) | 28/46 |
| lazer/osu.Game/Rulesets/UI/PlayfieldAdjustmentContainer.cs | 100.0% (3/3) | - (0/0) | 1/1 |
| lazer/osu.Game/Rulesets/UI/PlayfieldBorder.cs | 92.2% (71/77) | 50.0% (9/18) | 7/7 |
| lazer/osu.Game/Rulesets/UI/ReplayRecorder.cs | 0.0% (0/32) | 0.0% (0/16) | 0/9 |
| lazer/osu.Game/Rulesets/UI/RulesetInputManager.cs | 55.2% (48/87) | 40.5% (17/42) | 14/24 |
| lazer/osu.Game/Rulesets/UI/Scrolling/Algorithms/ConstantScrollAlgorithm.cs | 0.0% (0/6) | - (0/0) | 0/5 |
| lazer/osu.Game/Rulesets/UI/Scrolling/Algorithms/OverlappingScrollAlgorithm.cs | 0.0% (0/17) | 0.0% (0/6) | 0/7 |
| lazer/osu.Game/Rulesets/UI/Scrolling/Algorithms/SequentialScrollAlgorithm.cs | 0.0% (0/42) | 0.0% (0/14) | 0/12 |
| lazer/osu.Game/Rulesets/UI/Scrolling/DrawableScrollingRuleset.cs | 0.0% (0/90) | 0.0% (0/30) | 0/18 |
| lazer/osu.Game/Rulesets/UI/Scrolling/ScrollingHitObjectContainer.cs | 0.0% (0/98) | 0.0% (0/47) | 0/23 |
| lazer/osu.Game/Rulesets/UI/Scrolling/ScrollingPlayfield.cs | 0.0% (0/9) | - (0/0) | 0/8 |

</details>

<details><summary>osu.Game: replays (6 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| lazer/osu.Game/Input/Handlers/ReplayInputHandler.cs | 76.9% (20/26) | 91.7% (11/12) | 4/6 |
| lazer/osu.Game/Replays/Legacy/LegacyReplayFrame.cs | 68.4% (13/19) | 33.3% (4/12) | 9/11 |
| lazer/osu.Game/Replays/Replay.cs | 25.0% (2/8) | - (0/0) | 1/2 |
| lazer/osu.Game/Rulesets/Replays/AutoGenerator.cs | 23.5% (4/17) | 0.0% (0/4) | 2/6 |
| lazer/osu.Game/Rulesets/Replays/FramedReplayInputHandler.cs | 72.2% (39/54) | 47.8% (22/46) | 13/17 |
| lazer/osu.Game/Rulesets/Replays/ReplayFrame.cs | 83.3% (5/6) | - (0/0) | 2/3 |

</details>

<details><summary>osu.Game: mods (base) (45 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| lazer/osu.Game/Rulesets/Mods/DifficultyAdjustSettingsControl.cs | 0.0% (0/63) | 0.0% (0/12) | 0/15 |
| lazer/osu.Game/Rulesets/Mods/DifficultyBindable.cs | 85.7% (60/70) | 75.0% (21/28) | 18/19 |
| lazer/osu.Game/Rulesets/Mods/ICreateReplayData.cs | 0.0% (0/8) | 0.0% (0/2) | 0/5 |
| lazer/osu.Game/Rulesets/Mods/IMod.cs | 12.5% (1/8) | 0.0% (0/4) | 1/2 |
| lazer/osu.Game/Rulesets/Mods/MetronomeBeat.cs | 34.4% (11/32) | 16.7% (1/6) | 4/15 |
| lazer/osu.Game/Rulesets/Mods/Mod.cs | 23.5% (16/68) | 13.0% (6/46) | 4/29 |
| lazer/osu.Game/Rulesets/Mods/ModAccuracyChallenge.cs | 61.9% (26/42) | 41.7% (5/12) | 8/16 |
| lazer/osu.Game/Rulesets/Mods/ModAdaptiveSpeed.cs | 86.0% (86/100) | 82.1% (23/28) | 16/23 |
| lazer/osu.Game/Rulesets/Mods/ModAutoplay.cs | 9.1% (1/11) | - (0/0) | 1/11 |
| lazer/osu.Game/Rulesets/Mods/ModBarrelRoll.cs | 69.2% (18/26) | 33.3% (2/6) | 7/11 |
| lazer/osu.Game/Rulesets/Mods/ModCinema.cs | 5.3% (1/19) | 0.0% (0/2) | 1/10 |
| lazer/osu.Game/Rulesets/Mods/ModClassic.cs | 14.3% (1/7) | - (0/0) | 1/7 |
| lazer/osu.Game/Rulesets/Mods/ModDaycore.cs | 79.2% (19/24) | - (0/0) | 5/10 |
| lazer/osu.Game/Rulesets/Mods/ModDifficultyAdjust.cs | 50.0% (26/52) | 33.3% (8/24) | 8/18 |
| lazer/osu.Game/Rulesets/Mods/ModDoubleTime.cs | 58.3% (14/24) | 0.0% (0/6) | 5/11 |
| lazer/osu.Game/Rulesets/Mods/ModEasy.cs | 54.5% (6/11) | - (0/0) | 3/8 |
| lazer/osu.Game/Rulesets/Mods/ModEasyWithExtraLives.cs | 76.2% (16/21) | 50.0% (4/8) | 6/8 |
| lazer/osu.Game/Rulesets/Mods/ModExtensions.cs | 0.0% (0/18) | - (0/0) | 0/2 |
| lazer/osu.Game/Rulesets/Mods/ModFailCondition.cs | 87.5% (7/8) | 50.0% (1/2) | 5/6 |
| lazer/osu.Game/Rulesets/Mods/ModFlashlight.cs | 71.7% (99/138) | 66.7% (24/36) | 28/36 |
| lazer/osu.Game/Rulesets/Mods/ModHalfTime.cs | 58.3% (14/24) | 0.0% (0/6) | 5/11 |
| lazer/osu.Game/Rulesets/Mods/ModHardRock.cs | 40.0% (4/10) | - (0/0) | 3/9 |
| lazer/osu.Game/Rulesets/Mods/ModHidden.cs | 55.6% (5/9) | 100.0% (4/4) | 3/7 |
| lazer/osu.Game/Rulesets/Mods/ModMirror.cs | 25.0% (1/4) | - (0/0) | 1/4 |
| lazer/osu.Game/Rulesets/Mods/ModMuted.cs | 72.0% (36/50) | 66.7% (8/12) | 11/21 |
| lazer/osu.Game/Rulesets/Mods/ModNightcore.cs | 53.9% (41/76) | 2.1% (1/48) | 9/15 |
| lazer/osu.Game/Rulesets/Mods/ModNoFail.cs | 40.0% (6/15) | - (0/0) | 5/13 |
| lazer/osu.Game/Rulesets/Mods/ModNoMod.cs | 0.0% (0/5) | - (0/0) | 0/5 |
| lazer/osu.Game/Rulesets/Mods/ModNoScope.cs | 52.0% (13/25) | 33.3% (2/6) | 5/13 |
| lazer/osu.Game/Rulesets/Mods/ModPerfect.cs | 57.1% (8/14) | 87.5% (7/8) | 5/11 |
| lazer/osu.Game/Rulesets/Mods/ModPreset.cs | 0.0% (0/14) | 0.0% (0/14) | 0/8 |
| lazer/osu.Game/Rulesets/Mods/ModRandom.cs | 40.0% (2/5) | - (0/0) | 2/5 |
| lazer/osu.Game/Rulesets/Mods/ModRateAdjust.cs | 20.0% (2/10) | 0.0% (0/4) | 2/7 |
| lazer/osu.Game/Rulesets/Mods/ModRelax.cs | 40.0% (2/5) | - (0/0) | 2/5 |
| lazer/osu.Game/Rulesets/Mods/ModScoreV2.cs | 12.5% (1/8) | - (0/0) | 1/8 |
| lazer/osu.Game/Rulesets/Mods/ModSuddenDeath.cs | 40.0% (4/10) | 100.0% (2/2) | 3/9 |
| lazer/osu.Game/Rulesets/Mods/ModSynesthesia.cs | 20.0% (1/5) | - (0/0) | 1/5 |
| lazer/osu.Game/Rulesets/Mods/ModTimeRamp.cs | 73.5% (25/34) | 16.7% (2/12) | 9/13 |
| lazer/osu.Game/Rulesets/Mods/ModTouchDevice.cs | 22.2% (2/9) | - (0/0) | 2/9 |
| lazer/osu.Game/Rulesets/Mods/ModWindDown.cs | 90.0% (27/30) | 100.0% (4/4) | 8/11 |
| lazer/osu.Game/Rulesets/Mods/ModWindUp.cs | 90.0% (27/30) | 100.0% (4/4) | 8/11 |
| lazer/osu.Game/Rulesets/Mods/ModWithVisibilityAdjustment.cs | 97.0% (32/33) | 94.4% (17/18) | 8/8 |
| lazer/osu.Game/Rulesets/Mods/MultiMod.cs | 44.4% (4/9) | - (0/0) | 2/7 |
| lazer/osu.Game/Rulesets/Mods/RateAdjustModHelper.cs | 94.4% (17/18) | 87.5% (7/8) | 3/3 |
| lazer/osu.Game/Rulesets/Mods/UnknownMod.cs | 0.0% (0/11) | - (0/0) | 0/9 |

</details>

<details><summary>osu.Game: legacy score decoder (5 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| lazer/osu.Game/Scoring/Legacy/DatabasedLegacyScoreDecoder.cs | 0.0% (0/6) | 0.0% (0/2) | 0/3 |
| lazer/osu.Game/Scoring/Legacy/LegacyReplaySoloScoreInfo.cs | 40.0% (8/20) | 0.0% (0/2) | 7/8 |
| lazer/osu.Game/Scoring/Legacy/LegacyScoreDecoder.cs | 87.2% (143/164) | 79.1% (72/91) | 5/8 |
| lazer/osu.Game/Scoring/Legacy/LegacyScoreEncoder.cs | 0.0% (0/61) | 0.0% (0/20) | 0/9 |
| lazer/osu.Game/Scoring/Legacy/ScoreInfoExtensions.cs | 29.7% (19/64) | 34.0% (17/50) | 11/19 |

</details>

<details><summary>osu.Game: scoring misc (3 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| lazer/osu.Game/Scoring/HitResultDisplayStatistic.cs | 0.0% (0/10) | - (0/0) | 0/5 |
| lazer/osu.Game/Scoring/ScoreInfo.cs | 57.7% (71/123) | 51.4% (56/109) | 38/58 |
| lazer/osu.Game/Scoring/ScoreInfoExtensions.cs | 0.0% (0/16) | 0.0% (0/10) | 0/5 |

</details>

<details><summary>osu.Game: beatmaps (control points, decoder) (15 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| lazer/osu.Game/Beatmaps/Beatmap.cs | 57.9% (44/76) | 0.0% (0/12) | 27/32 |
| lazer/osu.Game/Beatmaps/BeatmapConverter.cs | 83.3% (40/48) | 80.0% (8/10) | 5/9 |
| lazer/osu.Game/Beatmaps/BeatmapDifficulty.cs | 73.1% (19/26) | 100.0% (12/12) | 10/11 |
| lazer/osu.Game/Beatmaps/BeatmapDifficultyCache.cs | 19.0% (37/195) | 7.4% (4/54) | 7/38 |
| lazer/osu.Game/Beatmaps/BeatmapProcessor.cs | 100.0% (10/10) | 100.0% (2/2) | 4/4 |
| lazer/osu.Game/Beatmaps/ControlPoints/ControlPoint.cs | 66.7% (14/21) | 33.3% (4/12) | 7/11 |
| lazer/osu.Game/Beatmaps/ControlPoints/ControlPointGroup.cs | 46.7% (14/30) | 16.7% (3/18) | 5/10 |
| lazer/osu.Game/Beatmaps/ControlPoints/ControlPointInfo.cs | 69.2% (83/120) | 61.5% (48/78) | 18/26 |
| lazer/osu.Game/Beatmaps/ControlPoints/DifficultyControlPoint.cs | 75.9% (22/29) | 20.0% (2/10) | 8/12 |
| lazer/osu.Game/Beatmaps/ControlPoints/EffectControlPoint.cs | 78.8% (26/33) | 40.0% (4/10) | 10/14 |
| lazer/osu.Game/Beatmaps/ControlPoints/SampleControlPoint.cs | 60.0% (21/35) | 33.3% (4/12) | 9/16 |
| lazer/osu.Game/Beatmaps/ControlPoints/TimingControlPoint.cs | 79.1% (34/43) | 0.0% (0/8) | 13/18 |
| lazer/osu.Game/Beatmaps/Formats/LegacyBeatmapDecoder.cs | 93.0% (254/273) | 71.7% (177/247) | 23/23 |
| lazer/osu.Game/Beatmaps/Formats/LegacyDecoder.cs | 86.2% (69/80) | 80.0% (48/60) | 13/16 |
| lazer/osu.Game/Beatmaps/IBeatmapDifficultyInfo.cs | 69.2% (9/13) | 66.7% (4/6) | 5/7 |

</details>

<details><summary>osu.Game: gameplay clocks/breaks (6 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| lazer/osu.Game/Beatmaps/Timing/BreakPeriod.cs | 65.0% (13/20) | 21.4% (3/14) | 6/10 |
| lazer/osu.Game/Beatmaps/Timing/TimeSignature.cs | 83.3% (10/12) | 75.0% (3/4) | 5/7 |
| lazer/osu.Game/Screens/Play/BreakTracker.cs | 95.7% (22/23) | 83.3% (5/6) | 5/5 |
| lazer/osu.Game/Screens/Play/GameplayClockContainer.cs | 0.0% (0/62) | 0.0% (0/12) | 0/25 |
| lazer/osu.Game/Screens/Play/GameplayClockExtensions.cs | 100.0% (4/4) | 50.0% (1/2) | 1/1 |
| lazer/osu.Game/Screens/Play/GameplayState.cs | 83.8% (31/37) | 37.5% (6/16) | 5/10 |

</details>

<details><summary>framework: clocks (11 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| osu-framework/osu.Framework/Timing/DecouplingFramedClock.cs | 40.3% (31/77) | 18.4% (7/38) | 9/16 |
| osu-framework/osu.Framework/Timing/FrameTimeInfo.cs | 0.0% (0/1) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Timing/FramedClock.cs | 97.7% (42/43) | 91.7% (11/12) | 12/13 |
| osu-framework/osu.Framework/Timing/FramedOffsetClock.cs | 85.7% (6/7) | - (0/0) | 3/4 |
| osu-framework/osu.Framework/Timing/IFrameBasedClock.cs | 100.0% (5/5) | - (0/0) | 1/1 |
| osu-framework/osu.Framework/Timing/InterpolatingFramedClock.cs | 62.0% (31/50) | 29.2% (7/24) | 11/13 |
| osu-framework/osu.Framework/Timing/ManualClock.cs | 100.0% (3/3) | - (0/0) | 3/3 |
| osu-framework/osu.Framework/Timing/ManualFramedClock.cs | 0.0% (0/6) | - (0/0) | 0/6 |
| osu-framework/osu.Framework/Timing/OffsetClock.cs | 0.0% (0/6) | - (0/0) | 0/4 |
| osu-framework/osu.Framework/Timing/StopwatchClock.cs | 33.3% (9/27) | 75.0% (3/4) | 5/12 |
| osu-framework/osu.Framework/Timing/ThrottledFrameClock.cs | 60.0% (18/30) | 45.0% (9/20) | 5/6 |

</details>

<details><summary>framework: input (queues, states, handlers) (112 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| osu-framework/osu.Framework/Input/Bindings/KeyBinding.cs | 72.7% (8/11) | - (0/0) | 4/6 |
| osu-framework/osu.Framework/Input/Bindings/KeyBindingContainer.cs | 36.5% (62/170) | 26.4% (43/163) | 15/22 |
| osu-framework/osu.Framework/Input/Bindings/KeyBindingExtensions.cs | 0.0% (0/1) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/Bindings/KeyCombination.cs | 20.5% (23/112) | 7.3% (8/109) | 9/25 |
| osu-framework/osu.Framework/Input/ButtonEventManager.cs | 12.1% (4/33) | 0.0% (0/14) | 2/9 |
| osu-framework/osu.Framework/Input/CustomInputManager.cs | 81.8% (9/11) | 75.0% (3/4) | 4/5 |
| osu-framework/osu.Framework/Input/Events/ClickEvent.cs | 0.0% (0/2) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/Events/DoubleClickEvent.cs | 0.0% (0/2) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/Events/DragEndEvent.cs | 0.0% (0/2) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/Events/DragEvent.cs | 0.0% (0/5) | 0.0% (0/2) | 0/3 |
| osu-framework/osu.Framework/Input/Events/DragStartEvent.cs | 0.0% (0/3) | - (0/0) | 0/2 |
| osu-framework/osu.Framework/Input/Events/FocusEvent.cs | 0.0% (0/3) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/Events/FocusLostEvent.cs | 0.0% (0/3) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/Events/HoverEvent.cs | 100.0% (2/2) | - (0/0) | 1/1 |
| osu-framework/osu.Framework/Input/Events/HoverLostEvent.cs | 100.0% (2/2) | - (0/0) | 1/1 |
| osu-framework/osu.Framework/Input/Events/JoystickAxisMoveEvent.cs | 0.0% (0/6) | - (0/0) | 0/3 |
| osu-framework/osu.Framework/Input/Events/JoystickButtonEvent.cs | 0.0% (0/4) | - (0/0) | 0/2 |
| osu-framework/osu.Framework/Input/Events/JoystickEvent.cs | 0.0% (0/4) | - (0/0) | 0/3 |
| osu-framework/osu.Framework/Input/Events/JoystickPressEvent.cs | 0.0% (0/2) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/Events/JoystickReleaseEvent.cs | 0.0% (0/2) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/Events/KeyBindingEvent.cs | 100.0% (3/3) | - (0/0) | 1/1 |
| osu-framework/osu.Framework/Input/Events/KeyBindingPressEvent.cs | 100.0% (3/3) | - (0/0) | 1/1 |
| osu-framework/osu.Framework/Input/Events/KeyBindingReleaseEvent.cs | 100.0% (2/2) | - (0/0) | 1/1 |
| osu-framework/osu.Framework/Input/Events/KeyBindingScrollEvent.cs | 0.0% (0/4) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/Events/KeyDownEvent.cs | 0.0% (0/4) | - (0/0) | 0/2 |
| osu-framework/osu.Framework/Input/Events/KeyUpEvent.cs | 0.0% (0/2) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/Events/KeyboardEvent.cs | 0.0% (0/7) | - (0/0) | 0/5 |
| osu-framework/osu.Framework/Input/Events/MidiDownEvent.cs | 0.0% (0/2) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/Events/MidiEvent.cs | 0.0% (0/8) | - (0/0) | 0/5 |
| osu-framework/osu.Framework/Input/Events/MidiUpEvent.cs | 0.0% (0/2) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/Events/MouseButtonEvent.cs | 0.0% (0/6) | 0.0% (0/2) | 0/3 |
| osu-framework/osu.Framework/Input/Events/MouseDownEvent.cs | 0.0% (0/2) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/Events/MouseEvent.cs | 40.0% (2/5) | - (0/0) | 1/4 |
| osu-framework/osu.Framework/Input/Events/MouseMoveEvent.cs | 60.0% (3/5) | 100.0% (2/2) | 1/3 |
| osu-framework/osu.Framework/Input/Events/MouseUpEvent.cs | 0.0% (0/2) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/Events/ScrollEvent.cs | 0.0% (0/5) | - (0/0) | 0/2 |
| osu-framework/osu.Framework/Input/Events/TabletAuxiliaryButtonEvent.cs | 0.0% (0/4) | - (0/0) | 0/2 |
| osu-framework/osu.Framework/Input/Events/TabletAuxiliaryButtonPressEvent.cs | 0.0% (0/2) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/Events/TabletAuxiliaryButtonReleaseEvent.cs | 0.0% (0/2) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/Events/TabletEvent.cs | 0.0% (0/4) | - (0/0) | 0/3 |
| osu-framework/osu.Framework/Input/Events/TabletPenButtonEvent.cs | 0.0% (0/4) | - (0/0) | 0/2 |
| osu-framework/osu.Framework/Input/Events/TabletPenButtonPressEvent.cs | 0.0% (0/2) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/Events/TabletPenButtonReleaseEvent.cs | 0.0% (0/2) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/Events/TouchDownEvent.cs | 0.0% (0/2) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/Events/TouchEvent.cs | 0.0% (0/8) | 0.0% (0/2) | 0/5 |
| osu-framework/osu.Framework/Input/Events/TouchMoveEvent.cs | 0.0% (0/5) | - (0/0) | 0/3 |
| osu-framework/osu.Framework/Input/Events/TouchUpEvent.cs | 0.0% (0/2) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/Events/UIEvent.cs | 54.5% (6/11) | 50.0% (3/6) | 4/9 |
| osu-framework/osu.Framework/Input/FrameworkActionContainer.cs | 100.0% (16/16) | - (0/0) | 3/3 |
| osu-framework/osu.Framework/Input/Handlers/InputHandler.cs | 53.8% (14/26) | 33.3% (2/6) | 5/12 |
| osu-framework/osu.Framework/Input/Handlers/Joystick/JoystickHandler.cs | 0.0% (0/41) | 0.0% (0/8) | 0/11 |
| osu-framework/osu.Framework/Input/Handlers/Keyboard/KeyboardHandler.cs | 0.0% (0/27) | 0.0% (0/6) | 0/7 |
| osu-framework/osu.Framework/Input/Handlers/Midi/MidiHandler.cs | 0.0% (0/136) | 0.0% (0/62) | 0/13 |
| osu-framework/osu.Framework/Input/Handlers/Mouse/MouseHandler.cs | 0.0% (0/117) | 0.0% (0/48) | 0/18 |
| osu-framework/osu.Framework/Input/Handlers/Pen/PenHandler.cs | 0.0% (0/63) | 0.0% (0/14) | 0/17 |
| osu-framework/osu.Framework/Input/Handlers/Tablet/AbsoluteTabletMode.cs | 0.0% (0/4) | - (0/0) | 0/2 |
| osu-framework/osu.Framework/Input/Handlers/Tablet/OpenTabletDriverHandler.cs | 0.0% (0/143) | 0.0% (0/44) | 0/23 |
| osu-framework/osu.Framework/Input/Handlers/Tablet/TabletDriver.cs | 0.0% (0/42) | 0.0% (0/20) | 0/9 |
| osu-framework/osu.Framework/Input/Handlers/Tablet/TabletInfo.cs | 0.0% (0/6) | - (0/0) | 0/3 |
| osu-framework/osu.Framework/Input/Handlers/Touch/TouchHandler.cs | 0.0% (0/28) | 0.0% (0/6) | 0/6 |
| osu-framework/osu.Framework/Input/InputManager.cs | 41.9% (165/394) | 32.8% (82/250) | 29/73 |
| osu-framework/osu.Framework/Input/InputResampler.cs | 100.0% (29/29) | 88.9% (16/18) | 3/3 |
| osu-framework/osu.Framework/Input/JoystickAxis.cs | 0.0% (0/3) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/JoystickAxisEventManager.cs | 0.0% (0/10) | 0.0% (0/4) | 0/4 |
| osu-framework/osu.Framework/Input/JoystickButtonEventManager.cs | 0.0% (0/4) | - (0/0) | 0/3 |
| osu-framework/osu.Framework/Input/KeyEventManager.cs | 0.0% (0/8) | 0.0% (0/2) | 0/5 |
| osu-framework/osu.Framework/Input/MidiKeyEventManager.cs | 0.0% (0/4) | - (0/0) | 0/3 |
| osu-framework/osu.Framework/Input/MouseButtonEventManager.cs | 12.0% (10/83) | 7.6% (5/66) | 3/15 |
| osu-framework/osu.Framework/Input/PassThroughInputManager.cs | 52.5% (64/122) | 50.0% (75/150) | 14/14 |
| osu-framework/osu.Framework/Input/PlatformActionContainer.cs | 100.0% (5/5) | - (0/0) | 4/4 |
| osu-framework/osu.Framework/Input/ReadableKeyCombinationProvider.cs | 0.0% (0/135) | 0.0% (0/171) | 0/3 |
| osu-framework/osu.Framework/Input/SDLWindowTextInput.cs | 0.0% (0/25) | 0.0% (0/4) | 0/8 |
| osu-framework/osu.Framework/Input/StateChanges/ButtonInput.cs | 37.5% (9/24) | 31.2% (5/16) | 2/5 |
| osu-framework/osu.Framework/Input/StateChanges/ButtonInputEntry.cs | 0.0% (0/3) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/StateChanges/Events/ButtonStateChangeEvent.cs | 0.0% (0/4) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/StateChanges/Events/InputStateChangeEvent.cs | 100.0% (4/4) | 50.0% (1/2) | 1/1 |
| osu-framework/osu.Framework/Input/StateChanges/Events/JoystickAxisChangeEvent.cs | 0.0% (0/4) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/StateChanges/Events/MousePositionChangeEvent.cs | 100.0% (3/3) | - (0/0) | 1/1 |
| osu-framework/osu.Framework/Input/StateChanges/Events/MouseScrollChangeEvent.cs | 0.0% (0/4) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/StateChanges/Events/TouchStateChangeEvent.cs | 0.0% (0/5) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/StateChanges/JoystickAxisInput.cs | 0.0% (0/29) | 0.0% (0/22) | 0/5 |
| osu-framework/osu.Framework/Input/StateChanges/JoystickButtonInput.cs | 28.6% (2/7) | - (0/0) | 1/4 |
| osu-framework/osu.Framework/Input/StateChanges/KeyboardKeyInput.cs | 28.6% (2/7) | - (0/0) | 1/4 |
| osu-framework/osu.Framework/Input/StateChanges/MidiKeyInput.cs | 54.5% (6/11) | 50.0% (1/2) | 2/4 |
| osu-framework/osu.Framework/Input/StateChanges/MouseButtonInput.cs | 50.0% (5/10) | - (0/0) | 2/5 |
| osu-framework/osu.Framework/Input/StateChanges/MouseButtonInputFromPen.cs | 0.0% (0/3) | - (0/0) | 0/2 |
| osu-framework/osu.Framework/Input/StateChanges/MouseButtonInputFromTouch.cs | 0.0% (0/4) | - (0/0) | 0/2 |
| osu-framework/osu.Framework/Input/StateChanges/MousePositionAbsoluteInput.cs | 100.0% (8/8) | 100.0% (6/6) | 1/1 |
| osu-framework/osu.Framework/Input/StateChanges/MousePositionAbsoluteInputFromPen.cs | 0.0% (0/1) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/StateChanges/MousePositionAbsoluteInputFromTouch.cs | 0.0% (0/4) | - (0/0) | 0/2 |
| osu-framework/osu.Framework/Input/StateChanges/MousePositionRelativeInput.cs | 0.0% (0/7) | 0.0% (0/4) | 0/1 |
| osu-framework/osu.Framework/Input/StateChanges/MousePositionRelativeInputFromPen.cs | 0.0% (0/1) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/StateChanges/MouseScrollRelativeInput.cs | 0.0% (0/9) | 0.0% (0/8) | 0/1 |
| osu-framework/osu.Framework/Input/StateChanges/TabletAuxiliaryButtonInput.cs | 28.6% (2/7) | - (0/0) | 1/4 |
| osu-framework/osu.Framework/Input/StateChanges/TabletPenButtonInput.cs | 28.6% (2/7) | - (0/0) | 1/4 |
| osu-framework/osu.Framework/Input/StateChanges/TouchInput.cs | 66.7% (12/18) | 33.3% (4/12) | 2/3 |
| osu-framework/osu.Framework/Input/States/ButtonStates.cs | 29.7% (11/37) | 15.0% (3/20) | 7/13 |
| osu-framework/osu.Framework/Input/States/InputState.cs | 100.0% (10/10) | 50.0% (6/12) | 2/2 |
| osu-framework/osu.Framework/Input/States/JoystickState.cs | 57.1% (4/7) | 0.0% (0/2) | 1/2 |
| osu-framework/osu.Framework/Input/States/KeyboardState.cs | 20.0% (1/5) | 0.0% (0/8) | 1/5 |
| osu-framework/osu.Framework/Input/States/MidiState.cs | 100.0% (2/2) | - (0/0) | 1/1 |
| osu-framework/osu.Framework/Input/States/MouseState.cs | 55.6% (5/9) | 0.0% (0/2) | 5/8 |
| osu-framework/osu.Framework/Input/States/TabletState.cs | 15.4% (2/13) | - (0/0) | 1/8 |
| osu-framework/osu.Framework/Input/States/TouchState.cs | 55.0% (11/20) | 30.0% (3/10) | 5/5 |
| osu-framework/osu.Framework/Input/TabletAuxiliaryButtonEventManager.cs | 0.0% (0/4) | - (0/0) | 0/3 |
| osu-framework/osu.Framework/Input/TabletPenButtonEventManager.cs | 0.0% (0/4) | - (0/0) | 0/3 |
| osu-framework/osu.Framework/Input/TextInputProperties.cs | 0.0% (0/1) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Input/TextInputSource.cs | 0.0% (0/28) | 0.0% (0/14) | 0/12 |
| osu-framework/osu.Framework/Input/TextInputType.cs | 0.0% (0/5) | 0.0% (0/8) | 0/3 |
| osu-framework/osu.Framework/Input/Touch.cs | 37.5% (3/8) | 0.0% (0/2) | 1/6 |
| osu-framework/osu.Framework/Input/TouchEventManager.cs | 0.0% (0/15) | - (0/0) | 0/7 |
| osu-framework/osu.Framework/Input/UserInputManager.cs | 15.4% (6/39) | 2.9% (1/34) | 3/6 |

</details>

<details><summary>framework: transforms (9 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| osu-framework/osu.Framework/Graphics/Transforms/CubicBezierEasingFunction.cs | 0.0% (0/24) | 0.0% (0/14) | 0/6 |
| osu-framework/osu.Framework/Graphics/Transforms/DefaultEasingFunction.cs | 44.8% (30/67) | 37.9% (25/66) | 3/3 |
| osu-framework/osu.Framework/Graphics/Transforms/Spring.cs | 0.0% (0/48) | 0.0% (0/8) | 0/21 |
| osu-framework/osu.Framework/Graphics/Transforms/TargetGroupingTransformTracker.cs | 88.6% (124/140) | 82.4% (89/108) | 12/12 |
| osu-framework/osu.Framework/Graphics/Transforms/Transform.cs | 88.9% (24/27) | 75.0% (6/8) | 17/20 |
| osu-framework/osu.Framework/Graphics/Transforms/TransformBindable.cs | 100.0% (10/10) | 100.0% (4/4) | 5/5 |
| osu-framework/osu.Framework/Graphics/Transforms/TransformCustom.cs | 76.0% (57/75) | 58.3% (21/36) | 13/14 |
| osu-framework/osu.Framework/Graphics/Transforms/TransformSequence.cs | 43.7% (62/142) | 48.3% (28/58) | 15/27 |
| osu-framework/osu.Framework/Graphics/Transforms/Transformable.cs | 92.1% (116/126) | 86.2% (69/80) | 25/25 |

</details>

<details><summary>framework: lifetime/containers (11 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| osu-framework/osu.Framework/Graphics/Containers/CompositeDrawable.DrawNode.cs | 34.2% (41/120) | 11.7% (7/60) | 8/16 |
| osu-framework/osu.Framework/Graphics/Containers/CompositeDrawable.cs | 79.9% (570/713) | 70.4% (324/460) | 110/127 |
| osu-framework/osu.Framework/Graphics/Containers/Container.cs | 64.2% (88/137) | 59.3% (32/54) | 38/63 |
| osu-framework/osu.Framework/Graphics/Containers/ContainerExtensions.cs | 8.2% (4/49) | 0.0% (0/36) | 2/4 |
| osu-framework/osu.Framework/Graphics/Containers/LifetimeManagementContainer.cs | 61.0% (36/59) | 16.7% (2/12) | 11/15 |
| osu-framework/osu.Framework/Graphics/Performance/FrameStatisticsDisplay.cs | 0.0% (0/332) | 0.0% (0/90) | 0/30 |
| osu-framework/osu.Framework/Graphics/Performance/FrameTimeDisplay.cs | 0.0% (0/52) | 0.0% (0/22) | 0/4 |
| osu-framework/osu.Framework/Graphics/Performance/GlobalStatisticsDisplay.cs | 0.0% (0/122) | 0.0% (0/22) | 0/16 |
| osu-framework/osu.Framework/Graphics/Performance/LifetimeEntry.cs | 100.0% (19/19) | 100.0% (8/8) | 10/10 |
| osu-framework/osu.Framework/Graphics/Performance/LifetimeEntryManager.cs | 69.4% (86/124) | 60.9% (53/87) | 11/13 |
| osu-framework/osu.Framework/Graphics/Performance/PerformanceOverlay.cs | 22.0% (24/109) | 13.6% (6/44) | 7/17 |

</details>

<details><summary>framework: Drawable (1 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| osu-framework/osu.Framework/Graphics/Drawable.cs | 81.0% (613/757) | 70.9% (368/519) | 161/202 |

</details>

<details><summary>framework: bindables (25 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| osu-framework/osu.Framework/Bindables/AggregateBindable.cs | 95.5% (42/44) | 85.0% (17/20) | 8/8 |
| osu-framework/osu.Framework/Bindables/Bindable.cs | 71.5% (123/172) | 61.7% (74/120) | 43/51 |
| osu-framework/osu.Framework/Bindables/BindableBool.cs | 72.7% (8/11) | 50.0% (4/8) | 3/4 |
| osu-framework/osu.Framework/Bindables/BindableColour4.cs | 0.0% (0/11) | 0.0% (0/4) | 0/4 |
| osu-framework/osu.Framework/Bindables/BindableDictionary.cs | 11.5% (21/182) | 3.2% (3/94) | 9/70 |
| osu-framework/osu.Framework/Bindables/BindableDouble.cs | 100.0% (4/4) | 50.0% (1/2) | 3/3 |
| osu-framework/osu.Framework/Bindables/BindableFloat.cs | 100.0% (4/4) | 50.0% (1/2) | 3/3 |
| osu-framework/osu.Framework/Bindables/BindableInt.cs | 66.7% (2/3) | - (0/0) | 1/2 |
| osu-framework/osu.Framework/Bindables/BindableList.cs | 43.2% (101/234) | 32.5% (52/160) | 33/71 |
| osu-framework/osu.Framework/Bindables/BindableLong.cs | 66.7% (2/3) | - (0/0) | 1/2 |
| osu-framework/osu.Framework/Bindables/BindableMarginPadding.cs | 0.0% (0/30) | 0.0% (0/10) | 0/7 |
| osu-framework/osu.Framework/Bindables/BindableNumber.cs | 78.9% (60/76) | 78.9% (30/38) | 20/25 |
| osu-framework/osu.Framework/Bindables/BindableNumberWithCurrent.cs | 0.0% (0/8) | 0.0% (0/2) | 0/4 |
| osu-framework/osu.Framework/Bindables/BindableSafeArea.cs | 100.0% (3/3) | - (0/0) | 2/2 |
| osu-framework/osu.Framework/Bindables/BindableSize.cs | 50.0% (10/20) | 0.0% (0/6) | 5/8 |
| osu-framework/osu.Framework/Bindables/BindableWithCurrent.cs | 25.0% (2/8) | 0.0% (0/2) | 1/4 |
| osu-framework/osu.Framework/Bindables/IBindable.cs | 50.0% (4/8) | 50.0% (1/2) | 1/3 |
| osu-framework/osu.Framework/Bindables/IBindableDictionary.cs | 0.0% (0/1) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Bindables/IBindableList.cs | 0.0% (0/1) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Bindables/IBindableWithCurrent.cs | 0.0% (0/3) | 0.0% (0/2) | 0/1 |
| osu-framework/osu.Framework/Bindables/LeasedBindable.cs | 0.0% (0/47) | 0.0% (0/30) | 0/12 |
| osu-framework/osu.Framework/Bindables/NonNullableBindable.cs | 91.7% (11/12) | 50.0% (1/2) | 5/5 |
| osu-framework/osu.Framework/Bindables/NotifyDictionaryChangedEventArgs.cs | 0.0% (0/14) | 0.0% (0/4) | 0/3 |
| osu-framework/osu.Framework/Bindables/RangeConstrainedBindable.cs | 65.6% (63/96) | 56.1% (37/66) | 18/21 |
| osu-framework/osu.Framework/Bindables/ValueChangedEvent.cs | 100.0% (3/3) | - (0/0) | 1/1 |

</details>

<details><summary>framework: utils/math (24 files)</summary>

| file | lines | branches | methods hit |
|---|---|---|---|
| osu-framework/osu.Framework/Graphics/Primitives/Line.cs | 38.5% (15/39) | 66.7% (4/6) | 3/16 |
| osu-framework/osu.Framework/Graphics/Primitives/ProjectionRange.cs | 0.0% (0/16) | 0.0% (0/10) | 0/4 |
| osu-framework/osu.Framework/Graphics/Primitives/Quad.cs | 38.2% (29/76) | 0.0% (0/48) | 10/20 |
| osu-framework/osu.Framework/Graphics/Primitives/RectangleF.cs | 62.5% (65/104) | 31.0% (13/42) | 34/54 |
| osu-framework/osu.Framework/Graphics/Primitives/RectangleI.cs | 22.4% (15/67) | 20.8% (10/48) | 6/38 |
| osu-framework/osu.Framework/Graphics/Primitives/SimpleConvexPolygon.cs | 0.0% (0/7) | - (0/0) | 0/5 |
| osu-framework/osu.Framework/Graphics/Primitives/Triangle.cs | 0.0% (0/29) | 0.0% (0/12) | 0/8 |
| osu-framework/osu.Framework/Graphics/Primitives/Vector2I.cs | 41.2% (7/17) | 0.0% (0/4) | 4/12 |
| osu-framework/osu.Framework/Utils/Blur.cs | 77.8% (7/9) | 66.7% (4/6) | 2/2 |
| osu-framework/osu.Framework/Utils/CircularArcProperties.cs | 64.3% (27/42) | 83.3% (5/6) | 1/3 |
| osu-framework/osu.Framework/Utils/ConvexPolygonClipper.cs | 0.0% (0/55) | 0.0% (0/30) | 0/8 |
| osu-framework/osu.Framework/Utils/General.cs | 21.4% (3/14) | 0.0% (0/6) | 1/1 |
| osu-framework/osu.Framework/Utils/HasOrderedElementsAttribute.cs | 0.0% (0/1) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Utils/IncrementalBSplineBuilder.cs | 0.0% (0/222) | 0.0% (0/106) | 0/23 |
| osu-framework/osu.Framework/Utils/Interpolation.cs | 37.0% (71/192) | 42.0% (42/100) | 13/50 |
| osu-framework/osu.Framework/Utils/MathUtils.cs | 0.0% (0/1) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Utils/NumberFormatter.cs | 0.0% (0/10) | 0.0% (0/8) | 0/2 |
| osu-framework/osu.Framework/Utils/OrderAttribute.cs | 100.0% (3/3) | - (0/0) | 1/1 |
| osu-framework/osu.Framework/Utils/PathApproximator.cs | 25.9% (84/324) | 20.5% (39/190) | 9/29 |
| osu-framework/osu.Framework/Utils/Precision.cs | 90.9% (10/11) | 100.0% (8/8) | 7/8 |
| osu-framework/osu.Framework/Utils/RNG.cs | 31.6% (6/19) | - (0/0) | 5/13 |
| osu-framework/osu.Framework/Utils/SourceGeneratorUtils.cs | 72.2% (13/18) | 63.6% (14/22) | 3/3 |
| osu-framework/osu.Framework/Utils/ThrowHelper.cs | 0.0% (0/1) | - (0/0) | 0/1 |
| osu-framework/osu.Framework/Utils/Validation.cs | 85.7% (12/14) | 78.6% (22/28) | 3/4 |

</details>

### Per method (judgement core files only; methods not fully covered, never-entered last)

<details><summary>osu ruleset: DHOs: 54 methods not fully covered (17 never entered)</summary>

| file:line | method | lines | branches |
|---|---|---|---|
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableHitCircle.cs:60 | `load(osu.Game.Rulesets.Osu.Configuration.OsuRulesetConfigManager)` | 44/45 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableHitCircle.cs:141 | `CheckForResult(System.Boolean,System.Double)` | 24/24 | 11/12 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableHitCircle.cs:214 | `UpdateHitStateTransforms(osu.Game.Rulesets.Objects.Drawables.ArmedState)` | 8/10 | 5/6 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableOsuHitObject.cs:157 | `ApplyRepeatFadeIn(osu.Framework.Graphics.Drawable,System.Double)` | 10/10 | 6/8 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSlider.cs:98 | `load()` | 38/39 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSlider.cs:156 | `OnFree()` | 4/4 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSlider.cs:173 | `StopAllSamples()` | 3/3 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSlider.cs:239 | `Update()` | 10/10 | 10/12 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSlider.cs:259 | `UpdateAfterChildren()` | 15/15 | 13/18 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSlider.cs:289 | `OnKilled()` | 3/3 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSlider.cs:295 | `CheckForResult(System.Boolean,System.Double)` | 23/23 | 15/16 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSlider.cs:353 | `UpdateHitStateTransforms(osu.Game.Rulesets.Objects.Drawables.ArmedState)` | 5/5 | 6/8 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSlider.cs:368 | `ReceivePositionalInputAt(osuTK.Vector2)` | 1/1 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderBall.cs:27 | `load(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject)` | 16/18 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderRepeat.cs:26 | `get_Slider()` | 1/1 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderRepeat.cs:49 | `load()` | 23/24 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderRepeat.cs:96 | `UpdateHitStateTransforms(osu.Game.Rulesets.Objects.Drawables.ArmedState)` | 8/8 | 3/4 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderRepeat.cs:121 | `UpdateSnakingPosition(osuTK.Vector2,osuTK.Vector2)` | 20/21 | 23/24 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderTail.cs:23 | `get_Slider()` | 1/1 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderTail.cs:52 | `load(osu.Game.Rulesets.Osu.Configuration.OsuRulesetConfigManager)` | 19/19 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderTail.cs:96 | `UpdateHitStateTransforms(osu.Game.Rulesets.Objects.Drawables.ArmedState)` | 8/9 | 4/6 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderTail.cs:127 | `OnApply()` | 4/4 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderTick.cs:82 | `UpdateHitStateTransforms(osu.Game.Rulesets.Objects.Drawables.ArmedState)` | 8/8 | 3/4 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSpinner.cs:88 | `load()` | 36/37 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSpinner.cs:171 | `StopAllSamples()` | 4/4 | 2/4 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSpinner.cs:178 | `AddNestedHitObject(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject)` | 3/3 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSpinner.cs:227 | `ApplySkin(osu.Game.Skinning.ISkinSource,System.Boolean)` | 3/3 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSpinner.cs:253 | `CheckForResult(System.Boolean,System.Double)` | 20/20 | 18/20 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSpinner.cs:281 | `Update()` | 14/14 | 16/18 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSpinner.cs:311 | `correctButtonPressed()` | 6/7 | 7/8 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSpinner.cs:342 | `updateBonusScore()` | 12/13 | 7/8 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSpinner.cs:378 | `MoveNext()` | 2/5 | 1/4 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/SliderInputManager.cs:80 | `PostProcessHeadJudgement(osu.Game.Rulesets.Osu.Objects.Drawables.DrawableSliderHead)` | 22/25 | 21/24 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/SliderInputManager.cs:148 | `TryJudgeNestedObject(osu.Game.Rulesets.Osu.Objects.Drawables.DrawableOsuHitObject,System.Double)` | 14/14 | 21/22 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/SliderInputManager.cs:218 | `updateTracking(System.Boolean)` | 27/33 | 21/28 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/SliderInputManager.cs:276 | `getInitialHitAction()` | 1/1 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/SpinnerSpinHistory.cs:66 | `ReportDelta(System.Double,System.Single)` | 12/17 | 5/10 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableHitCircle.cs:40 | `osu.Game.Rulesets.Osu.Skinning.IHasApproachCircle.get_ApproachCircle()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableHitCircle.cs:338 | `SuppressHitAnimations()` | 0/7 | 0/2 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableHitCircle.cs:355 | `RestoreHitAnimations()` | 0/3 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableOsuHitObject.cs:132 | `Shake()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSlider.cs:220 | `CreateNestedHitObject(osu.Game.Rulesets.Objects.HitObject)` | 0/5 | 0/8 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSlider.cs:378 | `SuppressHitAnimations()` | 0/11 | 0/6 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSlider.cs:402 | `RestoreHitAnimations()` | 0/6 | 0/2 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderHead.cs:28 | `.ctor(osu.Game.Rulesets.Osu.Objects.SliderHeadCircle)` | 0/2 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderRepeat.cs:42 | `.ctor(osu.Game.Rulesets.Osu.Objects.SliderRepeat)` | 0/2 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderRepeat.cs:167 | `SuppressHitAnimations()` | 0/9 | 0/2 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderRepeat.cs:187 | `RestoreHitAnimations()` | 0/4 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderTail.cs:43 | `.ctor(osu.Game.Rulesets.Osu.Objects.SliderTailCircle)` | 0/2 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderTail.cs:137 | `SuppressHitAnimations()` | 0/7 | 0/2 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderTail.cs:154 | `RestoreHitAnimations()` | 0/3 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSliderTick.cs:33 | `.ctor(osu.Game.Rulesets.Osu.Objects.SliderTick)` | 0/2 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSpinner.cs:216 | `CreateNestedHitObject(osu.Game.Rulesets.Objects.HitObject)` | 0/3 | 0/4 |
| lazer/osu.Game.Rulesets.Osu/Objects/Drawables/DrawableSpinnerBonusTick.cs:14 | `.ctor(osu.Game.Rulesets.Osu.Objects.SpinnerBonusTick)` | 0/2 | 0/0 |

</details>

<details><summary>osu ruleset: hit objects: 10 methods not fully covered (5 never entered)</summary>

| file:line | method | lines | branches |
|---|---|---|---|
| lazer/osu.Game.Rulesets.Osu/Objects/OsuHitObject.cs:189 | `UpdateComboInformation(osu.Game.Rulesets.Objects.Types.IHasComboInformation)` | 12/12 | 15/16 |
| lazer/osu.Game.Rulesets.Osu/Objects/Slider.cs:118 | `set_ClassicSliderBehaviour(System.Boolean)` | 4/4 | 2/4 |
| lazer/osu.Game.Rulesets.Osu/Objects/Slider.cs:158 | `ApplyDefaultsToSelf(osu.Game.Beatmaps.ControlPoints.ControlPointInfo,osu.Game.Beatmaps.IBeatmapDifficultyInfo)` | 6/6 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Objects/Slider.cs:258 | `UpdateNestedSamples()` | 11/11 | 12/14 |
| lazer/osu.Game.Rulesets.Osu/Objects/Spinner.cs:106 | `CreateSpinningSamples()` | 6/7 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Objects/OsuHitObject.cs:67 | `set_X(System.Single)` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Objects/OsuHitObject.cs:73 | `set_Y(System.Single)` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Objects/OsuHitObject.cs:110 | `get_ComboOffsetBindable()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Objects/OsuHitObject.cs:150 | `get_LastInComboBindable()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Objects/Slider.cs:34 | `set_Duration(System.Double)` | 0/1 | 0/0 |

</details>

<details><summary>osu ruleset: judgements/scoring: 5 methods not fully covered (2 never entered)</summary>

| file:line | method | lines | branches |
|---|---|---|---|
| lazer/osu.Game.Rulesets.Osu/Scoring/OsuHealthProcessor.cs:25 | `GetHealthIncreaseFor(osu.Game.Rulesets.Judgements.JudgementResult)` | 17/18 | 23/24 |
| lazer/osu.Game.Rulesets.Osu/Scoring/OsuHitWindows.cs:51 | `WindowFor(osu.Game.Rulesets.Scoring.HitResult)` | 4/5 | 4/6 |
| lazer/osu.Game.Rulesets.Osu/Scoring/OsuLegacyHealthProcessor.cs:42 | `GetHealthIncreaseFor(osu.Game.Rulesets.Objects.HitObject,osu.Game.Rulesets.Scoring.HitResult)` | 18/18 | 16/19 |
| lazer/osu.Game.Rulesets.Osu/Scoring/OsuScoreMultiplierCalculatorV1.cs:13 | `.ctor(osu.Game.Rulesets.Scoring.ScoreMultiplierContext)` | 0/23 | 0/8 |
| lazer/osu.Game.Rulesets.Osu/Scoring/OsuScoreMultiplierCalculatorV1.cs:90 | `rateAdjustMultiplier(System.Double)` | 0/5 | 0/2 |

</details>

<details><summary>osu ruleset: mods: 132 methods not fully covered (104 never entered)</summary>

| file:line | method | lines | branches |
|---|---|---|---|
| lazer/osu.Game.Rulesets.Osu/Mods/InputBlockingMod.cs:67 | `Update(osu.Game.Rulesets.UI.Playfield)` | 4/5 | 7/8 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModApproachDifferent.cs:57 | `getEasing(osu.Game.Rulesets.Osu.Mods.OsuModApproachDifferent/AnimationStyle)` | 7/11 | 7/11 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModBlinds.cs:141 | `Update()` | 14/18 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModBubbles.cs:83 | `ApplyToDrawableHitObject(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject)` | 30/34 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModDepth.cs:52 | `ApplyToDrawableRuleset(osu.Game.Rulesets.UI.DrawableRuleset`1<osu.Game.Rulesets.Osu.Objects.OsuHitObject>)` | 2/2 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModDifficultyAdjust.cs:23 | `.ctor()` | 13/15 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModFreezeFrame.cs:40 | `ApplyToBeatmap(osu.Game.Beatmaps.IBeatmap)` | 9/10 | 5/6 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModHidden.cs:65 | `applyHiddenState(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject,System.Boolean)` | 30/31 | 23/24 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModHidden.cs:190 | `hideSpinnerApproachCircle(osu.Game.Rulesets.Osu.Objects.Drawables.DrawableSpinner)` | 3/6 | 2/4 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModMagnetised.cs:44 | `ApplyToDrawableRuleset(osu.Game.Rulesets.UI.DrawableRuleset`1<osu.Game.Rulesets.Osu.Objects.OsuHitObject>)` | 2/2 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModMirror.cs:25 | `ApplyToHitObject(osu.Game.Rulesets.Objects.HitObject)` | 9/9 | 3/4 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModRandom.cs:44 | `ApplyToBeatmap(osu.Game.Beatmaps.IBeatmap)` | 28/29 | 14/16 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModRelax.cs:57 | `ApplyToPlayer(osu.Game.Screens.Play.Player)` | 5/8 | 3/4 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModRepel.cs:45 | `ApplyToDrawableRuleset(osu.Game.Rulesets.UI.DrawableRuleset`1<osu.Game.Rulesets.Osu.Objects.OsuHitObject>)` | 2/2 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModSpunOut.cs:37 | `onSpinnerUpdate(osu.Framework.Graphics.Drawable)` | 7/8 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModStrictTracking.cs:36 | `ApplyToDrawableHitObject(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject)` | 16/17 | 12/14 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModStrictTracking.cs:58 | `ApplyToBeatmap(osu.Game.Beatmaps.IBeatmap)` | 14/14 | 3/4 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModSynesthesia.cs:27 | `ApplyToBeatmap(osu.Game.Beatmaps.IBeatmap)` | 3/3 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModSynesthesia.cs:33 | `ApplyToDrawableHitObject(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject)` | 17/17 | 4/6 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTargetPractice.cs:109 | `ApplyToHealthProcessor(osu.Game.Rulesets.Scoring.HealthProcessor)` | 4/4 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTargetPractice.cs:134 | `ApplyNormalVisibilityState(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject,osu.Game.Rulesets.Objects.Dra` | 12/12 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTargetPractice.cs:162 | `ApplyToBeatmap(osu.Game.Beatmaps.IBeatmap)` | 20/20 | 3/4 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTargetPractice.cs:195 | `generateBeats(osu.Game.Beatmaps.IBeatmap,System.Collections.Generic.IReadOnlyCollection`1<osu.Game.Rulesets.Os` | 16/17 | 3/4 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTargetPractice.cs:237 | `fixComboInfo(System.Collections.Generic.List`1<osu.Game.Rulesets.Osu.Objects.OsuHitObject>,System.Collections.` | 18/18 | 5/6 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTargetPractice.cs:269 | `randomizeCirclePos(System.Collections.Generic.IReadOnlyList`1<osu.Game.Rulesets.Osu.Objects.OsuHitObject>,Syst` | 33/33 | 20/22 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTargetPractice.cs:354 | `isInsideBreakPeriod(System.Collections.Generic.IReadOnlyCollection`1<osu.Game.Rulesets.Osu.Objects.OsuHitObjec` | 9/9 | 3/4 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTargetPractice.cs:442 | `nodeIndexFromTime(osu.Game.Rulesets.Objects.Types.IHasRepeats,System.Double)` | 4/5 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTraceable.cs:40 | `applyTraceableState(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject,osu.Game.Rulesets.Objects.Drawables.` | 10/11 | 9/10 |
| lazer/osu.Game.Rulesets.Osu/Mods/InputBlockingMod.cs:25 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModAlternate.cs:14 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModAlternate.cs:16 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModAlternate.cs:17 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModAlternate.cs:19 | `get_Ranked()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModApproachDifferent.cs:19 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModApproachDifferent.cs:21 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModApproachDifferent.cs:22 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModAutopilot.cs:21 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModAutopilot.cs:23 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModAutopilot.cs:24 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModAutopilot.cs:25 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModAutoplay.cs:15 | `get_IncompatibleMods()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModAutoplay.cs:18 | `CreateReplayData(osu.Game.Beatmaps.IBeatmap,System.Collections.Generic.IReadOnlyList`1<osu.Game.Rulesets.Mods.` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModBlinds.cs:26 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModBlinds.cs:27 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModBlinds.cs:30 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModBlinds.cs:31 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModBlinds.cs:34 | `get_Ranked()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModBlinds.cs:48 | `AdjustRank(osu.Game.Scoring.ScoreRank,System.Double)` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModBloom.cs:24 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModBloom.cs:26 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModBloom.cs:27 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModBloom.cs:28 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModBloom.cs:90 | `.ctor()` | 0/3 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModBubbles.cs:31 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModBubbles.cs:35 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModBubbles.cs:37 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModBubbles.cs:39 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModCinema.cs:16 | `get_IncompatibleMods()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModCinema.cs:19 | `CreateReplayData(osu.Game.Beatmaps.IBeatmap,System.Collections.Generic.IReadOnlyList`1<osu.Game.Rulesets.Mods.` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModDeflate.cs:13 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModDeflate.cs:17 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModDeflate.cs:19 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModDepth.cs:23 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModDepth.cs:25 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModDepth.cs:26 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModDepth.cs:27 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModDifficultyAdjust.cs:46 | `get_ExtendedIconInformation()` | 0/7 | 0/10 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModDifficultyAdjust.cs:57 | `<get_ExtendedIconInformation>g__format\|7_0(System.String,osu.Game.Rulesets.Mods.DifficultyBindable)` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModDifficultyAdjust.cs:65 | `MoveNext()` | 0/7 | 0/6 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModDifficultyAdjust.cs:88 | `CreateSlider(osu.Framework.Bindables.BindableNumber`1<System.Single>)` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModDifficultyAdjust.cs:96 | `get_TooltipText()` | 0/3 | 0/4 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModDifficultyAdjust.cs:102 | `getPreemptTime(System.Single)` | 0/3 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModEasy.cs:12 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModFreezeFrame.cs:20 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModFreezeFrame.cs:24 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModFreezeFrame.cs:26 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModFreezeFrame.cs:33 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModGrow.cs:13 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModGrow.cs:17 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModGrow.cs:19 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModHidden.cs:26 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModMagnetised.cs:25 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModMagnetised.cs:27 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModMagnetised.cs:28 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModMagnetised.cs:29 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModMirror.cs:17 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModNoScope.cs:21 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModObjectScaleTween.cs:20 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModRandom.cs:26 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModRelax.cs:23 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModRelax.cs:175 | `HandlePress(System.Boolean)` | 0/3 | 0/2 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModRelax.cs:181 | `HandleRelease(System.Boolean)` | 0/2 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModRepel.cs:26 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModRepel.cs:28 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModRepel.cs:29 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModRepel.cs:30 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModSingleTap.cs:14 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModSingleTap.cs:16 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModSingleTap.cs:17 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModSingleTap.cs:19 | `get_Ranked()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModSpinIn.cs:19 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModSpinIn.cs:21 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModSpinIn.cs:22 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModSpinIn.cs:23 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModSpunOut.cs:18 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModSpunOut.cs:20 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModSpunOut.cs:21 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModSpunOut.cs:22 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModSpunOut.cs:24 | `get_Ranked()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModStrictTracking.cs:27 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModStrictTracking.cs:29 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModStrictTracking.cs:30 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModStrictTracking.cs:31 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTargetPractice.cs:37 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTargetPractice.cs:39 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTargetPractice.cs:40 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTargetPractice.cs:41 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTargetPractice.cs:104 | `get_RestartOnFail()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTouchDevice.cs:13 | `get_Ranked()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTraceable.cs:21 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTraceable.cs:23 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTraceable.cs:24 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTraceable.cs:25 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTraceable.cs:26 | `get_Ranked()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTransform.cs:20 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTransform.cs:22 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTransform.cs:23 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModTransform.cs:24 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModWiggle.cs:21 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModWiggle.cs:23 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModWiggle.cs:24 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Mods/OsuModWiggle.cs:25 | `get_Description()` | 0/1 | 0/0 |

</details>

<details><summary>osu ruleset: UI (playfield, hit policies, cursor): 14 methods not fully covered (6 never entered)</summary>

| file:line | method | lines | branches |
|---|---|---|---|
| lazer/osu.Game.Rulesets.Osu/UI/DrawableOsuRuleset.cs:45 | `load(osu.Game.Screens.Play.ReplayPlayer)` | 2/7 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/UI/DrawableOsuRuleset.cs:86 | `get_GameplayStartTime()` | 2/3 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/UI/LegacyHitPolicy.cs:38 | `CheckHittable(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject,System.Double,osu.Game.Rulesets.Scoring.Hi` | 17/18 | 19/20 |
| lazer/osu.Game.Rulesets.Osu/UI/OsuPlayfield.cs:101 | `set_HitPolicy(osu.Game.Rulesets.Osu.UI.IHitPolicy)` | 3/3 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/UI/OsuPlayfield.cs:137 | `load(osu.Game.Rulesets.Osu.Configuration.OsuRulesetConfigManager,osu.Game.Beatmaps.IBeatmap)` | 20/20 | 6/8 |
| lazer/osu.Game.Rulesets.Osu/UI/StartTimeOrderedHitPolicy.cs:28 | `CheckHittable(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject,System.Double,osu.Game.Rulesets.Scoring.Hi` | 11/12 | 13/14 |
| lazer/osu.Game.Rulesets.Osu/UI/StartTimeOrderedHitPolicy.cs:59 | `HandleHit(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject)` | 9/11 | 10/12 |
| lazer/osu.Game.Rulesets.Osu/UI/StartTimeOrderedHitPolicy.cs:89 | `MoveNext()` | 8/9 | 7/8 |
| lazer/osu.Game.Rulesets.Osu/UI/DrawableOsuRuleset.cs:35 | `get_Config()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/UI/DrawableOsuRuleset.cs:80 | `CreateReplayRecorder(osu.Game.Scoring.Score)` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/UI/OsuPlayfield.cs:51 | `get_SkinnableComponentScreenSpaceDrawQuad()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/UI/OsuPlayfield.cs:97 | `get_HitPolicy()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/UI/OsuPlayfield.cs:185 | `OnHitObjectRemoved(osu.Game.Rulesets.Objects.HitObject)` | 0/3 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/UI/OsuPlayfield.cs:209 | `ReceivePositionalInputAt(osuTK.Vector2)` | 0/1 | 0/0 |

</details>

<details><summary>osu ruleset: replays/input: 9 methods not fully covered (7 never entered)</summary>

| file:line | method | lines | branches |
|---|---|---|---|
| lazer/osu.Game.Rulesets.Osu/OsuInputManager.cs:67 | `Handle(osu.Framework.Input.Events.UIEvent)` | 2/2 | 3/6 |
| lazer/osu.Game.Rulesets.Osu/OsuInputManager.cs:100 | `ReloadMappings(System.Linq.IQueryable`1<osu.Game.Input.Bindings.RealmKeyBinding>)` | 3/4 | 1/2 |
| lazer/osu.Game.Rulesets.Osu/OsuInputManager.cs:34 | `get_AllowGameplayInputs()` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/OsuInputManager.cs:35 | `set_AllowGameplayInputs(System.Boolean)` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/OsuInputManager.cs:52 | `CheckScreenSpaceActionPressJudgeable(osuTK.Vector2)` | 0/1 | 0/2 |
| lazer/osu.Game.Rulesets.Osu/OsuInputManager.cs:88 | `set_AllowGameplayInputs(System.Boolean)` | 0/3 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Replays/OsuFramedReplayInputHandler.cs:20 | `IsImportant(osu.Game.Rulesets.Osu.Replays.OsuReplayFrame)` | 0/1 | 0/0 |
| lazer/osu.Game.Rulesets.Osu/Replays/OsuReplayFrame.cs:40 | `ToLegacy(osu.Game.Beatmaps.IBeatmap)` | 0/8 | 0/6 |
| lazer/osu.Game.Rulesets.Osu/Replays/OsuReplayFrame.cs:53 | `IsEquivalentTo(osu.Game.Rulesets.Replays.ReplayFrame)` | 0/1 | 0/6 |

</details>

<details><summary>osu.Game: scoring: 41 methods not fully covered (22 never entered)</summary>

| file:line | method | lines | branches |
|---|---|---|---|
| lazer/osu.Game/Rulesets/Scoring/DrainingHealthProcessor.cs:87 | `Update()` | 8/8 | 4/6 |
| lazer/osu.Game/Rulesets/Scoring/DrainingHealthProcessor.cs:102 | `ApplyBeatmap(osu.Game.Beatmaps.IBeatmap)` | 22/22 | 1/2 |
| lazer/osu.Game/Rulesets/Scoring/DrainingHealthProcessor.cs:165 | `ComputeDrainRate()` | 21/22 | 15/16 |
| lazer/osu.Game/Rulesets/Scoring/HealthProcessor.cs:39 | `TriggerFailure()` | 5/5 | 5/6 |
| lazer/osu.Game/Rulesets/Scoring/HitResult.cs:198 | `AffectsCombo(osu.Game.Rulesets.Scoring.HitResult)` | 2/2 | 15/19 |
| lazer/osu.Game/Rulesets/Scoring/HitResult.cs:214 | `AffectsAccuracy(osu.Game.Rulesets.Scoring.HitResult)` | 2/3 | 5/6 |
| lazer/osu.Game/Rulesets/Scoring/HitResult.cs:234 | `IsBasic(osu.Game.Rulesets.Scoring.HitResult)` | 1/3 | 6/8 |
| lazer/osu.Game/Rulesets/Scoring/HitResult.cs:295 | `IsMiss(osu.Game.Rulesets.Scoring.HitResult)` | 2/2 | 6/12 |
| lazer/osu.Game/Rulesets/Scoring/HitResult.cs:334 | `IsScorable(osu.Game.Rulesets.Scoring.HitResult)` | 2/4 | 5/8 |
| lazer/osu.Game/Rulesets/Scoring/HitResult.cs:363 | `IsValidHitResult(osu.Game.Rulesets.Scoring.HitResult,osu.Game.Rulesets.Scoring.HitResult,osu.Game.Rulesets.Sco` | 4/5 | 6/8 |
| lazer/osu.Game/Rulesets/Scoring/HitResult.cs:382 | `ValidateHitResultPair(osu.Game.Rulesets.Scoring.HitResult,osu.Game.Rulesets.Scoring.HitResult)` | 11/19 | 25/38 |
| lazer/osu.Game/Rulesets/Scoring/HitWindows.cs:43 | `LowestSuccessfulHitResult()` | 3/4 | 2/4 |
| lazer/osu.Game/Rulesets/Scoring/JudgementProcessor.cs:71 | `ApplyResult(osu.Game.Rulesets.Judgements.JudgementResult)` | 5/7 | 2/4 |
| lazer/osu.Game/Rulesets/Scoring/JudgementProcessor.cs:148 | `SimulateAutoplay(osu.Game.Beatmaps.IBeatmap)` | 9/10 | 3/4 |
| lazer/osu.Game/Rulesets/Scoring/JudgementProcessor.cs:204 | `Update()` | 7/7 | 3/4 |
| lazer/osu.Game/Rulesets/Scoring/LegacyDrainingHealthProcessor.cs:48 | `ComputeDrainRate()` | 47/53 | 35/44 |
| lazer/osu.Game/Rulesets/Scoring/ScoreProcessor.cs:241 | `ApplyResultInternal(osu.Game.Rulesets.Judgements.JudgementResult)` | 28/28 | 19/20 |
| lazer/osu.Game/Rulesets/Scoring/ScoreProcessor.cs:351 | `GetBaseScoreForResult(osu.Game.Rulesets.Scoring.HitResult)` | 9/10 | 12/16 |
| lazer/osu.Game/Rulesets/Scoring/ScoreProcessor.cs:506 | `FailScore(osu.Game.Scoring.ScoreInfo)` | 5/6 | 1/2 |
| lazer/osu.Game/Rulesets/Scoring/HealthProcessor.cs:62 | `RevertResultInternal(osu.Game.Rulesets.Judgements.JudgementResult)` | 0/5 | 0/2 |
| lazer/osu.Game/Rulesets/Scoring/HitResult.cs:378 | `GetIndexForOrderedDisplay(osu.Game.Rulesets.Scoring.HitResult)` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Scoring/HitWindows.cs:31 | `ensureValidHitWindows()` | 0/2 | 0/0 |
| lazer/osu.Game/Rulesets/Scoring/HitWindows.cs:57 | `MoveNext()` | 0/4 | 0/4 |
| lazer/osu.Game/Rulesets/Scoring/HitWindows.cs:69 | `IsHitResultAllowed(osu.Game.Rulesets.Scoring.HitResult)` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Scoring/HitWindows.cs:113 | `IsHitResultAllowed(osu.Game.Rulesets.Scoring.HitResult)` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Scoring/JudgementProcessor.cs:89 | `RevertResult(osu.Game.Rulesets.Judgements.JudgementResult)` | 0/4 | 0/2 |
| lazer/osu.Game/Rulesets/Scoring/JudgementProcessor.cs:132 | `ResetFromReplayFrame(osu.Game.Rulesets.Replays.ReplayFrame)` | 0/6 | 0/4 |
| lazer/osu.Game/Rulesets/Scoring/ScoreProcessor.cs:115 | `get_HitEvents()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Scoring/ScoreProcessor.cs:187 | `get_MaximumStatistics()` | 0/3 | 0/2 |
| lazer/osu.Game/Rulesets/Scoring/ScoreProcessor.cs:194 | `get_Statistics()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Scoring/ScoreProcessor.cs:297 | `RevertResultInternal(osu.Game.Rulesets.Judgements.JudgementResult)` | 0/21 | 0/14 |
| lazer/osu.Game/Rulesets/Scoring/ScoreProcessor.cs:389 | `RemoveScoreChange(osu.Game.Rulesets.Judgements.JudgementResult)` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Scoring/ScoreProcessor.cs:517 | `ResetFromReplayFrame(osu.Game.Rulesets.Replays.ReplayFrame)` | 0/12 | 0/4 |
| lazer/osu.Game/Rulesets/Scoring/ScoreProcessor.cs:536 | `GetScoreProcessorStatistics()` | 0/8 | 0/0 |
| lazer/osu.Game/Rulesets/Scoring/ScoreProcessor.cs:547 | `SetScoreProcessorStatistics(osu.Game.Rulesets.Scoring.ScoreProcessorStatistics)` | 0/6 | 0/0 |
| lazer/osu.Game/Rulesets/Scoring/ScoreProcessor.cs:585 | `AccuracyCutoffFromRank(osu.Game.Scoring.ScoreRank)` | 0/7 | 0/9 |
| lazer/osu.Game/Rulesets/Scoring/ScoreProcessor.cs:638 | `get_BaseScore()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Scoring/ScoreProcessor.cs:647 | `get_MaximumBaseScore()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Scoring/ScoreProcessor.cs:653 | `get_AccuracyJudgementCount()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Scoring/ScoreProcessor.cs:659 | `get_ComboPortion()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Scoring/ScoreProcessor.cs:665 | `get_BonusPortion()` | 0/1 | 0/0 |

</details>

<details><summary>osu.Game: judgements: 6 methods not fully covered (5 never entered)</summary>

| file:line | method | lines | branches |
|---|---|---|---|
| lazer/osu.Game/Rulesets/Judgements/Judgement.cs:102 | `HealthIncreaseFor(osu.Game.Rulesets.Scoring.HitResult)` | 1/13 | 3/17 |
| lazer/osu.Game/Rulesets/Judgements/Judgement.cs:23 | `get_MaxResult()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Judgements/Judgement.cs:90 | `get_MaxHealthIncrease()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Judgements/Judgement.cs:150 | `ToString()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Judgements/JudgementResult.cs:46 | `set_TimeOffset(System.Double)` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Judgements/JudgementResult.cs:125 | `ToString()` | 0/1 | 0/0 |

</details>

<details><summary>osu.Game: DrawableHitObject / pooling: 41 methods not fully covered (16 never entered)</summary>

| file:line | method | lines | branches |
|---|---|---|---|
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:60 | `.ctor(osu.Game.Rulesets.Objects.HitObject)` | 11/14 | 1/2 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:106 | `get_Result()` | 1/1 | 1/2 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:112 | `get_IsHit()` | 1/1 | 1/2 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:123 | `get_AllJudged()` | 1/1 | 1/2 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:227 | `LoadComplete()` | 10/11 | 0/0 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:261 | `OnApply(osu.Game.Rulesets.Objects.HitObjectLifetimeEntry)` | 28/31 | 13/22 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:324 | `updateStateFromResult()` | 5/6 | 3/4 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:336 | `OnFree(osu.Game.Rulesets.Objects.HitObjectLifetimeEntry)` | 20/20 | 4/6 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:404 | `onNewResult(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject,osu.Game.Rulesets.Judgements.JudgementResult` | 1/1 | 1/2 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:469 | `UpdateState(osu.Game.Rulesets.Objects.Drawables.ArmedState,System.Boolean)` | 19/19 | 17/18 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:566 | `skinChanged()` | 4/5 | 1/2 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:576 | `UpdateComboColour()` | 6/6 | 3/4 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:618 | `PlaySamples()` | 5/5 | 2/4 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:632 | `StopAllSamples()` | 2/3 | 2/4 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:693 | `get_HitStateUpdateTime()` | 1/1 | 1/2 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:728 | `ApplyResult(System.Action`2<osu.Game.Rulesets.Judgements.JudgementResult,T>,T)` | 11/15 | 9/16 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:761 | `UpdateResult(System.Boolean)` | 5/6 | 4/6 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:794 | `ensureEntryHasResult()` | 3/3 | 2/4 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:800 | `Dispose(System.Boolean)` | 10/11 | 2/4 |
| lazer/osu.Game/Rulesets/Objects/HitObject.cs:107 | `ApplyDefaults(osu.Game.Beatmaps.ControlPoints.ControlPointInfo,osu.Game.Beatmaps.IBeatmapDifficultyInfo,System` | 17/18 | 9/10 |
| lazer/osu.Game/Rulesets/Objects/HitObject.cs:149 | `<ApplyDefaults>g__onStartTimeChanged\|25_1(osu.Framework.Bindables.ValueChangedEvent`1<System.Double>)` | 3/4 | 1/2 |
| lazer/osu.Game/Rulesets/Objects/HitObject.cs:158 | `ApplyDefaultsToSelf(osu.Game.Beatmaps.ControlPoints.ControlPointInfo,osu.Game.Beatmaps.IBeatmapDifficultyInfo)` | 4/4 | 3/4 |
| lazer/osu.Game/Rulesets/Objects/HitObject.cs:203 | `get_MaximumJudgementOffset()` | 1/1 | 1/2 |
| lazer/osu.Game/Rulesets/Objects/HitObject.cs:207 | `CreateSlidingSamples()` | 8/8 | 3/4 |
| lazer/osu.Game/Rulesets/Objects/HitObject.cs:232 | `CreateHitSampleInfo(System.String)` | 5/6 | 5/6 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:132 | `get_SamplePlaybackPosition()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:250 | `Apply(osu.Game.Rulesets.Objects.HitObject)` | 0/3 | 0/0 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:408 | `onRevertResult()` | 0/3 | 0/2 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:412 | `onNestedRevertResult(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject,osu.Game.Rulesets.Judgements.Judgem` | 0/1 | 0/2 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:419 | `onDefaultsApplied(osu.Game.Rulesets.Objects.HitObject)` | 0/6 | 0/4 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:453 | `CreateNestedHitObject(osu.Game.Rulesets.Objects.HitObject)` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:464 | `ClearInternal(System.Boolean)` | 0/2 | 0/0 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:512 | `RefreshStateTransforms()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:562 | `skinSourceChanged()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:665 | `UpdateSubTreeMasking()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:681 | `get_InitialLifetimeOffset()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:713 | `ApplyResult(osu.Game.Rulesets.Scoring.HitResult)` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Objects/Drawables/DrawableHitObject.cs:789 | `CreateResult(osu.Game.Rulesets.Judgements.Judgement)` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Objects/HitObject.cs:185 | `CreateJudgement()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Objects/HitObject.cs:195 | `CreateHitWindows()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Objects/HitObject.cs:245 | `ToString()` | 0/1 | 0/0 |

</details>

<details><summary>osu.Game: Rulesets.UI (DrawableRuleset, FSC, playfield, HOC): 60 methods not fully covered (36 never entered)</summary>

| file:line | method | lines | branches |
|---|---|---|---|
| lazer/osu.Game/Rulesets/UI/FrameStabilityContainer.cs:97 | `load(osu.Game.Screens.Play.IGameplayClock)` | 6/6 | 2/4 |
| lazer/osu.Game/Rulesets/UI/FrameStabilityContainer.cs:109 | `UpdateSubTree()` | 7/7 | 5/6 |
| lazer/osu.Game/Rulesets/UI/FrameStabilityContainer.cs:129 | `updateClock()` | 26/37 | 23/42 |
| lazer/osu.Game/Rulesets/UI/FrameStabilityContainer.cs:222 | `updateReplay(System.Double&)` | 5/8 | 3/8 |
| lazer/osu.Game/Rulesets/UI/FrameStabilityContainer.cs:258 | `applyFrameStability(System.Double&)` | 12/12 | 7/8 |
| lazer/osu.Game/Rulesets/UI/FrameStabilityContainer.cs:303 | `get_AdjustmentsFromMods()` | 1/1 | 2/4 |
| lazer/osu.Game/Rulesets/UI/HitObjectContainer.cs:82 | `GetDrawable(osu.Game.Rulesets.Objects.HitObjectLifetimeEntry)` | 3/4 | 3/6 |
| lazer/osu.Game/Rulesets/UI/HitObjectContainer.cs:91 | `AddDrawable(osu.Game.Rulesets.Objects.HitObjectLifetimeEntry,osu.Game.Rulesets.Objects.Drawables.DrawableHitOb` | 4/4 | 2/4 |
| lazer/osu.Game/Rulesets/UI/HitObjectContainer.cs:99 | `RemoveDrawable(osu.Game.Rulesets.Objects.HitObjectLifetimeEntry,osu.Game.Rulesets.Objects.Drawables.DrawableHi` | 5/5 | 2/4 |
| lazer/osu.Game/Rulesets/UI/HitObjectContainer.cs:149 | `onNewResult(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject,osu.Game.Rulesets.Judgements.JudgementResult` | 1/1 | 1/2 |
| lazer/osu.Game/Rulesets/UI/HitObjectContainer.cs:155 | `bindStartTime(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject)` | 6/8 | 0/0 |
| lazer/osu.Game/Rulesets/UI/HitObjectContainer.cs:174 | `unbindAllStartTimes()` | 3/4 | 1/2 |
| lazer/osu.Game/Rulesets/UI/HitObjectContainer.cs:181 | `Compare(osu.Framework.Graphics.Drawable,osu.Framework.Graphics.Drawable)` | 3/4 | 4/6 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:69 | `get_AllHitObjects()` | 4/6 | 2/4 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:139 | `load()` | 5/5 | 1/2 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:254 | `LoadComplete()` | 4/5 | 2/4 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:265 | `Update()` | 9/10 | 9/12 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:398 | `osu.Game.Rulesets.UI.IPooledHitObjectProvider.GetPooledDrawableRepresentation(osu.Game.Rulesets.Objects.HitObj` | 30/30 | 11/14 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:433 | `prepareDrawableHitObjectPool(osu.Game.Rulesets.Objects.HitObject)` | 7/7 | 5/6 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:484 | `onNewResult(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject,osu.Game.Rulesets.Judgements.JudgementResult` | 3/3 | 1/2 |
| lazer/osu.Game/Rulesets/UI/RulesetInputManager.cs:86 | `HandleInputStateChange(osu.Framework.Input.StateChanges.Events.InputStateChangeEvent)` | 7/9 | 7/10 |
| lazer/osu.Game/Rulesets/UI/RulesetInputManager.cs:114 | `set_ReplayInputHandler(osu.Game.Input.Handlers.ReplayInputHandler)` | 8/10 | 3/6 |
| lazer/osu.Game/Rulesets/UI/RulesetInputManager.cs:145 | `Handle(osu.Framework.Input.Events.UIEvent)` | 1/5 | 4/8 |
| lazer/osu.Game/Rulesets/UI/RulesetInputManager.cs:240 | `Apply(osu.Framework.Input.States.InputState,osu.Framework.Input.StateChanges.IInputStateChangeHandler)` | 11/12 | 3/6 |
| lazer/osu.Game/Rulesets/UI/FrameStabilityContainer.cs:297 | `get_FramesPerSecond()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/UI/FrameStabilityContainer.cs:299 | `get_StartTime()` | 0/1 | 0/2 |
| lazer/osu.Game/Rulesets/UI/FrameStabilityContainer.cs:309 | `osu.Game.Rulesets.UI.IFrameStableClock.get_IsCatchingUp()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/UI/FrameStabilityContainer.cs:310 | `osu.Game.Rulesets.UI.IFrameStableClock.get_WaitingOnFrames()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/UI/HitObjectContainer.cs:71 | `Remove(osu.Game.Rulesets.Objects.HitObjectLifetimeEntry)` | 0/4 | 0/4 |
| lazer/osu.Game/Rulesets/UI/HitObjectContainer.cs:129 | `Add(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject)` | 0/6 | 0/2 |
| lazer/osu.Game/Rulesets/UI/HitObjectContainer.cs:139 | `Remove(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject)` | 0/3 | 0/2 |
| lazer/osu.Game/Rulesets/UI/HitObjectContainer.cs:145 | `IndexOf(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject)` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:60 | `get_ScreenSpaceToGamefield()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:106 | `get_SkinnableComponentScreenSpaceDrawQuad()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:171 | `Add(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject)` | 0/5 | 0/2 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:184 | `Remove(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject)` | 0/4 | 0/2 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:206 | `OnHitObjectRemoved(osu.Game.Rulesets.Objects.HitObject)` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:217 | `OnNewDrawableHitObject(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject)` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:229 | `CreateCursor()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:238 | `AddNested(osu.Game.Rulesets.UI.Playfield)` | 0/8 | 0/0 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:328 | `Remove(osu.Game.Rulesets.Objects.HitObject)` | 0/4 | 0/2 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:347 | `onEntryRemoved(osu.Game.Rulesets.Objects.HitObjectLifetimeEntry,osu.Game.Rulesets.Objects.HitObject)` | 0/4 | 0/2 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:362 | `CreateLifetimeEntry(osu.Game.Rulesets.Objects.HitObject)` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:491 | `revertResult(osu.Game.Rulesets.Objects.HitObjectLifetimeEntry)` | 0/5 | 0/2 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:525 | `SetKeepAlive(osu.Game.Rulesets.Objects.HitObject,System.Boolean)` | 0/6 | 0/4 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:540 | `KeepAllAlive()` | 0/5 | 0/4 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:552 | `get_PastLifetimeExtension()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:555 | `set_PastLifetimeExtension(System.Double)` | 0/4 | 0/2 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:567 | `get_FutureLifetimeExtension()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/UI/Playfield.cs:570 | `set_FutureLifetimeExtension(System.Double)` | 0/4 | 0/2 |
| lazer/osu.Game/Rulesets/UI/RulesetInputManager.cs:42 | `get_Recorder()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/UI/RulesetInputManager.cs:45 | `set_Recorder(osu.Game.Rulesets.UI.ReplayRecorder)` | 0/9 | 0/10 |
| lazer/osu.Game/Rulesets/UI/RulesetInputManager.cs:162 | `HandleMouseTouchStateChange(osu.Framework.Input.StateChanges.Events.TouchStateChangeEvent)` | 0/3 | 0/2 |
| lazer/osu.Game/Rulesets/UI/RulesetInputManager.cs:177 | `Attach(osu.Game.Screens.Play.HUD.InputCountController)` | 0/8 | 0/0 |
| lazer/osu.Game/Rulesets/UI/RulesetInputManager.cs:191 | `Attach(osu.Game.Screens.Play.HUD.ClicksPerSecond.ClicksPerSecondController)` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/UI/RulesetInputManager.cs:197 | `.ctor(osu.Game.Screens.Play.HUD.ClicksPerSecond.ClicksPerSecondController)` | 0/3 | 0/0 |
| lazer/osu.Game/Rulesets/UI/RulesetInputManager.cs:204 | `OnPressed(osu.Framework.Input.Events.KeyBindingPressEvent`1<T>)` | 0/2 | 0/0 |
| lazer/osu.Game/Rulesets/UI/RulesetInputManager.cs:210 | `OnReleased(osu.Framework.Input.Events.KeyBindingReleaseEvent`1<T>)` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/UI/RulesetInputManager.cs:216 | `CreateKeyBindingContainer(osu.Game.Rulesets.RulesetInfo,System.Int32,osu.Framework.Input.Bindings.Simultaneous` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/UI/RulesetInputManager.cs:220 | `get_HandleRepeats()` | 0/1 | 0/0 |

</details>

<details><summary>osu.Game: replays: 13 methods not fully covered (6 never entered)</summary>

| file:line | method | lines | branches |
|---|---|---|---|
| lazer/osu.Game/Input/Handlers/ReplayInputHandler.cs:45 | `Apply(osu.Framework.Input.States.InputState,osu.Framework.Input.StateChanges.IInputStateChangeHandler)` | 14/15 | 11/12 |
| lazer/osu.Game/Rulesets/Replays/FramedReplayInputHandler.cs:28 | `get_WaitingForFrame()` | 1/1 | 1/2 |
| lazer/osu.Game/Rulesets/Replays/FramedReplayInputHandler.cs:52 | `get_StartFrame()` | 2/3 | 1/2 |
| lazer/osu.Game/Rulesets/Replays/FramedReplayInputHandler.cs:67 | `get_EndFrame()` | 2/3 | 1/2 |
| lazer/osu.Game/Rulesets/Replays/FramedReplayInputHandler.cs:110 | `get_inImportantSection()` | 2/4 | 3/8 |
| lazer/osu.Game/Rulesets/Replays/FramedReplayInputHandler.cs:129 | `SetFrameFromTime(System.Double)` | 12/18 | 7/20 |
| lazer/osu.Game/Rulesets/Replays/FramedReplayInputHandler.cs:179 | `CollectPendingInputs(System.Collections.Generic.List`1<osu.Framework.Input.StateChanges.IInput>)` | 4/5 | 3/4 |
| lazer/osu.Game/Input/Handlers/ReplayInputHandler.cs:98 | `Apply(osu.Framework.Input.States.InputState,osu.Framework.Input.StateChanges.IInputStateChangeHandler)` | 0/2 | 0/0 |
| lazer/osu.Game/Input/Handlers/ReplayInputHandler.cs:113 | `.ctor(osu.Framework.Input.States.InputState,osu.Framework.Input.StateChanges.IInput,osu.Game.Rulesets.Replays.` | 0/3 | 0/0 |
| lazer/osu.Game/Rulesets/Replays/FramedReplayInputHandler.cs:42 | `get_NextFrame()` | 0/1 | 0/2 |
| lazer/osu.Game/Rulesets/Replays/FramedReplayInputHandler.cs:85 | `get_AllowedImportantTimeSpan()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Replays/FramedReplayInputHandler.cs:118 | `IsImportant(TFrame)` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Replays/FramedReplayInputHandler.cs:189 | `CollectReplayInputs(System.Collections.Generic.List`1<osu.Framework.Input.StateChanges.IInput>)` | 0/1 | 0/0 |

</details>

<details><summary>osu.Game: mods (base): 89 methods not fully covered (80 never entered)</summary>

| file:line | method | lines | branches |
|---|---|---|---|
| lazer/osu.Game/Rulesets/Mods/ModAccuracyChallenge.cs:71 | `ApplyToScoreProcessor(osu.Game.Rulesets.Scoring.ScoreProcessor)` | 12/12 | 3/4 |
| lazer/osu.Game/Rulesets/Mods/ModAdaptiveSpeed.cs:164 | `ApplyToDrawableHitObject(osu.Game.Rulesets.Objects.Drawables.DrawableHitObject)` | 19/25 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModAdaptiveSpeed.cs:192 | `ApplyToBeatmap(osu.Game.Beatmaps.IBeatmap)` | 9/9 | 5/6 |
| lazer/osu.Game/Rulesets/Mods/ModDifficultyAdjust.cs:40 | `.ctor()` | 17/19 | 4/4 |
| lazer/osu.Game/Rulesets/Mods/ModEasyWithExtraLives.cs:47 | `ApplyToPlayer(osu.Game.Screens.Play.Player)` | 3/4 | 1/2 |
| lazer/osu.Game/Rulesets/Mods/ModEasyWithExtraLives.cs:57 | `PerformFail()` | 4/4 | 3/4 |
| lazer/osu.Game/Rulesets/Mods/ModFailCondition.cs:34 | `TriggerFailure()` | 1/1 | 1/2 |
| lazer/osu.Game/Rulesets/Mods/ModPerfect.cs:32 | `FailCondition(osu.Game.Rulesets.Scoring.HealthProcessor,osu.Game.Rulesets.Judgements.JudgementResult)` | 2/2 | 5/6 |
| lazer/osu.Game/Rulesets/Mods/ModTimeRamp.cs:82 | `ApplyToBeatmap(osu.Game.Beatmaps.IBeatmap)` | 6/6 | 2/4 |
| lazer/osu.Game/Rulesets/Mods/ModAccuracyChallenge.cs:23 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModAccuracyChallenge.cs:27 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModAccuracyChallenge.cs:29 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModAccuracyChallenge.cs:31 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModAccuracyChallenge.cs:35 | `get_RequiresConfiguration()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModAccuracyChallenge.cs:37 | `get_Ranked()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModAccuracyChallenge.cs:43 | `MoveNext()` | 0/7 | 0/6 |
| lazer/osu.Game/Rulesets/Mods/ModAccuracyChallenge.cs:107 | `.ctor()` | 0/3 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModAdaptiveSpeed.cs:26 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModAdaptiveSpeed.cs:30 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModAdaptiveSpeed.cs:32 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModAdaptiveSpeed.cs:34 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModAdaptiveSpeed.cs:36 | `get_ValidForMultiplayer()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModAdaptiveSpeed.cs:37 | `get_ValidForMultiplayerAsFreeMod()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModAdaptiveSpeed.cs:152 | `ApplyToSample(osu.Framework.Audio.IAdjustableAudioComponent)` | 0/2 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModClassic.cs:12 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModClassic.cs:16 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModClassic.cs:18 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModClassic.cs:20 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModClassic.cs:31 | `get_Ranked()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModClassic.cs:33 | `get_ValidForFreestyleAsRequiredMod()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModDifficultyAdjust.cs:18 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModDifficultyAdjust.cs:20 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModDifficultyAdjust.cs:24 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModDifficultyAdjust.cs:26 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModDifficultyAdjust.cs:28 | `get_RequiresConfiguration()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModDifficultyAdjust.cs:30 | `get_ValidForFreestyleAsRequiredMod()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModDifficultyAdjust.cs:74 | `get_ExtendedIconInformation()` | 0/5 | 0/6 |
| lazer/osu.Game/Rulesets/Mods/ModDifficultyAdjust.cs:82 | `<get_ExtendedIconInformation>g__format\|29_0(System.String,osu.Game.Rulesets.Mods.DifficultyBindable)` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModDifficultyAdjust.cs:88 | `IsExactlyOneSettingChanged(osu.Game.Rulesets.Mods.DifficultyBindable[])` | 0/7 | 0/6 |
| lazer/osu.Game/Rulesets/Mods/ModDifficultyAdjust.cs:108 | `MoveNext()` | 0/5 | 0/4 |
| lazer/osu.Game/Rulesets/Mods/ModDoubleTime.cs:17 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModDoubleTime.cs:19 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModDoubleTime.cs:20 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModDoubleTime.cs:21 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModDoubleTime.cs:22 | `get_Ranked()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModDoubleTime.cs:39 | `MoveNext()` | 0/5 | 0/6 |
| lazer/osu.Game/Rulesets/Mods/ModEasy.cs:13 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModEasy.cs:15 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModEasy.cs:16 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModEasy.cs:18 | `get_Ranked()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModEasy.cs:19 | `get_ValidForFreestyleAsRequiredMod()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModEasyWithExtraLives.cs:30 | `MoveNext()` | 0/3 | 0/2 |
| lazer/osu.Game/Rulesets/Mods/ModEasyWithExtraLives.cs:65 | `get_RestartOnFail()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModFailCondition.cs:21 | `get_RestartOnFail()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModHalfTime.cs:17 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModHalfTime.cs:19 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModHalfTime.cs:20 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModHalfTime.cs:21 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModHalfTime.cs:22 | `get_Ranked()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModHalfTime.cs:39 | `MoveNext()` | 0/5 | 0/6 |
| lazer/osu.Game/Rulesets/Mods/ModNoFail.cs:16 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModNoFail.cs:18 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModNoFail.cs:19 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModNoFail.cs:20 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModNoFail.cs:22 | `get_Ranked()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModNoFail.cs:23 | `get_ValidForFreestyleAsRequiredMod()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModNoFail.cs:32 | `get_RestartOnFail()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModNoFail.cs:41 | `ApplyToHUD(osu.Game.Screens.Play.HUDOverlay)` | 0/2 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModPerfect.cs:16 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModPerfect.cs:18 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModPerfect.cs:19 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModPerfect.cs:20 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModPerfect.cs:21 | `get_Ranked()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModPerfect.cs:22 | `get_ValidForFreestyleAsRequiredMod()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModRateAdjust.cs:14 | `get_ValidForFreestyleAsRequiredMod()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModRateAdjust.cs:15 | `get_ValidForMultiplayerAsFreeMod()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModRateAdjust.cs:23 | `ApplyToSample(osu.Framework.Audio.IAdjustableAudioComponent)` | 0/2 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModRateAdjust.cs:34 | `MoveNext()` | 0/3 | 0/2 |
| lazer/osu.Game/Rulesets/Mods/ModRateAdjust.cs:39 | `get_ExtendedIconInformation()` | 0/1 | 0/2 |
| lazer/osu.Game/Rulesets/Mods/ModSuddenDeath.cs:16 | `get_Name()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModSuddenDeath.cs:18 | `get_Icon()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModSuddenDeath.cs:19 | `get_Type()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModSuddenDeath.cs:20 | `get_Description()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModSuddenDeath.cs:21 | `get_Ranked()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModSuddenDeath.cs:22 | `get_ValidForFreestyleAsRequiredMod()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModTimeRamp.cs:33 | `get_ValidForFreestyleAsRequiredMod()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModTimeRamp.cs:34 | `get_ValidForMultiplayerAsFreeMod()` | 0/1 | 0/0 |
| lazer/osu.Game/Rulesets/Mods/ModTimeRamp.cs:42 | `MoveNext()` | 0/5 | 0/8 |
| lazer/osu.Game/Rulesets/Mods/ModTimeRamp.cs:77 | `ApplyToSample(osu.Framework.Audio.IAdjustableAudioComponent)` | 0/2 | 0/0 |

</details>

<details><summary>osu.Game: legacy score decoder: 8 methods not fully covered (3 never entered)</summary>

| file:line | method | lines | branches |
|---|---|---|---|
| lazer/osu.Game/Scoring/Legacy/LegacyScoreDecoder.cs:39 | `Parse(System.IO.Stream)` | 76/80 | 28/34 |
| lazer/osu.Game/Scoring/Legacy/LegacyScoreDecoder.cs:170 | `readCompressedData(System.Byte[],System.Action`1<System.IO.StreamReader>)` | 13/15 | 4/6 |
| lazer/osu.Game/Scoring/Legacy/LegacyScoreDecoder.cs:204 | `PopulateMaximumStatistics(osu.Game.Scoring.ScoreInfo,osu.Game.Beatmaps.WorkingBeatmap)` | 18/22 | 13/17 |
| lazer/osu.Game/Scoring/Legacy/LegacyScoreDecoder.cs:270 | `readLegacyReplay(osu.Game.Replays.Replay,System.IO.StreamReader)` | 30/31 | 26/32 |
| lazer/osu.Game/Scoring/Legacy/LegacyScoreDecoder.cs:356 | `convertFrame(osu.Game.Replays.Legacy.LegacyReplayFrame,osu.Game.Rulesets.Replays.ReplayFrame)` | 6/7 | 1/2 |
| lazer/osu.Game/Scoring/Legacy/LegacyScoreDecoder.cs:261 | `PopulateTotalScoreWithoutMods(osu.Game.Scoring.ScoreInfo)` | 0/5 | 0/0 |
| lazer/osu.Game/Scoring/Legacy/LegacyScoreDecoder.cs:384 | `get_Hash()` | 0/1 | 0/0 |
| lazer/osu.Game/Scoring/Legacy/LegacyScoreDecoder.cs:386 | `.ctor(System.String)` | 0/3 | 0/0 |

</details>

<details><summary>osu.Game: gameplay clocks/breaks: 1 methods not fully covered (0 never entered)</summary>

| file:line | method | lines | branches |
|---|---|---|---|
| lazer/osu.Game/Screens/Play/BreakTracker.cs:34 | `set_Breaks(System.Collections.Generic.IReadOnlyList`1<osu.Game.Beatmaps.Timing.BreakPeriod>)` | 4/5 | 1/2 |

</details>

<details><summary>framework: clocks: 2 methods not fully covered (1 never entered)</summary>

| file:line | method | lines | branches |
|---|---|---|---|
| osu-framework/osu.Framework/Timing/FramedClock.cs:67 | `ProcessFrame()` | 25/25 | 9/10 |
| osu-framework/osu.Framework/Timing/FramedClock.cs:112 | `ToString()` | 0/1 | 0/0 |

</details>

<details><summary>framework: input (queues, states, handlers): 15 methods not fully covered (7 never entered)</summary>

| file:line | method | lines | branches |
|---|---|---|---|
| osu-framework/osu.Framework/Input/Bindings/KeyBindingContainer.cs:89 | `BuildNonPositionalInputQueue(System.Collections.Generic.List`1<osu.Framework.Graphics.Drawable>,System.Boolean` | 5/6 | 3/4 |
| osu-framework/osu.Framework/Input/Bindings/KeyBindingContainer.cs:103 | `BuildPositionalInputQueue(osuTK.Vector2,System.Collections.Generic.List`1<osu.Framework.Graphics.Drawable>)` | 5/6 | 3/4 |
| osu-framework/osu.Framework/Input/Bindings/KeyBindingContainer.cs:122 | `Handle(osu.Framework.Input.Events.UIEvent)` | 2/28 | 13/30 |
| osu-framework/osu.Framework/Input/Bindings/KeyBindingContainer.cs:324 | `PropagatePressed(System.Collections.Generic.IEnumerable`1<osu.Framework.Graphics.Drawable>,osu.Framework.Input` | 10/12 | 7/10 |
| osu-framework/osu.Framework/Input/Bindings/KeyBindingContainer.cs:396 | `PropagateReleased(System.Collections.Generic.IEnumerable`1<osu.Framework.Graphics.Drawable>,osu.Framework.Inpu` | 6/6 | 6/8 |
| osu-framework/osu.Framework/Input/Bindings/KeyBindingContainer.cs:407 | `TriggerReleased(T)` | 1/1 | 2/4 |
| osu-framework/osu.Framework/Input/Bindings/KeyBindingContainer.cs:411 | `TriggerPressed(T)` | 3/4 | 3/6 |
| osu-framework/osu.Framework/Input/Bindings/KeyBindingContainer.cs:434 | `triggerKeyBindingEvent(osu.Framework.Graphics.IDrawable,osu.Framework.Input.Events.KeyBindingEvent`1<T>)` | 4/6 | 6/12 |
| osu-framework/osu.Framework/Input/Bindings/KeyBindingContainer.cs:191 | `handleRepeat(osu.Framework.Input.States.InputState)` | 0/8 | 0/6 |
| osu-framework/osu.Framework/Input/Bindings/KeyBindingContainer.cs:213 | `handleNewPressed(osu.Framework.Input.States.InputState,osu.Framework.Input.Bindings.InputKey,System.Nullable`1` | 0/37 | 0/44 |
| osu-framework/osu.Framework/Input/Bindings/KeyBindingContainer.cs:306 | `getScrollAmount(osu.Framework.Input.Bindings.InputKey,System.Nullable`1<osuTK.Vector2>)` | 0/5 | 0/13 |
| osu-framework/osu.Framework/Input/Bindings/KeyBindingContainer.cs:356 | `releasePressedActions(osu.Framework.Input.States.InputState)` | 0/6 | 0/8 |
| osu-framework/osu.Framework/Input/Bindings/KeyBindingContainer.cs:369 | `handleNewReleased(osu.Framework.Input.States.InputState,osu.Framework.Input.Bindings.InputKey)` | 0/12 | 0/8 |
| osu-framework/osu.Framework/Input/Bindings/KeyBindingContainer.cs:421 | `getInputQueue(osu.Framework.Input.Bindings.IKeyBinding,System.Boolean)` | 0/6 | 0/6 |
| osu-framework/osu.Framework/Input/Bindings/KeyBindingContainer.cs:471 | `get_HandleRepeats()` | 0/1 | 0/0 |

</details>

<details><summary>framework: utils/math: 42 methods not fully covered (37 never entered)</summary>

| file:line | method | lines | branches |
|---|---|---|---|
| osu-framework/osu.Framework/Utils/Interpolation.cs:29 | `Damp(System.Double,System.Double,System.Double,System.Double)` | 2/3 | 2/4 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:209 | `ValueAt(System.Double,TValue,TValue,System.Double,System.Double,TEasing&)` | 2/3 | 1/2 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:261 | `ValueAt(System.Double,osuTK.Graphics.Color4,osuTK.Graphics.Color4,System.Double,System.Double,TEasing&)` | 14/14 | 5/6 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:337 | `ValueAt(System.Double,System.Double,System.Double,System.Double,System.Double,TEasing&)` | 9/10 | 5/6 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:401 | `.cctor()` | 22/39 | 21/38 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:60 | `Lagrange(System.ReadOnlySpan`1<osuTK.Vector2>,System.Double)` | 0/6 | 0/4 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:77 | `LagrangeBasis(System.ReadOnlySpan`1<osuTK.Vector2>,System.Int32,System.Double)` | 0/5 | 0/4 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:94 | `BarycentricWeights(System.ReadOnlySpan`1<osuTK.Vector2>)` | 0/9 | 0/6 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:121 | `BarycentricLagrange(System.ReadOnlySpan`1<osuTK.Vector2>,System.Double[],System.Double)` | 0/13 | 0/8 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:145 | `ValueAt(System.Double,osu.Framework.Graphics.Colour.ColourInfo,osu.Framework.Graphics.Colour.ColourInfo,System` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:148 | `ValueAt(System.Double,osu.Framework.Graphics.Effects.EdgeEffectParameters,osu.Framework.Graphics.Effects.EdgeE` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:151 | `ValueAt(System.Double,osu.Framework.Graphics.Colour.SRGBColour,osu.Framework.Graphics.Colour.SRGBColour,System` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:157 | `ValueAt(System.Double,osu.Framework.Graphics.Colour4,osu.Framework.Graphics.Colour4,System.Double,System.Doubl` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:160 | `ValueAt(System.Double,System.Byte,System.Byte,System.Double,System.Double,osu.Framework.Graphics.Easing)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:163 | `ValueAt(System.Double,System.SByte,System.SByte,System.Double,System.Double,osu.Framework.Graphics.Easing)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:166 | `ValueAt(System.Double,System.Int16,System.Int16,System.Double,System.Double,osu.Framework.Graphics.Easing)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:169 | `ValueAt(System.Double,System.UInt16,System.UInt16,System.Double,System.Double,osu.Framework.Graphics.Easing)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:172 | `ValueAt(System.Double,System.Int32,System.Int32,System.Double,System.Double,osu.Framework.Graphics.Easing)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:175 | `ValueAt(System.Double,System.UInt32,System.UInt32,System.Double,System.Double,osu.Framework.Graphics.Easing)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:178 | `ValueAt(System.Double,System.Int64,System.Int64,System.Double,System.Double,osu.Framework.Graphics.Easing)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:181 | `ValueAt(System.Double,System.UInt64,System.UInt64,System.Double,System.Double,osu.Framework.Graphics.Easing)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:187 | `ValueAt(System.Double,System.Decimal,System.Decimal,System.Double,System.Double,osu.Framework.Graphics.Easing)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:190 | `ValueAt(System.Double,System.Double,System.Double,System.Double,System.Double,osu.Framework.Graphics.Easing)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:196 | `ValueAt(System.Double,osuTK.Vector3,osuTK.Vector3,System.Double,System.Double,osu.Framework.Graphics.Easing)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:199 | `ValueAt(System.Double,osu.Framework.Graphics.Primitives.RectangleF,osu.Framework.Graphics.Primitives.Rectangle` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:202 | `ValueAt(System.Double,TValue,TValue,System.Double,System.Double,osu.Framework.Graphics.Easing)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:216 | `ApplyEasing(osu.Framework.Graphics.Easing,System.Double)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:220 | `ApplyEasing(TEasing&,System.Double)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:240 | `ValueAt(System.Double,osu.Framework.Graphics.Effects.EdgeEffectParameters,osu.Framework.Graphics.Effects.EdgeE` | 0/9 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:251 | `ValueAt(System.Double,osu.Framework.Graphics.Colour.SRGBColour,osu.Framework.Graphics.Colour.SRGBColour,System` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:284 | `ValueAt(System.Double,osu.Framework.Graphics.Colour4,osu.Framework.Graphics.Colour4,System.Double,System.Doubl` | 0/14 | 0/6 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:306 | `ValueAt(System.Double,System.Byte,System.Byte,System.Double,System.Double,TEasing&)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:309 | `ValueAt(System.Double,System.SByte,System.SByte,System.Double,System.Double,TEasing&)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:312 | `ValueAt(System.Double,System.Int16,System.Int16,System.Double,System.Double,TEasing&)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:315 | `ValueAt(System.Double,System.UInt16,System.UInt16,System.Double,System.Double,TEasing&)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:318 | `ValueAt(System.Double,System.Int32,System.Int32,System.Double,System.Double,TEasing&)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:321 | `ValueAt(System.Double,System.UInt32,System.UInt32,System.Double,System.Double,TEasing&)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:324 | `ValueAt(System.Double,System.Int64,System.Int64,System.Double,System.Double,TEasing&)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:327 | `ValueAt(System.Double,System.UInt64,System.UInt64,System.Double,System.Double,TEasing&)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:333 | `ValueAt(System.Double,System.Decimal,System.Decimal,System.Double,System.Double,TEasing&)` | 0/1 | 0/0 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:366 | `ValueAt(System.Double,osuTK.Vector3,osuTK.Vector3,System.Double,System.Double,TEasing&)` | 0/6 | 0/4 |
| osu-framework/osu.Framework/Utils/Interpolation.cs:378 | `ValueAt(System.Double,osu.Framework.Graphics.Primitives.RectangleF,osu.Framework.Graphics.Primitives.Rectangle` | 0/10 | 0/4 |

</details>

## 3. Unexercised branches that affect judgement or score (ranked)

### 3.1 Reachable from `.osr` playback (the actionable list)

Ranked by how much judgement/score they can affect.

| # | lazer location | branch never taken by the corpora | effect | Lean model | targeted test |
|---|---|---|---|---|---|
| 1 | `O/Objects/Drawables/SliderInputManager.cs:113-116`, `:130-133` (`PostProcessHeadJudgement`) | slider head hit late while the cursor is inside the 2.4r follow area of the *current* ball position but **outside** it for an already-passed, unjudged repeat or tick: `allTicksInRange = false` → those nested objects get `MissForcefully` and tracking only re-enables in the 1r ball area | per-object judgements (LargeTickMiss vs Hit), combo, slider result, score | yes: `Sim/Step.lean` `postProcessHeadJudgement` (`allIn := false`, `missForcefully`) | `ppmiss`: fast slider with repeats returning to the head, late press on the head; 38/40 jobs take the branch (repeat missed at head time) |
| 2 | `G/Rulesets/Scoring/DrainingHealthProcessor.cs:165-166` (`ComputeDrainRate`) | `healthIncreases.Count <= 1` → `DrainRate = 0` (non-legacy health processor, i.e. lazer replays without Classic, on a map with a single judgement) | health, fail with SD/PF/AC/no mods | yes: `Sim/Scoring.lean` `computeDrainRate` (`if incs.size ≤ 1 then return 0`) | `onejudgement`: single-circle maps, hit/late/miss/no press, mods none/SD/PF/NF/AC |
| 3 | `G/Scoring/Legacy/LegacyScoreDecoder.cs:305-306` | non-integer frame delta: `diff = (int)Math.Round(Parsing.ParseFloat(w))` (banker's rounding, saturating cast) | every frame time after it, so all judgements | yes: `Replay/Frames.lean:51-56` | `floatdelta`: deltas like `12.5`, `13.487`, `1.5e1`, `+12`, ` 12 `, `-2.5`, float32 reprs, mixed with integer deltas, stable and lazer format |
| 4 | `G/Scoring/Legacy/LegacyScoreDecoder.cs:109-110` | replay version in [20121008, 20140721): the online id is an **int32** (the decode position of everything after it depends on this) | whole replay decode | yes: `Replay/Osr.lean:177-178` | `oldversion`: versions 20110101…20140721 with int64/int32/no online id, beatmap versions 3/4/5/14 (+24 ms early-version offset, `:98`) |
| 5 | `O/Mods/OsuModTargetPractice.cs:210-216` | TP beat generation: a beat closer than BeatLength/2 to the next one is removed (`beats.RemoveAt(i)`) | which objects TP generates | yes: `Beatmap/ModTargetPractice.lean` `generateBeats` (backwards "kept" scan) | `tpbreaks`: maps with breaks and pairs of uninherited timing points 1-120 ms apart, seeded TP (± NF) |

These were already covered by the corpora (listed because they were suspected gaps): TP `isInsideBreakPeriod`
(`OsuModTargetPractice.cs:352-363`), spinner bonus beyond the spin limit (`DrawableSpinner.cs:359-364`), the legacy
drain fail paths (`LegacyDrainingHealthProcessor.cs:84-106`), Classic note lock, Alternate/SingleTap break resets
(`InputBlockingMod.cs:67-68`), and both arms of every hit-window and result switch that the osu! ruleset can produce.

### 3.2 Reachable only in theory (model has the logic; no input found that reaches it)

| lazer location | branch | why it is not reached | Lean model |
|---|---|---|---|
| `G/Rulesets/Scoring/LegacyDrainingHealthProcessor.cs:132-136` | `HpMultiplierNormal` overflowed to ∞ → "diverged, PASSING with zero drop" | Needs ≥ ~71k failing iterations (1.01ⁿ overflow). `testDrop` underflows to 0 after ~18k iterations, after which the end-HP check cannot fail. The recovery check passes once `mult ≥ avail/minIncrease` (~30 iterations, since every max result has a positive legacy increase, `OsuLegacyHealthProcessor.cs:55-84`). | yes (`Sim/Scoring.lean` `computeLegacyDrainRate`, `mult == ±∞ → (0, 1)`) |
| `LegacyDrainingHealthProcessor.cs:111-112`, `DrawableOsuRuleset.cs:89`, `OsuModFreezeFrame.cs:42`, `OsuModDifficultyAdjust`/`OsuModRandom` empty-map returns | beatmap with no hit objects | lazer rejects empty beatmaps before gameplay | yes (`topLevelObjectCount == 0`; `gameplayStartTime` default) |
| `O/Objects/Drawables/DrawableSpinner.cs:342-343` | spinner with 0 ticks | `totalSpins = MaximumBonusSpins + SpinsRequired + 2 ≥ 2`, because spinner duration is clamped ≥ 0 (`ConvertHitObjectParser.cs:157`) and the (int) cast saturates NaN to 0 | yes (`updateBonusScore` loops over the ticks) |
| `G/Rulesets/Objects/Drawables/DrawableHitObject.cs:324-325` | `updateStateFromResult` on (re)apply of an entry that already has a *hit* result (the Miss arm `:326-327` is covered) | an entry is only judged while its DHO is alive; a hit entry being re-applied needs a dead→alive transition, i.e. rewinding | yes (`Sim/Step.lean` `updateStateFromResult`, called from `becameAlive`) |
| `F/Utils/Interpolation.cs:345-346` | double `ValueAt` with zero duration at time ≠ start → end value | transforms with zero duration are applied with their end value without interpolating (`time >= EndTime`) | n/a (the transform engine models the end-value path) |
| `G/Rulesets/Scoring/HitWindows.cs:49`, `ScoreProcessor.cs:369` (Good), `OsuHitWindows.cs:51` arm for Good, `OsuLegacyHealthProcessor.cs:42` arms Good/Perfect/ComboBreak, `HitResult.cs:218/234/334/364` | results the osu! ruleset never produces | not osu! results | n/a |

### 3.3 Unreachable in `.osr` replay evaluation (by construction)

These are listed so that "uncovered" does not hide anything. None of them needs a model.

- **Rewinding.**
  - `SliderInputManager.cs:218-227` (tracking history),
  - `SpinnerSpinHistory.cs:81,107-116`,
  - `DrawableHitObject.cs:761-762`, `:408-412`,
  - `Playfield.cs:282-285,491`,
  - `HealthProcessor.cs:60-67`, `ScoreProcessor.cs:297,389`, `JudgementProcessor.cs:89`,
  - `ModAdaptiveSpeed.cs:176-186`, `InputBlockingMod.cs:70-71`, `OsuModStrictTracking.cs:45-46`,
  - `FramedReplayInputHandler.cs:148-149`, FSC direction flip `:187-188`, `:275`.
  - The oracle's schedules are non-decreasing, as are the model's.
- **Spectator / streaming replays.**
  - `FramedReplayInputHandler.cs:28,113-118,132-135,155-158,184` (WaitingForFrame, important frames;
    `FrameAccuratePlayback` is never set),
  - `ReplayInputHandler.cs:98,113`, `RulesetInputManager.cs:94-95`,
  - `JudgementProcessor.cs:132`, `ScoreProcessor.cs:517-547` (statistics frames),
  - FSC `waitingOnFrames` `:129-132`, `updateReplay` invalid `:156-157,243-244`.
- **Pause, seek, and non-frame-stable playback.**
  - FSC `:134-138`, `:161-181` (the bass guard needs `!hasReplayAttached`), `:232-234`,
  - `DrawableRuleset.cs:154-157`,
  - `OsuModSpunOut.cs:42-43` (rate 0).
- **Live input devices.**
  - `KeyBindingContainer.cs:127-182,191-213,356-421` (keyboard, mouse, scroll and repeat; replay actions arrive as
    `ReplayState` and go through `PropagatePressed` directly),
  - `RulesetInputManager.cs:145-216`,
  - `OsuModRelax.cs:69-76,175-181` (only without a replay),
  - `OsuInputManager.cs:52,103`.
- **ReplayPlayer UI and recorder.**
  - `DrawableOsuRuleset.cs:48-56` (analysis overlay),
  - `DrawableRuleset.cs:283-303`, `OsuReplayFrame.ToLegacy`.
- **Invariant `throw`s and defensive null checks.**
  - Hit policies `:29,60,67`, `DrawableHitObject.cs:729-741`, `HitResult.cs:383-407`, `JudgementProcessor.cs:72,156`,
  - `SliderInputManager.cs:250`, `DrawableSpinner.cs:311-312`,
  - `OsuHealthProcessor.cs:28-29` (every osu! object has combo information).
- **Non-pooled DHO paths.** These are unused because lazer pools every osu! DHO:
  - `DrawableHitObject.cs:199-201,262,277,292,453,789`,
  - `HitObjectContainer.cs:71-160`, `Playfield.cs:171-238,328-362,525-540`,
  - the `CreateNestedHitObject` overrides.
- **Legacy V1 score multiplier.** `OsuScoreMultiplierCalculatorV1` is not used for lazer scoring.
- **Decoder parts that do not affect judgement.**
  - `LegacyScoreDecoder.cs:143,222-228,261` (maximum statistics / total score without mods of the decoded ScoreInfo;
    the oracle's outputs come from the ScoreProcessor),
  - `:68,174,182,358` (error paths).
- **Visual-only mod code.**
  - HD spinner fades `OsuModHidden.cs:66,137-138,180-196`,
  - AD easings, Blinds/Bubbles/Bloom,
  - TP `nodeIndexFromTime` `:448` (samples only).

## 4. Targeted tests (`difftest/covfuzz.py`)

`python3 -I difftest/covfuzz.py --out DIR [--scenario …] [--seed S] [--count N] [--gen-mods POOL]` writes
`DIR/<scenario>/*.osu|*.osr` and `DIR/all.txt`. There is one scenario per §3.1 row (`ppmiss`, `onejudgement`,
`floatdelta`, `oldversion`, `tpbreaks`). Each sweeps the parameters around the branch condition, so that both outcomes
occur.

Corpus: `data/wip/lazer-coverage/covfuzz/{s1,s2}`, 400 jobs. s1 has no extra mods. s2 adds random ALL-pool mods with
settings (`--gen-mods ALL`).

**Coverage check.** A coverage re-run on these 400 jobs hits every §3.1 line:

- `SliderInputManager.cs:115,116,133`
- `DrainingHealthProcessor.cs:166`
- `LegacyScoreDecoder.cs:109,110,306`
- `OsuModTargetPractice.cs:215`

**Differential test (Lean evaltest vs oracle).** It used `difftest/eval_diff.py run`, with evaltest pinned at
`data/wip/end-to-end-eval/bin/evaltest` (built from 5c15cfb + perf fix). The comparison covers every judgement (type,
result, RawTime bits, combo, health), statistics, score, accuracy, rank, fail state, and the ReplayPlayer re-run when
the job failed.

| schedule | jobs | match | judgements compared | ReplayPlayer re-runs compared |
|---|---|---|---|---|
| catchup | 400 | 400 | 4674 | 202 |
| perframe | 400 | 400 | 4674 | 202 |
| dense1ms | 400 | 400 | 4674 | 202 |

Earlier exploratory batches (scratch, different seeds) also matched:

- 40 ppmiss: catchup, perframe, dense1ms;
- 120 onejudgement/floatdelta/oldversion/tpbreaks: 3 schedules;
- 180 ppmiss/floatdelta/onejudgement with ALL mods: catchup.

In total that is 1200 + 820 jobs with **0 mismatches**, so ISSUES.md is unchanged.

## 5. Notes and follow-ups

- The judgement core has no remaining actionable coverage gap. Future coverage work should look at *value* coverage
  rather than branch coverage. Examples: float-boundary cases already targeted by synth.py, schedule sensitivity
  (server-agreement), and mod-setting extremes.
- Re-measure after lazer/framework pin changes. Reuse `data/wip/lazer-coverage/covbin` (rebuild it with the command
  in §1) and the lists in `data/wip/lazer-coverage/lists`. A full corpus run is about 40 heavy chunks, roughly 2.5 h
  on the loaded VM.
- Not instrumented: osuTK (vector math is checked bit-exactly by nettest) and the oracle itself.
