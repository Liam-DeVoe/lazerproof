# Oracle vs server statistics on real lazer scores (D13)

Status: **PAUSED** 2026-10-22 04:20 UTC (machine time moved to the refinement proofs; restart commands in RESUME.md). Regenerate the tables with
`python3 -I difftest/oracle_vs_server_v2.py report --md data/oracle_v2/report.md`. That report is the
source of truth for the current numbers.

## What is compared

- Corpus: `difftest/fetch_v2.py` polls the public `/api/v2/scores?ruleset=osu` feed. It keeps lazer scores that
  have a replay and come from a gameplay-equivalent build (docs/lazer-builds.md; class A = identical to the
  pinned 2026.1005.0-lazer, class B = conditionally equivalent), with at most 1 score per beatmap and 5 per user.
  It downloads the replay and the `.osu`, and checks that md5(.osu) equals the beatmap md5 in the replay header.
  **1915 scores** so far (1767 A, 148 B; 42 different mods, e.g. HD 498, DT 440, HR 390, NF 321, RX 321, DA 195,
  EZ 166, NC 155, TD 114, CL 111, HT 55, SD 54, AC 28, FL 26, AP 22, plus single scores with SI/WG/TR/RP/BL/...).
  The crawl is bounded by disk (it stops below 3 GiB free) and by the shared CPU.
- The feed contains **passed scores only**, so fail semantics (D11) are not tested here (ISSUES G10).
- `difftest/oracle_vs_server_v2.py` runs the oracle on each replay. Mods come from the replay's own lazer JSON;
  they always equal the server's mods once values are normalised (10 vs 10.0, enum "1" vs 1). It then compares
  every HitResult count, `max_combo`, `accuracy`, `total_score`, `rank` and `passed` against the server JSON, and
  checks that `maximum_statistics` are equal. `maximum_statistics` were equal on every score: beatmap conversion and
  mod application match.
- The server accuracy is float32, served rounded to 6 dp. Example: 92030/108780 = 0.84601949 → f32 0.84601951 →
  served as 0.84602. The comparison applies exactly that transformation.

## Results (catchup, n=5113 of ~5900 crawled scores; data/oracle_v2/report.md, 2026-10-22)

| heuristic category (catchup) | count | meaning |
|---|---|---|
| exact | 3227 (63.1%) | every field equal |
| sched | 1800 (35.2%) | differences only in schedule-sensitive objects (tails, ticks, repeats, spinner bonus) |
| rounding | 21 (0.4%) | circle-level difference from integer-ms replay time rounding |
| sched-fd | 15 (0.3%) | frame-dependent or geometry-animating mod (GR, AP, ...) |
| replay-gap | 11 (0.2%) | the replay has no frames while objects are due |
| suspicious | 39 (0.8%) | anything else (before triage) |

- Build class A: 3007 exact / 1678 sched / 10 sched-fd / 35 suspicious; class B: 220 / 122 / 5 / 4.
- The bias is as before: the server has more slider-tail hits in 966 scores, fewer in 198 (live play samples tracking
  every rendered frame; the replay has <= 60 fps positions and integer-ms times).
- `maximum_statistics` and mods are still equal on every score. 3 scores are oracle errors (lazer throws).

### Triage of the 1886 catchup mismatches (`difftest/triage_v2.py`, `difftest/server_demonstrated.json`)

959 triaged, 927 untriaged (the pause stopped the backlog; the corpus grew from 1713 to 5113 evaluated meanwhile).

| triage category | count |
|---|---|
| demonstrated (exact server statistics on the bit-exact sim) | 570 |
| heuristic-sched (only tails/ticks/spinner ticks left, not flipped by dense1ms/perframe) | 360 |
| perturbation (old manual entries, see below) | 2 |
| suspicious | 27 |

Demonstrated by mechanism: note-lock rounding 397, spinner aliasing 86, schedule (dense1ms/perframe) 34, same-frame
split 32, flip-check 8, manual 6, replay gap 6, tracking regain at a rounded re-press 1. Most demonstrations also
reproduce `max_combo` and `total_score` (field `score_exact`), which depend on the order of results, not just counts.

**Suspicious headline: 46 of 5113 (0.90%)** = 27 triaged suspicious + 19 untriaged heuristic-suspicious.

Suspicious rate by mod (evaluated scores containing the mod; the report has the full list): HD 7/1364 (0.5%),
DT 4/1291 (0.3%), HR 6/1124 (0.5%), NF 16/765 (2.1%), RX 9/708 (1.3%), DA 8/521 (1.5%), EZ 5/451 (1.1%), CL 7/299
(2.3%), HT 4/105 (3.8%), AL 2/40 (5.0%), AP 1/52, DP 2/12, BR 2/11, **GR 4/7 (57%)**, BM 1/6, DF 1/3, TR 1/2.

**Concentration.** Common mods sit at 0.3-2%. The suspicious scores concentrate in the geometry-animating or
frame-dependent mods (GR 4/7, DP, BR, DF, TR, BM; AP; AL), where lazer's live behaviour depends on per-frame state the
replay does not carry. NF is high because low-accuracy, mash-heavy plays (many presses on circle StartTimes, many
misses) need several sub-ms events at once. CL is partly an artefact: classic slider results move Great/Ok with one
tail flip; the triage now treats that as schedule-only (applies to scores triaged from now on).

### Which schedule reproduces live play best?

Perframe and dense1ms were run on samples enriched with catchup mismatches, so their raw exact rates are not
comparable to catchup. Category changes on the same scores:

| | n | became exact | got worse |
|---|---|---|---|
| catchup → perframe (reference = each recorded frame time) | 128 | 2 | 0 (1 sched→sched-fd) |
| catchup → dense1ms (reference every 1 ms) | 34 (25 catchup non-exact) | **12** (11 sched + the AC fail case) | 1 exact→sched |

**Answer to "does the replay's own frame-time schedule reproduce more scores?":** barely (2/128). A **denser**
schedule does: dense1ms makes 12 of 25 catchup mismatches exact. This is consistent with live play running at a
much higher frame rate than the replay records. Exact under at least one schedule: 135/190 (only part of the
corpus has the extra schedules).

## Showing the "sched" cases really are schedule-sensitive (flip check)

The heuristic "sched" class only shows that the differences *could* come from slider tails/ticks/spinners.
To demonstrate it, `oracle_vs_server_v2.py flipcheck` uses per-judgement results from several schedules
(catchup, perframe, dense1ms, and `fine250` = an explicit reference every 0.25 ms) and from cursor-jitter runs
(`difftest/jitter_runs.py`: non-key-down frame positions moved by uniform ±1 osu!px, 3 seeds, so the margin test
uses the oracle itself). For each object it collects the set of results it took across runs. Objects that never
changed are fixed. A max-flow test then decides whether the *server's* per-result counts can be reached by
choosing, for each flipping object, one of its observed results. **A score counts as demonstrated only if that
works. Everything else stays suspicious.**

Sample: all 5 catchup-non-exact cases that were not "sched" at that time, 25 random "sched" scores, and 4 exact
controls (34 in total).

| flip check | count |
|---|---|
| demonstrated by schedule flips (catchup, perframe, dense1ms, fine250) | 21/34 (4 exact controls, 15 sched, 1 rounding, the AC fail case) |
| demonstrated with ±1 px cursor jitter (3 seeds) | 4/34 (CLHR, EZHT, NFWU, DAHDNF) |
| NOT demonstrated | 9/34 (1 is the replay with a 49 s input gap; the other 8 are covered below) |

Typical demonstrated case: 1–5 `SliderTailCircle`s (sometimes their `Slider` IgnoreHit/IgnoreMiss, a repeat or a
spinner tick) change result between catchup and dense1ms. Choosing among the observed results gives the server's
counts exactly. fine250 has finished for 7 of the 10 scores queued for it (each takes 10–170 min on the loaded VM);
the other 3 are still queued.

### Where disputed tails are decided (`difftest/tail_margin.py`, `difftest/tail_keytiming.py`)

Geometry comes from the oracle's own playable dump (`--dump-playable`: stacked position, calculated path, radius).
The cursor is the replay frames linearly interpolated, as OsuFramedReplayInputHandler does. The follow centre is
`StackedPosition + CurvePositionAt(clamp((t-start)/duration))` and the radii are r and 2.4r, as in
SliderInputManager.IsMouseInFollowArea.

- Controls: all 290 tails/ticks that the oracle *hits* have the interpolated cursor inside 2.4r over their window
  (by 9.7–108 px). This validates the geometry code.
- **Explained flips, 31 tails:** every one has the cursor inside 2.4r at some point in the window. 26 of the 31 are
  key-timing cases: the key is held at the last replay frame before the window, and the key-up frame comes 2–36 ms
  into the window. Under catchup no frame-stable step falls in [window start, release), so the tail never sees
  `Tracking` with a key held and is missed. dense1ms (and live play at high fps) has such a step, so the tail is
  hit. This is D13 sub-frame sampling of the key state.
- *Correction to the first version of this section:* it said that cursor position never decides the unexplained
  candidates. That came from a bad candidate selection (it took the k missed tails with the smallest in-window
  margin, including tails whose key was not held). The tracking trace below replaces it.

### Tracking traced along the whole slider (`difftest/tracking_trace.py`, Rust Sim)

`impl/simtest_rs/src/bin/tracktrace.rs` is a debugging binary of the Rust Sim. It uses the same loaders and the same
`mk_ctx`/`init_state`/`step_once` loop as `simtest_rs`; the core is unchanged. After every frame-stable step it
prints each slider's `Tracking`, "mouse in r", "mouse in 2.4r", "valid tracking action", pressed keys, head action
and `accept_any_after`. It runs in about 0.1 s per replay. Each run is first checked **judgement by judgement**
(object, nested index, type, result, in processor order) against the oracle's own catchup and dense1ms results.
Only validated runs are used.

For every tail/tick/repeat that misses under both catchup and dense1ms (on a slider whose head was hit), the script
finds the step where `Tracking` was last lost before the judgement and classifies the loss:
- **cursor**: the cursor left 2.4r while a valid key was held. The margin is the largest excursion of the
  interpolated cursor outside 2.4r between the last tracking step and the window start.
- **key**: no valid tracking action. The margin is the release time relative to the window start.
- **regain**: tracking can only restart inside r with a valid key held. The margin is the closest approach to r
  while a key is held.

A judgement counts as **live-flippable** if one of these margins is at the sub-frame level:
- a cursor excursion or regain within 3 px;
- or a key release less than 0.5 ms before the window, which integer-ms rounding of the release frame can move
  inside it (ISSUES G8).

Scores with sim-side mods (rate, AP, GR) run on the **Lean simtest** (M5–M7) through `--trace-tracking FILE`. That
option is a read-only debugging loop: the body of `Sim.run` plus pure queries after each step. Every other score
runs on the Rust Sim. **All 8 analysed scores match the oracle judgement by judgement under both catchup and
dense1ms,** including the two GR scores on M7 (`model/SimTest/Main.lean`, `difftest/tracking_trace.py`).

The coverage test needs two things:
- **Server hit more:** enough flippable misses: a cursor excursion or regain within 3 px, or a key release
  <0.5 ms before the window.
- **Oracle hit more:** enough *marginal hits*: cursor within 3 px of the 2.4r edge between the window start and the
  judging step.

Any other differing result (circles, spinners) blocks coverage. Results for the 9 flip-check scores without a
demonstrating flip (after jitter and fine250, 26/34 are demonstrated; HTNF 7737759009 became demonstrated by the
fine250 flips):

| score | result |
|---|---|
| 7737790568 HDNF | **explained by margin**: the tail deficit of 1 is covered by a key re-press 1.59 px from r |
| 7737792549 EZHD | **explained**. The circle part is rounding: shifting one press by 1 ms makes every statistic equal (`rounding_check.py`). The 3 missing tails are covered by 7 tails with ≤3 px margins |
| 7737721523 DTHR | **demonstrated** (new mechanism, *spinner rotation aliasing*). The only difference is spinner bonus: LargeBonus 6 vs 8. The replay has 28 ms frames under DT (`RecordFrameRate` × rate). In a consistently negative spin, three inter-frame angle deltas measure +157°, +177.7° and +131.2°. `SpinnerRotationTracker` normalises every delta to ±180° (SpinnerRotationTracker.cs:72–74), so a true motion of more than 180° between two frames counts backwards. Live play samples every frame and has no such aliasing. Inserting the true-direction midpoint frame for **any one** of the three gives **exactly the server's statistics** in the Lean sim (validated vs the oracle). Two or three insertions overshoot: LargeBonus 9 and 11 |
| 7737744200 DA | **suspicious, quantified**. The repeat and 2 of 4 tails are covered (re-press 0.02 px outside r; releases 0.10/0.12 ms before the window). For the other 2 tails the interpolated cursor leaves 2.4r **before** the window opens: 1.75 ms early by 7.25 px at 3.05 px/ms, and 20.4 ms early by 4.98 px at 0.74 px/ms. No live framerate can rescue them, since P(hit) = 0 at 240–1000 fps under the replay's linear path; a higher framerate only samples later, when the cursor is even further out. They would need the real sub-frame mouse path to deviate from the linear interpolation by ≥5–7 px. The same replay's interpolation error, measured by leaving out one frame (2-gap error divided by 4 for a one-gap estimate), has p90 of 1.65 px at 3–5 px/ms and 1.0 px at 0–1 px/ms. Required deviations are 4–7× the p90, so it stays suspicious |
| 7737756477 APEZNF | **suspicious**. The oracle hits 4 tails and 1 tick more than the server; only 1 tail hit is marginal. Code-level mechanism: Autopilot moves the cursor in `Update` from its own autoplay frames by nearest time (OsuModAutopilot.cs:43–55). The cursor therefore depends on the live update times, not on the replay. Not demonstrated |
| 7737710092 DAGRHDNFRX | **suspicious**: circle results also differ (Great/Meh/Miss). GR animates the hit area, and the oracle schedules disagree with each other on circles; tick deficit −4 with only 2 marginal |
| 7737744394 DAGRHDNFRX | **suspicious**: tails are covered in both directions (39 marginal oracle hits ≥ 5), but spinner bonus differs (LargeBonus 6 vs 5) and has not been analysed |
| 7737783636 NCRX | replay input gap (data defect) |

**Flip-check sample result: 4 of 34 suspicious** (DA, AP, 2×GR). There is no sign of an oracle error. Every one
of these 4 (and every explained case) is sub-frame information the 60 fps, integer-ms replay doesn't carry, or
per-frame mod logic.

### Mechanisms found in triage round 4 (2026-10-21/22)

- **Tool artefact, corrected.** `rounding_check.perturb` (used by the note-lock step and the press-shift search) moved a
  key-down frame behind a frame at the same integer ms. That made a backwards frame, which the decoder drops, so the
  "shift" silently deleted or delayed a frame. The earlier "reproduced by a +-1 ms press shift" results for CLNFRX
  7737904051 and HTNF 7737921480 were such artefacts. perturb now moves same-ms neighbours along (and skips moves that
  would cross a neighbour). The old note-lock demonstrations were rechecked and hold (DA+NF 7737796909, DT+NF
  7737902404, EZ+HD 7737792549, HT 7738006030, HRNF 7737788341).
- **Same-frame split (new, demonstrated).** Relax writes `changeState(false); changeState(true)` in one
  `OsuModRelax.Update`, before the DHOs update in that frame. The recorder writes two frames with the same time.
  Playback runs one frame-stable step per frame, so a DHO update (for example a LegacyHitPolicy blocker's miss expiry)
  runs between the release and the press. CLNFRX 7737904051: merging all 288 same-ms release+press pairs gives exact
  statistics, `max_combo` and `total_score`. The triage step merges such pairs; it is demonstrated in 32 scores.
- **Note-lock rounding combined with dense1ms.** HRNF 7737788341: the press at 115527 equals circle 607's StartTime, with
  the cursor already on 608. Moving it 1 ms earlier plus dense1ms gives exact statistics, max_combo and total_score.
- **Tracking regain at a rounded re-press.** DA 7737744200: de-alias + dense1ms leave one repeat whose re-press is
  0.02 px outside r from a ball receding at 0.58 px/ms. Any true press time < 31519.97 ms (inside the rounding
  interval) regains tracking, and that gives an exact result. This **localises the threshold** inside +-0.5 ms.
- **Perturbation thresholds.** Of the two old "perturbation" cases, CLNFRX is now explained by the same-frame split
  (no time threshold involved) and HTNF is not explained (below). Note-lock thresholds are exact integers
  (`time < StartTime`), so a press recorded exactly at StartTime is inside the rounding interval by construction. Hit
  windows are `floor(x) - 0.5`, so they can never flip under rounding. Positional thresholds need a geometric margin
  (as for DA above). New triage-made perturbation entries carry the shift and need the same margin check.

### Open suspicious cases (ISSUES G16, G18)

| score | status |
|---|---|
| AL 7737902231 | **localised** (G18). Spinner de-aliased. A force-miss search on stats+max_combo+total_score picks slider heads 146 (Great) and 152 (Meh) as the server's 2 extra misses. Both follow an Alternate-*blocked* Right re-press (137560, 143097). Relabelling exactly those 2 presses as Left (accepted live, so the following Left press is blocked) gives exact stats, max_combo and total_score. This is not a general rule: relabelling all blocked presses makes 9 of 20 AL scores worse. The live code path is unknown; ReplayRecorder precedes InputInterceptor in the KeyBindingContainer queue (later child, queue reversed) and records every press |
| HTNF 7737921480 | dense1ms fixes the tails. Slider 1847's head is Great on the server, but its only press is 2.4 px outside the head, and no shift helps |
| GR 7737710092 (+3 more GR, DAGRHDNFRX user) | dense1ms reproduces every circle count. The server has 15 fewer tail hits than dense1ms and 2 more tick misses; max_combo 75 vs 112 |
| AP 7737756477 | Autopilot advances one autoplay frame per Update, so it depends on frame rate by construction. Constant 30-500 fps oracle runs (`data/oracle_v2/fine*_ap.jsonl`) always hit 2-5 more tails than the server. A variable live frame rate is plausible but not shown |
| HDHR 7738056594 | localised: only circle 10 (Ok at +54 ms) moved >= 6 ms later reproduces the server (incl. score). Not sub-ms. The replay has no frames 310-18815 ms (a late start or pause) |
| DA 7738080249, DANF 7737892997 | one circle-result difference each; no feasible single shift. DANF is a mash-heavy play (948 misses, 50 presses at StartTimes) |
| the rest of the 46 | listed under "suspicious ids" in data/oracle_v2/report.md. 19 are untriaged |

## Deep-dived non-schedule mismatches

1. **Replay time rounding (3 scores: HT+NF, EZ+HD, DA+NF). Real lazer behaviour, not an oracle bug.** Lazer writes
   frame times as `(int)Math.Round(time)` (LegacyScoreEncoder.cs:173), and its decoder rounds fractional deltas back
   to integers (LegacyScoreDecoder.readLegacyReplay). `StartTimeOrderedHitPolicy.CheckHittable` blocks a hit while
   `time < blockingObject.StartTime` (StartTimeOrderedHitPolicy.cs:46), and StartTimes are integers. A live press at
   t−0.4 ms is blocked (Shake). After rounding, the same press lands exactly at t, is accepted, and force-misses the
   blocker with offset 0. Hit windows are `floor(x) − 0.5` (OsuHitWindows.SetDifficulty), so they can't flip under
   rounding; only these strict integer comparisons can. Demonstration (`difftest/rounding_check.py`): moving that
   one key-down frame 1 ms earlier
   - DA+NF 7737796909: **exact match** with the server;
   - EZ+HD 7737792549: all statistics equal (total_score differs only through combo order);
   - HT+NF 7737759009: the circle differences disappear; the remaining differences are slider tails.
2. **Input gap in the replay (1 score, 7737783636, NC+RX, 2026.1013.0-tachyon).** The replay has no frames for
   46096→95152 ms (166 objects), yet the server shows a full pass with 458 combo. The oracle (every schedule) misses
   every object from there on and fails. `difftest/replay_gaps.py` finds 3/1915 replays with such gaps (two of them
   on the pinned build). These replays are defective data, not judgement differences.
3. **Accuracy Challenge fail (7737779053, AC min 0.95 + DT+HD).** Under catchup and perframe, 4 slider tails fewer than
   live push the running accuracy below 0.95 at t=174630, and the score fails. Under dense1ms the score is **exact**
   (passes, every field equal). This is a fail cascade from a schedule-sensitive judgement.
4. **Grow (GR start_scale 0) + RX + DA, 2 scores.** Circle results differ *between oracle schedules*: catchup and
   perframe give different Great/Miss counts. Animated hit-area geometry is therefore step-dependent. A plausible
   mechanism (not yet traced): the press is hit-tested against geometry from the previous step. Tracked as
   "sched-fd" (with AP/MG/RP/AS/DF/TR/WG/SI/DP/BR/BU); flip check pending.
   Note: **RX is not frame-dependent for lazer replays.** `OsuModRelax.Update` returns early for non-legacy replays
   because the live RX presses are recorded in the replay frames (OsuModRelax.cs, `hasReplay && !legacyReplay`).
   RX scores agree like the rest: 54% exact, the rest sched.

**Oracle bugs found: none.** Each candidate traced back to a property of the data: server float32 accuracy, mod-value
spelling, integer replay times, missing replay frames, or schedule sensitivity. Mod settings deserialisation (DA with
extended_limits, DT/HT speed_change + adjust_pitch, AC minimum_accuracy, SD fail_on_slider_tail, CL sub-settings,
RD seed, MR reflection, GR start_scale) always reproduced the server's `maximum_statistics` and the mod multiplier.
On the 121 exact scores, `total_score` matched to the point.

## Open items (ISSUES.md G8-G11, G15, G16, G18)

- G8: integer-ms replay rounding (note-lock, regain); G15: spinner aliasing; both are replay-lossy, not model gaps.
- G10: no failed scores in the feed.
- G11/G16: 927 mismatches untriaged at the pause; the open suspicious cases are listed above.
- G18: the AL blocked-press anomaly.
- **No oracle or model bug has been found.** Every demonstrated case is a property of the replay data, or lazer
  live-vs-playback structure (sub-frame timing, same-frame key changes, per-frame mods).
