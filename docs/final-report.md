# lazerproof: final report (2026-10-23)

This report sorts everything the project claims into four kinds:

- **PROVED**: a machine-checked Lean theorem.
- **TRUSTED**: assumed. Nothing checks it mechanically. Each item says why it is reasonable.
- **TESTED**: checked by running both sides and comparing them. Each item gives the counts.
- **KNOWN-DIFFERENT**: a place where we know the output differs from osu!lazer or the osu! server, and why.

Every number cites a file or a commit. Where a result had not landed when this was written (2026-10-23 13:15 UTC),
the entry says **PENDING**.

Pinned versions (docs/fidelity-evidence.md, header):
- osu!lazer 2026.1005.0-lazer (ppy/osu 9a10d935b0);
- osu-framework 2026.921.1;
- .NET 10.0.13;
- glibc 2.39 (x86-64);
- the D10 playback environment: 1024×768, UI scale 1, default skin, no beatmap skin or storyboard.

---

## 1. Summary

Given a beatmap (`.osu`), a replay (`.osr`), optional mod overrides and a step schedule, `lazerproof` (through the Rust
evaluator `osu_eval`) prints every judgement, the statistics, max combo, accuracy, total score, rank and pass/fail.

Taken together, the proof and the tests make the following claim. The output is **exactly what osu!lazer
2026.1005.0-lazer computes when it replays this file**, with x86-64 glibc 2.39 floating-point results, under a
deterministic clock schedule (`catchup` by default; `perframe`, `dense1ms` or an explicit list on request).

The two halves of that claim have different strengths:

1. **Rust evaluator = Lean model.** This half is PROVED (`osu_eval_refines`, §2), under named input-size
   hypotheses. Each of them holds on every real input with a margin of ≥ 99×.
2. **Lean model = osu!lazer.** This half is TESTED, not proved (§4). There is no open mismatch: about 8,000 real
   lazer scores, 59 + 8 runs of lazer's real `ReplayPlayer` and 117 fuzzed schedules agree bit for bit. The one
   documented exception is ReplayPlayer's fail gate (§4.6).

Caveats, precisely:
- Rejections are compared by stage only; the printed reason text is not covered by the proof.
- Floats are equal up to NaN payload. No NaN output has ever been observed.
- The CLI shell (argument parsing and the JSON printer) is untranslated. It is covered by byte-identical
  regressions, not by the proof.
- The result is lazer **replaying the file**. It is not the live play the server scored. Those differ on about 37%
  of lazer scores for reasons outside any replay evaluator (§5).

---

## 2. The proof

### 2.1 The headline theorem

`OsuProofs.osu_eval_refines` (proofs/OsuProofs/Eval/JsonTop.lean). The exact statement is pinned in
proofs/scripts/headline_signature.txt.

**In plain words:** for every beatmap and replay byte string within the size bounds below, every mod override list
and every schedule, the Rust `eval::evaluate` (the function `osu_eval` runs):
- **terminates without a panic** (no overflow, no out-of-bounds index, no division by zero), and
- returns a result related to the Lean model's `OsuModel.Eval.evaluate defaultEnv` on the same inputs:
  - if both accept, all 23 result fields are equal (every judgement, statistics, combo, accuracy, score, rank,
    failed, …);
  - if both reject, the rejection stage is equal;
  - one accepting while the other rejects is excluded.

**Precisely:**

```
osu_eval_refines (O : js_EvalOpen) (e) (he : eval.env.default_env = ok e) (bm osr)
  (hb : InputBounds bm osr) (opts) (hopts : override mods ev_mcOk ∧ count < 2^61)
  (hpb : PlayableBounds bm osr opts) (sched) (hsched : explicit refs · 10^8 + 4 < 2^61)
  (hrb : RunBudgetIn defaultEnv bm osr opts sched) :
  ∃ r, eval.evaluate e bm osr opts sched = ok r ∧
       ev_topRel r (OsuModel.Eval.evaluate defaultEnv (bytesS bm) (bytesS osr) (ev_optsS opts) (ev_schedS sched))
```

Axioms: only Lean's three standard ones, `propext`, `Classical.choice` and `Quot.sound`. There are 0 `sorry`. There is
no `native_decide`, `implemented_by` or `ofReduceBool` (docs/final-audit.md §4 and pass 2 §A).

### 2.2 The hypotheses, one by one

None of these is a statement about how osu! behaves. Two are boundaries to C code (LZMA) and the platform. The rest
say "the input is not astronomically large", because the Rust uses fixed-width integers and the proof must show they
never overflow. Rows are from docs/proof-pipeline.md §5.

| hypothesis | what it says | why it is safe to assume |
|---|---|---|
| `O : js_EvalOpen` | one field, `lzmaBound`: the LZMA decoder never returns more bytes than the cap it was given | **TRUSTED** (§3.4). The C shim allocates at most `max_out` bytes and errors beyond it (model/c/lzma_shim.c). The decoder is opaque C, so Lean cannot see inside it. |
| `he : default_env = ok e` | names the environment the binary uses | Not an assumption about inputs. `eval.env.default_env_refines` (Eval/Osr.lean) proves `default_env` returns `ok`, so `e` exists. Since D72 its abstraction is the model's `defaultEnv` itself (`ev_envNorm_defaultEnv`). |
| `hb : InputBounds` | 64-bit platform; `.osu` shorter than `usize::MAX`; decoded `.osu` < 2^31 − 1 lines, each line < 2^61 characters, and slider paths < 2^32 control points / < 2^62 points; `.osr` < 2^62 bytes | Real files are < 10 MB. The LZMA payload is capped at 256 MiB. lazer itself uses `int` indices (< 2^31). §5 rows `h64`, `bmLen`, `decLines`, `osrLen`. The counts of timing points, difficulty points and objects are *derived* from `decLines`, not assumed (Eval/JsonDecSize.lean). |
| `hopts` | each `--mods` override config is well-formed (`ev_mcOk`), and there are < 2^61 of them | For the CLI path this is *proved* from the parser: `js_hopts_of_parse_mods` (Eval/JsonMods.lean). Only the count < 2^61 is trusted: argv is limited by Linux `ARG_MAX` (2 MiB), so the count is < 2^20 (§5 "CLI shell" row). |
| `hpb : PlayableBounds` | size bounds through the playable-beatmap pipeline: slider paths, control-point lists and nested-object counts after each mod hook (`GpbBounds`), and the simulation context (frames < 2^32, objects < 2^32, objects + nested < 2^62, autopilot frames < 2^62, top-level and nested object kinds) | All of these are sizes or "object kinds come from the converter". Measured on a large WG/DF/MU case: 758 objects, Σ(nested+1) = 1,699, path ≤ 286 points (docs/final-audit.md §2). Several conjuncts are provable and remain trusted only for lack of time (audit m8; §8). |
| `hsched` | an explicit schedule has fewer than ~2.3·10^10 reference times | A schedule is a text file of times. Real ones have < 10^7 entries. |
| `hrb : RunBudgetIn` | machine-integer headroom of the simulation: transform-tracker counters, `completed_spins` and the fail-trigger counter never overflow 64 bits. Stated on the model's own run: `(2U + Σ(nested+1) + 1)(2n+4) + objects·(4n+8) + 1 < 2^64−1`, `(U+1)·2·10^6 ≤ 2^54`, and `Σ(nested+1)·(1+2·#AC) ≤ 2^64−1` | **Checked on the whole corpus: `[runbudget] PASS` (ce6f6c9, docs/runbudget-check.md).** 12,490 real (map, replay) pairs × catchup/perframe/dense1ms × {own mods, +Wiggle} = 74,940 triples, all pass. Worst real case (2147769, a 55-minute map, dense1ms + WG): U = 14,541,791, margin **145×** below 2^64 and **619×** below 2^54. Synthetic worst case (a frame every 0.5 ms on the same map): margin 99×. The largest F3 value is 73,002. |

**Removed since headline-v1.** `SchedFramesIn` said that every simulation step's frame index is in range.

- It is **not derived**. Deriving it needs IEEE facts ("finite + 16.67 is finite") about Lean's `Float`, which the
  kernel treats as opaque.
- It was **replaced by a run-time check** (D72/D94). Both the model (`stepFramesOk`) and the Rust
  (`eval::step_frames_ok`) now check the range and reject at stage "sim" otherwise. `sched_ctx_refines` proves the
  two checks agree, so the theorem no longer needs the assumption.
- Behaviour on real inputs is unchanged: 12,724/12,724 corpus outputs are byte-identical (§4.5).

### 2.3 Coverage

Every Rust function reachable from `eval::evaluate` is **PROVED** or **COVERED**:
- **PROVED**: it has its own `_refines` theorem against the model function.
- **COVERED** (D63): it has no standalone theorem, but every place it is called is inside a proved function, so the
  parent's proof covers it.

Counts from the FINAL check_all at 04:52 (STATE.md "[infra] FINAL check_all OK", commit f30570a; docs/proof-status.md
at 1a89a65):

| area | proved | covered | total |
|---|---|---|---|
| net + beatmap | 559 | 0 | 559/559 |
| sim + replay | 364 (+1, see below) | 49 | 414/414 |
| eval | 138 | 1 | 139/139 |

- At 04:52 the one remaining function was `sim.step.simulate`. It was CONDITIONAL and has no Rust caller.
  `simulate_refines_full` proved it at d205c3a (05:01).
- headline-v1 check_all (e2b3db0): **1,180 theorems audited**, standard axioms only, 0 sorry, headline signature
  equal to the allowlist.
- D72 branch check_all: 1,184 audited (STATE 09:4x).
- check_all on main after the D72 merge (clean checkout, full rebuild): **1,184 theorems audited**, standard
  axioms only, 0 sorry, headline signature equal to the allowlist (STATE 13:0x "[d72] MERGED"). The per-area table
  above was not regenerated at that run; D72 added and retargeted theorems but no new uncovered Rust function.

**Allowlist.** check_all compares the headline's printed signature against proofs/scripts/headline_signature.txt.
Since audit pass 2 (N1) it also compares structural hashes of every proof-local definition behind it. That was 104
definitions at v1. After D72 it is 103: `SchedFramesIn`, `ev_envNorm`, `ev_cnNorm` and `simPacName` were dropped, and
`evS_sched0` was added. A new hypothesis, or a silently changed definition, fails the check. Every change is
re-recorded deliberately, with its diff in docs/proof-pipeline.md §5.

**Audits.** Two adversarial audits were run (docs/final-audit.md):
- pass 1: 0 critical, 3 major, 12 minor;
- pass 2: 0 critical, 0 major, 8 minor.

The three majors were resolved as follows:
- M1 (the Wiggle budget was false on long maps): fixed by Σ-alive accounting, then the corpus PASS.
- M2 (environment): fixed in D72.
- M3 (the CLI shell was not listed as trusted): now a §5 row.

### 2.4 Tags

- **headline-v1** = `ab24f87` (2026-10-23 07:25). Its hypothesis list included `SchedFramesIn`, and the spec side
  was `ev_envNorm defaultEnv`.
- **headline-v2** = tag object `ffeb824` on commit **`45f1c73`** (the D72 merge), after the clean check_all on main
  (STATE 13:0x "[d72] MERGED"). It has no `SchedFramesIn`, and the spec side is `defaultEnv`. The allowlist diff
  from v1 is in docs/proof-pipeline.md §5 (recorded in 5ea49a4).

---

## 3. The trusted base

These are not hypotheses of the theorem. They are the link between "a Lean theorem about the Aeneas translation" and
"the binary you run" (docs/proof-pipeline.md §4, §5, §5.1, §5.2).

### 3.1 Lean and the translation
- **Lean 4.35 kernel**, with core `Float` treated as opaque. The axiom audit runs `#print axioms` on every theorem.
- **Charon (nightly-2026-09-17) + Aeneas**, translating Rust → Lean (`proofs/OsuProofs/Generated/*`). This is the
  standard Aeneas trust.
  - Freshness is checked mechanically: `proofs/scripts/translation_fresh.sh` re-runs the recorded translation
    recipes and diffs the output against the committed `Generated/`.
  - The 02:25 run was identical, apart from `Source:` comment paths in the eval set.
  - Every later Rust change (D72, P1/P2/P3) was regenerated and re-checked with the same script.
- **Aeneas standard-library models** (`Vec`, slices, overflow-checked integers), plus 5 hand-written std items:
  `F64/F32::clone`, `Option::clone`, `Option::eq` and `Vec::pop`.
- **rustc/LLVM** compile the Rust as Charon saw it. The empirical check is the byte-identical regressions between
  the Rust binary and the compiled Lean model.

### 3.2 Floating point
- **Basic operations**: `+ − × ÷`, comparisons, `sqrt`, floor/ceil/trunc, conversions and saturating casts are IEEE
  round-to-nearest-even.
  - The Lean versions are kernel models, verified against .NET by `nettest`: 81.3M + 16.3M + 1.6M primitive checks
    and 10.1M library-op checks, 0 failures (docs/fidelity-evidence.md §1).
- **libm functions** (23 used: sin cos tan asin acos atan atan2 exp log log10 pow cbrt fmod and 10 f32 functions)
  are assumed equal to glibc 2.39 x86-64, in one of two ways:
  - **default Linux build**: `dlopen("libm.so.6")`. This matches only on glibc 2.39 on an FMA+AVX2 CPU, because
    glibc picks its `*_fma` variants there;
  - **vendored build** (D86; default on non-Linux, `--features vendored` on Linux): the glibc 2.39 sources of exactly
    these 23 functions are compiled in. Every multiply-add that GCC fuses in the FMA builds is written as an explicit
    `fma`, so the bits are the same on any compiler or CPU. Validation is in §6.
- **NaN**: every Rust NaN bit pattern maps to the model's single NaN. Output floats are compared up to NaN payload.
  Nothing proves that no output field can be NaN. None has been observed.
- **`parse_decimal`** (decimal text → float, used for `.osr` frames and `.osu` numbers) is a trusted primitive:
  - Rust's `dec2flt` is correctly rounded, and the model computes the correctly rounded value exactly;
  - it is partial (digits must be 0–9);
  - its inner `decimal_string` is ~3.5–5.4% of the run time (perf-plan §1), but it is not optimised, because a
    faster algorithm would change the trusted base.

### 3.3 LZMA
- One opaque function, `lzma_alone_decode`, is identified on both sides with liblzma 5.4.5:
  - by `dlopen("liblzma.so.5")` on Linux, or
  - by the vendored xz 5.4.5 decoder (4 files verbatim from Ubuntu's package, plus its two decoder patches).
- The vendored decoder was checked on 12,490 corpus `.osr` files and 32,474 truncated, corrupted or capped variants.
  Output bytes, return codes and byte counts were identical (§5.2).
- Both the model and the evaluator trust liblzma to equal lazer's managed SharpCompress `LzmaStream` on well-formed
  streams.
- `lzmaBound` (§2.2): the decoder never returns more than its cap.
- An out-of-memory error in liblzma is nondeterministic in reality but deterministic in the model. It can only turn a
  result into an error, never into a different score.

### 3.4 The CLI shell (untranslated)

`impl/osu_eval/src/main.rs` contains:
- argument parsing;
- `explicit:` schedule file parsing;
- the JSON printer;
- batch mode.

Separately, the four `text` modules (message and name strings) were excluded from translation, and `ev_tn` in the
proofs is a hand copy of the judgement type-name table.

Evidence: byte-identical output against the compiled Lean model in every regression, e.g. D54's 7,030 + 21,768 runs
and D72's 3,141 eval runs.

### 3.5 Stack and heap
- **Stack.** The evaluation runs on a thread with a 4 GiB reserved stack. That covers ~26M JSON array items, ~24M
  object members or ~11M nesting levels in the replay's score-info JSON. Real score-info JSON is ~1 KB.
  - Beyond that, and in the 8 MiB fallback when the reservation fails (main.rs:623–636), the process **aborts**. It
    never prints a wrong result.
- **Heap.** An allocation failure aborts the process. It never produces a wrong result.

---

## 4. Model ≡ lazer: the evidence (TESTED, not proved)

### 4.1 What "lazer" means here

There are three separate claims (docs/fidelity-evidence.md):
- **(A) model = harness.** The harness `oracle/` is a headless C# driver that runs lazer's own code with a
  deterministic clock.
- **(B) harness = lazer's real `ReplayPlayer`.**
- **(C) replaying the file = the live play the server scored.** §5 covers this one.

The tool's claim is (A) and (B) together.

### 4.2 Model = harness: the corpus

| comparison | cases | result | source |
|---|---|---|---|
| net floats vs .NET 10.0.13 | 81.3M + 16.3M + 1.6M primitive checks, 10.1M library-op checks, 54k `APIMod.ToMod` | 0 failures | fidelity-evidence §1 |
| beatmap decode/convert, NoMod | 1,625 real + 1,500 version-rewritten + 6,000 fuzzed + 7,000 generated maps | bit-identical | fidelity-evidence §1 |
| beatmap mods (all 48 acronyms + settings) | 48 × 400 maps, 3,478 random combos, 3,000 fuzz/gen, RD/TP 503 | bit-identical (2 skipped: lazer itself OOMs) | fidelity-evidence §1 |
| every lazer v2 score, catchup | **7,997 of 8,002** (5 are harness OOMs) | all match | fidelity-evidence §1 + "Runs 2026-10-23" |
| lazer v2 scores, perframe | 2,073 | 2,073 match (2.72M judgements) | fidelity-evidence §1 |
| the 8 never-compared server-suspicious ids × 3 schedules | 24 | 24 match | fidelity-evidence "Runs 2026-10-23" |
| lazer code coverage fuzz (covfuzz) | 400 × 3 schedules | 1,200/1,200 | fidelity-evidence §1 |
| stable replays end-to-end | ~300–600 (catchup, perframe, dense1ms, mod overrides, 485 job-mod jobs) | all match | fidelity-evidence §1, §2.1-5 |

**Sources and coverage notes:**
- The 7,417-score catchup re-run was on 2026-10-23, 00:40–00:55, with 7.9M judgements. The other 572 early scores
  were fresh oracle runs, with 609k judgements.
- Total: about 20k end-to-end jobs and ~10^8 float checks, with **no open model ≠ harness case**.
- About 3,900 of the 4,490 stable replays remain uncompared (§8).

### 4.3 Harness = lazer's real ReplayPlayer

`oracle player` runs lazer's real `ReplayPlayer` and records its step list. The same steps are then fed as an
explicit schedule to both the harness and the evaluator, and all three must agree bit for bit.

| batch | replays | result |
|---|---|---|
| 2026-10-21 (stable HD/HR/DT/NC/FL; R2R swap) | 9 | all equal |
| pilot (AL, TR, DF, BR, WD, ST, AC, SG, SO, MG, SI, FR, RD, SD, PF, DA, EZ lives) | 7 | 7/7 |
| broad (RX, AP, stable legacy-Relax RX/AP/AS, WU/WD/AS, DP, RP, GR, WG, TP, BL, TR, SI, MG, AD, BU, HD/FL/AC mixes, `--replace-mods` SD/PF, 10 random) | 43 | 43/43 (486,915 steps, 18,688 judgements) |
| fail path, separate `oracle_fail` build (D80c): 1 natural fail, ×2 with +HD+FL; 4 forced fails; 2 gate-held controls | 8 | 8/8 (115,365 steps, 5,970 judgements, incl. judgements after the fail) |

**Total: 59 real-ReplayPlayer runs on normal plays (9 + 7 + 43) plus 8 on fail paths. 0 mismatches.** (fidelity-evidence part 2 says "59 this session plus 9 from 10-21", but its own batches add up to 59 in all. The D72 regression re-ran the 58 explicit step lists from this session: 7 + 43 + 8.) These runs also test
irregular schedules: duplicate steps, fractional times and long gaps.

### 4.4 Explicit-schedule fuzz (D71(2))
- **Method.** 117 perturbed schedules were built from the 50 real-player step lists: jitter and duplicates, deleted
  windows, and truncation. That is 1.27M reference times and 43,269 judgements. Harness and evaluator were compared on
  each.
- **Result.** 115 matched, and the fuzz found **1 real mismatch (D80a)** and **1 input-contract gap (D80b)**. Both are
  fixed (§4.6).
- **After the D72 fix** (fidelity-evidence §2.3):
  - 119 cases were match before and still match;
  - both former mismatches now match;
  - the empty and decreasing lists are rejected with the harness's own messages.

### 4.5 Regressions for today's changes (D72, fidelity-evidence §2.3)
- **Corpus, new vs pre-patch `osu_eval`:** 12,724/12,724 byte-identical, and 2,099/2,099 per job.
- **Lean model vs Rust (simulation):** 6,292 runs, 0 mismatch.
- **Lean model vs Rust (end to end):** 3,141 runs, 3.46M judgements, 0 mismatch.

### 4.6 Bugs found, and how each was fixed

| found by | what | fix |
|---|---|---|
| early sim diff (10-21) | `DifficultyRange` float grouping copied from a doc summary → 1-ulp health difference | fixed. This led to the rule "model from lazer source, never from docs" |
| eval diff | BR mismatches were an evaluation-environment bug | fixed (95499c3) |
| sim diff | StrictTracking judged-slider behaviour | fixed (fidelity-evidence §1) |
| proof work (D55, 7ec6d6a; first labelled D49) | Adaptive Speed sorts end times with lazer's LINQ `Order()`, which is a **stable** sort under `double.CompareTo`. The model used an unstable IEEE `<` sort | model and Rust now use the same stable insertion sort. The difference is observable only with a −0/+0 pair. Harness 65/65 AS jobs match |
| proof work (D54) | the provability rewrite of the JSON readers overflowed the 8 MiB stack on 200k-item JSON | `osu_eval` runs on a 4 GiB-stack thread (§3.5) |
| audit pass 1, m9 | bezier/B-spline path fuel exhaustion **silently truncated** the path (lazer has no limit) | D72: it now rejects ("slider path approximation fuel exhausted") in model and Rust. Reachable only with crafted maps (≳ 25k-point zigzag segments) |
| audit pass 2, N2 | an explicit schedule containing `Infinity`: the Rust panicked, the model rejected | D72: both reject non-finite times |
| fuzz, D80a | **model bug.** A schedule that stops before the first judgement: lazer reports `total_score_without_mods` = 1,000,000, because `ScoreProcessor.Reset` keeps the perfect-play value. The model reported 0 | D72: initialised exactly as lazer does (`ScoreMax.initWithoutMods`). Repro now 1,000,000 = harness |
| fuzz, D80b | empty or decreasing explicit lists: the harness rejects, the model simulated them | D72: both reject at stage "sim" |
| real-Player fail runs, D81 | **fail-gate deviation**, see the next row | **kept, documented as a TESTED row** (D94 item 6) |
| real-Player fail runs, D81 (detail) | lazer's ReplayPlayer allows a fail when the *host frame's* clock passes the last replay frame. The model and the harness use frame-stable time. 5 of 8 constructed cases differ | Reference gating breaks the default `catchup` schedule (it fails c12184 at 11,179 instead of ~12,551), and the right semantics are unclear. Affects ReplayPlayer only, not live play or server scores. In the natural corpus only 1 replay fails under the replay gate, and it is not affected |
| user report (D83/D86) | `lazerproof` on macOS could not `dlopen libm.so.6` | vendored glibc libm + xz (§6). A fallback to the platform libm was rejected, because it would silently change bits |

### 4.7 Mods covered
- **Beatmap side:** all 48 lazer osu! mods, alone and in random combinations, with random settings including
  out-of-range values.
- **Simulation:** M0–M8, every mod family, on synthetic and real replays.
- **Real-ReplayPlayer coverage** (§4.3) includes the input, transform, rate-ramp and fail mods.
- **Thin coverage:**
  - Real-play coverage of the rare transform mods is low (GR 8, DF 4, SI 4, WG 4, TR 2 real v2 scores).
  - DA `extended_limits` and duplicate-mod lists are tested on the beatmap side only (§8).

---

## 5. Server agreement, and why it cannot reach 100%

Comparing replay playback with the stats the server recorded measures claim (C). The model is not involved: the
harness alone gives these numbers.

**Lazer scores, catchup** (data/oracle_v2/report.md, 2026-10-23 07:35, n = 8,000):

| category | count |
|---|---|
| exact (every field equal) | 5,033 (62.9%) |
| schedule-sensitive objects only (slider tails/ticks, spinner bonus) | 2,841 (35.5%) |
| integer-ms rounding | 36 (0.5%) |
| frame-dependent mods (GR, AP, …) | 23 (0.3%) |
| replay has a gap in its frames | 16 (0.2%) |
| suspicious | 51 (0.6%) |

All 51 suspicious ids were checked: **model = harness** in every case (50 bit-exact, 1 harness OOM). So none of them
is a model error (fidelity-evidence "Runs 2026-10-23").

**Why ~37% differ.** The server scored the **live** play, and the replay file is a lossy recording of it:
- **Sampling.** Live input is sampled every rendered frame, often 1000 Hz or more. The replay keeps ≤ 60 fps
  positions at integer-millisecond times. Slider-tail tracking is therefore decided on different samples: the server
  has more tail hits in 1,834 scores and fewer in 358.
- **Not reproducible by replaying.** lazer itself does not reproduce live results when it replays the file. This is
  upstream issue **ppy/osu#34016** (cited in docs/meta-review.md, 07:34). A denser schedule helps somewhat: under
  `dense1ms`, 12 of 25 catchup mismatches become exact (docs/server-agreement.md).
- **Platform.** Players on Windows, macOS or Android use a different libm, so their results can differ by an ulp.
  Screen resolution and skin also enter hit tests at the rounding level.

**Stable scores** are judged by osu!stable on the server. lazer replays stable files with the Classic mod, which
approximates stable's judging but does not reproduce it. So the stable statistics are expected to differ. lazerproof
compares 300/100/50/miss, max combo and stable accuracy for these, and prints that explanation.

### Worked examples (the two user-reported scores)

Both were re-run for this report on 2026-10-23 12:37:
- `oracle/oracle.sh run` (real lazer 2026.1005.0-lazer code, catchup), and
- `impl/target/release/osu_eval`,

both compared with `difftest/eval_diff.py`'s `compare`. Server values are from `~/.cache/lazerproof/scores/<id>.json`.

**7346217987** (lazer score, NoMod, 5774158 "The Eye Of Eternity [Greater than Gods]"):

| | lazerproof = lazer playback | server (live play) |
|---|---|---|
| total score | 986,539 | 988,924 |
| max combo | 4,090 | 4,094 |
| SliderTailHit / IgnoreMiss | 622 / 4 | 626 / 0 |
| Great / Ok | 2,838 / 18 | 2,838 / 18 |

Harness vs evaluator: **0 differences over 4,720 judgements**. The 4 differing objects are slider tails: the live
client tracked them, but at the replay's sample times the cursor or key state misses them. This is the ppy/osu#34016
class.

**7717732573** (stable score, legacy id 5088617977, HR, played by lazer with +CL; 5541387 "Glitch in My System"):

| | lazerproof = lazer playback | server (stable's own judging) |
|---|---|---|
| 300 / 100 / 50 / miss | 632 / 19 / 1 / 0 | 637 / 14 / 1 / 0 |
| max combo | 996 | 992 |
| accuracy (stable formula) | 0.979294 | 0.984407 |

Harness vs evaluator: **0 differences over 1,313 judgements**. Five circles that stable judged 300 are 100s under
lazer's Classic judging of the same file.

---

## 6. Portability

**x86-64 validation of the vendored libm and xz: DONE, 0 mismatches** (docs/proof-pipeline.md §5.2; STATE
08:0x "[d86] x86-64 validation DONE").

The comparison is bitwise, including NaN payloads, against the VM's glibc 2.39. Both gcc 13.3 and clang 18 builds
were checked.

| check | inputs |
|---|---|
| 8 unary f32 functions | every f32 bit pattern (2^32) per function per compiler |
| atan2f, powf | 3e9 random + 2e7 special each |
| 13 f64 functions | 2.5e9 random + specials each (±0, ±∞, NaN payloads, subnormals, k·π/2 ± 16 ulp, …; pow grid 2.2e7) |
| every libm call the evaluator makes on the corpus (`verify-libm` build checks each call against glibc in-process) | 20,476/20,476 runs byte-identical to the dlopen build (17.9M judgements); 2.89e9 calls, 0 mismatches |
| xz 5.4.5 decoder | 12,490 corpus `.osr` + 32,474 corrupted/truncated/capped variants: identical bytes and return codes |

**aarch64: DONE, 0 mismatches** (STATE 13:1x "[d86] DONE"; D96; docs/proof-pipeline.md §5.2). These are qemu runs
of gcc and clang builds (data/wip/d86/results_a64.jsonl):
- bit-exact, including NaN payloads: the f32 functions exhaustively, atan2f and powf on 1e9 inputs each, every f64
  function on 1e8 inputs;
- 1,486/1,486 corpus runs identical to the x86-64 build (1.73M judgements);
- x86-64 corpus regression of the clang-built vendored binary against the dlopen build: two passes so far, 1,700/1,700 and 2,239/2,239 identical (some job lists overlap; data/wip/d86/results_clang.jsonl and results_clang2.jsonl);
- the post-D72-merge build was re-checked (D96).

**Platforms:**
- x86-64 Linux (dlopen or vendored): supported, validated.
- macOS on Apple Silicon or Intel: builds with the vendored libraries automatically.
  `cargo check --target aarch64-apple-darwin` is clean. The aarch64 evidence above is from qemu. No run on real Mac
  hardware is recorded in the repo.
- Windows: not supported (MSVC lacks `__builtin_fma`). Use WSL2.

---

## 7. Performance

**Rule (D88): every optimisation is PROVED equal to the proved reference.** A Lean lemma shows `f = f_ref`, so
`osu_eval_refines` covers the fast code unchanged. There are no unproved fast paths. Build flags were changed only
where the corpus output stays byte-identical.

**How it is measured.**
- 1-core corpus: 12,776 jobs, jobs per user-second (each job is one replay evaluation).
- 200 batch: the first 200 v2 replays in one process.
- Worst map: 2147769 + 7738496475 (12,000 objects, 363k steps).
- The VM is shared at load ~4, so absolute numbers vary ±10%. Speedups are measured against a base run in the same
  session.

Sources: perf-plan = `git show worktree-agent-a4556b3114585f3dd:docs/perf-plan.md` §3–4. P2 and P3 figures are from
the STATE lines "[perf-H-P2] DONE" (8186cef) and "[perf-H-P3] DONE" (ebad67b).

| step | proof | corpus, 1 core | 200 batch | worst map | identical outputs |
|---|---|---|---|---|---|
| base (main 955bae7) | — | 21.8 replays/s | 25.6 replays/s | 0.17 replays/s (5.7–6.2 s) | — |
| + LTO, 1 codegen unit, panic=abort (3581b73) | none needed (build flags) | 24.4 (**−11% CPU**) | 26.8 | 0.20 (5.1 s) | 12,724/12,724 |
| + P1 hover candidates (only alive/previously hovered objects are re-checked) | `pf_run_with_eq : run_with = run_with_ref` (Perf/Hover*.lean, about 85 spec frame lemmas in HovFrames.lean) | 33.8 (**×1.49** vs same-session 22.6) | 35–36 | 1.6–1.8 (**×9**, 0.56–0.64 s) | 12,724/12,724 |
| P2 transforms (skip idle trackers, no clone), measured on top of the free wins alone | `update_transforms_eq_ref` (Perf/Transforms.lean) | 23.5 → 25.2 (**−7% CPU**) | 26–27 → 28.3 | unchanged | 12,724/12,724; D30 5,745 + 4,092 |
| P3 sort fast path (input already sorted → return it) | `stable_sort_by_eq_ref` (Perf/StableSort.lean, all inputs incl. NaN/±0) | 22.84 → 22.72 (within noise); **−2.4%** instructions | — | — | 12,724/12,724 |
| + P7 receptor cache in the hover update, on P1 (7e6fbe2) | Perf/RecCache.lean (receptor cached under a bit-identical key) | 37.6 | 42–43 | 1.7–1.9 | 12,724/12,724 |
| **all of the above (P1 + P7 + P2 + P3), merged with main 45f1c73, perf branch 264e9d1** | equality lemmas above; one check_all + allowlist re-record still to run | **44.6 replays/s (×2.07** vs main in the same session, 21.6) | **47–50 (×2.0** vs main, 24.6) | **1.9–2.0 (×12** vs main, 0.165) | 12,724 corpus + 2,051 perframe + 294 dense1ms, byte-identical to main |
| 4 cores | — | **PENDING** (not yet measured on a quiet machine) | | | |

**Status: PENDING MERGE.** The combined numbers are from perf-plan §4 at 264e9d1 and STATE 13:0x (orchestrator).
That branch's check_all (with the deliberate allowlist re-record) and its merge into main had not happened when this
was written, so main (headline-v2) still runs at the "base + free wins" speed.

**Correction.** The plan first estimated the sort at 9.1% of run time. That figure double-counted a recursive
function in the profiler, and the true share is ≈ 2.4% (perf-plan §1 "Correction").

**Remaining plan** (perf-plan §2.4):
- P4: per-step allocations in `update_order`, `input_order`, `alive_objects` and `lifetime_update` (~10% + malloc).
- P5: `update_state` object clones.
- P7 rest: slider-geometry caching.
- P6: CLI JSON rendering (1.7%, untranslated, byte-identity only).
- Not planned: `parse_decimal` (trusted, would change the trusted base) and liblzma (trusted C).

After P1 the profile is led by the real simulation work (`update_dho` 29%), so further gains are incremental.

---

## 8. Known gaps and next steps

**Proof**
- Regenerate the per-area PROVED/COVERED table at headline-v2 (and again after the perf merge).
- Several `PlayableBounds.simCtx` conjuncts are provable but still trusted (audit m8): top-level kinds, nested
  spinner-tick kinds, autopilot frame count, frame count < 2^32.
- Nothing proves that no output float is NaN. The rejection reason text is not covered.
- The proof-status classifier does not check what a `_refines` theorem states (m10). The PROVED/COVERED split was
  reviewed by hand in audit pass 2.

**Fidelity (model ≡ lazer)**
- The ReplayPlayer fail-gate deviation (§4.6) is kept, pending a clear semantics for catchup.
- 5 lazer scores are never compared, because the harness OOMs at 768 MB (fidelity-evidence §2.1-8). A run with
  ≥ 2 GB would close this.
- Coverage gaps:
  - ~3,900 stable replays not compared end to end;
  - few `dense1ms` runs on real lazer replays;
  - thin real play for the transform mods;
  - DA `extended_limits` and duplicate mods only on the beatmap side.
- Ranked next checks: fidelity-evidence §4 #4–#10, #12.
- The beatmap layer was last compared against lazer's C# directly on 10-21. Later checks are transitive, through
  Lean-vs-Lean and Lean-vs-Rust regressions.
- Environment variation (other resolutions, UI scale, skins) is not tested.
- Other platforms' lazer builds (different libm) are out of scope by design.

**Server agreement**: about 37% of lazer scores cannot match the live result from the replay file alone (§5). That
needs an upstream change (ppy/osu#34016), not a better evaluator. 906 server mismatches remain untriaged; the
background loop is paused (D89).

**Portability**
- No run on real macOS hardware is recorded.

**Performance**
- Merge the perf branch (264e9d1: P1/P2/P3/P7) into main after its check_all: PENDING.
- Measure 4-core throughput.
- Then P4, P5 and P7 (slider geometry).
