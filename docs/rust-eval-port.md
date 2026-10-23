# Rust port of the end-to-end model (`OsuModel.Eval`) and `osu_eval`

`impl/osu_eval_core/src/eval/*` ports the Lean end-to-end layer function by function (Aeneas subset,
impl/STYLE.md, "Translatability" in docs/rust-sim-port.md); `impl/osu_eval` is a drop-in for the Lean
`evaltest` (same CLI, byte-identical stdout). With the Net/Beatmap port (`net`, `beatmap`) and the Sim port
(`sim`, `replay`) this gives a Rust path `.osu` + `.osr` (+ mods) + schedule → result. DECISIONS D18.

## Correspondence (spec = Lean at `1b0a176`)

| Lean | Rust |
|---|---|
| `Eval.lean` (`Schedule`, `Options`, `Rejection`, `Result`, `sameMods`, `unseededRandom`, `resolveMods`, `playableOf`, `evaluate`, `playableFor`) | `eval/mod.rs` (`EvalResult` = `Result` without the unused `playable` field) |
| `Eval/Adapter.lean` (`toSimPlayable`, `judgementOf`, …) | `eval/adapter.rs`; the `Dump` section (`playableJson`) is in the shell `osu_eval/src/main.rs` |
| `Eval/Env.lean` (`defaultEnv`, incl. the HOC ancestor chains of 95499c3; `#guard chainsConsistent`) | `eval/env.rs` (+ unit test `chains_consistent`) |
| `Replay/Osr.lean` | `eval/osr.rs` |
| `Sim/ModsJson.lean` (`SimJson.V`, `value`, `toSetting`, `parseMods`) | `eval/mods_json.rs` |
| `lzmaAloneDecode` (`@[extern]`, `model/c/lzma_shim.c`) | `lzma.rs` — **trusted**, opaque to Charon |
| `EvalTest/Main.lean` | `osu_eval/src/main.rs` (not translated) |

Representation choices:
* The reader monad `RdM = ReaderT ByteArray (StateT Nat (Except String))` → `(b: &[u8], p: usize) -> Result<(T, usize), OsrErr>`;
  the JSON parser `StateT (List Char) (Except String)` → `(s: &[u32], p) -> Result<(V, usize), JsonErr>` (the remaining
  list = `s[p..]`; the spec's list recursion in `strBody` is a loop).
* Spec `String` messages → error enums with payloads (`OsrErr`, `JsonErr`, `ModsJsonErr`, `eval::Reason`,
  `eval::Stage`); the exact texts are in untranslated `text` submodules and `osu_eval` (sim messages as in `simtest_rs`).
* `HObj.typeName : String` → `type_id` constants `adapter::T_*` (text table `adapter::text::type_name`).
* `String.toNat!` / `Int` range checks (`toSetting`, `jsonInt`): magnitude saturated at 2^64 in `u128` (only compared
  against 64-bit ranges). `String.isNat`/`toInt?` follow Lean 4.35 (`_` digit separators allowed between digits).
* `readCompressedText`'s fast path (`String.fromUTF8?` on BOM-less input) → `utf8_valid` + `decode_utf8`.
* Printing: Lean's `Float.toBits` canonicalises NaN (verified on the 4.35 runtime), so `osu_eval` prints
  NaNs as `0x7ff8000000000000` / `0x7fc00000`. JSON strings use `Lean.Json.escape`'s rules.
* Not ported: `playableOverride` / `--sim-playable` (localisation only). `osu_eval --batch LIST` (lines
  `BEATMAP OSR OUT [MODS-JSON]`) is an addition for throughput.

## Trust boundary: LZMA

`crate::lzma::lzma_alone_decode` is a line-by-line port of `osu_lzma_alone_decode` (same initial buffer size,
growth, 256 MiB bound and `lzma_ret` → message mapping) onto the same system liblzma (xz-utils 5.4.5), resolved with
`dlopen("liblzma.so.5")`/`dlsym` (as `float.rs` resolves libm): no build script and no new link dependency for the
other workspace binaries. See docs/proof-pipeline.md §4 (trusted base).

## Verification (`difftest/rust_eval_diff.py`, `impl/tools/run_eval_chunks.py`)

Lean `evaltest` pinned at `1b0a176` (`data/wip/rust-eval/evaltest_lean_1b0a176`) vs `osu_eval`: identical exit code
and stdout bytes per job (with `--dump-playable`: identical dump files too); a Lean `PANIC` on stderr is counted.
Plans `data/wip/rust-eval/plan_{a,b,c,a2,b2,a3,ab}.json`, results `results_*.jsonl` (totals: `python3 data/wip/rust-eval/agg.py …`), corpora `lists/`, `fuzz1/`, `fuzz2/`
(generator `impl/tools/mk_osr_fuzz.py`).

## Results (2026-10-22; Lean `evaltest` @`1b0a176`, `osu_eval` @bdcbd22 = `osu_eval_b.bin`, plans a/b/c @38ef04a = `osu_eval_a.bin`)

**20,268 / 20,268 Lean-vs-Rust runs byte-identical (16.4M judgements; 3,560 identical rejections), 0 mismatches,
0 Lean PANICs, 0 timeouts.**

| corpus | options | schedule | runs | identical |
|---|---|---|---|---|
| lazer v2 corpus, all 7,756 scores (`data/replays_v2`, `index_v2.sqlite`, JSON mods + settings) | own mods | catchup | 7,756 | 7,756 |
| lazer v2, every 5th | own | perframe | 1,552 | 1,552 |
| lazer v2, every 40th | own | dense1ms | 194 | 194 |
| stable replays (`data/replays`), every 3rd of 4,490 | own (bitfield + auto Classic) | catchup | 1,497 | 1,497 |
| stable, every 9th | own | perframe | 499 | 499 |
| stable, every 45th | own | dense1ms | 100 | 100 |
| stable, every 15th | `--no-classic` / `--mods [NF]` | catchup | 300 + 300 | 600 |
| job-mod lists `data/wip/end-to-end-eval/h_{m5,m6,m7,all,per7,br60}` (485 jobs: M5/M6/M7/ALL pools, each M7 mod alone, BR stress) | `--replace-mods` + job mods | catchup / perframe / dense1ms (first 100) | 485 + 485 + 100 | 1,070 |
| malformed/fuzzed `fuzz1` (2,000: container truncation/flips/ruleset/version/7-bit lengths/dates/byte-array lengths/legacy mod bits, LZMA corruption, re-encoded frame text, score-info JSON, `--mods` args, broken beatmaps) | | catchup; `--dump-playable` | 2,000 + 2,000 | 4,000 (1,150 + 1,064 identical rejections) |
| `fuzz2` (1,500 lazer replays: frame-text and score-info JSON mutations only) | | catchup / perframe | 1,500 + 1,500 | 3,000 (666 + 680 identical rejections) |

Rejection stages exercised (fuzz1+fuzz2, all schedules): replay-decode 2,710, replay-frames 395, mods 308, playable 82,
beatmap-decode 51, sim 14 (plus the 1,064 `--dump-playable` rejections).
After the Aeneas restructuring (bdcbd22), Rust-vs-Rust (`osu_eval_a.bin` vs `osu_eval_b.bin`, plan_ab): 19,783/19,783
identical (all 7,756 v2 + all 4,490 stable catchup, job-mod lists, both fuzz corpora, v2 perframe, fuzz1 dumps); plans
a2/b2/a3 ran the final binary directly.

**Speed** (`impl/tools/bench_eval.py`, same jobs, each evaluator alone in one heavy slot, shared VM at load 5–10;
oracle = `oracle.sh batch` uncached, ReadyToRun build, on the first N jobs):

| schedule | jobs | osu_eval `--batch` | osu_eval per process | Lean evaltest | oracle (lazer) |
|---|---|---|---|---|---|
| catchup | 101 v2 (oracle 30) | **8.7 replays/s** | 8.2 | 0.43 | 0.23 |
| perframe | 40 v2 (oracle 15) | **8.2** | 7.7 | 0.41 | 0.42 |
| dense1ms | 10 v2 (oracle 5) | **2.3** | 2.2 | 0.081 | 0.021 |

i.e. ~20x the Lean model and ~20–100x the oracle; the whole pipeline (beatmap decode + playable + `.osr` + LZMA +
simulation + JSON output) is ~0.1 s per replay.

## Translatability (Charon + Aeneas)

`OUT=<scratch> HEAVY_MIN_MEM_MB=3000 tools/heavy impl/charon_check.sh --start-from crate::eval --opaque crate::lzma
--exclude crate::eval::text --exclude crate::eval::osr::text --exclude crate::eval::mods_json::text --exclude
crate::eval::adapter::text` translates everything reachable from `crate::eval` (eval + the whole beatmap/sim/replay/net
code it calls) **with 0 errors and 0 `sorry`** (bdcbd22+: Funs.lean 2.3 MB, ~2,360 definitions, 280 of them `eval.*`).
Peak RSS 2.7–2.9 GB, 3–5 min — it fits a normal heavy slot (no HEAVY_EXCLUSIVE needed). Opaque items: the 57 float
primitives, `lzma.lzma_alone_decode` (the one new trusted item), and the std models already in the trusted base
(`Option::clone`, `Option::eq`, `Vec::pop`). The generated Lean is not yet type-checked against the proofs package.

Fixes needed (rule already in impl/STYLE.md §5, "update loop state unconditionally"): a loop whose only state change is
a conditional `r = true` / `r = Some(i)` on a test of a borrowed slice element (`find_first`, `has_autoplay`,
`stats_entries_ok`) → "Could not match the contexts"; written as `r = r || test(xs, i)` /
`r = first_match(test(xs, i), i)` with the test in a helper taking the slice and the index. A `derive(PartialEq)` on an
enum of the opaque `lzma` module becomes one more axiom: `LzmaErr`/`OsrErr` derive only `Clone, Copy`.
A run with `--opaque` on beatmap/sim/net (to translate eval alone) does not work: field accesses of opaque structs fail.
