# Proof pipeline under the disk limit (research 2026-10-21)

This doc asks which machine-checked route from the Lean spec to a fast evaluator fits this VM. The VM has a
25 GB disk, and **6.0 GB was free when this was written** (other agents keep using more). It has 2 cores and
3.8 GB RAM. This doc refines D6 and D8.

All numbers below were measured on this VM unless they are marked *est.* The measurements came from GitHub
release assets, rust-lang dist manifests, archives streamed through `wc -c`/`tar tv` (nothing kept on disk), a
blobless sparse clone of mathlib4 v4.35.0 (since deleted), and two small Lean/Rust benchmarks.

## TL;DR ranking

| Rank | Route | Extra disk | Rust↔spec link | Verdict |
|---|---|---|---|---|
| **1** | **Fast evaluator written in Lean, proved equal to the clear spec in core Lean (no Mathlib), compiled to C. Rust is only a thin FFI/CLI shell.** | **~0 GB** (the toolchain is already installed) | The *executed code* is the proved Lean code. The Rust shell holds no logic. | **Do this now.** |
| 2 | Charon + Aeneas + Aeneas Lean lib, with a **filtered** Mathlib cache (only the ~1.1k modules Aeneas imports) | ~2.3-2.9 GB *est.* | A real Rust→Lean proof. | Feasible later if a pure-Rust core is required. Prove `aeneas(rust) = lean_fast`. |
| 3 | Charon + Aeneas with our **own Mathlib-free `Aeneas.Std` prelude** (upstream definitions copied, proofs re-done) | ~0.75 GB | Real, but the TCB adds our prelude copy and we lose the `step`/`scalar_tac` automation. | Fallback if rank 2 doesn't fit. |
| 4 | Verus plus a Lean→Verus `spec fn` printer | ~1.5 GB *est.* | The printer is unverified, and there is a semantic gap between Lean and Verus (Nat/int, uninterpreted floats). Verus has open float soundness bugs (#3073, #3136, #3194, #3172). | Not recommended. |
| 5 | Our own Rust-subset→Lean translator ("translation validation") | ~0 GB | The translator is unverified, in the TCB, and must model Rust semantics itself. | Weakest. Only as a last resort. |
| ✗ | Aeneas + **full** Mathlib (`lake exe cache get`) | **≥7.5 GB** | Real | **Does not fit.** |

## 1. Exact cost of Charon + Aeneas today

### Binaries (prebuilt, no OCaml/opam/nix needed)
- **Aeneas release** `nightly-2026.10.21-fc321a2`, asset `aeneas-linux-x86_64.tar.gz`: **161 MB** download,
  **595 MB** unpacked. Contents:
  - `aeneas` (42.5 MB)
  - `charon` + `charon-driver` (17.7 + 26.2 MB). This is the charon build that matches `charon-pin` (`de8736f7`).
  - `backends/lean` sources plus a **prebuilt `.lake/build` of the Aeneas Lean lib (436 MB)**. Of that, 171 MB is
    `setup.json`, 114 MB is `.olean.private`, 53 MB is `.c` and 46 MB is `.olean`.
  - The nested `lean-build-aeneas-x86_64-unknown-linux-gnu.tar.gz` (69 MB). It can be deleted after unpacking.
  - Binaries only (rank 3) come to ~90 MB.
- The **standalone Charon** releases (`charon-linux-x86_64.tar.gz`, 11.6 MB) are newer than the pin: nightly-2026.10.20
  is 15 commits ahead of `de8736f7`. **Use the charon that ships inside the Aeneas tarball.**
- No Docker image was found. There is a Nix flake (`nix run github:AeneasVerif/aeneas`), but Nix would cost more disk.

### Rust nightly needed by Charon
- `charon-driver` dynamically links `librustc_driver-415cc549468a4aa5.so`. That file is in the **`rustc`**
  component of `nightly-2026-09-17` (verified: the hash matches). **`rustc-dev` is NOT needed at runtime.** It is
  only needed to build charon from source.
- Unpacked sizes:

  | Component | Unpacked size |
  |---|---|
  | rustc | 425 MB |
  | rust-std | 168 MB |
  | cargo | 37 MB |
  | rust-src | 78 MB |
  | rustc-dev | 688 MB |
  | llvm-tools | ~150 MB *est.* |

- **The minimal profile is ~630 MB.** Do not let rustup auto-install the toolchain from charon's
  `rust-toolchain` file, because that adds rustc-dev, llvm-tools, rust-src, miri and 8 targets (>1.6 GB).

### Aeneas Lean library → Mathlib
- `backends/lean/lakefile.lean` contains `require mathlib @ "v4.35.0"` (rev `56a00585`), and
  `lean-toolchain` is v4.35.0, which matches our toolchain.
- 270 files and 49k lines in total. 31 distinct Mathlib imports, mostly `Data.BitVec`, `Tactic.Linarith`,
  `Ring`, `Data.Nat.Log`, `ZMod`, `Order.FixedPoints` and `Tactic.Tauto`. The Mathlib users are concentrated in
  `Std/Scalar/*`, `Std/Range`, `Tactic/{Step,Solver,ScalarTac,Simp}` and `Data/Range`.
- **Transitive closure:** 1081 of the 8624 Mathlib modules (12.5% of 98.9 MB of source). Upstream packages:
  only Batteries, Aesop and Qq. ProofWidgets, Plausible, LeanSearchClient and importGraph get cloned but are not
  imported.
- **Olean size.** Mathlib v4.35 publishes `.olean`, `.olean.server`, `.olean.private`, `.ilean` and `.trace`.
  The ratio of build output to source, measured on this toolchain's Init and Std (also module-system code), is
  **41-44x**. Applied to Mathlib:
  - **Full Mathlib: ~4.5-6 GB *est.*** Add ~1-2 GB for the `.ltar` copies in `~/.cache/mathlib` and ~0.7 GB for
    Lake's full `git clone` of mathlib4 (the repo is 506 MB plus the worktree). **That is ≥7.5 GB peak, which
    does not fit.**
  - **Filtered closure: ~0.55-0.8 GB *est.*** for Mathlib, plus ~0.2-0.4 GB for Batteries, Aesop and Qq.
- **Filtering is supported.** `lake exe cache get Mathlib.Data.BitVec Mathlib.Tactic.Linarith ...` (module names,
  globs or paths) fetches only those modules and their transitive imports. `cache get-` downloads without
  unpacking, so you can measure (`du -sh ~/.cache/mathlib`) before you commit the disk.
- **Pruning after download is not safe.** Lake treats `.ilean` and `.olean.private` as build outputs, and
  deleting them makes `lake build` try to rebuild Mathlib modules. Filter *before* the download instead, and run
  `lake exe cache clean!` afterwards to drop the `.ltar` copies.
- RAM: importing ~1.1k Mathlib modules plus Aeneas uses ~1-1.5 GB *est.* (mmapped oleans), which is fine with
  `-j1`.

### Rank-2 install steps (≈2.3-2.9 GB; run only when no other heavy job is running)
```bash
# a) binaries (161 MB download -> keep ~90 MB of binaries + the 436 MB prebuilt lib)
mkdir -p ~/tools/aeneas && cd ~/tools/aeneas
curl -LO https://github.com/AeneasVerif/aeneas/releases/download/nightly-2026.10.21-fc321a2/aeneas-linux-x86_64.tar.gz
tar xzf aeneas-linux-x86_64.tar.gz && rm aeneas-linux-x86_64.tar.gz \
  && rm backends/lean/.lake/lean-build-aeneas-x86_64-unknown-linux-gnu.tar.gz
# b) nightly, minimal (~630 MB)
rustup toolchain install nightly-2026-09-17 --profile minimal
#   run charon with: RUSTUP_TOOLCHAIN=nightly-2026-09-17 LD_LIBRARY_PATH=$(rustc +nightly-2026-09-17 --print sysroot)/lib \
#     ~/tools/aeneas/charon cargo --preset=aeneas   (rust-src (+78 MB) only if charon asks for it)
# c) proofs/ lake project: require aeneas from local path ~/tools/aeneas/backends/lean.
#    Avoid Lake's full mathlib clone: pre-create shallow clones at the manifest revs
git clone --depth 1 --branch v4.35.0 https://github.com/leanprover-community/mathlib4 proofs/.lake/packages/mathlib
#    (same for batteries/aesop/Qq/... at the revs in backends/lean/lake-manifest.json; verify `git rev-parse HEAD`)
cd proofs && lake exe cache get- Mathlib.Data.BitVec Mathlib.Tactic.Linarith ...   # the 31 seeds; check du
lake exe cache get <same args> && lake exe cache clean!
LEAN_NUM_THREADS=1 lake build -j1
```
The 31 seed modules are listed by
`grep -rhoE '^(public |meta )*import (all )?Mathlib\S*' backends/lean --include=*.lean | sort -u`.

## 2. Mathlib-free alternatives with a machine-checked link

- **Rank 3, own `Aeneas.Std` prelude.** Aeneas output only needs the *names* `Aeneas.Std.{Result, UScalar,
  IScalar, Vec, Slice, Array, ...}`. The definitions are built on core `BitVec`, and only the lemmas and tactics
  need Mathlib.
  - A prelude that copies the upstream *definitions* verbatim (about 3-5k of the 14.9k lines in `Aeneas/Std`) and
    re-proves only the lemmas we use with core `omega`/`grind`/`bv_decide` keeps the generated code's meaning
    identical to upstream.
  - Trust: Charon, Aeneas, plus a line-by-line diff of our prelude against upstream (script it).
  - Cost: binaries (~90 MB) plus the nightly (~630 MB).
  - Downside: we lose `step*`/`scalar_tac`, so the proofs are more manual.
- **Rank 4, Verus with generated specs.** A Lean meta-program would print model defs as Verus `spec fn`s.
  - The printer is unverified, and Lean `Nat`/`Int`/`Float` semantics must be mapped by hand.
  - Floats are uninterpreted in Verus, and there are open soundness bugs in its float handling.
  - In effect you get two sources of truth that are kept equal by a tool and by testing. Weaker than ranks 1-3.
  - Disk: 487 MB zip plus a pinned stable toolchain, ~1.5 GB *est.*
- **Rank 5, our own Rust-subset→Lean translator** (`syn`-based, for a restricted style we control).
  - Cheap on disk, but the translator is an unverified TCB component that must get Rust's overflow, cast and
    float semantics right.
  - The only mitigation is differential testing of the generated Lean against the Rust binary, which makes this
    no stronger than testing the Rust impl directly against the compiled Lean model.

## 3. Rank 1: the fast evaluator in Lean (the recommendation)

**Shape.**
- `model/` already has the clear spec.
- Add `OsuModel/Fast/*`: the same algorithm with arrays, indices, in-place updates and incremental state.
- Prove `Fast.eval b r s = Spec.eval b r s` with core tactics only (`simp`, `omega`, `grind`, `Array.getElem_set`
  lemmas, loop invariants via `termination_by` recursion). Mathlib is not needed: floats are never reasoned about
  numerically, they only need to be shared syntactically (see verification-tools.md), and the rest is
  Nat/Int/Array/List bookkeeping.
- Ban `implemented_by` and `@[extern]` in our code, because they break the link. The existing Net float layer's
  externs (libm) are the declared trusted base.

**Rust shell.**
- Build the Lean lib as a static lib (`lean_lib` facet `static`).
- Link `libOsuModel.a`, `libInit.a` (26 MB) and `libStd.a` (30 MB) only if they are imported. Also link
  `libleanrt.a`, `libleancpp.a`, `libgmp`, `libuv`, `libc++` and `libunwind` from `$(lean --print-prefix)/lib`.
  Never link `libLean.a` (312 MB). Keep `Lean` imports out of the evaluator modules.
- `build.rs` links them. At startup, call `lean_initialize_runtime_module()`, then
  `initialize_OsuModel(1, lean_io_mk_world())`, then `lean_io_mark_end_initialization()`.
- Call an `@[export osu_eval] def evalBytes : ByteArray → ByteArray → ... → ByteArray` (do .osu/.osr parsing in
  Lean too, so the shell contains no logic).
- Alternatively, skip Rust and ship the `lake exe` directly.

**Trust base.** The Lean kernel, the Lean compiler (LCNF → C), the runtime, clang, `Float` externs = `Float.Model`
(TestFloat-validated) and pinned glibc libm. This TCB is smaller than Aeneas's (no Charon, Aeneas or rustc
semantics) and gives a single source of truth.

**Performance (measured on this VM under load 5).** The kernel is 100 × 100k in-place updates of `a[i] = a[i]*k1 +
a[i-1]*k2 + c`:

| Variant | Time |
|---|---|
| Rust `-O` | 25-37 ms |
| Lean, `termination_by` recursion with `FloatArray.set` | 52-108 ms |
| Lean, `for`/`Id.run` loop | 50-78 ms |
| Lean, **naive version** | **2.2-3.3 s** |

So Lean is **~1.5-3x slower than Rust** when written carefully. In-place updates work: the arrays are unique,
there is no copying, and an `Array Obj` struct-update loop also ran in place (6M object checks in ~30 ms).

The naive version is ~100x slower because of a **Lean ≥4.33 pitfall**: `Float` literals compile to a *runtime*
`Float.ofScientific` call (~55 ns each, since it is now model-implemented), and `Nat.toFloat` takes ~74 ns.
`UInt64.toFloat` takes 2.4 ns. **Coding rules for `Fast`:**
- Hoist float constants into top-level `def`s. Closed terms are initialised once.
- Use `UInt64.toFloat`/`Float.ofBits`, never `Nat.toFloat`/literals inside loops.
- Prefer `USize`/`Fin`-indexed access with proofs over `a[i]!`.
- Keep arrays linear (never alias).
- Use `@[specialize]` on higher-order helpers.
- Grep the generated `.c` for `ofScientific`/`Nat_toFloat` inside hot functions as a CI check.

An osu! replay is ~10^4-10^5 frames × a few objects, so the expected cost is well under 10 ms per replay.
Parsing will dominate.

**Plan.**
1. Write the spec (in progress).
2. Write `Fast` and prove `Fast = Spec` milestone by milestone (the ratchet).
3. Add the Rust FFI shell plus difftest.
4. *Optional, later:* if a native-Rust core is wanted, write it in the Aeneas subset and prove
   `aeneas(rust) = Fast` via rank 2 or 3. `Fast` is already loop- and array-shaped, which makes that refinement
   much easier than one against the clear spec.

## 4. Trusted base of the refinement proofs (net + beatmap, 2026-10-21)

The Aeneas translation of `impl/osu_eval_core` (`net`, `beatmap` and the POC modules) is checked
against the spec in `proofs/OsuProofs`. Everything except the lines below is either generated by
Aeneas (`Generated/{Types,Funs}.lean`), part of the Aeneas library, or proved. The trusted lines are
all in `proofs/OsuProofs/Generated/{TypesExternal,FunsExternal}.lean`; each is one definition.

**Float types.** `float.F64 := OsuModel.Net.F64` (`Float`), `float.F32 := OsuModel.Net.F32`
(`Float32`). A Rust bit pattern denotes the Lean float with the same bits; every NaN pattern
denotes the model's single NaN.

**Float primitives (56, exactly the ones the translation uses).** Each `float::F64/F32` method is
identified with one `OsuModel.Net` (or `OsuModel.Beatmap.fmodF64`) function:

| Rust (`float.rs`) | Lean meaning | Why it is the same value |
|---|---|---|
| `from_bits` | `Float.ofBits` / `Float32.ofBits` | bit reinterpretation (NaN canonicalised, see above) |
| `to_bits` (**partial**: `fail` on NaN) | `toBits` | Rust sees the real NaN payload/sign, the model one NaN; proofs must show call sites never pass NaN (the Rust checks `is_nan` first where NaN can occur: `f64_round`, `f32_round`, `f64_is_inf`, `f32_is_inf`, `decimal::of_f64/of_f32`, `inverse_sqrt_fast`) |
| `is_negative` (**partial**) | `F64.isNegative` | sign bit; meaningful only on non-NaN |
| `add sub mul div neg` | `+ - * /`, `-` | IEEE RNE binary64/binary32 (SSE2 = RyuJIT), sign flip |
| `lt le eq is_nan` | `<`, `≤`, `==`, `isNaN` | IEEE predicates |
| `abs floor ceil trunc sqrt` | `F64.abs/floor/ceiling/truncate/sqrt` (F32 likewise) | kernel models, nettest-verified vs .NET (81M + 10M checks) |
| `to_f32`, `F32::to_f64` | `F64.toF32`, `F32.toF64` | `cvtsd2ss` RNE / exact |
| `from_i64`, `from_u64` (F64, F32) | `F64.ofInt`, `F32.ofInt` | one RNE rounding (Rust `as`) |
| `to_i32_sat`, `to_i64_sat`, `to_u32`, `to_u64` (F64; F32 `to_i32_sat`) | `F64.toInt32/toInt64/toUInt32/toUInt64` | Rust `as` saturates and maps NaN to 0 = .NET 9+ |
| `sin cos log atan2 pow …` (F64; F32 `sin cos atan2 …`) | `F64.sin …` (Lean core `@[extern]` libm, opaque) | both call glibc 2.39 `libm.so.6` (dlopen in Rust); or (D86, non-Linux / `--features vendored-libm`) the vendored build of the same glibc 2.39 sources, validated bit-identical (§5.2) |
| `fmod` | `OsuModel.Beatmap.fmodF64` | IEEE fmod is exact |
| `parse_decimal` (**partial**: digits must be 0..9) | `ofBitsN (Parse.decToBits fmt neg m e)` | Rust `dec2flt` is correctly rounded; the spec computes the correctly rounded value exactly |

The exact list is the `axiom` list of `Generated/FunsExternal_Template.lean` (regenerated with the
translation); `FunsExternal.lean` defines exactly those names (unused primitives are not defined).

**Std items not modelled by the Aeneas library (5).** `F64/F32::clone` (`derive(Clone)` on a
bit wrapper: identity), `Option::<T>::clone`, `<Option<T> as PartialEq>::eq`, `Vec::<T>::pop`.
Each is defined as the documented std behaviour (pure list/option operations), at the same trust
level as the Aeneas library's own std models.

**LZMA (end-to-end evaluator, `crate::lzma`, 2026-10-22; docs/rust-eval-port.md).** One opaque function:

| Rust | Lean meaning | Why it is the same value |
|---|---|---|
| `lzma::lzma_alone_decode(input, max_out) -> Result<Vec<u8>, LzmaErr>` | `OsuModel.Replay.Osr.lzmaAloneDecode` (itself an opaque `@[extern "osu_lzma_alone_decode"]`, `model/c/lzma_shim.c`) | line-by-line port of the C shim onto the same liblzma 5.4.5 (`dlopen("liblzma.so.5")`; Lean links the static library of the same package); `LzmaErr` ids = the shim's error strings |

Both the model and the implementation trust liblzma to equal lazer's managed SharpCompress `LzmaStream` on
well-formed `.lzma` streams (docs/model-eval.md "Trust boundary").

**Not trusted:** every .NET semantic (Math.Max/Min/Round/Clamp, decimal, Random, parsing,
BindableNumber, …) is ordinary translated Rust, proved against the spec.

## 5. Trusted assumptions of the end-to-end theorem (2026-10-22, D35; `proofs/OsuProofs/Eval/EndToEnd.lean`)

The top-level theorem `eval.evaluate_refines` holds for inputs satisfying `InputBounds bm osr` and `PlayableBounds bm osr opts` (the playable-pipeline size rows below; JsonFinal `eval.evaluate_refines_open`), and the named spec-run row `RunBudgetIn` (e2e2; the former row `SchedFramesIn` is a checked fact since D72). The headline is `osu_eval_refines` (Eval/JsonTop.lean, at `default_env`; allowlist proofs/scripts/headline_signature.txt).
**Allowlist change, D72 (headline-v1 ab24f87 -> D72 merge).** The changes to proofs/scripts/headline_signature.txt:
- Hypothesis `SchedFramesIn ...` is removed. The spec (`stepFramesOk`) and the Rust (`eval::step_frames_ok`) now check it and reject at stage "sim".
- The spec environment is `OsuModel.Eval.defaultEnv` itself, no longer `ev_envNorm defaultEnv`. `RunBudgetIn` and `evaluate` take it directly, because `ev_envNorm defaultEnv = defaultEnv` (M2a).
- Closure constants dropped: `SchedFramesIn`, `ev_envNorm`, `ev_cnNorm`, `simPacName` (104 -> 103).
- `evS_sched` is now `evS_sched0` (the old body plus `explicitRefsCheck`) wrapped by the `stepFramesOk` check. That gives new value hashes for `evS_sched` and `evS_sched0.*`.
- `RunBudgetIn` changes its value hash only: its `initState` takes `smax.initWithoutMods` (D80a).
- `GenPB`, `MsOk`, `StOk`, `dec_pathOk` and `PlayableBounds` also change value hash only. Their text is unchanged, but `(SliderPath.calculatePath ..).1` now projects out of an `Array Vec2 × F64 × Bool` triple (bezier fuel flag), so the same bound is stated on a differently typed term.
- Every type hash outside the headline line is unchanged.

These are *platform and input-size* hypotheses, not semantic ones: the Rust code panics (overflow / out-of-range
index) beyond them, so the refinement proof needs them; every input lazer accepts is many orders of magnitude below.
They are trusted in the sense that nothing checks them at run time (`osu_eval` could check the cheap ones up front).

| Hypothesis (`InputBounds` field) | Required by | Why it is reasonable |
|---|---|---|
| `h64 : System.Platform.numBits = 64` | slider_path (D31), schedule/sim2 (`usize` arithmetic, fuel loops 10^8), decoder (D36) | `osu_eval` is built and run only on x86-64 Linux (`usize` = 64 bit). |
| `bmLen : .osu bytes < usize::MAX` | `beatmap.text.stream_reader_decode` (D36) | a slice length is ≤ `usize::MAX` anyway; real .osu files are < 10 MB. |
| `decLines`: decoded .osu has < 2^31 − 1 lines, every line shorter than `N ≤ 2^61`, and `dec_pathOk N` (per hit-object line < 2^32 slider control points, spec `calculatePath` < 2^62 points) | decoder (D36), hit_object_parser, slider_path `of_control_points` (D31) | lazer reads lines into C# `int`-indexed lists (< 2^31); a control point takes ≥ 2 characters, so < 2^32 points is implied by lines < 8 GB; `calculatePath` emits O(points × bezier subdivisions) vertices, < 2^62 for any file that fits in memory. |
| `osrLen : .osr bytes < 2^62` | eval `osr`/`mods_json` (D35): reader positions, decompressed text and JSON string lengths (`JOk'` of mod settings) | LZMA output is bounded by `maxPayload` = 256 MiB (spec and Rust); real .osr files are < 10 MB. |
| *(derived, not assumed; 2026-10-22 json agent)* `LoadBounds.tp/dp/ep/n`: decoded timing / difficulty / effect points and hit objects < 2^31 | `get_playable_beatmap_refines` (via `ev_pbOk`) | PROVED from `decLines` (each line adds at most one point / object; the decoder invariant `dec_szOk` carried to the result: `js_decode_sizes`, Eval/JsonDecSize.lean; assembled in Eval/JsonPBounds.lean). |
| `PlayableBounds.sliderPaths` (separate top-level hypothesis `PlayableBounds bm osr opts`, Eval/E2EBase.lean; = `LoadBounds.sl`): per decoded slider < 2^32 control points and spec `calculatePath` (with `optimiseCatmull := true`) < 2^62 points | `get_playable_beatmap_refines` (`convert_beatmap` slider paths) | `decLines.dec_pathOk` bounds the same quantities for `optimiseCatmull := false` only; the catmull variant (the D49 control-point rebuild) is polynomial in the line length but not derived. |
| `PlayableBounds.decodeTime` / `.gameplay`: `GpbBounds D MS` for the decode-time mods (bitfield mods without unseeded RD/TP) and for the resolved gameplay mods; conjuncts below | `get_playable_beatmap_refines` (decode-time check and gameplay playable) | stated on spec values only (no Rust state); not derived (each depends on the per-mod hooks): |
| — `GpbBounds.st`: after each `applyAfterConversion` hook, every slider `StOk` (< 2^32 control points, path < 2^61/2^62) | `apply_after_conversion` (ST) | ST only rewrites existing sliders; sizes polynomial in the .osu size. |
| — `GpbBounds.cpe/cpt`: effect / timing point lists of the stage-2 beatmap < 2^31 | `apply_defaults` (control-point lookup indices) | no mod hook writes control points (grep: no `controlPoints :=` in the model mods); the decoded counts are derived above; a per-mod preservation lemma would make this derived. |
| — `GpbBounds.pp`: every pre-processed hit object `PathsOk` | `apply_defaults` (slider path / cumulative length) | same as `sliderPaths`, after the AC hooks. |
| — `GpbBounds.nest`: nested objects per hit object < 2^31 after `applyDefaults` | `apply_defaults` (tick / repeat generation) | nested objects = ticks/repeats, capped by lazer's own `int` indices. |
| — `GpbBounds.refl`: after each `applyToHitObject` hook, `ReflOk` (mirrored paths stay `PathsOk`) | `apply_to_hit_object` (HR/MR mirror) | mirroring preserves point counts. |
| — `GpbBounds.stk`: < 2^62 hit objects, all `PathsOk`, before stacking | `apply_stacking_all` | hit-object count is the decoded count (< 2^31). |
| — `GpbBounds.atb`: before each `applyToBeatmap` hook: `modStates` < 2^63, total nested count < 2^31 (`asCnt`), `GenOk` for every object, effect / timing lists < 2^31, `epoch` < 2^63 | `apply_to_beatmap` (AS, RD, TP generators; gen 119e5d4) | `GenOk` is the generators' well-formedness of their input objects (RD/TP read existing objects only); the counters are bounded by the number of hooks and objects. |
| `PlayableBounds.simCtx` (`ev_mkBoundsS P FS` for the spec sim playable `toSimPlayable PB` and the decoded replay frames `FS`; bridged to Rust by `ev_mkBounds_of`): frames < 2^32, hit objects < 2^32, objects + nested objects < 2^62, breaks < 2^63, per slider cumulative-length / path arrays < 2^62; per object nested < 2^32; top-level kinds circle/slider/spinner; any `AutoGen.generate P ms` output < 2^62 frames; nested objects of non-spinners are never spinner(-bonus) ticks (e2e2: `ev_ctxWF.tk` = sim8's `s8TKCtx`, lifetime_update) | `mk_ctx` and `mk_ctx_wf` (Eval/JsonMkCtxWF.lean) (`steps` frame indices, `ap_frames_of`/autogen, `mk_health_cfg`/`score_maxima`, `preceding_end_times`, `input_block_periods`) via `js_mk_ctx_full` (Eval/JsonMkCtx2.lean) | not derived: the frame count is bounded by the LZMA output (≤ `maxOut`) but the frames decoder bound is not threaded to here; the object counts follow from `GpbBounds` (< 2^31 decoded, nested < 2^31 each) but the sum over the gameplay pipeline is not carried to the adapter's output; the slider arrays are `GpbBounds.pp` after the adapter, likewise not carried; top-level kinds come from the adapter's per-HitObject-type mapping (not carried); nested kinds likewise: `CreateNestedHitObjects` (beatmap/objects.rs) generates spinner ticks only for spinners and nothing else writes a nested kind (not carried through the gameplay pipeline); the autopilot frame count is linear in the object count (a handful of frames per object) but sim2's `generate_refines` does not bound its output. |
| **`RunBudgetIn E bm osr opts sched`** (top-level hypothesis `hrb` of `osu_eval_refines`, e2e2; D67a/c, D70): for the spec context `CTX` and initial state `S0` that `evaluate` builds (`ev_simCtxOf`), `RunBudgetS CTX S0` (Sim/StepInv.lean): `(2U + Σ(nested+1) + 1)(2n+4) + objects(4n+8) + 1 < 2^64-1 ∧ (U+1)·2·10^6 ≤ 2^54`, U = `runBudgetNeed` = number of per-object updates of the whole spec run, n = custom-state cost of the visibility mods; and (D77) `e2AccBudS CTX`: `Σ(nested+1)·(1 + 2·#accuracy-challenge mods) ≤ 2^64-1` | `run_with` (step loop: transform tracker counters / sizes < `usize::MAX`, `completed_spins` headroom; init state: the `u64` `fail_triggers` counter, sim9 initLife via `e2_accR`) | machine-integer headroom, stated on real per-object costs (audit M1). Justification: the corpus check `runBudgetOkE` (Sim/StepInv.lean) over the whole corpus (catchup/perframe/dense1ms), `[runbudget] PASS` (ce6f6c9, docs/runbudget-check.md): RunBudgetS and the D77 conjunct hold on all 74940 triples (12490 real (map, replay) pairs × catchup/perframe/dense1ms × own mods / +WG); worst exact U = 14,541,791 (2147769/7738496475 dense1ms+WG), margin 145x vs 2^64−1 and 619x vs 2^54; F3 max 73002; synthetic 0.5 ms-frame worst case U = 21.3M (99x); transferred from the real context to the Rust-side `simCtxS` by `e2_runBudget_norm`. |
| *(removed, D72)* ~~`SchedFramesIn`~~ (every spec step has `frameIndex ∈ [-1, frames.size)`) | formerly `input_phase` | **no longer a hypothesis.** Deriving it from the inputs needs IEEE facts (`x + 16.67 ≠ +∞` for finite `x`) about Lean's opaque `Float`, which the kernel cannot prove. Instead the spec (`stepFramesOk`, Eval.lean) and the Rust (`eval::step_frames_ok` in `sched_ctx`) both CHECK the range after building the schedule and reject (stage "sim") otherwise. `sched_ctx_refines` proves the check, and the range follows from it. Behaviour-preserving at stage level: an index of `frames.size` (`+∞` proposed time) already made the spec reject in `replayPosition` (stage "sim"); only the reason text changes. Explicit schedules are also required to be non-empty, finite and non-decreasing (`explicitRefsCheck`, D80b/N2), so the Rust no longer panics on an `Infinity` reference. |
| *(no field; D54)* no stack exhaustion: `osu_eval` runs `real_main` on a thread with a 4 GiB reserved stack; the recursive JSON readers (`eval::mods_json` `value_f`, `array_items_rec`, `object_items_rec`) recurse once per nesting level and once per array item / object member, so their depth is bounded by the score-info / `--mods` JSON size | every refinement theorem through `mods_json` (score info in `osr.decode`, `parse_mods`); Aeneas/Lean model values, not stack usage | measured (release build, 64 MiB test thread): ~161 B of stack per array item, ~178 B per object member, ~369 B per nesting level, i.e. 4 GiB covers ~26M array items, ~24M members or ~11M nesting levels (≥ ~23 MB of JSON text in the worst case, nesting). Real score-info JSON is ~1 KB. NOT implied by `InputBounds`: `osrLen < 2^62` and `maxPayload` = 256 MiB of decompressed score info admit deeper/wider JSON (DECIDED D57: kept as this trusted row and stated in the Eval/EndToEnd.lean docstring, not as an `InputBounds` field, since the stackless Aeneas semantics would never use it; `--mods` JSON is parsed before `evaluate`, outside its theorem). Beyond the bound the process aborts (stack overflow), it never prints a wrong result. |
| *(no field; final audit M3)* **CLI shell** `impl/osu_eval/src/main.rs` (untranslated): argv parsing (option fall-through, schedule names), `explicit:` file parsing (`parse_explicit`: trim + `double_parse` per line), the JSON printer (`hex_d`, `jstr`, `acr_json`, `mods_json`, `sem_json`, `rejected_line`, stage/reason text, `playable_json`), batch mode; and for `--mods`: `parse_mods` yields < 2^61 configs | the headline `osu_eval_refines` (Eval/JsonTop.lean) is about `eval::evaluate`; `--mods` composes via `js_hopts_of_parse_mods` (every config `ev_mcOk`, proved from `parse_mods_refines`) | not translated by Aeneas; evidence is the byte-identical evaltest regressions (D30/D54). Also untranslated (excluded from the eval Charon run with `--exclude`): the four text modules `eval::text`, `eval::osr::text`, `eval::mods_json::text`, `eval::adapter::text` (message / name strings); the proofs use `ev_tn` (Eval/E2EBase.lean), a hand copy of `eval::adapter::text::type_name` (adapter.rs:289), so that table is trusted to match the Rust one. The 2^61 count: each mod config needs ≥ 2 characters of JSON and the argument is bounded by Linux `ARG_MAX` (2 MiB), so the count is < 2^20; not proved from the parser. |
| *(removed, D72; final audit M2)* ~~`Env.typeNames`~~ | — | closed by M2(a): the spec's `defaultEnv` (Eval/Env.lean `chainNode`) blanks every non-PAC chain type name, so `ev_envNorm defaultEnv = defaultEnv` (`ev_envNorm_defaultEnv`, Eval/Osr.lean), and `osu_eval_refines` is stated at `OsuModel.Eval.defaultEnv` itself. |
| *(no field; final audit m1)* **rejection reasons are not compared**: `ev_topRel` relates a Rust rejection to a spec rejection by STAGE only (D52b) | `osu_eval_refines`, `eval.evaluate_refines` | the reason text is informational; the printed reason is covered only by the evaltest regressions. |
| *(no field; final audit m2)* **floats up to NaN payload**: output float fields are compared as Lean `Float`s; FunsExternal maps every Rust NaN bit pattern to the model's single NaN (§4) | every float field of `ev_resS` | not proved NaN-free; if a NaN reached an output field, the printed `hex_d` bits could differ from evaltest's. No NaN output has been observed in the regressions. |

Further size hypotheses of the slice theorems that are discharged *inside* the proof (not trusted), e.g. vector
pushes `< usize::MAX` that follow from the input bounds, are not listed. Hypotheses found by
`grep -rn "numBits\|< 2^6\|< 2^3\|Usize.max" proofs/OsuProofs` (2026-10-22): `numBits = 64` (93 theorems: sim2 schedule,
slider_path, decoder), `< 2^31` (decoder/control-point counts, D33 `dec_cpiOk`; implied by the line bound), `< 2^32`
control points (slider_path), `< 2^61/2^62` path/line/string sizes (path_approximator, slider_path, number parsing,
D24/D26), `< Usize.max` slice lengths (D33). Sim-side ones (e.g. `refs.len * 10^8 + 4 < 2^61` of
`simulate_steps`, frame counts) will be added to `InputBounds` when those theorems are plugged into the
end-to-end proof; until then they appear inside the open `EvalAssumptions` fields.

Non-size facts the end-to-end theorem assumes (fields of `EvalAssumptions`, Eval/E2EBase.lean, besides the other
slices' callee theorems), added 2026-10-22 when `eval::osr::decode` was proved (Eval/Osr.lean):

| Fact | Kind | Why it is reasonable |
|---|---|---|
| `lzmaBound` (`ev_lzmaBound`): `lzmaAloneDecode d m = .ok r → r.size ≤ m` | trusted (LZMA boundary, §4) | the C shim allocates at most `maxOut` bytes and reports `output too large` beyond; the Rust port (`lzma_alone_decode`) is the same code on the same liblzma. Needed because the Rust maps an over-`usize::MAX` payload to an error. |
| `utf8` (`ev_utf8Fact`): `String.fromUTF8? raw = some s → s.toList = decodeUtf8 raw 0 ∧ raw does not start 00 00 FE` | PROVED (`js_ev_utf8`, Eval/JsonUtf8.lean + JsonDischarge.lean) | both are standard UTF-8 decoders; on well-formed input the replacement decoder is the identity, and `FE` is never valid UTF-8. Only used for the `readCompressedText` fast path (the Rust always uses `decode_utf8`). |
| `scoreInfo` (`ev_scoreInfoOk`): `decode_score_info` refines `decodeScoreInfo` | PROVED under `h64` (`js_ev_scoreInfo`, Eval/JsonScore.lean + JsonSize.lean + JsonDischarge.lean) | ordinary refinement obligation, to be proved. |

### 5.1 Trusted base of the Rust route (final audit m7, 2026-10-23, infra lead)

Besides the hypotheses above, the end-to-end statement "the `osu_eval` binary computes what the Lean spec says" rests on
these unchecked parts (none is a hypothesis of a Lean theorem; they are the meta-level link between the theorem and the
running binary):

| Item | Trusted for | Why it is reasonable / how it is checked |
|---|---|---|
| Lean 4.35 kernel (+ core `Float` as an opaque structure, Mathlib not used by the kernel check) | every theorem | the axiom audit (`check_all.sh`, `#print axioms`) shows only `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`/`implemented_by`/`ofReduceBool` (final audit §4). |
| Charon (nightly-2026-09-17) + Aeneas translation Rust -> LLBC -> Lean (`Generated/{,Sim,Eval}{Types,Funs}.lean`) | that the Lean functions are the semantics of `impl/osu_eval_core` | standard Aeneas trust; freshness of the committed translation is checked mechanically by `proofs/scripts/translation_fresh.sh` (re-runs the recorded recipes in a window and diffs against `Generated/`); run 2026-10-23 02:25-02:39: net+beatmap and sim+replay byte-identical, eval identical except the `Source:` comment paths. |
| Aeneas Std library models (`Vec`, `Slice`, scalar arithmetic with overflow = `fail`, `Result`) | every Rust primitive the translation calls | part of the Aeneas library (pinned in `lake-manifest.json`); the 5 hand-written std items are listed in §4. |
| rustc / LLVM code generation (release build of `osu_eval`) | that the binary runs the Rust semantics Charon saw | standard compiler trust; differential tests (D35 regression runs: Rust binary vs pinned Lean evaltest, byte-identical stdout) are the empirical check. |
| Heap exhaustion aborts the process (Rust `alloc` failure = abort, never a wrong result) | the Aeneas model treats allocation as total | an out-of-memory run prints nothing / exits non-zero; it can never print a wrong score. |
| Stack: `main.rs` runs evaluation on a thread with a 4 GiB reserved stack (D57); if that reservation fails it falls back to the default 8 MiB main-thread stack (`impl/osu_eval/src/main.rs:623-636`), where deep inputs (~200k-item arrays) overflow | recursion depth of the JSON / sim code | stack overflow aborts (guard page), never a wrong result; the 4 GiB reservation is virtual and succeeds on 64-bit Linux in practice. |
| LZMA "out of memory" is nondeterministic in reality but modelled as a deterministic result of the opaque `lzmaAloneDecode` (§4, `ev_lzmaBound`) | `.osr` decoding | the shim reports OOM as an error; the theorem then relates an error to an error. A run that hits OOM can differ from another run of the same input only by failing, never by a different score. |
| Platform: x86-64, glibc 2.39 libm via dlopen, SSE2 (D6); or vendored glibc 2.39 libm build ≡ glibc 2.39 x86-64 (D86; §5.2) | float primitives (§4) | dlopen: as documented in §4 (on an FMA+AVX2 CPU, where glibc's ifunc picks the `*_fma` builds; on older x86-64 CPUs the dlopen build gives different bits, the vendored one does not). Vendored: validated bit-identical to the VM's glibc 2.39 (validated: every f32 input for the 8 unary f32 functions, ≥2.5e9 random + special inputs per f64 and binary f32 function, 2.89e9 calls made by the evaluator on the 20,476-run corpus regression, 0 mismatches; §5.2). |

### 5.2 Vendored libm / liblzma (D86, 2026-10-23)

`impl/osu_eval_core/vendor/` holds the glibc 2.39 sources (Ubuntu 2.39-0ubuntu8.9; none of its patches touch libm) of
exactly the 23 functions `float.rs` calls, and the xz 5.4.5 `.lzma` decoder (Ubuntu 5.6.1+really5.4.5-1ubuntu0.4,
4 files verbatim plus its two decoder patches). `build.rs` compiles them (no `cc` crate; `$CC`, default `cc`) with the
pinned flags `-O2 -std=gnu11 -ffp-contract=off -fno-fast-math -fno-builtin -fno-strict-aliasing -fvisibility=hidden -fPIC`
into static libraries, exported as `lp_*`. Used always on non-Linux targets and on Linux with `--features vendored`
(`vendored-libm`, `vendored-lzma`); the default Linux build (and Charon) still dlopens the system libraries.

- **Which glibc variant**: on the VM's CPU (EPYC 9554P, FMA+AVX2) glibc's ifunc (`sysdeps/x86_64/fpu/multiarch/ifunc-fma.h`,
  `ifunc-avx-fma4.h`) selects the `-mfma -mavx2` builds of sin cos tan asin acos atan atan2 exp log pow sinf cosf expf
  logf powf; GCC contracts `a*b+c` there (GNU C default `-ffp-contract=fast`). The others (log10 cbrt fmod tanf asinf
  acosf atanf atan2f) are the generic SSE2 builds without contraction.
- **Portable reproduction**: every multiply-add GCC contracts in the FMA builds is written as an explicit
  `__builtin_fma` (found from GCC's widening_mul dump / FMA instruction counts, which match between the original
  `-ffp-contract=fast -mfma` build and the rewritten `-ffp-contract=off` build), and nothing else is contracted
  (`-ffp-contract=off`), so gcc and clang on x86-64 (with or without `-mfma`) and aarch64 compute the same operations.
  NaN results are produced explicitly in x86 form (default NaN `0xfff8…`/`0xffc00000`, first-operand quieting), and the
  SVID compat wrappers' |x|>1 results of asin/acos/asinf/acosf are reproduced, so even NaN payloads match.
- `float.rs` keeps the function-pointer table for the vendored functions (read through `black_box`), so LLVM's libcall
  simplifier cannot rewrite calls.
- **NaN payloads are unobservable anyway**: the Aeneas model of `to_bits`/`is_negative` fails on NaN (§4), so the
  refinement theorem implies no NaN reaches them; the printers canonicalise NaN (`hex64`, `dump.rs`).

**Validation (2026-10-23, against the VM's glibc 2.39 `libm.so.6`, bitwise incl. NaN payloads; gcc 13.3 and clang 18
builds of the archive build.rs produces; harness `data/wip/d86/`)**, 0 mismatches in every row:

| check | inputs |
|---|---|
| sinf cosf tanf asinf acosf atanf expf logf: every f32 bit pattern | 2^32 per function per compiler |
| atan2f powf: random pairs (uniform bit patterns + typical ranges, integer/half-integer y) + special grid | 3e9 + 2e7 per function |
| sin cos tan asin acos atan exp log log10 cbrt: random (uniform bit patterns + typical ranges) + specials (±0, ±inf, NaN payloads, subnormals, k·π/2 ±16 ulp for k ≤ 1000 and huge multiples, overflow/underflow thresholds) | 2.5e9 + 7.7e4 per function |
| atan2 pow fmod: random + special grid (pow: integer and half-integer y over all special bases, x near 1, negative x) | 2.5e9 + 2e7 per function |
| every libm call the evaluator makes on the D30 corpus set (`--features verify-libm`: each call also made on the dlopen'd glibc and compared in-process), while checking osu_eval output byte-identical to the dlopen build: v2 all 7,756, stable all 4,490, job mods 485, fuzz1/fuzz2 3,500, v2 perframe 1,552, stable perframe 499, v2 dense1ms 194, fuzz1 --dump-playable 2,000 | 20,476/20,476 runs identical; 2.89e9 calls (powf 2.57e9, pow 9.2e7, sin 6.4e7, cos 6.3e7, sinf/cosf 3.0e7 each, atan2 2.0e7, acos 1.0e7, atan2f 8.8e6, …; tan asin atan log10 cbrt tanf acosf atanf expf logf are never called on the corpus) |
| clang-build osu_eval (no verify instrumentation) vs the dlopen build, byte-identical stdout | 3,939/3,939 runs (v2 3,639, stable 300) |
| liblzma decoder (H5): 12,490 corpus `.osr` + 32,474 truncated/corrupted/`max_out` variants vs system liblzma | output bytes, return codes, total_in/out identical |

**aarch64** (`--target aarch64-unknown-linux-gnu`, gcc 13 and clang 18 builds of the same archive, run under
qemu-user; evidence for Apple Silicon): the hash of every result bit pattern over the same input streams equals the hash
of the x86-64 glibc 2.39 results, bit-exact including NaN payloads, for every f32 input of the 8 unary f32 functions
(2^32 each), 1e9 random pairs of atan2f and powf, and 1e8 random inputs of each of the 13 f64 functions. Every one of
these, for both compilers. An aarch64 osu_eval (clang build) under qemu is byte-identical to the x86-64 dlopen build on
1,486 corpus runs (v2 388 catchup + 388 perframe, stable 225, job mods 485). Not covered: Apple's own clang/libSystem
(`fma` comes from libSystem when not inlined; it is correctly rounded), and the macOS SDK compile itself (checked only
with `cargo check --target aarch64-apple-darwin`).
