# Verification tool choice (research as of 2026-10-21)

Goal: a Lean 4 model of lazer's osu! judgement/scoring that is the single source of truth, plus a fast Rust
implementation proven to refine it. The model must be bit-exact with .NET on IEEE-754 binary32/binary64
(`Vector2` positions and slider paths are float32; hit windows, score, accuracy are double).

## TL;DR recommendation

**Lean 4.35.0 spec using core `Float`/`Float32`, with transcendental functions as opaque shared primitives.
Rust impl written in the Aeneas subset; floats reach Aeneas only through a thin newtype shim (`F32`/`F64` over
`u32`/`u64` bits) whose methods are opaque to Charon and defined in Lean on top of `Float.ofBits`.
Charon+Aeneas translate the Rust to Lean, and we prove `rust_eval = spec_eval` in Lean.**

The Lean spec is also compiled natively and used as the executable model in differential testing against the
headless lazer oracle. That gives us a Plan B: if the Aeneas proofs stall, the compiled Lean model is already a
correct (if slower) evaluator, and the Rust impl falls back to being differentially tested against it.

Why:
1. **Single source of truth.** Aeneas is the only mature Rust-to-Lean pipeline. hax's recommended Lean backend
   is now Aeneas itself. Verus, Creusot and Kani would all make us restate the spec in their own language.
2. **No floating-point theorems are needed for refinement**, as long as the Rust runs the same float operations
   in the same order as the spec. We need that order for bit-exactness with .NET anyway. The proof then only
   rewrites `F64.add a b` on both sides; the float semantics are shared, not reasoned about. Float content matters
   only where the spec and the impl differ on purpose, and we avoid that.
3. **Lean 4.33+ (2026-08-10) made `Float`/`Float32` non-opaque.** They are defined through `Float.Model` (a
   UInt64 bit pattern with one canonical NaN). add, sub, mul, div, sqrt, neg, abs, comparisons, `ofScientific`
   and int conversions reduce in the kernel, and the model was validated against Berkeley TestFloat. So
   `0.1 + 0.2 != 0.3` holds by `rfl`/`decide`, and concrete test vectors can be checked in proofs without
   `native_decide`.
4. **Aeneas main now pins Lean v4.35.0 + Mathlib v4.35.0**, the toolchain we want, and ships nightly prebuilt
   binaries.

## Tool comparison

| Tool (version, date) | (a) Floats | (b) Maturity for 5-10k LoC with loops/Vec/structs | (c) Lean link | (d) Footprint | (e) Effort |
|---|---|---|---|---|---|
| **Aeneas + Charon** (nightly-2026.10.20-fc321a2; Charon pinned to rust nightly-2026-09-17) | **Not supported upstream.** Issue #828 "unsupported floats" is open; draft PR #1073 (May 2026) lowers f64/f32 to Lean `Float`/`Float32`; duckki has an f64-only branch (2026-10-19). Workaround: opaque newtype shim (below). | Good for safe Rust: structs, enums, Vec (`alloc.vec.Vec` model), slices, traits, loops. Limits: no `return` inside nested loops, no `break`/`continue` to an outer loop, no generics instantiated with `&mut`, no unsafe. Used for verified crypto (SymCrypt, ML-KEM) at this scale. | **Native.** Output is Lean 4 and proofs live next to the spec. | aeneas tarball 161 MB; Charon 12 MB plus a rust nightly with rustc-dev (~1.5 GB); Aeneas Lean lib depends on **Mathlib** (~5-6 GB oleans via `lake exe cache get`, 1.5-3 GB RAM per file). Tight but OK with swap and `-j1`. | Medium-high. The `progress`/`step` tactics automate a lot. Loops become recursive fns, so we need loop invariants as lemmas. |
| **Verus** (0.2026.10.18.7d82994, plus rolling releases) | Partial. vstd exposes `f32`/`f64` bit-level specs (`to_bits_spec`, `is_nan_spec`); add/sub/etc. are uninterpreted `add_spec` by default, with "no axioms on purpose"; `by(bit_vector)` uses SMT FP theory and is bit-precise. **Open soundness bugs found in Oct 2026:** #3073 (float ops not width-parametric, proves false), #3136 (casts), #3194 (0.0/-0.0 in patterns), #3172. | Most mature for large systems Rust (loops, Vec, structs). Fast SMT turnaround. | **None.** The spec must be duplicated as Verus `spec fn`s, so there are two sources of truth, linked only by testing. | Prebuilt zip 487 MB (includes Z3) plus a pinned stable rustup toolchain. Light on RAM. | Medium. Structural float refinement is easy with uninterpreted ops, but the Lean-to-Verus gap stays. |
| **hax** (cargo-hax v0.4.2, 2026-10-01) | Not documented for Lean. | The legacy Lean backend is deprecated; hax's recommended Lean backend runs through Charon/Aeneas, so same limits. F* backend is mature (crypto). | Via Aeneas. | OCaml + Rust + node. | Same as Aeneas. No reason to add this layer. |
| **Creusot** (v0.14.0, 2026-10-12) | Yes: `f32`/`f64` map to Why3 `ieee_float` (RNE add/sub/mul/div, comparisons), SMT FP theory (Z3/CVC5). Bit-precise for basic ops. | Mature-ish, good for loops/Vec via prophecies. | **None** (Why3/Coma). | opam + Why3 + solvers (~1-2 GB). | Medium; same duplication problem as Verus. |
| **Prusti** | Little float support. | **Effectively inactive** (repo moved; no active Rust-toolchain tracking). | None. | Viper + JVM. | Not viable. |
| **Kani** (0.68.0, 2026-09-16) | **Bit-precise** IEEE via CBMC's float encoding; transcendental functions are stubbed or over-approximated. | Bounded model checking: great for bounded harnesses, not for unbounded loop proofs over whole replays. | None. | `cargo install --locked kani-verifier && cargo kani setup` (~1 GB). Bit-blasting floats is RAM hungry. | Low per harness. **Use as a supplement** (shim and helper equivalence on all small inputs), not as the main tool. |
| **Lean-only (compile the spec)** | Lean `Float` compiles to C `double` (`Float32` to `float`) on SSE2, so IEEE basic ops are bit-exact on x86-64. Logic uses `Float.Model`. | Lean compiled code with `Array`/structs is decent (estimate 2-10x slower than Rust, still ms per replay). | It *is* the spec. | elan + toolchain ~1 GB; no Mathlib needed. | **Zero refinement proof.** You trust the Lean compiler and the compiled-`Float` = `Float.Model` link (validated by TestFloat). |
| Lean-to-Rust codegen | No general tool exists. AMO-Lean is crypto-specific. | n/a | n/a | n/a | Not viable. |

## Floating point: how faithful is each layer?

### Lean 4 core `Float` (4.33+; we pin 4.35.0)
- **Model-defined (kernel-reducible):** add, sub, mul, div, sqrt, neg, abs, `isNaN`/`isInf`/`isFinite`, compare/beq/lt/le,
  `ofScientific` (correctly rounded since #14110), `ofBits`, `toUInt64`-style conversions, and the same set for `Float32`.
- **Still opaque (no kernel reduction):** `floor`, `ceil`, `round`, **`Float.toFloat32` and `Float32.toFloat`**, `exp`,
  `log`, `pow`, `sin`, `cos`, `atan2`, `acos`, and so on.
- **Caveats:**
  - `Float.round` is C `round`, which rounds half away from zero. That is **not** .NET `Math.Round` (half to even).
    Define `roundHalfEven` ourselves.
  - The model has a single canonical NaN, so NaN payloads are not modelled. Lazer should never depend on NaN
    payloads; test for NaN appearing at all.
  - `DecidableEq` compares bit patterns, while `==` is IEEE equality.
- **Project rule.** We define our own `floor`, `ceil`, `truncate`, `roundHalfEven`, and the binary64↔binary32
  conversions on top of `Float.toBits`/`ofBits` and integer arithmetic. They must be kernel-reducible and are
  tested against hardware on TestFloat-style vectors. Optionally, prove them against FloatSpec. All conversions go
  through a single `F32`/`F64` primitive layer in the spec.
- **Libraries, if we ever need real-valued theorems:**
  - **FloatSpec** (Beneficial-AI-Foundation, v0.7.0, Lean v4.29): a Flocq port with no `sorry`, but its roadmap
    still lists open items, plus an IEEE754 layer and a `PrimFloat` bridge.
  - **FloatLib** (lean-dojo/FloatLib, arXiv 2609.19352, Sept 2026): IEEE binary/decimal/posit/P3109 formats,
    backends proved equal to an encoded spec, 102M TestFloat cases with no differences.
  - **FLoPS** (P3109 only) and **flean** (early stage).
  - Mathlib itself has no IEEE binary64.
  - We do **not** need any of these for the refinement proof (see the TL;DR).

### .NET (what the spec must mirror)
- **Basic ops.** RyuJIT on x64 uses scalar SSE2: no x87 excess precision, and no automatic FMA contraction (only an
  explicit `Math.FusedMultiplyAdd`). float32 arithmetic stays in float32, so `float op float` rounds to binary32.
  The C# rules decide when an expression is promoted to double, so the spec must reproduce the implicit
  conversions exactly.
- **`System.Numerics.Vector2`/osuTK `Vector2`.** SIMD lowering of `Dot`/`Length` must be checked. A 2-lane
  dot product is one rounded mul per lane plus one rounded add, the same as scalar, but confirm it with tests.
- **`Math.Round(double)`** rounds half to even (Rust: `f64::round_ties_even`). Lazer uses `(long)Math.Round(...)`
  for total score.
- **float to int casts.** These have been saturating on x86/x64 since **.NET 9** (NaN goes to 0), matching Rust `as`.
  Lazer targets net10.0. Confirm it with oracle tests.
- **Transcendentals** (`Math.Pow/Sin/Cos/Atan2/Acos/Exp/Log`, `MathF.*`) call the **platform libm** (glibc on
  Linux) through the CoreCLR PAL. They are not correctly rounded, and results can change between glibc versions:
  glibc 2.41+ imported CORE-MATH correctly-rounded versions of several binary32 functions. Uses in the judgement
  path found so far:
  - `Math.Pow(combo, COMBO_EXPONENT)` and `Math.Pow(acc, 5)` in `ScoreProcessor`.
  - `Math.Acos` in `SliderPath` (circular-arc subpoint count).
  - `Atan2`, `Sin`, `Cos` in osu-framework `PathApproximator` (circular arcs).
  - `MathF.Atan2` in `SpinnerRotationTracker`, plus `Interpolation.Damp`, which is a pow.
  - Mods: Random (`Math.Exp`) and Target Practice (`MathF` trig).
- **Handling transcendentals in the model.** Declare them in Lean as opaque primitives (`opaque libm_pow : Float →
  Float → Float`, and so on), call the same glibc functions from Rust (`f64::powf`, `f32::atan2` lower to libm on
  linux-gnu), and **pin the glibc version** used by both the oracle and our binaries (record it). This is a small,
  explicit trusted base.
- **Later hardening (optional).** Port glibc's exact algorithms for the few functions used (pow, atan2, sin, cos,
  acos, exp, and their f variants) into the spec using only basic ops. Then they become kernel-reducible and
  platform-independent; check them against glibc on 10^9 random inputs plus the worst cases.

### Rust
- On x86-64, `f32`/`f64` basic ops are IEEE (SSE2), LLVM never contracts to FMA without fast-math flags, and
  `as` casts saturate.
- Never use `mul_add`, fast-math or `-C target-cpu` tricks that change semantics, and don't let any crate reorder
  arithmetic.

### How to argue ".NET semantics = model"
It cannot be proved formally, because there is no formal semantics of RyuJIT. The chain is:
1. **The basic ops all are hardware IEEE (SSE2).** Lean `Float.Model` = IEEE is validated by TestFloat; .NET
   lowers to the same SSE2 instructions. Spot-check the JIT disassembly (`DOTNET_JitDisasm`) of hot functions
   such as `PathApproximator` and `HitWindows`.
2. **The spec reproduces the C# expression structure exactly.** Same order, same float/double promotion points,
   same `Math.Round` mode. Review it line by line against the source, citing file and line in comments.
3. **Differential testing.**
   - Primitive level: run each spec helper compiled (`lean --run` / `lake exe`) against tiny C# snippets on random
     and edge inputs (subnormals, ±0, halfway cases, NaN/inf).
   - Whole-pipeline level: compare against the headless lazer oracle, checking slider path points bit-for-bit
     (`BitConverter.DoubleToInt64Bits`) and judgement times, not just final scores.
4. **Pin the transcendental base** (the glibc version) and test it.

## Concrete install plan (do not run concurrently with dotnet/cargo builds)

```bash
# 1. Lean (the spec; no Mathlib needed for model/ unless we add proofs that import Aeneas)
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:v4.35.0
#   model/lean-toolchain: leanprover/lean4:v4.35.0   (v4.36.0-rc1 exists; stay on 4.35.0 to match Aeneas/Mathlib)

# 2. Rust stable for impl/ (pin in impl/rust-toolchain.toml), plus the nightly Charon needs
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal
rustup toolchain install nightly-2026-09-17 --component rustc-dev,llvm-tools,rust-src

# 3. Aeneas + Charon prebuilt (pick a matching nightly pair; Aeneas's charon-pin names commit de8736f7)
mkdir -p ~/tools/aeneas && cd ~/tools/aeneas
curl -LO https://github.com/AeneasVerif/aeneas/releases/download/nightly-2026.10.20-fc321a2/aeneas-linux-x86_64.tar.gz
curl -LO https://github.com/AeneasVerif/charon/releases/download/nightly-2026.10.20/charon-linux-x86_64.tar.gz
#   If the prebuilt charon != charon-pin, build from source instead:
#   git clone https://github.com/AeneasVerif/aeneas && cd aeneas && make setup-charon   (needs opam/OCaml 5.3 for aeneas itself)
#   usage: (cd impl && charon cargo --preset=aeneas) ; aeneas -backend lean impl.llbc -dest proofs/Generated

# 4. Proof project (proofs/): requires Aeneas Lean lib (pulls Mathlib v4.35.0)
#   lakefile: require aeneas from git "https://github.com/AeneasVerif/aeneas.git" @ "fc321a2" / "backends/lean"
lake exe cache get        # Mathlib oleans (~5-6 GB disk). Aeneas also publishes lean-build-aeneas-x86_64-*.tar.gz (69 MB)
LEAN_NUM_THREADS=1 lake build -j1   # stay under 3.8 GB RAM

# Optional supplements
cargo install --locked kani-verifier && cargo kani setup        # bounded checks of shim/helpers
# Verus (fallback only): https://github.com/verus-lang/verus/releases/tag/release/0.2026.10.18.7d82994 (x86-linux zip, 487 MB)
```

Disk budget: about 9 GB is free now. Mathlib (~6 GB) plus the nightly toolchain (~1.5 GB) is the big item, so
defer step 4 until the spec and impl exist, and prune `~/.nuget`/`obj` first if needed.

## Rust coding rules (to stay inside the Aeneas subset)
- Floats only through `struct F64(u64)` / `struct F32(u32)` with `#[inline(always)]` methods (`add`, `mul`, `sqrt`,
  `to_f32`, `round_half_even`, `libm_pow`, ...). Their bodies use native `f64::from_bits(..) + ..`, are marked
  opaque to Charon (`#[charon::opaque]`, or kept in a separate non-extracted module declared external), and are
  given Lean definitions in `proofs/Shim.lean`: `F64.add a b := ⟨(Float.ofBits a.0 + Float.ofBits b.0).toBits⟩`.
  - Trusted surface: about 30 one-line functions, each tested exhaustively or randomly against the native op,
    and with Kani where feasible.
  - **NaN caveat:** Lean's `toBits` canonicalises NaN, but hardware doesn't. Avoid carrying NaN bit patterns.
    Assert or flag any NaN in the oracle.
  - Once Aeneas merges native f64/f32 support (PR #1073 line of work), switch to plain `f64` and drop the shim.
- No `return`/`break` out of nested loops: restructure them as helper functions. No `&mut` in generic
  instantiations. No unsafe, no iterators that Aeneas lacks models for. Prefer `while` with explicit indices
  over `Vec`/slices.
- Keep each Rust function in 1:1 correspondence with a spec function where possible. Equality proofs then become
  `simp [spec_fn, rust_fn]` plus loop-induction lemmas.

## Known lazer discrepancies / test hints from other projects
- **SLAM** (github.com/sheynor43/SLAM, Rust lazer replay simulator; PR #76, merged 2026-10-11):
  - Replay frames are recorded at 60 Hz (`ReplayRecorder.RecordFrameRate`) and rounded to whole ms by
    `LegacyScoreEncoder`.
  - Stepping only on frames skips 36 ms slider-tail leniency windows (23/49 replays matched). Stepping 1 ms
    between frames, matching live `DEFAULT_ACTIVE_HZ = 1000`, gave 40/49 exact matches; the remaining 8 differed
    only in tail/tick/repeat/spinner-bonus counts.
  - Known divergence: a press exactly at an object's start time, where the hit policy flips.
  - Their target was the *live* score stored in the .osr. **Our target is lazer's replay playback through the
    headless oracle, which is deterministic.** Expect the stored live stats to differ sometimes. That is a known
    lazer behaviour (ppy/osu #23166, #26534, #25405, #12760), not a model bug.
- **The osu! wiki** (lazer feature comparison) documents lazer-specific rules. Each is an edge-case test target:
  - Slider head accuracy; a missed head gives a whole-slider miss.
  - Early click: tracking starts immediately. Late click: passed ticks/repeats count as hit.
  - Tail tracking can happen anywhere in the last 36 ms.
  - Spinner RPM cap scales with OD (250/380/430 RPM at OD 0/5/10).
  - Lenient notelock.
  - Hit-window edges use `<=`, and the edge outcome depends on rounding of the hit error.
  - Classic mod reverts notelock, slider head accuracy, and head/end leniency.
- **circleguard/circlecore** model stable judgement only (sliderbreaks not implemented). They are not useful as a
  lazer reference.
- Fuzz targets suggested by the above:
  - Presses at exactly `start ± window` and at `start` itself.
  - Frames straddling `tail - 36 ms`.
  - Very fast/short sliders.
  - Repeated identical-time frames.
  - Spinners at the RPM cap.
  - Circular-arc sliders with near-collinear control points (`Acos` subpoint count, B-spline fallback).
  - DT/HT rates (frame time scaling in double).

## Sources
- Lean reference, Floating-Point Numbers (v4.35.0): https://lean-lang.org/doc/reference/4.35.0/Basic-Types/Floating-Point-Numbers/
- Lean v4.33.0 release notes (Float non-opaque, #14110, #14180, #14181): https://lean-lang.org/doc/reference/4.35.0/releases/v4.33.0/
- Aeneas: https://github.com/AeneasVerif/aeneas, float issue https://github.com/AeneasVerif/aeneas/issues/828, draft PR https://github.com/AeneasVerif/aeneas/pull/1073
- Verus float: https://github.com/verus-lang/verus/blob/main/source/vstd/float.rs, examples/float.rs; issues #3073 #3136 #3172 #3194; PRs #3092 #3207
- Creusot float prelude: https://github.com/creusot-rs/creusot/blob/master/prelude-generator/float.coma
- hax Lean backend: https://hax.cryspen.com/manual/lean/
- FloatSpec: https://reservoir.lean-lang.org/@Beneficial-AI-Foundation/FloatSpec ; FloatLib: https://arxiv.org/abs/2609.19352
- SLAM PR #76: https://github.com/sheynor43/SLAM/pull/76
- osu! wiki lazer feature comparison: https://osu.ppy.sh/wiki/en/Client/Release_stream/Lazer/Feature_comparison
