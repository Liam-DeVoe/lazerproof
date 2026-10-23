# Proof pipeline proof of concept: Rust → Charon → Aeneas → Lean, proved against the spec (D12)

Status (2026-10-21): **it works end to end**. Three representative Rust functions were translated by
Charon+Aeneas, and each was proved in Lean to refine its `OsuModel` spec function. The proofs are
machine-checked with no `sorry` and no new axioms. The only trusted additions are the 18 one-line float
primitive identifications (§3). The same Rust compiles to plain SSE code and agrees with the compiled
Lean spec on random inputs (§6).

Layout:

| Path | What |
|---|---|
| `impl/` | Cargo workspace. `osu_eval_core` (translated) + `osu_eval_bench` (difftest generator / bench, not translated). |
| `impl/charon.sh` | Runs Charon, then Aeneas, and writes `proofs/OsuProofs/Generated/{Types,Funs}.lean` (+ templates). |
| `proofs/` | Separate Lean package `OsuProofs`: requires `aeneas` (path, release bundle) and `OsuModel` (`../model`). |
| `proofs/OsuProofs/Generated/` | Aeneas output (`Types.lean`, `Funs.lean`, regenerated) + hand-written `TypesExternal.lean`, `FunsExternal.lean` (the trusted primitive layer). |
| `proofs/OsuProofs/{Prims,HitWindows,Slider,Schedule}.lean` | Aeneas-side refinement proofs. |
| `proofs/OsuProofs/Spec/{Slider,Schedule}.lean` | Spec-side normal forms (import only `OsuModel`, so they check in ~20 s). |
| `proofs/PocSpec/Main.lean` | `pocspec` exe: differential checker using the compiled spec. |
| `proofs/scripts/check_all.sh` | Fast iteration: concatenates the Aeneas-side proofs into one file, so the slow import is paid once. |

## 1. Install (exact steps and versions)

Versions:
- **Aeneas** release `nightly-2026.10.21-fc321a2`, asset `aeneas-linux-x86_64.tar.gz`. It contains its matching `charon`/`charon-driver`.
- **Rust** `nightly-2026-09-17` (rustc 1.100.0-nightly 923c95cdf), **minimal profile**. Only the `rustc` component is needed by `charon-driver` (`librustc_driver-*.so`); `rustc-dev` is not.
- Lean `v4.35.0` (already installed) and Mathlib `v4.35.0` (rev `56a00585`), via a filtered cache.

```bash
# a) Aeneas bundle (161 MB download, 517 MB kept)
mkdir -p ~/tools/aeneas && cd ~/tools/aeneas
curl -sL -o /tmp/aeneas.tgz https://github.com/AeneasVerif/aeneas/releases/download/nightly-2026.10.21-fc321a2/aeneas-linux-x86_64.tar.gz
tar xzf /tmp/aeneas.tgz && rm /tmp/aeneas.tgz backends/lean/.lake/lean-build-aeneas-x86_64-unknown-linux-gnu.tar.gz
# b) nightly, minimal (602 MB). NEVER let rustup read ~/tools/aeneas/rust-toolchain (adds rustc-dev, miri, 8 targets).
~/.cargo/bin/rustup toolchain install nightly-2026-09-17 --profile minimal
# c) proofs/ package: lakefile.toml requires aeneas (path ~/tools/aeneas/backends/lean) + OsuModel (path ../model).
#    lake-manifest.json is written by hand: the two path deps + aeneas's manifest entries (inherited=true).
#    The git deps are pre-created as SHALLOW clones at the manifest revisions (mathlib clone: 153 MB instead of ~700 MB):
cd ~/lazerproof/proofs/.lake/packages   # for each package in aeneas's lake-manifest.json:
git init -q $name && git -C $name remote add origin $url && git -C $name fetch -q --depth 1 origin $rev && git -C $name checkout -q FETCH_HEAD
# d) filtered Mathlib cache: only the 31 Mathlib modules Aeneas imports (+ their closure: 1474 files, 101 MB of .ltar)
cd ~/lazerproof/proofs
SEEDS=$(grep -rhoE '^(public |meta )*import (all )?Mathlib\S*' ~/tools/aeneas/backends/lean --include=*.lean | sed -E 's/.*import (all )?//' | sort -u)
lake exe cache get- $SEEDS     # download only (builds the `cache` exe once, ~2 min)
lake exe cache get  $SEEDS     # unpack
rm -rf ~/.cache/mathlib proofs/.lake/packages/mathlib/.lake/build/bin   # .ltar copies + the cache exe (216 MB)
# e) 4 Batteries modules that Aeneas imports directly are not in the Mathlib closure; build them (seconds, NOT Mathlib):
lake build Batteries.Data.BitVec.Basic Batteries.Data.Fin.OfBits Batteries.Data.Int Batteries.Data.BitVec.Lemmas
lake build --no-build Aeneas   # must succeed: proves nothing else (Mathlib/Aeneas) needs rebuilding
# f) optional disk saving: delete Mathlib .lean sources that have no .olean (outside the closure): 117 MB -> 17 MB.
#    (lake hashes only the sources of modules it builds or checks.)
```

Things that did **not** work or must not be done:
- Deleting `mathlib/.lake/build/ir` (the `.c` files, 137 MB). Aeneas's `AeneasMeta` uses `precompileModules`, so lake then wants to rebuild the Mathlib modules in its import chain.
- Deleting the prebuilt Aeneas `ir/` (setup.json + .c) triggers a full rebuild of Aeneas.
- `lake build --no-build <target>` is the safe way to check whether lake would compile Mathlib.

### Disk and RAM

| Item | Disk |
|---|---|
| `~/tools/aeneas` (binaries 86 MB + prebuilt Lean lib 431 MB) | 517 MB |
| `~/.rustup/toolchains/nightly-2026-09-17` (minimal) | 602 MB |
| `proofs/.lake` (mathlib 1.1 GB incl. 0.9 GB oleans, aesop 134 MB, batteries 82 MB, rest) | 1.4 GB |
| `impl/target` | 6 MB |
| **Total** | **≈ 2.5 GB** |

Free disk went from 6.7 GB to 4.0 GB at the low point and was 4.5 GB after cleanup.

RAM: `import Aeneas` maps about 1.2-1.4 GB of oleans (max RSS 1.4 GB, mostly file-backed and reclaimable).
- Each proof file needed 1.2-2.0 GB RSS.
- On this VM, under load average 6-12 from the other agents' batches, the import alone took **150-250 s**. CPU time was only about 10 s; the rest was page faults.
- Practical consequences:
  - Build the proofs with `-j1`, and never next to another Lean/dotnet job.
  - Iterate with `scripts/check_all.sh`, which pays the import once for all proofs (one round ≈ 4-6 min).
  - Put spec-side lemmas in files that do not import Aeneas (`Spec/*.lean` check in 5-30 s).

## 2. Rust crate (`impl/osu_eval_core`)

| Rust | Spec | Kind |
|---|---|---|
| `hit_windows::difficulty_range1/difficulty_range/osu_hit_windows` | `OsuModel.Beatmap.difficultyRange1/difficultyRange/osuHitWindows` | (i) pure numeric |
| `hit_windows::result_for` | `OsuModel.Sim.HitWindows.resultFor` | (i) |
| `net::{max,min,clamp}` | `OsuModel.Net.F64.{max,min,clamp}` (.NET `Math.Max/Min/Clamp`) | helpers, *proved*, not trusted |
| `slider::cumulative_lengths` (+ `vsub`, `length`) | `OsuModel.Beatmap.SliderPath.calculateLength` (no `ExpectedDistance`) | (ii) loop over a slice, building a `Vec` |
| `schedule::simulate_steps` (+ `fsc_step`, `frame_time`) | `OsuModel.Sim.simulateSteps` (FSC + replay handler, D9) | (iii) state machine: nested loops, `break`, fuel, `i64` index, `Option` |

`charon cargo --preset=aeneas --opaque 'crate::float'` followed by
`aeneas -backend lean -use-lean-modules false -split-files` runs in about 5 s.

## 3. Floats: the trusted primitive layer

`impl/osu_eval_core/src/float.rs` defines `#[repr(transparent)] struct F64(u64)` / `F32(u32)` holding raw bits, with
`#[inline(always)]` methods.
- The whole module is opaque to Charon (`--opaque crate::float`). Aeneas emits `axiom`s only for the
  primitives that are actually used, in `FunsExternal_Template.lean`.
- We replace those with definitions in `Generated/TypesExternal.lean` and `Generated/FunsExternal.lean`.
- **The trusted base is exactly these lines**:

| Rust primitive | Lean definition (spec function) | Justification |
|---|---|---|
| type `F64` / `F32` | `OsuModel.Net.F64 = Float` / `F32 = Float32` | bit patterns; every Rust NaN ↦ the model's single NaN |
| `F64::from_bits(b)` | `Float.ofBits b` | canonicalises NaN, consistent with the above |
| `F64::{add,sub,mul,div}` | `a + b`, `a - b`, `a * b`, `a / b` (`Float.Model`) | SSE2 `addsd`… = RyuJIT's; TestFloat-validated model |
| `F64::{lt,le,eq}` | `decide (a < b)`, `decide (a ≤ b)`, `a == b` | IEEE predicates |
| `F64::is_nan` | `F64.isNaN` | |
| `F64::is_negative` | `if isNaN a then fail .panic else ok (F64.isNegative a)` | **partial**: only identified on non-NaN inputs (Rust sees the real NaN sign bit). The proofs must show that call sites never pass NaN, and `net::max/min` do show it. |
| `F64::abs` | `F64.abs` (clear sign bit) | |
| `F64::floor` | `F64.floor` (kernel model, nettest-verified vs .NET) | Rust `f64::floor` = libm `floor` or `roundsd` |
| `F64::sqrt` | `F64.sqrt` (kernel model) | `sqrtsd` |
| `F64::to_f32` | `F64.toF32` | `cvtsd2ss` RNE |
| `F32::{add,sub,mul}` | `a + b`, `a - b`, `a * b` on `Float32` | SSE `addss`… |
| `F32::to_f64` | `F32.toF64` | exact |

Rules followed by the crate:
- Every non-trivial .NET semantic (Max/Min/Clamp, …) is written in ordinary Rust over these primitives and **proved**.
- Float constants are `const K: F64 = F64::from_bits(0x…)`. Each constant is proved equal to the spec literal by
  `decide +kernel` (Lean's float model is kernel-reducible), e.g. `CATCHUP_THRESHOLD = sixtyFrameTime * F32.toF64 1.2`.
- To validate the trusted lines, extend `model/nettest` to call the Rust primitives too. They map to the same instructions, and nettest already checks the Lean models against .NET with 81M cases.

## 4. Proofs: what is proved, and how much effort it took

Each main theorem is stated as an equation `impl … = ok (…spec…)`. The proofs use the generated
code as is; no annotations were added on the Rust side.

| Theorem (file) | Statement (simplified) | Effort |
|---|---|---|
| `difficulty_range_refines`, `difficulty_range1_refines`, `osu_hit_windows_refines`, `result_for_refines` (HitWindows.lean) | `= ok spec` (HitWindows via field-wise map; HitResult via `hrSpec`) | ~1 h incl. learning; each proof 2-4 lines (`unfold; by_cases; simp`) |
| `max_refines`, `min_refines`, `clamp_refines` (Prims.lean) | `net.max a b = ok (F64.max a b)` etc. Needs `beq_not_nan_*` (IEEE `==` ⇒ not NaN, proved from Lean's `Float.Model`) for the partial `is_negative` | ~30 min |
| `cumulative_lengths_refines` (Slider.lean + Spec/Slider.lean) | `∃ v, impl path opt = ok (v, sl.calculatedLength) ∧ v.val = sl.cumulativeLength.toList` where `sl = calculateLength sp (path.map vSpec) opt`, `sp.expectedDistance = none` | ~2 h. Spec side: `forIn` over `[0:n]` → `List.foldl` (core simp lemmas) + `List.foldl_hom`. Impl side: induction on the remaining length; bounds by `omega` |
| `simulate_steps_refines` (Schedule.lean + Spec/Schedule.lean) | `∃ v, impl refs frames gst = ok v ∧ v.val.map stepSpec = simulateSteps refs frames gst` under `numBits = 64` and `refs.length * 10^8 + 4 < 2^61` | ~4 h. Spec side: `while`+`break` → structural recursion `inner` (via `Lean.Loop.forIn_eq_of_monadTail`, Lean ≥ 4.3x) + `Array.forIn_pure_yield_eq_foldl`. Impl side: `fsc_step` by case split, then inner/outer loop inductions with the invariant `|idx| ≤ 1 + steps.length` |

### How loops, overflow and panics show up

- **Loops.** Aeneas turns every Rust `while` into `loop body state`, where `body : state → Result (ControlFlow state result)` and
  `loop` is a `partial_fixpoint`. So there is no termination proof at translation time; *total correctness is proved* by our induction.
  - Nested loops become separate `…_loop0_loop0` functions.
  - The inner `break` is `done`.
  - We prove a one-line unfolding lemma per loop (`cum_loop_unfold` etc.) that keeps the recursive call folded. If you `simp` with the body equation directly, it also unfolds the body under the `loop` binder and later `rw`s fail.
- **Overflow and panics.** Every `+ - ` on `usize/i64/u32`, every slice index and every `Vec::push` is a `Result` that fails on
  overflow or out-of-bounds (`Vec.push` fails at `Usize.max`).
  - Each refinement theorem therefore *proves absence of panics*, under explicit size hypotheses.
  - The scalar-arith lemmas come from Aeneas (`I64.add_spec`, …). We wrap them as equations (`i64_add_one`, `usize_add_one`, `push_eq`, `index_eq` in Prims.lean) and discharge their side conditions with `omega`.
- **Platform.** `Usize.max` is platform-abstract (32 or 64 bit), so `i as usize` and large `Vec`s need the hypothesis `System.Platform.numBits = 64`.
- **The spec's `fuel`.** `simulateSteps` loops at most 10^8 times per reference. The Rust copies that bound exactly (`FUEL: u32`). The theorem needs `refs.length * 10^8 < 2^61` only so that the counters provably cannot overflow.

## 5. Friction points (and the fix used)

1. **Field named `ok`** (`HitWindows.ok`) breaks the generated Lean: inside the struct's namespace `ok self` resolves to the field
   projection. We renamed the Rust field to `ok_`. Rule: never name Rust fields or functions `ok`, `fail`, `div`, `loop`, `bind`.
2. **The module system.** Aeneas emits `module` files by default, and `module` files cannot import the non-module `OsuModel`.
   Use `-use-lean-modules false`.
3. **Name resolution in `FunsExternal`.** Inside `def float.F64.abs`, the name `F64.abs` resolves to itself. Write `OsuModel.Net.F64.abs`.
4. **`no_std`.** `f64::floor/sqrt` need `std`, so the crate is `std` (+ `alloc::vec::Vec`).
5. **`Result` is an interaction tree** (coinductive). `cases` works through its custom eliminator (`ret/vis/div`). `bind_ok` simp lemmas are
   available, but simp does not push `ok` through `if`, so we add `ite_ok` (Prims.lean).
6. **Derives.** `derive(Debug, PartialEq)` generate a lot of translated noise (fmt, discriminant compare). Derive only `Clone, Copy`.
7. **Prop vs Bool.** `if a.lt(b)` becomes `if decide (a < b) = true`. `simp` normalises it, but the spec's `&&` of Bools versus Rust's
   short-circuit `&&` (nested `if`) needs a case split (`repeat' split; simp_all`). That is fine for about 10 branches.
8. **Do-notation shape of the spec (Lean 4.35's new `do` elaborator).**
   - Mutable state is a nested *tuple* (not `MProd`).
   - The continuation after an `if` is *duplicated* into each branch, so `simulateSteps`' loop body is a large if-tree.
   - It was matched against our compact `stepT` by case splitting on `first`/`manual<gst`/…, then `repeat' split; all_goals simp_all` (30 s).
   - `generalize` of subterms breaks this (dependent `Decidable` instances), so don't.
9. **`Slice.length`/`Vec.length` are abbrevs** that `omega` treats as atoms different from `s.val.length`. Always state bounds with `.val.length`.
10. **Iteration speed** (§1). This was the dominant cost.

## 6. Runtime: native float code and differential test

- **Assembly** (`RUSTFLAGS="--emit asm"`, release):
  - Every wrapper op is a single SSE instruction. `F64(u64)` lives in an xmm register; `from_bits`/`to_bits` vanish.
  - `cumulative_lengths` inner loop: `subss/mulss/addss` → `sqrtss` → `cvtss2sd` → `addsd`. LLVM legally replaced
    `(float)Math.Sqrt((double)x)` by `sqrtss`, which is bit-identical for binary32.
  - `osu_hit_windows` even vectorises two lanes (`mulpd/addpd`, the same IEEE ops per lane).
  - With the default x86-64 baseline target, `floor` is a call to glibc `floor` (no SSE4.1). With `-C target-cpu=native` it becomes `roundsd`. Both are exact.
- **Benchmark** (`osu_eval_bench bench`, under load average ≈10, so noisy):

  | Operation | Time |
  |---|---|
  | `result_for` (1M calls) | ~20 ns/call |
  | `cumulative_lengths` | 11-19 ns/point |
  | Same loop written with plain `f32/f64` | 12-18 ns/point (no measurable wrapper cost) |
  | `simulate_steps` (100k perframe refs) | 10-45 ns/step |

- **Differential test** against the compiled Lean spec: see the last section ("Results").

## 7. Recommendation: scaling to the whole evaluator

Verdict: **D12's Aeneas route is viable on this VM.**
- Install footprint ≈ 2.5 GB, as estimated.
- Translation is instant.
- Proof effort is roughly 1 h per 10-20 lines of Rust after the learning curve, dominated by loop invariants and by matching the spec's control-flow shape.

The real risk is iteration latency (minutes per check) on a loaded 2-core VM, not expressiveness.

### Plan

1. **Write the Rust impl function-by-function mirroring the spec** (same decomposition, same operation order). Every spec `def` gets a Rust fn and a
   `*_refines` theorem stated as `impl … = ok (repr (spec …))`.
2. **Spec-side normal forms first.** For each spec loop, prove in an Aeneas-free file that the `do`/`for`/`while` code equals a plain
   recursion or fold. Reuse the generic `loop_inner`/`forIn_yield` lemmas from `Spec/Schedule.lean`. These checks are fast, and they are where most
   spec-shape surprises show up.
3. **Generic loop library.** Factor the three loop proofs into reusable lemmas:
   - "Aeneas index loop over a slice = `List.foldl`";
   - "fuel loop with break = `inner`";
   - "`Vec.push` accumulation = `List.append`".
   Most evaluator loops have one of these shapes.
4. **Representation maps** live in one file: impl struct ↦ spec struct (field-wise), `i64.val`, `Vec.val.toArray`, enums by match.
   Prefer making Rust structs field-for-field identical to the spec records.
5. **CI**: `charon.sh && lake build OsuProofs` (≈ 15-25 min on this VM), plus the `pocspec`-style difftest for every ported function.

### Rust style rules (to keep translation and proofs tractable)

- Floats only through `float::{F64,F32}` methods. No `f64` in translated code, no operator traits (`a.add(b)`, not `a + b`).
  Constants: `const K: F64 = F64::from_bits(0x…)`, each with a `decide +kernel` lemma.
- Never add a new opaque primitive casually. Each one is trusted and must be one IEEE operation equal to an existing `OsuModel.Net` function, and it should be added to nettest. Anything with .NET logic is written in translated Rust.
- Partial primitives (meaningless on NaN, etc.) get `fail` outside their domain in `FunsExternal`.
- Control flow:
  - `while` loops with an explicit index or fuel counter;
  - no iterators/closures (`for x in v.iter()`, `map`), no `return`/`break` out of nested loops, no `?` on custom error types;
  - `Option` for .NET exceptions.
- Mirror the spec's branch structure where it is cheap. Put the "compute" part in a small non-looping fn (like `fsc_step`), so that the
  loop proof only needs that fn's refinement lemma.
- Integers: `usize` indices, `i64` only where the spec has `Int`. Keep the bounds needed for no-overflow derivable from one global size
  hypothesis (e.g. number of frames/objects < 2^31).
- Structs: plain `struct` with named fields, `#[derive(Clone, Copy)]` at most.
  - No field or fn named `ok`, `fail`, `div`, `loop`, `bind`, `cont`, `done`.
  - No trait objects, no generics instantiated with `&mut`, no `unsafe`.
- `Vec` only for append-only outputs and read-only inputs (`&[T]`). For in-place state updates, prefer returning a new state struct (as with
  `SimState`) over `&mut` borrows into collections. Aeneas supports `&mut`, but the proof terms get heavier.
- Keep each translated fn small, at most ~40 lines and at most one loop. Case-split proofs scale with the branch count of a single function.

## Results (2026-10-21)

- `lake build OsuProofs` succeeds: all theorems in §4 are proved with no `sorry`. `OsuProofs/Axioms.lean` prints the axioms of
  each main theorem (confirmed: `propext`, `Classical.choice`, `Quot.sound` only). There is no `native_decide`.
- **Differential test**: `impl/target/release/osu_eval_bench gen N SEED | proofs/.lake/build/bin/pocspec` (spec-only exe,
  `lake build pocspec`).

  | Run | Cases | Mismatches |
  |---|---|---|
  | `gen 200000 42` | 200k | **0** |
  | `gen 1000000 7` | 1M | **0** |

  - The cases are spread evenly over 4 kinds: hit windows + `resultFor`, `difficultyRange` on raw/special doubles, slider lengths on random
    f32 paths incl. NaN/∞/subnormal bits, and step schedules with out-of-order frames.
  - NaNs compare equal to any NaN.
  - The generator keeps references and frame times finite. With a NaN reference, `proposed == r` never holds, so spec *and* impl run the
    full 10^8-step fuel per reference (≈3 GB; earlyoom killed it). That is a spec property, not a mismatch.
  - Run the generator under `ulimit -v`, but not the Lean exe: the Lean runtime aborts under `ulimit -v`.
- Build command, honouring the STATE.md resource rule: `LEAN_NUM_THREADS=1 tools/heavy lake build OsuProofs pocspec` (≈15-20 min incl.
  regenerated files). If `model/` switches lakefile format (it moved from `lakefile.toml` to `lakefile.lean`), update `configFile` in
  `proofs/lake-manifest.json`.
