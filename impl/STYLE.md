# Rust style for the translated core (`osu_eval_core`)

This extends the "Rust style rules" of `docs/proof-poc.md` (read that first). It records the
conventions used by the Net/Beatmap port (`src/net/*`, `src/beatmap/*`), so that the Sim/Replay port
(`src/sim/*`, `src/replay/*`) can follow the same ones. The aim: every function can later be
proved, with Charon + Aeneas, to refine the Lean function it names.

Translatability check (writes only to `$OUT`, never to `proofs/`):
`OUT=/tmp/x tools/heavy impl/charon_check.sh` (Charon to LLBC, then Aeneas to Lean).

## 1. Mirroring the spec

- **One Lean `def`, one Rust `fn`.**
  - Rust module = Lean file, in snake_case (`OsuModel/Beatmap/SliderPath.lean` becomes `beatmap/slider_path.rs`).
  - Rust fn = Lean def, in snake_case (`calculateLength` becomes `calculate_length`).
  - Namespaced defs get a prefix where needed (`F32.max` becomes `net::mathops::f32_max`).
  - Every fn has a doc comment naming its spec def: ``/// `C# name`; spec `Namespace.def` ``.
- **Same operations in the same order.**
  - Every float operation is the same IEEE operation, in the same order and grouping as the spec. `a - b + c` is `a.sub(b).add(c)`.
  - Never reassociate. Never "simplify" `0 + x` (it turns `-0` into `+0`). Never hoist arithmetic in a way that changes rounding.
- **Helpers that do not exist in Lean are allowed.** Examples: splitting a large def into a loop driver plus a step fn (`div` / `div_step` in `net/decimal.rs`), or a branch fn (`parse_slider`). The doc comment must say which part of which spec def the helper is.
- **Closures and higher-order arguments in the spec** become one of:
  - a **trait**: `SortCmp` / `SortKey` (`beatmap/dotnet.rs`), `HasTime` (`control_points.rs`);
  - a small **enum of the closures actually used**: `mods::PointMap` for `modifySlider f`;
  - **dispatch fns**: the spec's `Mod` record of optional closures becomes `mods::apply_after_conversion`, `apply_to_difficulty`, `apply_to_hit_object` and `apply_to_beatmap`, which match on the acronym.

## 2. Floats

- **Only `float::{F64, F32}`.** No `f64`/`f32` and no operator traits in translated code.
- **Constants** are `const K: F64 = F64::from_bits(0x…)` with a comment giving the literal.
  - Lean literals are correctly rounded, *directly* to the target format (`(0.7 : F32)` is not `(float)0.7`). Compute the bits with Rust's own parser (`"0.7".parse::<f32>()`), never with Python's `struct` (which rounds twice).
  - Constants that Lean computes (`def kFlat := 0.25 * 0.25 * 4`) are computed at run time by the same operations (`fn k_flat()`), not folded by hand.
- **Trusted primitives** live in `float.rs`, which is opaque to Charon. Add them *additively* (never rename). Current set:
  - IEEE arithmetic and predicates;
  - `floor`/`ceil`/`trunc`/`sqrt`;
  - the saturating casts `to_i32_sat`/`to_i64_sat`/`to_u32`/`to_u64` (Rust `as` saturates and maps NaN to 0, exactly like .NET 9+);
  - `from_i64`/`from_u64` (one RNE rounding, = `F64.ofInt`);
  - libm `sin cos tan asin acos atan atan2 exp log log10 pow cbrt` (glibc, called through `extern "C"` or std);
  - `fmod` (exact, = `DotNet.fmodF64`);
  - `parse_decimal` (correctly rounded decimal to binary, = `Parse.decToBits`). Its `digits` are digit *values* 0..=9.

  Each primitive is identified with one `OsuModel.Net` def. Everything with .NET logic is translated Rust on top of the primitives (`net::mathops::f64_round`, `f32_max`, …).
- **NaN.** Never branch on a NaN's sign or payload (`is_negative` is only meaningful on non-NaN values). The Lean runtime canonicalises NaN in `toBits`, Rust does not. The dump prints every NaN canonically.

## 3. Integers, strings, errors

- **Lean `Int32` is C# `int` and wraps.** Use `i32` with `wrapping_add/sub/mul` wherever the spec does `Int32` arithmetic that could overflow on fuzzed input (combo indices, stack heights, spinner counts).
  - Plain `+` is fine for loop indices bounded by array sizes; Aeneas proves those cannot overflow.
- **Lean `Nat` subtraction truncates.** Use `dotnet::nat_sub(a, b)`, never a raw `a - b` that could underflow.
- **Unbounded `Nat`/`Int` in the spec:**
  - use the smallest exact machine representation, and say so in a comment: `u128` for decimal mantissas, the explicit 192-bit `U192` for 96×96-bit products;
  - or saturate where only a range check follows (`parse::INT_CAP` for `int.Parse`);
  - or keep a digit string (the `double.Parse` mantissa).
- **Strings** are `Vec<u32>` / `&[u32]` of Unicode scalar values (`dotnet::Str`, = Lean `String`/`List Char`).
  - Literals are byte strings compared with `dotnet::str_eq(s, b"General")`.
  - List-recursive Lean helpers take an index instead of a list suffix (`parse::skip_white(s, i)`).
- **Exceptions:**
  - `.NET` exceptions are `Result<T, NetExn>`. Pipeline errors are `Result<T, DecodeError>`: `Msg(&'static str)` for messages, `Net(what, e)` for `liftNet what e`.
  - Messages that reach the dump are rendered byte-identically to Lean (`dump::render`).
  - Propagate with `tri!(e)`, the Aeneas-friendly `?` defined in `net/mod.rs`; it expands to a `match` and an early `return`.
  - **Inside loops**, do not `return`. Carry an `err: Option<E>` in the loop condition (`while err.is_none() && i < n`) and return after the loop.
- **Lean `a[i]!`** returns a default when out of bounds; Rust indexing panics. Use plain indexing where the spec's index is provably in range. Where it is not obvious, write an explicit default (`slider_path::get_f64`).

## 4. Control flow and data

- **Loops.**
  - Only `while` with an explicit counter. Lean `for _ in [0:fuel]` / `while … && fuel` loops keep the **same fuel bound** (`bSplineToPiecewiseLinear`: 10^8, tick generation: 10^7, …).
  - Lean `break`/`return` inside a loop becomes a `go`/`done`/`res: Option` flag in the loop condition.
  - No iterators, closures, `for x in`, `?`, or `return` inside loops.
- **Recursion** is allowed where the spec recurses (`intro_sort` with fuel, `merge_sort_range`, `assign`).
- **Mutation.**
  - Large records (`OsuHitObject`, `PlayableBeatmap`, `DecoderState`) are updated in place through `&mut` (`set_stack_height(&mut hos[k], v)`), mirroring the spec's functional update `{ h with … }`. This keeps the Rust allocation-free where Lean updates in place.
  - Small records (`Copy` structs such as `NestedObject`, `ParserState`, `NetDecimal`, `random::State`) are passed and returned by value.
  - When the spec reads a stale copy of a value that it later updates (`objectI` in `applyStacking`), the Rust re-reads it from the array. That gives the same value: the comment at the call site says why.
- **`Vec` operations used:** `new`, `with_capacity`, `push`, `pop`, `len`, indexing, `clone`, and a helper `dotnet::insert_at` (written with `push` and shifts).
  - Avoid `Vec::insert/remove/extend/iter/sort` and slice methods other than `len`/indexing.
- **Derives:** `Clone, Copy` (and `PartialEq, Eq` only on field-less or `Copy` enums that are compared). No `Debug`.
- **Names.** No field or fn named `ok`, `fail`, `div`, `loop`, `bind`, `cont`, `done` or `type`.
  - Used here instead: `ok_`, `ptype`, `etype`, `stype`, `otype`. (`F64::div` is an opaque primitive, so it is fine.)

## 5. Lessons from the Charon/Aeneas runs (keep to these)

- **No references inside data or loop state.** A `&'static str` / `&[u8]` inside an enum or struct that lives in a loop
  (`Option<DecodeError>` with a `&str` message) gives "Not implemented". Use integer ids instead: error messages are ids
  (`beatmap::errors`), setting keys and enum member tables are ids (`beatmap::names`). The text lives in an untranslated
  `text`/`strings` submodule that only the dump uses.
- **No constants that hold references** (`const T: [&[u8]; 12]`, promoted `&CONST`). Byte-string literals passed
  directly as call arguments (`str_eq(s, b"General")`) are fine.
- **Flat `match` on integers** rather than long `if … else if` chains: 40-branch chains blew Charon's memory up.
- **Loops:**
  - Do not `match` on an expression that borrows (`match f(&mut x) {…}`, `match at(v, i) {…}` returning `Result<&T, _>`).
    Bind the result to a local first, or avoid returning borrows in `Result`/`Option`.
  - Do not create a `let h = &v[i]` alias inside a loop that also mutates. Index directly, or move the inner part into a helper fn.
  - "Could not compute a loop fixed point": make the loop-carried state update unconditionally. For example, iterate
    over "next interesting index" helpers (`next_segment_end`, `next_match`) instead of `if cond { state = i }`,
    pass owned `Vec`s by value through helpers (`calculate_path_segment`), and put conditional `&mut v[k]` updates in a
    callee (`set_combo`).
- **Resources.** Aeneas needs about 3 GB RSS for `net` + `beatmap`. Run `MODULES="net beatmap" impl/charon_check.sh`
  only when memory is free (earlyoom kills it otherwise). `MODULES=net` alone needs about 0.3 GB.

## 6. Not translated

These modules are excluded from Charon; they are plain Rust test harnesses:
- `beatmap::dump` (string formatting);
- the binaries in `osu_eval_bench` (`bmdump_rs`, `nettest_rs`).

Keep them out of the core logic: they only print values.
