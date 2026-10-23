# .NET numeric primitives in the Lean model (`model/OsuModel/Net/`)

This file covers the bit-exact model of the CoreCLR (.NET 10.0.13, linux-x64) numeric primitives
that lazer's osu! judgement and scoring code uses.

- Package: `model/` (Lean 4.35.0, package `OsuModel`, no Mathlib).
- Library entry point: `import OsuModel.Net`.
- Differential tester: `model/nettest/` (C# generator) streams into `lake exe nettest` (Lean checker).

## Ground rules

* `F64 := Float`, `F32 := Float32` (abbrevs). Lean 4.35 defines these as `Float.Model`/`Float32.Model`
  (IEEE bit patterns with one canonical NaN).
  * The operations `+ - * /`, comparisons, `neg`, `ofBits`/`toBits` and `ofScientific` are
    **kernel-reducible**.
  * Compiled, they are the C operators, i.e. the same SSE2 instructions RyuJIT emits. RyuJIT never
    contracts to FMA and has no x87 excess precision.
* Everything this library adds is plain `Nat`/`Int` code with structural recursion only
  (`OsuModel/Net/Fmt.lean`: `decode`, `roundBin` = correct RNE rounding, `isqrt`). It reduces under
  `decide +kernel`; see `OsuModel/Net/Checks.lean` (~70 kernel-checked facts, two of them `∀` lemmas).
* Exceptions are modelled as `Except NetExn α`. `NetExn` is one of: format, overflow, argument,
  argumentOutOfRange, arithmetic.
* **Beware of dot notation.** `(x : Float).toInt32` resolves to *Lean core's* `Float.toInt32`, not
  `F64.toInt32`. Always write `F64.foo x` unless `x` is syntactically typed `F64`.

### NaN

Neither the Lean model nor the Lean runtime can represent NaN payloads or signs:

- the model has a single NaN, `0x7FF8000000000000`;
- the compiled `Float.ofBits`/`toBits` canonicalise NaN (verified).

.NET produces `0xFFF8000000000000` (`double.NaN`, `0/0`) and propagates payloads. The tester
therefore treats any NaN as equal to any NaN, and counts payload differences separately
("nan-payload-diff", informational).

Rule for the model: never branch on the sign or bits of a NaN. Lazer only uses `IsNaN`, and the
.NET primitives below never look at NaN bits.

The one observable consequence is **signalling NaN inputs**. They cannot be created by arithmetic
or parsing, only by bit reinterpretation. `Math.Pow(sNaN, 0)` is NaN on .NET but `pow(qNaN, 0) = 1`.
The tester reports these cases as "snan-input-diff"; they are not failures and are irrelevant to
lazer.

## Primitives

The Status column uses three values:
- **K**: kernel-computable definition.
- **E**: extern, trusted (glibc).
- **K\***: Lean core definition that is kernel-reducible.

Test op numbers refer to `NetTest/Main.lean`.

| .NET | semantics / source | Lean | Status | test op |
|---|---|---|---|---|
| `a+b a-b a*b a/b` (double, float) | IEEE RNE, SSE2 `addsd`… | `+ - * /` on `F64`/`F32` | K\* | 1–4, 6–9 (+ model 151–159) |
| `< <= == > >= !=` | IEEE (NaN false, `+0 == -0`) | `<`, `≤`, `==`; `a > b` ↔ `b < a`, `!=` ↔ `!(a == b)` | K\* | 5, 10 (+ model 155, 160) |
| unary `-` | sign flip | `-x` | K\* | 37, 47 |
| `(float)double` | `cvtsd2ss`, RNE, overflow → ∞ | `F64.toF32` (`convertBits`) | K | 11 |
| `(double)float` | exact | `F32.toF64` | K | 12 |
| `(double)int/long/uint/ulong`, `(float)…` | one correct RNE rounding (`(float)ulong` is *not* double-rounded, verified) | `F64.ofInt32/ofInt64/ofUInt32/ofUInt64`, `F32.…`, `F64.ofInt : Int → F64` | K | 13–20 |
| `(int)/(long)/(uint)/(ulong)` of double/float | **saturating** since .NET 9 (x64): truncate, clamp, NaN → 0, verified | `F64.toInt32/toInt64/toUInt32/toUInt64`, `F32.…` | K | 21–28 |
| `Math.Round(double)` | `[Intrinsic]` → `roundsd` mode 4; managed fallback `CopySign((a + CopySign(2^52,a)) - …, a)` | `F64.round` (managed formula) | K | 30 |
| `Math.Round(x, AwayFromZero)` | managed: `Truncate(x + CopySign(0.49999999999999994, x))` | `F64.roundMode x .awayFromZero` | K | 31 |
| `Math.Round(x, ToZero/ToNeg/ToPosInf)` | Truncate/Floor/Ceiling | `F64.roundMode` | K | via 32–34 |
| `Math.Round(x, digits[, mode])` | managed: digits ∉ [0,15] throws; if `|x| < 1e16`: `Round(x*10^d, mode)/10^d` (so `Round(2.675,2) = 2.68`) | `F64.roundDigits`, `F64.roundDigitsMode` | K | 58 |
| `MathF.Round(…)` | same with 2^23, `0.49999997f`, digits ≤ 6, limit `1e8f` | `F32.round`, `F32.roundMode`, `F32.roundDigits` | K | 40, 41, 59 |
| `Math.Floor/Ceiling/Truncate`, MathF | `roundsd`/`roundss` (SSE4.1); a zero result keeps the input sign (`Ceiling(-0.5) = -0`) | `F64.floor/ceiling/truncate`, `F32.…` (`roundIntBits`) | K | 32–34, 42–44 |
| `Math.Abs(double/float)` | clear the sign bit | `F64.abs`, `F32.abs` | K | 35, 45 |
| `Math.Max/Min(double)`, `MathF.Max/Min`, `Math.Max(float,float)` | managed IEEE 754:2019 maximum/minimum: NaN-propagating, `Max(+0,-0) = +0`, `Min(+0,-0) = -0` | `F64.max/min`, `F32.max/min` (literal source) | K | 50–53 |
| `Math.Clamp(v, min, max)` | `min > max` → ArgumentException; then `v < min ? min : v > max ? max : v` (NaN v → NaN) | `F64.clamp`, `F32.clamp` | K | 54, 55 |
| `Math.Sign(double/float)` | NaN → ArithmeticException; ±0 → 0 | `F64.sign`, `F32.sign : Except NetExn Int32` | K | 56, 57 |
| `Math.Sqrt`, `MathF.Sqrt` | `sqrtsd`/`sqrtss`, correctly rounded | `F64.sqrt`, `F32.sqrt`: `isqrt` on scaled significand + sticky → `roundBin` | K | 36, 46 (+ Lean `Float.Model.sqrt` 186, 196) |
| `Math.Sin Cos Tan Asin Acos Atan Atan2 Exp Log Log10 Pow Cbrt` | FCall → glibc `sin`… (`floatdouble.cpp`) | `F64.sin` … = Lean core `Float.sin` (`@[extern "sin"] opaque`) | E | 60–71 |
| `MathF.Sin Cos Tan Asin Acos Atan Atan2 Exp Log Pow` | glibc `sinf`… (`floatsingle.cpp`) | `F32.sin` … = `Float32.sin` (`sinf`) | E | 80–90 |
| `Math.Log(a, newBase)` | managed special cases, then `Log(a)/Log(newBase)` | `F64.logBase` | K + E | 73 |
| `double.Parse(s, Invariant)` | see below | `doubleParse : String → Except NetExn F64`, `doubleParseChars` | K | 100 |
| `float.Parse(s, Invariant)` | direct decimal → binary32 rounding | `floatParse` | K | 101 |
| `int.Parse(s, Invariant)` | `ws* [+-] digit+ ws* \0*`, out of range → Overflow | `intParse` | K | 102 |
| lazer `Parsing.ParseDouble/ParseFloat/ParseInt` | `osu.Game/Beatmaps/Formats/Parsing.cs`: parse, then `< -limit` / `> limit` → OverflowException, NaN → FormatException unless `allowNaN`; default limits `int.MaxValue` (as double), `(float)int.MaxValue = 2147483648f`, `int.MaxValue` | `Parsing.parseDouble/parseFloat/parseInt` (optional `parseLimit`, `allowNaN`) | K | 103–105 (C# side compiles lazer's `Parsing.cs` verbatim) |

### Parsing details (`Number.Parsing.Common.cs`, `Number.Parsing.cs`)

The grammar is `NumberStyles.Float | AllowThousands`:

```
ws* [+|-] body ws* \0*      (ws = U+0009–000D, U+0020)
```

Rules:

- **Thousands separator.** `,` is allowed in the integer part *after the first digit*:
  - `"1,,0"` = 10
  - `"1,"` = 1
  - `",1"` and `"1.5,"` are invalid.
- **At least one digit.** `"1."` and `".5"` are valid; `"."` and `".e5"` are not.
- **Exponent.** `e` must be followed by `[+-]digit`, otherwise the parse fails.
  - When the exponent reaches ≥ 10^8 during digit accumulation it saturates to ±int.MaxValue: the
    result is ∞ or 0 whenever the mantissa is non-zero (e.g. `"0.0001e100000000"` → ∞).
  - Otherwise the result is the **correctly rounded exact decimal**, including:
    - overflow → ±∞ (never an OverflowException);
    - `"-0"` → -0.0;
    - tails of more than 768 digits (handled with a sticky bit).
- **Trailing NULs** are accepted only after a number (`"1 \0"` is valid, `"1\0 "` and
  `"Infinity\0"` are invalid).
- **Infinity/NaN fallback.** `Trim()` with the *Unicode* whitespace set (so `" NaN　"` is
  NaN), then an ASCII case-insensitive match against `Infinity`, `-Infinity`, `NaN`, `+Infinity`,
  `+NaN` and `-NaN`. `∞` is not accepted.

Lean's own `Float.ofScientific`/`Float32.ofScientific` are correctly rounded and kernel-reducible.
The tester checks them against .NET (ops 200 and 201). Our parser uses its own `Parse.decToBits`
(through `roundBin`) so that the rounding code is shared and float32 rounding is direct.

## Transcendentals: trusted base

- **CoreCLR calls libm directly.** `src/coreclr/classlibnative/float/floatdouble.cpp` is just
  `return sin(x);` (and so on). `libcoreclr.so` imports `sin@GLIBC_2.2.5`, `pow@GLIBC_2.2.5`,
  `powf@GLIBC_2.27`, … from `libm.so.6` (`nm -D`).
- **JIT.** RyuJIT does not inline these on x64. It only constant-folds constant arguments, which
  also goes through libm via `libclrjit.so`.
- **Single-instruction intrinsics on x64:**
  - `Math.Sqrt` → `sqrtsd`
  - `Floor`/`Ceiling`/`Truncate`/`Round` → `roundsd`
  - `Abs` → `andps`
  - `FusedMultiplyAdd` → `vfmadd`
  - `Max`/`Min` → vectorised compare/blend sequences with the managed semantics

  All of these are modelled exactly (kernel-computable), not trusted.
- **Verified on this VM.** `nettest jit <x>` with `DOTNET_TieredCompilation=0
  DOTNET_JitDisasm="JitW:*"` shows:
  - `Math.Floor` → `vroundsd …, 9`
  - `Math.Round` → `vroundsd …, 4`
  - `Math.Sqrt` → `vsqrtsd`; `MathF.Sqrt` → `vsqrtss`
  - `Math.Max` → `vrangesd` + 2×`vfixupimmsd` (AVX-512; on other CPUs the managed code runs, with
    the same semantics up to NaN payload)
  - `(int)x` → `vcmpordsd`/`vcvttsd2si` + `cmov` saturation
  - `Math.Sin`/`Math.Pow`/`MathF.Atan2` → `call` (FCall into libm)

  With `LD_PRELOAD` of a shim defining `sin`, `pow` and `atan2f`, .NET returns the shim's values,
  which proves dynamic resolution through libm.
- **Lean side.** The compiled Lean binary dynamically links the system `libm.so.6`, with the same
  symbol versions (`sin@GLIBC_2.2.5`, …), so both call the identical code.
- **Pinned glibc: Ubuntu GLIBC 2.39-0ubuntu8.x (x86-64)**. glibc ≥ 2.41 swaps several binary32
  functions for CORE-MATH versions, and any other libm can differ in the last ulp. Re-run the tester
  after any OS upgrade.

## Differential test

```
cd model && lake build
cd nettest && dotnet build -c Release -m:1
dotnet bin/Release/net10.0/nettest.dll gen <countPerOp> <seed> [op,op,..] | ../.lake/build/bin/nettest
dotnet bin/Release/net10.0/nettest.dll lazer <countPerSetting> <seed> | ../.lake/build/bin/nettest   # needs lazer + oracle builds
```

**Generator inputs.** Uniform random bits, plus targeted distributions:
- specials and their ±2-ulp neighbours (±0, ±∞, quiet and signalling NaN, subnormal/normal
  boundaries, 2^52 and 2^23 boundaries, int32/int64 limits);
- moderate exponents and integers, halves and quarters;
- values with few low bits set (halfway cases);
- near-float doubles (`(float)x` ties) and correlated operand pairs (`b = ±a ± k ulp`);
- for transcendentals, "human" ranges.

**Parsing inputs.**
- exact decimal expansions of binary64/binary32 midpoints (±1 in the last digit, truncated, or with
  a non-zero tail);
- `R`/`G17`/`E16`-formatted random values;
- long digit strings (up to 900 digits, exponents up to ±1200);
- random strings over a hostile alphabet (`,`, `.`, `e`, signs, whitespace, `\0`, NBSP, `∞`,
  letters of Infinity/NaN);
- mutated numbers and symbol case/whitespace variants;
- a fixed list of edge cases (the probe results above).

Results:

| run | checks | failures |
|---|---|---|
| `gen 20000 1` | 1,625,419 | 0 (after sNaN classification) |
| `gen 200000 3` | 16,253,235 | 0 |
| `gen 1000000 20261021` | 81,266,671 | **0** (9 min; Pow/MathF.Pow: 119+141 sNaN-input cases, classified) |

`nettest probe` prints the hand-picked behaviour probes (parse edge cases, casts, Max/Min zeros,
NaN bits, CPU features: SSE4.1/AVX2/FMA/AVX-512F present on this VM).

## Library primitives (Random, decimal, osuTK, osu-framework)

Added for the mod specs (`docs/mods/*.md`). Sources are the decompiled binaries actually loaded at runtime
(`System.Private.CoreLib`/`System.Linq` 10.0.13, `ppy.osuTK.NS20 1.0.211`, `ppy.osu.Framework 2026.921.1`; the
framework checkout is the same tag). The C# side of the test calls the **real** `osuTK.dll`/`osu.Framework.dll` from the
nupkg cache (`nettest.csproj` `<Reference HintPath>`), and `nettest lazer` loads lazer's own pinned `osu.Game` build.
All Lean code is kernel-computable except the easing functions' glibc `pow/sin/cos` calls (E). Kernel-checked facts:
`OsuModel/Net/LibChecks.lean`.

| .NET / library | semantics (decompiled) | Lean | Status | test op |
|---|---|---|---|---|
| `new Random(int seed)`, `Next()`, `Next(max)`, `Next(min,max)`, `NextDouble()`, `NextSingle()` | `CompatSeedImpl` + `CompatPrng` (Knuth subtractive, 56-int state, `Sample() = InternalSample() * 4.656612875245797E-10`); `Next(max) = ConvertToIntegerNative<int>(Sample()*max)`; `Next(min,max)` with `GetSampleForLargeRange` when the range exceeds int.MaxValue; `NextSingle` retries while `(float)Sample() == 1` | `NetRandom.*` (`Net/Random.lean`; `nextSingle` takes fuel) | K | 110 |
| unseeded `new Random()`, `Random.Shared`, framework `RNG` | Xoshiro256** seeded from OS entropy | not modelled (non-reproducible; lazer uses it only when a `Seed` setting is null) | — | — |
| `decimal` representation | `(neg, mant < 2^96, scale ≤ 28)`, `GetBits` exact, `-0m` kept | `NetDecimal` (`Net/Decimal.lean`) | K | all below |
| `(decimal)double`, `decimal.CreateTruncating(double)` | `VarDecFromR8`: 15 significant digits computed in double, `Math.Round` half-even, ≤ 14 trailing zeros stripped; CreateTruncating saturates at ±2^96, NaN → `0.0m` (scale 1); the cast throws Overflow | `NetDecimal.ofF64`, `createTruncatingF64` | K | 112, 111 |
| `(decimal)float`, `decimal.CreateTruncating(float)` | `VarDecFromR4`: 7 digits, arithmetic in double | `ofF32`, `createTruncatingF32` | K | 114, 113 |
| `(double)decimal`, `(float)decimal`, `double/float.CreateTruncating(decimal)` | `VarR8FromDec`: `((double)lo64 + (double)hi32 * 2^64) / 1e{scale}`, sign flip; float = `(float)` of that | `NetDecimal.toF64`, `toF32` | K | 115, 116 |
| `decimal / decimal` | `VarDecDiv`: exact integer quotient, scale up by `SearchScale` (≤ 9 digits per step, ≤ 28), half-even with remainder, `OverflowUnscale` on 97-bit carry, `Unscale` (trailing zeros) only if inexact; DivideByZero, Overflow | `NetDecimal.div` | K | 117 |
| `decimal * decimal` | `VarDecMul` + `ScaleResult` (sticky half-even, scale ≤ 28, product > 47-scale of two 32-bit mantissas → `0m`) | `NetDecimal.mul` | K | 118 |
| `Math.Round(decimal)` | `InternalRound` ToEven, result scale 0, sign kept | `NetDecimal.round` | K | 119 |
| `BindableDouble/BindableFloat` (`BindableNumber.Value` setter, constructor, `MinValue`/`MaxValue`/`Precision` initialisers) | decimal snapping (`docs/mods/difficulty-rate-fail.md` §2.2), `double.Clamp = Min(Max(v,lo),hi)`, `Equals`-guarded store (old ±0 kept) | `Framework.Bindable.BD/BF` (`init`, `setValue`, `setMin`, …), `setDouble/setFloat` | K | 146–149; lazer `APIMod.ToMod` 230/231 |
| `Enumerable.Average(List<double>)` | sequential sum from `+0.0` (vectorised only for int/long), `/ count` | `SysMisc.averageF64` | K | 222 |
| `float/double.DegreesToRadians/RadiansToDegrees` | `(d * π) / 180`, `(r * 180) / π` (float: `π = (float)Math.PI`) | `SysMisc.F32/F64.*` | K | 220, 221 |
| osuTK `Vector2` (`+ - * /`, unary `-` = sign flip, `Length` = `(float)Math.Sqrt(x*x+y*y)`, `LengthSquared`, `LengthFast`, `Normalized`, `NormalizeFast`, `Distance` (double sqrt), `DistanceSquared`, `Dot`, `PerpDot`, `Lerp` = `blend*(b-a)+a`, `Clamp` (min test first), `ComponentMin/Max`, `Divide`, `Perpendicular*`) | decompiled `osuTK.Vector2` | `OsuTK.Vector2.*` (`Net/OsuTK.lean`) | K | 120–134 |
| osuTK `MathHelper.InverseSqrtFast(float)` | `xh = 0.5f*x; i = 0x5f375a86 - (bits >> 1); y = asfloat(i); y *= 1.5f - xh*y*y` | `MathHelper.inverseSqrtFast`, `lengthFast` | K | 131, 122 |
| osuTK `MathHelper` constants, `DegreesToRadians/RadiansToDegrees` (float: `x * 0.017453292f`, `x * 57.29578f` = 0x42652EE0) | folded constants | `MathHelper.*` | K | 136, 138 |
| osuTK `Matrix3.Mult` | row-major, `x*x4 + y*x5 + z*x6` left to right | `Matrix3.mult` | K | 135 |
| framework `Vector2Extensions.Transform/Distance/DistanceSquared` | `M11*x + M21*y + M31`; `Distance` uses `MathF.Sqrt` | `Framework.Vector2Extensions.*` | K | 140, 141 |
| framework `MatrixExtensions` (Translate/Rotate/Scale/Shear From Left/Right) | literal; rotate uses `cosf/sinf` | `Framework.MatrixExtensions.*` | K + E | 142 |
| framework `DrawInfo.ApplyTransform` | guards with float `!=`, FLOAT_EPSILON scale clamp, `float.DegreesToRadians` | `Framework.DrawInfo.applyTransform` | K + E | 143 |
| framework `Precision.AlmostEquals/AlmostBigger/DefinitelyBigger` (float, double, Vector2) | `|a-b| <= e`, `a > b - e`, `a - e > b`; `FLOAT_EPSILON = 1e-3f`, `DOUBLE_EPSILON = 1e-7` | `Framework.Precision.*` | K | 144, 145 |
| framework `DefaultEasingFunction.ApplyEasing` (all 36 `Easing` values; out-of-range → identity) | literal, consts folded by Roslyn in the same double order, `static readonly` offsets via glibc `pow`/`sin` | `Framework.applyEasing` | E | 210 |
| framework `Interpolation.ValueAt` (double, float, int, Vector2), `Lerp`, `Damp`, `DampContinuously` | double: `v1 + t*(v2-v1)` with `v1==v2`/`current==0`/`duration==0` shortcuts; float = `(float)` of the double version; int = `(int)Math.Round`; Vector2: float `current/duration`, `t = (float)ease((double)(c/d))` | `Framework.Interpolation.*` | E | 211–215 |
| `Math.Round(x, 2)` on WU/WD ramps | existing `F64.roundDigits` | — | K | 58 (extra targeted inputs) |

Lazer-level probe: `dotnet nettest.dll lazer <countPerSetting> <seed> | lake exe nettest` loads
`lazer/osu.Game.Rulesets.Osu/bin/Release/net10.0/osu.Game{,.Rulesets.Osu}.dll` (dependencies resolved from
`oracle/bin`). On stderr it prints every osu! mod's `GetSettingsSourceProperties()` order with bindable
type/default/range/precision, plus targeted `APIMod.ToMod` results (WU/WD cross constraints, DT 1.135 → 1.14,
Wiggle default 1.00000001490116, …). On stdout it streams ops 230/231 (random JSON values for all 18 double/float
mod settings) for the Lean checker.

Results (library ops):

| run | checks | failures |
|---|---|---|
| `gen 200000 20261021 <ops 58,110–149,210–222>` | 10,135,361 (incl. 735k `Random` calls over 10k seeds) | **0** (55 s) |
| `lazer 3000 7` | 54,000 `APIMod.ToMod` settings | **0** |

Found while testing (now modelled): `decimal.CreateTruncating(NaN)` is `0.0m` with scale 1; `BindableNumber` clamps
with `double.Clamp` (IEEE min/max: `-0 → +0` at a `0` bound) rather than `Math.Clamp`; `Bindable.Value` keeps the old
value when the new one is `Equals` (so `-0.0` never replaces `+0.0`); osuTK `RadiansToDegrees(float)` uses
`57.29578f` (0x42652EE0).

## Known gaps / not modelled

* NaN payload/sign, and signalling NaNs (see above).
* `decimal` addition/subtraction/comparison/`%`, `Round` with other modes or digits, and decimal parsing
  (not used by lazer's mod settings path).
* `Random.NextInt64`, `NextBytes`, `Shuffle`, `GetItems`; derived-class `Random` (`CompatDerivedImpl`); unseeded Xoshiro.
* osu-framework `Interpolation.ValueAt` for colours/rectangles/other types; `MatrixExtensions.FastInvert`.
* `Math.FusedMultiplyAdd`, `Math.ScaleB`, `Math.Log2`, `BitIncrement` and other unused APIs.
* `int.Parse` / `double.Parse` with non-invariant cultures, or `NumberStyles` other than the
  defaults.
* `Scale` int32 overflow inside .NET's number buffer (needs strings of more than 2^31 digits).
* Lean `Float.sqrt` itself is kernel-opaque (it uses `Nat.sqrt`, which is well-founded). Use
  `F64.sqrt` instead. It is tested equal to `Float.Model.sqrt` and to .NET.
