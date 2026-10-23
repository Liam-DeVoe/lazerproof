import OsuModel.Net.Convert
import OsuModel.Net.MathOps

/-!
# `System.Random(int seed)` — the legacy seeded generator (`CompatSeedImpl` + `CompatPrng`)

Source: decompiled `System.Private.CoreLib` 10.0.13 (`System.Random`, nested `CompatSeedImpl`,
`CompatPrng`). `new Random(seed)` with `GetType() == typeof(Random)` uses `CompatSeedImpl`
(Knuth's subtractive generator, the .NET Framework algorithm). lazer constructs exactly that:
`new Random((int)Seed.Value)` (OsuModRandom), `new Random(Seed.Value)` (OsuModTargetPractice),
`new Random((int)osuObject.StartTime)` (OsuModWiggle; the `(int)` is the saturating cast `F64.toInt32`).

Unseeded `new Random()` / `Random.Shared` / osu-framework `RNG` use `XoshiroImpl`, seeded from OS
entropy: **not reproducible, not modelled**. lazer only uses them when a mod's `Seed` setting is null
(`Seed.Value ??= RNG.Next()`), which never happens for a stored score — such replays must be rejected.

All state is `Int` (values stay in `[0, int.MaxValue)`; every operation is also wrapped to 32 bits
with `wrap32`, mirroring C# `unchecked` int arithmetic, although no step can actually overflow).
Kernel-computable (structural recursion only).
-/

namespace OsuModel.Net
namespace NetRandom

/-- `int.MaxValue` (`MBIG`). -/
def MBIG : Int := 2147483647
/-- `MSEED` -/
def MSEED : Int := 161803398

/-- two's-complement wrap to int32 (C# unchecked arithmetic). -/
@[inline] def wrap32 (x : Int) : Int := (Int32.ofInt x).toInt

/-- The generator state (`_seedArray` of 56 ints, `_inext`, `_inextp`). -/
structure State where
  a : Array Int
  inext : Nat
  inextp : Nat
deriving Repr, Inhabited

/-- First loop of `Initialize`: `for i in 1..54`. -/
def initLoop1 : Nat → Array Int → Int → Int → Nat → Array Int
  | 0, a, _, _, _ => a
  | n+1, a, mj, mk, ii =>
    let ii := if ii + 21 ≥ 55 then ii + 21 - 55 else ii + 21
    let a := a.set! ii mk
    let mk := wrap32 (mj - mk)
    let mk := if mk < 0 then wrap32 (mk + MBIG) else mk
    let mj := a[ii]!
    initLoop1 n a mj mk ii

/-- Inner loop of the second phase: `for k in 1..55: n = k + 30 (mod 55); a[k] -= a[1 + n]`. -/
def initLoop2Inner : Nat → Array Int → Nat → Array Int
  | 0, a, _ => a
  | m+1, a, k =>
    let n := if k + 30 ≥ 55 then k + 30 - 55 else k + 30
    let v := wrap32 (a[k]! - a[1 + n]!)
    let v := if v < 0 then wrap32 (v + MBIG) else v
    initLoop2Inner m (a.set! k v) (k + 1)

def initLoop2 : Nat → Array Int → Array Int
  | 0, a => a
  | j+1, a => initLoop2 j (initLoop2Inner 55 a 1)

/-- `new Random(seed)` (`CompatPrng.Initialize`). -/
def create (seed : Int32) : State :=
  let s := seed.toInt
  let sub : Int := if s = -2147483648 then 2147483647 else s.natAbs
  let mj := wrap32 (MSEED - sub)
  let a := (Array.replicate 56 (0 : Int)).set! 55 mj
  let a := initLoop1 54 a mj 1 0
  let a := initLoop2 4 a
  { a, inext := 0, inextp := 21 }

/-- `CompatPrng.InternalSample()` (= `Random.Next()`): a value in `[0, int.MaxValue)`. -/
def internalSample (st : State) : Int × State :=
  let inext := if st.inext + 1 ≥ 56 then 1 else st.inext + 1
  let inextp := if st.inextp + 1 ≥ 56 then 1 else st.inextp + 1
  let num := wrap32 (st.a[inext]! - st.a[inextp]!)
  let num := if num = MBIG then num - 1 else num
  let num := if num < 0 then wrap32 (num + MBIG) else num
  (num, { a := st.a.set! inext num, inext, inextp })

/-- `4.656612875245797E-10` = `1.0 / int.MaxValue` rounded (bits `0x3E00000000200000`). -/
def invMBIG : F64 := Float.ofBits 0x3E00000000200000

/-- `CompatPrng.Sample()` = `(double)InternalSample() * 4.656612875245797E-10` (= `NextDouble()`). -/
def sample (st : State) : F64 × State :=
  let (n, st) := internalSample st
  (F64.ofInt n * invMBIG, st)

/-- `Random.NextDouble()` -/
abbrev nextDouble := sample

/-- `Random.Next()` -/
def next (st : State) : Int32 × State :=
  let (n, st) := internalSample st
  (Int32.ofInt n, st)

/-- `Random.Next(maxValue)`: `maxValue < 0` throws ArgumentOutOfRange; otherwise
`double.ConvertToIntegerNative<int>(Sample() * (double)maxValue)` (in range: truncation; the
native and saturating casts agree there since `0 ≤ Sample() < 1`). -/
def nextMax (st : State) (maxValue : Int32) : Except NetExn (Int32 × State) :=
  if maxValue < 0 then .error .argumentOutOfRange
  else
    let (s, st) := sample st
    .ok (F64.toInt32 (s * F64.ofInt32 maxValue), st)

/-- `CompatPrng.GetSampleForLargeRange()` -/
def sampleForLargeRange (st : State) : F64 × State :=
  let (n, st) := internalSample st
  let (m, st) := internalSample st
  let n := if m % 2 = 0 then -n else n
  ((F64.ofInt n + c2147483646) / c4294967293, st)
where
  c2147483646 : F64 := Float.ofBits 0x41DFFFFFFF800000
  c4294967293 : F64 := Float.ofBits 0x41EFFFFFFFA00000

/-- `Random.Next(minValue, maxValue)`: `minValue > maxValue` throws ArgumentOutOfRange. -/
def nextRange (st : State) (minValue maxValue : Int32) : Except NetExn (Int32 × State) :=
  if maxValue < minValue then .error .argumentOutOfRange
  else
    let range : Int := maxValue.toInt - minValue.toInt
    if range > 2147483647 then
      let (s, st) := sampleForLargeRange st
      -- (int)(ConvertToIntegerNative<long>(s * (double)range) + minValue)
      let l := (F64.toInt64 (s * F64.ofInt range)).toInt + minValue.toInt
      .ok (Int32.ofInt l, st)
    else
      let (s, st) := sample st
      .ok (Int32.ofInt ((F64.toInt32 (s * F64.ofInt range)).toInt + minValue.toInt), st)

/-- `Random.NextSingle()`: `do num = (float)Sample() while !(num < 1f)`. The loop is bounded by
`fuel` (each retry needs `Sample() ≥ 1 - 2^-25`, probability ≈ 3e-8); `none` = fuel exhausted. -/
def nextSingle : (fuel : Nat) → State → Option (F32 × State)
  | 0, _ => none
  | fuel+1, st =>
    let (s, st) := sample st
    let f := F64.toF32 s
    if f < 1 then some (f, st) else nextSingle fuel st

end NetRandom
end OsuModel.Net
