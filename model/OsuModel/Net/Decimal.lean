import OsuModel.Net.Convert
import OsuModel.Net.MathOps

/-!
# `System.Decimal` (the subset osu-framework / lazer use)

Source: decompiled `System.Private.CoreLib` 10.0.13, `System.Decimal` and `System.Decimal.DecCalc`
(`VarDecFromR8`, `VarDecFromR4`, `VarR8FromDec`, `VarR4FromDec`, `VarDecDiv`, `VarDecMul`,
`ScaleResult`, `SearchScale`, `OverflowUnscale`, `Unscale`, `InternalRound`), plus
`decimal.CreateTruncating<double/float>` (`Double/Single.TryConvertTo<decimal>`: saturate at
`±7.922816251426434E+28` / `±7.9228163E+28f`, NaN → `0.0m`, i.e. scale 1).

The machine-word algorithms are transcribed as exact `Nat` arithmetic with the same control flow
(same scaling steps, same overflow/rounding decisions, same trailing-zero stripping), so the
result *representation* (mantissa, scale, sign bit — i.e. `decimal.GetBits`) matches, not just
the value. Differential test: `nettest` ops 111–118 compare all four `GetBits` words.

Representation: `neg` (sign bit), `mant < 2^96`, `scale ≤ 28`. Negative zero exists
(`(-0m).GetBits` has the sign bit) and is preserved where .NET preserves it.
Kernel-computable (no well-founded recursion; loops are fuel-bounded with fuel never exhausted:
each division iteration raises the scale, so ≤ 28 + 4 iterations happen).
-/

namespace OsuModel.Net

structure NetDecimal where
  neg : Bool
  mant : Nat
  scale : Nat
deriving Repr, DecidableEq, Inhabited

namespace NetDecimal

def two96 : Nat := 2 ^ 96
def zero : NetDecimal := ⟨false, 0, 0⟩
/-- `decimal.MaxValue` / `MinValue` -/
def maxValue : NetDecimal := ⟨false, two96 - 1, 0⟩
def minValue : NetDecimal := ⟨true, two96 - 1, 0⟩

/-- `decimal.GetBits`: `[lo, mid, hi, flags]`. -/
def getBits (d : NetDecimal) : UInt32 × UInt32 × UInt32 × UInt32 :=
  (UInt32.ofNat d.mant, UInt32.ofNat (d.mant >>> 32), UInt32.ofNat (d.mant >>> 64),
   UInt32.ofNat ((d.scale <<< 16) ||| (if d.neg then 0x80000000 else 0)))

/-- `new decimal(int[] bits)` / `decimal(lo, mid, hi, isNegative, scale)`. -/
def ofBits (lo mid hi flags : UInt32) : NetDecimal :=
  ⟨flags >>> 31 == 1, lo.toNat ||| (mid.toNat <<< 32) ||| (hi.toNat <<< 64), ((flags >>> 16) &&& 0xFF).toNat⟩

/-- `d > 0m` (`decimal.CompareTo`; `-0m` is not positive). -/
def isPositive (d : NetDecimal) : Bool := !d.neg && d.mant != 0

/-- `DoublePowers10[0..28]` = the double literals `1e0 … 1e28` (correctly rounded). -/
def doublePowers10 : Array F64 := (List.range 29).toArray.map fun k => F64.ofInt (10 ^ k)

/-- `2^64` as a double (`1.8446744073709552E+19`). -/
def ds2to64 : F64 := Float.ofBits 0x43F0000000000000

/-- `VarR8FromDec` = `(double)d` = `double.CreateTruncating(d)`:
`((double)Low64 + (double)High * 2^64) / DoublePowers10[scale]`, negated if the sign bit is set. -/
def toF64 (d : NetDecimal) : F64 :=
  let num := (F64.ofUInt64 (UInt64.ofNat (d.mant % 2 ^ 64)) + F64.ofInt (d.mant >>> 64) * ds2to64) /
    doublePowers10[d.scale]!
  if d.neg then -num else num

/-- `VarR4FromDec` = `(float)d` = `(float)VarR8FromDec(d)` (double rounding). -/
def toF32 (d : NetDecimal) : F32 := F64.toF32 d.toF64

/-- `C# >>` on int (arithmetic shift = floor division). -/
@[inline] def sar (x : Int) (k : Nat) : Int := Int.fdiv x (2 ^ k)

/-- Shared tail of `VarDecFromR8/R4` for a non-zero rounded mantissa and power. `maxStrip` is 14
(R8) or 6 (R4); `steps` are the greedy stripping powers (8,4,2,1 for R8; 4,2,1 for R4). -/
def finishFromR (neg : Bool) (mant : Nat) (power : Int) (maxStrip : Nat) (steps : List Nat) :
    Except NetExn NetDecimal :=
  if power < 0 then
    let v := mant * 10 ^ power.natAbs
    -- UInt64x64To128 throws when the product exceeds 96 bits (cannot happen for finite inputs).
    if v ≥ two96 then .error .overflow else .ok ⟨neg, v, 0⟩
  else
    let p := power.toNat
    let (m, p, _) := steps.foldl (init := (mant, p, Nat.min p maxStrip)) fun (m, p, lim) k =>
      if lim ≥ k && m % 10 ^ k == 0 then (m / 10 ^ k, p - k, lim - k) else (m, p, lim)
    .ok ⟨neg, m, p⟩

def p1e15 : F64 := F64.ofInt (10 ^ 15)
def p1e14 : F64 := F64.ofInt (10 ^ 14)
def p1e7 : F64 := F64.ofInt (10 ^ 7)
def p1e6 : F64 := F64.ofInt (10 ^ 6)
def f64ten : F64 := F64.ofInt 10

/-- `VarDecFromR8` = the `(decimal)double` operator (throws OverflowException for |x| ≥ 2^96,
∞ and NaN). About 15 significant digits, computed in double arithmetic. -/
def ofF64 (input : F64) : Except NetExn NetDecimal :=
  let e : Int := ((input.toBits >>> 52) &&& 0x7FF).toNat
  let num := e - 1022
  if num < -94 then .ok zero
  else if num > 96 then .error .overflow
  else
    let neg := input < 0
    let dbl := if neg then -input else input
    let power : Int := 14 - sar (num * 19728) 16
    let (dbl, power) : F64 × Int :=
      if power ≥ 0 then
        let power := if power > 28 then 28 else power
        (dbl * doublePowers10[power.toNat]!, power)
      else if power != -1 || p1e15 ≤ dbl then (dbl / doublePowers10[power.natAbs]!, power)
      else (dbl, 0)
    let (dbl, power) := if dbl < p1e14 && power < 28 then (dbl * f64ten, power + 1) else (dbl, power)
    -- SSE4.1 path: (ulong)(long)Math.Round(dbl)
    let mant := (F64.toInt64 (F64.round dbl)).toInt.toNat
    if mant == 0 then .ok zero
    else finishFromR neg mant power 14 [8, 4, 2, 1]

/-- `VarDecFromR4` = the `(decimal)float` operator: same algorithm with 7 digits (arithmetic in
double). -/
def ofF32 (input : F32) : Except NetExn NetDecimal :=
  let e : Int := ((input.toBits >>> 23) &&& 0xFF).toNat
  let num := e - 126
  if num < -94 then .ok zero
  else if num > 96 then .error .overflow
  else
    let neg := input < 0
    let dbl := F32.toF64 (if neg then -input else input)
    let power : Int := 6 - sar (num * 19728) 16
    let (dbl, power) : F64 × Int :=
      if power ≥ 0 then
        let power := if power > 28 then 28 else power
        (dbl * doublePowers10[power.toNat]!, power)
      else if power != -1 || p1e7 ≤ dbl then (dbl / doublePowers10[power.natAbs]!, power)
      else (dbl, 0)
    let (dbl, power) := if dbl < p1e6 && power < 28 then (dbl * f64ten, power + 1) else (dbl, power)
    -- SSE4.1 path: (uint)(int)Math.Round(dbl)
    let mant := (F64.toInt32 (F64.round dbl)).toInt.toNat
    if mant == 0 then .ok zero
    else finishFromR neg mant power 6 [4, 2, 1]

def f64DecMax : F64 := Float.ofBits 0x45F0000000000000  -- 7.922816251426434E+28 = 2^96
def f32DecMax : F32 := Float32.ofBits 0x6F800000        -- 7.9228163E+28f = 2^96

/-- `decimal.CreateTruncating(double)` (osu-framework `BindableNumber`): saturating, NaN → `0.0m`. -/
def createTruncatingF64 (x : F64) : Except NetExn NetDecimal :=
  if f64DecMax ≤ x then .ok maxValue
  else if x ≤ -f64DecMax then .ok minValue
  else if x.isNaN then .ok ⟨false, 0, 1⟩   -- the literal `0.0m` (scale 1)
  else ofF64 x

/-- `decimal.CreateTruncating(float)`. -/
def createTruncatingF32 (x : F32) : Except NetExn NetDecimal :=
  if f32DecMax ≤ x then .ok maxValue
  else if x ≤ -f32DecMax then .ok minValue
  else if x.isNaN then .ok ⟨false, 0, 1⟩   -- the literal `0.0m` (scale 1)
  else ofF32 x

/-! ### multiplication (`VarDecMul` + `ScaleResult`) -/

/-- `ScaleResult`: reduce the scale of the exact product `p` (≥ 2^96 or scale > 28) with
round-half-even (sticky over all discarded digits). Returns the new (mantissa, scale). -/
def scaleResult (p : Nat) (scale : Nat) : Except NetExn (Nat × Nat) := do
  let bitlen := p.log2 + 1
  let mut num : Int := 0
  if p ≥ two96 then
    -- hiRes*32 - 64 - 1 - lzcnt(top word) = bitlen - 97
    num := sar (((bitlen : Int) - 97) * 77) 8 + 1
    if num > scale then throw .overflow
  if num < (scale : Int) - 28 then num := (scale : Int) - 28
  if num == 0 then return (p, scale)
  let mut sc : Int := scale - num
  let mut q := p
  let mut sticky := false
  let mut rem := 0
  let mut pow := 1
  -- each iteration either divides more (num > 0), or adds one more digit (num := 1, scale--),
  -- or finishes; at most scale + 9 iterations
  for _ in [0:120] do
    sticky := sticky || rem != 0
    let chunk := if num ≥ 9 then 9 else num.toNat
    pow := 10 ^ chunk
    rem := q % pow
    q := q / pow
    num := num - 9
    if num > 0 then continue
    if q ≥ two96 then
      if sc == 0 then throw .overflow
      num := 1; sc := sc - 1
      continue
    let half := pow / 2
    if half ≤ rem && (half < rem || q % 2 == 1 || sticky) then
      q := q + 1
      if q ≥ two96 then
        if sc == 0 then throw .overflow
        sticky := false; rem := 0; num := 1; sc := sc - 1
        continue
    return (q, sc.toNat)
  return (q, sc.toNat)

/-- `decimal * decimal` (`VarDecMul`). -/
def mul (d1 d2 : NetDecimal) : Except NetExn NetDecimal := do
  let scale := d1.scale + d2.scale
  let neg := d1.neg != d2.neg
  if d1.mant < 2 ^ 32 && d2.mant < 2 ^ 32 then
    let mut p := d1.mant * d2.mant
    let mut s := scale
    if s > 28 then
      if s > 47 then return zero
      let pw := 10 ^ (s - 28)
      let q := p / pw
      let item := p % pw
      let half := pw / 2
      p := if item ≥ half && (item > half || q % 2 == 1) then q + 1 else q
      s := 28
    return ⟨neg, p, s⟩
  else
    let p := d1.mant * d2.mant
    if p == 0 then return zero
    if p ≥ two96 || scale > 28 then
      let (q, s) ← scaleResult p scale
      return ⟨neg, q, s⟩
    return ⟨neg, p, scale⟩

/-! ### division (`VarDecDiv`) -/

/-- `PowerOvflValues[i]` = `floor((2^96 - 1) / 10^(i+1))` as (hi, midlo). -/
def powerOvfl (i : Nat) : Nat × Nat :=
  let v := (two96 - 1) / 10 ^ (i + 1)
  (v >>> 64, v % 2 ^ 64)

/-- `SearchScale(quotient, scale)`: largest power (≤ 9, and ≤ 28 - scale when scale > 19) by
which the quotient can be scaled without exceeding 96 bits. Throws if the result cannot reach
scale 0. Literal transcription. -/
def searchScale (q : Nat) (scale : Int) : Except NetExn Nat :=
  let u := q >>> 64
  let low := q % 2 ^ 64
  let check (num : Nat) : Except NetExn Nat :=
    if (num : Int) + scale < 0 then .error .overflow else .ok num
  if u > 429496729 then check 0
  else
    let band : Nat :=
      let num :=
        if u > 42949 then
          if u > 4294967 then (if u > 42949672 then 1 else 2)
          else (if u > 429496 then 3 else 4)
        else if u > 429 then (if u > 4294 then 5 else 6)
        else (if u > 42 then 7 else 8)
      let (hi, ml) := powerOvfl (num - 1)
      if u == hi && low > ml then num - 1 else num
    if scale > 19 then
      let num := (28 - scale).toNat
      if u < (powerOvfl (num - 1)).1 then check num else check band
    else if u < 4 || (u == 4 && low ≤ 5441186219426131129) then .ok 9
    else check band

/-- `OverflowUnscale`: the 97-bit quotient `q` is divided by 10 with half-even rounding (sticky). -/
def overflowUnscale (q : Nat) (scale : Int) (sticky : Bool) : Except NetExn (Nat × Int) :=
  let scale := scale - 1
  if scale < 0 then .error .overflow
  else
    let r := q % 10
    let q := q / 10
    .ok (if r > 5 || (r == 5 && (sticky || q % 2 == 1)) then q + 1 else q, scale)

/-- `Unscale`: strip trailing zeros (8 at a time while possible, then 4, 2, 1 once each). -/
def unscale (q : Nat) (scale : Int) : Nat × Int := Id.run do
  let mut q := q
  let mut s := scale
  for _ in [0:4] do
    if q % 100000000 == 0 && s ≥ 8 then q := q / 100000000; s := s - 8
  if q % 10000 == 0 && s ≥ 4 then q := q / 10000; s := s - 4
  if q % 100 == 0 && s ≥ 2 then q := q / 100; s := s - 2
  if q % 10 == 0 && s ≥ 1 then q := q / 10; s := s - 1
  return (q, s)

/-- `decimal / decimal` (`VarDecDiv`). Throws DivideByZero (`.arithmetic`) / Overflow. -/
def div (d1 d2 : NetDecimal) : Except NetExn NetDecimal := do
  let den := d2.mant
  if den == 0 then throw .arithmetic
  let mut scale : Int := (d1.scale : Int) - d2.scale
  let mut flag := false
  let mut q := d1.mant / den
  let mut r := d1.mant % den
  let mut roundIt := false
  let mut done := false
  for _ in [0:40] do
    if done then break
    let mut p : Nat := 0
    if r == 0 then
      if scale ≥ 0 then done := true; break
      p := Nat.min 9 (-scale).toNat
    else
      flag := true
      if scale == 28 then roundIt := true; done := true; break
      p ← searchScale q scale
      if p == 0 then roundIt := true; done := true; break
    scale := scale + p
    let pw := 10 ^ p
    if q * pw ≥ two96 then throw .overflow  -- IncreaseScale overflow
    let rr := r * pw
    q := q * pw + rr / den
    r := rr % den
    if q ≥ two96 then
      let (q', s') ← overflowUnscale q scale (r != 0)
      q := q'; scale := s'
      done := true
      break
  if roundIt then
    if 2 * r > den || (2 * r == den && q % 2 == 1) then
      q := q + 1
      if q ≥ two96 then
        let (q', s') ← overflowUnscale q scale true
        q := q'; scale := s'
  if flag then
    let (q', s') := unscale q scale
    q := q'; scale := s'
  return ⟨d1.neg != d2.neg, q, scale.toNat⟩

/-! ### rounding -/

/-- `Math.Round(decimal)` = `decimal.Round(d)` = `Round(d, 0, ToEven)` (`InternalRound`):
half-even to an integer; the result has scale 0 (when the input scale was > 0) and keeps the
sign bit (so `Round(-0.4m)` is `-0m`). -/
def round (d : NetDecimal) : NetDecimal :=
  if d.scale == 0 then d
  else
    let pw := 10 ^ d.scale
    let q := d.mant / pw
    let r := d.mant % pw
    let q := if 2 * r > pw || (2 * r == pw && q % 2 == 1) then q + 1 else q
    ⟨d.neg, q, 0⟩

end NetDecimal
end OsuModel.Net
