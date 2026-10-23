/-!
# Generic IEEE-754 binary formats on raw bit patterns (`Nat`)

Everything in this file is plain `Nat`/`Int` arithmetic with structural recursion only, so it
reduces in the kernel (`decide +kernel`, `rfl`) and compiles to GMP-backed native code.

* `decode` splits a bit pattern into sign / class / integer significand / binary exponent.
* `roundBin` correctly rounds (round-to-nearest, ties-to-even — the only mode .NET uses) a
  non-negative real given as `(q + ε) · 2^e`, `ε ∈ [0,1)`, `sticky ↔ ε > 0`, into a format, and
  encodes the result (handles subnormals, overflow to infinity, carry into the next binade).
* `isqrt` is an integer square root (Newton iteration with explicit fuel).

These are the building blocks for the .NET primitives that Lean's `Float`/`Float32` either do not
provide (f64→f32 conversion, floor/ceil/trunc, decimal parsing) or do not provide in a
kernel-reducible way (`sqrt`).
-/

namespace OsuModel.Net

/-- An IEEE-754 binary interchange format: `mbits` stored fraction bits, `ebits` exponent bits. -/
structure Fmt where
  mbits : Nat
  ebits : Nat
deriving Repr, DecidableEq

namespace Fmt

/-- binary64 (`double`). -/
def f64 : Fmt := ⟨52, 11⟩
/-- binary32 (`float`). -/
def f32 : Fmt := ⟨23, 8⟩

/-- Precision (significand bits including the hidden bit). -/
def prec (f : Fmt) : Nat := f.mbits + 1
/-- Exponent bias. -/
def bias (f : Fmt) : Nat := 2 ^ (f.ebits - 1) - 1
/-- All-ones biased exponent (inf/NaN). -/
def emaxBiased (f : Fmt) : Nat := 2 ^ f.ebits - 1
/-- Exponent of the least significant significand bit of subnormals / the smallest normal binade. -/
def qmin (f : Fmt) : Int := 1 - (f.bias : Int) - f.mbits
/-- Total width in bits. -/
def width (f : Fmt) : Nat := f.mbits + f.ebits + 1
/-- Sign bit mask. -/
def signMask (f : Fmt) : Nat := 2 ^ (f.mbits + f.ebits)

/-- Encoding of a signed zero. -/
def encZero (f : Fmt) (neg : Bool) : Nat := if neg then f.signMask else 0
/-- Encoding of a signed infinity. -/
def encInf (f : Fmt) (neg : Bool) : Nat := f.encZero neg + f.emaxBiased * 2 ^ f.mbits
/-- The canonical quiet NaN (positive, payload 0). This is also Lean's logical NaN
(`Float.nan.toBits = 0x7FF8000000000000`). .NET's `double.NaN` is `0xFFF8000000000000` (negative);
NaN sign/payload are deliberately not modelled (see docs/net-float.md). -/
def encNaN (f : Fmt) : Nat := f.emaxBiased * 2 ^ f.mbits + 2 ^ (f.mbits - 1)

end Fmt

/-- A decoded floating-point value. `fin neg m e` denotes `(-1)^neg · m · 2^e` with `m > 0`. -/
inductive Dec where
  | nan
  | inf (neg : Bool)
  | zero (neg : Bool)
  | fin (neg : Bool) (m : Nat) (e : Int)
deriving Repr, DecidableEq, Inhabited

/-- Sign bit of a bit pattern. -/
def signOf (f : Fmt) (b : Nat) : Bool := (b / f.signMask) % 2 == 1

/-- Decode a bit pattern (only the low `f.width` bits are looked at). -/
def decode (f : Fmt) (b : Nat) : Dec :=
  let neg := signOf f b
  let be := (b / 2 ^ f.mbits) % 2 ^ f.ebits
  let fr := b % 2 ^ f.mbits
  if be == f.emaxBiased then
    (if fr == 0 then .inf neg else .nan)
  else if be == 0 then
    (if fr == 0 then .zero neg else .fin neg fr f.qmin)
  else
    .fin neg (fr + 2 ^ f.mbits) ((be : Int) - 1 + f.qmin)

/-- Encode `(-1)^neg · r · 2^Q` where `Q ≥ qmin`, `r ≤ 2^prec` and `r` already fits
(i.e. the value is already rounded to the format's grid). Overflows to infinity. -/
def encodeQ (f : Fmt) (neg : Bool) (r : Nat) (Q : Int) : Nat :=
  if r == 0 then f.encZero neg else
  let (r, Q) := if r ≥ 2 ^ f.prec then (r / 2, Q + 1) else (r, Q)
  if r < 2 ^ f.mbits then
    f.encZero neg + r            -- subnormal (then necessarily Q = qmin)
  else
    let be : Int := Q - f.qmin + 1
    if be ≥ (f.emaxBiased : Int) then f.encInf neg
    else f.encZero neg + be.toNat * 2 ^ f.mbits + (r - 2 ^ f.mbits)

/-- Correctly round (ties-to-even) `(-1)^neg · (q + ε) · 2^e` where `ε ∈ [0,1)` and `sticky ↔ ε > 0`.
Requires `q > 0` (if `q = 0` the result is a signed zero, regardless of `sticky`).
If `sticky` is set, `q` must have at least `prec + 1` bits (so the rounding position lies inside
`q`); all callers guarantee this. -/
def roundBin (f : Fmt) (neg : Bool) (q : Nat) (e : Int) (sticky : Bool) : Nat :=
  if q == 0 then f.encZero neg else
  -- Shift so that at least 3 bits are always dropped (k ≥ 3); exactness is preserved since
  -- the fraction ε sits strictly below the new last bit.
  let s := f.prec + 2
  let q := q <<< s
  let e := e - s
  let L : Nat := Nat.log2 q + 1
  let E : Int := (L : Int) - 1 + e            -- floor(log2 value)
  let Q : Int := max (E - ((f.prec : Int) - 1)) f.qmin  -- exponent of the result's last bit
  let k : Nat := (Q - e).toNat
  let r := q >>> k
  let rem := q % 2 ^ k
  let half := 2 ^ (k - 1)
  let up := decide (rem > half) || (rem == half && (sticky || r % 2 == 1))
  encodeQ f neg (if up then r + 1 else r) Q

/-- Exact encoding of a signed integer (rounded if it does not fit). -/
def encInt (f : Fmt) (neg : Bool) (n : Nat) : Nat :=
  if n == 0 then f.encZero neg else roundBin f neg n 0 false

/-- Newton iteration for `⌊√n⌋`, starting from an over-estimate. -/
def isqrtAux : Nat → Nat → Nat → Nat
  | 0, _, x => x
  | fuel + 1, n, x =>
    let y := (x + n / x) / 2
    if y < x then isqrtAux fuel n y else x

/-- Integer square root `⌊√n⌋` (fuel 256 is far more than needed for inputs below 2^4000). -/
def isqrt (n : Nat) : Nat :=
  if n == 0 then 0 else isqrtAux 256 n (2 ^ (Nat.log2 n / 2 + 1))

/-- Correctly rounded square root on bit patterns (IEEE `squareRoot`, as `sqrtsd`/`sqrtss`).
NaN → NaN, ±0 → ±0, negative → NaN, +∞ → +∞. -/
def sqrtBits (f : Fmt) (b : Nat) : Nat :=
  match decode f b with
  | .nan => f.encNaN
  | .inf false => f.encInf false
  | .inf true => f.encNaN
  | .zero neg => f.encZero neg
  | .fin true _ _ => f.encNaN
  | .fin false m e =>
    let s0 := 2 * f.prec + 4
    let s := if (e - s0) % 2 == 0 then s0 else s0 + 1
    let M := m <<< s
    let E2 := e - s
    let r := isqrt M
    roundBin f false r (E2 / 2) (r * r != M)

/-- Convert between formats (`cvtsd2ss` / `cvtss2sd`): exact or correctly rounded. -/
def convertBits (src dst : Fmt) (b : Nat) : Nat :=
  match decode src b with
  | .nan => dst.encNaN
  | .inf neg => dst.encInf neg
  | .zero neg => dst.encZero neg
  | .fin neg m e => roundBin dst neg m e false

/-- Integer-valued rounding directions used by Floor/Ceiling/Truncate. -/
inductive IntRound where
  | floor | ceil | trunc
deriving Repr, DecidableEq

/-- `roundsd`/`roundss` with a directed mode (Math.Floor / Ceiling / Truncate).
NaN/∞/±0 and values that are already integers are returned unchanged (NaN canonicalised);
a zero result keeps the sign of the input (e.g. `Ceiling(-0.5) = -0.0`). -/
def roundIntBits (f : Fmt) (mode : IntRound) (b : Nat) : Nat :=
  match decode f b with
  | .nan => f.encNaN
  | .inf _ | .zero _ => b
  | .fin neg m e =>
    if e ≥ 0 then b else
    let k := (-e).toNat
    let ip := m >>> k
    let fracNZ := m % 2 ^ k != 0
    let n := match mode with
      | .trunc => ip
      | .floor => if neg && fracNZ then ip + 1 else ip
      | .ceil => if !neg && fracNZ then ip + 1 else ip
    encInt f neg n

/-- Truncate a finite value to an integer (`Int`); `none` for NaN, `±∞` saturates via `some ±2^4096`
(callers clamp). -/
def truncToInt (f : Fmt) (b : Nat) : Option Int :=
  match decode f b with
  | .nan => none
  | .inf neg => some (if neg then -(2 ^ 4096 : Int) else 2 ^ 4096)
  | .zero _ => some 0
  | .fin neg m e =>
    let ip : Nat := if e ≥ 0 then m <<< e.toNat else m >>> (-e).toNat
    some (if neg then -(ip : Int) else ip)

/-- Saturating float→integer conversion (.NET 9+ semantics on all platforms):
NaN → 0, otherwise truncate toward zero and clamp to `[lo, hi]`. -/
def satConv (f : Fmt) (lo hi : Int) (b : Nat) : Int :=
  match truncToInt f b with
  | none => 0
  | some v => if v < lo then lo else if v > hi then hi else v

end OsuModel.Net
