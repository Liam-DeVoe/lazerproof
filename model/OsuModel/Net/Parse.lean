import OsuModel.Net.MathOps

/-!
# `double.Parse`, `float.Parse`, `int.Parse` (InvariantCulture) and lazer's `Parsing.*`

Modelled on .NET 10.0.13 `Number.Parsing.cs` / `Number.Parsing.Common.cs`:

`double.Parse(s, CultureInfo.InvariantCulture)` uses `NumberStyles.Float | AllowThousands`:
```
  ws* [+|-] body ws* \0*          (ws = U+0009..U+000D, U+0020 only)
  body = digits-with-commas [ '.' digits ] [ (e|E) [+|-] digit+ ]
```
* `,` (group separator) is accepted anywhere in the integer part *after the first digit*
  (`"1,,0"` = 10, `",1"` invalid, `"1,"` = 1); not after the `.`.
* at least one digit (integer or fraction) is required: `"."`, `".e5"` invalid, `"1."`, `".5"` valid.
* an `e` not followed by `[sign] digit` is not consumed (so the string is invalid).
* an exponent that reaches ≥ 10^8 while reading digits saturates: result is ±0 (negative exponent)
  or ±∞ (positive exponent) whenever the mantissa is non-zero.
* otherwise the result is the correctly rounded value of the *exact* decimal (.NET Core 3.0+ is
  IEEE-compliant, overflow gives ±∞, no OverflowException); `-0` gives `-0.0`.
* if the number grammar fails, the string is `Trim()`med (full Unicode `char.IsWhiteSpace` set!) and
  compared ASCII-case-insensitively with `Infinity`, `-Infinity`, `NaN`, `+Infinity`, `+NaN`, `-NaN`.
  Note `"Infinity\0"` is invalid (trailing NULs only allowed after a number).
* failure → `FormatException`.

`float.Parse` is identical but rounds directly decimal → binary32 (no double rounding).

`int.Parse(s, InvariantCulture)` (`NumberStyles.Integer`): `ws* [+|-] digit+ ws* \0*`; out of range
→ `OverflowException` (only if the grammar matched), else `FormatException`.
-/

namespace OsuModel.Net
namespace Parse

/-- `Number.IsWhite`: U+0009–U+000D and U+0020. -/
def isWhite (c : Char) : Bool := c.toNat == 0x20 || (0x09 ≤ c.toNat && c.toNat ≤ 0x0D)

/-- `char.IsWhiteSpace` (used by `string.Trim()` in the Infinity/NaN fallback). -/
def isUnicodeWhiteSpace (c : Char) : Bool :=
  let n := c.toNat
  isWhite c || n == 0x85 || n == 0xA0 || n == 0x1680 || (0x2000 ≤ n && n ≤ 0x200A) ||
    n == 0x2028 || n == 0x2029 || n == 0x202F || n == 0x205F || n == 0x3000

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def digitVal (c : Char) : Nat := c.toNat - '0'.toNat

def dropWhile (p : Char → Bool) : List Char → List Char
  | [] => []
  | c :: cs => if p c then dropWhile p cs else c :: cs

/-- `ReadOnlySpan<char>.ContainsAnyExcept('\0')` negated: rest consists of NULs only. -/
def allNul : List Char → Bool
  | [] => true
  | c :: cs => c.toNat == 0 && allNul cs

/-- ASCII-only case-insensitive equality (`StringComparison.OrdinalIgnoreCase` on these symbols;
verified: no non-ASCII char compares equal to any letter of `Infinity`/`NaN`). -/
def eqIgnoreCase : List Char → List Char → Bool
  | [], [] => true
  | a :: as, b :: bs => a.toLower == b.toLower && eqIgnoreCase as bs
  | _, _ => false

/-- Result of the numeric grammar. `mant` = all digits as an integer, `exp10` = decimal exponent
(already including the fraction length), `sat` = exponent saturation (`some negExp`). -/
structure Num where
  neg : Bool
  mant : Nat
  exp10 : Int
  sat : Option Bool
deriving Repr, DecidableEq

/-- Integer/fraction digit loop. Returns (mantissa, #fraction digits, seenDigit, rest). -/
def digitsLoop : List Char → Nat → Nat → Bool → Bool → Nat × Nat × Bool × List Char
  | [], m, nf, seen, _ => (m, nf, seen, [])
  | c :: cs, m, nf, seen, inDec =>
    if isDigit c then digitsLoop cs (m * 10 + digitVal c) (if inDec then nf + 1 else nf) true inDec
    else if c == '.' && !inDec then digitsLoop cs m nf seen true
    else if c == ',' && seen && !inDec then digitsLoop cs m nf seen inDec
    else (m, nf, seen, c :: cs)

/-- Exponent digits with the .NET saturation rule (`exp ≥ 100_000_000` before a further digit). -/
def expLoop : List Char → Nat → Bool → Nat × Bool × List Char
  | [], e, sat => (e, sat, [])
  | c :: cs, e, sat =>
    if isDigit c then
      if sat || e ≥ 100000000 then expLoop cs e true
      else expLoop cs (e * 10 + digitVal c) false
    else (e, sat, c :: cs)

/-- Optional exponent part. Returns (exponent, saturated?, rest); `(0, none, s)` if absent. -/
def parseExp (s : List Char) : Int × Option Bool × List Char :=
  match s with
  | c :: rest =>
    if c == 'e' || c == 'E' then
      let (negE, r) := match rest with
        | '+' :: r => (false, r)
        | '-' :: r => (true, r)
        | r => (false, r)
      match r with
      | d :: _ =>
        if isDigit d then
          let (e, sat, r') := expLoop r 0 false
          if sat then (0, some negE, r') else ((if negE then -(e : Int) else e), none, r')
        else (0, none, s)
      | [] => (0, none, s)
    else (0, none, s)
  | [] => (0, none, s)

/-- `TryStringToNumber` for `NumberStyles.Float | AllowThousands`, invariant culture. -/
def parseNumber (s : List Char) : Option Num :=
  let s := dropWhile isWhite s
  let (neg, s) := match s with
    | '+' :: r => (false, r)
    | '-' :: r => (true, r)
    | r => (false, r)
  let (m, nf, seen, s) := digitsLoop s 0 0 false false
  if !seen then none else
  let (e, sat, s) := parseExp s
  let s := dropWhile isWhite s
  if !allNul s then none else
  some { neg, mant := m, exp10 := e - nf, sat }

/-- Correctly rounded `(-1)^neg · m · 10^x` in format `f`, as bits. -/
def decToBits (f : Fmt) (neg : Bool) (m : Nat) (x : Int) : Nat :=
  if m == 0 then f.encZero neg
  else if x ≥ 0 then
    if x > 400 then f.encInf neg else roundBin f neg (m * 10 ^ x.toNat) 0 false
  else
    let k := (-x).toNat
    let lm := Nat.log2 m + 1
    -- value < 2^lm / 8^k: far below half the smallest subnormal → ±0
    if (lm : Int) - 3 * k < -1100 then f.encZero neg
    else
      let p := 10 ^ k
      let lp := Nat.log2 p + 1
      let s := f.prec + 4 + lp - lm   -- (truncated Nat subtraction: s ≥ 0)
      let num := m <<< s
      roundBin f neg (num / p) (-(s : Int)) (num % p != 0)

/-- Value of a successfully parsed number, as bits. -/
def numToBits (f : Fmt) (n : Num) : Nat :=
  match n.sat with
  | some negExp =>
    if n.mant == 0 then f.encZero n.neg
    else if negExp then f.encZero n.neg else f.encInf n.neg
  | none => decToBits f n.neg n.mant n.exp10

/-- Infinity/NaN fallback of `TryParseFloat`. `some (some neg)` = ±∞, `some none` = NaN. -/
def parseSymbol (s : List Char) : Option (Option Bool) :=
  let t := (dropWhile isUnicodeWhiteSpace (dropWhile isUnicodeWhiteSpace s).reverse).reverse
  let inf := "Infinity".toList
  let nan := "NaN".toList
  if eqIgnoreCase t inf then some (some false)
  else if eqIgnoreCase t ('-' :: inf) then some (some true)
  else if eqIgnoreCase t nan then some none
  else match t with
    | '+' :: r => if eqIgnoreCase r inf then some (some false)
                  else if eqIgnoreCase r nan then some none else none
    | '-' :: r => if eqIgnoreCase r nan then some none else none
    | _ => none

/-- Generic float parse to bits (`none` = FormatException). NaN is the canonical NaN. -/
def parseFloatBits (f : Fmt) (s : List Char) : Option Nat :=
  match parseNumber s with
  | some n => some (numToBits f n)
  | none => match parseSymbol s with
    | some (some neg) => some (f.encInf neg)
    | some none => some f.encNaN
    | none => none

/-- `int.Parse` grammar: returns the mathematical value, `none` on FormatException. -/
def parseIntegerValue (s : List Char) : Option Int :=
  let s := dropWhile isWhite s
  let (neg, s) := match s with
    | '+' :: r => (false, r)
    | '-' :: r => (true, r)
    | r => (false, r)
  match s with
  | d :: _ =>
    if !isDigit d then none else
    let (m, _, _, rest) := digitsLoop s 0 0 false true   -- `inDec = true`: no '.'/',' accepted
    let rest := dropWhile isWhite rest
    if !allNul rest then none else
    some (if neg then -(m : Int) else m)
  | [] => none

end Parse

open Parse in
/-- `double.Parse(s, CultureInfo.InvariantCulture)` on a list of UTF-16-free chars. -/
def doubleParseChars (s : List Char) : Except NetExn F64 :=
  match parseFloatBits Fmt.f64 s with
  | some b => .ok (F64.ofBitsN b)
  | none => .error .format

/-- `double.Parse(s, CultureInfo.InvariantCulture)`. -/
def doubleParse (s : String) : Except NetExn F64 := doubleParseChars s.toList

open Parse in
/-- `float.Parse(s, CultureInfo.InvariantCulture)`. -/
def floatParseChars (s : List Char) : Except NetExn F32 :=
  match parseFloatBits Fmt.f32 s with
  | some b => .ok (F32.ofBitsN b)
  | none => .error .format

def floatParse (s : String) : Except NetExn F32 := floatParseChars s.toList

open Parse in
/-- `int.Parse(s, CultureInfo.InvariantCulture)`. -/
def intParseChars (s : List Char) : Except NetExn Int32 :=
  match parseIntegerValue s with
  | none => .error .format
  | some v => if v < -2^31 || v > 2^31 - 1 then .error .overflow else .ok (Int32.ofInt v)

def intParse (s : String) : Except NetExn Int32 := intParseChars s.toList

/-! ## lazer `osu.Game/Beatmaps/Formats/Parsing.cs` -/
namespace Parsing

/-- `Parsing.MAX_COORDINATE_VALUE` -/
def MAX_COORDINATE_VALUE : Int32 := 131072
/-- `Parsing.MAX_PARSE_VALUE = int.MaxValue` (as double). -/
def MAX_PARSE_VALUE : F64 := F64.ofInt (2^31 - 1)

/-- `Parsing.ParseDouble(input, parseLimit = MAX_PARSE_VALUE, allowNaN = false)`. -/
def parseDouble (input : String) (parseLimit : F64 := MAX_PARSE_VALUE) (allowNaN := false) :
    Except NetExn F64 := do
  let output ← doubleParse input
  if output < -parseLimit then throw .overflow      -- "Value is too low"
  if parseLimit < output then throw .overflow       -- "Value is too high"
  if !allowNaN && output.isNaN then throw .format   -- "Not a number"
  return output

/-- `Parsing.ParseFloat(input, parseLimit = (float)MAX_PARSE_VALUE, allowNaN = false)`.
Note `(float)int.MaxValue = 2147483648f`. -/
def parseFloat (input : String) (parseLimit : F32 := MAX_PARSE_VALUE.toF32) (allowNaN := false) :
    Except NetExn F32 := do
  let output ← floatParse input
  if output < -parseLimit then throw .overflow
  if parseLimit < output then throw .overflow
  if !allowNaN && output.isNaN then throw .format
  return output

/-- `Parsing.ParseInt(input, parseLimit = (int)MAX_PARSE_VALUE)`. -/
def parseInt (input : String) (parseLimit : Int32 := 2147483647) : Except NetExn Int32 := do
  let output ← intParse input
  if output < -parseLimit then throw .overflow
  if output > parseLimit then throw .overflow
  return output

end Parsing
end OsuModel.Net
