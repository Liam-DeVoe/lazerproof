import OsuModel.Net
import OsuModel.Beatmap.CharTable

/-!
# .NET base-library behaviour used by the beatmap pipeline

Small, executable models of BCL routines whose exact behaviour is observable in lazer's beatmap
pipeline: string trimming/splitting, `Enum.TryParse`, `double.CompareTo`, `List<double>.BinarySearch`,
`List<T>.Sort(Comparison<T>)` (introsort, *unstable*), C# `%` on doubles, `Math.Max/Min` on `int`.

Strings: .NET strings are UTF-16; the model uses Lean `String` (Unicode scalar values). Every
operation below only inspects ASCII separators or uses predicates that agree on BMP characters;
supplementary characters are handled where it matters (`charIsLetter`, see `CharTable.lean`).
-/

namespace OsuModel.Beatmap
open OsuModel.Net

/-- `char.IsWhiteSpace` (identical to `Parse.isUnicodeWhiteSpace`; set checked with `bmtest whitespace`). -/
def isWhiteSpace (c : Char) : Bool := Parse.isUnicodeWhiteSpace c

/-- `string.TrimStart()` -/
def trimStart (s : String) : String := String.ofList (s.toList.dropWhile isWhiteSpace)
/-- `string.TrimEnd()` -/
def trimEnd (s : String) : String := String.ofList ((s.toList.reverse.dropWhile isWhiteSpace).reverse)
/-- `string.Trim()` -/
def trim (s : String) : String := trimEnd (trimStart s)

/-- `string.IsNullOrWhiteSpace(s)` (non-null). -/
def isNullOrWhiteSpace (s : String) : Bool := s.toList.all isWhiteSpace

/-- `s.Split(c)` (keeps empty entries; `"".Split(c) = [""]`). -/
def split (s : String) (c : Char) : Array String := (s.splitOn c.toString).toArray

/-- `line.Split(separator, 2, TrimEntries)` as used by `LegacyDecoder.SplitKeyVal`
(`LegacyDecoder.cs:155-164`): key and (possibly empty) value, both trimmed. -/
def splitKeyVal (line : String) (sep : Char := ':') : String × String :=
  match line.splitOn sep.toString with
  | [] => ("", "")
  | [k] => (trim k, "")
  | k :: rest => (trim k, trim (sep.toString.intercalate rest))

/-- `string.StartsWith(prefix)` (ordinal). -/
def startsWith (s p : String) : Bool := s.startsWith p

/-- `double.CompareTo(double)`: total order with NaN smallest, `-0 = +0`. -/
def compareF64 (a b : F64) : Int :=
  if a < b then -1 else if b < a then 1 else if a == b then 0
  else if a.isNaN then (if b.isNaN then 0 else -1) else 1

/-- C# `x % 1.0` on doubles (IEEE `fmod(x, 1)`: exact, sign of `x`). -/
def fmod1 (x : F64) : F64 :=
  if x.isNaN || x == F64.posInf || x == F64.negInf then F64.nan
  else if F64.abs x < 1 then x
  else
    let r := x - F64.truncate x
    if r == 0 then F64.copySign 0 x else r

/-- Decompose a finite double into `(sign, m, e)` with `|x| = m * 2^e` (`m < 2^53`). -/
def decomposeF64 (x : F64) : Bool × Nat × Int :=
  let b := x.toBits.toNat
  let neg := b >>> 63 == 1
  let ef := (b >>> 52) % 2048
  let f := b % 2^52
  if ef == 0 then (neg, f, -1074) else (neg, f + 2^52, (ef : Int) - 1075)

/-- `2^k` as a double, `-1074 ≤ k ≤ 1023` (exact). -/
def pow2F64 (k : Int) : F64 :=
  if k ≥ -1022 then Float.ofBits (UInt64.ofNat ((k + 1023).toNat <<< 52))
  else Float.ofBits (UInt64.ofNat (1 <<< (k + 1074).toNat))

/-- C# `a % b` on doubles = IEEE `fmod` (exact; result has the sign of `a`): NaN if `a` is
infinite or NaN or `b` is zero or NaN; `a` if `b` is infinite. Computed exactly on the integer
significands. -/
def fmodF64 (a b : F64) : F64 :=
  if a.isNaN || b.isNaN || a.isInf || b == 0 then F64.nan
  else if b.isInf then a
  else
    let (na, ma, ea) := decomposeF64 a
    let (_, mb, eb) := decomposeF64 b
    let k := min ea eb
    let A := ma * 2 ^ (ea - k).toNat
    let B := mb * 2 ^ (eb - k).toNat
    let r := A % B
    -- `r * 2^k` is exactly representable (it is at most |a| and on the grid of the smaller exponent)
    let v : F64 := F64.ofInt r * pow2F64 k
    if r == 0 then F64.copySign 0 a else if na then -v else v

/-- C# `a % b` on floats (`fmodf`): exact, so computing it in double and narrowing is exact. -/
def fmodF32 (a b : F32) : F32 := F64.toF32 (fmodF64 (F32.toF64 a) (F32.toF64 b))

/-- `List<double>.BinarySearch(value)` (`ArraySortHelper<double>.BinarySearch`, comparer
`double.CompareTo`): index if found, else bitwise complement of the insertion point. -/
def binarySearchF64 (a : Array F64) (v : F64) : Int := Id.run do
  let mut lo : Int := 0
  let mut hi : Int := a.size - 1
  -- at most ~64 iterations for any realistic size; fuel = size + 1 is always enough
  for _ in [0:a.size + 1] do
    if lo ≤ hi then
      let i := lo + (hi - lo) / 2
      let c := compareF64 a[i.toNat]! v
      if c == 0 then return i
      if c < 0 then lo := i + 1 else hi := i - 1
  return -lo - 1

/-! ## `List<T>.Sort(Comparison<T>)` = `ArraySortHelper<T>.IntrospectiveSort` (.NET 10)

Unstable. `nestedHitObjects.Sort((h1, h2) => h1.StartTime.CompareTo(h2.StartTime))` in
`HitObject.ApplyDefaults` (`HitObject.cs:130`) uses it, so the relative order of nested objects with
equal start times is whatever introsort produces. Faithful transcription of
`src/libraries/System.Private.CoreLib/src/System/Collections/Generic/ArraySortHelper.cs`
(`IntroSort`, `PickPivotAndPartition`, `InsertionSort`, `HeapSort`, `DownHeap`), operating on the
sub-range `[lo, lo+len)` of an array. Checked against .NET with `bmtest sorttest`. -/
namespace IntroSort

variable {α : Type} [Inhabited α] (cmp : α → α → Int)

def swap (a : Array α) (i j : Nat) : Array α :=
  let t := a[i]!
  (a.set! i a[j]!).set! j t

def swapIfGreater (a : Array α) (i j : Nat) : Array α :=
  if cmp a[i]! a[j]! > 0 then swap a i j else a

def insertionSort (a : Array α) (lo len : Nat) : Array α := Id.run do
  let mut a := a
  for i in [0:len - 1] do
    let t := a[lo + i + 1]!
    let mut j : Int := i
    let mut go := true
    for _ in [0:i + 1] do
      if go then
        if j ≥ 0 && cmp t a[lo + j.toNat]! < 0 then
          a := a.set! (lo + j.toNat + 1) a[lo + j.toNat]!
          j := j - 1
        else go := false
    a := a.set! (lo + (j + 1).toNat) t
  return a

def downHeap (a : Array α) (lo : Nat) (i0 n : Nat) : Array α := Id.run do
  let mut a := a
  let d := a[lo + i0 - 1]!
  let mut i := i0
  let mut go := true
  for _ in [0:n + 1] do
    if go && i ≤ n / 2 then
      let mut child := 2 * i
      if child < n && cmp a[lo + child - 1]! a[lo + child]! < 0 then child := child + 1
      if !(cmp d a[lo + child - 1]! < 0) then go := false
      else
        a := a.set! (lo + i - 1) a[lo + child - 1]!
        i := child
  a := a.set! (lo + i - 1) d
  return a

def heapSort (a : Array α) (lo n : Nat) : Array α := Id.run do
  let mut a := a
  let mut i := n / 2
  for _ in [0:n / 2] do
    a := downHeap cmp a lo i n
    i := i - 1
  let mut k := n
  for _ in [0:n - 1] do
    a := swap a lo (lo + k - 1)
    a := downHeap cmp a lo 1 (k - 1)
    k := k - 1
  return a

/-- Returns the partitioned array and the pivot position (relative to `lo`). -/
def pickPivotAndPartition (a : Array α) (lo len : Nat) : Array α × Nat := Id.run do
  let hi := len - 1
  let middle := hi / 2
  let mut a := swapIfGreater cmp a lo (lo + middle)
  a := swapIfGreater cmp a lo (lo + hi)
  a := swapIfGreater cmp a (lo + middle) (lo + hi)
  let pivot := a[lo + middle]!
  a := swap a (lo + middle) (lo + hi - 1)
  let mut left := 0
  let mut right := hi - 1
  for _ in [0:len + 1] do
    if left < right then
      -- while (comparer(keys[++left], pivot) < 0) ;
      left := left + 1
      let mut go := true
      for _ in [0:len] do
        if go then
          if cmp a[lo + left]! pivot < 0 then left := left + 1 else go := false
      -- while (comparer(pivot, keys[--right]) < 0) ;
      right := right - 1
      go := true
      for _ in [0:len] do
        if go then
          if cmp pivot a[lo + right]! < 0 then right := right - 1 else go := false
      if left < right then a := swap a (lo + left) (lo + right)
  if left != hi - 1 then a := swap a (lo + left) (lo + hi - 1)
  return (a, left)

/-- `IntroSort(keys[lo..lo+len), depthLimit)` -/
def introSort (a : Array α) (lo len depthLimit : Nat) : Nat → Array α
  | 0 => a
  | fuel + 1 => Id.run do
    let mut a := a
    let mut partitionSize := len
    let mut depth := depthLimit
    for _ in [0:len + 1] do
      if partitionSize > 1 then
        if partitionSize ≤ 16 then
          if partitionSize == 2 then
            return swapIfGreater cmp a lo (lo + 1)
          if partitionSize == 3 then
            a := swapIfGreater cmp a lo (lo + 1)
            a := swapIfGreater cmp a lo (lo + 2)
            return swapIfGreater cmp a (lo + 1) (lo + 2)
          return insertionSort cmp a lo partitionSize
        if depth == 0 then
          return heapSort cmp a lo partitionSize
        depth := depth - 1
        let (a', p) := pickPivotAndPartition cmp a lo partitionSize
        a := introSort a' (lo + p + 1) (partitionSize - (p + 1)) depth fuel
        partitionSize := p
    return a

/-- `BitOperations.Log2((uint)n)` for `n ≥ 1`. -/
def log2 (n : Nat) : Nat := Nat.log2 n

end IntroSort

/-- `List<T>.Sort(Comparison<T> cmp)` (introspective sort, unstable). -/
def listSort {α : Type} [Inhabited α] (cmp : α → α → Int) (a : Array α) : Array α :=
  if a.size > 1 then
    IntroSort.introSort cmp a 0 a.size (2 * (IntroSort.log2 a.size + 1)) (a.size + 1)
  else a

/-- Stable sort by key (LINQ `OrderBy(key)`; `Comparer<double>.Default` = `double.CompareTo`). -/
def stableSortBy {α : Type} (key : α → F64) (a : Array α) : Array α :=
  -- insertion sort on (key, index) is stable; use merge sort for O(n log n)
  let rec merge (xs ys : List α) (fuel : Nat) : List α :=
    match fuel, xs, ys with
    | 0, xs, ys => xs ++ ys
    | _, [], ys => ys
    | _, xs, [] => xs
    | f + 1, x :: xs', y :: ys' =>
      if compareF64 (key y) (key x) < 0 then y :: merge (x :: xs') ys' f else x :: merge xs' (y :: ys') f
  let rec sort (xs : List α) (fuel : Nat) : List α :=
    match fuel with
    | 0 => xs
    | f + 1 =>
      if xs.length ≤ 1 then xs
      else
        let n := xs.length / 2
        merge (sort (xs.take n) f) (sort (xs.drop n) f) (xs.length + 1)
  (sort a.toList (a.size + 1)).toArray

/-! ## `Enum.TryParse<TEnum>(string, out TEnum)` (case-sensitive, int-backed enums)

Behaviour pinned with `bmtest probe` (.NET 10.0.13):
* leading `char.IsWhiteSpace` is trimmed;
* if the first remaining char is an ASCII digit, `+` or `-`, the string is parsed as an `Int32`
  (trailing ASCII white space allowed); any int value is accepted (even undefined members);
  on failure the parse fails;
* otherwise it is a `,`-separated list of member names (each trimmed, case-sensitive), OR-ed;
* on failure the out value is `default` (0). -/
def enumTryParse (names : List (String × Int32)) (s : String) : Option Int32 :=
  let t := trimStart s
  match t.toList with
  | [] => none
  | c :: _ =>
    if Parse.isDigit c || c == '+' || c == '-' then
      match intParse t with
      | .ok v => some v
      | .error _ => none
    else
      let parts := t.splitOn ","
      parts.foldl (fun acc p =>
        match acc with
        | none => none
        | some v =>
          match names.find? (fun (n, _) => n == trim p) with
          | some (_, x) => some (v ||| x)
          | none => none) (some 0)

end OsuModel.Beatmap
