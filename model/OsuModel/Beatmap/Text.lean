import OsuModel.Beatmap.DotNet

/-!
# `StreamReader` text decoding and `ReadLine` (`osu.Game/IO/LineBufferedReader.cs`)

`LineBufferedReader` wraps `new StreamReader(stream, Encoding.UTF8, detectEncodingFromByteOrderMarks: true)`.

* BOM detection: `EF BB BF` → UTF-8 (BOM skipped); `FE FF` → UTF-16BE; `FF FE` → UTF-16LE
  (`FF FE 00 00` would be UTF-32LE and `00 00 FE FF` UTF-32BE — not modelled, reported as
  unsupported); otherwise UTF-8.
* Invalid UTF-8 is replaced by U+FFFD per *maximal subpart* (Unicode §3.9 / WHATWG; what
  `UTF8Encoding` with the default replacement fallback does since .NET Core 3.0).
* `ReadLine` splits on `\n`, `\r` and `\r\n`; a final line terminator does not start an extra line.

Unpaired UTF-16 surrogates cannot be represented by a Lean `String`; such input is reported as
unsupported (never observed in beatmaps).
-/

namespace OsuModel.Beatmap

/-- Decode UTF-8 bytes `[i, n)` with maximal-subpart U+FFFD replacement. -/
def decodeUtf8 (b : ByteArray) (start : Nat) : Array Char := Id.run do
  let n := b.size
  let mut out : Array Char := Array.mkEmpty n
  let mut i := start
  let repl : Char := '�'
  let cont (x : UInt8) : Bool := x &&& 0xC0 == 0x80
  for _ in [0:n + 1] do
    if i < n then
      let c0 := b[i]!
      if c0 < 0x80 then
        out := out.push (Char.ofNat c0.toNat); i := i + 1
      else if c0 < 0xC2 then
        out := out.push repl; i := i + 1
      else if c0 < 0xE0 then
        if i + 1 < n && cont b[i+1]! then
          out := out.push (Char.ofNat (((c0.toNat &&& 0x1F) <<< 6) ||| (b[i+1]!.toNat &&& 0x3F))); i := i + 2
        else
          out := out.push repl; i := i + 1
      else if c0 < 0xF0 then
        -- second byte range depends on the lead byte
        let lo : UInt8 := if c0 == 0xE0 then 0xA0 else 0x80
        let hi : UInt8 := if c0 == 0xED then 0x9F else 0xBF
        if i + 1 < n && lo ≤ b[i+1]! && b[i+1]! ≤ hi then
          if i + 2 < n && cont b[i+2]! then
            let cp := ((c0.toNat &&& 0x0F) <<< 12) ||| ((b[i+1]!.toNat &&& 0x3F) <<< 6) ||| (b[i+2]!.toNat &&& 0x3F)
            out := out.push (Char.ofNat cp); i := i + 3
          else
            out := out.push repl; i := i + 2
        else
          out := out.push repl; i := i + 1
      else if c0 < 0xF5 then
        let lo : UInt8 := if c0 == 0xF0 then 0x90 else 0x80
        let hi : UInt8 := if c0 == 0xF4 then 0x8F else 0xBF
        if i + 1 < n && lo ≤ b[i+1]! && b[i+1]! ≤ hi then
          if i + 2 < n && cont b[i+2]! then
            if i + 3 < n && cont b[i+3]! then
              let cp := ((c0.toNat &&& 0x07) <<< 18) ||| ((b[i+1]!.toNat &&& 0x3F) <<< 12) |||
                ((b[i+2]!.toNat &&& 0x3F) <<< 6) ||| (b[i+3]!.toNat &&& 0x3F)
              out := out.push (Char.ofNat cp); i := i + 4
            else
              out := out.push repl; i := i + 3
          else
            out := out.push repl; i := i + 2
        else
          out := out.push repl; i := i + 1
      else
        out := out.push repl; i := i + 1
  return out

/-- Decode UTF-16 code units (big- or little-endian) starting at `start`; `none` on an unpaired
surrogate. A trailing odd byte becomes U+FFFD. -/
def decodeUtf16 (b : ByteArray) (start : Nat) (bigEndian : Bool) : Option (Array Char) := Id.run do
  let n := b.size
  let unit (i : Nat) : Nat :=
    if bigEndian then b[i]!.toNat * 256 + b[i+1]!.toNat else b[i+1]!.toNat * 256 + b[i]!.toNat
  let mut out : Array Char := #[]
  let mut i := start
  for _ in [0:n + 1] do
    if i + 1 < n then
      let u := unit i
      if u < 0xD800 || u > 0xDFFF then
        out := out.push (Char.ofNat u); i := i + 2
      else if u ≤ 0xDBFF && i + 3 < n && 0xDC00 ≤ unit (i + 2) && unit (i + 2) ≤ 0xDFFF then
        out := out.push (Char.ofNat (0x10000 + ((u - 0xD800) <<< 10) + (unit (i + 2) - 0xDC00))); i := i + 4
      else return none
    else if i < n then
      out := out.push '�'; i := i + 1
  return some out

/-- The characters `StreamReader` produces for the given bytes, or `none` if unsupported. -/
def streamReaderDecode (b : ByteArray) : Option (Array Char) :=
  let n := b.size
  if n ≥ 4 && b[0]! == 0xFF && b[1]! == 0xFE && b[2]! == 0 && b[3]! == 0 then none
  else if n ≥ 4 && b[0]! == 0 && b[1]! == 0 && b[2]! == 0xFE && b[3]! == 0xFF then none
  else if n ≥ 2 && b[0]! == 0xFE && b[1]! == 0xFF then decodeUtf16 b 2 true
  else if n ≥ 2 && b[0]! == 0xFF && b[1]! == 0xFE then decodeUtf16 b 2 false
  else if n ≥ 3 && b[0]! == 0xEF && b[1]! == 0xBB && b[2]! == 0xBF then some (decodeUtf8 b 3)
  else some (decodeUtf8 b 0)

/-- Successive `StreamReader.ReadLine()` results. -/
def readLines (cs : Array Char) : Array String := Id.run do
  let mut lines : Array String := #[]
  let mut cur : String := ""
  let mut i := 0
  let n := cs.size
  let mut pending := false   -- whether `cur` holds a started line
  for _ in [0:n + 1] do
    if i < n then
      let c := cs[i]!
      if c == '\n' then
        lines := lines.push cur; cur := ""; pending := false; i := i + 1
      else if c == '\r' then
        lines := lines.push cur; cur := ""; pending := false
        i := if i + 1 < n && cs[i+1]! == '\n' then i + 2 else i + 1
      else
        cur := cur.push c; pending := true; i := i + 1
  if pending then lines := lines.push cur
  return lines

end OsuModel.Beatmap
