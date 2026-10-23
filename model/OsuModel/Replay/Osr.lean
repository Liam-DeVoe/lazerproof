import OsuModel.Beatmap.Text
import OsuModel.Beatmap.ModSettings
import OsuModel.Sim.ModsJson
import OsuModel.Sim.Basic

/-!
# `.osr` container decoding (`LegacyScoreDecoder.Parse`)

Mirrors `osu.Game/Scoring/Legacy/LegacyScoreDecoder.cs:37-193` (lazer 2026.1005.0) for the osu! ruleset, as driven
by the oracle (`oracle/Program.cs` `OracleScoreDecoder`: `GetBeatmap` always returns the given beatmap):

* header fields read with `SerializationReader` (`osu.Game/IO/Legacy/SerializationReader.cs`, a `BinaryReader`
  with UTF-8): ruleset byte, version, beatmap hash, player name, replay hash, six counts, score, max combo,
  perfect flag, legacy mods bitfield, HP graph, date, compressed replay, online id (version-dependent width),
  compressed lazer score info (version ≥ 30000001);
* `OsuRuleset.ConvertFromLegacyMods` (`osu.Game.Rulesets.Osu/OsuRuleset.cs:96-148`) and the automatic
  `ModClassic` for stable replays (version < `FIRST_LAZER_VERSION = 30000000`, `LegacyScoreDecoder.cs:88-92`,
  `LegacyScoreEncoder.cs:74`);
* the LZMA payloads (`readCompressedData`, `:168-193`) — **trusted boundary**: decompressed by the system liblzma
  through `c/lzma_shim.c` (lazer: SharpCompress `LzmaStream`; same `.lzma` "alone" format);
* the lazer score info JSON (`LegacyReplaySoloScoreInfo`, `osu.Game/Scoring/Legacy/LegacyReplaySoloScoreInfo.cs`):
  only `mods` (with settings) influences evaluation — it *replaces* the bitfield mods (`:134`). The other members
  (statistics, maximum statistics, rank, ids, client version, total score without mods, pauses) only feed the
  decoded `ScoreInfo`, which replay playback never reads; they are type-checked here only because a Newtonsoft
  deserialisation failure aborts the import (see `checkScoreInfo`).

The frame text itself is decoded by `OsuModel.Replay.decode` (`Replay/Frames.lean`).
-/

namespace OsuModel.Replay.Osr
open OsuModel.Net
open OsuModel.Beatmap (ModConfig JsonVal)

/-! ## LZMA (trusted) -/

/-- `.lzma` ("LZMA alone": 5 property bytes, 8-byte little-endian uncompressed size, LZMA stream) → bytes.
Implemented by liblzma's `lzma_alone_decoder` (`c/lzma_shim.c`); `maxOut` bounds the output size.
TRUSTED: not modelled in Lean (docs/model-eval.md, "Trust boundary"). -/
@[extern "osu_lzma_alone_decode"]
opaque lzmaAloneDecode (input : @& ByteArray) (maxOut : USize) : Except String ByteArray

/-- Output bound for one payload (stable replays are < 2 MB decompressed). -/
def maxPayload : USize := 268435456

/-! ## `SerializationReader` / `BinaryReader` over a byte array -/

abbrev RdM := ReaderT ByteArray (StateT Nat (Except String))

def readByte : RdM UInt8 := do
  let b ← read
  let p ← get
  if h : p < b.size then
    set (p + 1)
    return b[p]
  else throw "EndOfStreamException: Unable to read beyond the end of the stream."

/-- little-endian unsigned integer of `n` bytes -/
def readLE (n : Nat) : RdM Nat := do
  let b ← read
  let p ← get
  if hb : p + n ≤ b.size then
    let mut v := 0
    for hi : i in [0:n] do
      have hu : i < n := hi.upper
      v := v + (b[p + i]'(by omega)).toNat <<< (8 * i)
    set (p + n)
    return v
  else throw "EndOfStreamException: Unable to read beyond the end of the stream."

def readUInt16 : RdM Nat := readLE 2
def readInt32 : RdM Int32 := do return Int32.ofNat (← readLE 4)
def readInt64 : RdM Int64 := do return Int64.ofNat (← readLE 8)
/-- `BinaryReader.ReadBoolean` = `ReadByte() != 0` -/
def readBoolean : RdM Bool := do return (← readByte) != 0

/-- `BinaryReader.ReadBytes(count)`: returns fewer bytes at the end of the stream (no exception). -/
def readBytes (count : Nat) : RdM ByteArray := do
  let b ← read
  let p ← get
  let n := min count (b.size - p)
  set (p + n)
  return b.extract p (p + n)

/-- `BinaryReader.Read7BitEncodedInt` (.NET: at most 5 bytes, the 5th must be ≤ 0b1111). -/
def read7BitEncodedInt : RdM Int32 := do
  let mut result : Nat := 0
  for i in [0:4] do
    let b ← readByte
    result := result ||| ((b.toNat &&& 0x7F) <<< (7 * i))
    if b ≤ 0x7F then return Int32.ofNat result
  let b ← readByte
  if b > 0b1111 then throw "FormatException: Too many bytes in what should have been a 7-bit encoded integer."
  return Int32.ofNat (result ||| (b.toNat <<< 28))

/-- `SerializationReader.ReadString`: a zero byte = `null`; otherwise `BinaryReader.ReadString` (7-bit length,
UTF-8; replacement-character decoding as `Encoding.UTF8`). The string contents never influence evaluation. -/
def readString : RdM (Option String) := do
  if (← readByte) == 0 then return none
  let len ← read7BitEncodedInt
  if len < 0 then throw "IOException: Invalid string length"
  if len == 0 then return some ""
  let bs ← readBytes len.toNatClampNeg
  if bs.size < len.toNatClampNeg then throw "EndOfStreamException: Unable to read beyond the end of the stream."
  return some (String.ofList (OsuModel.Beatmap.decodeUtf8 bs 0).toList)

/-- `SerializationReader.ReadDateTime` (`:57-63`): negative ticks → `IOException`; `new DateTime(ticks, Utc)`
throws above `DateTime.MaxValue.Ticks`. -/
def readDateTime : RdM Int64 := do
  let t ← readInt64
  if t < 0 then throw "IOException: Bad ticks count read!"
  if t.toInt > 3155378975999999999 then throw "ArgumentOutOfRangeException: Ticks must be between DateTime.MinValue.Ticks and DateTime.MaxValue.Ticks."
  return t

/-- `SerializationReader.ReadByteArray` (`:36-43`): length > 0 → bytes, < 0 → `null`, 0 → empty. -/
def readByteArray : RdM (Option ByteArray) := do
  let len ← readInt32
  if len > 0 then return some (← readBytes len.toNatClampNeg)
  if len < 0 then return none
  return some ByteArray.empty

/-! ## Legacy mods -/

/-- `OsuRuleset.ConvertFromLegacyMods` (`OsuRuleset.cs:96-148`) as acronyms, in yield order. `HasFlag(f)` is
`(mods & f) == f` for these single-bit flags. -/
def convertFromLegacyMods (mods : Int32) : List String :=
  let m := mods.toUInt32
  let has (bit : Nat) : Bool := (m >>> bit.toUInt32) &&& 1 == 1
  (if has 9 then ["NC"] else if has 6 then ["DT"] else []) ++
  (if has 14 then ["PF"] else if has 5 then ["SD"] else []) ++
  (if has 13 then ["AP"] else []) ++
  (if has 22 then ["CN"] else if has 11 then ["AT"] else []) ++
  (if has 1 then ["EZ"] else []) ++
  (if has 10 then ["FL"] else []) ++
  (if has 8 then ["HT"] else []) ++
  (if has 4 then ["HR"] else []) ++
  (if has 3 then ["HD"] else []) ++
  (if has 0 then ["NF"] else []) ++
  (if has 7 then ["RX"] else []) ++
  (if has 12 then ["SO"] else []) ++
  (if has 23 then ["TP"] else []) ++
  (if has 2 then ["TD"] else []) ++
  (if has 29 then ["SV2"] else [])

/-- `LegacyScoreEncoder.FIRST_LAZER_VERSION` -/
def FIRST_LAZER_VERSION : Int32 := 30000000

/-! ## Container -/

/-- The fields of the `.osr` container that evaluation depends on (plus the beatmap hash, for reporting). -/
structure Container where
  rulesetId : UInt8
  version : Int32
  beatmapHash : Option String
  legacyMods : Int32
  compressedReplay : Option ByteArray
  compressedScoreInfo : Option ByteArray
deriving Inhabited

/-- `LegacyScoreDecoder.Parse` up to the end of the stream reads (`:47-118`). `GetRuleset(id)` of the oracle throws
for any ruleset other than osu! (0) right after the first byte. The decode-time `GetPlayableBeatmap` (`:94`) is
evaluated separately (`Eval`), since it only matters by throwing. -/
def readContainer : RdM Container := do
  let rulesetId ← readByte
  if rulesetId != 0 then throw s!"InvalidOperationException: only the osu! ruleset is supported (replay ruleset id {rulesetId})"
  let version ← readInt32
  let beatmapHash ← readString
  let _player ← readString
  let _md5 ← readString
  for _ in [0:6] do let _ ← readUInt16
  let _totalScore ← readInt32
  let _maxCombo ← readUInt16
  let _perfect ← readBoolean
  let legacyMods ← readInt32
  let _hpGraph ← readString
  let _date ← readDateTime
  let compressedReplay ← readByteArray
  if version ≥ 20140721 then let _ ← readInt64
  else if version ≥ 20121008 then let _ ← readInt32
  let compressedScoreInfo ← if version ≥ 30000001 then readByteArray else pure none
  return { rulesetId, version, beatmapHash, legacyMods, compressedReplay, compressedScoreInfo }

def parseContainer (bytes : ByteArray) : Except String Container :=
  (readContainer.run bytes).run' 0

/-- `readCompressedData` (`:168-193`) + `StreamReader(lzma).ReadToEnd()`: at least 13 header bytes, LZMA (trusted),
then `StreamReader` decoding (UTF-8 with BOM detection; `OsuModel.Beatmap.streamReaderDecode`). -/
def readCompressedText (data : ByteArray) : Except String String := do
  if data.size < 5 then throw "IOException: input .lzma is too short"
  if data.size < 13 then throw "IOException: Can't Read 1"
  let raw : ByteArray ← match lzmaAloneDecode data maxPayload with
    | .ok r => pure r
    | .error e => throw s!"lzma (trusted boundary): {e}"
  -- fast path: valid UTF-8 without a BOM decodes identically
  let hasBom := match (raw[0]? : Option UInt8), (raw[1]? : Option UInt8) with
    | some b0, some b1 => (b0 == 0xEF && b1 == 0xBB) || (b0 == 0xFE && b1 == 0xFF) || (b0 == 0xFF && b1 == 0xFE)
    | _, _ => false
  if !hasBom then
    if let some s := String.fromUTF8? raw then return s
  match OsuModel.Beatmap.streamReaderDecode raw with
  | some cs => return String.ofList cs.toList
  | none => throw "unsupported text encoding in compressed payload (UTF-32/invalid UTF-16; not modelled)"

/-! ## Lazer score info JSON (`LegacyReplaySoloScoreInfo`) -/

open SimJson (V) in
/-- Newtonsoft `ReadAsInt32`/`Int64` of an integer literal in range. -/
def jsonInt (v : V) (lo hi : Int) : Bool :=
  match v with
  | .num t =>
    !(t.any fun c => c == '.' || c == 'e' || c == 'E') &&
      (let n : Int := if t.startsWith "-" then -((t.drop 1).toNat! : Int) else (t.toNat! : Int)
       lo ≤ n && n ≤ hi)
  | _ => false

def i32lo : Int := -2147483648
def i32hi : Int := 2147483647
def i64lo : Int := -9223372036854775808
def i64hi : Int := 9223372036854775807

/-- `Enum` parsing as Newtonsoft does for enum names (case-insensitive) or integers. -/
def enumName (names : List String) (s : String) : Bool :=
  names.any (fun n => n.map Char.toLower == s.map Char.toLower) || (s.toInt?.isSome)

def scoreRankNames : List String := ["F", "D", "C", "B", "A", "S", "SH", "X", "XH"]

/-- `[EnumMember(Value = "...")]` of `HitResult` (`osu.Game/Rulesets/Scoring/HitResult.cs`): the snake_case names. -/
def snakeCase (s : String) : String := Id.run do
  let mut out := ""
  let mut first := true
  for c in s.toList do
    if c.isUpper && !first then out := out.push '_'
    out := out.push c.toLower
    first := false
  return out

/-- Dictionary keys accepted for `HitResult` (EnumMember values and member names, case-insensitive). -/
def hitResultKeys : List String :=
  OsuModel.Sim.HitResult.all.map (·.name) ++ OsuModel.Sim.HitResult.all.map (snakeCase ·.name)

open SimJson (V) in
/-- Type checks of the non-mod members (a Newtonsoft failure aborts `Parse`, i.e. the replay is rejected).
Not exhaustive: Newtonsoft's lenient conversions (e.g. numeric strings for integers) are not modelled. -/
def checkScoreInfo (kvs : List (String × V)) : Except String Unit := do
  for (k, v) in kvs do
    let bad := throw s!"JsonSerializationException: bad value for '{k}' in lazer score info"
    match k with
    | "statistics" | "maximum_statistics" =>
      match v with
      | .obj es =>
        for (rk, rv) in es do
          if !(enumName hitResultKeys rk) || !(jsonInt rv i32lo i32hi) then bad
      | .null => throw s!"NullReferenceException: '{k}' is null"
      | _ => bad
    | "online_id" => if !(jsonInt v i64lo i64hi) then bad
    | "user_id" => if !(jsonInt v i32lo i32hi) then bad
    | "total_score_without_mods" => match v with | .null => pure () | _ => if !(jsonInt v i64lo i64hi) then bad
    | "client_version" => match v with | .str _ | .null => pure () | _ => bad
    | "rank" => match v with
      | .null => pure ()
      | .str s => if !(enumName scoreRankNames s) then bad
      | _ => if !(jsonInt v i32lo i32hi) then bad
    | "pauses" => match v with
      | .arr xs => for x in xs do if !(jsonInt x i32lo i32hi) then bad
      | .null => throw "ArgumentNullException: pauses is null"
      | _ => bad
    | _ => pure ()

open SimJson (V) in
/-- One `APIMod` → `APIMod.ToMod(ruleset)` (`APIMod.cs:43-70`; `OsuModel.Beatmap.Settings.toMod`). -/
def apiModToMod (v : V) : Except String ModConfig := do
  match v with
  | .obj kvs =>
    let last (k : String) : Option V := (kvs.reverse.find? (·.1 == k)).map (·.2)
    let acronym ← match last "acronym" with
      | some (.str s) => pure (some s)
      | some (.num t) => pure (some t)
      | some (.bool b) => pure (some (if b then "True" else "False"))
      | some .null | none => pure none
      | _ => throw "JsonSerializationException: bad acronym"
    let settings ← match last "settings" with
      | some (.obj ss) => pure (ss.map fun (k, x) => (k, SimJson.toSetting x))
      | none => pure []
      | some .null => throw "NullReferenceException: mod settings are null"
      | _ => throw "JsonSerializationException: bad mod settings"
    match acronym with
    | some a => return OsuModel.Beatmap.Settings.toMod a settings
    | none => return { acronym := "", known := false }
  | _ => throw "JsonSerializationException: mod is not an object"

/-- The lazer score info (`:123-146`): JSON text → mods (replacing the decoded bitfield mods). -/
def decodeScoreInfo (text : String) : Except String (List ModConfig) := do
  let (v, rest) : SimJson.V × List Char ← match (SimJson.value).run text.toList with
    | .ok r => pure r
    | .error e => throw s!"JsonReaderException: {e}"
  -- `JsonConvert.DeserializeObject`: additional non-whitespace content is an error
  if rest.any (fun c => !(c == ' ' || c == '\n' || c == '\t' || c == '\r')) then
    throw "JsonReaderException: Additional text encountered after finished reading JSON content."
  match v with
  | .obj kvs =>
    checkScoreInfo kvs
    let modsV : Option SimJson.V := (kvs.reverse.find? (·.1 == "mods")).map (·.2)
    match modsV with
    | none => return []   -- `Mods = Array.Empty<APIMod>()`
    | some (.arr xs) => xs.mapM apiModToMod
    | some .null => throw "NullReferenceException: mods is null"
    | some _ => throw "JsonSerializationException: mods is not an array"
  | .null => throw "NullReferenceException: lazer score info is null"
  | _ => throw "JsonSerializationException: lazer score info is not an object"

/-! ## Decoded score -/

structure DecodedScore where
  container : Container
  /-- `ScoreInfo.IsLegacyScore` (`version < 30000000`) -/
  isLegacyScore : Bool
  /-- Mods before the lazer JSON (bitfield + automatic Classic): the list the decode-time `GetPlayableBeatmap`
  sees (`:88-94`). -/
  bitfieldMods : List ModConfig
  /-- `ScoreInfo.Mods` after `Parse`. -/
  mods : List ModConfig
  /-- Decompressed frame text (`none`: no / empty replay payload). -/
  frameText : Option String
deriving Inhabited

/-- Decode everything except the frames' dependency on the beatmap (frame text parsing needs the beatmap
version, see `Replay.decode`). -/
def decode (bytes : ByteArray) : Except String DecodedScore := do
  let c ← parseContainer bytes
  let isLegacyScore := c.version < FIRST_LAZER_VERSION
  let legacy := (convertFromLegacyMods c.legacyMods).map (OsuModel.Beatmap.Settings.toMod · [])
  let bitfieldMods := if isLegacyScore then legacy ++ [OsuModel.Beatmap.Settings.toMod "CL" []] else legacy
  let frameText ← match c.compressedReplay with
    | some d => if d.size > 0 then some <$> readCompressedText d else pure none
    | none => pure none
  let mods ← match c.compressedScoreInfo with
    | some d => if d.size > 0 then decodeScoreInfo (← readCompressedText d) else pure bitfieldMods
    | none => pure bitfieldMods
  return { container := c, isLegacyScore, bitfieldMods, mods, frameText }

end OsuModel.Replay.Osr
