import OsuModel.Beatmap.HitObjectParser
import OsuModel.Beatmap.Text

/-!
# `LegacyBeatmapDecoder` (`osu.Game/Beatmaps/Formats/LegacyBeatmapDecoder.cs`, `LegacyDecoder.cs`, `Decoder.cs`)

`decode : ByteArray → DecodeM DecodedBeatmap` mirrors
`Decoder.GetDecoder<Beatmap>(reader).Decode(reader)` as used by `WorkingBeatmapCache` /
`FlatWorkingBeatmap`, restricted to the state relevant to osu! gameplay:
format version, ruleset (`Mode`), `StackLeniency`, `[Difficulty]`, breaks, timing and difficulty
control points, and hit objects. Lines of all other kinds (metadata, colours, editor, storyboard
events, samples) cannot influence that state; they can only throw, which drops just that line.

Environment assumption (as in the game): rulesets 0–3 are available (`RulesetStore.GetRuleset`).
-/

namespace OsuModel.Beatmap
open OsuModel.Net

/-- `LegacyDecoder<T>.Section` enum members (`LegacyDecoder.cs:172-186`). -/
def sectionNames : List (String × Int32) :=
  [("General", 0), ("Editor", 1), ("Metadata", 2), ("Difficulty", 3), ("Events", 4), ("TimingPoints", 5),
   ("Colours", 6), ("HitObjects", 7), ("Variables", 8), ("Fonts", 9), ("CatchTheBeat", 10), ("Mania", 11)]

/-- `LegacyEventType` members (`osu.Game/Beatmaps/Legacy/LegacyEventType.cs`). -/
def eventTypeNames : List (String × Int32) :=
  [("Background", 0), ("Video", 1), ("Break", 2), ("Colour", 3), ("Sprite", 4), ("Sample", 5), ("Animation", 6)]

/-- `LegacyBeatmapDecoder.EARLY_VERSION_TIMING_OFFSET` -/
def EARLY_VERSION_TIMING_OFFSET : Int32 := 24
/-- `LegacyDecoder.LATEST_VERSION` -/
def LATEST_VERSION : Int32 := 14
/-- `LegacyBeatmapDecoder.MAX_MANIA_KEY_COUNT` -/
def MAX_MANIA_KEY_COUNT : F32 := 18

/-- Control points waiting in `pendingControlPoints` (`LegacyBeatmapDecoder.cs:571-603`), split by
type but keeping list order (timing-change lines are inserted at the front, others appended). -/
structure Pending where
  timing : List TimingPoint := []
  difficulty : List DifficultyPoint := []
  effect : List EffectPoint := []
  time : F64 := 0
deriving Inhabited, Repr

/-- Decoder state. -/
structure DecoderState where
  formatVersion : Int32
  offset : Int32
  sect : Int32 := 0
  rulesetId : Int32 := 0
  stackLeniency : F32 := 0.7
  audioLeadIn : F64 := 0
  difficulty : Difficulty := {}
  hasApproachRate : Bool := false
  cpi : ControlPointInfo := {}
  pending : Pending := {}
  breaks : Array BreakPeriod := #[]
  parser : ParserState
  hitObjects : Array ConvertHitObject := #[]
deriving Inhabited, Repr

namespace LegacyBeatmapDecoder

/-- `getOffsetTime(double time) => time + offset` (`:617`) -/
def offsetTime (s : DecoderState) (t : F64) : F64 := t + F64.ofInt s.offset.toInt

/-- `flushPendingPoints()` (`:589-603`): iterating the pending list backwards, the first point of
each type wins, i.e. the *last* list element of each type. -/
def flushPendingPoints (s : DecoderState) : DecoderState :=
  let t := s.pending.time
  let cpi := match s.pending.timing.getLast? with
    | some p => s.cpi.addTiming { p with time := t }
    | none => s.cpi
  let cpi := match s.pending.difficulty.getLast? with
    | some p => cpi.addDifficulty { p with time := t }
    | none => cpi
  let cpi := match s.pending.effect.getLast? with
    | some p => cpi.addEffect { p with time := t }
    | none => cpi
  { s with cpi, pending := { s.pending with timing := [], difficulty := [], effect := [] } }

/-- `addControlPoint(time, point, timingChange)` for one line's timing/difficulty points (`:576-587`).
The flush check happens on the first call of the line; later calls of the line have equal time. -/
def addLinePoints (s : DecoderState) (time : F64) (timing : Option TimingPoint) (diff : DifficultyPoint)
    (eff : EffectPoint) (timingChange : Bool) : DecoderState :=
  let s := if !(time == s.pending.time) then flushPendingPoints s else s
  let pTiming := match timing with
    | some tp => tp :: s.pending.timing      -- Insert(0, ...)
    | none => s.pending.timing
  let pDiff := if timingChange then diff :: s.pending.difficulty else s.pending.difficulty ++ [diff]
  let pEff := if timingChange then eff :: s.pending.effect else s.pending.effect ++ [eff]
  { s with pending := { timing := pTiming, difficulty := pDiff, effect := pEff, time } }

/-- `handleGeneral(line)` (`:244-309`): only `AudioLeadIn`, `StackLeniency` and `Mode` matter. -/
def handleGeneral (s : DecoderState) (line : String) : DecodeM DecoderState := do
  let (key, value) := splitKeyVal line
  match key with
  | "AudioLeadIn" =>
    let v ← liftNet "AudioLeadIn" (Parsing.parseInt value)
    return { s with audioLeadIn := F64.ofInt32 v }
  | "StackLeniency" => return { s with stackLeniency := ← liftNet "StackLeniency" (Parsing.parseFloat value) }
  | "Mode" =>
    let id ← liftNet "Mode" (Parsing.parseInt value)
    -- `RulesetStore?.GetRuleset(id) ?? throw new ArgumentException(...)`
    if 0 ≤ id && id ≤ 3 then return { s with rulesetId := id } else throw "Ruleset is not available locally."
  | _ => return s

/-- `handleDifficulty(line)` (`:401-436`) -/
def handleDifficulty (s : DecoderState) (line : String) : DecodeM DecoderState := do
  let (key, value) := splitKeyVal line
  let d := s.difficulty
  match key with
  | "HPDrainRate" => return { s with difficulty := { d with drainRate := ← liftNet key (Parsing.parseFloat value) } }
  | "CircleSize" => return { s with difficulty := { d with circleSize := ← liftNet key (Parsing.parseFloat value) } }
  | "OverallDifficulty" =>
    let od ← liftNet key (Parsing.parseFloat value)
    let d := { d with overallDifficulty := od }
    let d := if !s.hasApproachRate then { d with approachRate := od } else d
    return { s with difficulty := d }
  | "ApproachRate" =>
    let ar ← liftNet key (Parsing.parseFloat value)
    return { s with difficulty := { d with approachRate := ar }, hasApproachRate := true }
  | "SliderMultiplier" => return { s with difficulty := { d with sliderMultiplier := ← liftNet key (Parsing.parseDouble value) } }
  | "SliderTickRate" => return { s with difficulty := { d with sliderTickRate := ← liftNet key (Parsing.parseDouble value) } }
  | _ => return s

/-- Insert a break into the `SortedList<BreakPeriod>` (order: `StartTime`, then `EndTime`). -/
def insertBreak (bs : Array BreakPeriod) (b : BreakPeriod) : Array BreakPeriod :=
  let lt (x y : BreakPeriod) : Bool :=
    compareF64 x.startTime y.startTime < 0 || (compareF64 x.startTime y.startTime == 0 && compareF64 x.endTime y.endTime < 0)
  let i := (bs.findIdx? (fun q => lt b q)).getD bs.size
  bs.insertIdx! i b

/-- `handleEvent(line)` (`:438-482`): only breaks matter. -/
def handleEvent (s : DecoderState) (line : String) : DecodeM DecoderState := do
  let split := Beatmap.split line ','
  match enumTryParse eventTypeNames split[0]! with
  | some 2 =>
    let start := offsetTime s (← liftNet "break start" (Parsing.parseDouble (← at! split 1)))
    let endT := F64.max start (offsetTime s (← liftNet "break end" (Parsing.parseDouble (← at! split 2))))
    return { s with breaks := insertBreak s.breaks ⟨start, endT⟩ }
  | _ => return s

/-- `handleTimingPoint(line)` (`:484-569`) -/
def handleTimingPoint (s : DecoderState) (line : String) : DecodeM DecoderState := do
  let split := Beatmap.split line ','
  let time := offsetTime s (← liftNet "time" (Parsing.parseDouble (trim (← at! split 0))))
  -- beatLength is allowed to be NaN
  let beatLength ← liftNet "beatLength" (Parsing.parseDouble (trim (← at! split 1)) Parsing.MAX_PARSE_VALUE true)
  let speedMultiplier : F64 := if beatLength < 0 then 100.0 / -beatLength else 1
  let mut timeSignature : Int32 := 4
  if split.size ≥ 3 then
    if (← char0 split[2]!) != '0' then
      let n ← liftNet "timeSignature" (Parsing.parseInt split[2]!)
      if n ≤ 0 then throw "TimeSignature numerator must be positive"
      timeSignature := n
  if split.size ≥ 4 then let _ ← liftNet "sampleSet" (Parsing.parseInt split[3]!)
  if split.size ≥ 5 then let _ ← liftNet "customSampleBank" (Parsing.parseInt split[4]!)
  if split.size ≥ 6 then let _ ← liftNet "sampleVolume" (Parsing.parseInt split[5]!)
  let mut timingChange := true
  if split.size ≥ 7 then timingChange := (← char0 split[6]!) == '1'
  let mut kiai := false
  if split.size ≥ 8 then
    let flags ← liftNet "effectFlags" (Parsing.parseInt split[7]!)
    kiai := flags &&& 1 != 0
  let mut timing : Option TimingPoint := none
  if timingChange then
    if beatLength.isNaN then throw "Beat length cannot be NaN in a timing control point"
    timing := some { time, beatLength := clampBeatLength beatLength, timeSignature }
  let diff : DifficultyPoint :=
    { time, sliderVelocity := clampSV speedMultiplier, generateTicks := !beatLength.isNaN }
  -- osu!taiko and osu!mania use effect points for scroll speed (`:543-548`)
  let eff : EffectPoint :=
    { time, kiai, scrollSpeed := if s.rulesetId == 1 || s.rulesetId == 3 then clampScrollSpeed speedMultiplier else 1 }
  return addLinePoints s time timing diff eff timingChange

/-- `handleHitObject(line)` (`:605-611`). The parser state advances even on failure (see
`HitObjectParser.lean`). The decode-time `obj.ApplyDefaults` cannot throw for `Convert*` objects. -/
def handleHitObject (s : DecoderState) (line : String) : DecoderState :=
  let (p, r) := ConvertHitObjectParser.parse s.parser line
  match r with
  | .ok o => { s with parser := p, hitObjects := s.hitObjects.push o }
  | .error _ => { s with parser := p }

/-- `ParseLine(...)` dispatch (`LegacyBeatmapDecoder.cs:208-242`). Sections other than these
(Editor, Metadata, Colours, Variables, …) cannot affect the modelled state. -/
def parseLine (s : DecoderState) (line : String) : DecoderState :=
  let r : DecodeM DecoderState :=
    match s.sect with
    | 0 => handleGeneral s line
    | 3 => handleDifficulty s line
    | 4 => handleEvent s line
    | 5 => handleTimingPoint s line
    | 7 => .ok (handleHitObject s line)
    | _ => .ok s
  -- `catch (Exception e) { Logger.Log(...) }` (`LegacyDecoder.cs:69-77`)
  match r with
  | .ok s' => s'
  | .error _ => s

/-- `ShouldSkipLine(line)` (`LegacyDecoder.cs:81`) -/
def shouldSkipLine (line : String) : Bool :=
  isNullOrWhiteSpace line || (trimStart line).startsWith "//"

/-- `StripComments(line)` (`LegacyDecoder.cs:101-108`): cut at the first `//` if its index is > 0. -/
def stripComments (line : String) : String :=
  match (line.splitOn "//") with
  | first :: _ :: _ => if first.isEmpty then line else first
  | _ => line

/-- The line loop of `LegacyDecoder.ParseStreamInto` (`LegacyDecoder.cs:38-79`). -/
def parseLines (s0 : DecoderState) (lines : Array String) : DecoderState := Id.run do
  let mut s := s0
  for line0 in lines do
    if shouldSkipLine line0 then continue
    let line1 := if s.sect != 2 then stripComments line0 else line0
    let line := trimEnd line1
    if line.startsWith "[" && line.endsWith "]" then
      -- `Enum.TryParse(line[1..^1], out section)`: on failure `section = default` (General)
      let inner := String.ofList ((line.toList.drop 1).dropLast)
      s := { s with sect := (enumTryParse sectionNames inner).getD 0 }
      continue
    s := parseLine s line
  return s

/-- `applyDifficultyRestrictions` (`LegacyBeatmapDecoder.cs:118-132`) -/
def applyDifficultyRestrictions (d : Difficulty) (rulesetId : Int32) : Difficulty :=
  let clamp32 (v lo hi : F32) : F32 := if v < lo then lo else if hi < v then hi else v
  let clamp64 (v lo hi : F64) : F64 := if v < lo then lo else if hi < v then hi else v
  { drainRate := clamp32 d.drainRate 0 10
    circleSize := if rulesetId != 3 then clamp32 d.circleSize 0 10 else clamp32 d.circleSize 1 MAX_MANIA_KEY_COUNT
    overallDifficulty := clamp32 d.overallDifficulty 0 10
    approachRate := clamp32 d.approachRate 0 10
    sliderMultiplier := clamp64 d.sliderMultiplier 0.4 3.6
    sliderTickRate := clamp64 d.sliderTickRate 0.5 8 }

/-- `postProcessBreaks` (`:137-153`): new combo on the first object after each break. -/
def postProcessBreaks (breaks : Array BreakPeriod) (hos : Array ConvertHitObject) : Array ConvertHitObject := Id.run do
  let mut currentBreak := 0
  let mut out := #[]
  for h in hos do
    let mut force := false
    for _ in [0:breaks.size] do
      if currentBreak < breaks.size && breaks[currentBreak]!.endTime < h.startTime then
        force := true
        currentBreak := currentBreak + 1
    out := out.push { h with newCombo := h.newCombo || force }
  return out

/-- `applyDefaults(hitObject)` (`:155-166`): `GenerateTicks` / `SliderVelocityMultiplier` of
sliders from `DifficultyPointAt(StartTime)`. (The subsequent `ApplyDefaults` on the
`Convert*` object has no persistent effect on the modelled fields.) -/
def applyDecodeDefaults (cpi : ControlPointInfo) (h : ConvertHitObject) : ConvertHitObject :=
  match h.kind with
  | .slider .. =>
    let dp := cpi.difficultyPointAt h.startTime
    { h with generateTicks := dp.generateTicks, sliderVelocityMultiplier := dp.sliderVelocity }
  | _ => h

/-- `LegacyBeatmapDecoder.ParseStreamInto` (`:85-112`) for a decoder of the given version. -/
def parseStreamInto (formatVersion : Int32) (lines : Array String) : DecodedBeatmap :=
  let offset : Int32 := if formatVersion < 5 then EARLY_VERSION_TIMING_OFFSET else 0
  let s0 : DecoderState :=
    { formatVersion, offset, parser := { offset := F64.ofInt offset.toInt, formatVersion } }
  let s := parseLines s0 lines
  let difficulty := applyDifficultyRestrictions s.difficulty s.rulesetId
  let s := flushPendingPoints s
  let hos := stableSortBy (·.startTime) s.hitObjects
  let hos := postProcessBreaks s.breaks hos
  let hos := hos.map (applyDecodeDefaults s.cpi)
  { formatVersion, rulesetId := s.rulesetId, difficulty, stackLeniency := s.stackLeniency,
    audioLeadIn := s.audioLeadIn, controlPoints := s.cpi, breaks := s.breaks, hitObjects := hos }

/-- `Decoder.GetDecoder<Beatmap>(stream)` + `Decode(stream)` (`Decoder.cs:54-87`,
`LegacyBeatmapDecoder.Register`, `:53-57`). -/
def decode (bytes : ByteArray) : DecodeM DecodedBeatmap := do
  let some chars := streamReaderDecode bytes | throw "unsupported text encoding (UTF-32 / unpaired surrogate)"
  let lines := readLines chars
  -- skip (consume) leading lines that are empty after Trim()
  let k := (lines.findIdx? (fun l => !(trim l).isEmpty)).getD lines.size
  if k ≥ lines.size then throw "Unknown file format (no content)"
  let first := trim lines[k]!
  let rest := lines.extract k lines.size
  if first.startsWith "osu file format v" then
    -- `Parsing.ParseInt(m.Split('v').Last())`
    let lastPart := (Beatmap.split first 'v').back!
    let version ← liftNet "format version" (Parsing.parseInt lastPart)
    return parseStreamInto version rest
  else if first.startsWith "{" then
    throw "JSON beatmap (JsonBeatmapDecoder) not modelled"
  else
    -- fallback decoder: `new LegacyBeatmapDecoder()` (version = LATEST_VERSION)
    return parseStreamInto LATEST_VERSION rest

end LegacyBeatmapDecoder
end OsuModel.Beatmap
