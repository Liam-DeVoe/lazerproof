import OsuModel.Beatmap.SliderPath

/-!
# `ConvertHitObjectParser` (`osu.Game/Rulesets/Objects/Legacy/ConvertHitObjectParser.cs`)

Parses one `[HitObjects]` line into a `ConvertHitObject`. Any exception makes the decoder drop
the line (`LegacyDecoder.cs:69-77`), so the model returns `Except String`. Hit sounds and sample
banks are not modelled except for whether parsing them throws (which drops the line).

Parser state that survives a failed line (faithful to C#): `createHitCircle` / `createSpinner`
assign `lastObject` *before* the sample-bank fields are parsed, so e.g. a spinner line whose
sample field is malformed is dropped but still forces a new combo on the next object
(`lastObject is ConvertSpinner`). `firstObject` is only cleared on success.
-/

namespace OsuModel.Beatmap
open OsuModel.Net

/-- `LegacyBeatmapEncoder.FIRST_LAZER_VERSION` -/
def FIRST_LAZER_VERSION : Int32 := 128

/-- Errors of the decoder / converter (the message is informational only). -/
abbrev DecodeM := Except String

def liftNet {α : Type} (what : String) : Except NetExn α → DecodeM α
  | .ok a => .ok a
  | .error e => .error s!"{what}: {repr e}"

/-- `array[i]` (throws `IndexOutOfRangeException`). -/
def at! (a : Array String) (i : Nat) : DecodeM String :=
  if h : i < a.size then .ok a[i] else .error s!"index {i} out of range"

/-- `s[0]` -/
def char0 (s : String) : DecodeM Char :=
  match s.toList with
  | c :: _ => .ok c
  | [] => .error "index 0 out of range (empty string)"

/-- Parser state (`ConvertHitObjectParser` fields). -/
structure ParserState where
  offset : F64
  formatVersion : Int32
  firstObject : Bool := true
  /-- `lastObject is ConvertSpinner` -/
  lastObjectIsSpinner : Bool := false
deriving Inhabited, Repr

namespace ConvertHitObjectParser

/-- `readCustomSampleBanks(str, bankInfo, banksOnly)` (`:194-235`): only whether it throws matters. -/
def readCustomSampleBanks (str : String) (banksOnly : Bool := false) : DecodeM Unit := do
  if str.isEmpty then return
  let split := Beatmap.split str ':'
  let _ ← liftNet "bank" (Parsing.parseInt (← at! split 0))
  let _ ← liftNet "addBank" (Parsing.parseInt (← at! split 1))
  if banksOnly then return
  if split.size > 2 then
    let _ ← liftNet "customSampleBank" (Parsing.parseInt split[2]!)
  if split.size > 3 then
    let _ ← liftNet "volume" (Parsing.parseInt split[3]!)
  return

/-- `convertPathType(input)` (`:237-257`). -/
def convertPathType (input : String) : DecodeM PathType := do
  let c ← char0 input
  match c with
  | 'B' =>
    if input.length > 1 then
      match intParse (String.ofList (input.toList.drop 1)) with
      | .ok d => if d > 0 then return .bspline (some d) else return .bspline none
      | .error _ => return .bspline none
    else return .bspline none
  | 'L' => return .linear
  | 'P' => return .perfectCurve
  | _ => return .catmull   -- `default: case 'C':`

/-- A coordinate: `ParseFloat(s, MAX_COORDINATE_VALUE)`, truncated to `int` (then back to `float`)
for format versions below `FIRST_LAZER_VERSION` (`:56-59`, `:342-344`). -/
def parseCoord (formatVersion : Int32) (s : String) : DecodeM F32 := do
  let v ← liftNet "coordinate" (Parsing.parseFloat s (F32.ofInt Parsing.MAX_COORDINATE_VALUE.toInt))
  if formatVersion ≥ FIRST_LAZER_VERSION then return v
  else return F32.ofInt32 (F32.toInt32 v)

/-- `readPoint(value, startPos)` (`:338-347`) -/
def readPoint (formatVersion : Int32) (value : String) (startPos : Vec2) : DecodeM Vec2 := do
  let vs := Beatmap.split value ':'
  let x ← parseCoord formatVersion (← at! vs 0)
  let y ← parseCoord formatVersion (← at! vs 1)
  return Vec2.mk x y - startPos

/-- `isLinear(p0, p1, p2)` (`:424-426`): `Precision.AlmostEquals(0, cross)` (float). -/
def isLinear (p0 p1 p2 : Vec2) : Bool :=
  Precision.almostEqualsF32 0 ((p1.y - p0.y) * (p2.x - p0.x) - (p1.x - p0.x) * (p2.y - p0.y))

/-- `convertPoints(type, points, endPoint)` (`:357-427`): the concatenation of the yielded segments.
Throws (`vertices[0]`) for an empty point list. -/
def convertPoints (formatVersion : Int32) (type0 : PathType) (points : Array Vec2) (endPoint : Option Vec2) :
    DecodeM (Array PathControlPoint) := do
  let mut vertices : Array PathControlPoint := points.map fun p => { position := p }
  let mut type := type0
  if type == .perfectCurve then
    let endPointLength := if endPoint.isSome then 1 else 0
    if formatVersion < FIRST_LAZER_VERSION then
      if vertices.size + endPointLength != 3 then type := .bspline none
      else if isLinear points[0]! points[1]! (endPoint.getD points[2]!) then type := .linear
    else if vertices.size + endPointLength > 3 then type := .bspline none
  if vertices.size == 0 then throw "index 0 out of range (no vertices)"
  vertices := vertices.set! 0 { vertices[0]! with type := some type }
  let mut out : Array PathControlPoint := #[]
  let mut startIndex := 0
  let mut endIndex := 0
  for _ in [0:vertices.size] do
    endIndex := endIndex + 1
    if endIndex < vertices.size then
      if !(Vec2.eq vertices[endIndex]!.position vertices[endIndex - 1]!.position) then continue
      if type == .catmull && endIndex > 1 && formatVersion < FIRST_LAZER_VERSION then continue
      if endIndex == vertices.size - 1 then continue
      vertices := vertices.set! (endIndex - 1) { vertices[endIndex - 1]! with type := some type }
      out := out ++ vertices.extract startIndex endIndex
      startIndex := endIndex + 1
  -- here endIndex = vertices.size
  if startIndex < endIndex then
    out := out ++ vertices.extract startIndex endIndex
  return out

/-- `convertPathString(pointString, offset)` (`:280-348`). -/
def convertPathString (formatVersion : Int32) (pointString : String) (offset : Vec2) :
    DecodeM (Array PathControlPoint) := do
  let parts := Beatmap.split pointString '|'
  let mut points : Array Vec2 := #[]
  let mut segments : Array (PathType × Nat) := #[]
  for s in parts do
    let c ← char0 s
    if charIsLetter c then
      let pathType ← convertPathType s
      segments := segments.push (pathType, points.size)
      if points.size == 0 then points := points.push Vec2.zero
    else
      points := points.push (← readPoint formatVersion s offset)
  let mut controlPoints : Array PathControlPoint := #[]
  for i in [0:segments.size] do
    let (type, startIndex) := segments[i]!
    if i < segments.size - 1 then
      let endIndex := segments[i + 1]!.2
      -- `pointsBuffer[endIndex]`: if endIndex = pointsCount this reads stale pool memory, but then
      -- every later segment is empty and `convertPoints` throws, so the value never matters.
      let endPoint := points[endIndex]?.getD Vec2.zero
      controlPoints := controlPoints ++ (← convertPoints formatVersion type (points.extract startIndex endIndex) (some endPoint))
    else
      controlPoints := controlPoints ++ (← convertPoints formatVersion type (points.extract startIndex points.size) none)
  return controlPoints

/-- `LegacyHitObjectType` flags -/
def CIRCLE : Int32 := 1
def SLIDER : Int32 := 2
def NEW_COMBO : Int32 := 4
def SPINNER : Int32 := 8
def COMBO_OFFSET : Int32 := 112
def HOLD : Int32 := 128

/-- `Parse(text)` (`:52-192`). Returns the new parser state and the parsed object (or the error). -/
def parse (st : ParserState) (text : String) : ParserState × DecodeM ConvertHitObject := Id.run do
  -- Everything up to the creation of the object: failures leave the state unchanged.
  let pre : DecodeM (Vec2 × F64 × Int32 × Bool × Int32 × Array String) := do
    let split := Beatmap.split text ','
    let pos : Vec2 := ⟨← parseCoord st.formatVersion (← at! split 0), ← parseCoord st.formatVersion (← at! split 1)⟩
    let startTime := (← liftNet "startTime" (Parsing.parseDouble (← at! split 2))) + st.offset
    let type0 ← liftNet "type" (Parsing.parseInt (← at! split 3))
    let comboOffset : Int32 := (type0 &&& COMBO_OFFSET) >>> 4
    let type1 := type0 &&& ~~~COMBO_OFFSET
    let combo := type1 &&& NEW_COMBO != 0
    let type := type1 &&& ~~~NEW_COMBO
    let _soundType ← liftNet "soundType" (Parsing.parseInt (← at! split 4))
    return (pos, startTime, comboOffset, combo, type, split)
  match pre with
  | .error e => return (st, .error e)
  | .ok (pos, startTime, comboOffset, combo, type, split) =>
  let newComboOf (nc : Bool) := st.firstObject || st.lastObjectIsSpinner || nc
  let finish (st' : ParserState) (r : DecodeM ConvertHitObject) : ParserState × DecodeM ConvertHitObject :=
    match r with
    | .ok o => ({ st' with firstObject := false }, .ok { o with startTime })
    | .error e => (st', .error e)
  if type &&& CIRCLE != 0 then
    -- createHitCircle (sets lastObject), then readCustomSampleBanks(split[5])
    let obj : ConvertHitObject :=
      { startTime, position := pos, newCombo := newComboOf combo,
        comboOffset := if combo then comboOffset else 0, kind := .circle }
    let st' := { st with lastObjectIsSpinner := false }
    let r : DecodeM ConvertHitObject := do
      if split.size > 5 then readCustomSampleBanks split[5]!
      return obj
    return finish st' r
  else if type &&& SLIDER != 0 then
    let r : DecodeM ConvertHitObject := do
      let repeatCount0 ← liftNet "repeatCount" (Parsing.parseInt (← at! split 6))
      if repeatCount0 > 9000 then throw "Repeat count is way too high"
      let repeatCount : Int32 := if repeatCount0 - 1 < 0 then 0 else repeatCount0 - 1
      let mut length : Option F64 := none
      if split.size > 7 then
        let l := F64.max 0 (← liftNet "length" (Parsing.parseDouble split[7]! (F64.ofInt Parsing.MAX_COORDINATE_VALUE.toInt)))
        length := if l == 0 then none else some l
      if split.size > 10 then readCustomSampleBanks split[10]! true
      let nodes := repeatCount.toNatClampNeg + 2
      if split.size > 9 && split[9]!.length > 0 then
        let sets := Beatmap.split split[9]! '|'
        for i in [0:nodes] do
          if i < sets.size then readCustomSampleBanks sets[i]!
      -- split[8] (`int.TryParse`) cannot throw
      let controlPoints ← convertPathString st.formatVersion (← at! split 5) pos
      -- createSlider: zero-length fix (`:491-495`) uses the ConvertSlider's own path (OptimiseCatmull = false)
      let path := SliderPath.ofControlPoints controlPoints length false
      -- `path.Distance` runs `calculatePath`: lazer would not get past an unbounded subdivision (D72)
      if path.fuelOut then throw pathFuelMsg
      let repeatCount := if Precision.almostEqualsF64 path.distance 0 then 0 else repeatCount
      return { startTime, position := pos, newCombo := newComboOf combo,
               comboOffset := if combo then comboOffset else 0,
               kind := .slider controlPoints length repeatCount }
    match r with
    | .ok o => return finish { st with lastObjectIsSpinner := false } (.ok o)
    | .error e => return (st, .error e)
  else if type &&& SPINNER != 0 then
    let endR : DecodeM F64 := do liftNet "spinner end" (Parsing.parseDouble (← at! split 5))
    match endR with
    | .error e => return (st, .error e)
    | .ok endT =>
      let duration := F64.max 0 (endT + st.offset - startTime)
      let obj : ConvertHitObject :=
        { startTime, position := ⟨256, 192⟩, newCombo := combo, comboOffset := 0, kind := .spinner duration }
      let st' := { st with lastObjectIsSpinner := true }
      let r : DecodeM ConvertHitObject := do
        if split.size > 6 then readCustomSampleBanks split[6]!
        return obj
      return finish st' r
  else if type &&& HOLD != 0 then
    let r : DecodeM F64 := do
      let mut endTime := F64.max startTime (← liftNet "hold end" (Parsing.parseDouble (← at! split 2)))
      if split.size > 5 && !split[5]!.isEmpty then
        let ss := Beatmap.split split[5]! ':'
        endTime := F64.max startTime (← liftNet "hold end" (Parsing.parseDouble ss[0]!))
        readCustomSampleBanks (":".intercalate (ss.toList.drop 1))
      return endTime
    match r with
    | .error e => return (st, .error e)
    | .ok endTime =>
      let obj : ConvertHitObject :=
        { startTime, position := pos, newCombo := false, comboOffset := 0, kind := .hold (endTime + st.offset - startTime) }
      return finish { st with lastObjectIsSpinner := false } (.ok obj)
  else
    return (st, .error s!"Unknown hit object type: {split[3]!}")

end ConvertHitObjectParser
end OsuModel.Beatmap
