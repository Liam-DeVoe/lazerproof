import OsuModel.Net
import OsuModel.Sim.Basic

/-!
# Replay frames: `.osr` frame text → `OsuReplayFrame` list

Input is the *decompressed* LZMA frame payload of the `.osr` (LZMA decompression is a trusted
boundary, done by the harness). Models `LegacyScoreDecoder.readLegacyReplay`
(`osu.Game/Scoring/Legacy/LegacyScoreDecoder.cs:268-352`) including the stable fixups, and
`OsuReplayFrame.FromLegacy` (`osu.Game.Rulesets.Osu/Replays/OsuReplayFrame.cs:30-36`).
The same code path is used for stable and lazer (version ≥ 30000000) replays.
-/

namespace OsuModel.Replay
open OsuModel.Net OsuModel.Sim

/-- `OsuAction` (Left, Right, Smoke). -/
inductive Action where
  | left | right | smoke
deriving Inhabited, Repr, DecidableEq, BEq

/-- `OsuReplayFrame`: time (double), position (float32), actions in the fixed order Left, Right, Smoke. -/
structure Frame where
  time : F64
  pos : Vec2
  actions : List Action
deriving Inhabited, Repr

/-- `LegacyReplayFrame` (before conversion). -/
structure LegacyFrame where
  time : F64
  mouseX : F32
  mouseY : F32
  buttons : Int32
deriving Inhabited

/-- `int.TryParse(s, out int)` (NumberStyles.Integer, invariant culture as in the oracle). -/
def intTryParse (s : String) : Option Int32 :=
  match intParse s with
  | .ok v => some v
  | .error _ => none

/-- Parse the frame text; returns the list of `LegacyReplayFrame`s (before fixups).
`beatmapOffset` = `BeatmapVersion < 5 ? 24 : 0` of the playable beatmap. -/
def parseLegacyFrames (text : String) (beatmapOffset : Int64) : Except NetExn (Array LegacyFrame) := do
  let mut lastTime : Int64 := beatmapOffset
  let mut out : Array LegacyFrame := #[]
  for fr in text.splitOn "," do
    let s0 :: s1 :: s2 :: s3 :: _ := fr.splitOn "|" | continue   -- `split.Length < 4` → skip
    if s0 == "-12345" then continue
    let diff : Int32 ← match intTryParse s0 with
      | some d => pure d
      | none => do
        let f ← Parsing.parseFloat s0
        -- `(int)Math.Round(float)` resolves to `Math.Round(double)`; `(int)` is saturating.
        pure (F64.toInt32 (F64.round (F32.toF64 f)))
    let mouseX ← Parsing.parseFloat s1 (F32.ofInt32 Parsing.MAX_COORDINATE_VALUE)
    let mouseY ← Parsing.parseFloat s2 (F32.ofInt32 Parsing.MAX_COORDINATE_VALUE)
    lastTime := lastTime + diff.toInt64
    let buttons ← Parsing.parseInt s3
    out := out.push { time := F64.ofInt64 lastTime, mouseX, mouseY, buttons }
  return out

private def isSkipPos (f : LegacyFrame) : Bool :=
  -- `Position == new Vector2(256, -500)` (float ==)
  f.mouseX == (256 : F32) && f.mouseY == (-500 : F32)

/-- Stable fixups (`:318-337`) and backwards-time filtering (`:341-351`). -/
def fixupFrames (fs : Array LegacyFrame) : Array LegacyFrame := Id.run do
  let mut fs := fs
  if h : 2 ≤ fs.size then
    let f0 := fs[0]
    let f1 := fs[1]
    if f1.time < f0.time then
      fs := #[{ f0 with time := 0 }, { f1 with time := f0.time }] ++ fs.extract 2 fs.size
  if h : 3 ≤ fs.size then
    let f0 := fs[0]
    let f1 := fs[1]
    let f2 := fs[2]
    if f2.time < f0.time then
      fs := #[{ f0 with time := f2.time }, { f1 with time := f2.time }, f2] ++ fs.extract 3 fs.size
  if h : 2 ≤ fs.size then
    if isSkipPos fs[1] then fs := fs.eraseIdx 1
  if h : 1 ≤ fs.size then
    if isSkipPos fs[0] then fs := fs.eraseIdx 0
  let mut out : Array LegacyFrame := #[]
  for f in fs do
    match out.back? with
    | some cur => if f.time < cur.time then continue
    | none => pure ()
    out := out.push f
  return out

/-- `OsuReplayFrame.FromLegacy`: Left if `Left1|Left2` (bits 1|4), Right if `Right1|Right2` (2|8),
Smoke if bit 16 (`ReplayButtonState`, `Enum.HasFlag`). -/
def convertFrame (f : LegacyFrame) : Frame :=
  let b : UInt32 := f.buttons.toUInt32
  let bit (k : UInt32) : Bool := (b >>> k) &&& 1 == 1
  let left := bit 0 || bit 2
  let right := bit 1 || bit 3
  let smoke := bit 4
  { time := f.time, pos := ⟨f.mouseX, f.mouseY⟩
    actions := (if left then [Action.left] else []) ++ (if right then [Action.right] else [])
      ++ (if smoke then [Action.smoke] else []) }

/-- Full decode. `FramedReplayInputHandler`'s constructor additionally stable-sorts by time
(`osu.Game/Rulesets/Replays/FramedReplayInputHandler.cs:99`), which is the identity here because the
filter above leaves the times non-decreasing. -/
def decode (text : String) (beatmapVersion : Int) : Except NetExn (Array Frame) := do
  let offset : Int64 := if beatmapVersion < 5 then 24 else 0
  let fs ← parseLegacyFrames text offset
  return (fixupFrames fs).map convertFrame

end OsuModel.Replay
