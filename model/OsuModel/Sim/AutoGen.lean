import OsuModel.Sim.Geometry
import OsuModel.Sim.Mods
import OsuModel.Replay.Frames

/-!
# `OsuAutoGenerator` (used by Autopilot)

Literal transcription of `osu.Game.Rulesets.Osu/Replays/OsuAutoGenerator.cs` (`Generate`, `addHitObjectReplay`,
`calcSpinnerStartPosAndDirection`, `moveToHitObject`, `addHitObjectClickFrames`; `DelayedMovements` is never set,
so `addDelayedMovements` is dead code) and `OsuAutoGeneratorBase.cs` (`ApplyModsToTimeDelta`, `ApplyModsToRate`,
`GetFrameDelay`, `FindInsertionIndex`, `CirclePosition`). Floats: osuTK `Vector2` (`OsuModel.Net.OsuTK`).
Autopilot only reads the frames' times and positions, but the frame list structure (removals) depends on the
actions, so they are modelled too.
-/

namespace OsuModel.Sim
open OsuModel.Net OsuModel.Replay
open OsuModel.Net.OsuTK (Vector2)

def RateMod.apply (m : RateMod) (time rate : F64) : Except NetExn F64 :=
  match m with
  | .speed s => pure (rate * s)
  | .timeRamp i f b ft => do
    let amount := (time - b) / F64.max 1 (ft - b)
    let ramp := i + (f - i) * (← F64.clamp amount 0 1)
    return rate * (← F64.roundDigits ramp 2)
  | .adaptive i => pure (rate * i)

/-- A generated frame. `actions` is a *reference* to a `List<OsuAction>` (index into the generator's list heap):
`new OsuReplayFrame(…) { Actions = lastFrame.Actions }` shares the list object, and later
`frame.Actions.Clear(); frame.Actions.Add(a)` mutates it for every frame sharing it. -/
structure AFrame where
  time : F64
  pos : Vector2
  actions : Nat
  /-- `OsuKeyUpReplayFrame` -/
  keyUp : Bool := false
deriving Inhabited

namespace AutoGen

def v (x y : F32) : Vector2 := ⟨x, y⟩
def ofVec (p : Vec2) : Vector2 := ⟨p.x, p.y⟩
/-- `SPINNER_CENTRE = OsuPlayfield.BASE_SIZE / 2` -/
def spinnerCentre : Vector2 := ⟨(512 : F32) / 2, (384 : F32) / 2⟩
def spinRadius : F32 := 50
/-- `radsPerMillisecond = float.DegreesToRadians(spin_rpm * 360) / 60000` (constant-folded `spin_rpm * 360`,
then runtime `DegreesToRadians` and division: `0x3D4CCCCE`, docs/mods/input-mods.md §4.3). -/
def radsPerMillisecond : F32 := Float32.ofBits 0x3D4CCCCE
def keyUpDelay : F64 := 50
def minSeparationForAlternating : F64 := 266

structure G where
  frames : Array AFrame := #[]
  buttonIndex : Nat := 0
  /-- the `List<OsuAction>` objects -/
  heap : Array (List Action) := #[]

/-- `Except` is the rejection channel (a .NET exception, or an internal invariant violation / fuel exhaustion). -/
abbrev M := ReaderT (List RateMod) (StateT G (Except String))

def liftN {α} (e : Except NetExn α) : M α :=
  match e with | .ok v => pure v | .error x => throw s!"lazer would throw: {repr x}"

def liftS {α} (e : Except String α) : M α := match e with | .ok v => pure v | .error m => throw m

/-- Generator loops are bounded by fuel; running out is a rejection, never a silent truncation. -/
def outOfFuel {α} (what : String) : M α := throw s!"autogen: fuel exhausted in {what}"

def applyModsToTimeDelta (start endT : F64) : M F64 := do
  let mut d := endT - start
  for m in ← read do d := d / (← liftN (m.apply start 1))
  return d

def applyModsToRate (time rate : F64) : M F64 := do
  let mut r := rate
  for m in ← read do r ← liftN (m.apply time r)
  return r

def getFrameDelay (time : F64) : M F64 := applyModsToRate time (1000.0 / 60)

/-- `FindInsertionIndex`: `List.BinarySearch` with `f1.Time.CompareTo(f2.Time)`; on a hit, skip past equal times. -/
def findInsertionIndex (fs : Array AFrame) (t : F64) : Nat := Id.run do
  let r := bsearch fs (fun f => compareD f.time t)
  if r < 0 then return (-r - 1).toNat
  let mut idx := r.toNat
  -- `while (index < list.Count && list[index].Time == frame.Time) index++` (at most `fs.size` steps)
  for _ in [0:fs.size] do
    match fs[idx]? with
    | some f => if t == f.time then idx := idx + 1 else break
    | none => break
  return idx

def addFrame (f : AFrame) : M Unit := do
  let g ← get
  let i := findInsertionIndex g.frames f.time
  if h : i ≤ g.frames.size then set { g with frames := g.frames.insertIdx i f h }
  else throw s!"internal: insertion index {i} out of range"

def lastFrame : M AFrame := do
  match (← get).frames.back? with
  | some f => pure f
  | none => throw "internal: lastFrame on an empty frame list"

/-- `new List<OsuAction>(…)` -/
def newList (xs : List Action) : M Nat := do
  let g ← get
  set { g with heap := g.heap.push xs }
  return g.heap.size
def listOf (r : Nat) : M (List Action) := do
  match (← get).heap[r]? with
  | some l => pure l
  | none => throw s!"internal: action list {r} out of range"
/-- `list.Clear(); list.Add(a)` -/
def setList (r : Nat) (xs : List Action) : M Unit := do
  let g ← get
  if h : r < g.heap.size then set { g with heap := g.heap.set r xs h }
  else throw s!"internal: action list {r} out of range"

/-- `CirclePosition(t, radius) = ((float)(Math.Cos(t) * radius), (float)(Math.Sin(t) * radius))` -/
def circlePosition (t radius : F64) : Vector2 := ⟨F64.toF32 (F64.cos t * radius), F64.toF32 (F64.sin t * radius)⟩

/-- `calcSpinnerStartPosAndDirection` (`OsuAutoGenerator.cs:185-230`). -/
def calcSpinnerStart (prevPos : Vector2) : Vector2 × F32 :=
  let off := spinnerCentre - prevPos
  let distFromCentre := off.length
  let distToTangentPoint := F32.sqrt (distFromCentre * distFromCentre - spinRadius * spinRadius)
  if spinRadius < distFromCentre then
    let angle := F32.asin (spinRadius / distFromCentre)
    let dir : F32 := if 0 < angle then -1 else 1
    -- in-place: X first, then Y with the new X
    let x := off.x * F32.cos angle - off.y * F32.sin angle
    let y := x * F32.sin angle + off.y * F32.cos angle
    let o : Vector2 := (⟨x, y⟩ : Vector2).normalized
    let o := o * distToTangentPoint
    (prevPos + o, dir)
  else if 0 < off.length then
    (spinnerCentre - off * (spinRadius / off.length), 1)
  else
    (spinnerCentre + v 0 (-spinRadius), 1)

/-- `moveToHitObject` (`:232-276`). -/
def moveToHitObject (h : HObj) (target : Vector2) (easing : Framework.Easing) : M Unit := do
  let mut lf ← lastFrame
  let reaction ← applyModsToRate (h.start - h.preempt) 100
  let waitTime := h.start - F64.max 0 (h.preempt - reaction)
  let mut hasWaited := false
  if lf.time < waitTime then
    lf := { time := waitTime, pos := lf.pos, actions := lf.actions }   -- `{ Actions = lastFrame.Actions }` (shared)
    hasWaited := true
    addFrame lf
  let timeDifference ← applyModsToTimeDelta lf.time h.start
  let g ← get
  let lastLast : Option AFrame := if g.frames.size ≥ 2 then g.frames[g.frames.size - 2]? else none
  if 0 ≤ timeDifference then
    if let some ll := lastLast then
      if lf.keyUp && !hasWaited then
        -- lastFrame is Frames[^1] here (no wait): mutate it in place
        let np := Framework.Interpolation.valueAtV lf.time lf.pos target ll.time h.start easing
        lf := { lf with pos := np }
        let g ← get
        if h : 0 < g.frames.size then set { g with frames := g.frames.set (g.frames.size - 1) lf (by omega) }
        else throw "internal: empty frame list"
    let lastPosition := lf.pos
    let mut time := lf.time + (← getFrameDelay lf.time)
    let mut fuel := 10000000
    while time < h.start && fuel > 0 do
      fuel := fuel - 1
      let cur := Framework.Interpolation.valueAtV time lastPosition target lf.time h.start easing
      addFrame { time := F64.ofInt32 (F64.toInt32 time), pos := cur, actions := lf.actions }
      time := time + (← getFrameDelay time)
    if fuel == 0 && time < h.start then outOfFuel "time < h.start"
  if 0 ≤ timeDifference && timeDifference < minSeparationForAlternating then
    modify fun g => { g with buttonIndex := g.buttonIndex + 1 }
  else
    modify fun g => { g with buttonIndex := 0 }

/-- `addHitObjectClickFrames` (`:286-397`). -/
def addClickFrames (o : TopObj) (startPosition : Vector2) (spinnerDirection : F32) (stackedEnd : Vector2) : M Unit := do
  let h := o.h
  let mut action := if (← get).buttonIndex % 2 == 0 then Action.left else .right
  let startFrame : AFrame := { time := h.start, pos := startPosition, actions := ← newList [action] }
  let hEndTime := h.endTime + keyUpDelay
  let endDelay : F64 := if h.kind == .spinner then 1 else 0
  let mut endFrame : AFrame := { time := hEndTime + endDelay, pos := stackedEnd, actions := ← newList [], keyUp := true }
  let g ← get
  let index : Int := (findInsertionIndex g.frames startFrame.time : Int) - 1
  if 0 ≤ index then
    let some prevFrame := g.frames[index.toNat]? | throw "internal: insertion index out of range"
    let prevRef := prevFrame.actions
    if !(← listOf prevRef).isEmpty then
      if (← listOf prevRef).contains action then
        action := if action == .left then .right else .left
        setList startFrame.actions [action]
      let endIndex := findInsertionIndex g.frames endFrame.time
      let mut fs := g.frames
      if index < (fs.size : Int) - 1 then
        let cnt := endIndex - (index.toNat + 1)   -- Math.Max(0, …) on Nat subtraction
        fs := fs.extract 0 (index.toNat + 1) ++ fs.extract (index.toNat + 1 + cnt) fs.size
      modify fun g => { g with frames := fs }
      for h : j in [index.toNat + 1:fs.size] do
        let f := fs[j]'h.upper
        -- `previousActions` is the (possibly mutated) list object of the previous frame
        if j < fs.size - 1 || (← listOf f.actions) == (← listOf prevRef) then
          setList f.actions [action]
  addFrame startFrame
  match h.kind with
  | .spinner =>
    let difference := startPosition - spinnerCentre
    let radius := difference.length
    let mut angle : F32 := if radius == 0 then 0 else F32.atan2 difference.y difference.x
    let mut previousFrame := h.start
    let endT := h.endTime
    let mut nextFrame := h.start + (← getFrameDelay h.start)
    let mut fuel := 10000000
    while nextFrame < endT && fuel > 0 do
      fuel := fuel - 1
      let t := (← applyModsToTimeDelta previousFrame nextFrame) * F32.toF64 spinnerDirection
      angle := angle + F64.toF32 t * radsPerMillisecond
      let pos := spinnerCentre + circlePosition (F32.toF64 angle) (F32.toF64 spinRadius)
      addFrame { time := F64.ofInt32 (F64.toInt32 nextFrame), pos, actions := ← newList [action] }
      previousFrame := nextFrame
      nextFrame := nextFrame + (← getFrameDelay nextFrame)
    if fuel == 0 && nextFrame < endT then outOfFuel "nextFrame < endT"
    let t := (← applyModsToTimeDelta previousFrame endT) * F32.toF64 spinnerDirection
    angle := angle + F64.toF32 t * radsPerMillisecond
    let endPosition := spinnerCentre + circlePosition (F32.toF64 angle) (F32.toF64 spinRadius)
    addFrame { time := endT, pos := endPosition, actions := ← newList [action] }
    endFrame := { endFrame with pos := endPosition }
  | .slider =>
    let some sd := o.slider | throw "malformed: slider without slider data"
    let mut j ← getFrameDelay h.start
    let mut fuel := 10000000
    while j < sd.duration && fuel > 0 do
      fuel := fuel - 1
      -- `StackedPositionAt(t) = StackedPosition + CurvePositionAt(t)`
      let pos := ofVec h.stacked + ofVec (← liftS (sd.curvePositionAt (j / sd.duration)))
      addFrame { time := h.start + j, pos, actions := ← newList [action] }
      j := j + (← getFrameDelay (h.start + j))
    if fuel == 0 && j < sd.duration then outOfFuel "j < sd.duration"
    addFrame { time := h.endTime, pos := stackedEnd, actions := ← newList [action] }
  | _ => pure ()
  if (← lastFrame).time ≤ endFrame.time then addFrame endFrame

/-- `addHitObjectReplay` (`:144-183`). -/
def addHitObjectReplay (o : TopObj) : M Unit := do
  let h := o.h
  -- `StackedEndPosition`: the tail's stacked position for sliders (`EndPosition + StackOffset`), else `StackedPosition`
  let stackedEnd : Vector2 := match h.kind with
    | .slider => match o.nested.find? (·.kind == .tail) with | some t => ofVec t.stacked | none => ofVec h.stacked
    | _ => ofVec h.stacked
  let mut startPosition := ofVec h.stacked
  let mut easing := Framework.Easing.out
  let mut spinnerDirection : F32 := -1
  if h.kind == .spinner then
    let some sp := o.spinner | return
    if sp.spinsRequired == 0 then return
    let lp := (← lastFrame).pos
    let (sp', dir) := calcSpinnerStart lp
    startPosition := sp'
    spinnerDirection := dir
    if spinRadius < (spinnerCentre - lp).length then easing := .in_
  if (← get).frames.size > 0 then moveToHitObject h startPosition easing
  addClickFrames o startPosition spinnerDirection stackedEnd

/-- `Generate()` (`:69-92`). -/
def generate (pb : Playable) (mods : List RateMod) : Except String (Array AFrame) :=
  if h : pb.objects.size = 0 then pure #[] else
  let run : M Unit := do
    addFrame { time := pb.objects[0].h.start - 1500, pos := v 256 500, actions := ← newList [] }
    for o in pb.objects do addHitObjectReplay o
  return (← (run.run mods).run {}).2.frames

end AutoGen
end OsuModel.Sim
