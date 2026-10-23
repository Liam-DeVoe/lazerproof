import OsuModel.Sim.Geometry

/-!
# osu-framework transform system (M7)

Literal model of `Transformable` (`osu.Framework/Graphics/Transforms/Transformable.cs`),
`TargetGroupingTransformTracker` (`TargetGroupingTransformTracker.cs`), `Transform`/`TransformCustom`
(`Transform.cs`, `TransformCustom.cs`), `TransformSequence` (`TransformSequence.cs`) and the
`TransformableExtensions` used by lazer's drawable hit objects and mods, restricted to the members that can affect
judgement: `Position`, `Scale` (Vector2), `Rotation`, `Alpha` (float).

DHOs are `PoolableDrawableWithLifetime`s with `RemoveCompletedTransforms => false`
(`osu.Game/Rulesets/Objects/Pooling/PoolableDrawableWithLifetime.cs:72`): completed transforms stay, `tCanRewind` is
always true (every transform is `Rewindable`), nothing is ever removed by the tracker's update loop.
Each member has its own tracker (grouping = member name).
-/

namespace OsuModel.Sim
open OsuModel.Net

inductive Member where
  | position | scale | rotation | alpha
deriving Inhabited, BEq, DecidableEq, Repr

def Member.isScalar : Member → Bool
  | .rotation | .alpha => true
  | _ => false

/-- One transform. Scalar members keep their value in `.x`. -/
structure Tr where
  id : Nat := 0
  member : Member
  start : F64
  endT : F64
  sv : Vec2 := Vec2.zero
  ev : Vec2
  easing : Framework.Easing := .none
  /-- `PositionOffsetTransform` (`MoveToOffset`): `ReadIntoStartValue` sets `StartValue = Position`,
  `EndValue = Position + offset` (`TransformableExtensions.cs:800-823`). -/
  offset : Option Vec2 := none
  applied : Bool := false
  appliedToEnd : Bool := false
  hasStart : Bool := false
deriving Inhabited

structure Tracker where
  member : Member
  ts : Array Tr := #[]
  /-- `currentTransformID` -/
  counter : Nat := 0
  /-- `lastAppliedTransformIndices[member]` -/
  lastApplied : Nat := 0
deriving Inhabited

/-- A `Transformable` drawable: the modelled members, its trackers and the transform clock bookkeeping. -/
structure TObj where
  pos : Vec2 := Vec2.zero
  scale : Vec2 := ⟨1, 1⟩
  rot : F32 := 0
  alpha : F32 := 1
  trackers : Array Tracker := #[]
  /-- `Transformable.lastUpdateTransformsTime` (default 0) -/
  lastUpdate : F64 := 0
  /-- `TransformDelay` -/
  delay : F64 := 0
deriving Inhabited

namespace TObj

def get (o : TObj) : Member → Vec2
  | .position => o.pos
  | .scale => o.scale
  | .rotation => ⟨o.rot, 0⟩
  | .alpha => ⟨o.alpha, 0⟩

/-- Property setters (`Drawable.Position/Scale/Rotation/Alpha`): `if (old == value) return;` (float `==`). -/
def set (o : TObj) (m : Member) (v : Vec2) : TObj :=
  match m with
  | .position => if o.pos.eq v then o else { o with pos := v }
  | .scale => if o.scale.eq v then o else { o with scale := v }
  | .rotation => if o.rot == v.x then o else { o with rot := v.x }
  | .alpha => if o.alpha == v.x then o else { o with alpha := v.x }

end TObj

def toTK (v : Vec2) : OsuTK.Vector2 := ⟨v.x, v.y⟩
def ofTK (v : OsuTK.Vector2) : Vec2 := ⟨v.x, v.y⟩

/-- `TransformCustom.valueAt` / `PositionOffsetTransform.positionAt`: `t < Start → StartValue`, `t >= End → EndValue`,
else `Interpolation.ValueAt` (Vector2: float cur/dur; float: via double, `Interpolation.cs:329-362`). -/
def Tr.valueAt (t : Tr) (time : F64) : Vec2 :=
  if time < t.start then t.sv
  else if t.endT ≤ time then t.ev
  else if t.member.isScalar then
    ⟨Framework.Interpolation.valueAtF time t.sv.x t.ev.x t.start t.endT t.easing, 0⟩
  else ofTK (Framework.Interpolation.valueAtV time (toTK t.sv) (toTK t.ev) t.start t.endT t.easing)

/-- `Transform.Apply(time)`: write the member, `Applied = true`. -/
def applyTr (o : TObj) (t : Tr) (time : F64) : TObj × Tr :=
  (o.set t.member (t.valueAt time), { t with applied := true })

/-- `ReadIntoStartValue`. -/
def readStart (o : TObj) (t : Tr) : Tr :=
  let cur := o.get t.member
  match t.offset with
  | some off => { t with sv := cur, ev := cur + off, hasStart := true }
  | none => { t with sv := cur, hasStart := true }

/-- `TargetGroupingTransformTracker.UpdateTransforms(time, rewinding)` (`:63-200`) with `RemoveCompletedTransforms`
false, no looping transforms. -/
def trackerUpdate (o : TObj) (tk : Tracker) (time : F64) (rewinding : Bool) : TObj × Tracker := Id.run do
  -- `ts` keeps its length (transforms are only updated in place here), so it is a `Vector` of that length
  let n := tk.ts.size
  let mut o := o
  let mut ts : Vector Tr n := ⟨tk.ts, rfl⟩
  let mut last := tk.lastApplied
  if rewinding then
    last := 0
    let mut reverted := false
    for hk : k in [0:n] do
      let i := n - 1 - k
      have hi : i < n := by have hu : k < n := hk.upper; omega
      let t := ts[i]
      if !t.applied then continue
      if t.start ≤ time then
        if !reverted then
          ts := ts.set i { t with appliedToEnd := false }
          reverted := true
      else
        let (o', t') := applyTr o t time
        o := o'
        ts := ts.set i { t' with applied := false, appliedToEnd := false }
  let mut i := last
  -- `for (int i = last; i < transforms.Count; ++i)`: at most `n` iterations
  for _ in [0:n] do
    if hi : i < n then
      let mut t := ts[i]
      if time < t.start then break
      if !t.applied then
        for hj : j in [last:i] do
          have : j < n := by have hu : j < i := hj.upper; omega
          let u := ts[j]
          let mut u' := u
          if !u.appliedToEnd then
            let (o', uu) := applyTr o u t.start
            o := o'
            u' := uu
          ts := ts.set j { u' with appliedToEnd := true }
      if !t.hasStart then t := readStart o t
      if !t.appliedToEnd then
        let (o', tt) := applyTr o t time
        o := o'
        t := { tt with appliedToEnd := t.endT ≤ time }
      ts := ts.set i t
      if t.appliedToEnd then last := i + 1
      i := i + 1
    else break
  return (o, { tk with ts := ts.toArray, lastApplied := last })

/-- `Transformable.updateTransforms(time, forceRewindReprocess)` (`Transformable.cs:117-128`): each tracker in turn.
(`trackerUpdate` reads and writes only the member values of `o`, never `o.trackers`.) -/
def updateTransforms (o : TObj) (time : F64) (force : Bool := false) : TObj :=
  let rewinding := time < o.lastUpdate || force
  let o := { o with lastUpdate := time }
  let step (tk : Tracker) : StateM TObj Tracker := do
    let (o', tk') := trackerUpdate (← get) tk time rewinding
    set o'
    return tk'
  let (tks, o) := (o.trackers.mapM step).run o
  { o with trackers := tks }

/-- `double.CompareTo` order on (StartTime, TransformID) (`Transform.cs` COMPARER). -/
def trLess (a b : Tr) : Bool :=
  let c := compareD a.start b.start
  c < 0 || (c == 0 && a.id < b.id)

/-- `Transformable.AddTransform` (`Transformable.cs:350-381`) + `TargetGroupingTransformTracker.AddTransform` (`:202-230`):
assign the next ID, insert sorted, remove every later transform of the same member, reset the applied cache; then,
if it could have an immediate effect (`Start < now || End <= now`), `updateTransforms(now, Start <= now)`. -/
def addTransform (o : TObj) (t0 : Tr) (now : F64) : TObj :=
  -- the member's tracker (created on demand, `Transformable.cs:362-368`)
  let found := o.trackers.findFinIdx? (·.member == t0.member)
  let tk : Tracker := match found with
    | some k => o.trackers[k]
    | none => { member := t0.member }
  let t := { t0 with id := tk.counter + 1 }
  -- SortedList.Add: insertion point after all elements not greater than t
  let ins := (tk.ts.findIdx? (trLess t ·)).getD tk.ts.size
  let ts := (tk.ts.extract 0 ins).push t
  -- following transforms of the same member (all of this tracker's) are removed
  let tk' := { tk with ts, counter := tk.counter + 1, lastApplied := 0 }
  let o := { o with trackers := match found with
    | some k => o.trackers.set k tk' k.isLt
    | none => o.trackers.push tk' }
  if t.start < now || t.endT ≤ now then updateTransforms o now (t.start ≤ now) else o

/-- `ClearTransformsAfter(time)` for all members (`:259-285`). -/
def clearTransformsAfter (o : TObj) (time : F64) : TObj :=
  { o with trackers := o.trackers.map fun tk => { tk with ts := tk.ts.filter (fun t => t.start < time), lastApplied := 0 } }

def dblMinValue : F64 := Float.ofBits 0xFFEFFFFFFFFFFFFF

/-- `DrawableHitObject.clearExistingStateTransforms` (`DrawableHitObject.cs:501-507`): `ApplyTransformsAt(MinValue)`
(rewind to −∞ writes every applied transform's start value), then `ClearTransformsAfter(MinValue)`. -/
def clearState (o : TObj) : TObj :=
  clearTransformsAfter (updateTransforms o dblMinValue) dblMinValue

/-- `TransformStartTime = Clock.CurrentTime + TransformDelay`. -/
def startTime (o : TObj) (now : F64) : F64 := now + o.delay

/-- `BeginAbsoluteSequence(t)`: `TransformDelay = t - Clock.CurrentTime` (restored by the caller). -/
def absSeq (o : TObj) (now t : F64) : TObj := { o with delay := t - now }

/-! ## TransformSequence -/

/-- A `TransformSequence<T>`: `currentTime`, `lastEndTime` (`TransformSequence.cs:20-58`). -/
structure Seq where
  currentTime : F64
  lastEndTime : F64
  /-- `last != null` -/
  hasLast : Bool := false

/-- `TransformTo(member, value, duration, easing)` at `TransformStartTime` (`TransformableExtensions.cs:28-67`):
a new sequence, `Add` (lastEndTime update), then `AddTransform`. -/
def transformTo (o : TObj) (now : F64) (m : Member) (v : Vec2) (dur : F64) (e : Framework.Easing := .none)
    (offset : Option Vec2 := none) : TObj × Seq :=
  let st := startTime o now
  let t : Tr := { member := m, start := st, endT := st + dur, ev := v, easing := e, offset }
  -- `result.Add(t)`: `last == null` → `lastEndTime = t.EndTime`
  let seq : Seq := { currentTime := st, lastEndTime := t.endT, hasLast := true }
  (addTransform o t now, seq)

/-- `seq.Append(o => o.X(...))`: `BeginAbsoluteSequence(currentTime, false)` around the child, then `Add` its transform. -/
def Seq.append (s : Seq) (o : TObj) (now : F64) (m : Member) (v : Vec2) (dur : F64) (e : Framework.Easing := .none)
    (offset : Option Vec2 := none) : TObj × Seq :=
  let saved := o.delay
  let (o, child) := transformTo (absSeq o now s.currentTime) now m v dur e offset
  -- `Add`: `if (last == null || transform.EndTime > lastEndTime) lastEndTime = EndTime`
  let endT := child.lastEndTime
  ({ o with delay := saved },
   { s with lastEndTime := (if !s.hasLast || s.lastEndTime < endT then endT else s.lastEndTime), hasLast := true })

/-- `.Then()` = `currentTime = max(currentTime, lastEndTime); Delay(0)`. -/
def Seq.then_ (s : Seq) : Seq := { s with currentTime := F64.max s.currentTime s.lastEndTime }
/-- `.Delay(d)`: `currentTime += d`. -/
def Seq.delayBy (s : Seq) (d : F64) : Seq := { s with currentTime := s.currentTime + d }

/-- `t.Delay(d)` on a drawable: `new TransformSequence(t).Delay(d)`. -/
def delaySeq (o : TObj) (now d : F64) : Seq :=
  let st := startTime o now
  { currentTime := st + d, lastEndTime := st }

def vs (x : F32) : Vec2 := ⟨x, 0⟩

/-- `FadeInFromZero()` = `FadeTo(0).FadeIn(duration)` (`TransformableExtensions.cs:528-531`). -/
def fadeInFromZero (o : TObj) (now : F64) (dur : F64 := 0) (e : Framework.Easing := .none) : TObj :=
  let (o, s) := transformTo o now .alpha (vs 0) 0
  (s.append o now .alpha (vs 1) dur e).1

/-- `LatestTransformEndTime` (`Transformable.cs:59-80`): `max = TransformStartTime; if (t.EndTime > max) max = t.EndTime + 1`,
trackers in list order, transforms in sorted order. -/
def latestEnd (o : TObj) (now : F64) : F64 := Id.run do
  let mut m := startTime o now
  for tk in o.trackers do
    for t in tk.ts do
      if m < t.endT then m := t.endT + 1
  return m

end OsuModel.Sim
