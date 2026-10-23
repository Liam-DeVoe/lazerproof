import OsuModel.Beatmap.DotNet

/-!
# Control points (`osu.Game/Beatmaps/ControlPoints/*`, `osu.Game/Beatmaps/Legacy/LegacyControlPointInfo.cs`)

Modelled control point types: `TimingControlPoint` (beat length, time signature numerator),
`DifficultyControlPoint` (slider velocity, tick generation) and `EffectControlPoint` (kiai, scroll
speed; kiai is read by Target Practice through `HitObject.Kiai`). Sample points only affect audio
and live in an independent typed list, so dropping them does not change the other lists.

`ControlPointInfo` keeps one `ControlPointGroup` per distinct time, holding at most one point per
type (`ControlPointGroup.Add` replaces an existing point of the same type, `ControlPointGroup.cs:31-43`).
The typed lists (`timingPoints`, `difficultyPoints`) are therefore sorted by time with unique times;
we store just those lists.
-/

namespace OsuModel.Beatmap
open OsuModel.Net

/-- `TimingControlPoint` (`TimingControlPoint.cs`). `BeatLength` is a `BindableDouble` with
`MinValue = 6, MaxValue = 60000` (`:64-68`): every assignment is clamped (`T.Clamp`, verified by
`bmtest probe`). `TimeSignature.Numerator` is read by Random (`onBeat` downbeats); omit-first-bar-line
is irrelevant. -/
structure TimingPoint where
  time : F64
  beatLength : F64
  /-- `TimeSignature.Numerator` (default `SimpleQuadruple` = 4) -/
  timeSignature : Int32 := 4
deriving Inhabited, Repr

/-- `BeatLengthBindable` assignment: `Math.Clamp(v, 6, 60000)`. -/
def clampBeatLength (v : F64) : F64 :=
  if v < 6 then 6 else if (60000 : F64) < v then 60000 else v

/-- `TimingControlPoint.DEFAULT`: beat length `60000 / 60 = 1000` (`TimingControlPoint.cs:27-38`). -/
def TimingPoint.default : TimingPoint := ⟨0, 1000, 4⟩

/-- `DifficultyControlPoint` (`DifficultyControlPoint.cs`). `SliderVelocityBindable` is clamped to
`[0.1, 10]` on every assignment (`:24-28`). -/
structure DifficultyPoint where
  time : F64
  sliderVelocity : F64
  generateTicks : Bool
deriving Inhabited, Repr

/-- `SliderVelocityBindable` (and `Slider.SliderVelocityMultiplierBindable`) assignment:
`Math.Clamp(v, 0.1, 10)`. -/
def clampSV (v : F64) : F64 :=
  if v < 0.1 then 0.1 else if (10 : F64) < v then 10 else v

/-- `DifficultyControlPoint.DEFAULT` (SV 1, ticks on). -/
def DifficultyPoint.default : DifficultyPoint := ⟨0, 1, true⟩

/-- `DifficultyControlPoint.IsRedundant(existing)` (`DifficultyControlPoint.cs:49-52`). -/
def DifficultyPoint.isRedundant (p e : DifficultyPoint) : Bool :=
  p.generateTicks == e.generateTicks && p.sliderVelocity == e.sliderVelocity

/-- `EffectControlPoint` (`EffectControlPoint.cs`): `KiaiMode`, `ScrollSpeed` (`BindableDouble(1)`
clamped to `[0.01, 10]`). -/
structure EffectPoint where
  time : F64
  kiai : Bool
  scrollSpeed : F64 := 1
deriving Inhabited, Repr

/-- `ScrollSpeedBindable` assignment: `Math.Clamp(v, 0.01, 10)`. -/
def clampScrollSpeed (v : F64) : F64 :=
  if v < 0.01 then 0.01 else if (10 : F64) < v then 10 else v

/-- `EffectControlPoint.DEFAULT` -/
def EffectPoint.default : EffectPoint := ⟨0, false, 1⟩

/-- `EffectControlPoint.IsRedundant(existing)` (`EffectControlPoint.cs:59-62`) -/
def EffectPoint.isRedundant (p e : EffectPoint) : Bool :=
  p.kiai == e.kiai && p.scrollSpeed == e.scrollSpeed

/-- `ControlPointInfo.BinarySearch(list, time, EqualitySelection.Rightmost)` followed by the
`index < 0 ? ~index - 1` adjustment (`ControlPointInfo.cs:212-292`): index of the last point
with `Time ≤ time`, if any. Since times are unique per list this equals a linear "last ≤" scan;
we keep the binary search verbatim anyway. -/
def binarySearchIdx {α : Type} [Inhabited α] (list : Array α) (timeOf : α → F64) (time : F64) : Option Nat := Id.run do
  let n := list.size
  if n == 0 then return none
  if time < timeOf list[0]! then return none
  if timeOf list[n-1]! < time then return some (n - 1)
  let mut l : Int := 0
  let mut r : Int := n - 1
  let mut eq := false
  for _ in [0:n + 1] do
    if l ≤ r then
      let pivot := l + (r - l) / 2
      let pt := timeOf list[pivot.toNat]!
      if pt < time then l := pivot + 1
      else if time < pt then r := pivot - 1
      else
        eq := true
        l := pivot + 1
  let index : Int := if eq then l - 1 else -l - 1
  let index := if index < 0 then -index - 1 - 1 else index
  return if index ≥ 0 then some index.toNat else none

/-- The typed lists of a `LegacyControlPointInfo`. -/
structure ControlPointInfo where
  timingPoints : Array TimingPoint := #[]
  difficultyPoints : Array DifficultyPoint := #[]
  effectPoints : Array EffectPoint := #[]
deriving Inhabited, Repr

namespace ControlPointInfo

/-- `TimingPointAt(time)`: last timing point with `Time ≤ time`, else the *first* timing point,
else `TimingControlPoint.DEFAULT` (`ControlPointInfo.cs:75`). -/
def timingPointAt (c : ControlPointInfo) (time : F64) : TimingPoint :=
  match binarySearchIdx c.timingPoints (·.time) time with
  | some i => c.timingPoints[i]!
  | none => if c.timingPoints.size > 0 then c.timingPoints[0]! else TimingPoint.default

/-- `LegacyControlPointInfo.DifficultyPointAt(time)`: last ≤ `time`, else DEFAULT
(`LegacyControlPointInfo.cs:41`). -/
def difficultyPointAt (c : ControlPointInfo) (time : F64) : DifficultyPoint :=
  match binarySearchIdx c.difficultyPoints (·.time) time with
  | some i => c.difficultyPoints[i]!
  | none => DifficultyPoint.default

/-- `EffectPointAt(time)`: last ≤ `time`, else `EffectControlPoint.DEFAULT` (`ControlPointInfo.cs:67`). -/
def effectPointAt (c : ControlPointInfo) (time : F64) : EffectPoint :=
  match binarySearchIdx c.effectPoints (·.time) time with
  | some i => c.effectPoints[i]!
  | none => EffectPoint.default

/-- Insert into a time-sorted list with unique times, replacing a point at the same time
(`ControlPointInfo.GroupAt(time, true)` + `ControlPointGroup.Add`; group times compare with
`double.CompareTo`, so `-0 = +0`). The replaced point keeps the *group's* time. -/
def insertSorted {α : Type} [Inhabited α] (list : Array α) (timeOf : α → F64) (setTime : α → F64 → α) (p : α) : Array α :=
  let t := timeOf p
  match list.findIdx? (fun q => compareF64 (timeOf q) t == 0) with
  | some i => list.set! i (setTime p (timeOf list[i]!))
  | none =>
    let i := (list.findIdx? (fun q => compareF64 t (timeOf q) < 0)).getD list.size
    list.insertIdx! i p

/-- `ControlPointInfo.Add(time, TimingControlPoint)`: timing points are never redundant
(`TimingControlPoint.IsRedundant => false`). -/
def addTiming (c : ControlPointInfo) (p : TimingPoint) : ControlPointInfo :=
  { c with timingPoints := insertSorted c.timingPoints (·.time) (fun p t => { p with time := t }) p }

/-- `ControlPointInfo.Add(time, DifficultyControlPoint)`: dropped if redundant w.r.t.
`DifficultyPointAt(time)` (`LegacyControlPointInfo.CheckAlreadyExisting`, `:46-60`). Returns
whether it was added. -/
def addDifficulty (c : ControlPointInfo) (p : DifficultyPoint) : ControlPointInfo :=
  if p.isRedundant (c.difficultyPointAt p.time) then c
  else { c with difficultyPoints := insertSorted c.difficultyPoints (·.time) (fun p t => { p with time := t }) p }

/-- `ControlPointInfo.Add(time, EffectControlPoint)`: dropped if redundant w.r.t. `EffectPointAt(time)`
(`ControlPointInfo.CheckAlreadyExisting`, `:346-363`). -/
def addEffect (c : ControlPointInfo) (p : EffectPoint) : ControlPointInfo :=
  if p.isRedundant (c.effectPointAt p.time) then c
  else { c with effectPoints := insertSorted c.effectPoints (·.time) (fun p t => { p with time := t }) p }

/-- `ControlPointInfo.DeepClone()` (`ControlPointInfo.cs:378-386`): a fresh info to which all
points are re-`Add`ed in group (time) order — redundancy is re-checked, so difficulty points that
only became redundant because of a later-added earlier point are dropped here. -/
def deepClone (c : ControlPointInfo) : ControlPointInfo :=
  let c0 : ControlPointInfo := {}
  let c1 := c.timingPoints.foldl addTiming c0
  let c2 := c.difficultyPoints.foldl addDifficulty c1
  c.effectPoints.foldl addEffect c2

end ControlPointInfo
end OsuModel.Beatmap
