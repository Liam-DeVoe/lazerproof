import OsuModel.Beatmap.Mods

/-!
# Canonical text dump of a playable beatmap (same format as `model/bmtest/Dumper.cs`)

Floating-point values are printed as raw IEEE bits in lowercase hex (`double`: 16 digits,
`float`: 8 digits); NaN is canonicalised (`7ff8000000000000` / `7fc00000`).
-/

namespace OsuModel.Beatmap
open OsuModel.Net

namespace Dump

def hexN (width : Nat) (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (width - s.length) '0') ++ s

def D (x : F64) : String := if x.isNaN then "7ff8000000000000" else hexN 16 x.toBits.toNat
def F (x : F32) : String := if x.isNaN then "7fc00000" else hexN 8 x.toBits.toNat
def V (v : Vec2) : String := F v.x ++ "," ++ F v.y
def B (b : Bool) : String := if b then "1" else "0"
def I (i : Int32) : String := toString i.toInt

def pathType : Option PathType → String
  | none => "none"
  | some .catmull => "catmull"
  | some .linear => "linear"
  | some .perfectCurve => "perfect"
  | some (.bspline none) => "bezier"
  | some (.bspline (some d)) => s!"bspline{I d}"

def windows : Option HitWindows → String
  | none => "null"
  | some .empty => "empty"
  | some (.osu g o m) => s!"{D g},{D o},{D m},{D MISS_WINDOW}"

def kindName : ObjectKind → String
  | .circle => "circle" | .slider _ => "slider" | .spinner _ => "spinner"

def nestedName : NestedKind → String
  | .head => "head" | .tail => "tail" | .repeat => "repeat" | .tick => "tick"
  | .spinnerTick => "spintick" | .spinnerBonusTick => "spinbonus"

def dump (pb : PlayableBeatmap) : Array String := Id.run do
  let mut out : Array String := #[]
  out := out.push s!"version {I pb.formatVersion}"
  let d := pb.difficulty
  out := out.push s!"difficulty hp={F d.drainRate} cs={F d.circleSize} od={F d.overallDifficulty} ar={F d.approachRate} sm={D d.sliderMultiplier} tr={D d.sliderTickRate}"
  out := out.push s!"stackleniency {F pb.stackLeniency}"
  out := out.push s!"audioleadin {D pb.audioLeadIn}"
  for t in pb.controlPoints.timingPoints do
    out := out.push s!"timing {D t.time} {D t.beatLength} {I t.timeSignature}"
  for p in pb.controlPoints.difficultyPoints do
    out := out.push s!"diffpoint {D p.time} {D p.sliderVelocity} {B p.generateTicks}"
  for e in pb.controlPoints.effectPoints do
    out := out.push s!"effect {D e.time} {B e.kiai} {D e.scrollSpeed}"
  for b in pb.breaks do
    out := out.push s!"break {D b.startTime} {D b.endTime}"
  let mut i := 0
  for h in pb.hitObjects do
    let common := s!"start={D h.startTime} pos={V h.position} stack={I h.stackHeight} scale={F h.scale} radius={D h.radius} preempt={D h.timePreempt} fadein={D h.timeFadeIn} stackoffset={V h.stackOffset} stackedpos={V h.stackedPosition} ci={I h.comboIndex} ciwo={I h.comboIndexWithOffsets} icc={I h.indexInCurrentCombo} hw={windows h.hitWindows} mjo={D h.maximumJudgementOffset} kiai={B h.kiai}"
    out := out.push s!"object {i} {kindName h.kind} end={D h.endTime} {common} nc={B h.newCombo} co={I h.comboOffset} lic={B h.lastInCombo}"
    i := i + 1
    match h.kind with
    | .slider s =>
      let exp := match s.path.spec.expectedDistance with | some e => D e | none => "null"
      out := out.push s!"slider repeats={I s.repeatCount} vel={D s.velocity} tickdist={D s.tickDistance} tdm={D s.tickDistanceMultiplier} svm={D s.sliderVelocityMultiplier} genticks={B s.generateTicks} dist={D s.path.distance} cdist={D s.path.calculatedDistance} expected={exp} duration={D h.duration} spandur={D h.spanDuration} endpos={V h.endPosition} stackedendpos={V h.stackedEndPosition} classic={B s.classicSliderBehaviour}"
      for cp in s.path.spec.controlPoints do
        out := out.push s!"cp {V cp.position} {pathType cp.type}"
      for p in s.path.calculatedPath do
        out := out.push s!"pp {V p}"
      for c in s.path.cumulativeLength do
        out := out.push s!"cl {D c}"
    | .spinner s =>
      out := out.push s!"spinner duration={D s.duration} req={I s.spinsRequired} bonus={I s.maximumBonusSpins}"
    | .circle => pure ()
    let mut j := 0
    for n in h.nested do
      -- nested combo information is bound to the parent's (`HitObject.cs:118-128`)
      let common := s!"start={D n.startTime} pos={V n.position} stack={I n.stackHeight} scale={F n.scale} radius={D n.radius} preempt={D n.timePreempt} fadein={D n.timeFadeIn} stackoffset={V n.stackOffset} stackedpos={V n.stackedPosition} ci={I h.comboIndex} ciwo={I h.comboIndexWithOffsets} icc={I h.indexInCurrentCombo} hw={windows (some n.hitWindows)} mjo={D n.maximumJudgementOffset} kiai={B n.kiai}"
      let extra := match n.kind with
        | .tick => s!" prog={D n.pathProgress} span={I n.spanIndex} spanstart={D n.spanStartTime}"
        | .repeat => s!" prog={D n.pathProgress} rep={I n.repeatIndex}"
        | .tail => s!" rep={I n.repeatIndex} classic={B n.classicSliderBehaviour} st={B n.strictTrackingTail}"
        | .spinnerTick | .spinnerBonusTick => s!" spindur={D n.spinnerDuration}"
        | .head => s!" classic={B n.classicSliderBehaviour}"
      out := out.push s!"nested {j} {nestedName n.kind} {common}{extra}"
      j := j + 1
  return out

def settingValue : SettingValue → String
  | .bool b => B b
  | .int v | .enum v => I v
  | .double v => D v
  | .float v => F v
  | .optInt none | .optFloat none => "null"
  | .optInt (some v) => I v
  | .optFloat (some v) => F v

/-- `mod <i> <acronym> key=value...` (decoded settings, `bmtest` `ModDump.Settings`). -/
def modLines (mods : List ModConfig) : Array String := Id.run do
  let mut out := #[]
  let mut i := 0
  for m in mods do
    if !m.known then out := out.push s!"mod {i} unknown {m.acronym}??"
    else out := out.push (" ".intercalate (s!"mod {i} {m.acronym}" :: m.settings.toList.map fun (k, v) => s!"{k}={settingValue v}"))
    i := i + 1
  return out

def objRef (pb : PlayableBeatmap) : Option ObjRef → String
  | none => "null"
  | some r => if r.epoch != pb.epoch then "gone" else
    match r.nested with
    | none => toString r.index
    | some j => s!"{r.index}.{j}"

/-- `modstate` lines (`bmtest` `ModDump.States`), grouped by mod index. -/
def modStateLines (pb : PlayableBeatmap) (nmods : Nat) : Array String := Id.run do
  let mut out := #[]
  for i in [0:nmods] do
    for (k, st) in pb.modStates do
      if k != i then continue
      match st with
      | .firstObject r => out := out.push s!"modstate {i} firstobject {objRef pb r}"
      | .timeRamp b f => out := out.push s!"modstate {i} timeramp {D b} {D f}"
      | .precedingEndTimes es =>
        for (r, t) in es do out := out.push s!"modstate {i} preceding {objRef pb (some r)} {D t}"
  return out

/-- The full dump for one file, as `bmtest` prints it. -/
def dumpLoad (r : LoadResult) (mods : List ModConfig := []) : Array String :=
  match r with
  | .decodeError e => #[s!"error decode {e}"]
  | .otherRuleset id => #[s!"mode {I id}"]
  | .playableError e => #["mode 0", s!"error playable {e}"]
  | .ok pb => #["mode 0"] ++ modLines mods ++ dump pb ++ modStateLines pb mods.length

end Dump
end OsuModel.Beatmap
