import Lean.Data.Json
import OsuModel.Sim.Basic

/-!
# The playable beatmap, as consumed by the simulation

This is the interface between `OsuModel/Beatmap` (`.osu` → playable beatmap) and `OsuModel/Sim`.
It contains exactly the fields of `IBeatmap` (after `GetPlayableBeatmap` with the gameplay mods) that the
drawable/judgement layer reads. For differential testing it is loaded from the oracle's
`--dump-playable` JSON (`oracle/Dump.cs`, floats as raw IEEE bits).
-/

namespace OsuModel.Sim
open OsuModel.Net

inductive Kind where
  | circle | slider | spinner | head | tick | «repeat» | tail | spinnerTick | spinnerBonusTick
deriving Inhabited, Repr, DecidableEq, BEq

namespace Kind
def ofString? : String → Option Kind
  | "circle" => some circle | "slider" => some slider | "spinner" => some spinner
  | "head" => some head | "tick" => some tick | "repeat" => some «repeat» | "tail" => some tail
  | "spinner_tick" => some spinnerTick | "spinner_bonus_tick" => some spinnerBonusTick
  | _ => none
/-- C# class name as printed by the oracle (`HitObject.GetType().Name`). -/
def typeName : Kind → String
  | circle => "HitCircle" | slider => "Slider" | spinner => "Spinner" | head => "SliderHeadCircle"
  | tick => "SliderTick" | «repeat» => "SliderRepeat" | tail => "SliderTailCircle"
  | spinnerTick => "SpinnerTick" | spinnerBonusTick => "SpinnerBonusTick"
/-- `DrawableHitCircle` (incl. `DrawableSliderHead`): the objects that receive presses. -/
def isCircleLike : Kind → Bool
  | circle | head => true
  | _ => false
end Kind

/-- `OsuHitWindows` (Great/Ok/Meh/Miss) — only circles and slider heads have non-empty windows. -/
structure HitWindows where
  great : F64
  ok : F64
  meh : F64
  miss : F64
deriving Inhabited, Repr

namespace HitWindows
/-- `HitWindows.ResultFor(timeOffset)` (`osu.Game/Rulesets/Scoring/HitWindows.cs:83-94`) with
`OsuHitWindows.IsHitResultAllowed` = {Great, Ok, Meh, Miss}. -/
def resultFor (hw : HitWindows) (timeOffset : F64) : HitResult :=
  let o := F64.abs timeOffset
  if o ≤ hw.great then .great
  else if o ≤ hw.ok then .ok
  else if o ≤ hw.meh then .meh
  else if o ≤ hw.miss then .miss
  else .none
/-- `HitWindows.CanBeHit(timeOffset) = timeOffset <= WindowFor(Meh)` (`:109`). -/
def canBeHit (hw : HitWindows) (timeOffset : F64) : Bool := timeOffset ≤ hw.meh
end HitWindows

/-- Fields common to all (top-level and nested) `OsuHitObject`s. -/
structure HObj where
  kind : Kind
  /-- `HitObject.GetType().Name` (e.g. `StrictTrackingSliderTailCircle`) -/
  typeName : String := ""
  start : F64
  endTime : F64
  pos : Vec2
  stacked : Vec2
  stackHeight : Int
  scale : F32
  radius : F64
  preempt : F64
  /-- `TimeFadeIn` -/
  fadeIn : F64 := 0
  maxJudgementOffset : F64
  hitWindows : Option HitWindows
  maxResult : HitResult
  minResult : HitResult
  newCombo : Bool
  comboIndex : Nat
  indexInCombo : Nat
  lastInCombo : Bool
  /-- SliderTick -/
  spanIndex : Nat := 0
  spanStart : F64 := 0
  /-- SliderTick / SliderRepeat -/
  pathProgress : F64 := 0
  /-- SliderRepeat / SliderTailCircle -/
  repeatIndex : Nat := 0
deriving Inhabited

structure SliderData where
  spanCount : Nat
  duration : F64
  spanDuration : F64
  velocity : F64
  pathDistance : F64
  classic : Bool
  /-- `SliderPath.calculatedPath` (private), float vertices relative to the head. -/
  path : Array Vec2
  /-- `SliderPath.cumulativeLength` (private). -/
  cumLen : Array F64
deriving Inhabited

structure SpinnerData where
  duration : F64
  spinsRequired : Int
  maxBonusSpins : Int
deriving Inhabited

structure TopObj where
  h : HObj
  slider : Option SliderData := none
  spinner : Option SpinnerData := none
  nested : Array HObj
deriving Inhabited

structure Difficulty where
  cs : F32
  hp : F32
  od : F32
  ar : F32
deriving Inhabited

structure Playable where
  beatmapVersion : Int
  audioLeadIn : F64
  difficulty : Difficulty
  baseDifficulty : Difficulty
  sliderMultiplier : F64
  sliderTickRate : F64
  breaks : Array (F64 × F64)
  objects : Array TopObj
deriving Inhabited

/-! ## JSON loading (oracle `--dump-playable`, format "playable-1") -/
namespace Load
open Lean (Json)

def hexVal (s : String) : Except String Nat := do
  let cs := s.toList
  let cs := if cs.take 2 == ['0', 'x'] then cs.drop 2 else cs
  let mut v := 0
  for c in cs do
    let d ← if '0' ≤ c && c ≤ '9' then pure (c.toNat - 48)
      else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 87)
      else if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 55)
      else throw s!"bad hex digit in {s}"
    v := v * 16 + d
  return v

def f64 (j : Json) : Except String F64 := do return Float.ofBits (UInt64.ofNat (← hexVal (← j.getStr?)))
def f32 (j : Json) : Except String F32 := do return Float32.ofBits (UInt32.ofNat (← hexVal (← j.getStr?)))
def vec2 (j : Json) : Except String Vec2 := do
  match ← j.getArr? with
  | #[x, y] => return ⟨← f32 x, ← f32 y⟩
  | _ => throw "vec2: expected 2 elements"

def field (j : Json) (k : String) : Except String Json := j.getObjVal? k
def fF64 (j : Json) (k : String) : Except String F64 := do f64 (← field j k)
def fF32 (j : Json) (k : String) : Except String F32 := do f32 (← field j k)
def fNat (j : Json) (k : String) : Except String Nat := do (← field j k).getNat?
def fInt (j : Json) (k : String) : Except String Int := do (← field j k).getInt?
def fBool (j : Json) (k : String) : Except String Bool := do (← field j k).getBool?
def fStr (j : Json) (k : String) : Except String String := do (← field j k).getStr?
def fResult (j : Json) (k : String) : Except String HitResult := do
  let s ← fStr j k
  match HitResult.ofName? s with
  | some r => return r
  | none => throw s!"unknown HitResult {s}"

def optField (j : Json) {α : Type} (k : String) (d : α) (f : Json → Except String α) : Except String α :=
  match j.getObjVal? k with
  | .ok v => f v
  | .error _ => pure d

def hobj (j : Json) : Except String HObj := do
  let kindS ← fStr j "kind"
  let some kind := Kind.ofString? kindS | throw s!"unknown kind {kindS}"
  let hwA ← (← field j "hit_windows").getArr?
  let hitWindows ← match hwA with
    | #[g, o, m, x] => pure (some { great := ← f64 g, ok := ← f64 o, meh := ← f64 m, miss := ← f64 x })
    | _ => pure none
  -- Only OsuHitWindows are non-empty; empty windows are reported as all-zero.
  let hitWindows := match hitWindows with
    | some hw => if hw.miss == 0 then none else some hw
    | none => none
  let opt := @optField j
  return {
    kind, hitWindows, typeName := ← opt "type" kind.typeName (·.getStr?)
    start := ← fF64 j "start", endTime := ← fF64 j "end"
    pos := ← vec2 (← field j "pos"), stacked := ← vec2 (← field j "stacked")
    stackHeight := ← fInt j "stack_height", scale := ← fF32 j "scale", radius := ← fF64 j "radius"
    preempt := ← fF64 j "preempt", fadeIn := ← opt "fade_in" 0 f64, maxJudgementOffset := ← fF64 j "max_judgement_offset"
    maxResult := ← fResult j "max_result", minResult := ← fResult j "min_result"
    newCombo := ← fBool j "new_combo", comboIndex := ← fNat j "combo_index"
    indexInCombo := ← fNat j "index_in_combo", lastInCombo := ← fBool j "last_in_combo"
    spanIndex := ← opt "span_index" 0 (·.getNat?)
    spanStart := ← opt "span_start" 0 f64
    pathProgress := ← opt "path_progress" 0 f64
    repeatIndex := ← opt "repeat_index" 0 (·.getNat?) }

def topObj (j : Json) : Except String TopObj := do
  let h ← hobj j
  let nested ← (← (← field j "nested").getArr?).mapM hobj
  match h.kind with
  | .slider =>
    let pa ← (← field j "path").getArr?
    if pa.size % 2 != 0 then throw "slider path: odd number of coordinates"
    let mut path : Array Vec2 := #[]
    for h : i in [0:pa.size / 2] do
      have hu : i < pa.size / 2 := h.upper
      path := path.push ⟨← f32 (pa[2*i]'(by omega)), ← f32 (pa[2*i+1]'(by omega))⟩
    let cumLen ← (← (← field j "cumulative_length").getArr?).mapM f64
    return { h, nested, slider := some {
      spanCount := ← fNat j "span_count", duration := ← fF64 j "duration"
      spanDuration := ← fF64 j "span_duration", velocity := ← fF64 j "velocity"
      pathDistance := ← fF64 j "path_distance", classic := ← fBool j "classic", path, cumLen } }
  | .spinner =>
    return { h, nested, spinner := some {
      duration := ← fF64 j "duration", spinsRequired := ← fInt j "spins_required"
      maxBonusSpins := ← fInt j "maximum_bonus_spins" } }
  | _ => return { h, nested }

def difficulty (j : Json) : Except String Difficulty := do
  return { cs := ← fF32 j "cs", hp := ← fF32 j "hp", od := ← fF32 j "od", ar := ← fF32 j "ar" }

def playable (j : Json) : Except String Playable := do
  let fmt ← fStr j "format"
  if fmt != "playable-1" then throw s!"unsupported playable format {fmt}"
  let d ← field j "difficulty"
  let breaks ← (← (← field j "breaks").getArr?).mapM fun b => do
    match ← b.getArr? with
    | #[s, e] => return (← f64 s, ← f64 e)
    | _ => throw "break: expected [start, end]"
  return {
    beatmapVersion := ← fInt j "beatmap_version"
    audioLeadIn := ← fF64 j "audio_lead_in"
    difficulty := ← difficulty d
    baseDifficulty := ← difficulty (← field j "base_difficulty")
    sliderMultiplier := ← fF64 d "slider_multiplier"
    sliderTickRate := ← fF64 d "slider_tick_rate"
    breaks
    objects := ← (← (← field j "objects").getArr?).mapM topObj }

def playableOfString (s : String) : Except String Playable := do
  playable (← Json.parse s)
end Load

end OsuModel.Sim
