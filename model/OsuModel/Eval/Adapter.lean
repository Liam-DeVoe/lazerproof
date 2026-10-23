import OsuModel.Beatmap
import OsuModel.Sim.Playable

/-!
# Beatmap model → simulation input (`OsuModel.Beatmap.PlayableBeatmap` → `OsuModel.Sim.Playable`)

The sim consumes exactly the fields the oracle's `--dump-playable` writes (`oracle/Dump.cs:68-215`, the C# getters
of the playable `IBeatmap`'s objects). Each field below is the Beatmap model's counterpart of that getter:

| dump key (`Dump.cs`) | C# getter | Beatmap model |
|---|---|---|
| `start`, `end` | `StartTime`, `GetEndTime()` | `startTime`, `OsuHitObject.endTime` (nested: no duration → start) |
| `pos`, `stacked` | `Position`, `StackedPosition` | `position`, `stackedPosition` |
| `stack_height`, `scale`, `radius`, `preempt`, `fade_in` | | `stackHeight`, `scale`, `radius`, `timePreempt`, `timeFadeIn` |
| `max_judgement_offset` | `MaximumJudgementOffset` | `maximumJudgementOffset` |
| `hit_windows` | `HitWindows.WindowFor(Great/Ok/Meh/Miss)` | `.osu g o m` → `(g, o, m, 400)`; `.empty` → none |
| `max_result`/`min_result` | `CreateJudgement()` (`Objects/*.cs`, see `judgementOf`) | from kind + `classicSliderBehaviour` / strict tracking |
| `new_combo`, `combo_index`, `index_in_combo`, `last_in_combo` | combo bindables (nested: bound to the parent's index fields, `HitObject.cs:115-127`; own `NewCombo`/`LastInCombo` stay false) | |
| `span_index`, `span_start`, `path_progress`, `repeat_index` | `SliderTick`/`SliderRepeat`/`SliderTailCircle` | same names |
| slider `span_count`, `duration`, `span_duration`, `velocity`, `path_distance`, `classic`, `path`, `cumulative_length` | `SpanCount()`, …, `Path.Distance`, `ClassicSliderBehaviour`, private `calculatedPath`/`cumulativeLength` | `SliderData`, `SliderPath` caches |
| spinner `duration`, `spins_required`, `maximum_bonus_spins` | | `SpinnerData` |
| `beatmap_version`, `audio_lead_in`, `difficulty`, `base_difficulty`, `breaks` | `IBeatmap` | `PlayableBeatmap` |

Losslessness is checked against the oracle's dump with `evaltest --dump-playable` (`difftest/eval_diff.py playable`).
-/

namespace OsuModel.Eval
open OsuModel.Net
open OsuModel.Beatmap (PlayableBeatmap OsuHitObject NestedObject NestedKind ObjectKind)
open OsuModel.Sim (HitResult Kind)

def vec (v : OsuModel.Beatmap.Vec2) : OsuModel.Sim.Vec2 := ⟨v.x, v.y⟩

def windows : OsuModel.Beatmap.HitWindows → Option OsuModel.Sim.HitWindows
  | .empty => none
  | .osu g o m => some { great := g, ok := o, meh := m, miss := OsuModel.Beatmap.MISS_WINDOW }

/-- `Judgement.MinResult` default (`osu.Game/Rulesets/Judgements/Judgement.cs:61-84`). -/
def defaultMinResult : HitResult → HitResult
  | .smallBonus | .largeBonus | .ignoreHit => .ignoreMiss
  | .smallTickHit => .smallTickMiss
  | .largeTickHit => .largeTickMiss
  | .sliderTailHit => .ignoreMiss
  | _ => .miss

/-- `CreateJudgement()` → (MaxResult, MinResult):
`HitCircle.cs:11` OsuJudgement (Great); `Slider.cs:289-293` classic ? OsuJudgement : OsuIgnoreJudgement (IgnoreHit);
`SliderHeadCircle.cs:17` classic ? SliderTickJudgement (LargeTickHit) : OsuJudgement; `SliderTick.cs:36`
SliderTickJudgement; `SliderEndCircle.cs:49-54` (repeat) SliderEndJudgement (LargeTickHit);
`SliderTailCircle.cs:23-34` classic ? LegacyTailJudgement (SmallTickHit) : TailJudgement (SliderTailHit);
`OsuModStrictTracking.cs:88-94` StrictTrackingTailJudgement (SliderTailHit, MinResult LargeTickMiss);
`Spinner.cs:98` OsuJudgement; `SpinnerTick.cs:17,23-26` SmallBonus; `SpinnerBonusTick.cs:11-16` LargeBonus. -/
def judgementOf (k : Kind) (classic strictTail : Bool) : HitResult × HitResult :=
  let mx : HitResult := match k with
    | .circle | .spinner => .great
    | .slider => if classic then .great else .ignoreHit
    | .head => if classic then .largeTickHit else .great
    | .tick | .«repeat» => .largeTickHit
    | .tail => if strictTail then .sliderTailHit else if classic then .smallTickHit else .sliderTailHit
    | .spinnerTick => .smallBonus
    | .spinnerBonusTick => .largeBonus
  let mn := if k == .tail && strictTail then .largeTickMiss else defaultMinResult mx
  (mx, mn)

def nestedKind : NestedKind → Kind
  | .head => .head | .tick => .tick | .repeat => .«repeat» | .tail => .tail
  | .spinnerTick => .spinnerTick | .spinnerBonusTick => .spinnerBonusTick

def nestedTypeName (n : NestedObject) : String :=
  match n.kind with
  | .tail => if n.strictTrackingTail then "StrictTrackingSliderTailCircle" else "SliderTailCircle"
  | k => (nestedKind k).typeName

def adaptNested (h : OsuHitObject) (n : NestedObject) : OsuModel.Sim.HObj :=
  let kind := nestedKind n.kind
  let (maxResult, minResult) := judgementOf kind n.classicSliderBehaviour n.strictTrackingTail
  { kind, typeName := nestedTypeName n
    start := n.startTime, endTime := n.startTime
    pos := vec n.position, stacked := vec n.stackedPosition
    stackHeight := n.stackHeight.toInt, scale := n.scale, radius := n.radius, preempt := n.timePreempt
    fadeIn := n.timeFadeIn
    maxJudgementOffset := n.maximumJudgementOffset, hitWindows := windows n.hitWindows
    maxResult, minResult
    newCombo := false, comboIndex := h.comboIndex.toNatClampNeg, indexInCombo := h.indexInCurrentCombo.toNatClampNeg
    lastInCombo := false
    spanIndex := n.spanIndex.toNatClampNeg, spanStart := n.spanStartTime, pathProgress := n.pathProgress
    repeatIndex := n.repeatIndex.toNatClampNeg }

def adaptObject (h : OsuHitObject) : OsuModel.Sim.TopObj :=
  let (kind, typeName, classic, slider, spinner) : Kind × String × Bool × Option OsuModel.Sim.SliderData ×
      Option OsuModel.Sim.SpinnerData :=
    match h.kind with
    | .circle => (.circle, "HitCircle", false, none, none)
    | .slider s =>
      (.slider, (if s.strictTracking then "StrictTrackingSlider" else "Slider"), s.classicSliderBehaviour,
       some { spanCount := s.spanCount.toNatClampNeg, duration := h.duration, spanDuration := h.spanDuration
              velocity := s.velocity, pathDistance := s.path.distance, classic := s.classicSliderBehaviour
              path := s.path.calculatedPath.map vec, cumLen := s.path.cumulativeLength }, none)
    | .spinner s =>
      (.spinner, "Spinner", false, none,
       some { duration := s.duration, spinsRequired := s.spinsRequired.toInt, maxBonusSpins := s.maximumBonusSpins.toInt })
  let (maxResult, minResult) := judgementOf kind classic false
  { h := { kind, typeName
           start := h.startTime, endTime := h.endTime
           pos := vec h.position, stacked := vec h.stackedPosition
           stackHeight := h.stackHeight.toInt, scale := h.scale, radius := h.radius, preempt := h.timePreempt
           fadeIn := h.timeFadeIn
           maxJudgementOffset := h.maximumJudgementOffset
           hitWindows := match h.hitWindows with | some w => windows w | none => none
           maxResult, minResult
           newCombo := h.newCombo, comboIndex := h.comboIndex.toNatClampNeg
           indexInCombo := h.indexInCurrentCombo.toNatClampNeg, lastInCombo := h.lastInCombo }
    slider, spinner
    nested := h.nested.map (adaptNested h) }

def adaptDifficulty (d : OsuModel.Beatmap.Difficulty) : OsuModel.Sim.Difficulty :=
  { cs := d.circleSize, hp := d.drainRate, od := d.overallDifficulty, ar := d.approachRate }

/-- The adapter. -/
def toSimPlayable (pb : PlayableBeatmap) : OsuModel.Sim.Playable :=
  { beatmapVersion := pb.formatVersion.toInt
    audioLeadIn := pb.audioLeadIn
    difficulty := adaptDifficulty pb.difficulty
    baseDifficulty := adaptDifficulty pb.baseDifficulty
    sliderMultiplier := pb.difficulty.sliderMultiplier
    sliderTickRate := pb.difficulty.sliderTickRate
    breaks := pb.breaks.map fun b => (b.startTime, b.endTime)
    objects := pb.hitObjects.map adaptObject }

/-! ## Dump in the oracle's `--dump-playable` format ("playable-1"), restricted to the keys the sim reads -/

section Dump
open OsuModel.Sim (F64.hex F32.hex)

def js (s : String) : String := "\"" ++ s ++ "\""
def hx (x : F64) : String := js (OsuModel.Sim.F64.hex x)
def hf (x : F32) : String := js (OsuModel.Sim.F32.hex x)
def hv (v : OsuModel.Sim.Vec2) : String := "[" ++ hf v.x ++ "," ++ hf v.y ++ "]"
def obj (kvs : List (String × String)) : String :=
  "{" ++ ",".intercalate (kvs.map fun (k, v) => js k ++ ":" ++ v) ++ "}"
def arr (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"

def kindKey : Kind → String
  | .circle => "circle" | .slider => "slider" | .spinner => "spinner" | .head => "head" | .tick => "tick"
  | .«repeat» => "repeat" | .tail => "tail" | .spinnerTick => "spinner_tick" | .spinnerBonusTick => "spinner_bonus_tick"

def hobjKvs (h : OsuModel.Sim.HObj) : List (String × String) :=
  let hw := match h.hitWindows with
    | some w => arr [hx w.great, hx w.ok, hx w.meh, hx w.miss]
    | none => arr [hx 0, hx 0, hx 0, hx 0]
  [("kind", js (kindKey h.kind)), ("type", js h.typeName), ("start", hx h.start), ("end", hx h.endTime),
   ("pos", hv h.pos), ("stacked", hv h.stacked), ("stack_height", toString h.stackHeight), ("scale", hf h.scale),
   ("radius", hx h.radius), ("preempt", hx h.preempt), ("fade_in", hx h.fadeIn), ("max_judgement_offset", hx h.maxJudgementOffset),
   ("hit_windows", hw), ("max_result", js h.maxResult.name), ("min_result", js h.minResult.name),
   ("new_combo", toString h.newCombo), ("combo_index", toString h.comboIndex),
   ("index_in_combo", toString h.indexInCombo), ("last_in_combo", toString h.lastInCombo)]

def nestedJson (h : OsuModel.Sim.HObj) : String :=
  let extra := match h.kind with
    | .tick => [("span_index", toString h.spanIndex), ("span_start", hx h.spanStart), ("path_progress", hx h.pathProgress)]
    | .«repeat» => [("repeat_index", toString h.repeatIndex), ("path_progress", hx h.pathProgress)]
    | .tail => [("repeat_index", toString h.repeatIndex)]
    | _ => []
  obj (hobjKvs h ++ extra)

def topJson (o : OsuModel.Sim.TopObj) : String :=
  let extra := match o.slider, o.spinner with
    | some s, _ => [("span_count", toString s.spanCount), ("duration", hx s.duration), ("span_duration", hx s.spanDuration),
        ("velocity", hx s.velocity), ("path_distance", hx s.pathDistance), ("classic", toString s.classic),
        ("path", arr (s.path.toList.flatMap fun v => [hf v.x, hf v.y])), ("cumulative_length", arr (s.cumLen.toList.map hx))]
    | none, some s => [("duration", hx s.duration), ("spins_required", toString s.spinsRequired),
        ("maximum_bonus_spins", toString s.maxBonusSpins)]
    | none, none => []
  obj (hobjKvs o.h ++ extra ++ [("nested", arr (o.nested.toList.map nestedJson))])

def diffJson (d : OsuModel.Sim.Difficulty) (extra : List (String × String)) : String :=
  obj ([("cs", hf d.cs), ("hp", hf d.hp), ("od", hf d.od), ("ar", hf d.ar)] ++ extra)

/-- `Sim.Playable` as oracle `--dump-playable` JSON (only keys the sim reads; `judgement`,
`repeat_count`, `tick_distance*`, `generate_ticks`, `end_position` are not part of the sim interface). -/
def playableJson (p : OsuModel.Sim.Playable) : String :=
  obj [("format", js "playable-1"), ("beatmap_version", toString p.beatmapVersion), ("audio_lead_in", hx p.audioLeadIn),
       ("difficulty", diffJson p.difficulty [("slider_multiplier", hx p.sliderMultiplier), ("slider_tick_rate", hx p.sliderTickRate)]),
       ("base_difficulty", diffJson p.baseDifficulty []),
       ("breaks", arr (p.breaks.toList.map fun (a, b) => arr [hx a, hx b])),
       ("objects", arr (p.objects.toList.map topJson))]
end Dump

end OsuModel.Eval
