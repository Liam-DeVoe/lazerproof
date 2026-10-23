import OsuModel.Sim.Playable

/-!
# Score and health processors (M4)

* `ScoreProcessor` (`osu.Game/Rulesets/Scoring/ScoreProcessor.cs`, `OsuScoreProcessor.cs`): combo, statistics,
  accuracy, standardised total score, rank; maxima from `JudgementProcessor.SimulateAutoplay`.
* Health: `OsuHealthProcessor` (`DrainingHealthProcessor`, `HealthProcessor`) and, with Classic's `ClassicHealth`,
  `OsuLegacyHealthProcessor` (`LegacyDrainingHealthProcessor`); drain rate computation, per-step drain with
  break no-drain periods (`PeriodTracker`), default fail condition.
* Score multiplier: `OsuScoreMultiplierCalculatorV2` for the mods in scope.
All doubles in source order.
-/

namespace OsuModel.Sim
open OsuModel.Net

/-- `IBeatmapDifficultyInfo.DifficultyRange(difficulty, min, mid, max)` (`osu.Game/Beatmaps/IBeatmapDifficultyInfo.cs:57-72`):
`mid + (max - mid) * DifficultyRange(difficulty)` with `DifficultyRange(d) = (d - 5) / 5` (note the association). -/
def difficultyRange (d mn mid mx : F64) : F64 :=
  if 5 < d then mid + (mx - mid) * ((d - 5) / 5)
  else if d < 5 then mid + (mid - mn) * ((d - 5) / 5)
  else mid

/-- `ScoreProcessor.GetBaseScoreForResult` -/
def baseScore : HitResult → Nat
  | .smallTickHit => 10 | .largeTickHit => 30 | .sliderTailHit => 150 | .meh => 50 | .ok => 100
  | .good => 200 | .great | .perfect => 300 | .smallBonus => 10 | .largeBonus => 50 | _ => 0

/-- What the processors need to know about the judged object. -/
structure JInfo where
  kind : Kind
  maxResult : HitResult
  minResult : HitResult := .none
  ty : HitResult
  /-- `JudgementResult.TimeAbsolute` -/
  timeAbsolute : F64
  /-- `HitObject.GetEndTime()`, `TimeOffset` (for simulated health increase times) -/
  endTime : F64
  timeOffset : F64
  newCombo : Bool
  lastInCombo : Bool
deriving Inhabited

/-! ## ScoreProcessor -/

inductive Rank where
  | d | c | b | a | s | sh | x | xh | f
deriving Inhabited, Repr, DecidableEq, BEq

def Rank.name : Rank → String
  | .d => "D" | .c => "C" | .b => "B" | .a => "A" | .s => "S" | .sh => "SH" | .x => "X" | .xh => "XH" | .f => "F"


/-- Size of the per-`HitResult` statistics array (enum values `0..99`). -/
def nStats : Nat := 100
theorem HitResult.toNat_lt (r : HitResult) : r.toNat < nStats := by cases r <;> decide

structure ScoreSt where
  combo : Nat := 0
  highestCombo : Nat := 0
  stats : Array Nat := Array.replicate nStats 0
  stats_size : stats.size = nStats := by simp
  currentMaximumBaseScore : F64 := 0
  currentBaseScore : F64 := 0
  currentAccuracyJudgementCount : Nat := 0
  currentComboPortion : F64 := 0
  currentBonusPortion : F64 := 0
  accuracy : F64 := 1
  totalScoreWithoutMods : Int := 0
  totalScore : Int := 0
  judgedHits : Nat := 0
  lastTimeAbsolute : Option F64 := none
  hasCompleted : Bool := false
  /-- `MaximumAccuracy` (BindableDouble [0, 1]) -/
  maximumAccuracy : F64 := 1
  /-- `ScoreProcessor.rank` (updated on `Accuracy.ValueChanged`, `ScoreProcessor.cs:210,404-416`) -/
  rank : Rank := .x

instance : Inhabited ScoreSt := ⟨{}⟩

/-- `Statistics[r]` (total: the array always has `nStats` entries). -/
def ScoreSt.stat (s : ScoreSt) (r : HitResult) : Nat :=
  s.stats[r.toNat]'(s.stats_size ▸ r.toNat_lt)

structure ScoreMax where
  maximumBaseScore : F64 := 0
  maximumComboPortion : F64 := 0
  maximumAccuracyJudgementCount : Nat := 0
  maxStats : Array Nat := Array.replicate 100 0
  maxHits : Nat := 0
  scoreMultiplier : F64 := 1
  /-- any `AdjustRank` that changes ranks (HD, FL) -/
  rankAdjust : Bool := false
  /-- `TotalScoreWithoutMods` after `ApplyBeatmap`: `Reset(storeResults: true)` (`ScoreProcessor.cs:438-470`) first
  runs `updateScore()` on the simulated perfect play (with the maxima of the preceding `Reset(false)`, i.e. all 0) and
  then resets `TotalScore` but NOT `TotalScoreWithoutMods`, which keeps this value until the first `updateScore()`
  of the play (D80a) -/
  initWithoutMods : Int := 0
deriving Inhabited

/-- `BindableDouble { MinValue = 0, MaxValue = 1 }` set (precision `double.Epsilon` → no decimal rounding; clamp). -/
def zeroD : F64 := 0
def oneD : F64 := 1
/-- `Math.Clamp(x, lo, hi)` for literal bounds with `lo ≤ hi`: the `ArgumentException` branch of
`Math.Clamp` (`hi < lo`) is dead, so this is exactly its non-throwing branch (`OsuModel.Net.MathOps` `clamp`). -/
def clampK (x lo hi : F64) : F64 := if x < lo then lo else if hi < x then hi else x
def clamp01 (x : F64) : F64 := clampK x zeroD oneD

/-- `ScoreProcessor.RankFromScore` + `OsuScoreProcessor.RankFromScore` . -/
def rankFromScore (acc : F64) (missCount : Nat) : Rank :=
  let r := if acc == 1 then Rank.x else if 0.95 ≤ acc then .s else if 0.9 ≤ acc then .a
    else if 0.8 ≤ acc then .b else if 0.7 ≤ acc then .c else .d
  match r with
  | .s | .x => if missCount > 0 then .a else r
  | _ => r

/-- `ModHidden.AdjustRank` / `ModFlashlight.AdjustRank` (`ModHidden.cs:23-36`, `ModFlashlight.cs:64-77`). -/
def adjustRank (adj : Bool) (r : Rank) : Rank :=
  if !adj then r else match r with | .x => .xh | .s => .sh | r => r

/-- `ScoreProcessor.updateScore` (`ScoreProcessor.cs:391-402`, `ComputeTotalScore` `:427-432`). -/
def ScoreSt.updateScore (s : ScoreSt) (m : ScoreMax) : ScoreSt :=
  let accuracy := clamp01 (if 0 < s.currentMaximumBaseScore then s.currentBaseScore / s.currentMaximumBaseScore else 1)
  -- `Accuracy.ValueChanged += updateRank` (only on an actual change: `Bindable` Equals check)
  let rank := if Framework.Bindable.equalsD s.accuracy accuracy || s.rank == .f then s.rank
    else adjustRank m.rankAdjust (rankFromScore accuracy (s.stat .miss))
  let maximumAccuracy := clamp01 (if 0 < m.maximumBaseScore
    then (s.currentBaseScore + (m.maximumBaseScore - s.currentMaximumBaseScore)) / m.maximumBaseScore else 1)
  let comboProgress := if 0 < m.maximumComboPortion then s.currentComboPortion / m.maximumComboPortion else 1
  let accuracyProgress := if m.maximumAccuracyJudgementCount > 0
    then F64.ofInt s.currentAccuracyJudgementCount / F64.ofInt m.maximumAccuracyJudgementCount else 1
  let total := 500000 * accuracy * comboProgress + 500000 * F64.pow accuracy 5 * accuracyProgress + s.currentBonusPortion
  -- BindableLong { MinValue = 0 }
  let withoutMods := max 0 (F64.toInt64 (F64.round total)).toInt
  let tot := max 0 (F64.toInt64 (F64.round (F64.ofInt withoutMods * m.scoreMultiplier))).toInt
  { s with accuracy, totalScoreWithoutMods := withoutMods, totalScore := tot, rank, maximumAccuracy }

/-- `JudgementProcessor.ApplyResult` + `ScoreProcessor.ApplyResultInternal` (`:239-285`).
Returns the new state and `ComboAfterJudgement` (0 if ignored because failed). -/
def ScoreSt.apply (s : ScoreSt) (m : ScoreMax) (j : JInfo) (failedAtJudgement : Bool) (simulating : Bool) : ScoreSt × Nat :=
  let s := { s with judgedHits := s.judgedHits + 1, lastTimeAbsolute := some j.timeAbsolute }
  if failedAtJudgement then (s, 0)
  else
    let ty := j.ty
    let s := { s with stats := s.stats.modify ty.toNat (· + 1), stats_size := by simp [s.stats_size] }
    let combo := if ty.increasesCombo then s.combo + 1 else if ty.breaksCombo then 0 else s.combo
    let s := { s with combo, highestCombo := Nat.max s.highestCombo combo }
    let s := if j.maxResult.affectsAccuracy then
        { s with currentMaximumBaseScore := s.currentMaximumBaseScore + F64.ofInt (baseScore j.maxResult)
                 currentAccuracyJudgementCount := s.currentAccuracyJudgementCount + 1 }
      else s
    let s := if ty.affectsAccuracy then { s with currentBaseScore := s.currentBaseScore + F64.ofInt (baseScore ty) } else s
    let s := if ty.isBonus then { s with currentBonusPortion := s.currentBonusPortion + F64.ofInt (baseScore ty) }
      else if ty.isScorable then
        { s with currentComboPortion := s.currentComboPortion
            + F64.ofInt (baseScore j.maxResult) * F64.pow (F64.ofInt combo) 0.5 }
      else s
    let s := if simulating then s else s.updateScore m
    (s, combo)

/-! ## Health -/

/-- `OsuHealthProcessor.getHealthIncreaseFor` (`OsuHealthProcessor.cs:77-126`) — also the legacy table
before the `HpMultiplierNormal` factor. `Judgement.HealthIncreaseFor` default for other results is 0
(osu! judgements do not override it except through these processors). -/
def osuHealthIncrease (hp : F64) (kind : Kind) (ty : HitResult) : F64 :=
  match ty with
  | .smallTickMiss | .largeTickMiss => difficultyRange hp (-0.02) (-0.075) (-0.14)
  | .miss => difficultyRange hp (-0.03) (-0.125) (-0.2)
  | .smallTickHit => 0.02
  | .sliderTailHit | .largeTickHit =>
    match kind with
    | .tick => 0.015
    | .head | .tail | .«repeat» => 0.02
    | _ => 0
  | .meh => 0.002 | .ok => 0.011 | .great => 0.03 | .smallBonus => 0.0085 | .largeBonus => 0.01
  | _ => 0

/-- `OsuLegacyHealthProcessor.GetHealthIncreaseFor(hitObject, result)` (`OsuLegacyHealthProcessor.cs:40-86`). -/
def legacyHealthIncrease (hp mult : F64) (kind : Kind) (ty : HitResult) : F64 :=
  match ty with
  | .smallTickMiss | .largeTickMiss => difficultyRange hp (-0.02) (-0.075) (-0.14)
  | .miss => difficultyRange hp (-0.03) (-0.125) (-0.2)
  | _ =>
    let inc : F64 := match ty with
      | .smallTickHit => 0.02
      | .sliderTailHit | .largeTickHit => if kind == .tick then 0.015 else 0.02
      | .meh => 0.002 | .ok => 0.011 | .great => 0.03 | .smallBonus => 0.0085 | .largeBonus => 0.01
      | _ => 0
    mult * inc

/-- `OsuHealthProcessor` combo-end bonus state (`ComboResult`: None=0 < Good=1 < Perfect=2). -/
structure HealthSt where
  health : F64 := 1
  hasFailed : Bool := false
  comboResult : Nat := 2
  /-- `PeriodTracker.nearestIndex` -/
  nearestIndex : Nat := 0
  failTriggers : Nat := 0
  failed : Bool := false
  failTime : Option F64 := none
  /-- remaining lives of each EZ (`ModEasyWithExtraLives.retries`) -/
  retries : Array Nat := #[]
deriving Inhabited

structure HealthCfg where
  legacy : Bool
  hp : F64
  drainRate : F64
  hpMultiplierNormal : F64 := 1
  drainStartTime : F64
  gameplayEndTime : F64
  /-- `noDrainPeriodTracker` periods sorted by start (`OrderBy`, stable). -/
  periods : Array (F64 × F64)
deriving Inhabited

/-- `OsuHealthProcessor.GetHealthIncreaseFor(result)` incl. the combo-end bonus (not when simulating). -/
def HealthSt.increaseFor (h : HealthSt) (c : HealthCfg) (j : JInfo) (simulating : Bool) : HealthSt × F64 :=
  if c.legacy then (h, legacyHealthIncrease c.hp c.hpMultiplierNormal j.kind j.ty)
  else if simulating then (h, osuHealthIncrease c.hp j.kind j.ty)
  else
    -- every OsuHitObject is IHasComboInformation (nested objects: NewCombo/LastInCombo as dumped)
    let cr0 := if j.newCombo then 2 else h.comboResult
    let set (cr v : Nat) := Nat.min cr v
    let cr1 := match j.ty with
      | .largeTickMiss | .ok => set cr0 1
      | .meh | .miss => set cr0 0
      | _ => cr0
    let cr2 := if j.kind == .tail && !j.ty.isHit then set cr1 1 else cr1
    let base := osuHealthIncrease c.hp j.kind j.ty
    let inc := if j.lastInCombo && j.ty.isHit then
        (if cr2 == 2 then base + 0.07 else if cr2 == 1 then base + 0.05 else base + 0.03)
      else base
    ({ h with comboResult := cr2 }, inc)

/-- `DrainingHealthProcessor.CheckDefaultFailCondition` → `Precision.AlmostBigger(Health.MinValue, Health.Value)`. -/
def defaultFailCondition (h : HealthSt) (j : JInfo) : Bool :=
  if j.maxResult.isBonus || j.ty == .ignoreHit then false
  else 0 > h.health - (Float.ofBits 0x3E7AD7F29ABCAF48 : F64)

/-- `PeriodTracker.IsInAny(time)` (stateful nearest index). -/
def periodIsInAny (ps : Array (F64 × F64)) (idx : Nat) (time : F64) : Except String (Bool × Nat) := do
  if ps.size == 0 then return (false, idx)
  let get (i : Nat) : Except String (F64 × F64) := match ps[i]? with
    | some p => pure p
    | none => throw s!"internal: period index {i} out of range (size {ps.size})"
  let mut i := idx
  -- the `while` loops move `i` by at most `ps.size - 1` steps, so `ps.size` iterations always reach the exit
  if (← get i).2 < time then
    for _ in [0:ps.size] do
      if (← get i).2 < time && i < ps.size - 1 then i := i + 1 else break
  else
    for _ in [0:ps.size] do
      if time < (← get i).1 && i > 0 then i := i - 1 else break
  let (s, e) ← get i
  return (s ≤ time && time ≤ e, i)

/-- `DrainingHealthProcessor.Update` drain at step time `t` with `Time.Elapsed = elapsed`. -/
def HealthSt.drain (h : HealthSt) (c : HealthCfg) (t elapsed : F64) : Except String HealthSt := do
  let (inAny, idx) ← periodIsInAny c.periods h.nearestIndex t
  let h := { h with nearestIndex := idx }
  if inAny then return h
  else
    -- `Math.Clamp(…, drainStartTime, gameplayEndTime)` throws if the bounds are inverted
    let cl (x : F64) : Except String F64 := match F64.clamp x c.drainStartTime c.gameplayEndTime with
      | .ok v => pure v
      | .error e => throw s!"lazer would throw: Math.Clamp {repr e} (drain bounds)"
    let lastT ← cl (t - elapsed)
    let curT ← cl t
    return { h with health := clamp01 (h.health - c.drainRate * (curT - lastT)) }

/-! ## Maxima and drain rates (`ApplyBeatmap`: Reset(false); SimulateAutoplay; Reset(true)) -/

/-- `JudgementProcessor.enumerateRecursively`: nested first (recursively), then the object. -/
def simulatedJudgements (pb : Playable) : Array JInfo := Id.run do
  let mut out : Array JInfo := #[]
  for o in pb.objects do
    for n in o.nested do
      out := out.push { kind := n.kind, maxResult := n.maxResult, ty := n.maxResult, timeAbsolute := n.endTime
                        endTime := n.endTime, timeOffset := 0, newCombo := n.newCombo, lastInCombo := n.lastInCombo }
    out := out.push { kind := o.h.kind, maxResult := o.h.maxResult, ty := o.h.maxResult, timeAbsolute := o.h.endTime
                      endTime := o.h.endTime, timeOffset := 0, newCombo := o.h.newCombo, lastInCombo := o.h.lastInCombo }
  return out

def scoreMaxima (pb : Playable) (mult : F64) : ScoreMax := Id.run do
  let m0 : ScoreMax := { scoreMultiplier := mult }
  let mut s : ScoreSt := {}
  for j in simulatedJudgements pb do
    s := (s.apply m0 j false true).1
  -- Reset(storeResults: true): updateScore() first (with the maxima still 0, as in `m0`); it does not change the
  -- stored values, but its `TotalScoreWithoutMods` survives the reset (`initWithoutMods`, D80a)
  return { m0 with maximumBaseScore := s.currentBaseScore, maximumComboPortion := s.currentComboPortion
                   maximumAccuracyJudgementCount := s.currentAccuracyJudgementCount, maxStats := s.stats
                   maxHits := s.judgedHits, initWithoutMods := (s.updateScore m0).totalScoreWithoutMods }

/-- `DrainingHealthProcessor.ComputeDrainRate` (`DrainingHealthProcessor.cs:163-213`). -/
def computeDrainRate (incs : Array (F64 × F64)) (breaks : Array (F64 × F64)) (drainStart target : F64) :
    Except String F64 := do
  if incs.size ≤ 1 then return 0
  let mut adjustment : Int32 := 1
  let mut result : F64 := 1
  -- `adjustment` doubles each round, so the Int32 overflows to ≤ 0 within 32 rounds; fuel 100000 never runs out
  let mut fuel := 100000
  while 0 < adjustment && fuel > 0 do
    fuel := fuel - 1
    let mut currentHealth : F64 := 1
    let mut lowestHealth : F64 := 1
    let mut currentBreak := 0
    for h : i in [0:incs.size] do
      let currentTime := (incs[i]'h.upper).1
      let mut lastTime := if hp : 0 < i then (incs[i-1]'(by have hu : i < incs.size := h.upper; omega)).1 else drainStart
      -- `while (currentBreak < breaks.Count && breaks[currentBreak].EndTime <= currentTime)`: ≤ breaks.size steps
      for _ in [0:breaks.size] do
        match breaks[currentBreak]? with
        | some b =>
          if b.2 ≤ currentTime then
            lastTime := currentTime
            currentBreak := currentBreak + 1
          else break
        | none => break
      currentHealth := currentHealth - (currentTime - lastTime) * result
      lowestHealth := F64.min lowestHealth currentHealth
      currentHealth := F64.min 1 (currentHealth + (incs[i]'h.upper).2)
      if lowestHealth < 0 then break
    if F64.abs (lowestHealth - target) ≤ 0.01 then break
    adjustment := adjustment * 2
    -- `Math.Sign(NaN)` throws `ArithmeticException`
    let sgn : Int ← match F64.sign (lowestHealth - target) with
      | .ok v => pure v.toInt
      | .error e => throw s!"lazer would throw: Math.Sign {repr e} (ComputeDrainRate)"
    result := result + 1.0 / F64.ofInt32 adjustment * F64.ofInt sgn
  if fuel == 0 && 0 < adjustment then throw "internal: ComputeDrainRate fuel exhausted"
  return result

/-- `LegacyDrainingHealthProcessor.ComputeDrainRate` (`LegacyDrainingHealthProcessor.cs:46-158`).
Returns `(testDrop, HpMultiplierNormal)`. -/
def computeLegacyDrainRate (pb : Playable) (hp drainStart : F64) : Except String (F64 × F64) := do
  let lowestHpEver := difficultyRange hp 0.975 0.8 0.3
  let lowestHpEnd := difficultyRange hp 0.99 0.9 0.4
  let hpRecoveryAvailable := difficultyRange hp 0.04 0.02 0
  let mut mult : F64 := 1
  let mut testDrop : F64 := 0.00025
  let mut fuel := 1000000
  while fuel > 0 do
    fuel := fuel - 1
    let mut currentHp : F64 := 1
    let mut currentHpUncapped : F64 := 1
    let mut lowestHp := currentHp
    let mut lastTime := drainStart
    let mut currentBreak := 0
    let mut fail := false
    let mut topLevelObjectCount : Nat := 0
    for o in pb.objects do
      topLevelObjectCount := topLevelObjectCount + 1
      let h := o.h
      for _ in [0:pb.breaks.size] do
        match pb.breaks[currentBreak]? with
        | some b =>
          if b.2 ≤ h.start then
            lastTime := h.start
            currentBreak := currentBreak + 1
          else break
        | none => break
      -- reduceHp(testDrop * (h.StartTime - lastTime))
      let amt := testDrop * (h.start - lastTime)
      currentHpUncapped := F64.max 0 (currentHpUncapped - amt)
      currentHp := F64.max 0 (currentHp - amt)
      lastTime := h.endTime
      if currentHp < lowestHp then lowestHp := currentHp
      if currentHp ≤ lowestHpEver then
        fail := true
        testDrop := testDrop * 0.96
        break
      let hpReduction := testDrop * (h.endTime - h.start)
      let hpOverkill := F64.max 0 (hpReduction - currentHp)
      currentHpUncapped := F64.max 0 (currentHpUncapped - hpReduction)
      currentHp := F64.max 0 (currentHp - hpReduction)
      for n in o.nested do
        if h.kind == .spinner && n.kind == .spinnerBonusTick then continue
        if h.kind != .slider && h.kind != .spinner then continue
        let amount := legacyHealthIncrease hp mult n.kind n.maxResult
        currentHpUncapped := currentHpUncapped + amount
        currentHp := F64.max 0 (F64.min 1 (currentHp + amount))
      if 0 < hpOverkill && currentHp - hpOverkill ≤ lowestHpEver then
        fail := true
        testDrop := testDrop * 0.96
        break
      let amount := legacyHealthIncrease hp mult h.kind h.maxResult
      currentHpUncapped := currentHpUncapped + amount
      currentHp := F64.max 0 (F64.min 1 (currentHp + amount))
    if topLevelObjectCount == 0 then return (testDrop, mult)
    if !fail && currentHp < lowestHpEnd then
      fail := true
      testDrop := testDrop * 0.94
      mult := mult * 1.01
    let recovery := (currentHpUncapped - 1) / F64.max 1 (F64.ofInt topLevelObjectCount)
    if !fail && recovery < hpRecoveryAvailable then
      fail := true
      testDrop := testDrop * 0.96
      mult := mult * 1.01
    if !fail && (mult == F64.posInf || mult == F64.negInf) then
      return (0, 1)
    if !fail then return (testDrop, mult)
  throw "internal: legacy ComputeDrainRate fuel exhausted"

/-- `DrainingHealthProcessor.ApplyBeatmap` no-drain periods (`DrainingHealthProcessor.cs:100-118`):
from the last end time ≤ break start (or `double.MinValue`) to the first start time ≥ break end (or `MaxValue`). -/
def noDrainPeriods (pb : Playable) : Array (F64 × F64) := Id.run do
  let dmax : F64 := Float.ofBits 0x7FEFFFFFFFFFFFFF
  let mut ps : Array (F64 × F64) := #[]
  for (bs, be) in pb.breaks do
    let mut s : F64 := -dmax
    for o in pb.objects do
      if o.h.endTime ≤ bs then s := o.h.endTime
    let mut e : F64 := dmax
    for o in pb.objects do
      if be ≤ o.h.start then
        e := o.h.start
        break
    ps := ps.push (s, e)
  -- OrderBy(period => period.Start) (stable)
  return stableSortBy ps (fun a b => a.1 < b.1)

/-- Build the health configuration (`HealthProcessor.ApplyBeatmap` incl. the simulated autoplay pass). -/
def mkHealthCfg (pb : Playable) (legacy : Bool) : Except String HealthCfg := do
  let hp := F32.toF64 pb.difficulty.hp
  let drainStart := match pb.objects[0]? with | some o => o.h.start | none => 0
  let gameplayEnd := match pb.objects.back? with | some o => o.h.endTime | none => 0
  let periods := noDrainPeriods pb
  if legacy then
    let (rate, mult) ← computeLegacyDrainRate pb hp drainStart
    return { legacy, hp, drainRate := rate, hpMultiplierNormal := mult, drainStartTime := drainStart
             gameplayEndTime := gameplayEnd, periods }
  else
    let target0 := difficultyRange hp 0.99 0.9 0.4
    let target1 := target0 + 0 * (1 - target0)   -- DrainLenience = 0
    let target := clampK target1 0 1
    -- simulated health increases (non-bonus results), time = EndTime + TimeOffset (0)
    let mut incs : Array (F64 × F64) := #[]
    let cfg0 : HealthCfg := { legacy, hp, drainRate := 0, drainStartTime := drainStart, gameplayEndTime := gameplayEnd, periods }
    for j in simulatedJudgements pb do
      if !j.ty.isBonus then
        incs := incs.push (j.endTime + j.timeOffset, (({} : HealthSt).increaseFor cfg0 j true).2)
    return { cfg0 with drainRate := ← computeDrainRate incs pb.breaks drainStart target }

end OsuModel.Sim
