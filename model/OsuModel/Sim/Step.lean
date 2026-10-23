import OsuModel.Sim.State
import OsuModel.Sim.AutoGen

/-!
# The frame-stable step (lazer-map §3.1)

`stepOnce` runs one FrameStabilityContainer sub-frame at the scheduled time `t`:

1. FrameStableComponents (ScoreProcessor/HealthProcessor `Update`): drain — not modelled before M4.
2. `RulesetInputManager.Update` (`osu.Framework/Input/InputManager.cs:459-513`):
   replay position (`OsuFramedReplayInputHandler.CollectReplayInputs`) → `MousePositionAbsoluteInput.Apply`
   (on change: MouseMove + `updateHoverEvents`) → `ReplayState.Apply` (all releases, then presses,
   `RulesetInputManager.HandleInputStateChange`) → high-frequency MouseMove → `updateHoverEvents` if not done.
3. `Playfield.Update` (no `IUpdatableByPlayfield` mods in scope).
4. `HitObjectContainer.CheckChildrenLife` (`PooledDrawableWithLifetimeContainer.cs`, `LifetimeEntryManager.Update`).
5. DHO subtrees in `HitObjectContainer` child order (later start first; ties: later ChildID first).

Judgement application (`DrawableHitObject.ApplyResult`, `DrawableHitObject.cs:726-751`) sets the result and
`RawTime = Time.Current`, updates the drawable state (lifetime from the hit-state transforms), then
invokes the result chain: `OsuPlayfield.onNewResult` → `IHitPolicy.HandleHit` (may force earlier misses,
which reach the processors first) → processors (`Player.cs:399-404`).
-/

namespace OsuModel.Sim
open OsuModel.Net OsuModel.Replay

/-- Reference to a (nested) hit object: top-level index and nested index (`-1` = the object itself). -/
abbrev Ref := Nat × Int

namespace Sim

-- the small accessors below are `@[inline]` so that their `pure` meets the caller's bind in the compiled code (no
-- `Except`/`Prod` allocation per access in the per-step loops); this does not change their meaning
@[inline] def ctx : SimM Ctx := read
@[inline] def st : SimM St := get

/-- Total array access in `SimM`: out of range rejects the input (an internal invariant violation), never a default. -/
def liftExcept {α : Type} (e : Except String α) : SimM α :=
  match e with
  | .ok v => pure v
  | .error m => throw m

/-- A .NET exception inside lazer's computation (e.g. `Math.Clamp` with `min > max`): lazer would throw, so the input is
rejected. -/
def liftNet {α : Type} (e : Except NetExn α) : SimM α :=
  match e with
  | .ok v => pure v
  | .error x => throw s!"lazer would throw: {repr x}"

@[inline] def getA {α : Type} (a : Array α) (i : Nat) (what : String) : SimM α :=
  if h : i < a.size then pure a[i] else throw s!"internal: index {i} out of range for {what} (size {a.size})"
@[inline] def need {α : Type} (o : Option α) (what : String) : SimM α :=
  match o with
  | some x => pure x
  | none => throw s!"internal: missing {what}"
/-- The range check of `getA` alone, for an update by `modify` right after it: `let s ← st; set { s with xs := ← setA
s.xs … }` would share `s.xs` with the monad state and so copy the whole array on every update; `modify` keeps it
uniquely referenced (in place). After the check, `Array.modify`'s out-of-range no-op branch is dead. -/
@[inline] def checkIdx {α : Type} (a : Array α) (i : Nat) (what : String) : SimM Unit :=
  if i < a.size then pure () else throw s!"internal: index {i} out of range for {what} (size {a.size})"
/-- `Array.set` that rejects instead of silently ignoring an out-of-range index. -/
@[inline] def setA {α : Type} (a : Array α) (i : Nat) (x : α) (what : String) : SimM (Array α) :=
  if h : i < a.size then pure (a.set i x h) else throw s!"internal: set index {i} out of range for {what} (size {a.size})"

@[inline] def topObj (i : Nat) : SimM TopObj := do getA (← ctx).pb.objects i "objects"
@[inline] def nestedOf (o : TopObj) (j : Nat) : SimM HObj := getA o.nested j "nested"
def hobjOf (r : Ref) : SimM HObj := do
  let o ← topObj r.1
  if r.2 < 0 then return o.h else nestedOf o r.2.toNat
@[inline] def ostate (i : Nat) : SimM OState := do getA (← st).objs i "objs"
def modifyObj (i : Nat) (f : OState → OState) : SimM Unit := do
  checkIdx (← st).objs i "objs"
  modify fun s => { s with objs := s.objs.modify i f }

def resOf (r : Ref) : SimM (Option Res) := do
  let o ← ostate r.1
  if r.2 < 0 then return o.result else getA o.nested r.2.toNat "nested results"

def judged (r : Ref) : SimM Bool := do return (← resOf r).isSome

/-- `HitObjectLifetimeEntry.AllJudged` / `DrawableHitObject.AllJudged`. -/
def allJudged (i : Nat) : SimM Bool := do
  let o ← ostate i
  return o.result.isSome && o.nested.all (·.isSome)

def isHitRef (r : Ref) : SimM Bool := do
  match ← resOf r with
  | some (ty, _) => return ty.isHit
  | none => return false

/-! ## Pooled DHO instances, transformable state, presence, current geometry (M7) -/

inductive Part where
  | top | head
deriving Inhabited, BEq

@[inline] def instOf (k : Nat) : SimM Inst := do getA (← st).insts k "insts"
def modifyInst (k : Nat) (f : Inst → Inst) : SimM Unit := do
  checkIdx (← st).insts k "insts"
  modify fun s => { s with insts := s.insts.modify k f }
@[inline] def headIdxOf (i : Nat) : SimM Nat := do getA (← ctx).headIdx i "headIdx"
@[inline] def stepAt (k : Nat) : SimM Step := do getA (← ctx).steps k "steps"
/-- `Time.Elapsed` of the frame-stable clock in the current step (0 in the first). -/
def elapsedNow : SimM F64 := do
  let s ← st
  if s.k == 0 then return 0 else return s.t - (← stepAt (s.k - 1)).time

def partInst (i : Nat) (p : Part) : SimM Nat := do
  let os ← ostate i
  return if p == .top then os.inst else os.headInst
def partRef (i : Nat) (p : Part) : SimM Ref := do
  if p == .top then return (i, -1) else return (i, ((← headIdxOf i) : Int))
def partArmed (i : Nat) (p : Part) : SimM Armed := do
  let os ← ostate i
  return if p == .top then os.armed else os.headArmed

/-- `DrawablePool.Get` (`DrawablePool.cs`): pop the LIFO stack, or construct; prewarmed (`none`) and new instances are
fresh (loaded, never `LoadComplete`d). -/
def poolGet (pk : Nat) : SimM Nat := do
  let s ← st
  match ← getA s.pools pk "pools" with
  | some k :: rest =>
    set { s with pools := ← setA s.pools pk rest "pools" }
    return k
  | none :: rest =>
    set { s with pools := ← setA s.pools pk rest "pools", insts := s.insts.push {} }
    return s.insts.size
  | [] =>
    set { s with insts := s.insts.push {} }
    return s.insts.size

/-- `DrawablePool.Return`: pushed unless `CountAvailable >= maximumSize`. -/
def poolReturn (pk k : Nat) : SimM Unit := do
  let s ← st
  let p ← getA s.pools pk "pools"
  if p.length ≥ (← getA poolMax pk "poolMax") then return
  set { s with pools := ← setA s.pools pk (some k :: p) "pools" }

def poolKind (k : Kind) : Nat :=
  match k with | .circle => 0 | .slider => 1 | .head => 2 | _ => 3

def placementOf (tf : TObj) : Placement := { pos := tf.pos, scale := tf.scale, rot := tf.rot }

/-- `DrawableHitObject.IsPresent` (`DrawableHitObject.cs:144`): `base.IsPresent || (State == Idle && now >= LifetimeStart)`,
`Drawable.IsPresent = Alpha > 0.0001f && DrawScale.X != 0 && DrawScale.Y != 0` (`Drawable.cs:1336-1342`). -/
def presentTf (tf : TObj) (armed : Armed) (now lifetimeStart : F64) : Bool :=
  (Float32.ofBits 0x38D1B717 < tf.alpha && !(tf.scale.x == 0) && !(tf.scale.y == 0)) ||
  (armed == .idle && lifetimeStart ≤ now)

def partPresent (i : Nat) (p : Part) : SimM Bool := do
  let os ← ostate i
  let k ← partInst i p
  let ins ← instOf k
  let ls ← if p == .top then pure os.lifetimeStart else do
    let hd ← nestedOf (← topObj i) (← headIdxOf i)
    pure (hd.start - hd.preempt)
  return (← ctx).cfg.dbgNoPresence || presentTf ins.tf (← partArmed i p) (← st).t ls

/-- `ModBarrelRoll.ApplyToDrawableRuleset`: `PlayfieldAdjustmentContainer.Scale = min/max of Playfield.DrawSize` at load
(the playfield is not laid out yet; its DrawSize is the pre-layout one of the first step). -/
def brScale (env : Env) : Vec2 :=
  let sz := env.hocSize   -- placeholder until checked against a BR dump
  let mn := F32.min sz.x sz.y
  let mx := F32.max sz.x sz.y
  ⟨mn / mx, mn / mx⟩

/-- The HitObjectContainer DrawInfo now (input phase of the first step: the pre-layout one); with BarrelRoll the
ancestor chain is recomposed with the rotated/scaled `OsuPlayfieldAdjustmentContainer`. -/
def curHoc : SimM DrawInfo := do
  let c ← ctx
  let s ← st
  match c.cfg.barrelRoll with
  | none => return if s.k == 0 then c.env.hocFirst else c.env.hoc
  | some _ =>
    let nodes := if s.k == 0 then c.env.chainFirst else c.env.chain
    return composeChain nodes (some (s.brRot, brScale c.env))

def curEnv : SimM Env := do
  let c ← ctx
  if c.cfg.barrelRoll.isNone then return c.env
  return { c.env with hoc := ← curHoc }

/-- Circle HitReceptor DrawInfo from the DHO's current placement. -/
def curCircleReceptor (i : Nat) : SimM DrawInfo := do
  let ins ← instOf (← ostate i).inst
  let h := (← topObj i).h
  return receptorFromPlacement (← curEnv).hoc (placementOf ins.tf) Vec2.zero h.scale

/-- Slider DrawInfo / head receptor from the DrawableSlider instance's current state. -/
def curSliderGeom (i : Nat) : SimM SliderGeom := do
  let os ← ostate i
  let ins ← instOf os.inst
  let hins ← instOf os.headInst
  let h := (← topObj i).h
  return sliderGeomP (← curEnv) h (placementOf ins.tf) ins.size ins.origin ins.relAnchor (placementOf hins.tf)

def curSpinnerGeom (i : Nat) : SimM SpinnerGeom := do
  let ins ← instOf (← ostate i).inst
  return spinnerGeomP (← curEnv) (placementOf ins.tf)

/-! ## Lifetimes from hit-state transforms -/

/-- `Transformable.LatestTransformEndTime` for a sequence start `S` and transforms whose end times are `ends`
(in tracker order): `max = S; foreach t: if (t.EndTime > max) max = t.EndTime + 1`. -/
def latestTransformEndTime (s : F64) (ends : List F64) : F64 :=
  ends.foldl (fun m e => if m < e then e + 1 else m) s

/-- `BeginAbsoluteSequence(T)` at clock time `ct`: `TransformStartTime = ct + (T - ct)`. -/
def seqStart (ct T : F64) : F64 := ct + (T - ct)

/-- DrawableHitCircle (and DrawableSliderHead) `UpdateHitStateTransforms` + `Expire()`
(`DrawableHitCircle.cs:177-205`): `Delay(800).FadeOut()`; Miss additionally `FadeOut(100)`, which removes the
later alpha transform. Initial transforms end before `S`. -/
def circleLifetimeEnd (ct T : F64) (state : Option Bool) : F64 :=
  let s := seqStart ct T
  match state with
  | some false => latestTransformEndTime s [s + 100]   -- Miss
  | _ => latestTransformEndTime s [(s + 800) + 0]      -- Hit / Idle

/-- DrawableSlider `UpdateHitStateTransforms`: `this.FadeOut(240).Expire()` (`DrawableSlider.cs:351-365`);
DrawableSpinner: `this.FadeOut(fade_out_duration = 240)…; Expire()` (`DrawableSpinner.cs:158-169`). -/
def sliderLifetimeEnd (ct T : F64) : F64 :=
  let s := seqStart ct T
  latestTransformEndTime s [s + 240]

/-- `JudgementResult.TimeAbsolute = Math.Min(RawTime, EndTime + MaximumJudgementOffset)`. -/
def timeAbsolute (h : HObj) (raw : F64) : F64 := F64.min raw (h.endTime + h.maxJudgementOffset)

/-! ## Score processor (combo / statistics) -/

/-- `HealthProcessor.TriggerFailure` (`HealthProcessor.cs:37-44`) → `Failed?.Invoke()` = the oracle's `onFail`
(`oracle/Gameplay.cs`): ReplayPlayer semantics refuse until `t >= lastFrameTime` (`ReplayPlayer.cs:55-68`), then
`Mods.OfType<IApplicableFailOverride>().All(m => m.PerformFail())` in mod order (short-circuit); EZ refills
`Health` to `MaxValue` and spends a life (`ModEasyWithExtraLives.cs:53-63`). -/
def triggerFailure (c : Config) (h : HealthSt) (t : F64) (replayPlayer : Bool) (lastFrameTime : Option F64) :
    Except String HealthSt := do
  if h.hasFailed then return h
  let mut h := { h with failTriggers := h.failTriggers + 1 }
  if replayPlayer then
    match lastFrameTime with
    | some lf => if !(lf ≤ t) then return h
    | none => return h
  for o in c.failOverrides do
    match o with
    | .veto => return h
    | .allow => pure ()
    | .easy k =>
      -- `retries` has one entry per EZ (`Config.easyRetries`, `initState`)
      if hk : k < h.retries.size then
        let r := h.retries[k]
        if r != 0 then
          return { h with health := 1, retries := h.retries.set k (r - 1) hk }
      else throw s!"internal: EZ lives index {k} out of range"
  return { h with hasFailed := true, failed := true, failTime := some t }

/-- `FailConditions` (`ModSuddenDeath.cs:26-28` + `OsuModSuddenDeath.cs:25-34`, `ModPerfect.cs:31-35`,
`OsuModTargetPractice.cs:106-112`). -/
def failCondition (j : JInfo) : FailCond → Bool
  | .suddenDeath tail => (j.ty.affectsCombo && !j.ty.isHit) || (tail && j.kind == .tail && !j.ty.isHit)
  | .perfect =>
    let rel (r : HitResult) := r.affectsAccuracy || r.affectsCombo
    (rel j.minResult || rel j.maxResult || rel j.ty) && j.ty != j.maxResult
  | .targetPractice => j.ty.affectsCombo && !j.ty.isHit

/-- `HealthProcessor.ApplyResultInternal` (`HealthProcessor.cs:46-58`): returns the new state and `FailedAtJudgement`. -/
def healthApply (h : HealthSt) (hc : HealthCfg) (c : Config) (j : JInfo) (t : F64) (replayPlayer : Bool)
    (lastFrameTime : Option F64) : Except String (HealthSt × Bool) := do
  if h.hasFailed then return (h, true)
  else
    let (h, inc) := h.increaseFor hc j false
    let h := { h with health := clamp01 (h.health + inc) }
    if defaultFailCondition h j || c.failConds.any (failCondition j) then
      return (← triggerFailure c h t replayPlayer lastFrameTime, false)
    else return (h, false)

/-- `ModAccuracyChallenge` handlers (`ModAccuracyChallenge.cs:69-89`): fired from `ScoreProcessor.updateScore`
(`ScoreProcessor.cs:391-402`) when the bound `Accuracy` (Standard, set first) / `MaximumAccuracy` changes and the new
value is below `MinimumAccuracy`. -/
def accChallenge (c : Config) (h : HealthSt) (old new : ScoreSt) (t : F64) (replayPlayer : Bool)
    (lastFrameTime : Option F64) : Except String HealthSt := do
  let mut h := h
  for std in [true, false] do
    let (o, n) := if std then (old.accuracy, new.accuracy) else (old.maximumAccuracy, new.maximumAccuracy)
    if Framework.Bindable.equalsD o n then continue
    for (mn, s) in c.accChallenges do
      if s == std && n < mn then h ← triggerFailure c h t replayPlayer lastFrameTime
  return h

/-- `DrawableRuleset.NewResult` → `HealthProcessor.ApplyResult; ScoreProcessor.ApplyResult` (`Player.cs:399-404`). -/
def emit (r : Ref) (ty : HitResult) (t : F64) : SimM Unit := do
  let h ← hobjOf r
  let c ← ctx
  let j : JInfo := { kind := h.kind, maxResult := h.maxResult, minResult := h.minResult, ty
                     timeAbsolute := F64.min t (h.endTime + h.maxJudgementOffset)
                     endTime := h.endTime, timeOffset := F64.min (t - h.endTime) h.maxJudgementOffset
                     newCombo := h.newCombo, lastInCombo := h.lastInCombo }
  let s ← st
  let one (hs : HealthSt) (ss : ScoreSt) (rp : Bool) : Except String (HealthSt × ScoreSt × Bool × Nat) := do
    let (hs, fl) ← healthApply hs c.hcfg c.cfg j t rp c.lastFrameTime
    let (ss', combo) := ss.apply c.smax j fl false
    let hs ← accChallenge c.cfg hs ss ss' t rp c.lastFrameTime
    return (hs, ss', fl, combo)
  let (hl, sl, fl, combo) ← liftExcept (one s.health s.score false)
  let (hr, sr, fr, comboR) ← liftExcept (one s.healthRP s.scoreRP true)
  set { s with health := hl, score := sl, healthRP := hr, scoreRP := sr
               out := s.out.push { top := r.1, nested := r.2, kind := h.kind, typeName := h.typeName, result := ty, time := t, combo
                                   health := hl.health, failed := fl, comboRP := comboR, healthRP := hr.health, failedRP := fr } }

/-! ## Alive objects (`HitObjectContainer.AliveObjects`) and input order -/

/-- Stable insertion sort (`stableSortBy` in Basic). -/
def startOf (i : Nat) : SimM F64 := do return (← topObj i).h.start

/-- `AliveEntries.Values.OrderBy(h => h.HitObject.StartTime)`: dictionary enumeration order, stably sorted. -/
def aliveObjects : SimM (Array Nat) := do
  let s ← st
  let keyed ← (s.dictSlots.filterMap id).mapM fun i => do return (i, ← startOf i)
  return (stableSortBy keyed fun a b => a.2 < b.2).map (·.1)

/-- Non-positional input queue order of the alive DHOs (reversed tree order): earlier start first,
ties: smaller ChildID first. -/
def inputOrder : SimM (Array Nat) := do
  let s ← st
  let keyed ← s.active.mapM fun i => do return (i, ← startOf i, (← ostate i).childId)
  let lt (a b : Nat × F64 × Nat) : Bool := a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)
  return (stableSortBy keyed lt).map (·.1)

/-- HitObjectContainer child (= update) order: reverse of `inputOrder`. -/
def updateOrder : SimM (Array Nat) := do return (← inputOrder).reverse

/-! ## Hit policies -/

inductive ClickAction where
  | ignore | shake | hit
deriving Inhabited, DecidableEq, BEq

/-- `StartTimeOrderedHitPolicy.enumerateHitObjectsUpTo(targetTime)` (`StartTimeOrderedHitPolicy.cs:93-108`). -/
def enumerateUpTo (target : F64) : SimM (Array Ref) := do
  let alive ← aliveObjects
  let c ← ctx
  let mut out : Array Ref := #[]
  for i in alive do
    let o := (← topObj i)
    if !(o.h.start < target) then return out
    out := out.push (i, -1)
    for h : j in [0:o.nested.size] do
      if !((o.nested[j]'h.upper).start < target) then break
      out := out.push (i, j)
  return out

def circleLike (r : Ref) : SimM Bool := do return (← hobjOf r).kind.isCircleLike

/-- `IHitPolicy.CheckHittable(hitObject, time, result)`. -/
def checkHittable (r : Ref) (time : F64) (result : HitResult) : SimM ClickAction := do
  let c ← ctx
  let h ← hobjOf r
  match c.cfg.policy with
  | .startTimeOrdered =>
    -- `StartTimeOrderedHitPolicy.CheckHittable` (`:26-52`)
    let mut blocking : Option Ref := none
    for o in ← enumerateUpTo h.start do
      if ← circleLike o then blocking := some o
    if let some b := blocking then
      let bh ← hobjOf b
      if !(← judged b) && time < bh.start then return .shake
    if result == .none then return .shake
    return .hit
  | .legacy hittableRange =>
    -- `LegacyHitPolicy.CheckHittable` (`LegacyHitPolicy.cs:36-70`); `IndexOf` only finds top-level DHOs.
    let alive ← aliveObjects
    if r.2 < 0 then
      match alive.idxOf? r.1 with
      | some idx =>
        if idx > 0 then
          let p ← getA alive (idx - 1) "alive objects"
          let ph := (← topObj p).h
          if ph.stackHeight > 0 && !(← allJudged p) then return .ignore
      | none => pure ()
    if result == .none then return .shake
    for p in alive do
      if ← allJudged p then continue
      if r.2 < 0 && p == r.1 then break
      if (← topObj p).h.endTime + 3 < h.start then return .shake
    return if F64.abs (h.start - time) < hittableRange then .hit else .shake

/-! ## Adaptive Speed (`ModAdaptiveSpeed.cs:162-256`) -/

/-- `OnNewResult` handler of every AS mod. -/
def adaptiveSpeedOnResult (r : Ref) (ty : HitResult) (t : F64) : SimM Unit := do
  let c ← ctx
  if c.cfg.dynRates.isEmpty then return
  let h ← hobjOf r
  let mut ai := 0
  for d in c.cfg.dynRates, k in [0:c.cfg.dynRates.size] do
    match d with
    | .adaptive _ =>
      let s ← st
      let seen ← getA s.asSeen ai "asSeen"
      -- `ratesForRewinding.ContainsKey`, `shouldProcessResult` (`precedingEndTimes.ContainsKey`)
      let (top, ns) ← getA c.precEnd r.1 "precedingEndTimes"
      let prev? ← if r.2 < 0 then pure top else getA ns r.2.toNat "precedingEndTimes (nested)"
      if !(seen.contains r) && ty.affectsAccuracy then
        if let some prev := prev? then
          let rel : F64 ← if !ty.isHit then pure 0.95
            else liftNet (F64.clamp ((h.endTime - prev) / (timeAbsolute h t - prev)) 0.9 1.11)
          let speed ← getA s.speed k "speed"
          let recent0 ← getA s.asRecent ai "asRecent"
          let recent := (recent0.extract 1 8).push (← liftNet (F64.clamp (rel * speed) 0.4 2.5))
          let mut consistency : Int := 0
          let mut prevR : Option F64 := none
          for x in recent do
            if let some p := prevR then
              consistency := consistency + (← liftNet (F64.sign (x - p))).toInt
            prevR := some x
          let avg ← liftNet (SysMisc.averageF64 recent.toList)
          let target := Framework.Interpolation.lerp (← getA s.asTarget ai "asTarget") avg
            (F64.ofInt consistency.natAbs / (F64.ofInt 8 - 1))
          set { s with asSeen := ← setA s.asSeen ai (r :: seen) "asSeen", asRecent := ← setA s.asRecent ai recent "asRecent"
                       asTarget := ← setA s.asTarget ai target "asTarget" }
      ai := ai + 1
    | _ => pure ()

/-- `IUpdatableByPlayfield.Update` of the k-th time-varying rate mod: TimeRamp `SpeedChange = ApplyToRate(Clock.CurrentTime)`
(`ModTimeRamp.cs:100-108`); AS `SpeedChange = DampContinuously(SpeedChange, targetRate, 50, Clock.ElapsedFrameTime)`
(`ModAdaptiveSpeed.cs:155-158`). -/
def dynRateUpdate (k : Nat) : SimM Unit := do
  let c ← ctx
  let s ← st
  let elapsed ← elapsedNow
  let d ← getA c.cfg.dynRates k "dynRates"
  -- index of this AS among the adaptive mods
  let ai := ((c.cfg.dynRates.extract 0 k).filter fun d => match d with | .adaptive _ => true | _ => false).size
  let old ← getA s.speed k "speed"
  let v ← match d with
    | .timeRamp i f b ft => liftNet (timeRampRate i f b ft s.t)
    | .adaptive _ => do
      pure (Framework.Interpolation.dampContinuously old (← getA s.asTarget ai "asTarget") 50 elapsed)
  set { s with speed := ← setA s.speed k (← liftNet (d.setSpeed old v)) "speed" }

/-! ## DHO state updates (`DrawableHitObject.UpdateState`, `DrawableHitObject.cs:467-499`) -/

/-- Run `f` inside `BeginAbsoluteSequence(t)` on a part's transformable (delay restored afterwards). -/
def withAbs (k : Nat) (now t : F64) (f : TObj → TObj) : SimM Unit :=
  modifyInst k fun ins =>
    let saved := ins.tf.delay
    { ins with tf := { f (absSeq ins.tf now t) with delay := saved } }

/-- `ApplyCustomUpdateState` handlers. `forwarded`: the pass through the parent's handler list (a nested head's event
re-raised by `DrawableHitObject.onApplyCustomUpdateState`, `DrawableHitObject.cs:281,412`); the parent (slider) list
holds only the `ModWithVisibilityAdjustment` handlers (Classic subscribes on circles and heads only,
`OsuModClassic.cs:69-90`). Handler order = mod order (`Playfield.cs:405-417`). -/
def customState (i : Nat) (p : Part) (state : Armed) (forwarded : Bool) : SimM Unit := do
  let c ← ctx
  let o ← topObj i
  let r ← partRef i p
  let h ← hobjOf r
  let k ← partInst i p
  let kind := h.kind
  let now := (← st).t
  let s0 := h.start - h.preempt
  let isCircleDho := kind == .circle || kind == .head
  for hv : vi in [0:c.cfg.visMods.size] do
    let vm := c.cfg.visMods[vi]'hv.upper
    -- `IncreaseFirstObjectVisibility && o.HitObject ∈ FirstObject subtree` (`ModWithVisibilityAdjustment.cs:76-109`)
    let increased := (← getA c.firstObj vi "firstObj") == some i
    match vm with
    | .classicEarlyFade =>
      if forwarded || !isCircleDho || state == .hit then continue
      -- `BeginAbsoluteSequence(StateUpdateTime): Delay(ok).FadeOut(meh - ok)` (`OsuModClassic.cs:101-115`)
      let some hw := h.hitWindows | continue
      withAbs k now h.start fun tf => ((delaySeq tf now hw.ok).append tf now .alpha (vs 0) (hw.meh - hw.ok)).1
    | .scaleTween sc =>
      if increased || !(kind == .circle || kind == .slider) then continue
      withAbs k now s0 fun tf =>
        let (tf, sq) := transformTo tf now .scale ⟨sc, sc⟩ 0
        (sq.then_.append tf now .scale ⟨1, 1⟩ h.preempt .outSine).1
    | .spinIn =>
      if increased then continue
      if isCircleDho then
        withAbs k now s0 fun tf =>
          let (tf, sq) := transformTo tf now .rotation (vs 360) 0
          let tf := (sq.then_.append tf now .rotation (vs 0) h.preempt .inOutSine).1
          let (tf, sq) := transformTo tf now .scale ⟨2, 0⟩ 0
          let tf := (sq.then_.append tf now .scale ⟨1, 1⟩ h.preempt .inOutSine).1
          if state == .idle then (transformTo tf now .alpha (vs 1) 0).1 else tf
      else if kind == .slider then
        withAbs k now s0 fun tf =>
          let (tf, sq) := transformTo tf now .scale ⟨0, 0⟩ 0
          let tf := (sq.then_.append tf now .scale ⟨1, 1⟩ h.preempt .inOutSine).1
          if state == .idle then (transformTo tf now .alpha (vs 1) 0).1 else tf
    | .targetPractice =>
      if increased || !isCircleDho then continue
      withAbs k now s0 fun tf =>
        let tf := (transformTo tf now .scale ⟨0.5, 0.5⟩ 0).1
        (transformTo tf now .scale ⟨1, 1⟩ h.preempt).1
    | .hidden onlyApproach =>
      if onlyApproach then continue
      -- `getFadeOutParameters` (`OsuModHidden.cs:162-195`)
      let fadeStart := h.start - h.preempt + h.fadeIn
      let fadeDur := h.preempt * 0.3
      let longDur := h.endTime - fadeStart
      if isCircleDho then
        if !increased then withAbs k now fadeStart fun tf => (transformTo tf now .alpha (vs 0) fadeDur).1
      else if kind == .slider then
        modifyInst k fun ins =>
          let b := absSeq ins.bodyTf now fadeStart
          { ins with bodyTf := { (transformTo b now .alpha (vs 0) longDur .out).1 with delay := ins.bodyTf.delay } }
      else if kind == .spinner then
        withAbs k now (fadeStart + longDur) fun tf => (transformTo tf now .alpha (vs 0) fadeDur).1
    | .transform =>
      if !(kind == .circle || kind == .slider || kind == .spinner) then continue
      -- `OsuModTransform.applyTransform` (`OsuModTransform.cs:35-62`)
      let appearDistance : F32 := F64.toF32 (h.preempt - h.fadeIn) / 2
      let th := (← st).theta
      let orig := (← instOf k).tf.pos
      let off : Vec2 := Vec2.scale ⟨F32.cos th, F32.sin th⟩ appearDistance
      let appearTime := h.start - h.preempt - 1
      let moveDuration := h.preempt + 1
      withAbs k now appearTime fun tf =>
        let (tf, sq) := transformTo tf now .position Vec2.zero 0 .none (some off)
        (sq.append tf now .position orig moveDuration .inOutSine).1
      modify fun s => { s with theta := s.theta + F64.toF32 h.fadeIn / 1000 }
      if c.cfg.traceObj.isSome then modify fun s => { s with dbg := s.dbg.push s!"theta t={s.t} obj {i} {kind.typeName} {state == Armed.idle}" }
    | .wiggle strength =>
      -- `OsuModWiggle` (`OsuModWiggle.cs:42-81`): not for repeats/tails (not modelled DHOs here)
      let origin := (← instOf k).tf.pos
      let mut rng := NetRandom.create (F64.toInt32 h.start)
      let mut segs : Array (F64 × Vec2) := #[]
      let wig (rng : NetRandom.State) : Vec2 × NetRandom.State :=
        let (a, rng) := NetRandom.sample rng
        let (b, rng) := NetRandom.sample rng
        let ang : F32 := F64.toF32 (a * 2 * Framework.EasingConst.pi)
        let dist : F32 := F64.toF32 (b * strength * 7)
        (⟨F64.toF32 (F32.toF64 dist * F64.cos (F32.toF64 ang) + F32.toF64 origin.x),
          F64.toF32 (F32.toF64 dist * F64.sin (F32.toF64 ang) + F32.toF64 origin.y)⟩, rng)
      let n1 : Int := (F64.toInt32 h.preempt).toInt / 100
      for q in [0:n1.toNat] do
        let (v, rng') := wig rng
        rng := rng'
        segs := segs.push (h.start - h.preempt + F64.ofInt (q * 100), v)
      let dur? : Option F64 := if p == .top then
          (match o.h.kind with
           | .slider => o.slider.map (·.duration)
           | .spinner => o.spinner.map (·.duration)
           | _ => none)
        else none
      if let some d := dur? then
        let n2 := (F64.toInt32 (d / 100)).toInt
        for q in [0:n2.toNat] do
          let (v, rng') := wig rng
          rng := rng'
          segs := segs.push (h.start + F64.ofInt (q * 100), v)
      for (t0, v) in segs do
        withAbs k now t0 fun tf => (transformTo tf now .position v 100).1
    | .inert => pure ()

/-- `UpdateState(newState, force)` of a DHO part at the current clock time: `clearExistingStateTransforms` (also the
children, here the slider body), `UpdateInitialTransforms` at `Start - TimePreempt`, `UpdateStartTimeStateTransforms`
at `StartTime` (nothing on the modelled members), `UpdateHitStateTransforms` at `Result.TimeAbsolute ?? EndTime`
(`DrawableHitCircle.cs:209-235`, `DrawableSlider.cs:351-366`, `DrawableSpinner.cs:188-200`), `Expire()` → lifetime end,
then the `ApplyCustomUpdateState` handlers (`passes` = 2 for a nested DHO whose parent forwarder is attached). -/
def updateState (i : Nat) (p : Part) (newState : Armed) (force : Bool) (passes : Nat) : SimM Unit := do
  if (← partArmed i p) == newState && !force then return
  let now := (← st).t
  let k ← partInst i p
  let o ← topObj i
  let r ← partRef i p
  let h ← hobjOf r
  let hst := match ← resOf r with | some (_, raw) => timeAbsolute h raw | none => h.endTime
  let ins ← instOf k
  let isSlider := p == .top && o.h.kind == .slider
  let mut tf := clearState ins.tf
  let mut body := if isSlider then clearState ins.bodyTf else ins.bodyTf
  -- BeginAbsoluteSequence(Start - TimePreempt) (recursive): UpdateInitialTransforms
  let t0 := h.start - h.preempt
  tf := fadeInFromZero (absSeq tf now t0) now
  if isSlider then body := fadeInFromZero (absSeq body now t0) now h.fadeIn
  tf := { tf with delay := 0 }
  body := { body with delay := 0 }
  -- BeginAbsoluteSequence(HitStateUpdateTime): UpdateHitStateTransforms
  tf := absSeq tf now hst
  body := absSeq body now hst
  let mut lifeEnd : F64 := 0
  match h.kind with
  | .circle | .head =>
    -- `this.Delay(800).FadeOut()`; Miss: `this.FadeOut(100)`; (Hit with hit animations off: not the default)
    tf := ((delaySeq tf now 800).append tf now .alpha (vs 0) 0).1
    if newState == .miss then tf := (transformTo tf now .alpha (vs 0) 100).1
    lifeEnd := latestEnd tf now
    let closed := circleLifetimeEnd now hst (if newState == .idle then none else some (newState == .hit))
    -- debug cross-check of the transform engine, trace-only (D48: dbg is never written without --trace-obj)
    if !(closed == lifeEnd) && (← ctx).cfg.traceObj.isSome then
      modify fun s => { s with dbg := s.dbg.push s!"life {i} {p == Part.top} now={now.toBits} hst={hst.toBits} engine={lifeEnd.toBits} closed={closed.toBits}" }
  | .slider =>
    -- Hit: `if (HeadCircle.IsHit && SnakingOut) Body.FadeOut(40)`; `this.FadeOut(240).Expire()`
    if newState == .hit && (← isHitRef (i, (← headIdxOf i))) then
      body := (transformTo body now .alpha (vs 0) 40).1
    let (tf', sq) := transformTo tf now .alpha (vs 0) 240
    tf := tf'
    lifeEnd := latestEnd (absSeq tf now sq.currentTime) now
  | _ =>
    tf := (transformTo tf now .alpha (vs 0) 240).1
    lifeEnd := latestEnd tf now
  tf := { tf with delay := 0 }
  body := { body with delay := 0 }
  modifyInst k fun ins => { ins with tf, bodyTf := body }
  if p == .top then modifyObj i fun os => { os with armed := newState, lifetimeEnd := lifeEnd }
  else modifyObj i fun os => { os with headArmed := newState, headLifetimeEnd := lifeEnd }
  customState i p newState false
  if passes ≥ 2 then customState i p newState true

/-- `UpdateState` of a spinner tick DHO: only its `ApplyCustomUpdateState` dispatch is observable — Transform's shared
`theta` advances by the tick's `TimeFadeIn / 1000` per pass (`OsuModTransform.cs:57`; spinner ticks are not excluded). -/
def tickState (i j : Nat) (passes : Nat) (newState : Armed) (force : Bool) : SimM Unit := do
  let c ← ctx
  let n ← nestedOf (← topObj i) j
  let tk ← getA (← ostate i).tickInsts j "tickInsts"
  -- `if (State.Value == newState && !force) return;`
  if (← instOf tk).armed == newState && !force then return
  modifyInst tk fun ins => { ins with armed := newState }
  for _ in [0:passes] do
    for vm in c.cfg.visMods do
      match vm with
      | .transform =>
        modify fun s => { s with theta := s.theta + F64.toF32 n.fadeIn / 1000 }
        if c.cfg.traceObj.isSome then modify fun s => { s with dbg := s.dbg.push s!"theta t={s.t} tick {i} {j}" }
      | _ => pure ()

/-- `updateStateFromResult()` (`DrawableHitObject.cs:322-330`). -/
def updateStateFromResult (i : Nat) (p : Part) (passes : Nat) : SimM Unit := do
  let r ← partRef i p
  let st' : Armed := match ← resOf r with
    | some (ty, _) => if ty.isHit then .hit else .miss
    | none => .idle
  updateState i p st' true passes

/-! ## Judgement application -/

mutual
  /-- `DrawableHitObject.ApplyResult` + the `NewResult` chain. `fuel` bounds the HandleHit recursion. -/
  def applyResult (fuel : Nat) (r : Ref) (ty : HitResult) : SimM Unit := do
    let t := (← st).t
    let h ← hobjOf r
    -- result + RawTime
    if r.2 < 0 then modifyObj r.1 fun o => { o with result := some (ty, t) }
    else
      let os ← ostate r.1
      let ns ← setA os.nested r.2.toNat (some (ty, t)) "nested results"
      modifyObj r.1 fun o => { o with nested := ns }
    -- UpdateState(Hit/Miss): hit-state transforms → lifetime (nested heads: two handler passes)
    let ns : Armed := if ty.isHit then .hit else .miss
    match h.kind with
    | .circle | .slider | .spinner => updateState r.1 .top ns false 1
    | .head => updateState r.1 .head ns false 2
    | .spinnerTick | .spinnerBonusTick => tickState r.1 r.2.toNat 2 ns false
    | _ => pure ()
    -- OnNewResult: mod handlers first (subscribed when the pooled DHO is created, `Playfield.cs:399-417`, before the
    -- HitObjectContainer's `addDrawable` subscription), then → OsuPlayfield.onNewResult → HitPolicy.HandleHit
    adaptiveSpeedOnResult r ty t
    match fuel with
    | 0 => throw "internal: HandleHit recursion deeper than the object count"
    | fuel + 1 => handleHit fuel r
    -- → DrawableRuleset.NewResult → HealthProcessor, ScoreProcessor
    emit r ty t

  /-- `IHitPolicy.HandleHit`. StartTimeOrdered: miss every unjudged earlier circle/head (`:54-72`). Legacy: nothing. -/
  def handleHit (fuel : Nat) (r : Ref) : SimM Unit := do
    match (← ctx).cfg.policy with
    | .legacy _ => pure ()
    | .startTimeOrdered =>
      if !(← circleLike r) then return
      let h ← hobjOf r
      for o in ← enumerateUpTo h.start do
        if ← judged o then continue
        if ← circleLike o then
          let oh ← hobjOf o
          applyResult fuel o oh.minResult
end

def maxFuel : SimM Nat := do return (← ctx).pb.objects.size + 4

def hitForcefully (r : Ref) : SimM Unit := do applyResult (← maxFuel) r (← hobjOf r).maxResult
def missForcefully (r : Ref) : SimM Unit := do applyResult (← maxFuel) r (← hobjOf r).minResult

/-! ## Sliders (`SliderInputManager`) -/

def sliderData (i : Nat) : SimM SliderData := do need (← topObj i).slider "slider data"
def headOf (i : Nat) : SimM Nat := headIdxOf i
def tailOf (i : Nat) : SimM Nat := do getA (← ctx).tailIdx i "tailIdx"

def mouseInFollowArea (i : Nat) (expanded : Bool) : SimM Bool := do
  let o ← topObj i
  let sd ← sliderData i
  let g ← curSliderGeom i
  liftExcept (isMouseInFollowArea o.h sd g (← ostate i).sliderMouse (← st).t expanded)

def isValidTrackingAction (os : OState) (t : F64) (a : Action) : Bool :=
  match os.hitAction with
  | some ha =>
    if os.acceptAnyAfter.isNone || (match os.acceptAnyAfter with | some x => t ≤ x | none => true) then a == ha
    else a == .left || a == .right
  | none => a == .left || a == .right

/-- `SliderInputManager.updateTracking(isValidTrackingPosition)` (`SliderInputManager.cs:216-274`). -/
def updateTracking (i : Nat) (validPos : Bool) : SimM Unit := do
  let t := (← st).t
  let pressed := (← st).pressed
  let aj ← allJudged i
  let endT := (← topObj i).h.endTime
  modifyObj i fun os => Id.run do
    let mut os := os
    if os.hitAction.isNone then os := { os with acceptAnyAfter := none }
    if let some ha := os.hitAction then
      if os.acceptAnyAfter.isNone then
        let other := if ha == .right then Action.left else Action.right
        if !(os.lastPressed.contains other) then os := { os with acceptAnyAfter := some t }
    let valid := pressed.any (isValidTrackingAction os t)
    { os with lastPressed := pressed.toList
              tracking := (!aj || t ≤ endT) && validPos && valid }

/-- `SliderInputManager.PostProcessHeadJudgement` (`:78-140`). -/
def postProcessHeadJudgement (i : Nat) : SimM Unit := do
  let headRef : Ref := (i, (← headOf i))
  if !(← judged headRef) || !(← isHitRef headRef) then return
  if !(← mouseInFollowArea i true) then return
  let o ← topObj i
  let sd ← sliderData i
  let g ← curSliderGeom i
  let t := (← st).t
  let some mouse := (← ostate i).sliderMouse | return
  let m := mouseInSlider g mouse
  let mut allIn := true
  for j in [0:o.nested.size] do
    if ← judged (i, j) then continue
    let n := (← nestedOf o j)
    if t < n.start then break
    let radius := followRadius o.h true
    let p0 := (n.start - o.h.start) / sd.duration
    let progress := clampK p0 0 1   -- `Math.Clamp(…, 0, 1)`, literal bounds
    let pos ← liftExcept (sd.curvePositionAt progress)
    if radius * radius < (pos - m).lengthSquared then
      allIn := false
      break
  for j in [0:o.nested.size] do
    if ← judged (i, j) then continue
    let n := (← nestedOf o j)
    if t < n.start then break
    if allIn then hitForcefully (i, j) else missForcefully (i, j)
  let inBall ← mouseInFollowArea i false
  updateTracking i (allIn || inBall)

/-- `SliderInputManager.TryJudgeNestedObject(nested, timeOffset)` (`:142-178`). -/
def tryJudgeNested (i j : Nat) : SimM Unit := do
  let o ← topObj i
  let n := (← nestedOf o j)
  let t := (← st).t
  let offset := t - n.endTime
  match n.kind with
  | .tick | .«repeat» =>
    if offset < 0 then return
  | .tail =>
    -- SliderEventGenerator.TAIL_LENIENCY = -36
    if offset < -36 then return
    let mut lastTick : Option Nat := none
    for k in [0:o.nested.size] do
      if (← nestedOf o k).kind == .tick || (← nestedOf o k).kind == .«repeat» then lastTick := some k
    if let some k := lastTick then
      if !(← judged (i, k)) then return
  | _ => return
  if !(← judged (i, (← headOf i))) then return
  if (← ostate i).tracking then hitForcefully (i, j)
  else if 0 ≤ offset then missForcefully (i, j)

/-! ## Circles and slider heads -/

/-- `DrawableHitCircle.CheckForResult` (`DrawableHitCircle.cs:137-173`), `DrawableSliderHead.ResultFor/CheckForResult`
(`DrawableSliderHead.cs:52-74`). -/
def circleCheckForResult (r : Ref) (userTriggered : Bool) : SimM Unit := do
  let h ← hobjOf r
  let t := (← st).t
  let offset := t - h.endTime
  let some hw := h.hitWindows | return
  if !userTriggered then
    if !hw.canBeHit offset then missForcefully r
  else
    let base := hw.resultFor offset
    -- (no `&&` with a nested `(← …)`: it would be hoisted and run for circles too)
    let classicHead ← if h.kind == .head then do pure (← sliderData r.1).classic else pure false
    let result := if classicHead then (if base.isHit then HitResult.largeTickHit else .largeTickMiss) else base
    let action ← checkHittable r t result
    if result == .none || action != .hit then pure ()
    else applyResult (← maxFuel) r result
  if h.kind == .head then postProcessHeadJudgement r.1

/-- `DrawableHitObject.UpdateResult(userTriggered)` for circle-like objects. -/
def circleUpdateResult (r : Ref) (userTriggered : Bool) : SimM Unit := do
  if ← judged r then return
  circleCheckForResult r userTriggered

/-- `DrawableSlider.CheckForResult` (`DrawableSlider.cs:293-326`). -/
def sliderCheckForResult (i : Nat) : SimM Unit := do
  let o ← topObj i
  let t := (← st).t
  let tailJ ← judged (i, (← tailOf i))
  if !tailJ || t < o.h.endTime then return
  let sd ← sliderData i
  let os ← ostate i
  let total := o.nested.size
  let hits := os.nested.foldl (fun n r => match r with | some (ty, _) => if ty.isHit then n + 1 else n | none => n) 0
  let ty : HitResult :=
    if sd.classic then
      if hits == total then .great
      else if hits == 0 then .miss
      else
        let frac := F64.ofInt hits / F64.ofInt total
        if 0.5 ≤ frac then .ok else .meh
    else if hits > 0 then o.h.maxResult else o.h.minResult
  applyResult (← maxFuel) (i, -1) ty

/-! ## Per-step DHO updates -/

/-- The slider subtree update (`DrawableSlider` children order, `DrawableSlider.cs:96-128`):
SliderInputManager.Update → ticks → repeats → tail → head → slider `UpdateAfterChildren`. -/
def updateSlider (i : Nat) : SimM Unit := do
  let o ← topObj i
  let t := (← st).t
  let sd ← sliderData i
  let k := (← ostate i).inst
  -- DrawableSlider.Update: `Tracking.Value = SliderInputManager.Tracking` (`DrawableSlider.cs:237-242`; the bindable
  -- lives on the pooled instance), with OsuModStrictTracking's ValueChanged handler (`OsuModStrictTracking.cs:34-54`):
  -- on true → false, unless the slider is judged or `Time.Current < StartTime`, miss the strict tracking tail.
  let os ← ostate i
  let ins ← instOf k
  if os.tracking != ins.drawableTracking then
    modifyInst k fun ins => { ins with drawableTracking := os.tracking }
    if (← ctx).cfg.strictTracking && !os.tracking && os.result.isNone && !(t < o.h.start) then
      for j in [0:o.nested.size] do
        if (← nestedOf o j).typeName == "StrictTrackingSliderTailCircle" then
          if !(← judged (i, j)) then missForcefully (i, j)
          break
  -- (a judged slider keeps updating its subtree while present: with StrictTracking the slider can be judged before
  -- its head, which must still auto-miss)
  -- children in order (`DrawableSlider.cs:100-128`): SliderInputManager, shake[Body, tail proxy, ticks, repeats, tail],
  -- headContainer, …
  let tr := (← ostate i).tracking
  let inArea ← mouseInFollowArea i tr
  updateTracking i inArea
  -- Body (SkinnableDrawable → PlaySliderBody): first update → LoadComplete (ArgonSliderBody binds
  -- `PathRadius = path_radius * scale`, runOnce → Refresh if changed); transforms; the scheduled
  -- `Refresh` (pathVersion change on apply, `PlaySliderBody.cs:47`) runs only while the body is present.
  let env := (← ctx).env
  let ins ← instOf k
  let mut ins := ins
  if !ins.bodyLoaded then
    let r := env.argonPathRadius * o.h.scale
    ins := { ins with bodyLoaded := true }
    if !(ins.bodyRadius == r) then
      let (sz, off) ← liftExcept (bodyRefresh sd r)
      ins := { ins with bodyRadius := r, bodySize := sz, bodyOffset := off }
  ins := { ins with bodyTf := updateTransforms ins.bodyTf t }
  if ins.refreshPending && Float32.ofBits 0x38D1B717 < ins.bodyTf.alpha && !(ins.bodyTf.scale.x == 0) && !(ins.bodyTf.scale.y == 0) then
    let (sz, off) ← liftExcept (bodyRefresh sd ins.bodyRadius)
    ins := { ins with refreshPending := false, bodySize := sz, bodyOffset := off }
  modifyInst k fun _ => ins
  -- tickContainer, repeatContainer, tailContainer (each DHO: UpdateAfterChildren → UpdateResult(false))
  for kind in [Kind.tick, Kind.«repeat», Kind.tail] do
    for j in [0:o.nested.size] do
      if (← nestedOf o j).kind == kind && !(← judged (i, j)) then tryJudgeNested i j
  -- headContainer: lifetime of the head DHO (`UpdateChildrenLife`), then its UpdateSubTree
  let hj ← headOf i
  let head := (← nestedOf o hj)
  let os ← ostate i
  let headAlive := !(t < head.start - head.preempt) && t < os.headLifetimeEnd
  modifyObj i fun os => { os with headAlive }
  if headAlive then
    let hk := os.headInst
    if !(← instOf hk).loaded then
      modifyInst hk fun ins => { ins with loaded := true }
      updateStateFromResult i .head 2
    modifyInst hk fun ins => { ins with tf := updateTransforms ins.tf t }
    if ← partPresent i .head then circleUpdateResult (i, hj) false
  -- DrawableSlider.UpdateAfterChildren (`:257-285`): Size/OriginPosition from the body, nested RelativeAnchorPosition,
  -- then UpdateResult(false)
  -- `Ball.UpdateProgress(Math.Clamp((Time.Current - StartTime) / Duration, 0, 1))` → `Position = CurvePositionAt(p)`
  let p0 := (t - o.h.start) / sd.duration
  let prog ← liftNet (F64.clamp p0 0 1)
  let ball ← liftExcept (sd.curvePositionAt prog)
  modifyInst k fun ins => { ins with size := ins.bodySize, origin := ins.bodyOffset
                                     relAnchor := Vec2.cdiv ins.bodyOffset ins.bodySize, ballPos := ball }
  if (← ostate i).result.isNone then sliderCheckForResult i

/-! ## Spinners -/

/-- `SpinnerSpinHistory.TotalRotation => 360 * completedSpins.Count + currentSpinMaxRotation`. -/
def totalRotation (os : OState) : F32 := F32.ofInt (360 * (os.completedSpins : Int)) + os.currentSpinMax

/-- `DrawableSpinner.Progress` (`DrawableSpinner.cs:203-218`). -/
def spinnerProgress (sp : SpinnerData) (os : OState) : F32 :=
  if sp.spinsRequired == 0 then 1
  else
    let p : F32 := totalRotation os / 360 / F32.ofInt sp.spinsRequired
    -- `Math.Clamp(p, 0, 1)`: literal bounds, the throwing branch is dead
    if p < 0 then 0 else if 1 < p then 1 else p

/-- `SpinnerSpinHistory.ReportDelta(currentTime, delta)` (forward branch; time never decreases here). -/
def reportDelta (os : OState) (t : F64) (delta : F32) : Except String OState := do
  if delta == 0 then return os
  let mut os := { os with totalAccumulated := os.totalAccumulated + delta }
  if os.lastReportTime ≤ t then
    let cur := os.totalAccumulated - os.accumulatedAtLastCompletion
    os := { os with currentSpinMax := F32.max os.currentSpinMax (F32.abs cur) }
    let mut fuel := 1000000
    while (360 : F32) ≤ os.currentSpinMax && fuel > 0 do
      fuel := fuel - 1
      let cur := os.totalAccumulated - os.accumulatedAtLastCompletion
      -- `Math.Sign(float)` throws on NaN
      let dir : Int ← match F32.sign cur with
        | .ok v => pure v.toInt
        | .error e => throw s!"lazer would throw: Math.Sign {repr e} (SpinnerSpinHistory)"
      os := { os with completedSpins := os.completedSpins + 1
                      accumulatedAtLastCompletion := os.accumulatedAtLastCompletion + F32.ofInt (dir * 360) }
      os := { os with currentSpinMax := F32.abs (os.totalAccumulated - os.accumulatedAtLastCompletion) }
    if fuel == 0 && (360 : F32) ≤ os.currentSpinMax then throw "internal: ReportDelta fuel exhausted"
  else
    -- rewind branch (unreachable with a non-decreasing schedule)
    os := { os with currentSpinMax := F32.abs (os.totalAccumulated - os.accumulatedAtLastCompletion) }
  return { os with lastReportTime := t }

/-- `DrawableSpinner.updateBonusScore` (`DrawableSpinner.cs:335-366`). -/
def updateBonusScore (i : Nat) : SimM Unit := do
  let o ← topObj i
  if o.nested.size == 0 then return
  let os ← ostate i
  let spins : Int := (F32.toInt32 (totalRotation os / 360)).toInt
  if spins < os.completedFullSpins then
    modifyObj i fun os => { os with completedFullSpins := spins }
    return
  let mut fuel := 10000000
  while fuel > 0 do
    fuel := fuel - 1
    if (← ostate i).completedFullSpins == spins then break
    let mut tick : Option Nat := none
    for j in [0:o.nested.size] do
      if !(← judged (i, j)) then
        tick := some j
        break
    if let some j := tick then hitForcefully (i, j)
    modifyObj i fun os => { os with completedFullSpins := os.completedFullSpins + 1 }
  if fuel == 0 && !((← ostate i).completedFullSpins == spins) then throw "internal: updateBonusScore fuel exhausted"

/-- The spinner subtree update: `DrawableSpinner.Update` (Tracking) → `SpinnerRotationTracker.Update`
→ `DrawableSpinner.UpdateAfterChildren` (UpdateResult(false), then `updateBonusScore`). -/
def updateSpinner (i : Nat) : SimM Unit := do
  if (← ostate i).result.isSome then return
  let o ← topObj i
  let some sp := o.spinner | return
  let t := (← st).t
  let pressed := (← st).pressed
  let spinnable := o.h.start ≤ t && t < o.h.endTime
  let c ← ctx
  -- DrawableSpinner.Update (`if (HandleUserInput)`; SpunOut sets `HandleUserInput = false`)
  if !c.cfg.spunOut then
    let tracking := spinnable && (← ostate i).result.isNone && (pressed.contains .left || pressed.contains .right)
    modifyObj i fun os => { os with spinTracking := tracking }
  else
    -- OsuModSpunOut.onSpinnerUpdate (`OnUpdate`, right after `Update`; `OsuModSpunOut.cs:35-54`)
    modifyObj i fun os => { os with spinTracking := spinnable }
    let s ← st
    if !almostEqualsD s.clockRate 0 then
      let elapsed ← elapsedNow
      let e := elapsed / s.clockRate
      let speed : F32 := F64.toF32 (1.01 * F64.ofInt sp.spinsRequired / sp.duration)
      let deg := radiansToDegrees (F64.toF32 e * speed * Float32.ofBits 0x40490FDB * 2)
      -- SpinnerRotationTracker.AddRotation (`:93-111`): no-op outside spinnable time
      if spinnable then
        let d : F32 := F64.toF32 (F32.toF64 deg * F64.abs (← liftExcept (c.cfg.trueRate s.speed)))
        let os' ← liftExcept (reportDelta (← ostate i) t d)
        modifyObj i fun _ => os'
  -- DrawableSpinner.Update: the next unjudged tick gets `LifetimeStart = StartTime`; the ticks container (before the
  -- rotation tracker) then updates its alive ticks: a fresh instance's first update is `LoadComplete` (two passes)
  let mut nextTick : Option Nat := none
  for j in [0:o.nested.size] do
    if !(← judged (i, j)) then
      nextTick := some j
      break
  if let some j := nextTick then
    let tl ← setA (← ostate i).tickLive j true "tickLive"
    modifyObj i fun os => { os with tickLive := tl }
  for j in [0:o.nested.size] do
    let os ← ostate i
    if (← getA os.tickLive j "tickLive") && o.h.start ≤ t && !(← judged (i, j)) then
      let tk ← getA os.tickInsts j "tickInsts"
      if !(← instOf tk).loaded then
        modifyInst tk fun ins => { ins with loaded := true }
        tickState i j 2 .idle true
  -- SpinnerRotationTracker.Update
  let g ← curSpinnerGeom i
  let os ← ostate i
  if let some pos := os.spinMouse then
    let thisAngle : F32 := -(radiansToDegrees (F32.atan2 (pos.x - g.trackerSize.x / 2) (pos.y - g.trackerSize.y / 2)))
    let mut delta : F32 := match os.lastAngle with | none => 0 | some la => thisAngle - la
    if 180 < delta then delta := delta - 360
    if delta < -180 then delta := delta + 360
    let mut os := os
    if os.spinTracking && spinnable then
      -- AddRotation: delta = (float)(delta * Math.Abs(GetTrueGameplayRate()))  (`SpinnerRotationTracker.cs:106-107`)
      let rate : F64 ← liftExcept ((← ctx).cfg.trueRate (← st).speed)
      let d : F32 := F64.toF32 (F32.toF64 delta * F64.abs rate)
      os ← liftExcept (reportDelta os t d)
    os := { os with lastAngle := some thisAngle }
    modifyObj i fun _ => os
  -- UpdateAfterChildren → UpdateResult(false) → CheckForResult (`DrawableSpinner.cs:220-249`)
  if (← ostate i).result.isNone && o.h.start ≤ t && !(t < o.h.endTime) then
    for j in [0:o.nested.size] do
      if !(← judged (i, j)) then missForcefully (i, j)
    let p := spinnerProgress sp (← ostate i)
    let ty : HitResult :=
      if (1 : F32) ≤ p then .great
      else if 0.9 < F32.toF64 p then .ok
      else if 0.75 < F32.toF64 p then .meh
      else o.h.minResult
    applyResult (← maxFuel) (i, -1) ty
  updateBonusScore i

/-- A top-level DHO's `UpdateSubTree` (`Drawable.cs:469-498`, `CompositeDrawable.cs:907-950`): `LoadComplete` on the
first update of a fresh pooled instance (→ `updateStateFromResult`, `DrawableHitObject.cs:225-241`), `UpdateTransforms`,
then nothing more unless present (no `Update`, no children, no `UpdateAfterChildren`/`UpdateResult`). -/
def updateDho (i : Nat) : SimM Unit := do
  let o ← topObj i
  let k := (← ostate i).inst
  if !(← instOf k).loaded then
    modifyInst k fun ins => { ins with loaded := true }
    updateStateFromResult i .top 1
  let t := (← st).t
  modifyInst k fun ins => { ins with tf := updateTransforms ins.tf t }
  if !(← partPresent i .top) then return
  match o.h.kind with
  | .circle => circleUpdateResult (i, -1) false
  | .slider => updateSlider i
  | .spinner => updateSpinner i
  | _ => pure ()

/-- `DrawableHitObject.OnKilled` (nested first, then self). -/
def onKilled (i : Nat) : SimM Unit := do
  let o ← topObj i
  match o.h.kind with
  | .circle => circleUpdateResult (i, -1) false
  | .slider =>
    for j in [0:o.nested.size] do
      if ← judged (i, j) then continue
      if (← nestedOf o j).kind == .head then circleUpdateResult (i, j) false
      else tryJudgeNested i j
    if (← ostate i).result.isNone then sliderCheckForResult i
  | .spinner =>
    -- nested ticks have no own CheckForResult; the spinner's CheckForResult (end reached → miss ticks, result)
    let t := (← st).t
    if (← ostate i).result.isNone && o.h.start ≤ t && !(t < o.h.endTime) then
      for j in [0:o.nested.size] do
        if !(← judged (i, j)) then missForcefully (i, j)
      let some sp := o.spinner | return
      let p := spinnerProgress sp (← ostate i)
      let ty : HitResult :=
        if (1 : F32) ≤ p then .great
        else if 0.9 < F32.toF64 p then .ok
        else if 0.75 < F32.toF64 p then .meh
        else o.h.minResult
      applyResult (← maxFuel) (i, -1) ty
  | _ => pure ()

/-! ## Lifetime management (`LifetimeEntryManager.Update`) -/

/-- `DrawableOsuHitObject.OnApply` bindings of a pooled instance (`DrawableOsuHitObject.cs:57-65`): the bound copies
only fire `ValueChanged` on a change: `UpdatePosition` (`Position = StackedPosition`; head: no-op; spinner:
`Position = Position`), slider `ScaleBindable` → body `PathRadius` (`PlaySliderBody`: `OBJECT_RADIUS * scale`, then
`ArgonSliderBody` once loaded: `path_radius * scale`; each change refreshes the body immediately), and the slider's
`pathVersion` (always changes, `DrawableSlider.cs:143-150`) → `Scheduler.AddOnce(Refresh)`. -/
def applyBindings (i : Nat) (p : Part) (k : Nat) : SimM Unit := do
  let o ← topObj i
  let hix := (← headIdxOf i)
  let h ← if p == .top then pure o.h else nestedOf o hix
  let ins ← instOf k
  let mut ins := ins
  let vEq (a b : Vec2) : Bool := (a.x == b.x || (a.x.isNaN && b.x.isNaN)) && (a.y == b.y || (a.y.isNaN && b.y.isNaN))
  let posChanged := !(vEq ins.boundPos h.pos)
  ins := { ins with boundPos := h.pos }
  let setPos (ins : Inst) (v : Vec2) : Inst := { ins with tf := ins.tf.set .position v }
  if posChanged then
    match h.kind with
    | .circle | .slider => ins := setPos ins h.stacked
    | .spinner => ins := setPos ins h.pos
    | _ => pure ()
  if h.kind != .spinner then
    let stackChanged := ins.boundStack != h.stackHeight
    ins := { ins with boundStack := h.stackHeight }
    if stackChanged && (h.kind == .circle || h.kind == .slider) then ins := setPos ins h.stacked
  let scaleChanged := !(ins.boundScale == h.scale || (ins.boundScale.isNaN && h.scale.isNaN))
  ins := { ins with boundScale := h.scale }
  if p == .top && o.h.kind == .slider then
    let sd ← need o.slider "slider data"
    if scaleChanged then
      let r1 : F32 := objectRadius * h.scale
      if !(ins.bodyRadius == r1) then
        let (sz, off) ← liftExcept (bodyRefresh sd r1)
        ins := { ins with bodyRadius := r1, bodySize := sz, bodyOffset := off }
      if ins.bodyLoaded then
        let r2 := (← ctx).env.argonPathRadius * h.scale
        if !(ins.bodyRadius == r2) then
          let (sz, off) ← liftExcept (bodyRefresh sd r2)
          ins := { ins with bodyRadius := r2, bodySize := sz, bodyOffset := off }
    ins := { ins with refreshPending := true }
  modifyInst k fun _ => ins

/-- `EntryBecameAlive` → `GetDrawable` (pool `Get` + `Apply`: nested heads first, each `UpdateState(Idle)` from `Apply`
since pooled instances are loaded, with one handler pass; then the object's own bindings and state) → `AddInternal`. -/
def becameAlive (i : Nat) : SimM Unit := do
  let o ← topObj i
  let s ← st
  let (slots, free) ← match s.freeList with
    | slot :: rest => do pure (← setA s.dictSlots slot (some i) "dictionary entries", rest)
    | [] => pure (s.dictSlots.push (some i), [])
  set { s with childCounter := s.childCounter + 1, dictSlots := slots, freeList := free, active := s.active.push i }
  let cid := (← st).childCounter
  let k ← poolGet (poolKind o.h.kind)
  let hk ← if o.h.kind == .slider then poolGet 2 else pure 0
  let a0 := (← instOf k).armed
  let ha0 := (← instOf hk).armed
  modifyObj i fun os => { os with armed := a0, headArmed := if o.h.kind == .slider then ha0 else .idle }
  modifyObj i fun os =>
    { os with
      life := .alive, childId := cid, hitAction := none, inst := k, headInst := hk
      hovered := false, tracking := false, acceptAnyAfter := none, lastPressed := [], sliderMouse := none
      headAlive := false, headLifetimeEnd := F64.posInf
      spinTracking := false, spinMouse := none, lastAngle := none, totalAccumulated := 0
      accumulatedAtLastCompletion := 0, currentSpinMax := 0, completedSpins := 0, lastReportTime := F64.negInf
      completedFullSpins := 0 }
  -- `Apply` runs `updateStateFromResult` only `if (IsLoaded)` (`DrawableHitObject.cs:311-319`); pool instances are only
  -- `LoadComponents`-loaded (`LoadState.Ready`, `DrawablePool.cs:53-61`) until their first `UpdateSubTree`, so a fresh
  -- instance gets its first state update from `LoadComplete` instead
  if o.h.kind == .slider then
    applyBindings i .head hk
    if (← instOf hk).loaded then updateStateFromResult i .head 1
  if o.h.kind == .spinner then
    let mut tis : Array Nat := #[]
    for j in [0:o.nested.size] do
      let tk ← poolGet (if (← nestedOf o j).kind == .spinnerBonusTick then 5 else 4)
      tis := tis.push tk
    modifyObj i fun os => { os with tickInsts := tis, tickLive := tis.map fun _ => false }
    for h : j in [0:tis.size] do
      if (← instOf (tis[j]'h.upper)).loaded then tickState i j 1 .idle true
  applyBindings i .top k
  if (← instOf k).loaded then updateStateFromResult i .top 1

/-- `EntryBecameDead` → `aliveDrawableMap.Remove` (Dictionary free list) → `RemoveDrawable`: `OnKilled`, then removal →
`Return` → `OnFree` (nested heads returned first, then `clearExistingStateTransforms`) → pool. -/
def becameDead (i : Nat) : SimM Unit := do
  let s ← st
  match s.dictSlots.idxOf? (some i) with
  | some slot => set { s with dictSlots := ← setA s.dictSlots slot none "dictionary entries", freeList := slot :: s.freeList }
  | none => throw s!"internal: dead object {i} not in the alive dictionary"
  modifyObj i fun os => { os with life := .past }
  onKilled i
  let o ← topObj i
  let os ← ostate i
  if o.h.kind == .slider then
    modifyInst os.headInst fun ins => { ins with tf := clearState ins.tf, armed := os.headArmed }
    poolReturn 2 os.headInst
  if o.h.kind == .spinner then
    for h : j in [0:os.tickInsts.size] do
      poolReturn (if (← nestedOf o j).kind == .spinnerBonusTick then 5 else 4) (os.tickInsts[j]'h.upper)
  modifyInst os.inst fun ins => { ins with tf := clearState ins.tf, bodyTf := clearState ins.bodyTf, armed := os.armed }
  poolReturn (poolKind o.h.kind) os.inst

def lifetimeUpdate : SimM Unit := do
  let t := (← st).t
  let c ← ctx
  if (← st).firstLifetimeUpdate then
    modify fun s => { s with firstLifetimeUpdate := false }
    let mut fut : Array Nat := #[]
    for i in [0:c.pb.objects.size] do
      let os ← ostate i
      if t < os.lifetimeStart then fut := fut.push i
      else if os.lifetimeEnd ≤ t then modifyObj i fun os => { os with life := .past }
      else becameAlive i
    let keyed ← fut.mapM fun i => do return (i, (← ostate i).lifetimeStart)
    let sorted := (stableSortBy keyed fun a b => a.2 < b.2).map (·.1)
    modify fun s => { s with futureOrder := sorted, nextFuture := 0 }
  else
    let mut fuel := c.pb.objects.size + 1
    while fuel > 0 do
      fuel := fuel - 1
      let s ← st
      if h : s.nextFuture < s.futureOrder.size then
        let i := s.futureOrder[s.nextFuture]
        let os ← ostate i
        if t < os.lifetimeStart then break
        modify fun s => { s with nextFuture := s.nextFuture + 1 }
        if os.lifetimeEnd ≤ t then modifyObj i fun os => { os with life := .past }
        else becameAlive i
      else break
  -- newly dead entries (activeEntries order)
  for i in (← st).active do
    let os ← ostate i
    if os.lifetimeEnd ≤ t || t < os.lifetimeStart then becameDead i
  let keep ← (← st).active.filterM fun i => do return (← ostate i).life == .alive
  modify fun s => { s with active := keep }

/-! ## Input -/

/-- `Interpolation.ValueAt(time, Vector2, Vector2, t0, t1)` (`osu.Framework/Utils/Interpolation.cs:352-362`). -/
def interpolate (time : F64) (v1 v2 : Vec2) (t0 t1 : F64) : Vec2 :=
  let current : F32 := F64.toF32 (time - t0)
  let duration : F32 := F64.toF32 (t1 - t0)
  if duration == f32zero || current == f32zero then v1
  else
    let tt : F32 := current / duration
    v1 + Vec2.scale (v2 - v1) tt

/-- `OsuFramedReplayInputHandler.CollectReplayInputs` position (gamefield). -/
def replayPosition (frames : Array Frame) (idx : Int) (t : F64) : SimM Vec2 := do
  let sf ← getA frames (max 0 idx).toNat "frames"
  let ef ← getA frames (min (idx + 1) (frames.size - 1 : Int)).toNat "frames"
  return interpolate t sf.pos ef.pos sf.time ef.time

/-- `InputManager.updateHoverEvents`: every alive (loaded) HitReceptor's `IsHovered := Contains(mouse)`;
receptors no longer in the positional queue are unhovered. -/
def updateHover : SimM Unit := do
  let c ← ctx
  let s ← st
  let mouse := s.mouse
  for i in [0:c.pb.objects.size] do
    let os ← getA s.objs i "objs"
    let o := (← topObj i)
    -- `DrawableHitObject.PropagatePositionalInputSubTree => HandleUserInput` (`DrawableHitObject.cs:76`): DHOs pass
    -- positional input regardless of their presence (alpha); the receptor itself is always present
    let hov ← if os.life != .alive then pure false
      else match o.h.kind with
        | .circle => do pure (receptorContains (← curCircleReceptor i) mouse)
        | .slider => do
          if !os.headAlive then pure false
          else pure (receptorContains (← curSliderGeom i).headReceptor mouse)
        | _ => pure false
    if hov != os.hovered then modifyObj i fun os => { os with hovered := hov }

/-- MouseMove to the positional queue: `SliderInputManager.OnMouseMove` of every alive slider
(on movement and as high-frequency event every step). -/
def sliderMouseMove : SimM Unit := do
  let c ← ctx
  let s ← st
  for i in s.active do
    if (← topObj i).h.kind == .slider then
      modifyObj i fun os => { os with sliderMouse := some s.mouse }

/-- `SpinnerRotationTracker.OnMouseMove` (only on actual movement: not `IRequireHighFrequencyMousePosition`):
`mousePosition = Parent!.ToLocalSpace(e.ScreenSpaceMousePosition)`. -/
def spinnerMouseMove : SimM Unit := do
  let c ← ctx
  let s ← st
  -- SpunOut: `HandleUserInput = false` stops positional input to the spinner subtree
  if c.cfg.spunOut then return
  for i in s.active do
    if (← topObj i).h.kind == .spinner then
      let g ← curSpinnerGeom i
      modifyObj i fun os => { os with spinMouse := some (g.aspect.toLocal s.mouse) }

/-- `HitReceptor.CanBeHit()`: circle `!AllJudged`; slider head `!AllJudged` of the head, or with
`OsuModClassic.ClassicNoteLock` `!slider.AllJudged` (`OsuModClassic.cs:96-99`). -/
def receptorCanBeHit (r : Ref) : SimM Bool := do
  if r.2 < 0 || (← ctx).cfg.classicHeadBlock then return !(← allJudged r.1)
  return !(← judged r)

/-- `InputBlockingMod.InputInterceptor.OnPressed` = `!checkCorrectAction(a)` (`InputBlockingMod.cs:76-113`) of the
k-th AL/SG; returns whether the press is blocked. -/
def interceptPress (k : Nat) (a : Action) : SimM Bool := do
  let c ← ctx
  let s ← st
  let (inAny, idx) ← liftExcept (periodIsInAny c.blockPeriods (← getA s.blockIdx k "blockIdx") s.t)
  set { s with blockIdx := ← setA s.blockIdx k idx "blockIdx" }
  if inAny then return false
  if a != .left && a != .right then return false
  let last ← getA s.blockLast k "blockLast"
  let alternate ← getA c.cfg.inputBlockers k "inputBlockers"
  let valid := if alternate then last != some a else (last.isNone || last == some a)
  if valid then
    let s ← st
    set { s with blockLast := ← setA s.blockLast k (some a) "blockLast" }
    return false
  return true

/-- `HitReceptor.OnPressed` over the `KeyBindingInputQueue` (`DrawableHitCircle.cs:277-308`). -/
def propagatePress (a : Action) : SimM Unit := do
  let c ← ctx
  -- the interceptors are the last children of the KeyBindingInputManager: first in the (reversed) input queue,
  -- the last-added one first (`InputBlockingMod.cs:43-46`)
  for k' in [0:c.cfg.inputBlockers.size] do
    let k := c.cfg.inputBlockers.size - 1 - k'
    if ← interceptPress k a then return
  for i in ← inputOrder do
    let o := (← topObj i)
    let os ← ostate i
    -- `PropagateNonPositionalInputSubTree => HandleUserInput` (`DrawableHitObject.cs:78`): presence does not matter
    let r? : Option Ref ← match o.h.kind with
      | .circle => pure (some (i, -1))
      | .slider => if os.headAlive then do pure (some (i, ((← headIdxOf i) : Int))) else pure none
      | _ => pure none
    let some r := r? | continue
    if !(← receptorCanBeHit r) then continue
    if a != .left && a != .right then continue
    if os.hovered then
      circleUpdateResult r true
      modifyObj i fun os => { os with hitAction := os.hitAction <|> some a }
      return

/-- `KeyBindingContainer.TriggerPressed` (Unique mode: only if not already pressed; added before propagation). -/
def triggerPressed (a : Action) : SimM Unit := do
  if (← st).pressed.contains a then return
  modify fun s => { s with pressed := s.pressed.push a }
  propagatePress a

/-- `KeyBindingContainer.TriggerReleased`. -/
def triggerReleased (a : Action) : SimM Unit := do
  modify fun s => { s with pressed := s.pressed.filter (· != a) }

/-- `ReplayInputHandler.ReplayState.Apply` (`osu.Game/Input/Handlers/ReplayInputHandler.cs:43-70`). -/
def replayStateDiff (last : Option (List Action)) (cur : List Action) : List Action × List Action :=
  match last with
  | none => ([], cur)
  | some [] => ([], cur)
  | some l =>
    if cur.isEmpty then (l, [])
    else if l == cur then ([], [])
    else (l.filter (!cur.contains ·), cur.filter (!l.contains ·))

def inputPhase : SimM Unit := do
  let c ← ctx
  let s ← st
  if c.frames.size == 0 then return     -- replay handler inactive (IsActive => HasFrames)
  let step ← stepAt s.k
  let gp ← replayPosition c.frames step.frameIndex s.t
  let hoc ← curHoc
  let screen := hoc.toScreen gp
  let mut hoverDone := false
  -- MousePositionAbsoluteInput.Apply
  if !s.mouseValid || !(s.mouse.eq screen) then
    modify fun s => { s with mouseValid := true, mouse := screen }
    sliderMouseMove
    spinnerMouseMove
    updateHover
    hoverDone := true
  -- ReplayState.Apply
  let cur ← if step.frameIndex < 0 then pure [] else do pure (← getA c.frames step.frameIndex.toNat "frames").actions
  let (released, pressed) := replayStateDiff (← st).lastReplay cur
  modify fun s => { s with lastReplay := some cur }
  for a in released do triggerReleased a
  for a in pressed do triggerPressed a
  -- high-frequency MouseMove (sliders; `CursorContainer.OnMouseMove`: `ActiveCursor.Position = Parent.ToLocalSpace(mouse)`)
  if (← st).mouseValid then
    sliderMouseMove
    modify fun s => { s with cursorPos := hoc.toLocal s.mouse }
  if !hoverDone then updateHover

/-! ## Playfield.Update: `IUpdatableByPlayfield` mods (P3) -/

/-- `OsuModRelax.Update` (`OsuModRelax.cs:73-156`; legacy replays only: `LegacyReplayPressHandler` triggers presses
directly on the KeyBindingContainer). -/
def relaxUpdate : SimM Unit := do
  let c ← ctx
  if c.cfg.lazerReplay then return
  let time := (← st).t
  let mut requiresHold := false
  let mut requiresHit := false
  for i in ← aliveObjects do
    let o := (← topObj i)
    -- `RELAX_LENIENCY = 12` (float)
    if time < o.h.start - 12 then break
    let os ← ostate i
    if (← isHitRef (i, -1)) || ((o.h.kind == .slider || o.h.kind == .spinner) && o.h.endTime < time) then continue
    -- handleHitCircle: `HitArea.IsHovered && HitWindows.CanBeHit(time - StartTime)`
    let hitCircle (h : HObj) : Bool := match h.hitWindows with
      | some hw => os.hovered && hw.canBeHit (time - h.start)
      | none => false
    match o.h.kind with
    | .circle => requiresHit := requiresHit || hitCircle o.h
    | .slider =>
      let hj := (← headIdxOf i)
      if !(← isHitRef (i, hj)) then requiresHit := requiresHit || hitCircle (← nestedOf o hj)
      requiresHold := requiresHold || (← mouseInFollowArea i (← instOf os.inst).drawableTracking)
    | .spinner =>
      requiresHold := requiresHold || (match o.spinner with | some sp => sp.spinsRequired > 0 | none => false)
    | _ => pure ()
  let changeState (down : Bool) : SimM Unit := do
    let s ← st
    if s.relaxDown == down then return
    set { s with relaxDown := down, relaxLast := time }
    if (← ctx).cfg.traceObj.isSome then
      modify fun s => { s with dbg := s.dbg.push s!"relax t={time} down={down} wasLeft={s.relaxWasLeft}" }
    if down then
      triggerPressed (if s.relaxWasLeft then .left else .right)
      modify fun s => { s with relaxWasLeft := !s.relaxWasLeft }
    else
      triggerReleased (if s.relaxWasLeft then .right else .left)
  if requiresHit then
    changeState false
    changeState true
  if requiresHold then changeState true
  else if (← st).relaxDown && 50 < time - (← st).relaxLast then changeState false

/-- `OsuModAutopilot.Update` (`OsuModAutopilot.cs:43-59`): at most one generated frame per step, injected as
`MousePositionAbsoluteInput { playfield.ToScreenSpace(pos) }.Apply` (immediate MouseMove + hover on change). -/
def autopilotUpdate : SimM Unit := do
  let c ← ctx
  let s ← st
  let fs := c.apFrames
  if s.apFrame == (fs.size : Int) - 1 then return
  let time := s.t
  let cur := s.apFrame
  let advance ← if cur < 0 then pure true else do
    let nxt ← getA fs (cur + 1).toNat "autopilot frames"
    let now ← getA fs cur.toNat "autopilot frames"
    pure (F64.abs (nxt.1 - time) ≤ F64.abs (now.1 - time))
  if advance then
    let n := (cur + 1).toNat
    modify fun s => { s with apFrame := cur + 1 }
    -- OsuPlayfield.ToScreenSpace: the HitObjectContainer is an untransformed child, same DrawInfo
    let screen := (← curEnv).hoc.toScreen (← getA fs n "autopilot frames").2
    let s ← st
    if !s.mouseValid || !(s.mouse.eq screen) then
      -- MouseMove also reaches the CursorContainer (`ActiveCursor.Position`, read by MG/RP later in this P3)
      let hoc := (← curEnv).hoc
      modify fun s => { s with mouseValid := true, mouse := screen, cursorPos := hoc.toLocal screen }
      sliderMouseMove
      spinnerMouseMove
      updateHover

/-- `InputBlockingMod.Update` (`:65-72`). -/
def inputBlockUpdate (k : Nat) : SimM Unit := do
  let c ← ctx
  let s ← st
  if (← getA s.blockLast k "blockLast").isSome then
    let (inAny, idx) ← liftExcept (periodIsInAny c.blockPeriods (← getA s.blockIdx k "blockIdx") s.t)
    set { s with blockIdx := ← setA s.blockIdx k idx "blockIdx" }
    if inAny then
      let s ← st
      set { s with blockLast := ← setA s.blockLast k none "blockLast" }

/-- `OsuModDepth.Update` (`OsuModDepth.cs:75-161`): every alive circle/slider gets `Position`/`Scale` from the time. -/
def depthUpdate : SimM Unit := do
  let c ← ctx
  let time := (← st).t
  let camZ : F32 := -200
  let camXY : Vec2 := ⟨256, 192⟩
  let maxDepth := c.cfg.depthMax
  let scaleForDepth (z : F32) : F32 := -camZ / F32.max 1 (z - camZ)
  let sliderMinDepth : F32 := -camZ / (1.5 : F32) + camZ
  let toPf (sc : F32) (p : Vec2) : Vec2 := Vec2.scale (p - camXY) sc + camXY
  for i in (← st).active do
    let o := (← topObj i)
    let h := o.h
    let k := (← ostate i).inst
    let dur ← if h.kind == .slider then do pure (← need o.slider "slider data").duration else pure 0
    let circleZ : F32 :=
      let speed := F32.toF64 maxDepth / h.preempt
      let appear := h.start - h.preempt
      maxDepth - F64.toF32 ((F64.max time appear - appear) * speed)
    let z? : Option F32 := match h.kind with
      | .circle => some circleZ
      | .slider =>
        let baseSpeed := F32.toF64 maxDepth / h.preempt
        let appear := h.start - h.preempt
        let zEnd := maxDepth - F64.toF32 ((F64.max (h.start + dur) appear - appear) * baseSpeed)
        if sliderMinDepth < zEnd then some circleZ else
        let offsetAfter := dur + 500
        let slowSpeed := F64.min (F32.toF64 (-sliderMinDepth) / offsetAfter) baseSpeed
        let decT := h.preempt * 0.2
        let decD : F32 := F64.toF32 (decT * (baseSpeed + slowSpeed) * 0.5)
        some (if time < h.start - decT then
            let full := decD + F64.toF32 (baseSpeed * (h.preempt - decT))
            full - F64.toF32 ((F64.max time appear - appear) * baseSpeed)
          else if time < h.start then
            let to := time - (h.start - decT)
            let dec := (slowSpeed - baseSpeed) / decT
            decD - F64.toF32 (baseSpeed * to + dec * to * to * 0.5)
          else
            let endT := h.start + offsetAfter
            Neg.neg (F64.toF32 ((F64.min time endT - h.start) * slowSpeed)))
      | _ => none
    if let some z := z? then
      let sc := scaleForDepth z
      modifyInst k fun ins => { ins with tf := (ins.tf.set .position (toPf sc h.stacked)).set .scale ⟨sc, sc⟩ }

/-- `OsuModMagnetised.Update` / `OsuModRepel.Update` (`OsuModMagnetised.cs:47-81`, `OsuModRepel.cs:48-95`). -/
def magnetUpdate (repel : Bool) : SimM Unit := do
  let c ← ctx
  let s ← st
  let cursorPos := s.cursorPos
  let elapsed ← elapsedNow
  for i in s.active do
    let o := (← topObj i)
    let os ← ostate i
    let k := os.inst
    let ins ← instOf k
    let pos := ins.tf.pos
    -- (a nested `(← …)` would be hoisted out of `&&` and evaluated for circles too)
    let headJudged ← if o.h.kind == .slider then judged (i, ((← headIdxOf i) : Int)) else pure false
    let dest0 : Vec2 := if !repel then cursorPos else
      let cl (v lo hi : Vec2) : Vec2 := ofTK (OsuTK.Vector2.clamp (toTK v) (toTK lo) (toTK hi))
      let d := cl (Vec2.scale pos 2 - cursorPos) Vec2.zero ⟨512, 384⟩
      match o.slider with
      | some sd =>
        -- `CalculatePossibleMovementBounds` (`OsuHitObjectGenerationUtils.Reposition.cs:266-303`)
        let r := F64.toF32 o.h.radius
        let (mnX, mxX, mnY, mxY) := sd.path.foldl (fun (a, b, c', d') v =>
          (F32.min a v.x, F32.max b v.x, F32.min c' v.y, F32.max d' v.y)) (F32.posInf, F32.negInf, F32.posInf, F32.negInf)
        let left := -(mnX - r)
        let right := (512 : F32) - (mxX + r)
        let top := -(mnY - r)
        let bottom := (384 : F32) - (mxY + r)
        let w := right - left
        let hh := bottom - top
        cl d ⟨left, top⟩ ⟨left + w, top + hh⟩
      | none => d
    let target? : Option Vec2 := match o.h.kind with
      | .circle => some dest0
      | .slider => some (if headJudged then dest0 - ins.ballPos else dest0)
      | _ => none
    if let some dest := target? then
      let damp : F64 := if repel
        then F32.toF64 (OsuTK.Vector2.distance (toTK pos) (toTK cursorPos)) / (0.04 * F32.toF64 c.cfg.repelStrength + 0.04)
        else Framework.Interpolation.lerp 3000 40 (F32.toF64 c.cfg.magnetStrength)
      let x := F64.toF32 (Framework.Interpolation.dampContinuously (F32.toF64 pos.x) (F32.toF64 dest.x) damp elapsed)
      let y := F64.toF32 (Framework.Interpolation.dampContinuously (F32.toF64 pos.y) (F32.toF64 dest.y) damp elapsed)
      modifyInst k fun ins => { ins with tf := ins.tf.set .position ⟨x, y⟩ }

def playfieldUpdate : SimM Unit := do
  for u in (← ctx).cfg.updatables do
    match u with
    | .dynRate k => dynRateUpdate k
    | .depth => depthUpdate
    | .barrelRoll =>
      -- `Rotation = (ccw ? -1 : 1) * 360 * (float)(Time.Current / 60000 * SpinSpeed)` (`ModBarrelRoll.cs:57-61`)
      let some (speed, ccw) := (← ctx).cfg.barrelRoll | pure ()
      let t := (← st).t
      let r : F32 := F32.ofInt ((if ccw then -1 else 1) * 360) * F64.toF32 (t / 60000 * speed)
      modify fun s => { s with brRot := r }
    | .magnetised => magnetUpdate false
    | .repel => magnetUpdate true
    | .relax => relaxUpdate
    | .autopilot => autopilotUpdate
    | .inputBlock k => inputBlockUpdate k

/-- FrameStableComponents: `JudgementProcessor.Update` (HasCompleted) and `DrainingHealthProcessor.Update` (drain). -/
def processorsPhase : SimM Unit := do
  let c ← ctx
  let s ← st
  let elapsed ← elapsedNow
  let completed (sc : ScoreSt) : ScoreSt :=
    { sc with hasCompleted := sc.judgedHits == c.smax.maxHits &&
        (sc.judgedHits == 0 || (match sc.lastTimeAbsolute with | some ta => ta < s.t | none => true)) }
  -- FrameStabilityContainer.updateClock: `manualClock.Rate = Math.Abs(referenceClock.Rate) * direction`
  -- (reference `Rate` = AggregateFrequency × AggregateTempo, oracle/Gameplay.cs:501-502), before this step's P3.
  let rate ← liftExcept (c.cfg.trueRate s.speed)
  set { s with clockRate := F64.abs rate * 1, score := completed s.score, scoreRP := completed s.scoreRP
               health := ← liftExcept (s.health.drain c.hcfg s.t elapsed)
               healthRP := ← liftExcept (s.healthRP.drain c.hcfg s.t elapsed) }

def stepOnce : SimM Unit := do
  processorsPhase
  inputPhase
  playfieldUpdate
  lifetimeUpdate
  for i in ← updateOrder do
    if (← ostate i).life == .alive then updateDho i

def run : SimM Unit := do
  let steps := (← ctx).steps
  for stp in steps, k in [0:steps.size] do
    let t := stp.time
    modify fun s => { s with k, t }
    stepOnce
    if let some i := (← ctx).cfg.traceObj then
      let s ← st
      let os ← ostate i
      let ins ← instOf os.inst
      let m := match os.spinMouse with | some p => s!"{p.x.toBits},{p.y.toBits}" | none => "-"
      modify fun s => { s with dbg := s.dbg.push s!"t={t.toBits} life={os.life == Life.alive} pressed={s.pressed.size} track={os.spinTracking} smouse={m} rot={os.totalAccumulated.toBits} hov={os.hovered} pos={ins.tf.pos.x.toBits},{ins.tf.pos.y.toBits} a={ins.tf.alpha.toBits} size={ins.size.x.toBits},{ins.size.y.toBits} origin={ins.origin.x.toBits},{ins.origin.y.toBits} mouse={s.mouse.x.toBits},{s.mouse.y.toBits}" }

end Sim

/-- `ModAdaptiveSpeed.ApplyToBeatmap` (`ModAdaptiveSpeed.cs:190-216`): objects with non-empty hit windows in
depth-first pre-order (top-level, then nested), `endTimes = GetEndTime()s .Order().Distinct()`, and for each object
the end time preceding its own (`BinarySearch`, complement, `- 1`). -/
def precedingEndTimes (pb : Playable) : Except String (Array (Option F64 × Array (Option F64))) := do
  let mut ts : Array F64 := #[]
  for o in pb.objects do
    if o.h.hitWindows.isSome then ts := ts.push o.h.endTime
    for n in o.nested do
      if n.hitWindows.isSome then ts := ts.push n.endTime
  -- `Order()` (ModAdaptiveSpeed.cs:193) = LINQ `OrderBy(identity)` with `Comparer<double>.Default` (`double.CompareTo`:
  -- NaN first, -0 = +0): a STABLE sort (EnumerableSorter ties broken by index; double is not "implicitly stable" in
  -- .NET 10, so no unstable fast path), then `Distinct()` (`double.Equals`, keeps the first). D55.
  let sorted := stableSortBy ts fun a b => compareD a b < 0
  let mut endTimes : Array F64 := #[]
  for x in sorted do
    let fresh := match endTimes.back? with
      | none => true
      | some l => !(Framework.Bindable.equalsD l x)
    if fresh then endTimes := endTimes.push x
  let look (hw : Option HitWindows) (e : F64) : Except String (Option F64) :=
    if hw.isNone then pure none else
    let b := bsearch endTimes fun x => compareD x e
    let idx := (if b < 0 then -b - 1 else b) - 1
    if idx < 0 then pure none else
    match endTimes[idx.toNat]? with
    | some v => pure (some v)
    | none => throw "internal: precedingEndTimes binary search out of range"
  pb.objects.mapM fun o => do return (← look o.h.hitWindows o.h.endTime, ← o.nested.mapM fun n => look n.hitWindows n.endTime)

/-- `InputBlockingMod.ApplyToDrawableRuleset` periods (`InputBlockingMod.cs:48-60`): `(int.MinValue, V(first) - 1)` and
`(break.Start, V(first object with StartTime >= break.End) - 1)`, `V(h) = StartTime - HitWindows.WindowFor(Meh)` (0 for
empty windows), sorted by start (`PeriodTracker`, stable). `new Period(start, end)` throws for `start >= end` and
`First(…)` throws for a break without a later object (load failures in lazer): rejected. -/
def inputBlockPeriods (pb : Playable) : Except String (Array (F64 × F64)) := do
  let some o0 := pb.objects[0]? | return #[]
  let vt (h : HObj) : F64 := h.start - (match h.hitWindows with | some hw => hw.meh | none => 0)
  let period (a b : F64) : Except String (F64 × F64) :=
    if a < b then pure (a, b) else throw "InputBlockingMod: invalid period (start >= end), lazer throws"
  let mut ps : Array (F64 × F64) := #[← period (F64.ofInt (-2147483648)) (vt o0.h - 1)]
  for (bs, be) in pb.breaks do
    match pb.objects.find? (fun o => be ≤ o.h.start) with
    | some o => ps := ps.push (← period bs (vt o.h - 1))
    | none => throw "InputBlockingMod: break without a following object, lazer throws"
  return stableSortBy ps fun a b => a.1 < b.1

/-- Build the context and initial state. Rejects malformed playables (a slider without head or tail). -/
def mkCtx (env : Env) (cfg : Config) (pb : Playable) (frames : Array Frame) (kind : ScheduleKind) : Except String Ctx := do
  let idxOf (o : TopObj) (k : Kind) (last : Bool) : Except String Nat := do
    if o.h.kind != .slider then return 0
    let mut r : Option Nat := none
    for n in o.nested, j in [0:o.nested.size] do
      if n.kind == k then
        r := some j
        if !last then break
    match r with
    | some j => return j
    | none => throw s!"malformed playable: slider at {o.h.start} without a {repr k}"
  let apFrames ← if cfg.updatables.any (fun u => match u with | .autopilot => true | _ => false)
    then do pure ((← AutoGen.generate pb cfg.rateMods.toList).map fun f => (f.time, (⟨f.pos.x, f.pos.y⟩ : Vec2)))
    else pure #[]
  let stepsA ← steps kind pb frames
  let hcfg ← mkHealthCfg pb cfg.legacyHealth
  let blockPeriods ← if cfg.inputBlockers.isEmpty then pure #[] else inputBlockPeriods pb
  let precEnd ← if cfg.dynRates.any (fun d => match d with | .adaptive _ => true | _ => false)
    then precedingEndTimes pb else pure #[]
  let headIdx ← pb.objects.mapM (idxOf · .head false)
  let tailIdx ← pb.objects.mapM (idxOf · .tail true)
  return {
    env, cfg, pb, frames, steps := stepsA, futureOrder := #[]
    smax := { scoreMaxima pb cfg.scoreMultiplier with rankAdjust := cfg.rankAdjust }, hcfg
    apFrames, blockPeriods
    -- `ModWithVisibilityAdjustment.ApplyToBeatmap` FirstObject (HD/TC skip spinners and their ticks)
    firstObj := cfg.visMods.map fun vm =>
      pb.objects.findIdx? fun o => !(vm.skipsSpinners && o.h.kind == .spinner)
    precEnd
    lastFrameTime := frames.back?.map (·.time)
    headIdx, tailIdx }

def netStr {α} (e : Except NetExn α) : Except String α :=
  match e with | .ok v => .ok v | .error x => .error s!"lazer would throw: {repr x}"

/-- `initWithoutMods`: `TotalScoreWithoutMods` as `ScoreProcessor.ApplyBeatmap` leaves it (`ScoreMax.initWithoutMods`,
D80a); `Reset` zeroes every other score field. -/
def initState (cfg : Config) (pb : Playable) (initWithoutMods : Int) : Except String St := do
  let adaptive := cfg.dynRates.filterMap fun d => match d with | .adaptive i => some i | _ => none
  let asInit ← netStr (adaptive.mapM fun i => DynRate.setSpeed (.adaptive i) 1 i)
  let speed ← netStr (cfg.dynRates.mapM (·.initialSpeed))
  -- `ScoreProcessor.Reset` → `updateRank()` with `Accuracy = 1` → X (adjusted); `TotalScoreWithoutMods` is not reset
  let score : ScoreSt := { rank := adjustRank cfg.rankAdjust .x, totalScoreWithoutMods := initWithoutMods }
  let health : HealthSt := { retries := cfg.easyRetries }
  let objs := pb.objects.map fun o =>
      ({ lifetimeStart := o.h.start - o.h.preempt
         -- OsuHitObjectLifetimeEntry: LifetimeEnd = EndTime + HitWindows.WindowFor(Miss) (0 for empty windows)
         lifetimeEnd := o.h.endTime + (match o.h.hitWindows with | some hw => hw.miss | none => 0)
         nested := o.nested.map fun _ => none } : OState)
  return {
    objs, score, scoreRP := score, health, healthRP := health, speed
    -- AS `ApplyToTrack`: `targetRate = InitialRate` (via the InitialRate callback), `recentRates = [InitialRate] * 8`
    asTarget := asInit, asRecent := adaptive.map fun i => Array.replicate 8 i, asSeen := adaptive.map fun _ => []
    blockLast := cfg.inputBlockers.map fun _ => none, blockIdx := cfg.inputBlockers.map fun _ => 0 }

/-- Run the simulation; `Except` carries a rejection (malformed input, or a computation lazer would throw on). -/
def runWith (c : Ctx) (cfg : Config) (pb : Playable) : Except String St := do
  let ((), s) ← (Sim.run.run c).run (← initState cfg pb c.smax.initWithoutMods)
  return s

def simulate (env : Env) (cfg : Config) (pb : Playable) (frames : Array Frame) (kind : ScheduleKind) :
    Except String (Ctx × St) := do
  let c ← mkCtx env cfg pb frames kind
  return (c, ← runWith c cfg pb)

end OsuModel.Sim
