import OsuModel.Sim.Geometry
import OsuModel.Sim.Schedule
import OsuModel.Sim.Scoring
import OsuModel.Sim.Mods
import OsuModel.Sim.Transforms

/-!
# Simulation state

One `OState` per top-level hit object: its `HitObjectLifetimeEntry` (lifetime + alive state in the
`HitObjectContainer`'s `LifetimeEntryManager`), the judgement results of the object and of its
nested objects (`JudgementResult.Type`, `RawTime`), and the per-drawable state that influences
judgement: `HitReceptor.HitAction` / `IsHovered` (circle, or the slider head's receptor), the
`SliderInputManager` state, the slider head's lifetime.

Global state: the `HitObjectContainer`'s alive dictionary (`PooledDrawableWithLifetimeContainer.aliveDrawableMap`,
a .NET `Dictionary` whose enumeration order — with free-list reuse — determines `AliveObjects` tie order),
the drawable ChildID counter (`CompositeDrawable.currentChildID`, determines update/input order ties),
input-manager state (mouse position, last replay state, `KeyBindingContainer.pressedActions`),
and the ScoreProcessor's combo/statistics.
-/

namespace OsuModel.Sim
open OsuModel.Net OsuModel.Replay

inductive Life where
  | future | alive | past
deriving Inhabited, Repr, DecidableEq, BEq

/-- `ArmedState` of a DHO (`DrawableHitObject.State`). -/
inductive Armed where
  | idle | hit | miss
deriving Inhabited, BEq, DecidableEq

/-- A pooled drawable instance (`DrawablePool` stacks, `OsuPlayfield.cs:141-164`). State that survives re-use:
the transformable members/trackers (after `clearExistingStateTransforms` on free), `LoadComplete` done, the bound copies
of `PositionBindable`/`StackHeightBindable`/`ScaleBindable` (their `ValueChanged` only fires on a change), and for
`DrawableSlider` its `Size`/`OriginPosition`, the head's `RelativeAnchorPosition`, the slider body's last
`Refresh` result, pending scheduled refresh and the body's transforms, and the `Tracking` bindable. -/
structure Inst where
  /-- `DrawableOsuHitObject.load`: `Alpha = 0` -/
  tf : TObj := { alpha := 0 }
  loaded : Bool := false
  boundPos : Vec2 := Vec2.zero
  boundStack : Int := 0
  boundScale : F32 := 0
  size : Vec2 := Vec2.zero
  origin : Vec2 := Vec2.zero
  relAnchor : Vec2 := Vec2.zero
  bodySize : Vec2 := Vec2.zero
  bodyOffset : Vec2 := Vec2.zero
  bodyRadius : F32 := 0
  refreshPending : Bool := false
  bodyTf : TObj := {}
  bodyLoaded : Bool := false
  drawableTracking : Bool := false
  /-- `DrawableHitObject.State` (a bindable of the instance: survives re-use; a re-used instance that never got loaded
  keeps its previous state until its next `UpdateState`) -/
  armed : Armed := .idle
  /-- `DrawableSliderBall.Position` (`UpdateProgress` in the slider's `UpdateAfterChildren`) -/
  ballPos : Vec2 := Vec2.zero
deriving Inhabited

/-- Pools: 0 = DrawableHitCircle, 1 = DrawableSlider, 2 = DrawableSliderHead, 3 = DrawableSpinner,
4 = DrawableSpinnerTick, 5 = DrawableSpinnerBonusTick. -/
def poolInitial : Array Nat := #[20, 20, 20, 2, 10, 10]
def poolMax : Array Nat := #[100, 100, 100, 20, 200, 200]

/-- A judgement result: `(Type, RawTime)`. -/
abbrev Res := HitResult × F64

structure OState where
  life : Life := .future
  lifetimeStart : F64
  lifetimeEnd : F64
  /-- `Drawable.ChildID` in the HitObjectContainer (assigned on `AddInternal`). -/
  childId : Nat := 0
  result : Option Res := none
  nested : Array (Option Res)
  /-- `HitReceptor.HitAction` (circle's own receptor, or the slider head's). -/
  hitAction : Option Action := none
  /-- `HitReceptor.IsHovered`. -/
  hovered : Bool := false
  /-- Slider head DHO lifetime (nested in `headContainer`) and whether it was alive at the last slider update. -/
  headLifetimeEnd : F64 := F64.posInf
  headAlive : Bool := false
  /-- `SliderInputManager` -/
  tracking : Bool := false
  /-- pooled instances in use (top-level DHO, slider head DHO) -/
  inst : Nat := 0
  headInst : Nat := 0
  /-- `DrawableHitObject.State` of the top-level DHO and of the head -/
  armed : Armed := .idle
  headArmed : Armed := .idle
  /-- spinner tick DHO instances (per nested index; 0 for non-ticks) and whether the spinner has set their
  `LifetimeStart` (`DrawableSpinner.Update`: next unjudged tick, `DrawableSpinner.cs:288-302`) -/
  tickInsts : Array Nat := #[]
  tickLive : Array Bool := #[]
  acceptAnyAfter : Option F64 := none
  lastPressed : List Action := []
  sliderMouse : Option Vec2 := none
  /-- `SpinnerRotationTracker` (`Skinning/Default/SpinnerRotationTracker.cs`) -/
  spinTracking : Bool := false
  spinMouse : Option Vec2 := none
  lastAngle : Option F32 := none
  /-- `SpinnerSpinHistory` (`Objects/Drawables/SpinnerSpinHistory.cs`) -/
  totalAccumulated : F32 := 0
  accumulatedAtLastCompletion : F32 := 0
  currentSpinMax : F32 := 0
  completedSpins : Nat := 0
  lastReportTime : F64 := F64.negInf
  /-- `DrawableSpinner.completedFullSpins` -/
  completedFullSpins : Int := 0
deriving Inhabited

/-- One judgement as seen by the processors (oracle `judgements[]`). -/
structure JRec where
  top : Nat
  nested : Int
  kind : Kind
  typeName : String := ""
  result : HitResult
  time : F64
  combo : Nat
  /-- live semantics: `HealthProcessor.Health` after the judgement, `FailedAtJudgement` -/
  health : F64 := 1
  failed : Bool := false
  /-- the same under ReplayPlayer fail semantics -/
  comboRP : Nat := 0
  healthRP : F64 := 1
  failedRP : Bool := false
deriving Inhabited

/-- Static per-run context. -/
structure Ctx where
  env : Env
  cfg : Config
  pb : Playable
  frames : Array Frame
  steps : Array Step
  /-- Entries that are `Future` after the first lifetime update, in `LifetimeStartComparator` order. -/
  futureOrder : Array Nat
  /-- Per slider: index of the head / tail in `NestedHitObjects` (located by type: nested objects are
  sorted with the unstable `List.Sort`, so equal start times could reorder them). `mkCtx` rejects a slider without
  a head or tail; for other objects the entry is 0 and never used. -/
  headIdx : Array Nat
  tailIdx : Array Nat
  smax : ScoreMax
  hcfg : HealthCfg
  /-- `Replay.Frames.LastOrDefault()?.Time` (ReplayPlayer fail gate) -/
  lastFrameTime : Option F64
  /-- per `Config.visMods` entry: the top-level object containing `FirstObject` (increased visibility) -/
  firstObj : Array (Option Nat) := #[]
  /-- `ModAdaptiveSpeed.precedingEndTimes` per object (`(top-level, nested)`), only with AS. -/
  precEnd : Array (Option F64 × Array (Option F64)) := #[]
  /-- Autopilot: `OsuAutoGenerator` frames (time, gamefield position). -/
  apFrames : Array (F64 × Vec2) := #[]
  /-- `InputBlockingMod.nonGameplayPeriods` (sorted by start). -/
  blockPeriods : Array (F64 × F64) := #[]
deriving Inhabited

structure St where
  k : Nat := 0
  t : F64 := 0
  objs : Array OState
  firstLifetimeUpdate : Bool := true
  nextFuture : Nat := 0
  futureOrder : Array Nat := #[]
  /-- `LifetimeEntryManager.activeEntries` (list order). -/
  active : Array Nat := #[]
  /-- `Dictionary` entries array (`none` = free slot) and free list (most recently freed first). -/
  dictSlots : Array (Option Nat) := #[]
  freeList : List Nat := []
  childCounter : Nat := 0
  mouseValid : Bool := false
  mouse : Vec2 := Vec2.zero
  lastReplay : Option (List Action) := none
  pressed : Array Action := #[]
  /-- processors, live (`Player`) and `ReplayPlayer` fail semantics -/
  score : ScoreSt := {}
  health : HealthSt := {}
  scoreRP : ScoreSt := {}
  healthRP : HealthSt := {}
  out : Array JRec := #[]
  /-- `SpeedChange` of each time-varying rate mod (`Config.dynRates`). -/
  speed : Array F64 := #[]
  /-- `ModAdaptiveSpeed` state (`targetRate`, `recentRates`, keys of `ratesForRewinding`), per AS mod. -/
  asTarget : Array F64 := #[]
  asRecent : Array (Array F64) := #[]
  asSeen : Array (List (Nat × Int)) := #[]
  /-- `FrameStabilityContainer` clock `Rate` set in `updateClock` (= reference `Rate` at step start). -/
  clockRate : F64 := 1
  /-- `OsuModRelax`: `isDownState`, `wasLeft`, `lastStateChangeTime` -/
  relaxDown : Bool := false
  relaxWasLeft : Bool := false
  relaxLast : F64 := 0
  /-- `OsuModAutopilot.currentFrame` -/
  apFrame : Int := -1
  /-- `InputBlockingMod`: `LastAcceptedAction`, `PeriodTracker.nearestIndex` (per mod) -/
  blockLast : Array (Option Action) := #[]
  blockIdx : Array Nat := #[]
  /-- pooled instances; per pool a LIFO stack (`none` = a never-used prewarmed instance) -/
  insts : Array Inst := #[]
  pools : Array (List (Option Nat)) := poolInitial.map fun n => List.replicate n none
  /-- BarrelRoll: `OsuPlayfieldAdjustmentContainer.Rotation` -/
  brRot : F32 := 0
  /-- `OsuModTransform.theta` (shared by all DHOs, advanced per handler call) -/
  theta : F32 := 0
  /-- `Playfield.Cursor.ActiveCursor.DrawPosition` (set by MouseMove in the input phase) -/
  cursorPos : Vec2 := Vec2.zero
  /-- debug messages (printed to stderr by simtest) -/
  dbg : Array String := #[]
deriving Inhabited

/-- The simulation monad. `Except String` is the explicit rejection channel: every array/option access in the
simulation is either provably in bounds or rejects the input with a message (never a silent `default`). -/
abbrev SimM := ReaderT Ctx (StateT St (Except String))

end OsuModel.Sim
