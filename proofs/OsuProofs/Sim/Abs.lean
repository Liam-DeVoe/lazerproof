/-
Abstraction maps (`AbsTo`, OsuProofs/Auto/Abs.lean style) from the Aeneas translation of the sim+replay
Rust port (`OsuImpl.sim.*`, `OsuImpl.replay.*`; Generated/SimTypes.lean) to the spec (`OsuModel.Sim`,
`OsuModel.Replay`, Lean spec frozen at 1b0a176, DECISIONS D20).

Representation choices of the port (docs/rust-sim-port.md "Correspondence"), each a bijection on reachable values:
* statistics: spec `Array Nat` of 100 entries indexed by `HitResult.toNat` ↦ Rust `[u64; 18]` by ordinal
  (`hr_index`); `statsS` rebuilds the 100-entry array (entries other than 0..16, 99 are 0 in every reachable state).
* `HObj.typeName : String` ↦ `type_id : u32` into a name table held by the shell (+ `strict_tail`). The table
  is not part of the translated data; `hobjS tn` takes it as a parameter. The `AbsTo` instance uses the kind's
  default class name (the table entry 0, `TYPE_DEFAULT`) — use it only in statements whose spec side does not
  read `typeName`.
* break / no-drain periods `(F64 × F64)` ↦ `Period { start, end }`.
-/
import OsuProofs.Auto.Abs
import OsuProofs.Generated.SimFuns
import OsuModel.Sim.State
open Aeneas Aeneas.Std Result
open OsuModel.Net

deriving instance Inhabited for OsuImpl.sim.mods.FailCond
deriving instance Inhabited for OsuImpl.sim.mods.FailOverride
deriving instance Inhabited for OsuImpl.sim.mods.AccChallenge
deriving instance Inhabited for OsuImpl.sim.playable.Period
deriving instance Inhabited for OsuImpl.sim.basic.Vec2
deriving instance Inhabited for OsuImpl.sim.basic.HitResult
deriving instance Inhabited for OsuImpl.sim.playable.Kind
deriving instance Inhabited for OsuImpl.sim.playable.HObj
deriving instance Inhabited for OsuImpl.sim.playable.TopObj

namespace OsuProofs
open OsuImpl

instance : AbsTo sim.basic.Vec2 OsuModel.Sim.Vec2 := ⟨fun v => ⟨v.x, v.y⟩⟩
instance : AbsTo sim.basic.Mat3 OsuModel.Sim.Mat3 :=
  ⟨fun m => ⟨m.m11, m.m12, m.m13, m.m21, m.m22, m.m23, m.m31, m.m32, m.m33⟩⟩
instance : AbsTo sim.basic.DrawInfo OsuModel.Sim.DrawInfo := ⟨fun d => ⟨abs d.matrix, abs d.inverse⟩⟩

def hrS : sim.basic.HitResult → OsuModel.Sim.HitResult
  | .None => .none | .Miss => .miss | .Meh => .meh | .Ok_ => .ok | .Good => .good | .Great => .great
  | .Perfect => .perfect | .SmallTickMiss => .smallTickMiss | .SmallTickHit => .smallTickHit
  | .LargeTickMiss => .largeTickMiss | .LargeTickHit => .largeTickHit | .SmallBonus => .smallBonus
  | .LargeBonus => .largeBonus | .IgnoreMiss => .ignoreMiss | .IgnoreHit => .ignoreHit
  | .ComboBreak => .comboBreak | .SliderTailHit => .sliderTailHit | .LegacyComboIncrease => .legacyComboIncrease
instance : AbsTo sim.basic.HitResult OsuModel.Sim.HitResult := ⟨hrS⟩

def kindS : sim.playable.Kind → OsuModel.Sim.Kind
  | .Circle => .circle | .Slider => .slider | .Spinner => .spinner | .Head => .head | .Tick => .tick
  | .Repeat => .«repeat» | .Tail => .tail | .SpinnerTick => .spinnerTick | .SpinnerBonusTick => .spinnerBonusTick
instance : AbsTo sim.playable.Kind OsuModel.Sim.Kind := ⟨kindS⟩

instance : AbsTo sim.playable.HitWindows OsuModel.Sim.HitWindows := ⟨fun w => ⟨w.great, w.ok_, w.meh, w.miss⟩⟩

/-- `HObj` with the shell's type-name table `tn` (`type_id` ↦ class name; `0` = the kind's default name). -/
def hobjS (tn : Nat → String) (h : sim.playable.HObj) : OsuModel.Sim.HObj :=
  { kind := kindS h.kind, typeName := tn h.type_id.val, start := h.start, endTime := h.end_time
    pos := abs h.pos, stacked := abs h.stacked, stackHeight := h.stack_height.val, scale := h.scale
    radius := h.radius, preempt := h.preempt, fadeIn := h.fade_in, maxJudgementOffset := h.max_judgement_offset
    hitWindows := h.hit_windows.map abs, maxResult := hrS h.max_result, minResult := hrS h.min_result
    newCombo := h.new_combo, comboIndex := h.combo_index.val, indexInCombo := h.index_in_combo.val
    lastInCombo := h.last_in_combo, spanIndex := h.span_index.val, spanStart := h.span_start
    pathProgress := h.path_progress, repeatIndex := h.repeat_index.val }
/-- Default table: only the kind's default class name. -/
def simTnDefault (_ : Nat) : String := ""
instance : AbsTo sim.playable.HObj OsuModel.Sim.HObj := ⟨hobjS simTnDefault⟩

instance : AbsTo sim.playable.SliderData OsuModel.Sim.SliderData :=
  ⟨fun s => { spanCount := s.span_count.val, duration := s.duration, spanDuration := s.span_duration
              velocity := s.velocity, pathDistance := s.path_distance, classic := s.classic
              path := abs s.path, cumLen := abs s.cum_len }⟩
instance : AbsTo sim.playable.SpinnerData OsuModel.Sim.SpinnerData :=
  ⟨fun s => ⟨s.duration, s.spins_required.val, s.max_bonus_spins.val⟩⟩
def topS (tn : Nat → String) (o : sim.playable.TopObj) : OsuModel.Sim.TopObj :=
  { h := hobjS tn o.h, slider := o.slider.map abs, spinner := o.spinner.map abs
    nested := (o.nested.val.map (hobjS tn)).toArray }
instance : AbsTo sim.playable.TopObj OsuModel.Sim.TopObj := ⟨topS simTnDefault⟩
instance : AbsTo sim.playable.Period (F64 × F64) := ⟨fun p => (p.start, p.«end»)⟩
instance : AbsTo sim.playable.Difficulty OsuModel.Sim.Difficulty := ⟨fun d => ⟨d.cs, d.hp, d.od, d.ar⟩⟩
def playableS (tn : Nat → String) (p : sim.playable.Playable) : OsuModel.Sim.Playable :=
  { beatmapVersion := p.beatmap_version.val, audioLeadIn := p.audio_lead_in, difficulty := abs p.difficulty
    baseDifficulty := abs p.base_difficulty, sliderMultiplier := p.slider_multiplier
    sliderTickRate := p.slider_tick_rate, breaks := abs p.breaks
    objects := (p.objects.val.map (topS tn)).toArray }
instance : AbsTo sim.playable.Playable OsuModel.Sim.Playable := ⟨playableS simTnDefault⟩

/-! ## Scoring -/
instance : AbsTo sim.scoring.JInfo OsuModel.Sim.JInfo :=
  ⟨fun j => { kind := kindS j.kind, maxResult := hrS j.max_result, minResult := hrS j.min_result, ty := hrS j.ty
              timeAbsolute := j.time_absolute, endTime := j.end_time, timeOffset := j.time_offset
              newCombo := j.new_combo, lastInCombo := j.last_in_combo }⟩

def rankS : sim.scoring.Rank → OsuModel.Sim.Rank
  | .D => .d | .C => .c | .B => .b | .A => .a | .S => .s | .SH => .sh | .X => .x | .XH => .xh | .F => .f
instance : AbsTo sim.scoring.Rank OsuModel.Sim.Rank := ⟨rankS⟩

/-- Statistics by ordinal (18 entries) ↦ the spec's 100-entry array by enum value (`LegacyComboIncrease = 99`). -/
def statsS (a : Std.Array Std.U64 18#usize) : _root_.Array Nat :=
  Array.ofFn (n := 100) fun i =>
    if i.val = 99 then (a.val.getD 17 0#u64).val else if i.val < 17 then (a.val.getD i.val 0#u64).val else 0
theorem statsS_size (a : Std.Array Std.U64 18#usize) : (statsS a).size = OsuModel.Sim.nStats := by
  simp [statsS, OsuModel.Sim.nStats]

def scoreS (s : sim.scoring.ScoreSt) : OsuModel.Sim.ScoreSt :=
  { combo := s.combo.val, highestCombo := s.highest_combo.val, stats := statsS s.stats, stats_size := statsS_size _
    currentMaximumBaseScore := s.current_maximum_base_score, currentBaseScore := s.current_base_score
    currentAccuracyJudgementCount := s.current_accuracy_judgement_count.val
    currentComboPortion := s.current_combo_portion, currentBonusPortion := s.current_bonus_portion
    accuracy := s.accuracy, totalScoreWithoutMods := s.total_score_without_mods.val
    totalScore := s.total_score.val, judgedHits := s.judged_hits.val
    lastTimeAbsolute := s.last_time_absolute, hasCompleted := s.has_completed
    maximumAccuracy := s.maximum_accuracy, rank := rankS s.rank }
instance : AbsTo sim.scoring.ScoreSt OsuModel.Sim.ScoreSt := ⟨scoreS⟩

instance : AbsTo sim.scoring.ScoreMax OsuModel.Sim.ScoreMax :=
  ⟨fun m => { maximumBaseScore := m.maximum_base_score, maximumComboPortion := m.maximum_combo_portion
              maximumAccuracyJudgementCount := m.maximum_accuracy_judgement_count.val
              maxStats := statsS m.max_stats, maxHits := m.max_hits.val, scoreMultiplier := m.score_multiplier
              rankAdjust := m.rank_adjust, initWithoutMods := m.init_without_mods.val }⟩

instance : AbsTo sim.scoring.HealthSt OsuModel.Sim.HealthSt :=
  ⟨fun h => { health := h.health, hasFailed := h.has_failed, comboResult := h.combo_result.val
              nearestIndex := h.nearest_index.val, failTriggers := h.fail_triggers.val, failed := h.failed
              failTime := h.fail_time, retries := abs h.retries }⟩
instance : AbsTo sim.scoring.HealthCfg OsuModel.Sim.HealthCfg :=
  ⟨fun c => { legacy := c.legacy, hp := c.hp, drainRate := c.drain_rate, hpMultiplierNormal := c.hp_multiplier_normal
              drainStartTime := c.drain_start_time, gameplayEndTime := c.gameplay_end_time, periods := abs c.periods }⟩

/-! ## Mods (`Config`) -/
instance : AbsTo sim.mods.AudioProp OsuModel.Sim.AudioProp := ⟨fun | .Frequency => .frequency | .Tempo => .tempo⟩
instance : AbsTo sim.mods.RateVal OsuModel.Sim.RateVal := ⟨fun | .Const v => .const v | .Dyn k => .dyn k.val⟩
instance : AbsTo sim.mods.RateSource (OsuModel.Sim.AudioProp × OsuModel.Sim.RateVal) := ⟨fun r => (abs r.prop, abs r.val)⟩
instance : AbsTo sim.mods.DynRate OsuModel.Sim.DynRate :=
  ⟨fun | .TimeRamp a b c d => .timeRamp a b c d | .Adaptive a => .adaptive a⟩
instance : AbsTo sim.mods.FailOverride OsuModel.Sim.FailOverride :=
  ⟨fun | .Veto => .veto | .Easy k => .easy k.val | .Allow => .allow⟩
instance : AbsTo sim.mods.FailCond OsuModel.Sim.FailCond :=
  ⟨fun | .SuddenDeath b => .suddenDeath b | .Perfect => .perfect | .TargetPractice => .targetPractice⟩
instance : AbsTo sim.mods.RateMod OsuModel.Sim.RateMod :=
  ⟨fun | .Speed s => .speed s | .TimeRamp a b c d => .timeRamp a b c d | .Adaptive a => .adaptive a⟩
instance : AbsTo sim.mods.Updatable OsuModel.Sim.Updatable :=
  ⟨fun | .DynRate k => .dynRate k.val | .Depth => .depth | .Magnetised => .magnetised | .Repel => .repel
       | .BarrelRoll => .barrelRoll | .Relax => .relax | .Autopilot => .autopilot | .InputBlock k => .inputBlock k.val⟩
instance : AbsTo sim.mods.VisMod OsuModel.Sim.VisMod :=
  ⟨fun | .ScaleTween s => .scaleTween s | .SpinIn => .spinIn | .Transform => .transform | .Wiggle w => .wiggle w
       | .TargetPractice => .targetPractice | .Hidden b => .hidden b | .Inert => .inert
       | .ClassicEarlyFade => .classicEarlyFade⟩
instance : AbsTo sim.mods.PolicyKind OsuModel.Sim.PolicyKind :=
  ⟨fun | .StartTimeOrdered => .startTimeOrdered | .Legacy r => .legacy r⟩
instance : AbsTo sim.mods.AccChallenge (F64 × Bool) := ⟨fun a => (a.min_acc, a.standard)⟩
/-- `Config`; the spec's debugging fields (`traceObj`, `dbgNoPresence`) and the unread `mods` list keep their
defaults (simtest's non-debug runs). -/
def configS (c : sim.mods.Config) : OsuModel.Sim.Config :=
  { policy := abs c.policy, classicHeadBlock := c.classic_head_block, legacyHealth := c.legacy_health
    failOverrides := abs c.fail_overrides, easyRetries := abs c.easy_retries, failConds := abs c.fail_conds
    accChallenges := abs c.acc_challenges, rankAdjust := c.rank_adjust, rateSources := abs c.rate_sources
    dynRates := abs c.dyn_rates, scoreMultiplier := c.score_multiplier, updatables := abs c.updatables
    inputBlockers := abs c.input_blockers, spunOut := c.spun_out, strictTracking := c.strict_tracking
    lazerReplay := c.lazer_replay, rateMods := abs c.rate_mods, visMods := abs c.vis_mods, depthMax := c.depth_max
    magnetStrength := c.magnet_strength, repelStrength := c.repel_strength, barrelRoll := c.barrel_roll }
instance : AbsTo sim.mods.Config OsuModel.Sim.Config := ⟨configS⟩

end OsuProofs
