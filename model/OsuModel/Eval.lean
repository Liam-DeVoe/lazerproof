import OsuModel.Beatmap
import OsuModel.Replay.Osr
import OsuModel.Replay.Frames
import OsuModel.Sim.Step
import OsuModel.Eval.Adapter
import OsuModel.Eval.Env

/-!
# End-to-end model: `.osu` bytes + `.osr` bytes (+ mod override) + schedule → result

```
evaluate env beatmapBytes osrBytes opts schedule
  = beatmap decode            (OsuModel.Beatmap, LegacyBeatmapDecoder)
    .osr decode               (OsuModel.Replay.Osr, LegacyScoreDecoder.Parse; LZMA = trusted)
    decode-time playable      (LegacyScoreDecoder.cs:94, only its failure matters)
    mod resolution            (oracle ResolveMods: --replace-mods / --no-classic / --mods; Player DeepClone)
    gameplay playable         (WorkingBeatmap.GetPlayableBeatmap with the gameplay mods) → adapter → Sim.Playable
    frames                    (OsuModel.Replay.decode, beatmap version offset)
    schedule + simulation     (OsuModel.Sim: Config.ofMods, steps, Sim.run)
```

Every lazer failure on the way (exceptions in decoding, unsupported inputs, non-reproducible mods) makes the model
**reject** the input with a stage and a reason (ISSUES.md G12, docs/model-eval.md "Rejections").
-/

namespace OsuModel.Eval
open OsuModel.Net OsuModel.Sim OsuModel.Replay
open OsuModel.Beatmap (ModConfig DecodedBeatmap PlayableBeatmap)

/-- The step schedule (D9): a reference schedule kind or an explicit reference-time list
(oracle `--schedule explicit:FILE`: one reference per entry, non-empty, non-decreasing, finite (`explicitRefsCheck`);
stops after the last). -/
inductive Schedule where
  | kind (k : ScheduleKind)
  | explicit (refs : Array F64)
deriving Inhabited

def Schedule.name : Schedule → String
  | .kind .catchup => "catchup" | .kind .perframe => "perframe" | .kind .dense1ms => "dense1ms"
  | .explicit _ => "explicit"

/-- Oracle-like mod options (`oracle/Program.cs` `ResolveMods`). -/
structure Options where
  /-- `--mods`: APIMods (already `ToMod`-decoded); each replaces a decoded mod with the same acronym, else appended -/
  modsOverride : Option (List ModConfig) := none
  /-- `--replace-mods`: the override replaces the decoded list entirely (only if an override is given) -/
  replaceMods : Bool := false
  /-- `--no-classic`: drop every `ModClassic` -/
  noClassic : Bool := false
deriving Inhabited

structure Rejection where
  stage : String
  reason : String
deriving Inhabited, Repr

/-- Per fail semantics (`live` = Player, `replay_player` = ReplayPlayer). -/
structure SemResult where
  score : ScoreSt
  health : HealthSt
deriving Inhabited

structure Result where
  isLegacyScore : Bool
  replayVersion : Int32
  replayBeatmapHash : Option String
  decodedMods : List ModConfig
  mods : List ModConfig
  trueGameplayRate : F64
  hitObjects : Nat
  frames : Nat
  scheduleName : String
  r0 : F64
  endTime : F64
  gameplayStartTime : F64
  lastFrameTime : Option F64
  references : Nat
  steps : Nat
  stepTimes : Array F64
  live : SemResult
  /-- `none`: identical to live (the health processor never attempted to fail; as the oracle reports it) -/
  replayPlayer : Option SemResult
  maxStats : Array Nat
  /-- processor-order judgements (health/failed: live semantics) -/
  judgements : Array JRec
  scoreMultiplier : F64
  playable : OsuModel.Sim.Playable
deriving Inhabited

abbrev EvalM := Except Rejection

def reject {α} (stage reason : String) : EvalM α := throw { stage, reason }
def liftE {α ε} [ToString ε] (stage : String) : Except ε α → EvalM α
  | .ok v => pure v
  | .error e => reject stage (toString e)

instance : ToString NetExn := ⟨fun e => reprStr e⟩

/-- Structural equality of decoded mod lists (acronym, known flag, settings). -/
def sameMods (a b : List ModConfig) : Bool :=
  a.length == b.length && (a.zip b).all fun (x, y) =>
    x.acronym == y.acronym && x.known == y.known && x.settings.size == y.settings.size &&
    (x.settings.zip y.settings).all fun (p, q) => p.1 == q.1 && p.2 == q.2

/-- Random / Target Practice without a seed: lazer draws a seed from `RNG.Next()`; not reproducible (ISSUES G5). -/
def unseededRandom (m : ModConfig) : Bool :=
  m.known && (m.acronym == "RD" || m.acronym == "TP") && (m.getOptInt "seed").isNone

/-- `ResolveMods` (`oracle/Program.cs:194-219`), then the Autoplay check (`:234-235`). -/
def resolveMods (decoded : List ModConfig) (o : Options) : EvalM (List ModConfig) := do
  let mut mods := if o.replaceMods && o.modsOverride.isSome then [] else decoded
  if o.noClassic then mods := mods.filter fun m => !(m.known && m.acronym == "CL")
  if let some ov := o.modsOverride then
    for m in ov do
      if !m.known then reject "mods" s!"unknown mod acronym: {m.acronym}"
      mods := mods.filter (·.acronym != m.acronym) ++ [m]
  -- `m is ModAutoplay` (OsuModAutoplay, OsuModCinema)
  if mods.any fun m => m.known && (m.acronym == "AT" || m.acronym == "CN") then
    reject "mods" "autoplay-type mods are not supported (they replace the replay)"
  return mods

def playableOf (d : DecodedBeatmap) (mods : List ModConfig) : Except String PlayableBeatmap :=
  OsuModel.Beatmap.getPlayableBeatmap d (mods.map ModConfig.allHooks)

/-- The explicit-schedule input contract (D80b, D79 N2): the oracle rejects an empty or decreasing list
(`ScheduleSpec.Parse`, `oracle/Schedule.cs:55,58`); a non-finite reference is rejected too (a `+∞` reference drives
the FSC past the last replay frame, a NaN one never reaches its reference). `r - r == 0` holds exactly for finite
`r` (IEEE 754: `∞ - ∞` and NaN operands give NaN). `prev` starts at `-∞`, below every finite reference. -/
def explicitRefsScan : List F64 → F64 → Except String Unit
  | [], _ => pure ()
  | r :: rs, prev =>
    if !(r - r == 0) then throw "explicit schedule: a reference time is not finite"
    else if r < prev then throw "explicit schedule must be non-decreasing"
    else explicitRefsScan rs r

def explicitRefsCheck (refs : Array F64) : Except String Unit :=
  if refs.size == 0 then throw "explicit schedule is empty" else explicitRefsScan refs.toList F64.negInf

/-- Every step's replay-frame index lies in `[-1, frames.size)` (D79 N2). `simulateSteps` moves the index to
`frames.size` only for a proposed FSC time of `+∞`; the simulation would then read past the last frame
(`replayPosition`: an `internal:` rejection at stage "sim"), so this check (also stage "sim") only names that
rejection earlier. It makes the frame-index range a checked fact instead of an assumption. -/
def stepFramesOk (steps : Array Step) (nFrames : Nat) : Bool :=
  steps.all fun st => decide (-1 ≤ st.frameIndex) && decide (st.frameIndex < (nFrames : Int))

/-- The end-to-end evaluation. -/
def evaluate (env : Env) (beatmap osr : ByteArray) (opts : Options) (sched : Schedule)
    (playableOverride : Option OsuModel.Sim.Playable := none) : EvalM Result := do
  -- beatmap (`Decoder.GetDecoder<Beatmap>(LineBufferedReader).Decode`; oracle `Decode`)
  let d ← liftE "beatmap-decode" (OsuModel.Beatmap.LegacyBeatmapDecoder.decode beatmap)
  if d.rulesetId != 0 then
    reject "beatmap-decode" s!"beatmap ruleset {d.rulesetId}: conversion of non-osu! beatmaps is not modelled"
  -- replay container, payloads, lazer score info
  let sc ← liftE "replay-decode" (Osr.decode osr)
  -- decode-time `GetPlayableBeatmap(ruleset, bitfield mods (+ Classic))` (LegacyScoreDecoder.cs:94): only its
  -- failure is observable. Unseeded RD/TP are dropped here (their decode-time run is non-reproducible and can
  -- only matter by throwing).
  let decodeTimeMods := sc.bitfieldMods.filter (!unseededRandom ·)
  let mods ← resolveMods sc.mods opts
  if !(sameMods decodeTimeMods mods) then
    let _ ← liftE "replay-decode (decode-time GetPlayableBeatmap)" (playableOf d decodeTimeMods)
  -- gameplay playable (`Player`: `gameplayMods = Mods.Select(m => m.DeepClone())`, `GetPlayableBeatmap`)
  if let some m := mods.find? unseededRandom then
    reject "playable" s!"{m.acronym} without a seed is not reproducible (lazer uses RNG.Next(); ISSUES G5)"
  let pb ← liftE "playable" (playableOf d mods)
  -- (`playableOverride`: debugging/localisation only — e.g. the oracle's `--dump-playable`, to separate adapter
  -- from simulation differences within one binary)
  let spb := playableOverride.getD (toSimPlayable pb)
  -- frames (`readLegacyReplay`, offset from the decode-time playable's `BeatmapVersion` = the beatmap's)
  let frames ← match sc.frameText with
    | some t => liftE "replay-frames" (OsuModel.Replay.decode t spb.beatmapVersion)
    | none => pure #[]
  let cfg := { Config.ofMods mods spb with lazerReplay := !sc.isLegacyScore }
  let ft := frames.map (·.time)
  let gst := gameplayStartTime spb
  let r0 := referenceStart spb
  let endT := referenceEnd spb
  -- simulation rejections (malformed input, or a computation lazer itself would throw on) → stage "sim"
  let (refsN, c) ← match sched with
    | .kind k => do pure ((← liftE "sim" (references k r0 endT ft)).size, ← liftE "sim" (mkCtx env cfg spb frames k))
    | .explicit refs => do
      liftE "sim" (explicitRefsCheck refs)
      let c0 ← liftE "sim" (mkCtx env cfg spb frames .catchup)
      pure (refs.size, { c0 with steps := ← liftE "sim" (simulateSteps refs ft gst) })
  if !stepFramesOk c.steps c.frames.size then
    reject "sim" "schedule: a step's replay frame index passes the last frame (an FSC time of +inf)"
  let s ← liftE "sim" (runWith c cfg spb)
  let rate ← liftE "sim" (do cfg.trueRate (← netStr (cfg.dynRates.mapM (·.initialSpeed))))
  let sem (sc : ScoreSt) (h : HealthSt) : SemResult := { score := sc, health := h }
  return {
    isLegacyScore := sc.isLegacyScore, replayVersion := sc.container.version
    replayBeatmapHash := sc.container.beatmapHash
    decodedMods := sc.mods, mods
    trueGameplayRate := rate
    hitObjects := spb.objects.size, frames := frames.size
    scheduleName := sched.name, r0, endTime := endT, gameplayStartTime := gst
    lastFrameTime := c.lastFrameTime, references := refsN, steps := c.steps.size
    stepTimes := c.steps.map (·.time)
    live := sem s.score s.health
    replayPlayer := if s.health.failTriggers == 0 then none else some (sem s.scoreRP s.healthRP)
    maxStats := c.smax.maxStats, judgements := s.out, scoreMultiplier := cfg.scoreMultiplier
    playable := spb }

/-- Only the adapter output (for the losslessness check against `oracle --dump-playable`). -/
def playableFor (beatmap osr : ByteArray) (opts : Options) : EvalM OsuModel.Sim.Playable := do
  let d ← liftE "beatmap-decode" (OsuModel.Beatmap.LegacyBeatmapDecoder.decode beatmap)
  let sc ← liftE "replay-decode" (Osr.decode osr)
  let mods ← resolveMods sc.mods opts
  return toSimPlayable (← liftE "playable" (playableOf d mods))

end OsuModel.Eval
