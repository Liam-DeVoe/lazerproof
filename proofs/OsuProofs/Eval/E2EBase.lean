/-
Definitions of the end-to-end refinement (top-level theorem: Eval/EndToEnd.lean; DECISIONS D35).

`OsuImpl.eval.evaluate` (the Aeneas translation of `impl/osu_eval_core/src/eval/mod.rs` `evaluate`: `.osu` bytes +
`.osr` bytes + options + schedule → result or rejection) refines the spec `OsuModel.Eval.evaluate`
(model/OsuModel/Eval.lean, with `playableOverride = none`):

  `eval.evaluate_refines : EvalAssumptions → … → ∃ r, eval.evaluate env bm osr opts sched = ok r ∧
     ev_topRel r (OsuModel.Eval.evaluate (abs env) (bytesS bm) (bytesS osr) (ev_optsS opts) (ev_schedS sched))`

`ev_topRel`: an `Ok` result equals the spec result field by field (`ev_resS`; the spec's `playable` field, which
the Rust result does not carry, is taken from the spec side), a rejection has the same stage
(`ev_stageS`; reasons are informational, as for the beatmap/sim layers: D33/D34).

OPEN OBLIGATIONS: everything the proof needs from other slices is collected in the structure
`EvalAssumptions` below (one field per callee, each a `_refines`-shaped statement). They are NOT axioms: the
theorem is stated with `EvalAssumptions` as a hypothesis, so `#print axioms` stays standard and the remaining
obligations are visible here. When a field is proved elsewhere, its proof can be plugged in.
-/
import OsuProofs.Eval.ModsJson
import OsuProofs.Auto.Base
import OsuProofs.Sim.AbsState
import OsuProofs.Beatmap.Decoder3
import OsuProofs.Post.Playable3
import OsuProofs.Sim.CtxWF
import OsuProofs.Sim.StepInv
import OsuProofs.Eval.E2Cong
import OsuModel.Eval
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

/-! ## Representation -/

/-- `eval::adapter::text::type_name` (the shell's type-name table of the `type_id`s of the adapter). -/
def ev_tn (t : Nat) : String :=
  match t with
  | 1 => "HitCircle" | 2 => "Slider" | 3 => "StrictTrackingSlider" | 4 => "Spinner" | 5 => "SliderHeadCircle"
  | 6 => "SliderTick" | 7 => "SliderRepeat" | 8 => "SliderTailCircle" | 9 => "StrictTrackingSliderTailCircle"
  | 10 => "SpinnerTick" | 11 => "SpinnerBonusTick" | _ => ""

def ev_kindS : sim.schedule.ScheduleKind → OsuModel.Sim.ScheduleKind
  | .Catchup => .catchup | .Perframe => .perframe | .Dense1ms => .dense1ms

def ev_schedS : eval.Schedule → OsuModel.Eval.Schedule
  | .Kind k => .kind (ev_kindS k)
  | .Explicit refs => .explicit refs.val.toArray

def ev_optsS (o : eval.Options) : OsuModel.Eval.Options :=
  { modsOverride := o.mods_override.map (·.val.map mcS), replaceMods := o.replace_mods, noClassic := o.no_classic }

/-- `eval::text::stage` -/
def ev_stageS : eval.Stage → String
  | .BeatmapDecode => "beatmap-decode" | .ReplayDecode => "replay-decode"
  | .DecodeTimePlayable => "replay-decode (decode-time GetPlayableBeatmap)" | .Mods => "mods"
  | .Playable => "playable" | .ReplayFrames => "replay-frames" | .Sim => "sim"

def ev_semS (x : eval.SemResult) : OsuModel.Eval.SemResult := { score := scoreS x.score, health := abs x.health }

def ev_schedName : Option sim.schedule.ScheduleKind → String
  | some k => (OsuModel.Eval.Schedule.kind (ev_kindS k)).name
  | none => "explicit"

/-- The Rust result with the spec's `playable` field `pl` (the only field the Rust result does not carry). -/
def ev_resS (r : eval.EvalResult) (pl : OsuModel.Sim.Playable) : OsuModel.Eval.Result :=
  { isLegacyScore := r.is_legacy_score, replayVersion := i32S r.replay_version
    replayBeatmapHash := r.replay_beatmap_hash.map vstrS
    decodedMods := r.decoded_mods.val.map mcS, mods := r.mods.val.map mcS
    trueGameplayRate := r.true_gameplay_rate, hitObjects := r.hit_objects.val, frames := r.frames.val
    scheduleName := ev_schedName r.schedule_kind, r0 := r.r0, endTime := r.end_time
    gameplayStartTime := r.gameplay_start_time, lastFrameTime := r.last_frame_time
    references := r.references.val, steps := r.steps.val, stepTimes := r.step_times.val.toArray
    live := ev_semS r.live, replayPlayer := r.replay_player.map ev_semS, maxStats := statsS r.max_stats
    judgements := (r.judgements.val.map (jrecS ev_tn)).toArray, scoreMultiplier := r.score_multiplier
    playable := pl }

/-- Rust `Result<EvalResult, Rejection>` vs the spec's `Except Rejection Result`. -/
def ev_topRel : core.result.Result eval.EvalResult eval.Rejection →
    Except OsuModel.Eval.Rejection OsuModel.Eval.Result → Prop
  | .Ok r, .ok R => R = ev_resS r R.playable
  | .Err e, .error E => E.stage = ev_stageS e.stage
  | _, _ => False

/-- A rejection-level relation for the intermediate steps of `evaluate`. -/
def ev_rjRel {α β} (f : α → β) : core.result.Result α eval.Rejection → Except OsuModel.Eval.Rejection β → Prop
  | .Ok a, .ok b => f a = b
  | .Err e, .error E => E.stage = ev_stageS e.stage
  | _, _ => False

/-- Callee results: equal values, or both errors (messages informational). -/
def ev_eRel {α β ε ε'} (f : α → β) : core.result.Result α ε → Except ε' β → Prop
  | .Ok a, .ok b => f a = b
  | .Err _, .error _ => True
  | _, _ => False

/-- well-formed decoded mod config (what the mod-settings refinements need: D26) -/
def ev_mcOk (m : beatmap.mod_settings.ModConfig) : Prop :=
  VValid m.acronym ∧ m.acronym.val.length < 2^62 ∧ KeysOk m.settings.val

/-- well-formed Rust `Config`: every dynamic rate source indexes `dyn_rates` (as built by `config_of_mods`) -/
def ev_cfgWF (c : sim.mods.Config) : Prop :=
  ∀ s ∈ c.rate_sources.val, ∀ k, s.val = .Dyn k → k.val < c.dyn_rates.val.length

/-- Rust `Config` vs a spec `Config`: equal up to the spec-only fields (`mods` acronym list, read by nothing;
debug fields `traceObj`/`dbgNoPresence`), which `configS` sets to their defaults. -/
def ev_cfgRel (c : sim.mods.Config) (C : OsuModel.Sim.Config) : Prop :=
  configS c = { C with mods := [], traceObj := none, dbgNoPresence := false }

/-- Rust `Ctx` vs spec `Ctx` (spec `Ctx.futureOrder` is `#[]` after `mkCtx`; config as `ev_cfgRel`). -/
def ev_ctxRel (c : sim.state.Ctx) (C : OsuModel.Sim.Ctx) : Prop :=
  ev_cfgRel c.cfg C.cfg ∧ simCtxS ev_tn (alloc.vec.Vec.new _) c = { C with cfg := configS c.cfg }

/-- `.osr` container (`LegacyScoreDecoder` fields kept by the model) -/
def ev_containerS (c : eval.osr.Container) : OsuModel.Replay.Osr.Container :=
  { rulesetId := UInt8.ofBitVec c.ruleset_id.bv, version := i32S c.version, beatmapHash := c.beatmap_hash.map vstrS
    legacyMods := i32S c.legacy_mods, compressedReplay := c.compressed_replay.map (fun v => bytesS v.slice)
    compressedScoreInfo := c.compressed_score_info.map (fun v => bytesS v.slice) }

def ev_dsS (d : eval.osr.DecodedScore) : OsuModel.Replay.Osr.DecodedScore :=
  { container := ev_containerS d.container, isLegacyScore := d.is_legacy_score
    bitfieldMods := d.bitfield_mods.val.map mcS, mods := d.mods.val.map mcS, frameText := d.frame_text.map vstrS }

/-- well-formedness of a decoded score (all mod configs `ev_mcOk`; the frame text a valid string) -/
def ev_dsOk (d : eval.osr.DecodedScore) : Prop :=
  (∀ m ∈ d.bitfield_mods.val, ev_mcOk m) ∧ (∀ m ∈ d.mods.val, ev_mcOk m) ∧ (∀ t, d.frame_text = some t → ev_VV t) ∧
    d.mods.val.length < 2^62

/-! ## Open obligations (other slices, and the parts of this slice not yet proved)

Each field is the `_refines` statement of one callee of `eval::evaluate`, in the representation above.
-/
/-! ## Trusted platform / input-size assumptions (docs/proof-pipeline.md "Trusted assumptions")

The slice theorems carry size hypotheses (Aeneas proves every `+`, `push` and index in range only under them). They are
collected here as ONE predicate on the two input files; the table in docs/proof-pipeline.md says where each comes from
and why it holds for every input lazer accepts. Fields are added as further slice theorems are plugged in. -/
structure InputBounds (bm osr : Slice U8) : Prop where
  /-- 64-bit platform (`usize` = `u64`; D28/D31/D36, slider_path, schedule) -/
  h64 : System.Platform.numBits = 64
  /-- `.osu` size (`beatmap.text.stream_reader_decode`, D36) -/
  bmLen : bm.val.length < Usize.max
  /-- decoded `.osu` text: fewer than 2^31 - 1 lines, every line shorter than some `N ≤ 2^61`, and `dec_pathOk N`
  (each line's slider control points < 2^32 and `SliderPath.calculatePath` < 2^62 points) (D36, D31 slider_path) -/
  decLines : ∃ N, N ≤ 2^61 ∧ dec_pathOk N ∧ ∀ cs, streamReaderDecode (bytesS bm) = some cs →
    (readLines cs).size + 1 < 2^31 ∧ ∀ L ∈ readLines cs, L.length < N
  /-- `.osr` size (this slice: positions and the decompressed/JSON texts stay below 2^62, D35) -/
  osrLen : osr.val.length < 2^62

/-- Spec-level size bounds of the playable pipeline for the decoded beatmap `d` and mod list `ms` (`LoadBounds`,
Post/Playable3.lean: decoded control-point / hit-object counts, slider paths, `GpbBounds`). -/
def ev_pbOk (d : beatmap.types.DecodedBeatmap) (ms : Slice beatmap.mod_settings.ModConfig) : Prop :=
  LoadBounds (dec_dbS d) ((ms.val.map mcS).map ModConfig.allHooks)

/-- Spec-level fact (Lean core vs the model's decoder; OPEN): a byte array that Lean's `String.fromUTF8?` accepts
decodes to the same characters under `decodeUtf8` (replacement decoding is the identity on well-formed UTF-8), and does
not start with `00 00 FE` (`FE` is never valid UTF-8). Used for the fast path of `readCompressedText`. -/
def ev_utf8Fact : Prop := ∀ (raw : ByteArray) (s : String), String.fromUTF8? raw = some s →
  s.toList = (OsuModel.Beatmap.decodeUtf8 raw 0).toList ∧ ¬ (3 ≤ raw.size ∧ raw[0]! = 0 ∧ raw[1]! = 0 ∧ raw[2]! = 0xFE)

/-- Trusted-boundary fact (OPEN): the liblzma shim never returns more than `maxOut` bytes (`osu_lzma_alone_decode`
caps the output buffer; docs/proof-pipeline.md §4). -/
def ev_lzmaBound : Prop := ∀ d m r, OsuModel.Replay.Osr.lzmaAloneDecode d m = .ok r → r.size ≤ m.toNat

/-- (this slice, OPEN) the lazer score-info JSON decoder `eval::osr::decode_score_info` refines `decodeScoreInfo` -/
def ev_scoreInfoOk : Prop := ∀ (text : Slice U32), ValidStr text → text.val.length < 2^62 →
  ∃ r, eval.osr.decode_score_info text = ok r ∧
    (match r, OsuModel.Replay.Osr.decodeScoreInfo (String.ofList (strS text)) with
     | .Ok ms, .ok MS => ms.val.map mcS = MS ∧ (∀ m ∈ ms.val, ev_mcOk m) ∧ ms.val.length < 2^62
     | .Err _, .error _ => True
     | _, _ => False)

theorem ev_i32S_zero : i32S 0#i32 = 0 := by decide

/-- the adapter's `strict_tail` flag is `type_id == 9` (`T_STRICT_TRACKING_SLIDER_TAIL_CIRCLE`) for every nested
object (derived: `js_strict_of`, Eval/JsonStrict.lean) -/
def ev_strictOk (pb : sim.playable.Playable) : Prop :=
  ∀ o ∈ pb.objects.val, ∀ n ∈ o.nested.val, n.strict_tail = (n.type_id.val == 9)

/-- size bounds `mk_ctx` needs of its playable / frames: frames < 2^32 (`steps`), objects < 2^32 (autogen),
objects + nested objects < 2^62 (health/score maxima, preceding end times), breaks < Usize.max (block periods),
slider cumulative-length / path arrays < 2^62 (autogen slider geometry). -/
def ev_mkBounds (pb : sim.playable.Playable) (fs : alloc.vec.Vec replay.frames.Frame) : Prop :=
  fs.val.length < 2^32 ∧ pb.objects.val.length < 2^32 ∧
  (pb.objects.val.map (fun o => o.nested.val.length + 1)).sum < 2^62 ∧
  pb.breaks.val.length < Usize.max ∧
  (∀ o ∈ pb.objects.val, ∀ sd, o.slider = some sd → sd.cum_len.val.length < 2^62 ∧ sd.path.val.length < 2^62) ∧
  ((∀ o ∈ pb.objects.val, o.nested.val.length < 2^32) ∧
   (∀ o ∈ pb.objects.val, o.h.kind = .Circle ∨ o.h.kind = .Slider ∨ o.h.kind = .Spinner) ∧
   (∀ ms G, OsuModel.Sim.AutoGen.generate (playableS ev_tn pb) ms = .ok G → G.size < 2^62) ∧
   ev_strictOk pb ∧ (∀ f ∈ fs.val, f.actions.len.val ≤ 3) ∧
   (∀ o ∈ pb.objects.val, o.h.kind ≠ .Spinner → ∀ n ∈ o.nested.val,
     n.kind ≠ .SpinnerTick ∧ n.kind ≠ .SpinnerBonusTick))

/-- spec-level `ev_mkBounds` (TRUSTED row `PlayableBounds.simCtx`, docs/proof-pipeline.md §5) -/
def ev_mkBoundsS (P : OsuModel.Sim.Playable) (FS : _root_.Array OsuModel.Replay.Frame) : Prop :=
  FS.size < 2^32 ∧ P.objects.size < 2^32 ∧ (P.objects.toList.map (fun o => o.nested.size + 1)).sum < 2^62 ∧
  P.breaks.size < 2^63 ∧
  (∀ o ∈ P.objects.toList, ∀ sd, o.slider = some sd → sd.cumLen.size < 2^62 ∧ sd.path.size < 2^62) ∧
  ((∀ o ∈ P.objects.toList, o.nested.size < 2^32) ∧
   (∀ o ∈ P.objects.toList, o.h.kind = .circle ∨ o.h.kind = .slider ∨ o.h.kind = .spinner) ∧
   (∀ ms G, OsuModel.Sim.AutoGen.generate P ms = .ok G → G.size < 2^62) ∧
   (∀ o ∈ P.objects.toList, o.h.kind ≠ .spinner → ∀ n ∈ o.nested.toList,
     n.kind ≠ .spinnerTick ∧ n.kind ≠ .spinnerBonusTick))

theorem ev_mkBounds_of (h64 : System.Platform.numBits = 64) (spb : sim.playable.Playable)
    (fs : alloc.vec.Vec replay.frames.Frame)
    (h : ev_mkBoundsS (playableS ev_tn spb) (fs.val.map abs).toArray) (hst : ev_strictOk spb)
    (hac : ∀ f ∈ fs.val, f.actions.len.val ≤ 3) : ev_mkBounds spb fs := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hU := usize_max_64 h64
  refine ⟨by simpa using h1, by simpa [playableS] using h2, ?_, ?_, ?_, ?_, ?_, h8, hst, hac, ?_⟩
  · simpa [playableS, topS, List.map_map, Function.comp_def] using h3
  · have : (abs spb.breaks : _root_.Array (F64 × F64)).size = spb.breaks.val.length := by simp [abs]
    simp only [playableS, this] at h4; omega
  · intro o ho sd hsd
    have := h5 (topS ev_tn o) (by simp [playableS]; exact ⟨o, ho, rfl⟩) (abs sd) (by simp [topS, hsd])
    simpa [abs] using this
  · intro o ho
    have := h6 (topS ev_tn o) (by simp [playableS]; exact ⟨o, ho, rfl⟩)
    simpa [topS] using this
  · intro o ho
    have := h7 (topS ev_tn o) (by simp [playableS]; exact ⟨o, ho, rfl⟩)
    simp only [topS, hobjS] at this
    cases hk : o.h.kind <;> simp_all [kindS]
  · intro o ho hs n hn
    have := h9 (topS ev_tn o) (by simp [playableS]; exact ⟨o, ho, rfl⟩)
      (by simp only [topS, hobjS]; cases hk : o.h.kind <;> simp_all [kindS])
      (hobjS ev_tn n) (by simp [topS]; exact ⟨n, hn, rfl⟩)
    simp only [hobjS] at this
    cases hk : n.kind <;> simp_all [kindS]

/-- (D77, part of the RunBudget row) judgement slots × (1 + 2·#accuracy challenges) fit a `u64`: the Rust
`fail_triggers` counter gets up to `1 + 2·#AC` increments per judgement (sim9's initial lifetime invariant) -/
def e2AccBudS (CTX : OsuModel.Sim.Ctx) : Prop :=
  (CTX.pb.objects.toList.map (fun o => o.nested.size + 1)).sum * (1 + 2 * CTX.cfg.accChallenges.size) ≤ 2 ^ 64 - 1

structure EvalAssumptions : Prop where
  /-- (beatmap slice) `playable::get_playable_beatmap` refines `getPlayableBeatmap` (via `Eval.playableOf`) -/
  playable : ∀ (d : beatmap.types.DecodedBeatmap) (ms : Slice beatmap.mod_settings.ModConfig),
    (∀ m ∈ ms.val, ev_mcOk m) → ev_pbOk d ms → ∃ r, beatmap.playable.get_playable_beatmap d ms = ok r ∧
    ev_eRel abs r (OsuModel.Eval.playableOf (dec_dbS d) (ms.val.map mcS))
  /-- (replay slice) `replay::frames::decode` refines `OsuModel.Replay.decode` -/
  frames : ∀ (t : Slice U32) (v : I64), ValidStr t → t.val.length < 2^62 → ∃ r, replay.frames.decode t v = ok r ∧
    ev_eRel (fun fs => (fs.val.map abs).toArray) r (OsuModel.Replay.decode (String.ofList (strS t)) v.val) ∧
    ∀ fs, r = .Ok fs → fs.val.length ≤ t.val.length ∧ ∀ f ∈ fs.val, f.actions.len.val ≤ 3
  /-- (sim slice) `mods::config_of_mods` refines `Config.ofMods` (+ `lazerReplay`); `ev_cfgWF`: the dynamic rate
  sources index `dyn_rates` -/
  config : ∀ (ms : Slice beatmap.mod_settings.ModConfig) (pb : sim.playable.Playable) (lr : Bool),
    (∀ m ∈ ms.val, ev_mcOk m) → ms.val.length < 2^62 + 2^61 → ∃ c, sim.mods.config_of_mods ms pb lr = ok c ∧
    ev_cfgRel c { OsuModel.Sim.Config.ofMods (ms.val.map mcS) (playableS ev_tn pb) with lazerReplay := lr } ∧ ev_cfgWF c
  /-- (sim slice) schedule leaves -/
  gst : ∀ pb, ∃ x, sim.schedule.gameplay_start_time pb = ok x ∧ OsuModel.Sim.gameplayStartTime (playableS ev_tn pb) = x
  r0 : ∀ pb, ∃ x, sim.schedule.reference_start pb = ok x ∧ OsuModel.Sim.referenceStart (playableS ev_tn pb) = x
  endT : ∀ pb, ∃ x, sim.schedule.reference_end pb = ok x ∧ OsuModel.Sim.referenceEnd (playableS ev_tn pb) = x
  frameTimes : ∀ fs : Slice replay.frames.Frame, ∃ r, sim.schedule.frame_times fs = ok r ∧
    ((fs.val.map abs).toArray : Array OsuModel.Replay.Frame).map (·.time) = r.val.toArray
  references : ∀ k r0 e (ft : Slice F64), ft.val.length + 2 ≤ Usize.max → ∃ r, sim.schedule.references k r0 e ft = ok r ∧
    ev_eRel (fun v => v.val.toArray) r (OsuModel.Sim.references (ev_kindS k) r0 e ft.val.toArray)
  simulateSteps : ∀ (refs ft : Slice F64) gst, refs.val.length * 100000000 + 4 < 2^61 →
    ∃ r, sim.schedule.simulate_steps refs ft gst = ok r ∧
    ev_eRel (fun v => (v.val.map abs).toArray) r (OsuModel.Sim.simulateSteps refs.val.toArray ft.val.toArray gst)
  /-- (sim slice) `step::mk_ctx` refines `mkCtx`, for every spec config related to the Rust one -/
  mkCtx : ∀ env (c : sim.mods.Config) pb (fs : alloc.vec.Vec replay.frames.Frame) k (C : OsuModel.Sim.Config),
    ev_cfgRel c C → ev_mkBounds pb fs → ∃ r, sim.step.mk_ctx env c pb fs k = ok r ∧
    (match r, OsuModel.Sim.mkCtx (abs env) C (playableS ev_tn pb) (fs.val.map abs).toArray (ev_kindS k) with
     | .Ok ctx, .ok CTX => ctx.cfg = c ∧ CTX.cfg = C ∧ ctx.pb = pb ∧ CTX.pb = playableS ev_tn pb ∧ ev_ctxRel ctx CTX
     | .Err _, .error _ => True
     | _, _ => False) ∧
    ∀ ctx, r = .Ok ctx → ev_ctxWF ctx
  /-- (sim slice) `step::run_with` refines `runWith` -/
  runWith : ∀ (ctx : sim.state.Ctx) (CTX : OsuModel.Sim.Ctx), ev_ctxRel ctx CTX → ev_ctxWF ctx →
    CTX.cfg.traceObj = none → CTX.cfg.dbgNoPresence = false → e2CfgIdx CTX.cfg →
    (∀ st ∈ ctx.steps.val, -1 ≤ st.frame_index.val ∧ st.frame_index.val < (ctx.frames.val.length : Int)) →
    (∀ S0, OsuModel.Sim.initState CTX.cfg CTX.pb CTX.smax.initWithoutMods = .ok S0 → RunBudgetS CTX S0) → e2AccBudS CTX →
    ∃ r, sim.step.run_with ctx = ok r ∧ ev_eRel (simStS ev_tn) r (OsuModel.Sim.runWith CTX CTX.cfg CTX.pb)
  /-- (sim slice) `DynRate.initialSpeed` -/
  dynInit : ∀ d, ∃ r, sim.mods.dyn_rate_initial_speed d = ok r ∧ ev_eRel id r (abs d : OsuModel.Sim.DynRate).initialSpeed
  /-- (sim slice) `Config.trueRate` (the Rust is total; the spec's out-of-range error is unreachable for configs
  built by `config_of_mods`, here: `ev_cfgRel` + speeds for every dynamic rate) -/
  trueRate : ∀ (c : sim.mods.Config) (sp : Slice F64) (C : OsuModel.Sim.Config), ev_cfgRel c C → ev_cfgWF c →
    sp.val.length = c.dyn_rates.val.length → ∃ x, sim.mods.true_rate c sp = ok x ∧ C.trueRate sp.val.toArray = .ok x
  /-- (Lean core vs model, OPEN) `ev_utf8Fact` -/
  utf8 : ev_utf8Fact
  /-- (trusted LZMA boundary) `ev_lzmaBound` -/
  lzmaBound : ev_lzmaBound
  /-- (this slice, OPEN) `ev_scoreInfoOk` -/
  scoreInfo : ev_scoreInfoOk

/-! ## The spec `evaluate`, staged (same computation, one `match` per stage; `ev_specEval_eq`) -/
section Staged
open OsuModel.Eval OsuModel.Sim OsuModel.Replay

def evS_beatmap (B : ByteArray) : EvalM OsuModel.Beatmap.DecodedBeatmap :=
  match liftE "beatmap-decode" (OsuModel.Beatmap.LegacyBeatmapDecoder.decode B) with
  | .error e => .error e
  | .ok d => if d.rulesetId != 0 then
      reject "beatmap-decode" s!"beatmap ruleset {d.rulesetId}: conversion of non-osu! beatmaps is not modelled"
    else .ok d

def evS_dtCheck (d : OsuModel.Beatmap.DecodedBeatmap) (dtm mods : List ModConfig) : EvalM Unit :=
  if !(sameMods dtm mods) then
    match liftE "replay-decode (decode-time GetPlayableBeatmap)" (playableOf d dtm) with
    | .error e => .error e
    | .ok _ => .ok ()
  else .ok ()

def evS_gameplay (d : OsuModel.Beatmap.DecodedBeatmap) (mods : List ModConfig) : EvalM PlayableBeatmap :=
  match mods.find? unseededRandom with
  | some m => reject "playable" s!"{m.acronym} without a seed is not reproducible (lazer uses RNG.Next(); ISSUES G5)"
  | none => liftE "playable" (playableOf d mods)

def evS_frames (text : Option String) (v : Int) : EvalM (Array Frame) :=
  match text with
  | some t => liftE "replay-frames" (OsuModel.Replay.decode t v)
  | none => .ok #[]

def evS_sched0 (env : Env) (cfg : Config) (spb : OsuModel.Sim.Playable) (frames : Array Frame) :
    OsuModel.Eval.Schedule → EvalM (Nat × Ctx)
  | .kind k =>
    match liftE "sim" (references k (referenceStart spb) (referenceEnd spb) (frames.map (·.time))) with
    | .error e => .error e
    | .ok rs => match liftE "sim" (mkCtx env cfg spb frames k) with
      | .error e => .error e
      | .ok c => .ok (rs.size, c)
  | .explicit refs =>
    match liftE "sim" (explicitRefsCheck refs) with
    | .error e => .error e
    | .ok _ => match liftE "sim" (mkCtx env cfg spb frames .catchup) with
      | .error e => .error e
      | .ok c0 => match liftE "sim" (simulateSteps refs (frames.map (·.time)) (gameplayStartTime spb)) with
        | .error e => .error e
        | .ok st => .ok (refs.size, { c0 with steps := st })

/-- the schedule stage: `evS_sched0`, then the `stepFramesOk` check (D72) -/
def evS_sched (env : Env) (cfg : Config) (spb : OsuModel.Sim.Playable) (frames : Array Frame)
    (sched : OsuModel.Eval.Schedule) : EvalM (Nat × Ctx) :=
  match evS_sched0 env cfg spb frames sched with
  | .error e => .error e
  | .ok (n, c) => if !stepFramesOk c.steps c.frames.size then
      reject "sim" "schedule: a step's replay frame index passes the last frame (an FSC time of +inf)"
    else .ok (n, c)

def evS_rate (cfg : Config) : EvalM F64 :=
  liftE "sim" (do cfg.trueRate (← netStr (cfg.dynRates.mapM (·.initialSpeed))))

/-- TRUSTED input-size assumptions of the playable pipeline (docs/proof-pipeline.md §5, rows `PlayableBounds.*`).
The decoded control-point / hit-object counts of `LoadBounds` are NOT assumed: they follow from `InputBounds.decLines`
(Eval/JsonDecSize.lean). Assumed: the slider paths of the decoded beatmap (`LoadBounds.sl`) and the pipeline bounds
`GpbBounds` for the decode-time and the resolved gameplay mod lists, and the simulation-context sizes `ev_mkBoundsS`. -/
structure PlayableBounds (bm osr : Slice U8) (opts : eval.Options) : Prop where
  sliderPaths : ∀ D, LegacyBeatmapDecoder.decode (bytesS bm) = .ok D → ∀ o ∈ D.hitObjects, ∀ cps dd r,
    o.kind = .slider cps dd r → cps.size < 2^32 ∧
    (SliderPath.calculatePath { controlPoints := cps, expectedDistance := dd, optimiseCatmull := true }).1.size < 2^62
  decodeTime : ∀ D SC, LegacyBeatmapDecoder.decode (bytesS bm) = .ok D →
    OsuModel.Replay.Osr.decode (bytesS osr) = .ok SC →
    GpbBounds D ((SC.bitfieldMods.filter (!OsuModel.Eval.unseededRandom ·)).map ModConfig.allHooks)
  gameplay : ∀ D SC M, LegacyBeatmapDecoder.decode (bytesS bm) = .ok D →
    OsuModel.Replay.Osr.decode (bytesS osr) = .ok SC → OsuModel.Eval.resolveMods SC.mods (ev_optsS opts) = .ok M →
    GpbBounds D (M.map ModConfig.allHooks)
  /-- the simulation context's sizes (`ev_mkBoundsS`) for the spec playable and replay frames -/
  simCtx : ∀ DB SC MODS PB FS, evS_beatmap (bytesS bm) = .ok DB → OsuModel.Replay.Osr.decode (bytesS osr) = .ok SC →
    OsuModel.Eval.resolveMods SC.mods (ev_optsS opts) = .ok MODS → evS_gameplay DB MODS = .ok PB →
    evS_frames SC.frameText (OsuModel.Eval.toSimPlayable PB).beatmapVersion = .ok FS →
    ev_mkBoundsS (OsuModel.Eval.toSimPlayable PB) FS

def ev_specEval (env : Env) (B O : ByteArray) (opts : OsuModel.Eval.Options) (sched : OsuModel.Eval.Schedule) :
    EvalM OsuModel.Eval.Result :=
  match evS_beatmap B with
  | .error e => .error e
  | .ok d =>
  match liftE "replay-decode" (Osr.decode O) with
  | .error e => .error e
  | .ok sc =>
  match resolveMods sc.mods opts with
  | .error e => .error e
  | .ok mods =>
  match evS_dtCheck d (sc.bitfieldMods.filter (!unseededRandom ·)) mods with
  | .error e => .error e
  | .ok _ =>
  match evS_gameplay d mods with
  | .error e => .error e
  | .ok pb =>
  match evS_frames sc.frameText (toSimPlayable pb).beatmapVersion with
  | .error e => .error e
  | .ok frames =>
  match evS_sched env { Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore }
      (toSimPlayable pb) frames sched with
  | .error e => .error e
  | .ok (refsN, c) =>
  match liftE "sim" (runWith c { Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore }
      (toSimPlayable pb)) with
  | .error e => .error e
  | .ok s =>
  match evS_rate { Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } with
  | .error e => .error e
  | .ok rate =>
  .ok {
    isLegacyScore := sc.isLegacyScore, replayVersion := sc.container.version
    replayBeatmapHash := sc.container.beatmapHash
    decodedMods := sc.mods, mods
    trueGameplayRate := rate
    hitObjects := (toSimPlayable pb).objects.size, frames := frames.size
    scheduleName := sched.name, r0 := referenceStart (toSimPlayable pb), endTime := referenceEnd (toSimPlayable pb)
    gameplayStartTime := gameplayStartTime (toSimPlayable pb)
    lastFrameTime := c.lastFrameTime, references := refsN, steps := c.steps.size
    stepTimes := c.steps.map (·.time)
    live := { score := s.score, health := s.health }
    replayPlayer := if s.health.failTriggers == 0 then none else some { score := s.scoreRP, health := s.healthRP }
    maxStats := c.smax.maxStats, judgements := s.out
    scoreMultiplier := ({ Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } : Config).scoreMultiplier
    playable := toSimPlayable pb }

theorem ev_specEval_eq (env : Env) (B O : ByteArray) (opts : OsuModel.Eval.Options) (sched : OsuModel.Eval.Schedule) :
    OsuModel.Eval.evaluate env B O opts sched = ev_specEval env B O opts sched := by
  unfold OsuModel.Eval.evaluate ev_specEval evS_beatmap evS_dtCheck evS_gameplay evS_frames evS_sched evS_sched0 evS_rate
  cases h1 : liftE "beatmap-decode" (OsuModel.Beatmap.LegacyBeatmapDecoder.decode B) with
  | error e => rfl
  | ok d =>
    by_cases hr : (d.rulesetId != 0) = true
    · simp only [hr, if_true, except_bind_ok, OsuModel.Eval.reject, except_throw, except_bind_error]
    · simp only [hr, except_bind_ok, Bool.false_eq_true, if_false]
      cases h2 : liftE "replay-decode" (OsuModel.Replay.Osr.decode O) with
      | error e => rfl
      | ok sc =>
        simp only [except_bind_ok]
        cases h3 : resolveMods sc.mods opts with
        | error e => rfl
        | ok mods =>
          simp only [except_bind_ok]
          by_cases hs : (!sameMods (List.filter (fun x => !unseededRandom x) sc.bitfieldMods) mods) = true
          · simp only [hs, if_true]
            cases h4 : liftE "replay-decode (decode-time GetPlayableBeatmap)"
                (playableOf d (List.filter (fun x => !unseededRandom x) sc.bitfieldMods))
            · rfl
            simp only [except_bind_ok]
            cases h5 : List.find? unseededRandom mods
            · simp only
              cases h6 : liftE "playable" (playableOf d mods)
              · rfl
              rename_i pb
              simp only [except_bind_ok, Option.getD_none]
              cases h7 : sc.frameText
              · simp only [pure, Except.pure, except_bind_ok]
                cases sched with
                | kind k =>
                  dsimp only
                  cases h9 : liftE "sim" (references k (referenceStart (toSimPlayable pb)) (referenceEnd (toSimPlayable pb)) (Array.map (fun x => x.time) (#[] : Array OsuModel.Replay.Frame)))
                  · rfl
                  rename_i rs
                  simp only [except_bind_ok]
                  cases h10 : liftE "sim" (mkCtx env { Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } (toSimPlayable pb) (#[] : Array OsuModel.Replay.Frame) k)
                  · rfl
                  rename_i c
                  simp only [except_bind_ok, pure, Except.pure]
                  by_cases hfo : (!stepFramesOk c.steps c.frames.size) = true
                  · simp only [hfo, if_true, OsuModel.Eval.reject, except_throw, except_bind_error]
                  simp only [hfo, Bool.false_eq_true, if_false, except_bind_ok]
                  cases h11 : liftE "sim" (runWith c { Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } (toSimPlayable pb)) with
                  | error e => rfl
                  | ok s =>
                    simp only [except_bind_ok]
                    cases h12 : liftE "sim" (do ({ Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } : Config).trueRate (← netStr (({ Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } : Config).dynRates.mapM (·.initialSpeed)))) with
                    | error e => rfl
                    | ok rate =>
                      simp only [except_bind_ok, Except.pure]
                | explicit refs =>
                  dsimp only
                  cases h8b : liftE "sim" (explicitRefsCheck refs)
                  · rfl
                  simp only [except_bind_ok]
                  cases h10 : liftE "sim" (mkCtx env { Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } (toSimPlayable pb) (#[] : Array OsuModel.Replay.Frame) .catchup)
                  · rfl
                  rename_i c0
                  simp only [except_bind_ok]
                  cases h9 : liftE "sim" (simulateSteps refs (Array.map (fun x => x.time) (#[] : Array OsuModel.Replay.Frame)) (gameplayStartTime (toSimPlayable pb)))
                  · rfl
                  rename_i st
                  simp only [except_bind_ok, pure, Except.pure]
                  by_cases hfo : (!stepFramesOk st c0.frames.size) = true
                  · simp only [hfo, if_true, OsuModel.Eval.reject, except_throw, except_bind_error]
                  simp only [hfo, Bool.false_eq_true, if_false, except_bind_ok]
                  cases h11 : liftE "sim" (runWith { c0 with steps := st } { Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } (toSimPlayable pb)) with
                  | error e => rfl
                  | ok s =>
                    simp only [except_bind_ok]
                    cases h12 : liftE "sim" (do ({ Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } : Config).trueRate (← netStr (({ Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } : Config).dynRates.mapM (·.initialSpeed)))) with
                    | error e => rfl
                    | ok rate =>
                      simp only [except_bind_ok, Except.pure]
              · rename_i t
                simp only
                cases h8 : liftE "replay-frames" (OsuModel.Replay.decode t (toSimPlayable pb).beatmapVersion)
                · rfl
                rename_i frames
                simp only [except_bind_ok]
                cases sched with
                | kind k =>
                  dsimp only
                  cases h9 : liftE "sim" (references k (referenceStart (toSimPlayable pb)) (referenceEnd (toSimPlayable pb)) (Array.map (fun x => x.time) frames))
                  · rfl
                  rename_i rs
                  simp only [except_bind_ok]
                  cases h10 : liftE "sim" (mkCtx env { Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } (toSimPlayable pb) frames k)
                  · rfl
                  rename_i c
                  simp only [except_bind_ok, pure, Except.pure]
                  by_cases hfo : (!stepFramesOk c.steps c.frames.size) = true
                  · simp only [hfo, if_true, OsuModel.Eval.reject, except_throw, except_bind_error]
                  simp only [hfo, Bool.false_eq_true, if_false, except_bind_ok]
                  cases h11 : liftE "sim" (runWith c { Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } (toSimPlayable pb)) with
                  | error e => rfl
                  | ok s =>
                    simp only [except_bind_ok]
                    cases h12 : liftE "sim" (do ({ Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } : Config).trueRate (← netStr (({ Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } : Config).dynRates.mapM (·.initialSpeed)))) with
                    | error e => rfl
                    | ok rate =>
                      simp only [except_bind_ok, Except.pure]
                | explicit refs =>
                  dsimp only
                  cases h8b : liftE "sim" (explicitRefsCheck refs)
                  · rfl
                  simp only [except_bind_ok]
                  cases h10 : liftE "sim" (mkCtx env { Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } (toSimPlayable pb) frames .catchup)
                  · rfl
                  rename_i c0
                  simp only [except_bind_ok]
                  cases h9 : liftE "sim" (simulateSteps refs (Array.map (fun x => x.time) frames) (gameplayStartTime (toSimPlayable pb)))
                  · rfl
                  rename_i st
                  simp only [except_bind_ok, pure, Except.pure]
                  by_cases hfo : (!stepFramesOk st c0.frames.size) = true
                  · simp only [hfo, if_true, OsuModel.Eval.reject, except_throw, except_bind_error]
                  simp only [hfo, Bool.false_eq_true, if_false, except_bind_ok]
                  cases h11 : liftE "sim" (runWith { c0 with steps := st } { Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } (toSimPlayable pb)) with
                  | error e => rfl
                  | ok s =>
                    simp only [except_bind_ok]
                    cases h12 : liftE "sim" (do ({ Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } : Config).trueRate (← netStr (({ Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } : Config).dynRates.mapM (·.initialSpeed)))) with
                    | error e => rfl
                    | ok rate =>
                      simp only [except_bind_ok, Except.pure]
            · simp only [OsuModel.Eval.reject, except_throw, except_bind_error]

          · simp only [hs, Bool.false_eq_true, if_false]
            cases h5 : List.find? unseededRandom mods
            · simp only
              cases h6 : liftE "playable" (playableOf d mods)
              · rfl
              rename_i pb
              simp only [except_bind_ok, Option.getD_none]
              cases h7 : sc.frameText
              · simp only [pure, Except.pure, except_bind_ok]
                cases sched with
                | kind k =>
                  dsimp only
                  cases h9 : liftE "sim" (references k (referenceStart (toSimPlayable pb)) (referenceEnd (toSimPlayable pb)) (Array.map (fun x => x.time) (#[] : Array OsuModel.Replay.Frame)))
                  · rfl
                  rename_i rs
                  simp only [except_bind_ok]
                  cases h10 : liftE "sim" (mkCtx env { Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } (toSimPlayable pb) (#[] : Array OsuModel.Replay.Frame) k)
                  · rfl
                  rename_i c
                  simp only [except_bind_ok, pure, Except.pure]
                  by_cases hfo : (!stepFramesOk c.steps c.frames.size) = true
                  · simp only [hfo, if_true, OsuModel.Eval.reject, except_throw, except_bind_error]
                  simp only [hfo, Bool.false_eq_true, if_false, except_bind_ok]
                  cases h11 : liftE "sim" (runWith c { Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } (toSimPlayable pb)) with
                  | error e => rfl
                  | ok s =>
                    simp only [except_bind_ok]
                    cases h12 : liftE "sim" (do ({ Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } : Config).trueRate (← netStr (({ Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } : Config).dynRates.mapM (·.initialSpeed)))) with
                    | error e => rfl
                    | ok rate =>
                      simp only [except_bind_ok, Except.pure]
                | explicit refs =>
                  dsimp only
                  cases h8b : liftE "sim" (explicitRefsCheck refs)
                  · rfl
                  simp only [except_bind_ok]
                  cases h10 : liftE "sim" (mkCtx env { Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } (toSimPlayable pb) (#[] : Array OsuModel.Replay.Frame) .catchup)
                  · rfl
                  rename_i c0
                  simp only [except_bind_ok]
                  cases h9 : liftE "sim" (simulateSteps refs (Array.map (fun x => x.time) (#[] : Array OsuModel.Replay.Frame)) (gameplayStartTime (toSimPlayable pb)))
                  · rfl
                  rename_i st
                  simp only [except_bind_ok, pure, Except.pure]
                  by_cases hfo : (!stepFramesOk st c0.frames.size) = true
                  · simp only [hfo, if_true, OsuModel.Eval.reject, except_throw, except_bind_error]
                  simp only [hfo, Bool.false_eq_true, if_false, except_bind_ok]
                  cases h11 : liftE "sim" (runWith { c0 with steps := st } { Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } (toSimPlayable pb)) with
                  | error e => rfl
                  | ok s =>
                    simp only [except_bind_ok]
                    cases h12 : liftE "sim" (do ({ Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } : Config).trueRate (← netStr (({ Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } : Config).dynRates.mapM (·.initialSpeed)))) with
                    | error e => rfl
                    | ok rate =>
                      simp only [except_bind_ok, Except.pure]
              · rename_i t
                simp only
                cases h8 : liftE "replay-frames" (OsuModel.Replay.decode t (toSimPlayable pb).beatmapVersion)
                · rfl
                rename_i frames
                simp only [except_bind_ok]
                cases sched with
                | kind k =>
                  dsimp only
                  cases h9 : liftE "sim" (references k (referenceStart (toSimPlayable pb)) (referenceEnd (toSimPlayable pb)) (Array.map (fun x => x.time) frames))
                  · rfl
                  rename_i rs
                  simp only [except_bind_ok]
                  cases h10 : liftE "sim" (mkCtx env { Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } (toSimPlayable pb) frames k)
                  · rfl
                  rename_i c
                  simp only [except_bind_ok, pure, Except.pure]
                  by_cases hfo : (!stepFramesOk c.steps c.frames.size) = true
                  · simp only [hfo, if_true, OsuModel.Eval.reject, except_throw, except_bind_error]
                  simp only [hfo, Bool.false_eq_true, if_false, except_bind_ok]
                  cases h11 : liftE "sim" (runWith c { Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } (toSimPlayable pb)) with
                  | error e => rfl
                  | ok s =>
                    simp only [except_bind_ok]
                    cases h12 : liftE "sim" (do ({ Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } : Config).trueRate (← netStr (({ Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } : Config).dynRates.mapM (·.initialSpeed)))) with
                    | error e => rfl
                    | ok rate =>
                      simp only [except_bind_ok, Except.pure]
                | explicit refs =>
                  dsimp only
                  cases h8b : liftE "sim" (explicitRefsCheck refs)
                  · rfl
                  simp only [except_bind_ok]
                  cases h10 : liftE "sim" (mkCtx env { Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } (toSimPlayable pb) frames .catchup)
                  · rfl
                  rename_i c0
                  simp only [except_bind_ok]
                  cases h9 : liftE "sim" (simulateSteps refs (Array.map (fun x => x.time) frames) (gameplayStartTime (toSimPlayable pb)))
                  · rfl
                  rename_i st
                  simp only [except_bind_ok, pure, Except.pure]
                  by_cases hfo : (!stepFramesOk st c0.frames.size) = true
                  · simp only [hfo, if_true, OsuModel.Eval.reject, except_throw, except_bind_error]
                  simp only [hfo, Bool.false_eq_true, if_false, except_bind_ok]
                  cases h11 : liftE "sim" (runWith { c0 with steps := st } { Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } (toSimPlayable pb)) with
                  | error e => rfl
                  | ok s =>
                    simp only [except_bind_ok]
                    cases h12 : liftE "sim" (do ({ Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } : Config).trueRate (← netStr (({ Config.ofMods mods (toSimPlayable pb) with lazerReplay := !sc.isLegacyScore } : Config).dynRates.mapM (·.initialSpeed)))) with
                    | error e => rfl
                    | ok rate =>
                      simp only [except_bind_ok, Except.pure]
            · simp only [OsuModel.Eval.reject, except_throw, except_bind_error]


theorem js_evS_beatmap_ok {B : ByteArray} {D : OsuModel.Beatmap.DecodedBeatmap} (h : evS_beatmap B = .ok D) :
    OsuModel.Beatmap.LegacyBeatmapDecoder.decode B = .ok D := by
  unfold evS_beatmap at h
  cases hx : OsuModel.Beatmap.LegacyBeatmapDecoder.decode B with
  | error e => rw [hx] at h; simp [liftE, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw] at h
  | ok d =>
    rw [hx] at h; simp only [liftE, pure, Except.pure] at h
    split at h
    · simp [OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw] at h
    · cases h; rfl

theorem js_liftE_ok {α ε : Type} [ToString ε] {s : String} {x : Except ε α} {y : α} (h : liftE s x = .ok y) :
    x = .ok y := by
  cases x with
  | error e => simp [liftE, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw] at h
  | ok v => simp only [liftE, pure, Except.pure] at h; cases h; rfl

/-! ## Named top-level hypotheses on the spec simulation (TRUSTED §5 rows `RunBudget`, `ScheduleFrames`) -/

/-- the spec simulation context `CTX` (and config `C`) that `evaluate E` builds for these inputs -/
def ev_simCtxOf (E : Env) (bm osr : Slice U8) (opts : eval.Options) (sched : eval.Schedule)
    (C : Config) (CTX : Ctx) : Prop :=
  ∃ DB SC MODS PB FS N, evS_beatmap (bytesS bm) = .ok DB ∧ Osr.decode (bytesS osr) = .ok SC ∧
    resolveMods SC.mods (ev_optsS opts) = .ok MODS ∧ evS_gameplay DB MODS = .ok PB ∧
    evS_frames SC.frameText (toSimPlayable PB).beatmapVersion = .ok FS ∧
    C = { Config.ofMods MODS (toSimPlayable PB) with lazerReplay := !SC.isLegacyScore } ∧
    evS_sched E C (toSimPlayable PB) FS (ev_schedS sched) = .ok (N, CTX)

/-- TRUSTED size row `RunBudget` (D67a/c, D70; docs/proof-pipeline.md §5): machine-integer headroom of the step loop
(transform tracker counters, completed_spins), stated on the spec run (`RunBudgetS`, Sim/StepInv.lean); checked on
the corpus with `runBudgetOkE`; and (D77) the init-state counter headroom `e2AccBudS` (`fail_triggers`) -/
def RunBudgetIn (E : Env) (bm osr : Slice U8) (opts : eval.Options) (sched : eval.Schedule) : Prop :=
  (∀ C CTX S0, ev_simCtxOf E bm osr opts sched C CTX → initState CTX.cfg CTX.pb CTX.smax.initWithoutMods = .ok S0 → RunBudgetS CTX S0) ∧
  (∀ C CTX, ev_simCtxOf E bm osr opts sched C CTX → e2AccBudS CTX)

end Staged

end OsuProofs
