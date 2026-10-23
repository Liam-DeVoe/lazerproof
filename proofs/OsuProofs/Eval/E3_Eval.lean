/-
eval3 slice: the remaining `eval/mod.rs` glue: `reject`, `sim_rej` (rejection constructors), `playable_of`
(= `get_playable_beatmap`, refines `Eval.playableOf`) and `playable_for` (the `--dump-playable` path, refines
`Eval.playableFor`). Rejections are related at the stage level (`ev_rjRel`, D52 (b)); the callees are the proved
`beatmap.decoder.decode_refines` (via `js_decode_sizes`), `eval.osr.decode_refines` (with the proved utf8 and
score-info facts; only the trusted LZMA bound `ev_lzmaBound` remains a hypothesis, as for `eval.osr.decode`),
`eval.resolve_mods_refines`, `js_ev_playable` and `eval.adapter.to_sim_playable_refines`.
-/
import OsuProofs.Eval.JsonFinal
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

/-- `reject` builds the rejection of the spec's `reject stage reason` (stages related by `ev_stageS`; the reason
texts are informational, D52 (b)). -/
theorem eval.reject_refines (s : eval.Stage) (r : eval.Reason) {α β : Type} (f : α → β) (txt : String) :
    eval.reject s r = ok ⟨s, r⟩ ∧
      ev_rjRel f (core.result.Result.Err ⟨s, r⟩ : core.result.Result α eval.Rejection)
        (OsuModel.Eval.reject (α := β) (ev_stageS s) txt) := by
  refine ⟨rfl, ?_⟩
  simp [ev_rjRel, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw]

/-- `sim_rej` is the spec's `liftE "sim"` of a failed sim computation. -/
theorem eval.sim_rej_refines (e : sim.err.SimErr) {α β ε : Type} [ToString ε] (f : α → β) (E : ε) :
    eval.sim_rej e = ok ⟨.Sim, .Sim e⟩ ∧
      ev_rjRel f (core.result.Result.Err ⟨.Sim, .Sim e⟩ : core.result.Result α eval.Rejection)
        (OsuModel.Eval.liftE (α := β) "sim" (.error E)) := by
  refine ⟨rfl, ?_⟩
  simp [ev_rjRel, OsuModel.Eval.liftE, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw, ev_stageS]

/-- `playable_of` refines `Eval.playableOf` (well-formed mods, spec-level `LoadBounds`). -/
theorem eval.playable_of_refines (h64 : System.Platform.numBits = 64) (d : beatmap.types.DecodedBeatmap)
    (mods : Slice beatmap.mod_settings.ModConfig) (hm : ∀ m ∈ mods.val, ev_mcOk m) (hpb : ev_pbOk d mods) :
    ∃ r, eval.playable_of d mods = ok r ∧ ev_eRel abs r (OsuModel.Eval.playableOf (dec_dbS d) (mods.val.map mcS)) := by
  unfold eval.playable_of
  exact js_ev_playable h64 d mods hm hpb

/-- `decode_osr` without `EvalAssumptions` (utf8 and score-info facts proved; LZMA bound trusted). -/
theorem e3_decode_osr (hL : ev_lzmaBound) (b : Slice U8) (h64 : System.Platform.numBits = 64)
    (hb : b.val.length < 2^62) :
    ∃ r, eval.decode_osr b = ok r ∧
      (match r, OsuModel.Eval.liftE "replay-decode" (OsuModel.Replay.Osr.decode (bytesS b)) with
       | .Ok d, .ok D => ev_dsS d = D ∧ ev_dsOk d
       | .Err e, .error E => E.stage = ev_stageS e.stage
       | _, _ => False) := by
  obtain ⟨r, hr, hrel⟩ := eval.osr.decode_refines js_ev_utf8 hL (js_ev_scoreInfo h64) h64 b hb
  unfold eval.decode_osr; rw [hr]; simp only [bind_ok]
  revert hrel
  cases r with
  | Ok d =>
    cases OsuModel.Replay.Osr.decode (bytesS b) with
    | ok D => intro h; exact ⟨.Ok d, rfl, by simpa [OsuModel.Eval.liftE, pure, Except.pure] using h⟩
    | error _ => intro h; exact h.elim
  | Err e =>
    cases OsuModel.Replay.Osr.decode (bytesS b) with
    | ok _ => intro h; exact h.elim
    | error _ => intro _; exact ⟨.Err ⟨.ReplayDecode, .Osr e⟩, by simp [eval.reject],
        by simp [OsuModel.Eval.liftE, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw, ev_stageS]⟩

theorem e3_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl
theorem e3_err_bind {ε α β : Type} (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = Except.error e := rfl
theorem e3_liftE_ok {α ε : Type} [ToString ε] (s : String) (a : α) :
    OsuModel.Eval.liftE (ε := ε) s (.ok a) = .ok a := rfl
theorem e3_pf_eq (B O : ByteArray) (o : OsuModel.Eval.Options) : OsuModel.Eval.playableFor B O o =
    (OsuModel.Eval.liftE "beatmap-decode" (LegacyBeatmapDecoder.decode B) >>= fun d =>
     OsuModel.Eval.liftE "replay-decode" (OsuModel.Replay.Osr.decode O) >>= fun sc =>
     OsuModel.Eval.resolveMods sc.mods o >>= fun mods =>
     OsuModel.Eval.liftE "playable" (OsuModel.Eval.playableOf d mods) >>= fun pb =>
     Except.ok (OsuModel.Eval.toSimPlayable pb)) := rfl

/-- `playable_for` (the `--dump-playable` path) refines `Eval.playableFor`. Hypotheses as for
`eval.evaluate_refines` (input bounds, playable bounds, well-formed override mods), plus the trusted LZMA bound. -/
theorem eval.playable_for_refines (hL : ev_lzmaBound) (bm osr : Slice U8) (hb : InputBounds bm osr)
    (opts : eval.Options)
    (hopts : ∀ ov, opts.mods_override = some ov → (∀ m ∈ ov.val, ev_mcOk m) ∧ ov.val.length < 2^62)
    (hpb : PlayableBounds bm osr opts) :
    ∃ r, eval.playable_for bm osr opts = ok r ∧
      ev_rjRel (playableS ev_tn) r (OsuModel.Eval.playableFor (bytesS bm) (bytesS osr) (ev_optsS opts)) := by
  rw [e3_pf_eq]
  unfold eval.playable_for
  obtain ⟨N, hN, hpath, hsize⟩ := hb.decLines
  obtain ⟨r1, h1, rel1, hsz⟩ := js_decode_sizes bm hb.bmLen hb.h64 N hN hpath hsize
  rw [h1]; simp only [bind_ok]
  revert rel1
  cases r1 with
  | Err e =>
    cases LegacyBeatmapDecoder.decode (bytesS bm) with
    | ok _ => intro h; exact h.elim
    | error _ =>
      intro _
      refine ⟨.Err ⟨.BeatmapDecode, .Decode e⟩, by simp [eval.reject], ?_⟩
      simp [OsuModel.Eval.liftE, ev_rjRel, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw, ev_stageS,
        e3_err_bind]
  | Ok d =>
  cases hDec : LegacyBeatmapDecoder.decode (bytesS bm) with
  | error _ => intro h; exact h.elim
  | ok D =>
  intro hD; simp only [hRel] at hD; subst hD
  have hdsz := hsz d rfl
  simp only [e3_liftE_ok, e3_ok_bind]
  -- .osr
  obtain ⟨r2, h2, rel2⟩ := e3_decode_osr hL osr hb.h64 hb.osrLen
  rw [h2]; simp only [bind_ok]
  revert rel2
  cases r2 with
  | Err e =>
    cases hO : OsuModel.Eval.liftE "replay-decode" (OsuModel.Replay.Osr.decode (bytesS osr)) with
    | ok _ => intro h; exact h.elim
    | error E =>
      intro h
      exact ⟨.Err e, rfl, by simpa [e3_err_bind, ev_rjRel] using h⟩
  | Ok sc =>
  cases hEO : OsuModel.Eval.liftE "replay-decode" (OsuModel.Replay.Osr.decode (bytesS osr)) with
  | error _ => intro h; exact h.elim
  | ok SC =>
  intro hS
  obtain ⟨hS, hok⟩ := hS; subst hS
  have hO := js_liftE_ok hEO
  simp only [e3_ok_bind]
  obtain ⟨hokB, hokM, hokT, hokL⟩ := hok
  -- resolve
  obtain ⟨r3, h3, rel3, hok3⟩ := eval.resolve_mods_refines hb.h64 (alloc.vec.Vec.deref sc.mods) opts (by simpa using hokM)
    (by simpa using hokL) hopts
  rw [h3]; simp only [bind_ok]
  simp only [ms_deref_val] at rel3
  have hm' : (ev_dsS sc).mods = sc.mods.val.map mcS := rfl
  rw [hm']
  revert rel3
  cases r3 with
  | Err e =>
    cases OsuModel.Eval.resolveMods (sc.mods.val.map mcS) (ev_optsS opts) with
    | ok _ => intro h; exact h.elim
    | error E => intro h; exact ⟨.Err e, rfl, by simpa [e3_err_bind, ev_rjRel] using h⟩
  | Ok v2 =>
  cases hRM : OsuModel.Eval.resolveMods (sc.mods.val.map mcS) (ev_optsS opts) with
  | error _ => intro h; exact h.elim
  | ok MODS =>
  intro hM; simp only [ev_rjRel] at hM; subst hM
  have hv2ok := hok3 v2 rfl
  simp only [e3_ok_bind]
  -- playable
  obtain ⟨r4, h4, rel4⟩ := eval.playable_of_refines hb.h64 d (alloc.vec.Vec.deref v2) (by simpa using hv2ok) (by
    have hG := hpb.gameplay _ _ _ hDec hO (by rw [hm']; exact hRM)
    exact js_pbOk_of d _ _ hdsz (hpb.sliderPaths _ hDec) hG (by first | rfl | simp [ms_deref_val]))
  simp only [ms_deref_val] at rel4
  rw [h4]; simp only [bind_ok]
  revert rel4
  cases r4 with
  | Err e =>
    cases OsuModel.Eval.playableOf (dec_dbS d) (v2.val.map mcS) with
    | ok _ => intro h; exact h.elim
    | error _ =>
      intro _
      exact ⟨.Err ⟨.Playable, .Decode e⟩, by simp [eval.reject],
        by simp [ev_rjRel, OsuModel.Eval.liftE, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw, ev_stageS,
          e3_err_bind]⟩
  | Ok pb =>
    cases OsuModel.Eval.playableOf (dec_dbS d) (v2.val.map mcS) with
    | error _ => intro h; exact h.elim
    | ok PB =>
      intro hP; simp only [ev_eRel] at hP; subst hP
      obtain ⟨spb, h6, e6⟩ := eval.adapter.to_sim_playable_refines pb
      refine ⟨.Ok spb, by simp [h6], ?_⟩
      simp [ev_rjRel, e6, e3_liftE_ok, e3_ok_bind]

end OsuProofs
