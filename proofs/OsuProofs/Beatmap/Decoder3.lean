/-
`beatmap::decoder` part 3: `handle_hit_object`, `parse_line`, `parse_lines`, `parse_stream_into`, `decode`.
The line loop keeps the size invariant `dec_szOk s n` (control-point/pending/break/hit-object counts with `n`
lines to go stay below 2^31); per-handler frame facts come from spec-level lemmas (`dec_hg_frame`, ...) and a
strengthened timing-point lemma (`dec_htp_full`). Input-size assumptions are explicit: `numBits = 64`, line
lengths `< N ≤ 2^61`, the line count `+ 1 < 2^31`, and `dec_pathOk N` for slider paths (see
`slider_path.of_control_points_refines`). Helper names are prefixed `dec_`.
-/
import OsuProofs.Beatmap.Decoder2
import OsuProofs.Beatmap.HitObjectParser4
import OsuProofs.Beatmap.DotNetSort
import OsuProofs.Beatmap.Text
import OsuProofs.LoopsR
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.deprecated false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap OsuProofs

namespace OsuProofs
open OsuImpl

/-- The state fields a section handler may not touch. -/
def dec_frame (S S' : DecoderState) : Prop :=
  S'.cpi = S.cpi ∧ S'.pending = S.pending ∧ S'.hitObjects = S.hitObjects ∧ S'.sect = S.sect

theorem dec_hg_frame (S S' : DecoderState) (L : String) (h : LegacyBeatmapDecoder.handleGeneral S L = .ok S') :
    dec_frame S S' ∧ S'.breaks = S.breaks := by
  unfold LegacyBeatmapDecoder.handleGeneral at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first | (simp only [Except.ok.injEq] at h; subst h; exact ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩) | (cases h) | simp_all [dec_frame]

theorem dec_hd_frame (S S' : DecoderState) (L : String) (h : LegacyBeatmapDecoder.handleDifficulty S L = .ok S') :
    dec_frame S S' ∧ S'.breaks = S.breaks := by
  unfold LegacyBeatmapDecoder.handleDifficulty at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first | (simp only [Except.ok.injEq] at h; subst h; exact ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩) | (cases h) | simp_all [dec_frame]

theorem dec_insertIdx_size (bs : _root_.Array BreakPeriod) (b : BreakPeriod) (p : BreakPeriod → Bool) :
    (bs.insertIdx! ((bs.findIdx? p).getD bs.size) b).size = bs.size + 1 := by
  have hle : (bs.findIdx? p).getD bs.size ≤ bs.size := by
    cases h : bs.findIdx? p with
    | none => simp
    | some i => simp; exact le_of_lt (Array.findIdx?_eq_some_iff_getElem.mp h).1
  unfold Array.insertIdx!; rw [dif_pos hle]; simp

theorem dec_insertBreak_size (bs : _root_.Array BreakPeriod) (b : BreakPeriod) :
    (LegacyBeatmapDecoder.insertBreak bs b).size = bs.size + 1 := by
  unfold LegacyBeatmapDecoder.insertBreak
  exact dec_insertIdx_size _ _ _

theorem dec_he_frame (S S' : DecoderState) (L : String) (h : LegacyBeatmapDecoder.handleEvent S L = .ok S') :
    dec_frame S S' ∧ S'.breaks.size ≤ S.breaks.size + 1 := by
  unfold LegacyBeatmapDecoder.handleEvent at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first | (simp only [Except.ok.injEq] at h; subst h; exact ⟨⟨rfl, rfl, rfl, rfl⟩, by simp [dec_insertBreak_size]⟩) | (simp only [Except.ok.injEq] at h; subst h; exact ⟨⟨rfl, rfl, rfl, rfl⟩, by omega⟩) | (cases h) | simp_all [dec_frame]

/-- What a decoder line handler may change, for the line-loop size invariant. -/
def dec_frameR (s s' : beatmap.decoder.DecoderState) (k : Nat) : Prop :=
  dec_cpiOk s'.cpi k ∧ s'.pending.timing.val.length ≤ s.pending.timing.val.length + 1 ∧
  s'.pending.difficulty.val.length ≤ s.pending.difficulty.val.length + 1 ∧
  s'.pending.effect.val.length ≤ s.pending.effect.val.length + 1 ∧
  s'.breaks = s.breaks ∧ s'.hit_objects = s.hit_objects ∧ s'.sect = s.sect

theorem dec_frameR_refl (s : beatmap.decoder.DecoderState) (k : Nat) (hc : dec_cpiOk s.cpi (k+1)) : dec_frameR s s k := by
  refine ⟨?_, by omega, by omega, by omega, rfl, rfl, rfl⟩
  unfold dec_cpiOk at *; omega

macro "dec_dstep2 " r:term:max h:term:max v:ident : tactic =>
  `(tactic| (rcases $r:term with $v:ident | e; (on_goal 2 => exact ⟨_, rfl, Or.inr ⟨⟨e, rfl⟩, dec_err_bind $h _, rfl⟩, dec_frameR_refl _ _ (by assumption)⟩); simp only [rel_ok $h, except_bind_ok, id_eq]))

theorem dec_htp_full (s : beatmap.decoder.DecoderState) (line : Slice U32)
    (hs : ValidStr line) (hn : line.val.length < 2^62) (hn2 : line.val.length < Usize.max)
    (k : Nat) (hc : dec_cpiOk s.cpi (k+1))
    (hp : s.pending.timing.val.length + 1 < Usize.max ∧ s.pending.difficulty.val.length + 1 < Usize.max ∧
      s.pending.effect.val.length + 1 < Usize.max) :
    ∃ p, beatmap.decoder.handle_timing_point s line = ok p ∧
      dec_hRel s p (LegacyBeatmapDecoder.handleTimingPoint (dec_dsS s) (String.ofList (strS line))) ∧
      dec_frameR s p.2 k := by
  unfold beatmap.decoder.handle_timing_point
  rw [dec_htp_body, dec_htp_eq]
  obtain ⟨sp, hsp, hspv, hspV, hspL⟩ := split_rel line hs hn2 44#u32 (by decide)
  rw [comma_lit] at hspv
  simp only [hsp, bind_ok]
  rw [← hspv]
  have hVv : ∀ v ∈ sp.val, ValidStr (alloc.vec.Vec.deref v) := fun v hv => validStr_of v (hspV v hv)
  have hV' : ∀ l ∈ (alloc.vec.Vec.deref sp).val, ValidL l.val := by intro l hl; rw [deref_valA] at hl; exact hspV l hl
  have e0 : (0#usize : Usize).val = 0 := rfl
  have e1 : (1#usize : Usize).val = 1 := rfl
  -- time
  obtain ⟨r0, h0, h0r, h0m⟩ := beatmap.hit_object_parser.at_refines (alloc.vec.Vec.deref sp) 0#usize
  rw [deref_valA, e0] at h0r; rw [deref_valA] at h0m
  simp only [h0, bind_ok]
  dec_dstep2 r0 h0r v
  have hvm := h0m v rfl
  obtain ⟨tv, htv, htvS, htvV⟩ := trim_valid (alloc.vec.Vec.deref v) (hVv v hvm)
  have htl := dec_trim_len _ (hVv v hvm) tv htv
  rw [strV_deref] at htvS
  have htl2 : (alloc.vec.Vec.deref tv).val.length < 2^62 := by
    have := hspL v hvm; simp at htl ⊢; omega
  simp only [htv, bind_ok, net.parse.parse_double_default_refines _ (validStr_of tv htvV) htl2, strV_deref]
  have etv : strV tv = trim (strV v) := htvS
  rw [etv]
  obtain ⟨r2, h2, h2r⟩ := lift_net_exceptI beatmap.errors.W_TIME id id (fun _ => rfl)
    (Parsing.parseDouble (trim (strV v))) "time"
  simp only [h2, bind_ok]
  cases hx : liftNet "time" (Parsing.parseDouble (trim (strV v))) with
  | error m =>
    rw [hx] at h2r
    rcases r2 with t | e
    · simp [hRel] at h2r
    · exact ⟨_, rfl, Or.inr ⟨⟨e, rfl⟩, ⟨m, rfl⟩, rfl⟩, dec_frameR_refl s k hc⟩
  | ok t =>
  rw [hx] at h2r
  rcases r2 with t' | e
  on_goal 2 => simp [hRel] at h2r
  simp only [hRel, id] at h2r; subst t'
  simp only [except_bind_ok]
  simp only [dec_offset_time, bind_ok, id]
  -- beatLength
  obtain ⟨r3, h3, h3r, h3m⟩ := beatmap.hit_object_parser.at_refines (alloc.vec.Vec.deref sp) 1#usize
  rw [deref_valA, e1] at h3r; rw [deref_valA] at h3m
  simp only [h3, bind_ok]
  dec_dstep2 r3 h3r v3
  have hvm3 := h3m v3 rfl
  obtain ⟨tv3, htv3, htvS3, htvV3⟩ := trim_valid (alloc.vec.Vec.deref v3) (hVv v3 hvm3)
  have htl3 := dec_trim_len _ (hVv v3 hvm3) tv3 htv3
  rw [strV_deref] at htvS3
  have htl4 : (alloc.vec.Vec.deref tv3).val.length < 2^62 := by
    have := hspL v3 hvm3; simp at htl3 ⊢; omega
  simp only [htv3, bind_ok, parse_MAX_PARSE_VALUE,
    net.parse.parsing_parse_double_refines _ (validStr_of tv3 htvV3) htl4, strV_deref]
  have etv3 : strV tv3 = trim (strV v3) := htvS3
  rw [etv3]
  obtain ⟨r5, h5, h5r⟩ := lift_net_exceptI beatmap.errors.W_BEATLENGTH id id (fun _ => rfl)
    (Parsing.parseDouble (trim (strV v3)) Parsing.MAX_PARSE_VALUE true) "beatLength"
  simp only [h5, bind_ok]
  cases hx5 : liftNet "beatLength" (Parsing.parseDouble (trim (strV v3)) Parsing.MAX_PARSE_VALUE true) with
  | error m =>
    rw [hx5] at h5r
    rcases r5 with bl | e
    · simp [hRel] at h5r
    · exact ⟨_, rfl, Or.inr ⟨⟨e, rfl⟩, ⟨m, rfl⟩, rfl⟩, dec_frameR_refl s k hc⟩
  | ok bl =>
  rw [hx5] at h5r
  rcases r5 with bl' | e
  on_goal 2 => simp [hRel] at h5r
  simp only [hRel, id] at h5r; subst bl'
  simp only [except_bind_ok]
  simp only [beatmap.decoder.tp_speed_multiplier_refines, bind_ok, id]
  -- time signature
  obtain ⟨r6, h6, h6r⟩ := beatmap.decoder.tp_time_signature_refines (alloc.vec.Vec.deref sp) hV'
  rw [deref_valA] at h6r
  change hRel i32S r6 (dec_TS (vstrs sp.val)) at h6r
  simp only [h6, bind_ok]
  dec_dstep2 r6 h6r ts
  -- three int checks
  obtain ⟨r7, h7, h7r⟩ := beatmap.decoder.tp_check_int_refines (alloc.vec.Vec.deref sp) hV' 3#usize
    beatmap.errors.W_SAMPLESET "sampleSet"
  rw [deref_valA] at h7r
  change hRel id r7 (dec_CI (vstrs sp.val) 3 "sampleSet") at h7r
  simp only [h7, bind_ok]
  dec_dstep2 r7 h7r u7
  obtain ⟨r8, h8, h8r⟩ := beatmap.decoder.tp_check_int_refines (alloc.vec.Vec.deref sp) hV' 4#usize
    beatmap.errors.W_CUSTOMSAMPLEBANK "customSampleBank"
  rw [deref_valA] at h8r
  change hRel id r8 (dec_CI (vstrs sp.val) 4 "customSampleBank") at h8r
  simp only [h8, bind_ok]
  dec_dstep2 r8 h8r u8
  obtain ⟨r9, h9, h9r⟩ := beatmap.decoder.tp_check_int_refines (alloc.vec.Vec.deref sp) hV' 5#usize
    beatmap.errors.W_SAMPLEVOLUME "sampleVolume"
  rw [deref_valA] at h9r
  change hRel id r9 (dec_CI (vstrs sp.val) 5 "sampleVolume") at h9r
  simp only [h9, bind_ok]
  dec_dstep2 r9 h9r u9
  -- timing change, kiai
  obtain ⟨r10, h10, h10r⟩ := beatmap.decoder.tp_timing_change_refines (alloc.vec.Vec.deref sp) hV'
  rw [deref_valA] at h10r
  change hRel id r10 (dec_TC (vstrs sp.val)) at h10r
  simp only [h10, bind_ok]
  dec_dstep2 r10 h10r tc
  obtain ⟨r11, h11, h11r⟩ := beatmap.decoder.tp_kiai_refines (alloc.vec.Vec.deref sp) hV'
  rw [deref_valA] at h11r
  change hRel id r11 (dec_KI (vstrs sp.val)) at h11r
  simp only [h11, bind_ok]
  dec_dstep2 r11 h11r kiai
  -- timing point
  obtain ⟨r12, h12, h12r⟩ := beatmap.decoder.tp_timing_refines (LegacyBeatmapDecoder.offsetTime (dec_dsS s) t) bl ts tc
  change hRel (Option.map tpS) r12 (dec_TM (LegacyBeatmapDecoder.offsetTime (dec_dsS s) t) bl (i32S ts) tc) at h12r
  simp only [h12, bind_ok]
  dec_dstep2 r12 h12r timing
  simp only [beatmap.control_points.clamp_sv_refines, float.F64.is_nan, beatmap.decoder.tp_scroll_speed_refines, bind_ok]
  obtain ⟨s', hs', hs'v, hck, hpt, hpd, hpe, hbr, hho, -, hsect, -⟩ := beatmap.decoder.add_line_points_refines s k hc hp
    (LegacyBeatmapDecoder.offsetTime (dec_dsS s) t) timing
    { time := LegacyBeatmapDecoder.offsetTime (dec_dsS s) t, slider_velocity := clampSV (if bl < 0 then 100.0 / -bl else 1),
      generate_ticks := decide (¬ (bl.isNaN = true)) }
    { time := LegacyBeatmapDecoder.offsetTime (dec_dsS s) t, kiai := kiai,
      scroll_speed := if (i32S s.ruleset_id == 1 || i32S s.ruleset_id == 3) = true then
        clampScrollSpeed (if bl < 0 then 100.0 / -bl else 1) else 1 } tc
  simp only [hs', bind_ok]
  refine ⟨_, rfl, Or.inl ⟨rfl, ?_⟩, hck, hpt, hpd, hpe, hbr, hho, hsect⟩
  rw [hs'v]
  simp [dpS, epS, dec_dsS]

/-- Input-size assumption for slider paths (from `slider_path.of_control_points_refines`): for every line
shorter than `n`, the spec control points of field 5 number < 2^32 and `calculatePath` stays < 2^62. -/
def dec_pathOk (n : Nat) : Prop :=
  ∀ (L : String), L.length < n → ∀ fv pos cps, ConvertHitObjectParser.convertPathString fv (split L ',')[5]! pos = .ok cps →
    cps.size < 2^32 ∧ ∀ len, (SliderPath.calculatePath { controlPoints := cps, expectedDistance := len, optimiseCatmull := false }).1.size < 2^62

/-- Size invariant of the line loop with `n` lines still to go. -/
def dec_szOk (s : beatmap.decoder.DecoderState) (n : Nat) : Prop :=
  dec_cpiOk s.cpi (n+1) ∧ s.pending.timing.val.length + n + 1 < 2^31 ∧ s.pending.difficulty.val.length + n + 1 < 2^31 ∧
  s.pending.effect.val.length + n + 1 < 2^31 ∧ s.breaks.val.length + n < 2^31 ∧ s.hit_objects.val.length + n < 2^31

theorem dec_frame_sizes (s s' : beatmap.decoder.DecoderState) (h : dec_frame (dec_dsS s) (dec_dsS s')) :
    s'.cpi.timing_points.val.length = s.cpi.timing_points.val.length ∧
    s'.cpi.difficulty_points.val.length = s.cpi.difficulty_points.val.length ∧
    s'.cpi.effect_points.val.length = s.cpi.effect_points.val.length ∧
    s'.pending.timing.val.length = s.pending.timing.val.length ∧
    s'.pending.difficulty.val.length = s.pending.difficulty.val.length ∧
    s'.pending.effect.val.length = s.pending.effect.val.length ∧
    s'.hit_objects.val.length = s.hit_objects.val.length ∧ s'.sect = s.sect := by
  obtain ⟨hc, hp, hh, hs⟩ := h
  simp only [dec_dsS, cpS, dec_pendS] at hc hp hh hs
  have c1 := congrArg (fun c => c.timingPoints.size) hc
  have c2 := congrArg (fun c => c.difficultyPoints.size) hc
  have c3 := congrArg (fun c => c.effectPoints.size) hc
  have p1 := congrArg (fun c => c.timing.length) hp
  have p2 := congrArg (fun c => c.difficulty.length) hp
  have p3 := congrArg (fun c => c.effect.length) hp
  have h1 := congrArg _root_.Array.size hh
  simp at c1 c2 c3 p1 p2 p3 h1
  exact ⟨c1, c2, c3, p1, p2, p3, h1, dec_i32S_inj _ _ hs⟩

theorem dec_strS_len (line : Slice U32) : (String.ofList (strS line)).length = line.val.length := by
  simp [strS]

theorem beatmap.decoder.handle_hit_object_refines (s : beatmap.decoder.DecoderState) (line : Slice U32)
    (hs : ValidStr line) (hn : line.val.length < 2^61) (h64 : System.Platform.numBits = 64)
    (N : Nat) (hpath : dec_pathOk N) (hln : line.val.length < N) (hh : s.hit_objects.val.length < Usize.max) :
    ∃ s', beatmap.decoder.handle_hit_object s line = ok s' ∧
      dec_dsS s' = LegacyBeatmapDecoder.handleHitObject (dec_dsS s) (String.ofList (strS line)) ∧
      s'.cpi = s.cpi ∧ s'.pending = s.pending ∧ s'.breaks = s.breaks ∧
      s'.hit_objects.val.length ≤ s.hit_objects.val.length + 1 ∧ s'.sect = s.sect := by
  unfold beatmap.decoder.handle_hit_object LegacyBeatmapDecoder.handleHitObject
  obtain ⟨⟨p1, r⟩, hp, hp1, hp2⟩ := beatmap.hit_object_parser.parse_refines s.parser line hs hn h64
    (fun fv pos cps h => hpath _ (by rw [dec_strS_len]; exact hln) fv pos cps h)
  have e : (dec_dsS s).parser = psS s.parser := rfl
  rw [e]
  simp only [hp, bind_ok, uncurry_apply_pair]
  cases hP : ConvertHitObjectParser.parse (psS s.parser) (String.ofList (strS line)) with
  | mk P1 R =>
    rw [hP] at hp1 hp2
    simp only at hp1 hp2 ⊢
    cases r with
    | Ok o =>
      rw [rel_ok hp2]
      simp only [vec_push_ok s.hit_objects o hh, bind_ok]
      refine ⟨_, rfl, ?_, rfl, rfl, rfl, by simp, rfl⟩
      simp [dec_dsS, hp1]
    | Err e =>
      cases hR : R with
      | ok y => rw [hR] at hp2; simp [hRel] at hp2
      | error m =>
        refine ⟨_, rfl, ?_, rfl, rfl, rfl, by simp, rfl⟩
        simp [dec_dsS, hp1]

/-- `parseLine`'s `catch`: the handler's new state, or the old one on failure. -/
def dec_resS (s : DecoderState) (X : DecodeM DecoderState) : DecoderState :=
  match X with
  | .ok s' => s'
  | .error _ => s

theorem dec_szOk_mono (s : beatmap.decoder.DecoderState) (n : Nat) (h : dec_szOk s (n+1)) : dec_szOk s n := by
  unfold dec_szOk dec_cpiOk at *; omega

theorem dec_line_sz (s : beatmap.decoder.DecoderState)
    (p : core.result.Result Unit beatmap.hit_object_parser.DecodeError × beatmap.decoder.DecoderState)
    (X : DecodeM DecoderState) (n : Nat) (h : dec_hRel s p X)
    (hf : ∀ S', X = .ok S' → dec_frame (dec_dsS s) S' ∧ S'.breaks.size ≤ (dec_dsS s).breaks.size + 1)
    (hsz : dec_szOk s (n+1)) : dec_szOk p.2 n ∧ p.2.sect = s.sect ∧
      dec_dsS p.2 = dec_resS (dec_dsS s) X := by
  rcases h with ⟨_, hx⟩ | ⟨_, ⟨m, hx⟩, hs⟩
  · obtain ⟨hfr, hb⟩ := hf _ hx
    obtain ⟨c1, c2, c3, p1, p2, p3, h1, hsect⟩ := dec_frame_sizes s p.2 hfr
    simp only [dec_dsS, List.size_toArray, List.length_map] at hb
    refine ⟨?_, hsect, by rw [hx]; rfl⟩
    unfold dec_szOk dec_cpiOk at *
    rw [c1, c2, c3, p1, p2, p3, h1]; omega
  · rw [hs, hx]; exact ⟨dec_szOk_mono s n hsz, rfl, rfl⟩

theorem dec_line_eq (s : beatmap.decoder.DecoderState)
    (p : core.result.Result Unit beatmap.hit_object_parser.DecodeError × beatmap.decoder.DecoderState)
    (X : DecodeM DecoderState) (h : dec_hRel s p X) :
    dec_dsS p.2 = dec_resS (dec_dsS s) X := by
  rcases h with ⟨_, hx⟩ | ⟨_, ⟨m, hx⟩, hs⟩
  · rw [hx]; rfl
  · rw [hs, hx]; rfl

theorem dec_umax31 (h64 : System.Platform.numBits = 64) (x : Nat) (h : x < 2^31) : x < Usize.max := by
  rw [hop_umax64 h64]; omega

set_option maxHeartbeats 1000000 in
theorem beatmap.decoder.parse_line_refines (s : beatmap.decoder.DecoderState) (line : Slice U32)
    (hs : ValidStr line) (hn : line.val.length < 2^61) (h64 : System.Platform.numBits = 64)
    (N : Nat) (hpath : dec_pathOk N) (hln : line.val.length < N) (n : Nat) (hsz : dec_szOk s (n+1)) :
    ∃ s', beatmap.decoder.parse_line s line = ok s' ∧
      dec_dsS s' = LegacyBeatmapDecoder.parseLine (dec_dsS s) (String.ofList (strS line)) ∧
      dec_szOk s' n ∧ s'.sect = s.sect := by
  obtain ⟨hc, hpt, hpd, hpe, hbr, hho⟩ := hsz
  have hsz' : dec_szOk s (n+1) := ⟨hc, hpt, hpd, hpe, hbr, hho⟩
  unfold beatmap.decoder.parse_line LegacyBeatmapDecoder.parseLine
  have hsect : (dec_dsS s).sect = i32S s.sect := rfl
  rw [hsect]
  by_cases h7 : s.sect = 7#i32
  · have e7 : i32S s.sect = 7 := by rw [h7]; decide
    rw [if_pos h7]
    obtain ⟨s', hs', hs'v, hcpi, hpend, hbrk, hhl, hsec⟩ := beatmap.decoder.handle_hit_object_refines s line hs hn h64 N
      hpath hln (dec_umax31 h64 _ (by omega))
    refine ⟨s', hs', ?_, ?_, hsec⟩
    · rw [hs'v, e7]; rfl
    · refine ⟨by rw [hcpi]; unfold dec_cpiOk at *; omega, by rw [hpend]; omega, by rw [hpend]; omega,
        by rw [hpend]; omega, by rw [hbrk]; omega, by omega⟩
  · rw [if_neg h7]
    have hgen := fun (hp : _) (X : DecodeM DecoderState) (h : dec_hRel s hp X)
        (hf : ∀ S', X = .ok S' → dec_frame (dec_dsS s) S' ∧ S'.breaks.size ≤ (dec_dsS s).breaks.size + 1) =>
      dec_line_sz s hp X n h hf hsz'
    by_cases h0 : s.sect = 0#i32
    · have e0 : i32S s.sect = 0 := by rw [h0]; decide
      rw [if_pos h0, if_pos h0]
      obtain ⟨⟨r1, s2⟩, hp, hpr⟩ := beatmap.decoder.handle_general_refines s line hs (by omega)
      obtain ⟨hz, hsec, heq⟩ := hgen (r1, s2) _ hpr (fun S' h => by
        obtain ⟨hf, hb⟩ := dec_hg_frame _ _ _ h; exact ⟨hf, by rw [hb]; omega⟩)
      rw [hp]
      refine ⟨s2, ?_, ?_, hz, hsec⟩
      · simp only [bind_ok, uncurry_apply_pair]; cases r1 <;> rfl
      · rw [heq, e0]; rfl
    by_cases h3 : s.sect = 3#i32
    · have e3 : i32S s.sect = 3 := by rw [h3]; decide
      rw [if_neg h0, if_pos h3, if_neg h0, if_pos h3]
      obtain ⟨⟨r1, s2⟩, hp, hpr⟩ := beatmap.decoder.handle_difficulty_refines s line hs (by omega)
      obtain ⟨hz, hsec, heq⟩ := hgen (r1, s2) _ hpr (fun S' h => by
        obtain ⟨hf, hb⟩ := dec_hd_frame _ _ _ h; exact ⟨hf, by rw [hb]; omega⟩)
      rw [hp]
      refine ⟨s2, by simp only [bind_ok, uncurry_apply_pair]; cases r1 <;> rfl, ?_, hz, hsec⟩
      rw [heq, e3]; rfl
    by_cases h4 : s.sect = 4#i32
    · have e4 : i32S s.sect = 4 := by rw [h4]; decide
      rw [if_neg h0, if_neg h3, if_pos h4, if_neg h0, if_neg h3, if_pos h4]
      obtain ⟨⟨r1, s2⟩, hp, hpr⟩ := beatmap.decoder.handle_event_refines s line hs (by omega) (by rw [hop_umax64 h64]; omega)
        (dec_umax31 h64 _ (by omega))
      obtain ⟨hz, hsec, heq⟩ := hgen (r1, s2) _ hpr (fun S' h => dec_he_frame _ _ _ h)
      rw [hp]
      refine ⟨s2, by simp only [bind_ok, uncurry_apply_pair]; cases r1 <;> rfl, ?_, hz, hsec⟩
      rw [heq, e4]; rfl
    by_cases h5 : s.sect = 5#i32
    · have e5 : i32S s.sect = 5 := by rw [h5]; decide
      rw [if_neg h0, if_neg h3, if_neg h4, if_pos h5, if_neg h0, if_neg h3, if_neg h4]
      obtain ⟨⟨r1, s2⟩, hp, hpr, hck, hp1, hp2, hp3, hbk, hhk, hsk⟩ := dec_htp_full s line hs (by omega) (by rw [hop_umax64 h64]; omega)
        (n+1) hc ⟨dec_umax31 h64 _ (by omega), dec_umax31 h64 _ (by omega), dec_umax31 h64 _ (by omega)⟩
      rw [hp]
      simp only at hck hp1 hp2 hp3 hbk hhk hsk
      refine ⟨s2, by simp only [bind_ok, uncurry_apply_pair]; cases r1 <;> rfl, ?_, ?_, hsk⟩
      · rw [dec_line_eq s (r1, s2) _ hpr, e5]; rfl
      · refine ⟨hck, by omega, by omega, by omega, by rw [hbk]; omega, by rw [hhk]; omega⟩
    · rw [if_neg h0, if_neg h3, if_neg h4, if_neg h5]
      refine ⟨s, rfl, ?_, dec_szOk_mono s n hsz', rfl⟩
      generalize hv : i32S s.sect = v
      split
      all_goals first
        | rfl
        | (exfalso; exact h0 (dec_i32S_inj _ _ (by rw [hv]; decide)))
        | (exfalso; exact h3 (dec_i32S_inj _ _ (by rw [hv]; decide)))
        | (exfalso; exact h4 (dec_i32S_inj _ _ (by rw [hv]; decide)))
        | (exfalso; exact h5 (dec_i32S_inj _ _ (by rw [hv]; decide)))
        | (exfalso; exact h7 (dec_i32S_inj _ _ (by rw [hv]; decide)))

theorem dec_sc_full (line : Slice U32) :
    ∃ v, beatmap.decoder.strip_comments line = ok v ∧
      strV v = LegacyBeatmapDecoder.stripComments (String.ofList (strS line)) ∧ ∃ j, v.val = line.val.take j := by
  obtain ⟨k, f, hk, hf1, hf0⟩ := dec_sc_loop line line.val.length 0#usize (by simp) (by simp)
    (by intro p hp; simp at hp)
  have hlen : (strS line).length = line.val.length := by simp [strS]
  have hall : ∃ v, beatmap.dotnet.sub_str line 0#usize (Slice.len line) = ok v ∧ strV v = String.ofList (strS line) ∧
      ∃ j, v.val = line.val.take j := by
    obtain ⟨v, hv, hvv⟩ := beatmap.dotnet.sub_str_refines line 0#usize (Slice.len line) (by simp) (by simp)
    refine ⟨v, hv, ?_, line.val.length, ?_⟩
    · simp [strV, hvv, strS]
    · simp [hvv]
  unfold beatmap.decoder.strip_comments LegacyBeatmapDecoder.stripComments
  rw [dec_splitOn_ss]
  simp only [hk, bind_ok]
  cases f with
  | false =>
    rw [dec_ss2_none _ (by rw [hlen]; exact hf0 rfl)]
    simp only [Bool.false_eq_true, ite_false, List.map_cons, List.map_nil]
    exact hall
  | true =>
    obtain ⟨hk1, hkn, hkd⟩ := hf1 rfl
    rw [dec_ss2_prefix k.val (strS line) (by rw [hlen]; omega) hkn, hkd, dec_ss2_slash2]
    simp only [ite_true, List.modifyHead_cons, List.append_nil, List.map_cons]
    have hE : ("" : String).isEmpty = true := by decide
    by_cases hk0 : k.val = 0
    · have hk0' : ¬ k > 0#usize := by show ¬ (0#usize : Usize).val < k.val; simp; omega
      have hk0'' : ¬ (0#usize : Usize) < k := hk0'
      simp only [uncurry_apply_pair]
      rw [if_pos trivial, if_neg hk0']
      simp only [hk0, List.take_zero, String.ofList_nil]
      cases h : dec_ss2 ((strS line).drop (0 + 2)) with
      | nil => simpa using hall
      | cons a t => simpa using hall
    · have hk0' : k > 0#usize := by show (0#usize : Usize).val < k.val; simp; omega
      have hk0'' : (0#usize : Usize) < k := hk0'
      simp only [uncurry_apply_pair]
      rw [if_pos trivial, if_pos hk0']
      obtain ⟨v, hv, hvv⟩ := beatmap.dotnet.sub_str_refines line 0#usize k (by simp) (by omega)
      refine ⟨v, hv, ?_, k.val, by simp [hvv]⟩
      have hne : (String.ofList ((strS line).take k.val)).isEmpty = false := by
        rw [Bool.eq_false_iff]; intro h
        rw [String.isEmpty_iff] at h
        have h2 : (strS line).take k.val = [] := by
          have := congrArg String.toList h; simpa using this
        rw [List.take_eq_nil_iff] at h2
        rcases h2 with h2 | h2
        · omega
        · rw [h2] at hlen; simp only [List.length_nil] at hlen; omega
      cases h : dec_ss2 ((strS line).drop (k.val + 2)) with
      | nil => exact absurd h (dec_ss2_ne_nil _)
      | cons a t =>
        have hc' : ¬ (k.val = 0 ∨ line.val = []) := by
          rintro (h | h)
          · omega
          · simp [h] at hk1
        simp [hne, hc', strV, hvv, strS, List.map_take]

theorem dec_te_full (s : Slice U32) (hs : ValidStr s) :
    ∃ v, beatmap.dotnet.trim_end s = ok v ∧ strV v = trimEnd (String.ofList (strS s)) ∧ ValidL v.val ∧
      v.val.length ≤ s.val.length := by
  obtain ⟨v, hv, hvv⟩ := beatmap.dotnet.trim_end_refines s hs
  obtain ⟨v', hv', hvv'⟩ := trim_common s hs false true beatmap.dotnet.trim_end (fun _ => rfl)
  have e : v' = v := by rw [hv] at hv'; simpa using hv'.symm
  subst e
  simp only [if_true, Bool.false_eq_true, if_false] at hvv'
  refine ⟨v', hv, hvv, fun u hu => hs u ?_, ?_⟩
  · rw [hvv'] at hu; exact mem_rtrimU_sub _ _ hu
  · rw [hvv']; unfold rtrimU; simp only [List.length_reverse]
    exact (List.dropWhile_suffix _).length_le.trans (by simp)

open LegacyBeatmapDecoder in
/-- One iteration of the `parseLines` loop. -/
def dec_plStep (s : DecoderState) (line0 : String) : DecoderState :=
  if shouldSkipLine line0 then s else
  let line1 := if s.sect != 2 then stripComments line0 else line0
  let line := trimEnd line1
  if line.startsWith "[" && line.endsWith "]" then
    { s with sect := (enumTryParse sectionNames (String.ofList ((line.toList.drop 1).dropLast))).getD 0 }
  else parseLine s line

theorem dec_parseLines_eq (s0 : DecoderState) (lines : _root_.Array String) :
    LegacyBeatmapDecoder.parseLines s0 lines =
      iterR (fun j s => .yield (dec_plStep s lines[j]!)) 0 lines.size s0 := by
  unfold LegacyBeatmapDecoder.parseLines
  simp only [Id.run]
  rw [forIn_array_iterR]
  refine congrArg (fun f => iterR f 0 lines.size s0) (funext fun j => funext fun acc => ?_)
  simp only [dec_plStep]
  split_ifs <;> rfl

theorem dec_litS1 (n : Usize) (l : List U8) (h : l.length = n.val) :
    String.ofList (litS (Array.to_slice (Array.make n l h))) = String.ofList (l.map (fun b : U8 => Char.ofNat b.val)) := by
  simp [litS, Array.to_slice, Array.make, Array.from_val, Slice.from_val]

theorem dec_lb : String.ofList (([91#u8] : List U8).map (fun b : U8 => Char.ofNat b.val)) = "[" := by decide
theorem dec_rb : String.ofList (([93#u8] : List U8).map (fun b : U8 => Char.ofNat b.val)) = "]" := by decide

theorem dec_inner_eq (v : alloc.vec.Vec U32) (hv : 2 ≤ v.val.length) (w : alloc.vec.Vec U32)
    (hw : w.val = (v.val.drop 1).take (v.val.length - 1 - 1)) :
    strV w = String.ofList (((strV v).toList.drop 1).dropLast) := by
  simp only [strV, String.toList_ofList, hw]
  congr 1
  rw [List.dropLast_eq_take, ← List.map_drop, ← List.map_take]
  simp

theorem dec_pl_step (lines : Slice (alloc.vec.Vec U32)) (s : beatmap.decoder.DecoderState) (k : Usize)
    (hk : k.val < lines.val.length) (hV : ∀ l ∈ lines.val, ValidL l.val) (h64 : System.Platform.numBits = 64)
    (N : Nat) (hN : N ≤ 2^61) (hL : ∀ l ∈ lines.val, l.val.length < N) (hpath : dec_pathOk N)
    (n : Nat) (hsz : dec_szOk s (n+1)) :
    ∃ s2 k1, beatmap.decoder.parse_lines_loop.body lines s k = ok (.cont (s2, k1)) ∧ k1.val = k.val + 1 ∧
      dec_dsS s2 = dec_plStep (dec_dsS s) (strV (lines.val[k.val]'hk)) ∧ dec_szOk s2 n := by
  have hmx : lines.val.length ≤ Usize.max := lines.property
  have hk' : k < Slice.len lines := by show k.val < (Slice.len lines).val; simpa using hk
  have hm := List.getElem_mem hk
  set L0 := lines.val[k.val]'hk with hL0
  have hL0V := hV L0 hm
  have hL0L := hL L0 hm
  obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by omega)
  unfold beatmap.decoder.parse_lines_loop.body
  simp only [hk', ite_true, index_eq lines k hk, bind_ok]
  rw [beatmap.decoder.should_skip_line_refines _ (validStr_of L0 hL0V), bind_ok, strV_deref]
  by_cases hsk : LegacyBeatmapDecoder.shouldSkipLine (strV L0) = true
  · simp only [hsk, ite_true, bind_ok, hk1]
    exact ⟨s, k1, rfl, hk1v, by simp [dec_plStep, hsk], dec_szOk_mono s n hsz⟩
  · simp only [hsk, Bool.false_eq_true, ite_false]
    have hsect : (s.sect != 2#i32) = ((dec_dsS s).sect != 2) := by
      rw [hop_bne_i32S]; rfl
    obtain ⟨line1, hl1, hl1v, hl1j⟩ : ∃ line1, (if (s.sect != 2#i32) = true then
        beatmap.decoder.strip_comments (alloc.vec.Vec.deref (lines.val[k.val]'hk))
        else beatmap.dotnet.sub_str (alloc.vec.Vec.deref (lines.val[k.val]'hk)) 0#usize (alloc.vec.Vec.len (lines.val[k.val]'hk))) = ok line1 ∧
        strV line1 = (if ((dec_dsS s).sect != 2) = true then LegacyBeatmapDecoder.stripComments (strV L0) else strV L0) ∧
        ∃ j, line1.val = L0.val.take j := by
      by_cases hc : (s.sect != 2#i32) = true
      · rw [if_pos hc]
        obtain ⟨v, hv, hvv, hvj⟩ := dec_sc_full (alloc.vec.Vec.deref L0)
        refine ⟨v, hv, ?_, by simpa [deref_valA] using hvj⟩
        rw [← hsect, if_pos hc, hvv, strV_deref]
      · rw [if_neg hc]
        obtain ⟨v, hv, hvv⟩ := beatmap.dotnet.sub_str_refines (alloc.vec.Vec.deref L0) 0#usize (alloc.vec.Vec.len L0) (by simp) (by simp)
        refine ⟨v, hv, ?_, L0.val.length, by simp [hvv]⟩
        rw [← hsect, if_neg hc]; simp [strV, hvv]
    simp only [hl1, bind_ok]
    have hl1V : ValidL line1.val := by
      obtain ⟨j, hj⟩ := hl1j; intro u hu; rw [hj] at hu; exact hL0V u (List.mem_of_mem_take hu)
    have hl1L : line1.val.length ≤ L0.val.length := by
      obtain ⟨j, hj⟩ := hl1j; rw [hj]; simp
    obtain ⟨line, hl, hlv, hlV, hll⟩ := dec_te_full (alloc.vec.Vec.deref line1) (validStr_of line1 hl1V)
    rw [strV_deref] at hlv
    simp only [hl, bind_ok, lift]
    rw [beatmap.dotnet.starts_with_refines _ (validStr_of line hlV), bind_ok, dec_litS1, dec_lb, strV_deref]
    rw [beatmap.dotnet.ends_with_refines _ (validStr_of line hlV), bind_ok, dec_litS1, dec_rb, strV_deref]
    have hspec : dec_plStep (dec_dsS s) (strV L0) =
        if ((strV line).startsWith "[" && (strV line).endsWith "]") = true then
          { dec_dsS s with sect := (enumTryParse sectionNames (String.ofList (((strV line).toList.drop 1).dropLast))).getD 0 }
        else LegacyBeatmapDecoder.parseLine (dec_dsS s) (strV line) := by
      unfold dec_plStep; rw [if_neg hsk]; simp only []; rw [← hl1v, ← hlv]
    have hlenL : line.val.length < N := by have := hll; rw [deref_valA] at this; omega
    have hPL : ∃ s', beatmap.decoder.parse_line s (alloc.vec.Vec.deref line) = ok s' ∧
        dec_dsS s' = LegacyBeatmapDecoder.parseLine (dec_dsS s) (strV line) ∧ dec_szOk s' n := by
      obtain ⟨s', hs', hs'v, hsz', -⟩ := beatmap.decoder.parse_line_refines s (alloc.vec.Vec.deref line)
        (validStr_of line hlV) (by rw [deref_valA]; omega) h64 N hpath (by rw [deref_valA]; exact hlenL) n hsz
      exact ⟨s', hs', by rw [hs'v, strV_deref], hsz'⟩
    obtain ⟨s', hs', hs'v, hsz'⟩ := hPL
    by_cases hb1 : (strV line).startsWith "[" = true
    · by_cases hb2 : (strV line).endsWith "]" = true
      · simp only [hb1, hb2, ite_true]
        obtain ⟨inner, hin, hinv, hinV, hinL⟩ : ∃ inner, (if alloc.vec.Vec.len line ≥ 2#usize then (do
              let i3 ← alloc.vec.Vec.len line - 1#usize
              beatmap.dotnet.sub_str (alloc.vec.Vec.deref line) 1#usize i3) else ok (alloc.vec.Vec.new U32)) = ok inner ∧
            strV inner = String.ofList (((strV line).toList.drop 1).dropLast) ∧ ValidL inner.val ∧
            inner.val.length ≤ line.val.length := by
          by_cases h2 : 2 ≤ line.val.length
          · have h2' : alloc.vec.Vec.len line ≥ 2#usize := by show (2#usize : Usize).val ≤ (alloc.vec.Vec.len line).val; simpa using h2
            obtain ⟨i3, hi3, hi3v⟩ := usize_sub_one (alloc.vec.Vec.len line) (by simp; omega)
            obtain ⟨w, hw, hwv⟩ := beatmap.dotnet.sub_str_refines (alloc.vec.Vec.deref line) 1#usize i3 (by simp at hi3v ⊢; omega)
              (by simp at hi3v ⊢; omega)
            refine ⟨w, by rw [if_pos h2', hi3, bind_ok, hw], dec_inner_eq line h2 w (by simp [hwv, hi3v]),
              fun u hu => hlV u ?_, by rw [hwv]; simp⟩
            rw [hwv] at hu; simp at hu; exact List.mem_of_mem_tail (List.mem_of_mem_take hu)
          · have h2' : ¬ alloc.vec.Vec.len line ≥ 2#usize := by show ¬ (2#usize : Usize).val ≤ (alloc.vec.Vec.len line).val; simpa using h2
            refine ⟨alloc.vec.Vec.new U32, by rw [if_neg h2'], ?_, by intro u hu; simp at hu, by simp⟩
            have : ((strV line).toList.drop 1).dropLast = [] := by
              simp only [strV, String.toList_ofList]
              have : (List.drop 1 (line.val.map chOf)).length ≤ 1 := by simp; omega
              rcases h : List.drop 1 (line.val.map chOf) with _ | ⟨a, _ | ⟨b, t⟩⟩
              · rfl
              · rfl
              · rw [h] at this; simp at this
            rw [this]; simp [strV]
        simp only [hin, bind_ok]
        obtain ⟨o, ho, hov⟩ := beatmap.dotnet.enum_try_parse_refines beatmap.names.T_SECTION (alloc.vec.Vec.deref inner)
          (validStr_of inner hinV) (by rw [deref_valA, hop_umax64 h64]; omega)
        have hT : enumTable beatmap.names.T_SECTION.val = sectionNames := by unfold beatmap.names.T_SECTION; rfl
        rw [hT, strV_deref, hinv] at hov
        simp only [ho, bind_ok]
        rw [hspec, if_pos (by simp [hb1, hb2])]
        cases o with
        | none =>
          simp only [bind_ok, hk1]
          refine ⟨_, k1, rfl, hk1v, ?_, ?_⟩
          · rw [← hov]; simp [dec_dsS]; decide
          · exact dec_szOk_mono s n hsz
        | some x =>
          simp only [bind_ok, hk1]
          refine ⟨_, k1, rfl, hk1v, ?_, ?_⟩
          · rw [← hov]; simp [dec_dsS]
          · exact dec_szOk_mono s n hsz
      · simp only [hb1, hb2, ite_true, Bool.false_eq_true, ite_false, hs', bind_ok, hk1]
        refine ⟨s', k1, rfl, hk1v, ?_, hsz'⟩
        rw [hspec, if_neg (by simp [hb2]), hs'v]
    · simp only [hb1, Bool.false_eq_true, ite_false, hs', bind_ok, hk1]
      refine ⟨s', k1, rfl, hk1v, ?_, hsz'⟩
      rw [hspec, if_neg (by simp [hb1]), hs'v]

theorem beatmap.decoder.parse_lines_refines (s : beatmap.decoder.DecoderState) (lines : Slice (alloc.vec.Vec U32))
    (hV : ∀ l ∈ lines.val, ValidL l.val) (h64 : System.Platform.numBits = 64)
    (N : Nat) (hN : N ≤ 2^61) (hL : ∀ l ∈ lines.val, l.val.length < N) (hpath : dec_pathOk N)
    (hsz : dec_szOk s lines.val.length) :
    ∃ s', beatmap.decoder.parse_lines s lines = ok s' ∧
      dec_dsS s' = LegacyBeatmapDecoder.parseLines (dec_dsS s) (vstrs lines.val) ∧ dec_szOk s' 0 := by
  unfold beatmap.decoder.parse_lines beatmap.decoder.parse_lines_loop
  rw [dec_parseLines_eq, vstrs_size]
  have hmx : lines.val.length ≤ Usize.max := lines.property
  have := loop_iterR (fun (t : beatmap.decoder.DecoderState × Usize) => beatmap.decoder.parse_lines_loop.body lines t.1 t.2)
    (fun j S => .yield (dec_plStep S (vstrs lines.val)[j]!)) lines.val.length (fun t => t.2.val)
    (fun t S => dec_dsS t.1 = S ∧ dec_szOk t.1 (lines.val.length - t.2.val) ∧ t.2.val ≤ lines.val.length)
    (fun y S => dec_dsS y = S ∧ dec_szOk y 0)
    (by
      rintro ⟨st, k⟩ S ⟨rfl, hz, hkl⟩ hk
      dsimp only at hz hkl hk ⊢
      constructor
      · intro s' hs'
        cases hs'
        have e : lines.val.length - k.val = (lines.val.length - k.val - 1) + 1 := by omega
        rw [e] at hz
        obtain ⟨s2, k1, hb, hk1, hs2, hz2⟩ := dec_pl_step lines st k hk hV h64 N hN hL hpath _ hz
        refine ⟨(s2, k1), hb, hk1, ?_, ?_, ?_⟩
        · rw [hs2, vstrs_get! _ _ hk]
        · dsimp only; rw [hk1]; have : lines.val.length - (k.val + 1) = lines.val.length - k.val - 1 := by omega
          rw [this]; exact hz2
        · dsimp only; omega
      · intro s' hs'; cases hs')
    (by
      rintro ⟨st, k⟩ S ⟨rfl, hz, hkl⟩ hk
      dsimp only at hz hkl hk ⊢
      have hk' : ¬ k < Slice.len lines := by show ¬ k.val < (Slice.len lines).val; simp; omega
      refine ⟨st, by simp [beatmap.decoder.parse_lines_loop.body, hk'], rfl, ?_⟩
      have : lines.val.length - k.val = 0 := by omega
      rw [this] at hz; exact hz)
    (s, 0#usize) (dec_dsS s) ⟨rfl, by simpa using hsz, by simp⟩ (by simp)
  obtain ⟨y, hy, hq1, hq2⟩ := this
  refine ⟨y, hy, ?_, hq2⟩
  simpa using hq1

theorem dec_merge_map {α β : Type} (f : α → β) (key : β → F64) : ∀ (fuel : Nat) (xs ys : List α),
    stableSortBy.merge key (xs.map f) (ys.map f) fuel = (stableSortBy.merge (key ∘ f) xs ys fuel).map f := by
  intro fuel
  induction fuel with
  | zero => intro xs ys; simp [stableSortBy.merge]
  | succ n ih =>
    intro xs ys
    cases xs with
    | nil => cases ys <;> simp [stableSortBy.merge]
    | cons x xs' =>
      cases ys with
      | nil => simp [stableSortBy.merge]
      | cons y ys' =>
        simp only [List.map_cons, stableSortBy.merge, Function.comp]
        split
        · rw [← List.map_cons, ih]; simp
        · rw [← List.map_cons, ih]; simp

theorem dec_sort_map {α β : Type} (f : α → β) (key : β → F64) : ∀ (fuel : Nat) (xs : List α),
    stableSortBy.sort key (xs.map f) fuel = (stableSortBy.sort (key ∘ f) xs fuel).map f := by
  intro fuel
  induction fuel with
  | zero => intro xs; simp [stableSortBy.sort]
  | succ n ih =>
    intro xs
    simp only [stableSortBy.sort, List.length_map]
    split
    · rfl
    · rw [← List.map_take, ← List.map_drop, ih, ih, dec_merge_map]

theorem dec_stableSortBy_map {α β : Type} (f : α → β) (key : β → F64) (a : _root_.Array α) :
    stableSortBy key (a.map f) = (stableSortBy (key ∘ f) a).map f := by
  unfold stableSortBy
  simp only [Array.toList_map, Array.size_map]
  rw [dec_sort_map]; simp

theorem dec_ck_clone (k : beatmap.types.ConvertKind) :
    beatmap.types.ConvertKind.Insts.CoreCloneClone.clone k = ok k := by
  cases k with
  | Circle => rfl
  | Slider c o r =>
    cases o <;> simp [beatmap.types.ConvertKind.Insts.CoreCloneClone.clone, hop_pcp_clone,
      core.option.Option.Insts.CoreCloneClone.clone, float.F64.Insts.CoreCloneClone.clone, lift,
      core.clone.impls.CloneI32.clone]
  | Spinner d => simp [beatmap.types.ConvertKind.Insts.CoreCloneClone.clone, float.F64.Insts.CoreCloneClone.clone]
  | Hold d => simp [beatmap.types.ConvertKind.Insts.CoreCloneClone.clone, float.F64.Insts.CoreCloneClone.clone]

theorem dec_cho_clone1 (x : beatmap.types.ConvertHitObject) :
    beatmap.types.ConvertHitObject.Insts.CoreCloneClone.clone x = ok x := by
  simp [beatmap.types.ConvertHitObject.Insts.CoreCloneClone.clone, float.F64.Insts.CoreCloneClone.clone,
    net.osutk.Vector2.Insts.CoreCloneClone.clone, lift, core.clone.impls.CloneBool.clone,
    core.clone.impls.CloneI32.clone, dec_ck_clone]

theorem dec_cho_clone (v : alloc.vec.Vec beatmap.types.ConvertHitObject) :
    alloc.vec.CloneVec.clone beatmap.types.ConvertHitObject.Insts.CoreCloneClone v = ok v := by
  obtain ⟨s, hs, hsv⟩ := eq_ok_of_spec (Slice.clone_spec (clone := beatmap.types.ConvertHitObject.Insts.CoreCloneClone.clone)
    (s := v.slice) (by intro x _; exact dec_cho_clone1 x))
  simp only [alloc.vec.CloneVec.clone, beatmap.types.ConvertHitObject.Insts.CoreCloneClone, hs, bind_ok, ← hsv]
  rw [bind_tc_ok]

theorem dec_psi_loop (cpi : beatmap.control_points.ControlPointInfo) (hc : cpi.difficulty_points.val.length < 2^31) :
    ∀ j (hos : alloc.vec.Vec beatmap.types.ConvertHitObject) (i : Usize), i.val + j = hos.val.length →
      ∃ r, beatmap.decoder.parse_stream_into_loop cpi hos i = ok r ∧
        r.val.map choS = (hos.val.take i.val).map choS ++
          (hos.val.drop i.val).map (fun h => LegacyBeatmapDecoder.applyDecodeDefaults (cpS cpi) (choS h)) := by
  intro j
  induction j with
  | zero =>
    intro hos i hi
    have hn : ¬ i < alloc.vec.Vec.len hos := by show ¬ i.val < (alloc.vec.Vec.len hos).val; simp; omega
    refine ⟨hos, ?_, ?_⟩
    · unfold beatmap.decoder.parse_stream_into_loop
      rw [loop_unfold]; simp [beatmap.decoder.parse_stream_into_loop.body, hn]
    · rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega)]; simp
  | succ j ih =>
    intro hos i hi
    have hil : i.val < hos.val.length := by omega
    have hn : i < alloc.vec.Vec.len hos := by show i.val < (alloc.vec.Vec.len hos).val; simpa using hil
    have hmx : hos.val.length ≤ Usize.max := hos.property
    obtain ⟨h', hh', hh'v, -⟩ := beatmap.decoder.apply_decode_defaults_refines cpi (hos.val[i.val]'hil) hc
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
    have hb : beatmap.decoder.parse_stream_into_loop.body cpi hos i = ok (.cont (alloc.vec.Vec.set hos i h', i1)) := by
      simp [beatmap.decoder.parse_stream_into_loop.body, hn, vec_index_mut_eq hos i hil, hh', hi1]
    obtain ⟨r, hr, hrv⟩ := ih (alloc.vec.Vec.set hos i h') i1 (by simp [vec_set_val']; omega)
    refine ⟨r, ?_, ?_⟩
    · unfold beatmap.decoder.parse_stream_into_loop
      rw [loop_unfold]; simp only [hb, bind_ok]
      unfold beatmap.decoder.parse_stream_into_loop at hr
      simpa using hr
    · rw [hrv, hi1v, vec_set_val']
      rw [List.take_succ, List.drop_set_of_lt (by omega)]
      rw [List.drop_eq_getElem_cons hil]
      simp [List.take_set_of_le, List.getElem?_set_self (show i.val < hos.val.length from hil), hh'v]
      rw [List.drop_eq_getElem_cons (show i.val < (List.map (fun h => LegacyBeatmapDecoder.applyDecodeDefaults (cpS cpi) (choS h)) hos.val).length by simp; omega)]
      simp

def dec_dbS (d : beatmap.types.DecodedBeatmap) : DecodedBeatmap :=
  { formatVersion := i32S d.format_version, rulesetId := i32S d.ruleset_id, difficulty := dec_diffS d.difficulty,
    stackLeniency := d.stack_leniency, audioLeadIn := d.audio_lead_in, controlPoints := cpS d.control_points,
    breaks := (d.breaks.val.map dec_bpS).toArray, hitObjects := (d.hit_objects.val.map choS).toArray }

theorem beatmap.decoder.parse_stream_into_refines (fv : I32) (lines : Slice (alloc.vec.Vec U32))
    (hV : ∀ l ∈ lines.val, ValidL l.val) (h64 : System.Platform.numBits = 64)
    (N : Nat) (hN : N ≤ 2^61) (hL : ∀ l ∈ lines.val, l.val.length < N) (hpath : dec_pathOk N)
    (hn : lines.val.length + 1 < 2^31) :
    ∃ d, beatmap.decoder.parse_stream_into fv lines = ok d ∧
      dec_dbS d = LegacyBeatmapDecoder.parseStreamInto (i32S fv) (vstrs lines.val) := by
  unfold beatmap.decoder.parse_stream_into LegacyBeatmapDecoder.parseStreamInto
  have hoff : (if fv < 5#i32 then ok beatmap.decoder.EARLY_VERSION_TIMING_OFFSET else ok 0#i32 : Result I32) =
      ok (if fv < 5#i32 then beatmap.decoder.EARLY_VERSION_TIMING_OFFSET else 0#i32) := by split <;> rfl
  have hsl : float.F32.from_bits 1060320051#u32 = ok (0.7 : F32) := by simp; decide
  have hD0 : beatmap.decoder.D0 = ok (0 : F64) := by unfold beatmap.decoder.D0; simp; decide
  simp only [hoff, bind_ok, hsl, beatmap.control_points.cpi_empty, hD0, lift]
  generalize hoffd : (if fv < 5#i32 then beatmap.decoder.EARLY_VERSION_TIMING_OFFSET else 0#i32) = off
  have hoffS : (if i32S fv < 5 then OsuModel.Beatmap.EARLY_VERSION_TIMING_OFFSET else 0) = i32S off := by
    rw [← hoffd]
    have h5 : (fv < 5#i32) ↔ (i32S fv < 5) := by
      rw [Int32.lt_iff_toInt_lt, i32S_toInt]; show fv.val < (5#i32 : I32).val ↔ _; simp
    by_cases h : fv < 5#i32
    · rw [if_pos h, if_pos (h5.mp h)]; simp [beatmap.decoder.EARLY_VERSION_TIMING_OFFSET, OsuModel.Beatmap.EARLY_VERSION_TIMING_OFFSET, i32S]
    · rw [if_neg h, if_neg (fun h' => h (h5.mpr h'))]; decide
  rw [hoffS]
  have hcast : (IScalar.cast .I64 off).val = off.val := by
    first | simp [IScalar.cast_val_eq] | (rw [IScalar.cast_val_eq]; simp; omega) | scalar_tac
  have hfi : float.F64.from_i64 (IScalar.cast .I64 off) = ok (F64.ofInt (i32S off).toInt) := by
    simp only [float.F64.from_i64, hcast, i32S_toInt]
  have hdd : ∃ d0, beatmap.types.DIFFICULTY_DEFAULT = ok d0 ∧ dec_diffS d0 = {} := by
    unfold beatmap.types.DIFFICULTY_DEFAULT
    simp only [float.F32.from_bits, float.F64.from_bits, bind_ok]
    exact ⟨_, rfl, by simp only [dec_diffS]; congr 1 <;> decide⟩
  obtain ⟨d0, hd0, hd0v⟩ := hdd
  simp only [hfi, bind_ok, hd0]
  generalize hS0 : ({ formatVersion := i32S fv, offset := i32S off, parser := { offset := F64.ofInt (i32S off).toInt, formatVersion := i32S fv } } : DecoderState) = S0
  generalize hs0 : ({ format_version := fv, offset := off, sect := 0#i32, ruleset_id := 0#i32, stack_leniency := 0.7, audio_lead_in := 0, difficulty := d0, has_approach_rate := false, cpi := { timing_points := alloc.vec.Vec.new beatmap.control_points.TimingPoint, difficulty_points := alloc.vec.Vec.new beatmap.control_points.DifficultyPoint, effect_points := alloc.vec.Vec.new beatmap.control_points.EffectPoint }, pending := { timing := alloc.vec.Vec.new beatmap.control_points.TimingPoint, difficulty := alloc.vec.Vec.new beatmap.control_points.DifficultyPoint, effect := alloc.vec.Vec.new beatmap.control_points.EffectPoint, time := 0 }, breaks := alloc.vec.Vec.new beatmap.types.BreakPeriod, parser := { offset := F64.ofInt (i32S off).toInt, format_version := fv, first_object := true, last_object_is_spinner := false }, hit_objects := alloc.vec.Vec.new beatmap.types.ConvertHitObject } : beatmap.decoder.DecoderState) = s0
  have hds0 : dec_dsS s0 = S0 := by
    rw [← hs0, ← hS0]; simp only [dec_dsS, cpS, dec_pendS, hd0v, psS]; simp; decide
  have hsz0 : dec_szOk s0 lines.val.length := by
    rw [← hs0]; unfold dec_szOk dec_cpiOk; simp; omega
  obtain ⟨s, hs, hsv, hsz⟩ := beatmap.decoder.parse_lines_refines s0 lines hV h64 N hN hL hpath hsz0
  rw [hds0] at hsv
  simp only [hs, bind_ok]
  obtain ⟨dr, hdr, hdrv⟩ := beatmap.decoder.apply_difficulty_restrictions_refines s.difficulty s.ruleset_id
  simp only [hdr, bind_ok]
  obtain ⟨hc1, -, -, -, -, hho⟩ := hsz
  obtain ⟨c', hfl, hflv, hc'⟩ := beatmap.decoder.flush_pending_points_refines s 0 hc1
  simp only [hfl, bind_ok, dec_cho_clone]
  obtain ⟨hos1, hsort, hsortv⟩ := beatmap.dotnet.stable_sort_by_refines beatmap.types.ConvertHitObject.Insts.CoreCloneClone
    dec_cho_clone1 beatmap.types.ConvertHitObject.Insts.Osu_eval_coreBeatmapDotnetSortKey (fun h => h.start_time)
    (fun x => rfl) s.hit_objects (by omega)
  simp only [hsort, bind_ok]
  obtain ⟨hos2, hpp, hppv⟩ := beatmap.decoder.post_process_breaks_refines (alloc.vec.Vec.deref s.breaks) hos1
  simp only [hpp, bind_ok]
  obtain ⟨hos3, hl, hlv⟩ := dec_psi_loop c' (by unfold dec_cpiOk at hc'; omega) hos2.val.length hos2 0#usize (by simp)
  simp only [hl, bind_ok]
  refine ⟨_, rfl, ?_⟩
  rw [← hsv, ← hflv]
  simp only [dec_dbS]
  rw [DecodedBeatmap.mk.injEq]
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · rw [hdrv]; rfl
  · simp only [dec_dsS]
    have e1 : (s.hit_objects.val.map choS).toArray = s.hit_objects.val.toArray.map choS := by simp
    rw [e1, dec_stableSortBy_map]
    have e2 : ((fun h : ConvertHitObject => h.startTime) ∘ choS) = (fun h => h.start_time) := rfl
    rw [e2, ← hsortv]
    have e3 : hos1.val.toArray.map choS = (hos1.val.map choS).toArray := by simp
    rw [e3]
    have e4 : (s.breaks.val.map dec_bpS).toArray = dec_bpsA (alloc.vec.Vec.deref s.breaks) := by
      simp [dec_bpsA, deref_valA]
    rw [e4, ← hppv]
    have h0z : (0#usize : Usize).val = 0 := rfl
    rw [h0z] at hlv
    simp only [List.take_zero, List.nil_append, List.drop_zero, List.map_nil] at hlv
    simp [hlv, Function.comp_def]

theorem dec_trim_empty (l : alloc.vec.Vec U32) (hl : ValidL l.val) :
    ∃ v, beatmap.dotnet.trim (alloc.vec.Vec.deref l) = ok v ∧ (v.val.length = 0 ↔ (trim (strV l)).isEmpty = true) ∧
      strV v = trim (strV l) ∧ ValidL v.val := by
  obtain ⟨v, hv, hvv, hvV⟩ := trim_valid (alloc.vec.Vec.deref l) (validStr_of l hl)
  rw [strV_deref] at hvv
  refine ⟨v, hv, ?_, hvv, hvV⟩
  rw [← hvv, String.isEmpty_iff]
  constructor
  · intro h; rw [List.length_eq_zero_iff.mp h]; rfl
  · intro h; have := congrArg String.length h; simpa using this

theorem dec_decode_loop (lines : alloc.vec.Vec (alloc.vec.Vec U32)) (hV : ∀ l ∈ lines.val, ValidL l.val) :
    ∀ j (k : Usize) (hkj : k.val + j = lines.val.length),
      (∀ p (hp : p < k.val), (trim (strV (lines.val[p]'(by omega)))).isEmpty = true) →
      ∃ r, beatmap.decoder.decode_loop lines k false = ok r ∧
        r.val = ((linesS lines).findIdx? (fun l => !(trim l).isEmpty)).getD (linesS lines).size := by
  have hmx : lines.val.length ≤ Usize.max := lines.property
  intro j
  induction j with
  | zero =>
    intro k hk hall
    have hn : ¬ k < alloc.vec.Vec.len lines := by show ¬ k.val < (alloc.vec.Vec.len lines).val; simp; omega
    refine ⟨k, ?_, ?_⟩
    · unfold beatmap.decoder.decode_loop; rw [loop_unfold]
      simp [beatmap.decoder.decode_loop.body, hn]
    · have : (linesS lines).findIdx? (fun l => !(trim l).isEmpty) = none := by
        rw [Array.findIdx?_eq_none_iff]
        intro x hx
        simp only [linesS, List.mem_toArray, List.mem_map] at hx
        obtain ⟨l, hl, rfl⟩ := hx
        obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hl
        simp [hall p (by omega)]
      rw [this]; simp [linesS]; omega
  | succ j ih =>
    intro k hk hall
    have hkl : k.val < lines.val.length := by omega
    have hn : k < alloc.vec.Vec.len lines := by show k.val < (alloc.vec.Vec.len lines).val; simpa using hkl
    have hm := List.getElem_mem hkl
    obtain ⟨v, hv, hvE, -, -⟩ := dec_trim_empty _ (hV _ hm)
    by_cases he : (trim (strV (lines.val[k.val]'hkl))).isEmpty = true
    · have hne : ¬ (alloc.vec.Vec.len v != 0#usize) = true := by
        simp only [bne_iff_ne, ne_eq, Decidable.not_not]
        apply UScalar.eq_of_val_eq; simpa using hvE.mpr he
      obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by omega)
      have hb : beatmap.decoder.decode_loop.body lines k false = ok (.cont (k1, false)) := by
        have hve : v.val = [] := List.length_eq_zero_iff.mp (hvE.mpr he)
        simp [beatmap.decoder.decode_loop.body, hn, vec_index_eq' lines k hkl, hv, hne, hk1, hve]
      obtain ⟨r, hr, hrv⟩ := ih k1 (by omega) (by
        intro p hp
        by_cases hpk : p < k.val
        · exact hall p hpk
        · have : p = k.val := by omega
          subst this; exact he)
      refine ⟨r, ?_, hrv⟩
      unfold beatmap.decoder.decode_loop; rw [loop_unfold]; simp only [hb, bind_ok]
      unfold beatmap.decoder.decode_loop at hr; simpa using hr
    · have hne : (alloc.vec.Vec.len v != 0#usize) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro h; apply he; apply hvE.mp; have := congrArg UScalar.val h; simpa using this
      have hb : beatmap.decoder.decode_loop.body lines k false = ok (.cont (k, true)) := by
        have hve : ¬ v.val = [] := by intro h; apply he; apply hvE.mp; simp [h]
        simp [beatmap.decoder.decode_loop.body, hn, vec_index_eq' lines k hkl, hv, hne, hve]
      have hb2 : beatmap.decoder.decode_loop.body lines k true = ok (.done k) := by
        simp [beatmap.decoder.decode_loop.body]
      refine ⟨k, ?_, ?_⟩
      · unfold beatmap.decoder.decode_loop; rw [loop_unfold]; simp only [hb, bind_ok]
        rw [loop_unfold]; simp only [hb2, bind_ok]
      · have : (linesS lines).findIdx? (fun l => !(trim l).isEmpty) = some k.val := by
          rw [Array.findIdx?_eq_some_iff_getElem]
          refine ⟨by simp [linesS]; exact hkl, by simp [linesS, he], ?_⟩
          intro p hp; simp [linesS, hall p hp]
        rw [this]; rfl

theorem beatmap.decoder.decode_refines (bytes : Slice U8) (hb : bytes.val.length < Usize.max)
    (h64 : System.Platform.numBits = 64) (N : Nat) (hN : N ≤ 2^61) (hpath : dec_pathOk N)
    (hsize : ∀ cs, streamReaderDecode (bytesS bytes) = some cs →
      (readLines cs).size + 1 < 2^31 ∧ ∀ L ∈ readLines cs, L.length < N) :
    ∃ r, beatmap.decoder.decode bytes = ok r ∧
      hRel dec_dbS r (LegacyBeatmapDecoder.decode (bytesS bytes)) := by
  obtain ⟨o, ho, hov, hoV⟩ := beatmap.text.stream_reader_decode_refines bytes hb
  unfold beatmap.decoder.decode LegacyBeatmapDecoder.decode
  rw [← hov]
  simp only [ho, bind_ok]
  cases o with
  | none => exact ⟨_, rfl, trivial⟩
  | some c =>
    have hcV := hoV c rfl
    simp only [optS, Option.map_some]
    obtain ⟨lines, hl, hlv, hlV⟩ := beatmap.text.read_lines_refines (alloc.vec.Vec.deref c) (validStr_of c hcV)
    have hcs : (strS (alloc.vec.Vec.deref c)).toArray = (c.val.map chOf).toArray := by simp [strS, deref_valA]
    rw [hcs] at hlv
    obtain ⟨hsz1, hsz2⟩ := hsize _ (by rw [← hov]; rfl)
    rw [← hlv] at hsz1 hsz2 ⊢
    simp only [hl, bind_ok]
    have hLsz : (linesS lines).size = lines.val.length := by simp [linesS]
    obtain ⟨k, hk, hkv⟩ := dec_decode_loop lines hlV lines.val.length 0#usize (by simp) (by intro p hp; simp at hp)
    simp only [hk, bind_ok]
    rw [← hkv, hLsz]
    have hmx : lines.val.length ≤ Usize.max := lines.property
    by_cases hge : k.val ≥ lines.val.length
    · have hge' : k ≥ alloc.vec.Vec.len lines := by show (alloc.vec.Vec.len lines).val ≤ k.val; simpa using hge
      rw [if_pos hge', if_pos hge]
      exact ⟨_, rfl, trivial⟩
    · have hge' : ¬ k ≥ alloc.vec.Vec.len lines := by show ¬ (alloc.vec.Vec.len lines).val ≤ k.val; simpa using hge
      rw [if_neg hge', if_neg hge]
      have hkl : k.val < lines.val.length := by omega
      have hm := List.getElem_mem hkl
      obtain ⟨first, hf, -, hfv, hfV⟩ := dec_trim_empty _ (hlV _ hm)
      have hgetL : (linesS lines)[k.val]! = strV (lines.val[k.val]'hkl) := by
        rw [getElem!_pos _ _ (by rw [hLsz]; exact hkl)]; simp [linesS]
      rw [hgetL, ← hfv]
      have hrest : alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice (alloc.vec.Vec U32)) lines { start := k } =
          ok (Slice.drop lines.slice k) := by
        have hsl : lines.slice.val.length = lines.val.length := rfl
        simp [alloc.vec.Vec.index, core.slice.index.SliceIndexRangeFromUsizeSlice.index, Slice.length]; omega
      simp only [vec_index_eq' lines k hkl, bind_ok, hf, hrest, lift]
      have hrestv : (Slice.drop lines.slice k).val = lines.val.drop k.val := by simp [Slice.drop]; rfl
      have hrestS : vstrs (Slice.drop lines.slice k).val = (linesS lines).extract k.val lines.val.length := by
        rw [hrestv]; simp [vstrs, linesS, List.map_drop]
      rw [← hrestS]
      have hrV : ∀ l ∈ (Slice.drop lines.slice k).val, ValidL l.val := by
        intro l hl; rw [hrestv] at hl; exact hlV l (List.mem_of_mem_drop hl)
      have hrL : ∀ l ∈ (Slice.drop lines.slice k).val, l.val.length < N := by
        intro l hl; rw [hrestv] at hl
        have := hsz2 (strV l) (by simp [linesS]; exact ⟨l, List.mem_of_mem_drop hl, rfl⟩)
        simpa [strV] using this
      have hrn : (Slice.drop lines.slice k).val.length + 1 < 2^31 := by
        rw [hrestv]; simp; rw [hLsz] at hsz1; omega
      rw [beatmap.dotnet.starts_with_refines _ (validStr_of first hfV), bind_ok, dec_litS1, strV_deref]
      have hosu : String.ofList (([111#u8, 115#u8, 117#u8, 32#u8, 102#u8, 105#u8, 108#u8, 101#u8, 32#u8, 102#u8, 111#u8,
          114#u8, 109#u8, 97#u8, 116#u8, 32#u8, 118#u8] : List U8).map (fun b : U8 => Char.ofNat b.val)) = "osu file format v" := by decide
      rw [hosu]
      by_cases hb1 : (strV first).startsWith "osu file format v" = true
      · rw [if_pos hb1, if_pos hb1]
        have hfl : first.val.length < Usize.max := by
          have := hsz2 (strV (lines.val[k.val]'hkl)) (by simp [linesS]; exact ⟨_, hm, rfl⟩)
          rw [hop_umax64 h64]; simp [strV] at this
          have hle : first.val.length ≤ (lines.val[k.val]'hkl).val.length := by
            have := dec_trim_len _ (validStr_of _ (hlV _ hm)) first hf; simpa using this
          omega
        obtain ⟨parts, hps, hpsv, hpsV, hpsL⟩ := split_rel (alloc.vec.Vec.deref first) (validStr_of first hfV)
          (by simpa using hfl) 118#u32 (by decide)
        have hvlit : chOf 118#u32 = 'v' := by decide
        rw [hvlit, strV_deref] at hpsv
        have hpne : 0 < parts.val.length := by
          have := congrArg _root_.Array.size hpsv
          rw [vstrs_size] at this; rw [this]
          simp only [split, List.size_toArray, strV]
          rw [splitOn_char]; simp only [List.length_map]
          exact List.length_pos_of_ne_nil (List.splitOn_ne_nil _ _)
        obtain ⟨i2, hi2, hi2v⟩ := usize_sub_one (alloc.vec.Vec.len parts) (by simp; omega)
        have hi2l : i2.val < parts.val.length := by simp at hi2v; omega
        have hpm := List.getElem_mem hi2l
        simp only [hps, bind_ok, hi2, vec_index_eq' parts i2 hi2l]
        have hback : (split (strV first) 'v').back! = strV (parts.val[i2.val]'hi2l) := by
          rw [← hpsv, Array.back!, vstrs_size, vstrs_get! _ _ (by omega)]
          congr 2; simp at hi2v; omega
        rw [hback]
        rw [net.parse.parse_int_default_refines _ (validStr_of _ (hpsV _ hpm)), bind_ok, strV_deref]
        obtain ⟨r1, hr1, hr1r⟩ := lift_net_exceptI beatmap.errors.W_FORMAT_VERSION i32I i32S (fun _ => rfl)
          (Parsing.parseInt (strV (parts.val[i2.val]'hi2l))) "format version"
        simp only [hr1, bind_ok]
        rcases r1 with v1 | e
        · rw [rel_ok hr1r, except_bind_ok]
          obtain ⟨db, hdb, hdbv⟩ := beatmap.decoder.parse_stream_into_refines v1 _ hrV h64 N hN hrL hpath hrn
          simp only [hdb, bind_ok]
          exact ⟨_, rfl, hdbv⟩
        · exact ⟨_, rfl, rel_err hr1r _ _⟩
      · rw [if_neg hb1, if_neg hb1]
        rw [beatmap.dotnet.starts_with_refines _ (validStr_of first hfV), bind_ok, dec_litS1, strV_deref]
        have hbr : String.ofList (([123#u8] : List U8).map (fun b : U8 => Char.ofNat b.val)) = "{" := by decide
        rw [hbr]
        by_cases hb2 : (strV first).startsWith "{" = true
        · rw [if_pos hb2, if_pos hb2]; exact ⟨_, rfl, trivial⟩
        · rw [if_neg hb2, if_neg hb2]
          obtain ⟨db, hdb, hdbv⟩ := beatmap.decoder.parse_stream_into_refines beatmap.decoder.LATEST_VERSION _ hrV h64 N hN
            hrL hpath hrn
          simp only [hdb, bind_ok]
          refine ⟨_, rfl, ?_⟩
          show dec_dbS db = _
          rw [hdbv]
          have hlv : i32S beatmap.decoder.LATEST_VERSION = OsuModel.Beatmap.LATEST_VERSION := by
            simp [beatmap.decoder.LATEST_VERSION, OsuModel.Beatmap.LATEST_VERSION, i32S]
          rw [hlv]

end OsuProofs
