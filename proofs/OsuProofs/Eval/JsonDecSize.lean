/-
Decoded-beatmap size bounds from the `.osu` size bound (json agent, E2E owner): `js_decode_sizes` is
`beatmap.decoder.decode_refines` (Beatmap/Decoder3.lean, copied) with the decoder's size invariant `dec_szOk`
carried to the result: fewer than 2^31 timing / difficulty / effect points and hit objects. Discharges
`LoadBounds.tp/dp/ep/n` of the playable pipeline (Eval/JsonPBounds.lean).
-/
import OsuProofs.Beatmap.Decoder3
import OsuProofs.Post.GenTP3
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

def js_decSz (d : beatmap.types.DecodedBeatmap) : Prop :=
  d.control_points.timing_points.val.length < 2^31 ∧ d.control_points.difficulty_points.val.length < 2^31 ∧
  d.control_points.effect_points.val.length < 2^31 ∧ d.hit_objects.val.length < 2^31

theorem js_forIn_push {α σ : Type} (sz : σ → Nat) (f : α → σ → Id (ForInStep σ))
    (hf : ∀ x r, ∃ r', f x r = ForInStep.yield r' ∧ sz r' = sz r + 1) :
    ∀ (l : List α) (init : σ), sz (Id.run (forIn l init f)) = sz init + l.length := by
  intro l; induction l with
  | nil => intro init; rfl
  | cons x l ih =>
    intro init
    obtain ⟨r', h1, h2⟩ := hf x init
    have := ih r'
    simp only [List.forIn_cons, h1]
    show sz (Id.run (forIn l r' f)) = sz init + (l.length + 1)
    omega

theorem js_forIn_push_arr {α β γ : Type} (F : α → γ × _root_.Array β → Id (ForInStep (γ × _root_.Array β)))
    (hF : ∀ x r, ∃ r', F x r = ForInStep.yield r' ∧ r'.2.size = r.2.size + 1) (a : _root_.Array α) (init : γ × _root_.Array β) :
    (Id.run (forIn a init F)).2.size = init.2.size + a.size := by
  rw [← Array.forIn_toList]
  have := js_forIn_push (fun r : γ × _root_.Array β => r.2.size) F hF a.toList init
  simpa using this

theorem js_ppb_size (breaks : _root_.Array BreakPeriod) (hos : _root_.Array ConvertHitObject) :
    (LegacyBeatmapDecoder.postProcessBreaks breaks hos).size = hos.size := by
  unfold LegacyBeatmapDecoder.postProcessBreaks
  refine Eq.trans (js_forIn_push_arr _ ?hF hos ((0 : Nat), (#[] : _root_.Array ConvertHitObject))) (by simp)
  intro x r
  exact ⟨_, rfl, by simp⟩

theorem js_psi_sizes (fv : I32) (lines : Slice (alloc.vec.Vec U32))
    (hV : ∀ l ∈ lines.val, ValidL l.val) (h64 : System.Platform.numBits = 64)
    (N : Nat) (hN : N ≤ 2^61) (hL : ∀ l ∈ lines.val, l.val.length < N) (hpath : dec_pathOk N)
    (hn : lines.val.length + 1 < 2^31) :
    ∃ d, beatmap.decoder.parse_stream_into fv lines = ok d ∧
      dec_dbS d = LegacyBeatmapDecoder.parseStreamInto (i32S fv) (vstrs lines.val) ∧ js_decSz d := by
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
  refine ⟨_, rfl, ?_, ?sz⟩
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
  case sz =>
    unfold dec_cpiOk at hc'
    have l3 := congrArg List.length hlv
    have l2 := congrArg _root_.Array.size hppv
    have l1 := congrArg _root_.Array.size hsortv
    simp [js_ppb_size, gen_ssb_size] at l1 l2 l3
    simp only [js_decSz]
    omega

theorem js_decode_sizes (bytes : Slice U8) (hb : bytes.val.length < Usize.max)
    (h64 : System.Platform.numBits = 64) (N : Nat) (hN : N ≤ 2^61) (hpath : dec_pathOk N)
    (hsize : ∀ cs, streamReaderDecode (bytesS bytes) = some cs →
      (readLines cs).size + 1 < 2^31 ∧ ∀ L ∈ readLines cs, L.length < N) :
    ∃ r, beatmap.decoder.decode bytes = ok r ∧
      hRel dec_dbS r (LegacyBeatmapDecoder.decode (bytesS bytes)) ∧ ∀ d, r = .Ok d → js_decSz d := by
  obtain ⟨o, ho, hov, hoV⟩ := beatmap.text.stream_reader_decode_refines bytes hb
  unfold beatmap.decoder.decode LegacyBeatmapDecoder.decode
  rw [← hov]
  simp only [ho, bind_ok]
  cases o with
  | none => exact ⟨_, rfl, trivial, fun d h => by cases h⟩
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
      exact ⟨_, rfl, trivial, fun d h => by cases h⟩
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
          obtain ⟨db, hdb, hdbv, hdsz⟩ := js_psi_sizes v1 _ hrV h64 N hN hrL hpath hrn
          simp only [hdb, bind_ok]
          exact ⟨_, rfl, hdbv, fun d h => by cases h; exact hdsz⟩
        · exact ⟨_, rfl, rel_err hr1r _ _, fun d h => by cases h⟩
      · rw [if_neg hb1, if_neg hb1]
        rw [beatmap.dotnet.starts_with_refines _ (validStr_of first hfV), bind_ok, dec_litS1, strV_deref]
        have hbr : String.ofList (([123#u8] : List U8).map (fun b : U8 => Char.ofNat b.val)) = "{" := by decide
        rw [hbr]
        by_cases hb2 : (strV first).startsWith "{" = true
        · rw [if_pos hb2, if_pos hb2]; exact ⟨_, rfl, trivial, fun d h => by cases h⟩
        · rw [if_neg hb2, if_neg hb2]
          obtain ⟨db, hdb, hdbv, hdsz⟩ := js_psi_sizes beatmap.decoder.LATEST_VERSION _ hrV h64 N hN
            hrL hpath hrn
          simp only [hdb, bind_ok]
          refine ⟨_, rfl, ?_, fun d h => by cases h; exact hdsz⟩
          show dec_dbS db = _
          rw [hdbv]
          have hlv : i32S beatmap.decoder.LATEST_VERSION = OsuModel.Beatmap.LATEST_VERSION := by
            simp [beatmap.decoder.LATEST_VERSION, OsuModel.Beatmap.LATEST_VERSION, i32S]
          rw [hlv]

end OsuProofs
