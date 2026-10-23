/-
`beatmap::decoder`: refinement proofs for the legacy `.osu` decoder helpers (`clamp32/64`,
`apply_difficulty_restrictions`, `break_lt`, the `tp_*` timing-point field parsers, `should_skip_line`,
`handle_general`, `handle_difficulty`, `insert_break`, `handle_event`, `flush_pending_points`,
`add_line_points`, `apply_decode_defaults`, `post_process_breaks`). Helper names are prefixed `dec_`.
Errors are related by `dec_hRel` (both sides succeed with related states, or both fail and the Rust
state is unchanged).
-/
import OsuProofs.Beatmap.HitObjectParser2
import OsuProofs.Beatmap.DecoderStr
import OsuProofs.Beatmap.DotNet
import OsuProofs.Beatmap.ControlPoints
import OsuProofs.LoopsR
import OsuProofs.Beatmap.PathApproxBase
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

/-! ## representation of the decoder types -/
def dec_diffS (d : beatmap.types.Difficulty) : Difficulty :=
  ⟨d.drain_rate, d.circle_size, d.overall_difficulty, d.approach_rate, d.slider_multiplier, d.slider_tick_rate⟩
def dec_bpS (b : beatmap.types.BreakPeriod) : BreakPeriod := ⟨b.start_time, b.end_time⟩

theorem beatmap.decoder.clamp32_refines (v lo hi : F32) :
    beatmap.decoder.clamp32 v lo hi = ok (if v < lo then lo else if hi < v then hi else v) := by
  unfold beatmap.decoder.clamp32; simp
theorem beatmap.decoder.clamp64_refines (v lo hi : F64) :
    beatmap.decoder.clamp64 v lo hi = ok (if v < lo then lo else if hi < v then hi else v) := by
  unfold beatmap.decoder.clamp64; simp

theorem beatmap.decoder.apply_difficulty_restrictions_refines (d : beatmap.types.Difficulty) (rid : I32) :
    ∃ r, beatmap.decoder.apply_difficulty_restrictions d rid = ok r ∧
      dec_diffS r = LegacyBeatmapDecoder.applyDifficultyRestrictions (dec_diffS d) (i32S rid) := by
  unfold beatmap.decoder.apply_difficulty_restrictions LegacyBeatmapDecoder.applyDifficultyRestrictions
  have e0 : float.F32.from_bits 0#u32 = ok (0 : F32) := by simp; decide
  have e1 : float.F32.from_bits 1065353216#u32 = ok (1 : F32) := by simp; decide
  have e10 : float.F32.from_bits 1092616192#u32 = ok (10 : F32) := by simp; decide
  have em : beatmap.decoder.MAX_MANIA_KEY_COUNT = ok MAX_MANIA_KEY_COUNT := by
    unfold beatmap.decoder.MAX_MANIA_KEY_COUNT; simp; decide
  have f5 : float.F64.from_bits 4600877379321698714#u64 = ok (0.4 : F64) := by simp; decide
  have f6 : float.F64.from_bits 4615288898129284301#u64 = ok (3.6 : F64) := by simp; decide
  have f8 : float.F64.from_bits 4602678819172646912#u64 = ok (0.5 : F64) := by simp; decide
  have f9 : float.F64.from_bits 4620693217682128896#u64 = ok (8 : F64) := by simp; decide
  have h3 : (rid != 3#i32) = (i32S rid != 3) := by
    have : rid = 3#i32 ↔ i32S rid = 3 := by
      constructor
      · intro e; rw [e]; decide
      · intro e; have := congrArg Int32.toInt e; rw [i32S_toInt] at this
        exact IScalar.eq_of_val_eq (by rw [this]; decide)
    rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne, ne_eq, ne_eq, this]
  simp only [e0, e1, e10, f5, f6, f8, f9, bind_ok, beatmap.decoder.clamp32_refines, beatmap.decoder.clamp64_refines, h3]
  split <;> simp [em, beatmap.decoder.clamp32_refines, dec_diffS] <;> (refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl)

/-- Helper (spec: the local `lt` of `LegacyBeatmapDecoder.insertBreak`). -/
theorem beatmap.decoder.break_lt_refines (x y : beatmap.types.BreakPeriod) :
    beatmap.decoder.break_lt x y = ok (compareF64 x.start_time y.start_time < 0 ||
      (compareF64 x.start_time y.start_time == 0 && compareF64 x.end_time y.end_time < 0)) := by
  unfold beatmap.decoder.break_lt
  obtain ⟨a, ha, hav⟩ := beatmap.dotnet.compare_f64_refines x.start_time y.start_time
  obtain ⟨b, hb, hbv⟩ := beatmap.dotnet.compare_f64_refines x.end_time y.end_time
  simp only [ha, bind_ok, hb]
  have l1 : (a < 0#i32) ↔ a.val < 0 := by show a.val < (0#i32 : I32).val ↔ _; simp
  have l2 : (a = 0#i32) ↔ a.val = 0 := ⟨fun h => by rw [h]; rfl, fun h => IScalar.eq_of_val_eq (by rw [h]; rfl)⟩
  have l3 : (b < 0#i32) ↔ b.val < 0 := by show b.val < (0#i32 : I32).val ↔ _; simp
  by_cases c1 : a.val < 0
  · simp [l1.mpr c1, ← hav, c1]
  · by_cases c2 : a.val = 0
    · simp [show ¬ a < 0#i32 from fun h => c1 (l1.mp h), l2.mpr c2, ← hav, ← hbv, c2, l3]
    · simp [show ¬ a < 0#i32 from fun h => c1 (l1.mp h), show ¬ a = 0#i32 from fun h => c2 (l2.mp h), ← hav, c1, c2]

/-- Helper (spec: `speedMultiplier` of `handleTimingPoint`). -/
theorem beatmap.decoder.tp_speed_multiplier_refines (bl : F64) :
    beatmap.decoder.tp_speed_multiplier bl = ok (if bl < 0 then 100.0 / -bl else 1) := by
  unfold beatmap.decoder.tp_speed_multiplier
  have h0 : beatmap.decoder.D0 = ok (0 : F64) := by unfold beatmap.decoder.D0; simp; decide
  have h1 : beatmap.decoder.D1 = ok (1 : F64) := by unfold beatmap.decoder.D1; simp; decide
  have h100 : beatmap.decoder.D100 = ok (100.0 : F64) := by unfold beatmap.decoder.D100; simp; decide
  simp only [h0, h1, h100, bind_ok, float.F64.lt, float.F64.neg, float.F64.div]
  split <;> rename_i h <;> simp at h <;> simp [h]

theorem dec_i32S_inj (x y : I32) (h : i32S x = i32S y) : x = y := by
  have := congrArg Int32.toInt h; rw [i32S_toInt, i32S_toInt] at this
  exact IScalar.eq_of_val_eq this

/-- Helper (spec: the effect point's `scrollSpeed` in `handleTimingPoint`). -/
theorem beatmap.decoder.tp_scroll_speed_refines (rid : I32) (sm : F64) :
    beatmap.decoder.tp_scroll_speed rid sm = ok (if i32S rid == 1 || i32S rid == 3 then clampScrollSpeed sm else 1) := by
  unfold beatmap.decoder.tp_scroll_speed
  have h1 : beatmap.decoder.D1 = ok (1 : F64) := by unfold beatmap.decoder.D1; simp; decide
  have i1 : i32S 1#i32 = 1 := by decide
  have i3 : i32S 3#i32 = 3 := by decide
  by_cases c1 : rid = 1#i32
  · subst c1; simp [i1, beatmap.control_points.clamp_scroll_speed_refines]
  · have n1 : ¬ i32S rid = 1 := fun h => c1 (dec_i32S_inj _ _ (by rw [h, i1]))
    by_cases c3 : rid = 3#i32
    · subst c3; simp [i3, beatmap.control_points.clamp_scroll_speed_refines]
    · have n3 : ¬ i32S rid = 3 := fun h => c3 (dec_i32S_inj _ _ (by rw [h, i3]))
      simp [c1, c3, n1, n3, h1]

/-- Helper (spec: the `if timingChange` part of `handleTimingPoint`). -/
theorem beatmap.decoder.tp_timing_refines (time bl : F64) (ts : I32) (tc : Bool) :
    ∃ r, beatmap.decoder.tp_timing time bl ts tc = ok r ∧
      hRel (Option.map tpS) r (if tc = true then
        (if bl.isNaN = true then throw "Beat length cannot be NaN in a timing control point"
          else pure (some ({ time, beatLength := clampBeatLength bl, timeSignature := i32S ts } : TimingPoint)))
        else pure none) := by
  unfold beatmap.decoder.tp_timing
  cases tc
  · exact ⟨_, rfl, rfl⟩
  · by_cases hn : bl.isNaN = true
    · simp only [if_true, float.F64.is_nan, hn, bind_ok]; exact ⟨_, rfl, trivial⟩
    · simp only [if_true, float.F64.is_nan, hn, bind_ok, Bool.false_eq_true, if_false, beatmap.control_points.clamp_beat_length_refines]
      exact ⟨_, rfl, rfl⟩

theorem dec_idx (sp : Slice (alloc.vec.Vec U32)) (k : Usize) (h : k.val < sp.val.length) :
    Slice.index_usize sp k = ok (sp.val[k.val]'h) := index_eq sp k h

/-- Helper (spec: `if split.size ≥ k+1 then let _ ← liftNet what (parseInt split[k]!)` in `handleTimingPoint`). -/
theorem beatmap.decoder.tp_check_int_refines (sp : Slice (alloc.vec.Vec U32)) (hV : ∀ l ∈ sp.val, ValidL l.val)
    (k : Usize) (w : U32) (what : String) :
    ∃ r, beatmap.decoder.tp_check_int sp k w = ok r ∧
      hRel id r (if (vstrs sp.val).size ≥ k.val + 1 then
          (do let _ ← liftNet what (Parsing.parseInt (vstrs sp.val)[k.val]!); pure ()) else pure ()) := by
  unfold beatmap.decoder.tp_check_int
  rw [vstrs_size]
  by_cases h : sp.val.length > k.val
  · have h' : Slice.len sp > k := by show k.val < (Slice.len sp).val; simpa using h
    simp only [h', if_true, show sp.val.length ≥ k.val + 1 by omega, dec_idx sp k h, bind_ok, vstrs_get! _ _ h]
    rw [net.parse.parse_int_default_refines _ (validStr_of _ (hV _ (List.getElem_mem h))), bind_ok, strV_deref]
    obtain ⟨r1, hr1, hr1v⟩ := lift_net_exceptI w i32I i32S (fun _ => rfl) (Parsing.parseInt (strV (sp.val[k.val]'h))) what
    simp only [hr1, bind_ok]
    rcases r1 with a | e
    · rw [rel_ok hr1v]; exact ⟨_, rfl, rfl⟩
    · exact ⟨_, rfl, rel_err hr1v _ _⟩
  · have h' : ¬ Slice.len sp > k := by show ¬ k.val < (Slice.len sp).val; simpa using h
    simp only [h', if_false, show ¬ sp.val.length ≥ k.val + 1 by omega]; exact ⟨_, rfl, rfl⟩

/-- Helper (spec: `timingChange` of `handleTimingPoint`). -/
theorem beatmap.decoder.tp_timing_change_refines (sp : Slice (alloc.vec.Vec U32)) (hV : ∀ l ∈ sp.val, ValidL l.val) :
    ∃ r, beatmap.decoder.tp_timing_change sp = ok r ∧
      hRel id r (if (vstrs sp.val).size ≥ 7 then (do let c ← char0 (vstrs sp.val)[6]!; pure (c == '1')) else pure true) := by
  unfold beatmap.decoder.tp_timing_change
  rw [vstrs_size]
  by_cases h : sp.val.length ≥ 7
  · have h' : Slice.len sp ≥ 7#usize := by show (7#usize : Usize).val ≤ (Slice.len sp).val; simpa using h
    have hl6 : 6 < sp.val.length := by omega
    have hidx : Slice.index_usize sp 6#usize = ok (sp.val[6]'hl6) := dec_idx sp 6#usize (by simp; omega)
    simp only [h', h, if_true, hidx, bind_ok, vstrs_get! sp.val 6 hl6]
    obtain ⟨r0, hr0, hr0v, hr0m⟩ := beatmap.hit_object_parser.char0_refines (alloc.vec.Vec.deref (sp.val[6]'hl6))
    rw [strV_deref] at hr0v; rw [ds_deref_val] at hr0m
    simp only [hr0, bind_ok]
    rcases r0 with c | e
    · rw [rel_ok hr0v]
      have hc := hV _ (List.getElem_mem hl6) c (hr0m c rfl)
      refine ⟨_, rfl, ?_⟩
      show decide (c = 49#u32) = (chOf c == '1')
      by_cases e : c = 49#u32
      · subst e; decide
      · have : chOf c ≠ '1' := fun h => e (UScalar.eq_of_val_eq (by rw [(chOf_eq_of_valid c hc '1').mp h]; rfl))
        simp [e, this]
    · exact ⟨_, rfl, rel_err hr0v _ _⟩
  · have h' : ¬ Slice.len sp ≥ 7#usize := by show ¬ (7#usize : Usize).val ≤ (Slice.len sp).val; simpa using h
    simp only [h', h, if_false]; exact ⟨_, rfl, rfl⟩

/-- Helper (spec: `kiai` of `handleTimingPoint`). -/
theorem beatmap.decoder.tp_kiai_refines (sp : Slice (alloc.vec.Vec U32)) (hV : ∀ l ∈ sp.val, ValidL l.val) :
    ∃ r, beatmap.decoder.tp_kiai sp = ok r ∧
      hRel id r (if (vstrs sp.val).size ≥ 8 then
        (do let flags ← liftNet "effectFlags" (Parsing.parseInt (vstrs sp.val)[7]!); pure (flags &&& 1 != 0)) else pure false) := by
  unfold beatmap.decoder.tp_kiai
  rw [vstrs_size]
  by_cases h : sp.val.length ≥ 8
  · have h' : Slice.len sp ≥ 8#usize := by show (8#usize : Usize).val ≤ (Slice.len sp).val; simpa using h
    have hl : 7 < sp.val.length := by omega
    have hidx : Slice.index_usize sp 7#usize = ok (sp.val[7]'hl) := dec_idx sp 7#usize (by simp; omega)
    simp only [h', h, if_true, hidx, bind_ok, vstrs_get! sp.val 7 hl]
    rw [net.parse.parse_int_default_refines _ (validStr_of _ (hV _ (List.getElem_mem hl))), bind_ok, strV_deref]
    obtain ⟨r1, hr1, hr1v⟩ := lift_net_exceptI beatmap.errors.W_EFFECTFLAGS i32I i32S (fun _ => rfl)
      (Parsing.parseInt (strV (sp.val[7]'hl))) "effectFlags"
    simp only [hr1, bind_ok]
    rcases r1 with a | e
    · rw [rel_ok hr1v]
      refine ⟨.Ok (a &&& 1#i32 != 0#i32), by simp [lift], ?_⟩
      show (a &&& 1#i32 != 0#i32) = (i32S a &&& 1 != 0)
      have e1 : i32S (a &&& 1#i32) = i32S a &&& 1 := by unfold i32S; simp
      have e0 : i32S 0#i32 = 0 := by decide
      rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne, ne_eq, ne_eq, ← e1, ← e0]
      exact ⟨fun h1 h2 => h1 (dec_i32S_inj _ _ h2), fun h1 h2 => h1 (by rw [h2])⟩
    · exact ⟨_, rfl, rel_err hr1v _ _⟩
  · have h' : ¬ Slice.len sp ≥ 8#usize := by show ¬ (8#usize : Usize).val ≤ (Slice.len sp).val; simpa using h
    simp only [h', h, if_false]; exact ⟨_, rfl, rfl⟩

/-- Helper (spec: `timeSignature` of `handleTimingPoint`). -/
theorem beatmap.decoder.tp_time_signature_refines (sp : Slice (alloc.vec.Vec U32)) (hV : ∀ l ∈ sp.val, ValidL l.val) :
    ∃ r, beatmap.decoder.tp_time_signature sp = ok r ∧
      hRel i32S r (if (vstrs sp.val).size ≥ 3 then
        (do let c ← char0 (vstrs sp.val)[2]!
            if c != '0' then
              (do let n ← liftNet "timeSignature" (Parsing.parseInt (vstrs sp.val)[2]!)
                  if n ≤ 0 then throw "TimeSignature numerator must be positive" else pure n)
            else pure 4) else pure 4) := by
  unfold beatmap.decoder.tp_time_signature
  rw [vstrs_size]
  by_cases h : sp.val.length ≥ 3
  · have h' : Slice.len sp ≥ 3#usize := by show (3#usize : Usize).val ≤ (Slice.len sp).val; simpa using h
    have hl : 2 < sp.val.length := by omega
    have hidx : Slice.index_usize sp 2#usize = ok (sp.val[2]'hl) := dec_idx sp 2#usize (by simp; omega)
    simp only [h', h, if_true, hidx, bind_ok, vstrs_get! sp.val 2 hl]
    obtain ⟨r0, hr0, hr0v, hr0m⟩ := beatmap.hit_object_parser.char0_refines (alloc.vec.Vec.deref (sp.val[2]'hl))
    rw [strV_deref] at hr0v; rw [ds_deref_val] at hr0m
    simp only [hr0, bind_ok]
    rcases r0 with c | e
    · rw [rel_ok hr0v]; simp only [except_bind_ok]
      have hc := hV _ (List.getElem_mem hl) c (hr0m c rfl)
      by_cases c0 : c = 48#u32
      · subst c0
        have : (chOf 48#u32 != '0') = false := by decide
        simp only [this, Bool.false_eq_true, if_false]
        exact ⟨.Ok 4#i32, by simp, rfl⟩
      · have : (chOf c != '0') = true := by
          have : chOf c ≠ '0' := fun h => c0 (UScalar.eq_of_val_eq (by rw [(chOf_eq_of_valid c hc '0').mp h]; rfl))
          simpa using this
        have c0' : (c != 48#u32) = true := by simpa using c0
        simp only [this, if_true, c0']
        rw [net.parse.parse_int_default_refines _ (validStr_of _ (hV _ (List.getElem_mem hl))), bind_ok, strV_deref]
        obtain ⟨r1, hr1, hr1v⟩ := lift_net_exceptI beatmap.errors.W_TIMESIGNATURE i32I i32S (fun _ => rfl)
          (Parsing.parseInt (strV (sp.val[2]'hl))) "timeSignature"
        simp only [hr1, bind_ok]
        rcases r1 with a | e
        · rw [rel_ok hr1v]; simp only [except_bind_ok]
          have hle : (a ≤ 0#i32) ↔ (i32S a ≤ 0) := by
            rw [Int32.le_iff_toInt_le, i32S_toInt]; show (a.val ≤ (0#i32 : I32).val) ↔ _; simp
          by_cases k : a ≤ 0#i32
          · simp only [k, if_true, hle.mp k]; exact ⟨_, rfl, trivial⟩
          · have k' : ¬ i32S a ≤ 0 := fun h => k (hle.mpr h)
            simp only [k, if_false, k']; exact ⟨_, rfl, rfl⟩
        · exact ⟨_, rfl, rel_err hr1v _ _⟩
    · exact ⟨_, rfl, rel_err hr0v _ _⟩
  · have h' : ¬ Slice.len sp ≥ 3#usize := by show ¬ (3#usize : Usize).val ≤ (Slice.len sp).val; simpa using h
    simp only [h', h, if_false]; exact ⟨_, rfl, rfl⟩

theorem beatmap.decoder.should_skip_line_refines (line : Slice U32) (hs : ValidStr line) :
    beatmap.decoder.should_skip_line line = ok (LegacyBeatmapDecoder.shouldSkipLine (String.ofList (strS line))) := by
  unfold beatmap.decoder.should_skip_line LegacyBeatmapDecoder.shouldSkipLine
  rw [beatmap.dotnet.is_null_or_white_space_refines line hs, bind_ok]
  cases hn : isNullOrWhiteSpace (String.ofList (strS line))
  · obtain ⟨v, hv, hvv, hvV, _⟩ := trim_start_valid line hs
    simp only [Bool.false_eq_true, if_false, hv, bind_ok, lift, Array.to_slice, Array.make, Bool.false_or]
    rw [beatmap.dotnet.starts_with_refines _ (validStr_of v hvV)]
    have h1 : String.ofList (strS (alloc.vec.Vec.deref v)) = trimStart (String.ofList (strS line)) := by
      rw [← hvv]; simp [strS, ds_deref_val]
    rw [h1]; congr 2
  · simp

def dec_pendS (p : beatmap.decoder.Pending) : Pending :=
  ⟨p.timing.val.map tpS, p.difficulty.val.map dpS, p.effect.val.map epS, p.time⟩
def dec_dsS (s : beatmap.decoder.DecoderState) : DecoderState :=
  { formatVersion := i32S s.format_version, offset := i32S s.offset, sect := i32S s.sect, rulesetId := i32S s.ruleset_id,
    stackLeniency := s.stack_leniency, audioLeadIn := s.audio_lead_in, difficulty := dec_diffS s.difficulty,
    hasApproachRate := s.has_approach_rate, cpi := cpS s.cpi, pending := dec_pendS s.pending,
    breaks := (s.breaks.val.map dec_bpS).toArray, parser := psS s.parser,
    hitObjects := (s.hit_objects.val.map choS).toArray }

/-- A decoder line handler: success with the new state, or a failure that leaves the state unchanged
(`parseLine` then keeps the old state, `LegacyDecoder.cs:69-77`). -/
def dec_hRel (s : beatmap.decoder.DecoderState) (p : core.result.Result Unit beatmap.hit_object_parser.DecodeError ×
    beatmap.decoder.DecoderState) (x : DecodeM DecoderState) : Prop :=
  (p.1 = .Ok () ∧ x = .ok (dec_dsS p.2)) ∨ ((∃ e, p.1 = .Err e) ∧ (∃ m, x = .error m) ∧ p.2 = s)

theorem dec_key (k : alloc.vec.Vec U32) (hk : ValidL k.val) (lit : Slice U8) (S : String) (hS : String.ofList (litS lit) = S) :
    beatmap.dotnet.str_eq (alloc.vec.Vec.deref k) lit = ok (decide (strV k = S)) := by
  rw [beatmap.dotnet.str_eq_refines _ (validStr_of k hk)]
  congr 1; apply decide_eq_decide.mpr
  rw [← hS, ← strV_deref]
  constructor
  · intro h; rw [h]
  · intro h; have := congrArg String.toList h; simpa using this

theorem dec_key' (k : alloc.vec.Vec U32) (hk : ValidL k.val) (n : Usize) (l : List U8) (h : l.length = n.val) :
    beatmap.dotnet.str_eq (alloc.vec.Vec.deref k) (Array.to_slice (Array.make n l h)) =
      ok (decide (strV k = String.ofList (l.map (fun b : U8 => Char.ofNat b.val)))) := by
  rw [dec_key k hk _ _ rfl]; simp [litS, Array.to_slice, Array.make, Array.from_val, Slice.from_val]

theorem dec_lit_AudioLeadIn : String.ofList (([65#u8, 117#u8, 100#u8, 105#u8, 111#u8, 76#u8, 101#u8, 97#u8, 100#u8, 73#u8, 110#u8] : List U8).map (fun b : U8 => Char.ofNat b.val)) = "AudioLeadIn" := by decide
theorem dec_lit_StackLeniency : String.ofList (([83#u8, 116#u8, 97#u8, 99#u8, 107#u8, 76#u8, 101#u8, 110#u8, 105#u8, 101#u8, 110#u8, 99#u8, 121#u8] : List U8).map (fun b : U8 => Char.ofNat b.val)) = "StackLeniency" := by decide
theorem dec_lit_Mode : String.ofList (([77#u8, 111#u8, 100#u8, 101#u8] : List U8).map (fun b : U8 => Char.ofNat b.val)) = "Mode" := by decide
theorem dec_lit_HPDrainRate : String.ofList (([72#u8, 80#u8, 68#u8, 114#u8, 97#u8, 105#u8, 110#u8, 82#u8, 97#u8, 116#u8, 101#u8] : List U8).map (fun b : U8 => Char.ofNat b.val)) = "HPDrainRate" := by decide
theorem dec_lit_CircleSize : String.ofList (([67#u8, 105#u8, 114#u8, 99#u8, 108#u8, 101#u8, 83#u8, 105#u8, 122#u8, 101#u8] : List U8).map (fun b : U8 => Char.ofNat b.val)) = "CircleSize" := by decide
theorem dec_lit_OverallDifficulty : String.ofList (([79#u8, 118#u8, 101#u8, 114#u8, 97#u8, 108#u8, 108#u8, 68#u8, 105#u8, 102#u8, 102#u8, 105#u8, 99#u8, 117#u8, 108#u8, 116#u8, 121#u8] : List U8).map (fun b : U8 => Char.ofNat b.val)) = "OverallDifficulty" := by decide
theorem dec_lit_ApproachRate : String.ofList (([65#u8, 112#u8, 112#u8, 114#u8, 111#u8, 97#u8, 99#u8, 104#u8, 82#u8, 97#u8, 116#u8, 101#u8] : List U8).map (fun b : U8 => Char.ofNat b.val)) = "ApproachRate" := by decide
theorem dec_lit_SliderMultiplier : String.ofList (([83#u8, 108#u8, 105#u8, 100#u8, 101#u8, 114#u8, 77#u8, 117#u8, 108#u8, 116#u8, 105#u8, 112#u8, 108#u8, 105#u8, 101#u8, 114#u8] : List U8).map (fun b : U8 => Char.ofNat b.val)) = "SliderMultiplier" := by decide
theorem dec_lit_SliderTickRate : String.ofList (([83#u8, 108#u8, 105#u8, 100#u8, 101#u8, 114#u8, 84#u8, 105#u8, 99#u8, 107#u8, 82#u8, 97#u8, 116#u8, 101#u8] : List U8).map (fun b : U8 => Char.ofNat b.val)) = "SliderTickRate" := by decide

theorem dec_trim_len (s : Slice U32) (hs : ValidStr s) (v : alloc.vec.Vec U32) (h : beatmap.dotnet.trim s = ok v) :
    v.val.length ≤ s.val.length := by
  obtain ⟨v', hv', hvv'⟩ := trim_common s hs true true beatmap.dotnet.trim (fun _ => rfl)
  rw [h] at hv'; have e : v = v' := by simpa using hv'
  subst e; simp only [if_true] at hvv'; rw [hvv']
  unfold rtrimU; simp only [List.length_reverse]
  exact le_trans (List.dropWhile_suffix _).length_le (by simp [(List.dropWhile_suffix wsU).length_le])

theorem dec_skv_len (line : Slice U32) (hs : ValidStr line) (sep : U32) (k v : alloc.vec.Vec U32)
    (h : beatmap.dotnet.split_key_val line sep = ok (k, v)) : v.val.length ≤ line.val.length := by
  obtain ⟨i, f, hl, hi, _, hf, _⟩ := skv_loop_ok line sep
  unfold beatmap.dotnet.split_key_val at h
  simp only [hl, bind_ok, uncurry_apply_pair] at h
  cases f
  · obtain ⟨t, ht, _, _⟩ := trim_valid line hs
    simp only [Bool.false_eq_true, if_false, ht, bind_ok] at h
    simp at h; obtain ⟨_, rfl⟩ := h; simp [alloc.vec.Vec.new]
  · obtain ⟨hlt, _⟩ := hf rfl
    have hmax : line.val.length ≤ Usize.max := line.property
    obtain ⟨kk, hk, _⟩ := beatmap.dotnet.sub_str_refines line 0#usize i (by simp) hi
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
    obtain ⟨vv, hvv, hvvv⟩ := beatmap.dotnet.sub_str_refines line i1 (Slice.len line) (by simp; omega) (by simp)
    have hvvV : ValidL vv.val := fun u hu => hs u (by rw [hvvv] at hu; exact List.mem_of_mem_drop (List.mem_of_mem_take hu))
    have hkkV : ValidL kk.val := fun u hu => hs u (by
      obtain ⟨kk', hk', hkv'⟩ := beatmap.dotnet.sub_str_refines line 0#usize i (by simp) hi
      rw [hk] at hk'; have e : kk = kk' := by simpa using hk'
      subst e; rw [hkv'] at hu; exact List.mem_of_mem_drop (List.mem_of_mem_take hu))
    obtain ⟨t1, ht1, _, _⟩ := trim_valid (alloc.vec.Vec.deref kk) (validStr_of kk hkkV)
    obtain ⟨t2, ht2, _, _⟩ := trim_valid (alloc.vec.Vec.deref vv) (validStr_of vv hvvV)
    simp only [if_true, hk, hi1, hvv, ht1, ht2, bind_ok] at h
    simp at h; obtain ⟨_, rfl⟩ := h
    have := dec_trim_len _ (validStr_of vv hvvV) t2 ht2
    rw [ds_deref_val, hvvv] at this; simp at this; omega

theorem beatmap.decoder.handle_general_refines (s : beatmap.decoder.DecoderState) (line : Slice U32) (hs : ValidStr line)
    (hn : line.val.length < 2^62) :
    ∃ p, beatmap.decoder.handle_general s line = ok p ∧
      dec_hRel s p (LegacyBeatmapDecoder.handleGeneral (dec_dsS s) (String.ofList (strS line))) := by
  unfold beatmap.decoder.handle_general LegacyBeatmapDecoder.handleGeneral
  obtain ⟨k, v, hkv, hkvS, hkV, hvV⟩ := beatmap.dotnet.split_key_val_refines line hs 58#u32 (by decide)
  rw [colon_lit] at hkvS
  simp only [hkv, bind_ok, uncurry_apply_pair]
  rw [← hkvS]
  simp only [lift, bind_ok, dec_key' k hkV, dec_lit_AudioLeadIn, dec_lit_StackLeniency, dec_lit_Mode]
  have hvS : ValidStr (alloc.vec.Vec.deref v) := validStr_of v hvV
  have hvn : (alloc.vec.Vec.deref v).val.length < 2^62 := by
    rw [ds_deref_val]; have := dec_skv_len line hs 58#u32 k v hkv; omega
  by_cases c1 : strV k = "AudioLeadIn"
  · simp only [c1, decide_true, if_true]
    rw [net.parse.parse_int_default_refines _ hvS, bind_ok, strV_deref]
    obtain ⟨r1, hr1, hr1v⟩ := lift_net_exceptI beatmap.errors.W_AUDIOLEADIN i32I i32S (fun _ => rfl)
      (Parsing.parseInt (strV v)) "AudioLeadIn"
    simp only [hr1, bind_ok]
    rcases r1 with a | e
    · have := rel_ok hr1v
      simp only [float.F64.from_i64, bind_ok]
      refine ⟨_, rfl, Or.inl ⟨rfl, ?_⟩⟩
      simp only [this, except_bind_ok]
      simp [dec_dsS, F64.ofInt32, i32S_toInt]
    · refine ⟨_, rfl, Or.inr ⟨⟨e, rfl⟩, ?_, rfl⟩⟩
      cases h : liftNet "AudioLeadIn" (Parsing.parseInt (strV v)) with
      | ok _ => rw [h] at hr1v; simp [hRel] at hr1v
      | error m => exact ⟨m, by simp [h]⟩
  · simp only [c1, decide_false, Bool.false_eq_true, if_false]
    by_cases c2 : strV k = "StackLeniency"
    · simp only [c2, decide_true, if_true]
      rw [net.parse.parse_float_default_refines _ hvS hvn, bind_ok, strV_deref]
      obtain ⟨r1, hr1, hr1v⟩ := lift_net_exceptI beatmap.errors.W_STACKLENIENCY id id (fun _ => rfl)
        (Parsing.parseFloat (strV v)) "StackLeniency"
      simp only [hr1, bind_ok]
      rcases r1 with a | e
      · have := rel_ok hr1v
        refine ⟨_, rfl, Or.inl ⟨rfl, ?_⟩⟩
        simp only [this, except_bind_ok]
        simp [dec_dsS]
      · refine ⟨_, rfl, Or.inr ⟨⟨e, rfl⟩, ?_, rfl⟩⟩
        cases h : liftNet "StackLeniency" (Parsing.parseFloat (strV v)) with
        | ok _ => rw [h] at hr1v; simp [hRel] at hr1v
        | error m => exact ⟨m, by simp [h]⟩
    · simp only [c2, decide_false, Bool.false_eq_true, if_false]
      by_cases c3 : strV k = "Mode"
      · simp only [c3, decide_true, if_true]
        rw [net.parse.parse_int_default_refines _ hvS, bind_ok, strV_deref]
        obtain ⟨r1, hr1, hr1v⟩ := lift_net_exceptI beatmap.errors.W_MODE i32I i32S (fun _ => rfl)
          (Parsing.parseInt (strV v)) "Mode"
        simp only [hr1, bind_ok]
        rcases r1 with a | e
        · have := rel_ok hr1v
          simp only [this, except_bind_ok]
          have l0 : (0#i32 ≤ a) ↔ (0 ≤ i32S a) := by
            rw [Int32.le_iff_toInt_le, i32S_toInt]; show ((0#i32 : I32).val ≤ a.val) ↔ _; simp
          have l3 : (a ≤ 3#i32) ↔ (i32S a ≤ 3) := by
            rw [Int32.le_iff_toInt_le, i32S_toInt]; show (a.val ≤ (3#i32 : I32).val) ↔ _; simp
          by_cases d0 : 0#i32 ≤ a
          · by_cases d3 : a ≤ 3#i32
            · simp only [d0, d3, if_true, l0.mp d0, l3.mp d3, decide_true, Bool.and_self]
              refine ⟨_, rfl, Or.inl ⟨rfl, ?_⟩⟩
              simp [dec_dsS]
            · simp only [d0, d3, if_true, if_false, l0.mp d0, (show ¬ i32S a ≤ 3 from fun h => d3 (l3.mpr h))]
              refine ⟨_, rfl, Or.inr ⟨⟨_, rfl⟩, ⟨_, rfl⟩, rfl⟩⟩
          · simp only [d0, if_false, (show ¬ 0 ≤ i32S a from fun h => d0 (l0.mpr h))]
            refine ⟨_, rfl, Or.inr ⟨⟨_, rfl⟩, ⟨_, rfl⟩, rfl⟩⟩
        · refine ⟨_, rfl, Or.inr ⟨⟨e, rfl⟩, ?_, rfl⟩⟩
          cases h : liftNet "Mode" (Parsing.parseInt (strV v)) with
          | ok _ => rw [h] at hr1v; simp [hRel] at hr1v
          | error m => exact ⟨m, by simp [h]⟩
      · simp only [c3, decide_false, Bool.false_eq_true, if_false]
        refine ⟨_, rfl, Or.inl ⟨rfl, ?_⟩⟩
        simp [c1, c2, c3]

theorem beatmap.decoder.handle_difficulty_refines (s : beatmap.decoder.DecoderState) (line : Slice U32) (hs : ValidStr line)
    (hn : line.val.length < 2^62) :
    ∃ p, beatmap.decoder.handle_difficulty s line = ok p ∧
      dec_hRel s p (LegacyBeatmapDecoder.handleDifficulty (dec_dsS s) (String.ofList (strS line))) := by
  unfold beatmap.decoder.handle_difficulty LegacyBeatmapDecoder.handleDifficulty
  obtain ⟨k, v, hkv, hkvS, hkV, hvV⟩ := beatmap.dotnet.split_key_val_refines line hs 58#u32 (by decide)
  rw [colon_lit] at hkvS
  simp only [hkv, bind_ok, uncurry_apply_pair]
  rw [← hkvS]
  simp only [lift, bind_ok, dec_key' k hkV, dec_lit_HPDrainRate, dec_lit_CircleSize, dec_lit_OverallDifficulty,
    dec_lit_ApproachRate, dec_lit_SliderMultiplier, dec_lit_SliderTickRate]
  have hvS : ValidStr (alloc.vec.Vec.deref v) := validStr_of v hvV
  have hvn : (alloc.vec.Vec.deref v).val.length < 2^62 := by
    rw [ds_deref_val]; have := dec_skv_len line hs 58#u32 k v hkv; omega
  by_cases cHPDrainRate : strV k = "HPDrainRate"
  · simp only [cHPDrainRate, decide_true, if_true]
    rw [net.parse.parse_float_default_refines _ hvS hvn, bind_ok, strV_deref]
    obtain ⟨r1, hr1, hr1v⟩ := lift_net_exceptI beatmap.errors.W_HPDRAINRATE id id (fun _ => rfl) (Parsing.parseFloat (strV v)) "HPDrainRate"
    simp only [hr1, bind_ok]
    rcases r1 with a | e
    · have := rel_ok hr1v
      refine ⟨_, rfl, Or.inl ⟨rfl, ?_⟩⟩
      simp only [this, except_bind_ok]
      simp [dec_dsS, dec_diffS]
    · refine ⟨_, rfl, Or.inr ⟨⟨e, rfl⟩, ?_, rfl⟩⟩
      cases h : liftNet "HPDrainRate" (Parsing.parseFloat (strV v)) with
      | ok _ => rw [h] at hr1v; simp [hRel] at hr1v
      | error m => exact ⟨m, by simp [h]⟩
  · simp only [cHPDrainRate, decide_false, Bool.false_eq_true, if_false]
    by_cases cCircleSize : strV k = "CircleSize"
    · simp only [cCircleSize, decide_true, if_true]
      rw [net.parse.parse_float_default_refines _ hvS hvn, bind_ok, strV_deref]
      obtain ⟨r1, hr1, hr1v⟩ := lift_net_exceptI beatmap.errors.W_CIRCLESIZE id id (fun _ => rfl) (Parsing.parseFloat (strV v)) "CircleSize"
      simp only [hr1, bind_ok]
      rcases r1 with a | e
      · have := rel_ok hr1v
        refine ⟨_, rfl, Or.inl ⟨rfl, ?_⟩⟩
        simp only [this, except_bind_ok]
        simp [dec_dsS, dec_diffS]
      · refine ⟨_, rfl, Or.inr ⟨⟨e, rfl⟩, ?_, rfl⟩⟩
        cases h : liftNet "CircleSize" (Parsing.parseFloat (strV v)) with
        | ok _ => rw [h] at hr1v; simp [hRel] at hr1v
        | error m => exact ⟨m, by simp [h]⟩
    · simp only [cCircleSize, decide_false, Bool.false_eq_true, if_false]
      by_cases cOverallDifficulty : strV k = "OverallDifficulty"
      · simp only [cOverallDifficulty, decide_true, if_true]
        rw [net.parse.parse_float_default_refines _ hvS hvn, bind_ok, strV_deref]
        obtain ⟨r1, hr1, hr1v⟩ := lift_net_exceptI beatmap.errors.W_OVERALLDIFFICULTY id id (fun _ => rfl) (Parsing.parseFloat (strV v)) "OverallDifficulty"
        simp only [hr1, bind_ok]
        rcases r1 with a | e
        · have := rel_ok hr1v
          simp only [this, except_bind_ok]
          cases har : s.has_approach_rate
          · simp only [Bool.false_eq_true, if_false]
            refine ⟨_, rfl, Or.inl ⟨rfl, ?_⟩⟩
            simp [dec_dsS, dec_diffS, har]
          · simp only [if_true]
            refine ⟨_, rfl, Or.inl ⟨rfl, ?_⟩⟩
            simp [dec_dsS, dec_diffS, har]
        · refine ⟨_, rfl, Or.inr ⟨⟨e, rfl⟩, ?_, rfl⟩⟩
          cases h : liftNet "OverallDifficulty" (Parsing.parseFloat (strV v)) with
          | ok _ => rw [h] at hr1v; simp [hRel] at hr1v
          | error m => exact ⟨m, by simp [h]⟩
      · simp only [cOverallDifficulty, decide_false, Bool.false_eq_true, if_false]
        by_cases cApproachRate : strV k = "ApproachRate"
        · simp only [cApproachRate, decide_true, if_true]
          rw [net.parse.parse_float_default_refines _ hvS hvn, bind_ok, strV_deref]
          obtain ⟨r1, hr1, hr1v⟩ := lift_net_exceptI beatmap.errors.W_APPROACHRATE id id (fun _ => rfl) (Parsing.parseFloat (strV v)) "ApproachRate"
          simp only [hr1, bind_ok]
          rcases r1 with a | e
          · have := rel_ok hr1v
            refine ⟨_, rfl, Or.inl ⟨rfl, ?_⟩⟩
            simp only [this, except_bind_ok]
            simp [dec_dsS, dec_diffS]
          · refine ⟨_, rfl, Or.inr ⟨⟨e, rfl⟩, ?_, rfl⟩⟩
            cases h : liftNet "ApproachRate" (Parsing.parseFloat (strV v)) with
            | ok _ => rw [h] at hr1v; simp [hRel] at hr1v
            | error m => exact ⟨m, by simp [h]⟩
        · simp only [cApproachRate, decide_false, Bool.false_eq_true, if_false]
          by_cases cSliderMultiplier : strV k = "SliderMultiplier"
          · simp only [cSliderMultiplier, decide_true, if_true]
            rw [net.parse.parse_double_default_refines _ hvS hvn, bind_ok, strV_deref]
            obtain ⟨r1, hr1, hr1v⟩ := lift_net_exceptI beatmap.errors.W_SLIDERMULTIPLIER id id (fun _ => rfl) (Parsing.parseDouble (strV v)) "SliderMultiplier"
            simp only [hr1, bind_ok]
            rcases r1 with a | e
            · have := rel_ok hr1v
              refine ⟨_, rfl, Or.inl ⟨rfl, ?_⟩⟩
              simp only [this, except_bind_ok]
              simp [dec_dsS, dec_diffS]
            · refine ⟨_, rfl, Or.inr ⟨⟨e, rfl⟩, ?_, rfl⟩⟩
              cases h : liftNet "SliderMultiplier" (Parsing.parseDouble (strV v)) with
              | ok _ => rw [h] at hr1v; simp [hRel] at hr1v
              | error m => exact ⟨m, by simp [h]⟩
          · simp only [cSliderMultiplier, decide_false, Bool.false_eq_true, if_false]
            by_cases cSliderTickRate : strV k = "SliderTickRate"
            · simp only [cSliderTickRate, decide_true, if_true]
              rw [net.parse.parse_double_default_refines _ hvS hvn, bind_ok, strV_deref]
              obtain ⟨r1, hr1, hr1v⟩ := lift_net_exceptI beatmap.errors.W_SLIDERTICKRATE id id (fun _ => rfl) (Parsing.parseDouble (strV v)) "SliderTickRate"
              simp only [hr1, bind_ok]
              rcases r1 with a | e
              · have := rel_ok hr1v
                refine ⟨_, rfl, Or.inl ⟨rfl, ?_⟩⟩
                simp only [this, except_bind_ok]
                simp [dec_dsS, dec_diffS]
              · refine ⟨_, rfl, Or.inr ⟨⟨e, rfl⟩, ?_, rfl⟩⟩
                cases h : liftNet "SliderTickRate" (Parsing.parseDouble (strV v)) with
                | ok _ => rw [h] at hr1v; simp [hRel] at hr1v
                | error m => exact ⟨m, by simp [h]⟩
            · simp only [cSliderTickRate, decide_false, Bool.false_eq_true, if_false]
              refine ⟨_, rfl, Or.inl ⟨rfl, ?_⟩⟩
              simp [cHPDrainRate, cCircleSize, cOverallDifficulty, cApproachRate, cSliderMultiplier, cSliderTickRate]

def dec_lt (x y : BreakPeriod) : Bool :=
  compareF64 x.startTime y.startTime < 0 || (compareF64 x.startTime y.startTime == 0 && compareF64 x.endTime y.endTime < 0)

theorem dec_break_lt (x y : beatmap.types.BreakPeriod) : beatmap.decoder.break_lt x y = ok (dec_lt (dec_bpS x) (dec_bpS y)) := by
  rw [beatmap.decoder.break_lt_refines]; rfl

theorem dec_ib_loop (bs : alloc.vec.Vec beatmap.types.BreakPeriod) (b : beatmap.types.BreakPeriod) :
    ∃ i, beatmap.decoder.insert_break_loop bs b 0#usize false = ok i ∧ i.val ≤ bs.val.length ∧
      (∀ j q, j < i.val → bs.val[j]? = some q → dec_lt (dec_bpS b) (dec_bpS q) = false) ∧
      (∀ q, bs.val[i.val]? = some q → dec_lt (dec_bpS b) (dec_bpS q) = true) := by
  unfold beatmap.decoder.insert_break_loop
  obtain ⟨y, hy, hq⟩ := loop_ok (fun (x : Usize × Bool) => beatmap.decoder.insert_break_loop.body bs b x.1 x.2)
    (fun x => bs.val.length - x.1.val + (if x.2 then 0 else 1))
    (fun x => x.1.val ≤ bs.val.length ∧ (∀ j q, j < x.1.val → bs.val[j]? = some q → dec_lt (dec_bpS b) (dec_bpS q) = false) ∧
      (x.2 = true → ∀ q, bs.val[x.1.val]? = some q → dec_lt (dec_bpS b) (dec_bpS q) = true))
    (fun i => i.val ≤ bs.val.length ∧ (∀ j q, j < i.val → bs.val[j]? = some q → dec_lt (dec_bpS b) (dec_bpS q) = false) ∧
      (∀ q, bs.val[i.val]? = some q → dec_lt (dec_bpS b) (dec_bpS q) = true))
    (by
      rintro ⟨i, f⟩ ⟨hi, hne, hf⟩
      dsimp only at hi hne hf ⊢
      cases f with
      | true => left; exact ⟨i, by simp [beatmap.decoder.insert_break_loop.body], hi, hne, hf rfl⟩
      | false =>
        by_cases hlt : i.val < bs.val.length
        · right
          have hlt' : i < alloc.vec.Vec.len bs := by show i.val < (alloc.vec.Vec.len bs).val; simpa using hlt
          have hidx := vec_index_eq' bs i hlt
          by_cases hl : dec_lt (dec_bpS b) (dec_bpS (bs.val[i.val]'hlt)) = true
          · refine ⟨(i, true), by simp [beatmap.decoder.insert_break_loop.body, hlt', hidx, dec_break_lt, hl], ⟨hi, hne, ?_⟩, by simp⟩
            intro _ q hq; rw [List.getElem?_eq_getElem hlt] at hq; simp at hq; rw [← hq]; exact hl
          · have hl' : dec_lt (dec_bpS b) (dec_bpS (bs.val[i.val]'hlt)) = false := by simpa using hl
            obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := bs.property; omega)
            refine ⟨(i1, false), by simp [beatmap.decoder.insert_break_loop.body, hlt', hidx, dec_break_lt, hl', hi1],
              ⟨by dsimp only; omega, ?_, by simp⟩, by dsimp only; omega⟩
            intro j q hj hq; dsimp only at hj
            by_cases hji : j = i.val
            · subst hji; rw [List.getElem?_eq_getElem hlt] at hq; simp at hq; rw [← hq]; exact hl'
            · exact hne j q (by omega) hq
        · left
          have hlt' : ¬ i < alloc.vec.Vec.len bs := by show ¬ i.val < (alloc.vec.Vec.len bs).val; simpa using hlt
          refine ⟨i, by simp [beatmap.decoder.insert_break_loop.body, hlt'], hi, hne, ?_⟩
          intro q hq; rw [List.getElem?_eq_none (by omega)] at hq; cases hq)
    (0#usize, false) ⟨by simp, by simp, by simp⟩
  exact ⟨y, hy, hq⟩

theorem beatmap.decoder.insert_break_refines (bs : alloc.vec.Vec beatmap.types.BreakPeriod) (b : beatmap.types.BreakPeriod)
    (hl : bs.val.length < Usize.max) :
    ∃ w, beatmap.decoder.insert_break bs b = ok w ∧
      (w.val.map dec_bpS).toArray = LegacyBeatmapDecoder.insertBreak ((bs.val.map dec_bpS).toArray) (dec_bpS b) := by
  obtain ⟨i, hi, hil, hne, hf⟩ := dec_ib_loop bs b
  obtain ⟨w, hw, hwv⟩ := beatmap.dotnet.insert_at_refines beatmap.types.BreakPeriod.Insts.CoreCloneClone (fun _ => rfl) bs i b hil hl
  refine ⟨w, by unfold beatmap.decoder.insert_break; rw [hi, bind_ok]; exact hw, ?_⟩
  unfold LegacyBeatmapDecoder.insertBreak
  have hfi : ((bs.val.map dec_bpS).toArray.findIdx? (fun q => dec_lt (dec_bpS b) q)).getD (bs.val.map dec_bpS).toArray.size = i.val := by
    rw [List.findIdx?_toArray]
    by_cases hlt : i.val < bs.val.length
    · have : (bs.val.map dec_bpS).findIdx? (fun q => dec_lt (dec_bpS b) q) = some i.val := by
        rw [List.findIdx?_eq_some_iff_getElem]
        refine ⟨by simpa using hlt, ?_, ?_⟩
        · simp; exact hf _ (List.getElem?_eq_getElem hlt)
        · intro j hj; simp; exact hne j _ hj (List.getElem?_eq_getElem (by omega))
      rw [this]; rfl
    · have : (bs.val.map dec_bpS).findIdx? (fun q => dec_lt (dec_bpS b) q) = none := by
        rw [List.findIdx?_eq_none_iff]
        intro q hq
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
        simp at hj ⊢
        exact hne j _ (by omega) (List.getElem?_eq_getElem hj)
      rw [this]; simp; omega
  show _ = (List.map dec_bpS bs.val).toArray.insertIdx! (((bs.val.map dec_bpS).toArray.findIdx? (fun q => dec_lt (dec_bpS b) q)).getD
    (bs.val.map dec_bpS).toArray.size) (dec_bpS b)
  rw [hfi, hwv]
  apply Array.toList_inj.mp
  rw [Array.insertIdx!, dif_pos (by simp; omega)]
  simp [List.map_insertIdx]

theorem dec_offset_time (s : beatmap.decoder.DecoderState) (t : F64) :
    beatmap.decoder.offset_time s t = ok (LegacyBeatmapDecoder.offsetTime (dec_dsS s) t) := by
  unfold beatmap.decoder.offset_time LegacyBeatmapDecoder.offsetTime
  simp [lift, dec_dsS, i32S_toInt]

theorem comma_lit : chOf 44#u32 = ',' := by decide

theorem beatmap.decoder.handle_event_refines (s : beatmap.decoder.DecoderState) (line : Slice U32) (hs : ValidStr line)
    (hn : line.val.length < 2^62) (hn2 : line.val.length < Usize.max) (hb : s.breaks.val.length < Usize.max) :
    ∃ p, beatmap.decoder.handle_event s line = ok p ∧
      dec_hRel s p (LegacyBeatmapDecoder.handleEvent (dec_dsS s) (String.ofList (strS line))) := by
  unfold beatmap.decoder.handle_event LegacyBeatmapDecoder.handleEvent
  obtain ⟨sp, hsp, hspv, hspV, hspL⟩ := split_rel line hs hn2 44#u32 (by decide)
  rw [comma_lit] at hspv
  simp only [hsp, bind_ok]
  rw [← hspv]
  have hne : 0 < sp.val.length := by
    have := congrArg Array.size hspv; simp only [vstrs, split, List.size_toArray, List.length_map] at this
    rw [this, ← comma_lit, splitOn_char]; simp; exact List.length_pos_of_ne_nil (List.splitOn_ne_nil _ _)
  have h0 := vec_index_eq' sp 0#usize (by simpa using hne)
  have hm0 := List.getElem_mem (show (0#usize : Usize).val < sp.val.length by simpa using hne)
  obtain ⟨o, ho, hov⟩ := beatmap.dotnet.enum_try_parse_refines beatmap.names.T_EVENT_TYPE _ (validStr_of _ (hspV _ hm0))
    (by have := hspL _ hm0; simp at this ⊢; omega)
  simp only [h0, bind_ok, ho]
  have hT : enumTable beatmap.names.T_EVENT_TYPE.val = eventTypeNames := by
    unfold beatmap.names.T_EVENT_TYPE; rfl
  rw [hT, strV_deref] at hov
  have hg0 : (vstrs sp.val)[0]! = strV (sp.val[(0#usize : Usize).val]'(by simpa using hne)) := vstrs_get! _ _ _
  rw [hg0, ← hov]
  rcases o with _ | i
  · exact ⟨_, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · by_cases hi2 : i = 2#i32
    · subst hi2
      have e2 : i32S 2#i32 = 2 := by decide
      simp only [Option.map_some, e2]
      split
      swap
      · exfalso; rename_i h; exact h (by decide)
      split
      swap
      · exfalso; rename_i h; exact h (by decide)
      have e1 : (1#usize : Usize).val = 1 := rfl
      have e2' : (2#usize : Usize).val = 2 := rfl
      have errC : ∀ {α : Type} (e : beatmap.hit_object_parser.DecodeError) (x : DecodeM α) (k : α → DecodeM DecoderState),
          (∃ m, x = .error m) → dec_hRel s (core.result.Result.Err e, s) (x >>= k) := by
        intro α e x k ⟨m, hm⟩; rw [hm]; exact Or.inr ⟨⟨e, rfl⟩, ⟨m, rfl⟩, rfl⟩
      have errOf : ∀ {α β : Type} {f : α → β} {e} {x : Except String β}, hRel f (core.result.Result.Err e) x → ∃ m, x = .error m := by
        intro α β f e x h; cases x with
        | ok _ => simp [hRel] at h
        | error m => exact ⟨m, rfl⟩
      obtain ⟨r0, hr0, hr0v, hr0m⟩ := beatmap.hit_object_parser.at_refines (alloc.vec.Vec.deref sp) 1#usize
      rw [deref_valA, e1] at hr0v; rw [deref_valA] at hr0m
      simp only [hr0, bind_ok]
      rcases r0 with v1 | e
      case Err => exact ⟨_, rfl, errC e _ _ (errOf hr0v)⟩
      rw [rel_ok hr0v]; simp only [except_bind_ok]
      have hm1 := hr0m v1 rfl
      rw [net.parse.parse_double_default_refines _ (validStr_of _ (hspV _ hm1)) (by have := hspL _ hm1; simp; omega), bind_ok, strV_deref]
      obtain ⟨r1, hr1, hr1v⟩ := lift_net_exceptI beatmap.errors.W_BREAK_START id id (fun _ => rfl)
        (Parsing.parseDouble (strV v1)) "break start"
      simp only [hr1, bind_ok]
      rcases r1 with a | e
      case Err => exact ⟨_, rfl, errC e _ _ (errOf hr1v)⟩
      rw [rel_ok hr1v]; simp only [except_bind_ok, dec_offset_time, bind_ok]
      obtain ⟨r2, hr2, hr2v, hr2m⟩ := beatmap.hit_object_parser.at_refines (alloc.vec.Vec.deref sp) 2#usize
      rw [deref_valA, e2'] at hr2v; rw [deref_valA] at hr2m
      simp only [hr2, bind_ok]
      rcases r2 with v2 | e
      case Err => exact ⟨_, rfl, errC e _ _ (errOf hr2v)⟩
      rw [rel_ok hr2v]; simp only [except_bind_ok]
      have hm2 := hr2m v2 rfl
      rw [net.parse.parse_double_default_refines _ (validStr_of _ (hspV _ hm2)) (by have := hspL _ hm2; simp; omega), bind_ok, strV_deref]
      obtain ⟨r3, hr3, hr3v⟩ := lift_net_exceptI beatmap.errors.W_BREAK_END id id (fun _ => rfl)
        (Parsing.parseDouble (strV v2)) "break end"
      simp only [hr3, bind_ok]
      rcases r3 with b | e
      case Err => exact ⟨_, rfl, errC e _ _ (errOf hr3v)⟩
      rw [rel_ok hr3v]; simp only [except_bind_ok, dec_offset_time, bind_ok, hop_net_max_eq]
      obtain ⟨w, hw, hwv⟩ := beatmap.decoder.insert_break_refines s.breaks
        ⟨LegacyBeatmapDecoder.offsetTime (dec_dsS s) a, F64.max (LegacyBeatmapDecoder.offsetTime (dec_dsS s) a)
          (LegacyBeatmapDecoder.offsetTime (dec_dsS s) b)⟩ hb
      simp only [hw, bind_ok]
      refine ⟨_, rfl, Or.inl ⟨rfl, ?_⟩⟩
      simp only [dec_dsS, hwv]; rfl
    · have n2 : i32S i ≠ 2 := fun h => hi2 (dec_i32S_inj _ _ (by rw [h]; decide))
      simp only [Option.map_some]
      split
      · exfalso; exact hi2 (by decide)
      · refine ⟨_, rfl, Or.inl ⟨rfl, ?_⟩⟩
        split
        · exfalso; rename_i x heq; simp at heq; exact n2 heq
        · rfl

def dec_cpiOk (c : beatmap.control_points.ControlPointInfo) (k : Nat) : Prop :=
  c.timing_points.val.length + k < 2^31 ∧ c.difficulty_points.val.length + k < 2^31 ∧ c.effect_points.val.length + k < 2^31

theorem dec_getLast_idx {α β} (l : List α) (f : α → β) (h : 0 < l.length) (i : Usize) (hi : i.val = l.length - 1) :
    (l.map f).getLast? = some (f (l[i.val]'(by omega))) := by
  rw [List.getLast?_eq_getElem?]; simp [hi, List.getElem?_eq_getElem (show l.length - 1 < l.length by omega)]

theorem beatmap.decoder.flush_pending_points_refines (s : beatmap.decoder.DecoderState) (k : Nat) (hc : dec_cpiOk s.cpi (k+1)) :
    ∃ c', beatmap.decoder.flush_pending_points s = ok { s with cpi := c', pending := { s.pending with
        timing := alloc.vec.Vec.new _, difficulty := alloc.vec.Vec.new _, effect := alloc.vec.Vec.new _ } } ∧
      dec_dsS { s with cpi := c', pending := { s.pending with
        timing := alloc.vec.Vec.new _, difficulty := alloc.vec.Vec.new _, effect := alloc.vec.Vec.new _ } } =
        LegacyBeatmapDecoder.flushPendingPoints (dec_dsS s) ∧ dec_cpiOk c' k := by
  unfold beatmap.decoder.flush_pending_points LegacyBeatmapDecoder.flushPendingPoints
  obtain ⟨h1, h2, h3⟩ := hc
  have hu : (2:Nat)^31 ≤ Usize.max := by have := usize_ge_32; omega
  -- timing
  obtain ⟨c1, hc1, hc1v, hc1t⟩ : ∃ c1, (if alloc.vec.Vec.len s.pending.timing > 0#usize then do
        let i ← alloc.vec.Vec.len s.pending.timing - 1#usize
        let p ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice beatmap.control_points.TimingPoint) s.pending.timing i
        beatmap.control_points.add_timing s.cpi { p with time := s.pending.time }
      else ok s.cpi) = ok c1 ∧
      cpS c1 = (match (dec_pendS s.pending).timing.getLast? with
        | some p => (cpS s.cpi).addTiming { p with time := (dec_pendS s.pending).time }
        | none => cpS s.cpi) ∧
      (c1.timing_points.val.length ≤ s.cpi.timing_points.val.length + 1 ∧ c1.difficulty_points = s.cpi.difficulty_points ∧
        c1.effect_points = s.cpi.effect_points) := by
    by_cases hn : s.pending.timing.val.length > 0
    · have hn' : alloc.vec.Vec.len s.pending.timing > 0#usize := by show (0#usize : Usize).val < _; simpa using hn
      obtain ⟨i, hi, hiv⟩ := usize_sub_one (alloc.vec.Vec.len s.pending.timing) (by simp; omega)
      simp at hiv
      have hl : i.val < s.pending.timing.val.length := by omega
      obtain ⟨c', hc', hc'v, hd, he, hlen⟩ := beatmap.control_points.add_timing_refines s.cpi
        { s.pending.timing.val[i.val]'hl with time := s.pending.time } (by omega)
      refine ⟨c', by simp only [hn', if_true, hi, bind_ok, vec_index_eq' _ i hl, hc'], ?_, hlen, hd, he⟩
      rw [hc'v]; simp only [dec_pendS]; rw [dec_getLast_idx _ tpS hn i hiv]; rfl
    · have hn' : ¬ alloc.vec.Vec.len s.pending.timing > 0#usize := by show ¬ (0#usize : Usize).val < _; simpa using hn
      have : s.pending.timing.val = [] := by simpa using hn
      exact ⟨s.cpi, by simp only [hn', if_false], by simp [dec_pendS, this], by omega, rfl, rfl⟩
  -- difficulty
  obtain ⟨c2, hc2, hc2v, hc2t⟩ : ∃ c2, (if alloc.vec.Vec.len s.pending.difficulty > 0#usize then do
        let i ← alloc.vec.Vec.len s.pending.difficulty - 1#usize
        let p ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice beatmap.control_points.DifficultyPoint) s.pending.difficulty i
        beatmap.control_points.add_difficulty c1 { p with time := s.pending.time }
      else ok c1) = ok c2 ∧
      cpS c2 = (match (dec_pendS s.pending).difficulty.getLast? with
        | some p => (cpS c1).addDifficulty { p with time := (dec_pendS s.pending).time }
        | none => cpS c1) ∧
      (c2.difficulty_points.val.length ≤ c1.difficulty_points.val.length + 1 ∧ c2.timing_points = c1.timing_points ∧
        c2.effect_points = c1.effect_points) := by
    by_cases hn : s.pending.difficulty.val.length > 0
    · have hn' : alloc.vec.Vec.len s.pending.difficulty > 0#usize := by show (0#usize : Usize).val < _; simpa using hn
      obtain ⟨i, hi, hiv⟩ := usize_sub_one (alloc.vec.Vec.len s.pending.difficulty) (by simp; omega)
      simp at hiv
      have hl : i.val < s.pending.difficulty.val.length := by omega
      obtain ⟨c', hc', hc'v, hd, he, hlen⟩ := beatmap.control_points.add_difficulty_refines c1
        { s.pending.difficulty.val[i.val]'hl with time := s.pending.time } (by rw [hc1t.2.1]; omega)
      refine ⟨c', by simp only [hn', if_true, hi, bind_ok, vec_index_eq' _ i hl, hc'], ?_, hlen, hd, he⟩
      rw [hc'v]; simp only [dec_pendS]; rw [dec_getLast_idx _ dpS hn i hiv]; rfl
    · have hn' : ¬ alloc.vec.Vec.len s.pending.difficulty > 0#usize := by show ¬ (0#usize : Usize).val < _; simpa using hn
      have : s.pending.difficulty.val = [] := by simpa using hn
      exact ⟨c1, by simp only [hn', if_false], by simp [dec_pendS, this], by omega, rfl, rfl⟩
  -- effect
  obtain ⟨c3, hc3, hc3v, hc3t⟩ : ∃ c3, (if alloc.vec.Vec.len s.pending.effect > 0#usize then do
        let i ← alloc.vec.Vec.len s.pending.effect - 1#usize
        let p ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice beatmap.control_points.EffectPoint) s.pending.effect i
        beatmap.control_points.add_effect c2 { p with time := s.pending.time }
      else ok c2) = ok c3 ∧
      cpS c3 = (match (dec_pendS s.pending).effect.getLast? with
        | some p => (cpS c2).addEffect { p with time := (dec_pendS s.pending).time }
        | none => cpS c2) ∧
      (c3.effect_points.val.length ≤ c2.effect_points.val.length + 1 ∧ c3.timing_points = c2.timing_points ∧
        c3.difficulty_points = c2.difficulty_points) := by
    by_cases hn : s.pending.effect.val.length > 0
    · have hn' : alloc.vec.Vec.len s.pending.effect > 0#usize := by show (0#usize : Usize).val < _; simpa using hn
      obtain ⟨i, hi, hiv⟩ := usize_sub_one (alloc.vec.Vec.len s.pending.effect) (by simp; omega)
      simp at hiv
      have hl : i.val < s.pending.effect.val.length := by omega
      obtain ⟨c', hc', hc'v, hd, he, hlen⟩ := beatmap.control_points.add_effect_refines c2
        { s.pending.effect.val[i.val]'hl with time := s.pending.time } (by rw [hc2t.2.2, hc1t.2.2]; omega)
      refine ⟨c', by simp only [hn', if_true, hi, bind_ok, vec_index_eq' _ i hl, hc'], ?_, hlen, hd, he⟩
      rw [hc'v]; simp only [dec_pendS]; rw [dec_getLast_idx _ epS hn i hiv]; rfl
    · have hn' : ¬ alloc.vec.Vec.len s.pending.effect > 0#usize := by show ¬ (0#usize : Usize).val < _; simpa using hn
      have : s.pending.effect.val = [] := by simpa using hn
      exact ⟨c2, by simp only [hn', if_false], by simp [dec_pendS, this], by omega, rfl, rfl⟩
  simp only [hc1, hc2, hc3, bind_ok]
  refine ⟨c3, rfl, ?_, ?_⟩
  · simp only [dec_dsS, dec_pendS, hc3v, hc2v, hc1v, alloc.vec.Vec.new]; rfl
  · have a1 := hc1t.1; have a2 := hc2t.1; have a3 := hc3t.1
    have b1 := congrArg (fun v => v.val.length) hc1t.2.1; have b2 := congrArg (fun v => v.val.length) hc1t.2.2
    have b3 := congrArg (fun v => v.val.length) hc2t.2.1; have b4 := congrArg (fun v => v.val.length) hc2t.2.2
    have b5 := congrArg (fun v => v.val.length) hc3t.2.1; have b6 := congrArg (fun v => v.val.length) hc3t.2.2
    refine ⟨by omega, by omega, by omega⟩

theorem beatmap.decoder.add_line_points_refines (s : beatmap.decoder.DecoderState) (k : Nat) (hc : dec_cpiOk s.cpi (k+1))
    (hp : s.pending.timing.val.length + 1 < Usize.max ∧ s.pending.difficulty.val.length + 1 < Usize.max ∧
      s.pending.effect.val.length + 1 < Usize.max)
    (time : F64) (timing : Option beatmap.control_points.TimingPoint) (diff : beatmap.control_points.DifficultyPoint)
    (eff : beatmap.control_points.EffectPoint) (tc : Bool) :
    ∃ s', beatmap.decoder.add_line_points s time timing diff eff tc = ok s' ∧
      dec_dsS s' = LegacyBeatmapDecoder.addLinePoints (dec_dsS s) time (timing.map tpS) (dpS diff) (epS eff) tc ∧
      dec_cpiOk s'.cpi k ∧ s'.pending.timing.val.length ≤ s.pending.timing.val.length + 1 ∧
      s'.pending.difficulty.val.length ≤ s.pending.difficulty.val.length + 1 ∧
      s'.pending.effect.val.length ≤ s.pending.effect.val.length + 1 ∧
      s'.breaks = s.breaks ∧ s'.hit_objects = s.hit_objects ∧ s'.parser = s.parser ∧ s'.sect = s.sect ∧
      s'.ruleset_id = s.ruleset_id ∧ s'.offset = s.offset ∧ s'.format_version = s.format_version := by
  unfold beatmap.decoder.add_line_points LegacyBeatmapDecoder.addLinePoints
  obtain ⟨s1, hs1, hs1v, hc1, hp1, hrest⟩ : ∃ s1, (if (time == s.pending.time) = true then ok s else beatmap.decoder.flush_pending_points s) = ok s1 ∧
      dec_dsS s1 = (if (!(time == (dec_dsS s).pending.time)) = true then LegacyBeatmapDecoder.flushPendingPoints (dec_dsS s) else dec_dsS s) ∧
      dec_cpiOk s1.cpi k ∧ (s1.pending.timing.val.length ≤ s.pending.timing.val.length ∧
        s1.pending.difficulty.val.length ≤ s.pending.difficulty.val.length ∧ s1.pending.effect.val.length ≤ s.pending.effect.val.length) ∧
      (s1.breaks = s.breaks ∧ s1.hit_objects = s.hit_objects ∧ s1.parser = s.parser ∧ s1.sect = s.sect ∧
       s1.ruleset_id = s.ruleset_id ∧ s1.offset = s.offset ∧ s1.format_version = s.format_version) := by
    have ht : (dec_dsS s).pending.time = s.pending.time := rfl
    rw [ht]
    cases hb : (time == s.pending.time)
    · obtain ⟨c', hf, hfv, hok⟩ := beatmap.decoder.flush_pending_points_refines s k hc
      simp only [Bool.false_eq_true, if_false, Bool.not_false, if_true, hf]
      exact ⟨_, rfl, hfv, hok, by simp [alloc.vec.Vec.new], by simp⟩
    · obtain ⟨h1, h2, h3⟩ := hc
      simp only [if_true, Bool.not_true, Bool.false_eq_true, if_false]
      exact ⟨s, rfl, rfl, ⟨by omega, by omega, by omega⟩, ⟨le_refl _, le_refl _, le_refl _⟩, by simp⟩
  simp only [float.F64.eq, hs1, bind_ok]
  rw [← hs1v]
  obtain ⟨q1, q2, q3⟩ := hp
  obtain ⟨p1, p2, p3⟩ := hp1
  cases timing with
  | none =>
    simp only [bind_ok]
    cases tc with
    | true =>
      obtain ⟨wd, hwd, hwdv⟩ := beatmap.dotnet.insert_at_refines beatmap.control_points.DifficultyPoint.Insts.CoreCloneClone (fun _ => rfl)
        s1.pending.difficulty 0#usize diff (by simp) (by omega)
      obtain ⟨we, hwe, hwev⟩ := beatmap.dotnet.insert_at_refines beatmap.control_points.EffectPoint.Insts.CoreCloneClone (fun _ => rfl)
        s1.pending.effect 0#usize eff (by simp) (by omega)
      simp only [if_true, hwd, hwe, bind_ok]
      refine ⟨_, rfl, ?_, hc1, by simp [*] <;> omega, by simp [*] <;> omega, by simp [*] <;> omega, by simp [hrest]⟩
      simp [dec_dsS, dec_pendS, *]
    | false =>
      obtain ⟨wd, hwd, hwdv⟩ := push_eq s1.pending.difficulty diff (by omega)
      obtain ⟨we, hwe, hwev⟩ := push_eq s1.pending.effect eff (by omega)
      simp only [Bool.false_eq_true, if_false, hwd, hwe, bind_ok]
      refine ⟨_, rfl, ?_, hc1, by simp [*] <;> omega, by simp [*] <;> omega, by simp [*] <;> omega, by simp [hrest]⟩
      simp [dec_dsS, dec_pendS, *]
  | some tp =>
    cases tc with
    | true =>
      obtain ⟨w, hw, hwv⟩ := beatmap.dotnet.insert_at_refines beatmap.control_points.TimingPoint.Insts.CoreCloneClone (fun _ => rfl)
        s1.pending.timing 0#usize tp (by simp) (by omega)
      simp only [hw, bind_ok]
      obtain ⟨wd, hwd, hwdv⟩ := beatmap.dotnet.insert_at_refines beatmap.control_points.DifficultyPoint.Insts.CoreCloneClone (fun _ => rfl)
        s1.pending.difficulty 0#usize diff (by simp) (by omega)
      obtain ⟨we, hwe, hwev⟩ := beatmap.dotnet.insert_at_refines beatmap.control_points.EffectPoint.Insts.CoreCloneClone (fun _ => rfl)
        s1.pending.effect 0#usize eff (by simp) (by omega)
      simp only [if_true, hwd, hwe, bind_ok]
      refine ⟨_, rfl, ?_, hc1, by simp [*] <;> omega, by simp [*] <;> omega, by simp [*] <;> omega, by simp [hrest]⟩
      simp [dec_dsS, dec_pendS, *]
    | false =>
      obtain ⟨w, hw, hwv⟩ := beatmap.dotnet.insert_at_refines beatmap.control_points.TimingPoint.Insts.CoreCloneClone (fun _ => rfl)
        s1.pending.timing 0#usize tp (by simp) (by omega)
      simp only [hw, bind_ok]
      obtain ⟨wd, hwd, hwdv⟩ := push_eq s1.pending.difficulty diff (by omega)
      obtain ⟨we, hwe, hwev⟩ := push_eq s1.pending.effect eff (by omega)
      simp only [Bool.false_eq_true, if_false, hwd, hwe, bind_ok]
      refine ⟨_, rfl, ?_, hc1, by simp [*] <;> omega, by simp [*] <;> omega, by simp [*] <;> omega, by simp [hrest]⟩
      simp [dec_dsS, dec_pendS, *]

theorem beatmap.decoder.apply_decode_defaults_refines (cpi : beatmap.control_points.ControlPointInfo)
    (h : beatmap.types.ConvertHitObject) (hc : cpi.difficulty_points.val.length < 2^31) :
    ∃ h', beatmap.decoder.apply_decode_defaults cpi h = ok h' ∧
      choS h' = LegacyBeatmapDecoder.applyDecodeDefaults (cpS cpi) (choS h) ∧ h'.start_time = h.start_time := by
  unfold beatmap.decoder.apply_decode_defaults LegacyBeatmapDecoder.applyDecodeDefaults
  rcases hk : h.kind with _ | ⟨cps, d, r⟩ | d | d
  all_goals simp only [hk]
  · exact ⟨h, rfl, by simp [choS, hk, ckS], rfl⟩
  · rw [beatmap.control_points.difficulty_point_at_refines cpi h.start_time hc, bind_ok]
    refine ⟨_, rfl, ?_, rfl⟩
    simp [choS, hk, ckS, dpI]
  · exact ⟨h, rfl, by simp [choS, hk, ckS], rfl⟩
  · exact ⟨h, rfl, by simp [choS, hk, ckS], rfl⟩

def dec_ppIn (B : _root_.Array BreakPeriod) (hT : F64) (_ : Nat) (s : Nat × Bool) : ForInStep (Nat × Bool) :=
  if (decide (s.1 < B.size) && decide (B[s.1]!.endTime < hT)) = true then .yield (s.1 + 1, true) else .yield s
def dec_ppOut (B : _root_.Array BreakPeriod) (hos : _root_.Array ConvertHitObject) (j : Nat)
    (s : Nat × _root_.Array ConvertHitObject) : ForInStep (Nat × _root_.Array ConvertHitObject) :=
  let h := hos[j]!
  let r := iterR (dec_ppIn B h.startTime) 0 (B.size - 0) (s.1, false)
  .yield (r.1, s.2.push { h with newCombo := h.newCombo || r.2 })

theorem dec_pp_eq (B : _root_.Array BreakPeriod) (hos : _root_.Array ConvertHitObject) :
    LegacyBeatmapDecoder.postProcessBreaks B hos = (iterR (dec_ppOut B hos) 0 hos.size (0, #[])).2 := by
  unfold LegacyBeatmapDecoder.postProcessBreaks
  simp only [Id.run]
  rw [forIn_array_iterR]
  change (iterR _ 0 hos.size (0, #[])).2 = _
  congr 2
  funext j acc
  rw [forIn_range_iterR]
  simp only [dec_ppOut]
  have : (fun (_ : Nat) (__s : Nat × Bool) =>
      (if (decide (__s.1 < B.size) && decide (B[__s.1]!.endTime < hos[j]!.startTime)) = true then
        pure (ForInStep.yield (__s.1 + 1, true)) else pure (ForInStep.yield (__s.1, __s.2)) : Id (ForInStep (Nat × Bool)))) =
      dec_ppIn B hos[j]!.startTime := by
    funext x s; simp only [dec_ppIn]; split <;> rfl
  rw [this]; rfl

def dec_bpsA (b : Slice beatmap.types.BreakPeriod) : _root_.Array BreakPeriod := (b.val.map dec_bpS).toArray

theorem dec_pp_inner2 (breaks : Slice beatmap.types.BreakPeriod) (hos : alloc.vec.Vec beatmap.types.ConvertHitObject)
    (i : Usize) (hi : i.val < hos.val.length) (cb : Usize) (hcb : cb.val ≤ breaks.val.length) :
    ∃ y, beatmap.decoder.post_process_breaks_loop0_loop0 breaks hos cb i false 0#usize = ok y ∧
      (y.1.val, y.2) = iterR (dec_ppIn (dec_bpsA breaks) (hos.val[i.val]'hi).start_time) 0 (breaks.val.length - 0) (cb.val, false) ∧
      y.1.val ≤ breaks.val.length := by
  unfold beatmap.decoder.post_process_breaks_loop0_loop0
  have hmax : breaks.val.length ≤ Usize.max := breaks.property
  have := loop_iterR (fun (t : Usize × Bool × Usize) => beatmap.decoder.post_process_breaks_loop0_loop0.body breaks hos i t.1 t.2.1 t.2.2)
    (dec_ppIn (dec_bpsA breaks) (hos.val[i.val]'hi).start_time) breaks.val.length (fun t => t.2.2.val)
    (fun t s => s = (t.1.val, t.2.1) ∧ t.1.val ≤ breaks.val.length ∧ t.2.2.val ≤ breaks.val.length)
    (fun y s => s = (y.1.val, y.2) ∧ y.1.val ≤ breaks.val.length)
    (by
      rintro ⟨c, f, k⟩ s ⟨rfl, hc, hkn⟩ hk
      dsimp only at hc hk hkn ⊢
      have hk' : k < Slice.len breaks := by show k.val < (Slice.len breaks).val; simpa using hk
      obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by omega)
      constructor
      · intro s' hs'
        unfold dec_ppIn at hs'
        by_cases hcl : c.val < breaks.val.length
        · have hcl' : c < Slice.len breaks := by show c.val < (Slice.len breaks).val; simpa using hcl
          have hgb : (dec_bpsA breaks)[c.val]! = dec_bpS (breaks.val[c.val]'hcl) := by
            rw [getElem!_pos _ _ (by simpa [dec_bpsA] using hcl)]; simp [dec_bpsA]
          by_cases hlt : (breaks.val[c.val]'hcl).end_time < (hos.val[i.val]'hi).start_time
          · obtain ⟨c1, hc1, hc1v⟩ := usize_add_one c (by omega)
            have : (decide (c.val < (dec_bpsA breaks).size) && decide ((dec_bpsA breaks)[c.val]!.endTime < (hos.val[i.val]'hi).start_time)) = true := by
              simp [hgb, dec_bpS, hlt, dec_bpsA, hcl]
            rw [if_pos this] at hs'; cases hs'
            refine ⟨(c1, true, k1), ?_, by simp [hk1v], ?_, ?_⟩
            · simp [beatmap.decoder.post_process_breaks_loop0_loop0.body, hk', hcl', index_eq breaks c hcl,
                vec_index_eq' hos i hi, hlt, hc1, hk1]
            · simp [hc1v]
            · dsimp only; constructor <;> omega
          · have : (decide (c.val < (dec_bpsA breaks).size) && decide ((dec_bpsA breaks)[c.val]!.endTime < (hos.val[i.val]'hi).start_time)) = false := by
              simp [hgb, dec_bpS, hlt]
            rw [if_neg (by simp [this])] at hs'; cases hs'
            refine ⟨(c, f, k1), ?_, by simp [hk1v], rfl, by dsimp only; constructor <;> omega⟩
            simp [beatmap.decoder.post_process_breaks_loop0_loop0.body, hk', hcl', index_eq breaks c hcl,
              vec_index_eq' hos i hi, hlt, hk1]
        · have hcl' : ¬ c < Slice.len breaks := by show ¬ c.val < (Slice.len breaks).val; simpa using hcl
          have : (decide (c.val < (dec_bpsA breaks).size) && decide ((dec_bpsA breaks)[c.val]!.endTime < (hos.val[i.val]'hi).start_time)) = false := by
            simp [dec_bpsA, hcl]
          rw [if_neg (by simp [this])] at hs'; cases hs'
          refine ⟨(c, f, k1), ?_, by simp [hk1v], rfl, by dsimp only; constructor <;> omega⟩
          simp [beatmap.decoder.post_process_breaks_loop0_loop0.body, hk', hcl', hk1]
      · intro s' hs'; unfold dec_ppIn at hs'; split at hs' <;> cases hs')
    (by
      rintro ⟨c, f, k⟩ s ⟨rfl, hc, hkn⟩ hk
      dsimp only at hc hk hkn ⊢
      have hk' : ¬ k < Slice.len breaks := by show ¬ k.val < (Slice.len breaks).val; simpa using hk
      exact ⟨(c, f), by simp [beatmap.decoder.post_process_breaks_loop0_loop0.body, hk'], rfl, by dsimp only; omega⟩)
    (cb, false, 0#usize) (cb.val, false) ⟨rfl, hcb, by simp⟩ (by simp)
  obtain ⟨y, hy, hq, hb⟩ := this
  exact ⟨y, hy, by simpa using hq.symm, hb⟩

theorem dec_pp_outer (breaks : Slice beatmap.types.BreakPeriod) (hos : alloc.vec.Vec beatmap.types.ConvertHitObject) :
    ∃ w, beatmap.decoder.post_process_breaks_loop0 breaks hos 0#usize 0#usize = ok w ∧
      w.val.map choS = (iterR (dec_ppOut (dec_bpsA breaks) (hos.val.map choS).toArray) 0 hos.val.length (0, #[])).2.toList := by
  unfold beatmap.decoder.post_process_breaks_loop0
  have hmax : hos.val.length ≤ Usize.max := hos.property
  have := loop_iterR (fun (t : alloc.vec.Vec beatmap.types.ConvertHitObject × Usize × Usize) =>
      beatmap.decoder.post_process_breaks_loop0.body breaks t.1 t.2.1 t.2.2)
    (dec_ppOut (dec_bpsA breaks) (hos.val.map choS).toArray) hos.val.length (fun t => t.2.2.val)
    (fun t s => s.1 = t.2.1.val ∧ t.2.1.val ≤ breaks.val.length ∧ t.1.val.length = hos.val.length ∧
      (t.1.val.take t.2.2.val).map choS = s.2.toList ∧ t.1.val.drop t.2.2.val = hos.val.drop t.2.2.val)
    (fun y s => y.val.map choS = s.2.toList)
    (by
      rintro ⟨h', c, i⟩ ⟨sc, sa⟩ ⟨hsc, hcb, hlen, htk, hdr⟩ hi
      dsimp only at hsc hcb hlen htk hdr hi ⊢
      subst hsc
      have hi' : i.val < h'.val.length := by omega
      have hget : h'.val[i.val]'hi' = hos.val[i.val]'hi := by
        have := congrArg (fun l => l[0]?) hdr
        simp only [List.getElem?_drop, Nat.add_zero] at this
        rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi] at this
        simpa using this
      obtain ⟨⟨yc, yf⟩, hy, hyq, hyb⟩ := dec_pp_inner2 breaks h' i hi' c hcb
      rw [hget] at hyq
      have hyq' : (yc.val, yf) = iterR (dec_ppIn (dec_bpsA breaks) (hos.val[i.val]'hi).start_time) 0 (dec_bpsA breaks).size (c.val, false) := by
        rw [hyq]; simp [dec_bpsA]
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
      have hA : ((hos.val.map choS).toArray)[i.val]! = choS (hos.val[i.val]'hi) := by
        rw [getElem!_pos _ _ (by simpa using hi)]; simp
      constructor
      · intro s' hs'
        simp only [dec_ppOut, hA] at hs'
        cases hs'
        have hlt : i < alloc.vec.Vec.len h' := by show i.val < (alloc.vec.Vec.len h').val; simpa using hi'
        refine ⟨(alloc.vec.Vec.set h' i { (hos.val[i.val]'hi) with new_combo := (hos.val[i.val]'hi).new_combo || yf }, yc, i1),
          ?_, by simp [hi1v], ?_⟩
        · simp only [beatmap.decoder.post_process_breaks_loop0.body, if_pos hlt, hy, bind_ok, uncurry_apply_pair,
            vec_index_eq' h' i hi', vec_index_mut_eq h' i hi', hi1, hget]
          cases (hos.val[i.val]'hi).new_combo <;> simp
        · dsimp only
          refine ⟨?_, hyb, by simp [hlen], ?_, ?_⟩
          · have := congrArg Prod.fst hyq'; simpa [choS] using this.symm
          · rw [hi1v]
            simp only [alloc.vec.Vec.set_val_eq]
            rw [List.take_succ, List.take_set_of_le (by omega), List.map_append, htk]
            rw [List.getElem?_set_self (by omega)]
            have := congrArg Prod.snd hyq'
            simp only at this
            simp [choS, ← this]
          · rw [hi1v]
            simp only [alloc.vec.Vec.set_val_eq]
            rw [List.drop_set_of_lt (by omega)]
            have := congrArg (List.drop 1) hdr
            simpa [List.drop_drop, Nat.add_comm] using this
      · intro s' hs'; simp [dec_ppOut] at hs')
    (by
      rintro ⟨h', c, i⟩ ⟨sc, sa⟩ ⟨hsc, hcb, hlen, htk, hdr⟩ hi
      dsimp only at hsc hcb hlen htk hdr hi ⊢
      have hlt : ¬ i < alloc.vec.Vec.len h' := by show ¬ i.val < (alloc.vec.Vec.len h').val; simp; omega
      refine ⟨h', by simp [beatmap.decoder.post_process_breaks_loop0.body, hlt], ?_⟩
      rw [← htk, List.take_of_length_le (by omega)])
    (hos, 0#usize, 0#usize) (0, #[]) ⟨by simp, by simp, rfl, by simp, by simp⟩ (by simp)
  obtain ⟨y, hy, hq⟩ := this
  exact ⟨y, hy, by simpa using hq⟩

theorem beatmap.decoder.post_process_breaks_refines (breaks : Slice beatmap.types.BreakPeriod)
    (hos : alloc.vec.Vec beatmap.types.ConvertHitObject) :
    ∃ w, beatmap.decoder.post_process_breaks breaks hos = ok w ∧
      (w.val.map choS).toArray = LegacyBeatmapDecoder.postProcessBreaks (dec_bpsA breaks) (hos.val.map choS).toArray := by
  obtain ⟨w, hw, hq⟩ := dec_pp_outer breaks hos
  refine ⟨w, hw, ?_⟩
  rw [dec_pp_eq, hq]; simp

end OsuProofs
