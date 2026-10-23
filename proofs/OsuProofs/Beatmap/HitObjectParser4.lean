/-
`beatmap::hit_object_parser` part 4: `parse_slider` and `parse`. The spec's slider body (`let mut length`,
`if` without `else`) is first shown equal to the straight-line chain `hop_sliderC` (`hop_slider_eq`, case
analysis); `parse` is related through `hop_parse_eq : parse = hop_parseS st (hop_preSpec ...)` (rfl) and the
local `finish` (`hop_finS`). Extra hypotheses: `numBits = 64` and, for the slider path, that the spec control
points of field 5 number < 2^32 with `calculatePath` output < 2^62 (from `slider_path.of_control_points_refines`).
Helper names are prefixed `hop_`.
-/
import OsuProofs.Beatmap.HitObjectParser3
import OsuProofs.Beatmap.SliderPath
import OsuProofs.Beatmap.Vector2
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

/-- The slider branch `r` of `ConvertHitObjectParser.parse` (verbatim; `nc` = `newComboOf combo`). -/
def hop_sliderS (st : ParserState) (split : _root_.Array String) (pos : Vec2) (startTime : F64) (combo : Bool)
    (comboOffset : Int32) (nc : Bool) : DecodeM ConvertHitObject := do
      let repeatCount0 ← liftNet "repeatCount" (Parsing.parseInt (← at! split 6))
      if repeatCount0 > 9000 then throw "Repeat count is way too high"
      let repeatCount : Int32 := if repeatCount0 - 1 < 0 then 0 else repeatCount0 - 1
      let mut length : Option F64 := none
      if split.size > 7 then
        let l := F64.max 0 (← liftNet "length" (Parsing.parseDouble split[7]! (F64.ofInt Parsing.MAX_COORDINATE_VALUE.toInt)))
        length := if l == 0 then none else some l
      if split.size > 10 then ConvertHitObjectParser.readCustomSampleBanks split[10]! true
      let nodes := repeatCount.toNatClampNeg + 2
      if split.size > 9 && split[9]!.length > 0 then
        let sets := OsuModel.Beatmap.split split[9]! '|'
        for i in [0:nodes] do
          if i < sets.size then ConvertHitObjectParser.readCustomSampleBanks sets[i]!
      let controlPoints ← ConvertHitObjectParser.convertPathString st.formatVersion (← at! split 5) pos
      let path := SliderPath.ofControlPoints controlPoints length false
      if path.fuelOut then throw pathFuelMsg
      let repeatCount := if Precision.almostEqualsF64 path.distance 0 then 0 else repeatCount
      return { startTime, position := pos, newCombo := nc,
               comboOffset := if combo then comboOffset else 0,
               kind := .slider controlPoints length repeatCount }

def hop_RC (split : _root_.Array String) : DecodeM Int32 := do
  let rc0 ← liftNet "repeatCount" (OsuModel.Net.Parsing.parseInt (← at! split 6))
  if rc0 > 9000 then throw "Repeat count is way too high"
  else pure (if rc0 - 1 < 0 then 0 else rc0 - 1)
def hop_LEN (sp : _root_.Array String) : DecodeM (Option F64) :=
  if sp.size > 7 then do
    let l := F64.max 0 (← liftNet "length" (Parsing.parseDouble sp[7]! (F64.ofInt Parsing.MAX_COORDINATE_VALUE.toInt)))
    pure (if l == 0 then none else some l)
  else pure none
def hop_CB (sp : _root_.Array String) : DecodeM Unit :=
  if sp.size > 10 then ConvertHitObjectParser.readCustomSampleBanks sp[10]! true else pure ()
def hop_NB (sp : _root_.Array String) (nodes : Nat) : DecodeM Unit :=
  if sp.size > 9 && sp[9]!.length > 0 then (do
    let sets := OsuModel.Beatmap.split sp[9]! '|'
    for i in [0:nodes] do
      if i < sets.size then ConvertHitObjectParser.readCustomSampleBanks sets[i]!
    : DecodeM Unit) else pure ()

def hop_sliderC (st : ParserState) (split : _root_.Array String) (pos : Vec2) (startTime : F64) (combo : Bool)
    (comboOffset : Int32) (nc : Bool) : DecodeM ConvertHitObject := do
  let rc ← hop_RC split
  let len ← hop_LEN split
  hop_CB split
  hop_NB split (rc.toNatClampNeg + 2)
  let cps ← ConvertHitObjectParser.convertPathString st.formatVersion (← at! split 5) pos
  if (SliderPath.ofControlPoints cps len false).fuelOut then throw pathFuelMsg
  else
  pure { startTime, position := pos, newCombo := nc, comboOffset := if combo then comboOffset else 0,
         kind := .slider cps len
           (if Precision.almostEqualsF64 (SliderPath.ofControlPoints cps len false).distance 0 then 0 else rc) }

set_option maxHeartbeats 4000000 in
theorem hop_slider_eq (st : ParserState) (split : _root_.Array String) (pos : Vec2) (startTime : F64) (combo : Bool)
    (comboOffset : Int32) (nc : Bool) :
    hop_sliderS st split pos startTime combo comboOffset nc = hop_sliderC st split pos startTime combo comboOffset nc := by
  unfold hop_sliderS hop_sliderC hop_RC hop_LEN hop_CB hop_NB
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  cases at! split 6 <;> simp only []
  rename_i t6
  cases liftNet "repeatCount" (Parsing.parseInt t6) <;> simp only []
  rename_i rc0
  by_cases h7 : split.size > 7 <;> by_cases h9 : split.size > 9 <;> by_cases h10 : split.size > 10 <;>
    (try (exfalso; omega)) <;> simp only [h7, h9, h10, ite_true, ite_false]
  all_goals (repeat' split)
  all_goals first | rfl | assumption | (exfalso; omega) | (simp only [Except.error.injEq, Except.ok.injEq, reduceCtorEq] at *; done) | (simp_all; done) | (simp only [Except.ok.injEq] at *; subst_vars; simp_all; done) | (rename_i h; split at h <;> simp_all; done)

theorem hop_umax64 (h64 : System.Platform.numBits = 64) : Usize.max = 2^64 - 1 := by
  simp [Usize.max, Usize.numBits, h64]

theorem hop_hcast_i32 (x : I32) (h0 : 0 ≤ x.val) : (IScalar.hcast .Usize x).val = x.val.toNat := by
  rw [IScalar.hcast_val_eq]
  have : (2:Int)^31 ≤ 2^UScalarTy.Usize.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.Usize_numBits_eq, h]
  have h1 : x.val < 2^31 := by have := x.hmax; simp at this; omega
  rw [Int.emod_eq_of_lt h0 (by omega)]

theorem hop_pcp_clone (v : alloc.vec.Vec beatmap.types.PathControlPoint) :
    alloc.vec.CloneVec.clone beatmap.types.PathControlPoint.Insts.CoreCloneClone v = ok v := by
  obtain ⟨s, hs, hsv⟩ := eq_ok_of_spec (Slice.clone_spec (clone := beatmap.types.PathControlPoint.Insts.CoreCloneClone.clone)
    (s := v.slice) (by intro x _; rfl))
  simp only [alloc.vec.CloneVec.clone, beatmap.types.PathControlPoint.Insts.CoreCloneClone, hs, bind_ok, ← hsv]
  rw [bind_tc_ok]

theorem hop_at_get (a : _root_.Array String) (i : Nat) (x : String) (h : at! a i = .ok x) : a[i]! = x := by
  unfold at! at h
  split at h
  · rename_i hi; simp only [Except.ok.injEq] at h; rw [getElem!_pos a i hi]; exact h
  · cases h

theorem hop_RC_nonneg (S : _root_.Array String) (r : Int32) (h : hop_RC S = .ok r) : 0 ≤ r.toInt := by
  unfold hop_RC at h
  cases h1 : at! S 6 with
  | error e => rw [h1] at h; cases h
  | ok t =>
    rw [h1] at h
    cases h2 : liftNet "repeatCount" (Parsing.parseInt t) with
    | error e => simp only [except_bind_ok, h2] at h; cases h
    | ok rc0 =>
      simp only [except_bind_ok, h2] at h
      split at h
      · cases h
      · simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
        subst h
        split
        · simp
        · rename_i hn; simp only [Int32.lt_iff_toInt_lt] at hn; simp at hn ⊢; omega

macro "hop_rstep2 " r:term:max h:term:max v:ident : tactic =>
  `(tactic| (rcases $r:term with $v:ident | e; (on_goal 2 => exact ⟨_, rfl, rel_err $h _ _⟩); simp only [rel_ok $h, except_bind_ok, id_eq]))

theorem beatmap.hit_object_parser.parse_slider_refines (st : beatmap.hit_object_parser.ParserState)
    (pre : beatmap.hit_object_parser.PreParse) (nc : Bool)
    (hV : ∀ l ∈ pre.split.val, ValidL l.val) (hL : ∀ l ∈ pre.split.val, l.val.length < 2^61)
    (h64 : System.Platform.numBits = 64)
    (hcp : ∀ cps, ConvertHitObjectParser.convertPathString (i32S st.format_version) (vstrs pre.split.val)[5]! (bv2S pre.pos) = .ok cps →
      cps.size < 2^32 ∧ ∀ len, (SliderPath.calculatePath { controlPoints := cps, expectedDistance := len, optimiseCatmull := false }).1.size < 2^62) :
    ∃ r, beatmap.hit_object_parser.parse_slider st pre nc = ok r ∧
      hRel choS r (hop_sliderS (psS st) (vstrs pre.split.val) (bv2S pre.pos) pre.start_time pre.combo (i32S pre.combo_offset) nc) := by
  rw [hop_slider_eq]
  unfold beatmap.hit_object_parser.parse_slider hop_sliderC
  simp only [psS]
  have hV' : ∀ l ∈ (alloc.vec.Vec.deref pre.split).val, ValidL l.val := by intro l hl; rw [deref_valA] at hl; exact hV l hl
  have hL62 : ∀ l ∈ (alloc.vec.Vec.deref pre.split).val, l.val.length < 2^62 := by
    intro l hl; rw [deref_valA] at hl; have := hL l hl; omega
  have hLm : ∀ l ∈ (alloc.vec.Vec.deref pre.split).val, l.val.length < Usize.max := by
    intro l hl; rw [deref_valA] at hl; have := hL l hl; rw [hop_umax64 h64]; omega
  -- repeat count
  obtain ⟨r0, h0, h0r⟩ := beatmap.hit_object_parser.ps_repeat_count_refines (alloc.vec.Vec.deref pre.split) hV'
  rw [deref_valA] at h0r
  change hRel i32S r0 (hop_RC (vstrs pre.split.val)) at h0r
  simp only [h0, bind_ok]
  hop_rstep2 r0 h0r rc
  have hrc0 : 0 ≤ rc.val := by have := hop_RC_nonneg _ _ (rel_ok h0r); rw [i32S_toInt] at this; exact this
  -- length
  obtain ⟨r1, h1, h1r⟩ := beatmap.hit_object_parser.ps_length_refines (alloc.vec.Vec.deref pre.split) hV' hL62
  rw [deref_valA] at h1r
  change hRel id r1 (hop_LEN (vstrs pre.split.val)) at h1r
  simp only [h1, bind_ok]
  hop_rstep2 r1 h1r len
  -- check banks
  obtain ⟨r2, h2, h2r⟩ := beatmap.hit_object_parser.ps_check_banks_refines (alloc.vec.Vec.deref pre.split) hV' hLm
  rw [deref_valA] at h2r
  change hRel id r2 (hop_CB (vstrs pre.split.val)) at h2r
  simp only [h2, bind_ok]
  hop_rstep2 r2 h2r u2
  -- node banks
  have hcast := hop_hcast_i32 rc hrc0
  obtain ⟨nodes, hnodes, hnodesv⟩ := usize_add_k (IScalar.hcast .Usize rc) 2#usize (by
    rw [hcast, hop_umax64 h64]; have := rc.hmax; simp at this ⊢; omega)
  simp only [lift, bind_ok, hnodes]
  obtain ⟨r3, h3, h3r⟩ := beatmap.hit_object_parser.ps_node_banks_refines (alloc.vec.Vec.deref pre.split) hV' hLm nodes
  rw [deref_valA] at h3r
  have hnv : nodes.val = (i32S rc).toNatClampNeg + 2 := by
    rw [hnodesv, hcast]; simp [Int32.toNatClampNeg, i32S_toInt]
  rw [hnv] at h3r
  change hRel id r3 (hop_NB (vstrs pre.split.val) ((i32S rc).toNatClampNeg + 2)) at h3r
  simp only [h3, bind_ok]
  hop_rstep2 r3 h3r u3
  -- control points
  have e5 : (5#usize : Usize).val = 5 := rfl
  obtain ⟨r4, h4, h4r, h4m⟩ := beatmap.hit_object_parser.at_refines (alloc.vec.Vec.deref pre.split) 5#usize
  rw [deref_valA, e5] at h4r; rw [deref_valA] at h4m
  simp only [h4, bind_ok]
  hop_rstep2 r4 h4r v2
  have hvm2 := h4m v2 rfl
  have h5idx : (vstrs pre.split.val)[5]! = strV v2 := hop_at_get _ _ _ (rel_ok h4r)
  have hl2 := hL v2 hvm2
  obtain ⟨r5, h5, h5r⟩ := beatmap.hit_object_parser.convert_path_string_refines st.format_version (alloc.vec.Vec.deref v2)
    (validStr_of v2 (hV v2 hvm2)) (by rw [deref_valA, hop_umax64 h64]; omega) (by rw [deref_valA]; omega) pre.pos
  rw [strV_deref] at h5r
  simp only [h5, bind_ok]
  hop_rstep2 r5 h5r v3
  obtain ⟨hcs, hcalc⟩ := hcp (hop_pcpsA v3) (by rw [h5idx]; exact rel_ok h5r)
  simp only [hop_pcp_clone, bind_ok]
  obtain ⟨path, hpath, hpathv⟩ := beatmap.slider_path.of_control_points_refines v3 len false h64
    (by simpa [hop_pcpsA] using hcs) (by have := hcalc len; simpa [hop_pcpsA, pcpsS] using this)
  have hD0 : beatmap.hit_object_parser.D0 = ok (0 : F64) := by
    unfold beatmap.hit_object_parser.D0; simp; decide
  simp only [hpath, bind_ok, beatmap.slider_path.distance_refines, hpathv, hD0, beatmap.vector2.almost_equals_f64_refines]
  have hpc : hop_pcpsA v3 = pcpsS v3.val := rfl
  rw [hpc]
  by_cases hf : path.fuel_out = true
  · have hf' : (SliderPath.ofControlPoints (pcpsS v3.val) len false).fuelOut = true := by rw [← hpathv]; exact hf
    simp only [hf, hf', ite_true]
    exact ⟨_, rfl, trivial⟩
  have hf' : (SliderPath.ofControlPoints (pcpsS v3.val) len false).fuelOut = false := by
    rw [← hpathv]; show path.fuel_out = false; simpa using hf
  simp only [hf, hf', ite_false, Bool.false_eq_true]
  by_cases hb : Precision.almostEqualsF64 (SliderPath.ofControlPoints (pcpsS v3.val) len false).distance 0 = true
  · by_cases hc : pre.combo = true
    · obtain ⟨o, ho, hov⟩ := beatmap.hit_object_parser.new_object_refines pre.start_time pre.pos nc pre.combo_offset
        (beatmap.types.ConvertKind.Slider v3 len 0#i32)
      simp only [hb, hc, ite_true, bind_ok, ho]
      refine ⟨_, rfl, ?_⟩
      show choS o = _
      have hz : i32S 0#i32 = 0 := by decide
      rw [hov]; simp [ckS, hb, hc, hz]
    · obtain ⟨o, ho, hov⟩ := beatmap.hit_object_parser.new_object_refines pre.start_time pre.pos nc 0#i32
        (beatmap.types.ConvertKind.Slider v3 len 0#i32)
      simp only [hb, hc, ite_true, ite_false, Bool.false_eq_true, bind_ok, ho]
      refine ⟨_, rfl, ?_⟩
      show choS o = _
      have hz : i32S 0#i32 = 0 := by decide
      rw [hov]; simp [ckS, hb, hc, hz]
  · by_cases hc : pre.combo = true
    · obtain ⟨o, ho, hov⟩ := beatmap.hit_object_parser.new_object_refines pre.start_time pre.pos nc pre.combo_offset
        (beatmap.types.ConvertKind.Slider v3 len rc)
      simp only [hb, hc, ite_true, ite_false, Bool.false_eq_true, bind_ok, ho]
      refine ⟨_, rfl, ?_⟩
      show choS o = _
      have hz : i32S 0#i32 = 0 := by decide
      rw [hov]; simp [ckS, hb, hc, hz]
    · obtain ⟨o, ho, hov⟩ := beatmap.hit_object_parser.new_object_refines pre.start_time pre.pos nc 0#i32
        (beatmap.types.ConvertKind.Slider v3 len rc)
      simp only [hb, hc, ite_false, Bool.false_eq_true, bind_ok, ho]
      refine ⟨_, rfl, ?_⟩
      show choS o = _
      have hz : i32S 0#i32 = 0 := by decide
      rw [hov]; simp [ckS, hb, hc, hz]

macro "hop_rstep3 " r:term:max h:term:max v:ident : tactic =>
  `(tactic| (rcases $r:term with $v:ident | e; (on_goal 2 => exact ⟨_, rfl, rel_err $h _ _, by intro p hp; cases hp⟩); rw [rel_ok $h, except_bind_ok]))

theorem hop_pre_parse_ok (st : beatmap.hit_object_parser.ParserState) (text : Slice U32)
    (hs : ValidStr text) (hn : text.val.length < 2^62) (hn2 : text.val.length < Usize.max) :
    ∃ sp, beatmap.dotnet.split text 44#u32 = ok sp ∧ ∃ r, beatmap.hit_object_parser.pre_parse st text = ok r ∧
      hRel hop_preS r (hop_preSpec (psS st) (String.ofList (strS text))) ∧ ∀ p, r = .Ok p → p.split = sp := by
  unfold beatmap.hit_object_parser.pre_parse hop_preSpec
  obtain ⟨sp, hsp, hspv, hspV, hspL⟩ := split_rel text hs hn2 44#u32 (by decide)
  have hc : chOf 44#u32 = ',' := by decide
  rw [hc] at hspv
  simp only [psS]
  refine ⟨sp, hsp, ?_⟩
  simp only [hsp, bind_ok, ← hspv]
  obtain ⟨r0, h0, h0r, h0m⟩ := beatmap.hit_object_parser.at_refines (alloc.vec.Vec.deref sp) 0#usize
  rw [deref_valA] at h0r h0m
  simp only [h0, bind_ok]
  have e0 : (0#usize : Usize).val = 0 := rfl
  have e1 : (1#usize : Usize).val = 1 := rfl
  have e2 : (2#usize : Usize).val = 2 := rfl
  have e3 : (3#usize : Usize).val = 3 := rfl
  have e4 : (4#usize : Usize).val = 4 := rfl
  have hVv : ∀ v ∈ sp.val, ValidStr (alloc.vec.Vec.deref v) := fun v hv => validStr_of v (hspV v hv)
  have hLv : ∀ v ∈ sp.val, (alloc.vec.Vec.deref v).val.length < 2^62 := by
    intro v hv; have := hspL v hv; simp; omega
  rw [e0] at h0r
  hop_rstep3 r0 h0r v
  have hvm := h0m v rfl
  obtain ⟨r1, h1, h1r⟩ := beatmap.hit_object_parser.parse_coord_refines st.format_version _ (hVv v hvm) (hLv v hvm)
  rw [strV_deref] at h1r
  simp only [h1, bind_ok]
  hop_rstep3 r1 h1r x
  obtain ⟨r2, h2, h2r, h2m⟩ := beatmap.hit_object_parser.at_refines (alloc.vec.Vec.deref sp) 1#usize
  rw [deref_valA, e1] at h2r; rw [deref_valA] at h2m
  simp only [h2, bind_ok]
  hop_rstep3 r2 h2r v2
  have hvm2 := h2m v2 rfl
  obtain ⟨r3, h3, h3r⟩ := beatmap.hit_object_parser.parse_coord_refines st.format_version _ (hVv v2 hvm2) (hLv v2 hvm2)
  rw [strV_deref] at h3r
  simp only [h3, bind_ok]
  hop_rstep3 r3 h3r y
  obtain ⟨r4, h4, h4r, h4m⟩ := beatmap.hit_object_parser.at_refines (alloc.vec.Vec.deref sp) 2#usize
  rw [deref_valA, e2] at h4r; rw [deref_valA] at h4m
  simp only [h4, bind_ok]
  hop_rstep3 r4 h4r v4
  have hvm4 := h4m v4 rfl
  simp only [net.parse.parse_double_default_refines _ (hVv v4 hvm4) (hLv v4 hvm4), bind_ok, strV_deref]
  obtain ⟨r6, h6, h6r⟩ := lift_net_exceptI beatmap.errors.W_STARTTIME id id (fun _ => rfl)
    (Parsing.parseDouble (strV v4)) "startTime"
  simp only [h6, bind_ok]
  hop_rstep3 r6 h6r t
  simp only [float.F64.add, bind_ok, id]
  obtain ⟨r7, h7, h7r, h7m⟩ := beatmap.hit_object_parser.at_refines (alloc.vec.Vec.deref sp) 3#usize
  rw [deref_valA, e3] at h7r; rw [deref_valA] at h7m
  simp only [h7, bind_ok]
  hop_rstep3 r7 h7r v6
  have hvm6 := h7m v6 rfl
  simp only [net.parse.parse_int_default_refines _ (hVv v6 hvm6), bind_ok, strV_deref]
  obtain ⟨r9, h9, h9r⟩ := lift_net_exceptI beatmap.errors.W_TYPE i32I i32S (fun _ => rfl)
    (Parsing.parseInt (strV v6)) "type"
  simp only [h9, bind_ok]
  hop_rstep3 r9 h9r v7
  obtain ⟨c, hc4, hcv⟩ := hop_i32S_shr4 (v7 &&& beatmap.hit_object_parser.COMBO_OFFSET)
  simp only [lift, bind_ok, hc4]
  obtain ⟨r10, h10, h10r, h10m⟩ := beatmap.hit_object_parser.at_refines (alloc.vec.Vec.deref sp) 4#usize
  rw [deref_valA, e4] at h10r; rw [deref_valA] at h10m
  simp only [h10, bind_ok]
  hop_rstep3 r10 h10r v8
  have hvm8 := h10m v8 rfl
  simp only [net.parse.parse_int_default_refines _ (hVv v8 hvm8), bind_ok, strV_deref]
  obtain ⟨r12, h12, h12r⟩ := lift_net_exceptI beatmap.errors.W_SOUNDTYPE i32I i32S (fun _ => rfl)
    (Parsing.parseInt (strV v8)) "soundType"
  simp only [h12, bind_ok]
  hop_rstep3 r12 h12r w
  refine ⟨_, rfl, ?_, by intro p hp; cases hp; rfl⟩
  have hCO : i32S beatmap.hit_object_parser.COMBO_OFFSET = ConvertHitObjectParser.COMBO_OFFSET := by
    simp [beatmap.hit_object_parser.COMBO_OFFSET, ConvertHitObjectParser.COMBO_OFFSET, i32S]
  have hNC : i32S beatmap.hit_object_parser.NEW_COMBO = ConvertHitObjectParser.NEW_COMBO := by
    simp [beatmap.hit_object_parser.NEW_COMBO, ConvertHitObjectParser.NEW_COMBO, i32S]
  have h0' : i32S 0#i32 = 0 := by decide
  have hinj : ∀ a b : I32, (a != b) = (i32S a != i32S b) := by
    intro a b
    have : a = b ↔ i32S a = i32S b := by
      constructor
      · rintro rfl; rfl
      · intro h; unfold i32S at h
        have := congrArg Int32.toBitVec h; simp at this
        rcases a with ⟨abv⟩; rcases b with ⟨bbv⟩; simp at this; subst this; rfl
    simp [bne, this]
  simp only [hRel, hop_preS, pure, Except.pure, bv2S, hcv, hop_i32S_and, hop_i32S_not, hCO, hNC, hinj, h0']

/-- The local `finish` of `ConvertHitObjectParser.parse`. -/
def hop_finS (st' : ParserState) (startTime : F64) (r : DecodeM ConvertHitObject) : ParserState × DecodeM ConvertHitObject :=
  match r with
  | .ok o => ({ st' with firstObject := false }, .ok { o with startTime })
  | .error e => (st', .error e)

open OsuModel.Beatmap.ConvertHitObjectParser in
/-- `ConvertHitObjectParser.parse` after its `pre` block (verbatim, with the slider/hold bodies named). -/
def hop_parseS (st : ParserState) (pre : DecodeM (Vec2 × F64 × Int32 × Bool × Int32 × _root_.Array String)) :
    ParserState × DecodeM ConvertHitObject := Id.run do
  match pre with
  | .error e => return (st, .error e)
  | .ok (pos, startTime, comboOffset, combo, type, split) =>
  let newComboOf (nc : Bool) := st.firstObject || st.lastObjectIsSpinner || nc
  let finish (st' : ParserState) (r : DecodeM ConvertHitObject) : ParserState × DecodeM ConvertHitObject :=
    hop_finS st' startTime r
  if type &&& CIRCLE != 0 then
    -- createHitCircle (sets lastObject), then readCustomSampleBanks(split[5])
    let obj : ConvertHitObject :=
      { startTime, position := pos, newCombo := newComboOf combo,
        comboOffset := if combo then comboOffset else 0, kind := .circle }
    let st' := { st with lastObjectIsSpinner := false }
    let r : DecodeM ConvertHitObject := do
      if split.size > 5 then readCustomSampleBanks split[5]!
      return obj
    return finish st' r
  else if type &&& SLIDER != 0 then
    let r : DecodeM ConvertHitObject := hop_sliderS st split pos startTime combo comboOffset (newComboOf combo)
    match r with
    | .ok o => return finish { st with lastObjectIsSpinner := false } (.ok o)
    | .error e => return (st, .error e)
  else if type &&& SPINNER != 0 then
    let endR : DecodeM F64 := do liftNet "spinner end" (Parsing.parseDouble (← at! split 5))
    match endR with
    | .error e => return (st, .error e)
    | .ok endT =>
      let duration := F64.max 0 (endT + st.offset - startTime)
      let obj : ConvertHitObject :=
        { startTime, position := ⟨256, 192⟩, newCombo := combo, comboOffset := 0, kind := .spinner duration }
      let st' := { st with lastObjectIsSpinner := true }
      let r : DecodeM ConvertHitObject := do
        if split.size > 6 then readCustomSampleBanks split[6]!
        return obj
      return finish st' r
  else if type &&& HOLD != 0 then
    let r : DecodeM F64 := hop_holdS split startTime
    match r with
    | .error e => return (st, .error e)
    | .ok endTime =>
      let obj : ConvertHitObject :=
        { startTime, position := pos, newCombo := false, comboOffset := 0, kind := .hold (endTime + st.offset - startTime) }
      return finish { st with lastObjectIsSpinner := false } (.ok obj)
  else
    return (st, .error s!"Unknown hit object type: {split[3]!}")


theorem hop_parse_eq (st : ParserState) (text : String) :
    ConvertHitObjectParser.parse st text = hop_parseS st (hop_preSpec st text) := rfl

theorem hop_finish_ok (st2 : beatmap.hit_object_parser.ParserState)
    (r : core.result.Result beatmap.types.ConvertHitObject beatmap.hit_object_parser.DecodeError)
    (r' : DecodeM ConvertHitObject) (h : hRel choS r r') (startTime : F64)
    (hs : ∀ o, r = .Ok o → o.start_time = startTime) :
    ∃ p, beatmap.hit_object_parser.finish st2 r = ok p ∧ psS p.1 = (hop_finS (psS st2) startTime r').1 ∧
      hRel choS p.2 (hop_finS (psS st2) startTime r').2 := by
  obtain ⟨p, hp, hp1, hp2⟩ := beatmap.hit_object_parser.finish_refines st2 r r' h startTime hs
  refine ⟨p, hp, ?_, ?_⟩ <;> cases r' <;> simp_all [hop_finS]

theorem hop_opt_banks (sp : alloc.vec.Vec (alloc.vec.Vec U32)) (hV : ∀ l ∈ sp.val, ValidL l.val)
    (hL : ∀ l ∈ sp.val, l.val.length < Usize.max) (ku : Usize) (k : Nat) (hk : ku.val = k)
    (obj : beatmap.types.ConvertHitObject) (objS : ConvertHitObject) (hobj : choS obj = objS) :
    ∃ r1, (if alloc.vec.Vec.len sp > ku then do
        let v ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (alloc.vec.Vec U32)) sp ku
        let r2 ← beatmap.hit_object_parser.read_custom_sample_banks (alloc.vec.Vec.deref v) false
        match r2 with
        | core.result.Result.Ok _ => ok (core.result.Result.Ok obj)
        | core.result.Result.Err e => ok (core.result.Result.Err e)
      else ok (core.result.Result.Ok obj)) = ok r1 ∧
      hRel choS r1 (if (vstrs sp.val).size > k then (do
          ConvertHitObjectParser.readCustomSampleBanks (vstrs sp.val)[k]!
          pure objS : DecodeM ConvertHitObject) else pure objS) ∧
      ∀ o, r1 = .Ok o → o = obj := by
  rw [vstrs_size]
  by_cases h : sp.val.length > k
  · have h' : alloc.vec.Vec.len sp > ku := by show ku.val < (alloc.vec.Vec.len sp).val; simp; omega
    have hk' : ku.val < sp.val.length := by omega
    have hm := List.getElem_mem hk'
    obtain ⟨q, hq, hqr⟩ := beatmap.hit_object_parser.read_custom_sample_banks_refines _ (validStr_of _ (hV _ hm))
      (by simp; exact hL _ hm) false
    rw [strV_deref] at hqr
    have hg : (vstrs sp.val)[k]! = strV (sp.val[ku.val]'hk') := by
      have := vstrs_get! sp.val k (by omega); rw [this]; congr 2; omega
    simp only [h', ite_true, h, vec_index_eq' sp ku hk', bind_ok, hq, hg]
    cases q with
    | Ok u =>
      refine ⟨_, rfl, ?_, by intro o ho; simp at ho; exact ho.symm⟩
      rw [rel_ok hqr]; exact hobj
    | Err e =>
      refine ⟨_, rfl, rel_err hqr _ _, by intro o ho; cases ho⟩
  · have h' : ¬ alloc.vec.Vec.len sp > ku := by show ¬ ku.val < (alloc.vec.Vec.len sp).val; simp; omega
    simp only [h', ite_false, h]
    exact ⟨_, rfl, hobj, by intro o ho; simp at ho; exact ho.symm⟩

theorem hop_comma_lit : chOf 44#u32 = ',' := by decide

theorem hop_bne_i32S (a b : I32) : (a != b) = (i32S a != i32S b) := by
  have : a = b ↔ i32S a = i32S b := by
    constructor
    · rintro rfl; rfl
    · intro h; unfold i32S at h
      have := congrArg Int32.toBitVec h; simp at this
      rcases a with ⟨abv⟩; rcases b with ⟨bbv⟩; simp at this; subst this; rfl
  simp [bne, this]

theorem hop_type_test (a C : I32) (c : Int32) (hc : i32S C = c) :
    ((i32S a &&& c) != 0) = ((a &&& C) != 0#i32) := by
  rw [hop_bne_i32S, hop_i32S_and, hc]; rfl

theorem hop_new_object_st (st : F64) (pos : net.osutk.Vector2) (nc : Bool) (co : I32) (k : beatmap.types.ConvertKind)
    (o : beatmap.types.ConvertHitObject) (h : beatmap.hit_object_parser.new_object st pos nc co k = ok o) :
    o.start_time = st := by
  unfold beatmap.hit_object_parser.new_object at h
  have h1 : float.F64.from_bits 4607182418800017408#u64 = ok (1 : F64) := by simp; decide
  simp only [h1, bind_ok, ok.injEq] at h; rw [← h]

theorem hop_sliderC_st (st : ParserState) (split : _root_.Array String) (pos : Vec2) (startTime : F64) (combo : Bool)
    (comboOffset : Int32) (nc : Bool) (v : ConvertHitObject)
    (h : hop_sliderC st split pos startTime combo comboOffset nc = .ok v) : v.startTime = startTime := by
  unfold hop_sliderC at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  repeat' split at h
  all_goals first | (simp only [Except.ok.injEq] at h; rw [← h]) | (cases h) | simp_all

theorem beatmap.hit_object_parser.parse_refines (st : beatmap.hit_object_parser.ParserState) (text : Slice U32)
    (hs : ValidStr text) (hn : text.val.length < 2^61) (h64 : System.Platform.numBits = 64)
    (hcp : ∀ fv pos cps, ConvertHitObjectParser.convertPathString fv (split (String.ofList (strS text)) ',')[5]! pos = .ok cps →
      cps.size < 2^32 ∧ ∀ len, (SliderPath.calculatePath { controlPoints := cps, expectedDistance := len, optimiseCatmull := false }).1.size < 2^62) :
    ∃ p, beatmap.hit_object_parser.parse st text = ok p ∧
      psS p.1 = (ConvertHitObjectParser.parse (psS st) (String.ofList (strS text))).1 ∧
      hRel choS p.2 (ConvertHitObjectParser.parse (psS st) (String.ofList (strS text))).2 := by
  rw [hop_parse_eq]
  have hmax : text.val.length < Usize.max := by rw [hop_umax64 h64]; omega
  obtain ⟨sp, hsp, r, hr, hrr, hrsp⟩ := hop_pre_parse_ok st text hs (by omega) hmax
  obtain ⟨sp', hsp', hspv, hspV, hspL⟩ := split_rel text hs hmax 44#u32 (by decide)
  rw [hsp] at hsp'; simp only [ok.injEq] at hsp'; subst hsp'
  rw [hop_comma_lit] at hspv
  unfold beatmap.hit_object_parser.parse
  simp only [hr, bind_ok]
  rcases r with p | e
  on_goal 2 =>
    cases hx : hop_preSpec (psS st) (String.ofList (strS text)) with
    | ok y => rw [hx] at hrr; simp [hRel] at hrr
    | error m => exact ⟨_, rfl, rfl, trivial⟩
  have hx := rel_ok hrr
  have hps := hrsp p rfl
  rw [hx]
  dsimp only [hop_parseS, Id.run, hop_preS]
  have hnc : (if st.first_object = true then ok (p, true) else if st.last_object_is_spinner = true then ok (p, true)
      else ok (p, p.combo) : Result (beatmap.hit_object_parser.PreParse × Bool)) =
      ok (p, st.first_object || st.last_object_is_spinner || p.combo) := by
    cases st.first_object <;> cases st.last_object_is_spinner <;> rfl
  simp only [hnc, bind_ok, lift, uncurry_apply_pair]
  have hCI : i32S beatmap.hit_object_parser.CIRCLE = ConvertHitObjectParser.CIRCLE := by
    simp [beatmap.hit_object_parser.CIRCLE, ConvertHitObjectParser.CIRCLE, i32S]
  have hSL : i32S beatmap.hit_object_parser.SLIDER = ConvertHitObjectParser.SLIDER := by
    simp [beatmap.hit_object_parser.SLIDER, ConvertHitObjectParser.SLIDER, i32S]
  have hSP : i32S beatmap.hit_object_parser.SPINNER = ConvertHitObjectParser.SPINNER := by
    simp [beatmap.hit_object_parser.SPINNER, ConvertHitObjectParser.SPINNER, i32S]
  have hHO : i32S beatmap.hit_object_parser.HOLD = ConvertHitObjectParser.HOLD := by
    simp [beatmap.hit_object_parser.HOLD, ConvertHitObjectParser.HOLD, i32S]
  simp only [hop_type_test _ _ _ hCI, hop_type_test _ _ _ hSL, hop_type_test _ _ _ hSP, hop_type_test _ _ _ hHO]
  have hspV' : ∀ l ∈ p.split.val, ValidL l.val := by rw [hps]; exact hspV
  have hspL' : ∀ l ∈ p.split.val, l.val.length < 2^61 := by rw [hps]; intro l hl; have := hspL l hl; omega
  have hspM : ∀ l ∈ p.split.val, l.val.length < Usize.max := by
    intro l hl; have := hspL' l hl; rw [hop_umax64 h64]; omega
  have hz : i32S 0#i32 = 0 := by decide
  by_cases hc1 : (p.otype &&& beatmap.hit_object_parser.CIRCLE != 0#i32) = true
  · simp only [hc1, ite_true]
    have hi1 : (if p.combo = true then ok p.combo_offset else ok 0#i32 : Result I32) =
        ok (if p.combo = true then p.combo_offset else 0#i32) := by split <;> rfl
    simp only [hi1, bind_ok]
    obtain ⟨o, ho, hov⟩ := beatmap.hit_object_parser.new_object_refines p.start_time p.pos
      (st.first_object || st.last_object_is_spinner || p.combo) (if p.combo = true then p.combo_offset else 0#i32)
      beatmap.types.ConvertKind.Circle
    have hos := hop_new_object_st _ _ _ _ _ o ho
    simp only [ho, bind_ok]
    have hobj : choS o = ({ startTime := p.start_time, position := bv2S p.pos, newCombo := (psS st).firstObject || (psS st).lastObjectIsSpinner || p.combo, comboOffset := if p.combo = true then i32S p.combo_offset else 0, kind := ConvertKind.circle } : ConvertHitObject) := by
      rw [hov]; cases p.combo <;> simp [ckS, hz, psS]
    have hfin := fun (r1 : core.result.Result beatmap.types.ConvertHitObject beatmap.hit_object_parser.DecodeError)
        (r' : DecodeM ConvertHitObject) (hr : hRel choS r1 r') (hro : ∀ o', r1 = .Ok o' → o' = o) =>
      hop_finish_ok { st with last_object_is_spinner := false } r1 r' hr p.start_time
        (by intro o' ho'; rw [hro o' ho', hos])
    rw [vstrs_size]
    by_cases h5 : p.split.val.length > 5
    · have h5' : alloc.vec.Vec.len p.split > 5#usize := by show (5#usize : Usize).val < (alloc.vec.Vec.len p.split).val; simpa using h5
      have h5i : (5#usize : Usize).val < p.split.val.length := by simpa using h5
      have hm := List.getElem_mem h5i
      obtain ⟨q, hq, hqr⟩ := beatmap.hit_object_parser.read_custom_sample_banks_refines _ (validStr_of _ (hspV' _ hm))
        (by simp; exact hspM _ hm) false
      rw [strV_deref] at hqr
      have hg : (vstrs p.split.val)[5]! = strV (p.split.val[(5#usize : Usize).val]'h5i) := vstrs_get! _ _ _
      simp only [h5', ite_true, h5, vec_index_eq' p.split 5#usize h5i, bind_ok, hq, hg]
      cases q with
      | Ok u =>
        simp only [bind_ok]
        obtain ⟨q', hq', hq1, hq2⟩ := hfin (.Ok o)
          (ConvertHitObjectParser.readCustomSampleBanks (strV (p.split.val[(5#usize : Usize).val]'h5i)) false >>= fun _ => pure ({ startTime := p.start_time, position := bv2S p.pos, newCombo := (psS st).firstObject || (psS st).lastObjectIsSpinner || p.combo, comboOffset := if p.combo = true then i32S p.combo_offset else 0, kind := ConvertKind.circle } : ConvertHitObject))
          (by rw [rel_ok hqr]; exact hobj) (by intro o' h; simp at h; exact h.symm)
        exact ⟨q', hq', hq1, hq2⟩
      | Err e =>
        simp only [bind_ok]
        obtain ⟨q', hq', hq1, hq2⟩ := hfin (.Err e)
          (ConvertHitObjectParser.readCustomSampleBanks (strV (p.split.val[(5#usize : Usize).val]'h5i)) false >>= fun _ => pure ({ startTime := p.start_time, position := bv2S p.pos, newCombo := (psS st).firstObject || (psS st).lastObjectIsSpinner || p.combo, comboOffset := if p.combo = true then i32S p.combo_offset else 0, kind := ConvertKind.circle } : ConvertHitObject))
          (rel_err hqr _ _) (by intro o' h; cases h)
        exact ⟨q', hq', hq1, hq2⟩
    · have h5' : ¬ alloc.vec.Vec.len p.split > 5#usize := by show ¬ (5#usize : Usize).val < (alloc.vec.Vec.len p.split).val; simpa using h5
      simp only [h5', ite_false, h5, bind_ok]
      obtain ⟨q', hq', hq1, hq2⟩ := hfin (.Ok o) (pure ({ startTime := p.start_time, position := bv2S p.pos, newCombo := (psS st).firstObject || (psS st).lastObjectIsSpinner || p.combo, comboOffset := if p.combo = true then i32S p.combo_offset else 0, kind := ConvertKind.circle } : ConvertHitObject)) hobj (by intro o' h; simp at h; exact h.symm)
      exact ⟨q', hq', hq1, hq2⟩
  · simp only [hc1, ite_false, Bool.false_eq_true]
    by_cases hc2 : (p.otype &&& beatmap.hit_object_parser.SLIDER != 0#i32) = true
    · simp only [hc2, ite_true]
      have hcp' : ∀ cps, ConvertHitObjectParser.convertPathString (i32S st.format_version) (vstrs p.split.val)[5]! (bv2S p.pos) = .ok cps →
          cps.size < 2^32 ∧ ∀ len, (SliderPath.calculatePath { controlPoints := cps, expectedDistance := len, optimiseCatmull := false }).1.size < 2^62 := by
        rw [hps, hspv]; exact hcp _ _
      obtain ⟨r1, hr1, hr1r⟩ := beatmap.hit_object_parser.parse_slider_refines st p
        (st.first_object || st.last_object_is_spinner || p.combo) hspV' hspL' h64 hcp'
      change hRel choS r1 (hop_sliderS (psS st) (vstrs p.split.val) (bv2S p.pos) p.start_time p.combo (i32S p.combo_offset)
        ((psS st).firstObject || (psS st).lastObjectIsSpinner || p.combo)) at hr1r
      simp only [hr1, bind_ok]
      cases r1 with
      | Ok o =>
        have hsv := rel_ok hr1r
        have hos : o.start_time = p.start_time := by
          have := hop_sliderC_st _ _ _ _ _ _ _ _ (by rw [← hop_slider_eq]; exact hsv)
          simpa [choS] using this
        rw [hsv]
        simp only []
        obtain ⟨q', hq', hq1, hq2⟩ := hop_finish_ok { st with last_object_is_spinner := false } (.Ok o) (.ok (choS o)) rfl
          p.start_time (by intro o' h; simp at h; rw [← h, hos])
        exact ⟨q', hq', hq1, hq2⟩
      | Err e =>
        cases hx : hop_sliderS (psS st) (vstrs p.split.val) (bv2S p.pos) p.start_time p.combo (i32S p.combo_offset)
            ((psS st).firstObject || (psS st).lastObjectIsSpinner || p.combo) with
        | ok y => rw [hx] at hr1r; simp [hRel] at hr1r
        | error m => exact ⟨_, rfl, rfl, trivial⟩
    · simp only [hc2, ite_false, Bool.false_eq_true]
      by_cases hc3 : (p.otype &&& beatmap.hit_object_parser.SPINNER != 0#i32) = true
      · simp only [hc3, ite_true]
        by_cases h5 : p.split.val.length > 5
        · have h5' : alloc.vec.Vec.len p.split > 5#usize := by show (5#usize : Usize).val < (alloc.vec.Vec.len p.split).val; simpa using h5
          have h5i : (5#usize : Usize).val < p.split.val.length := by simpa using h5
          have hm := List.getElem_mem h5i
          have hat : at! (vstrs p.split.val) 5 = .ok (strV (p.split.val[(5#usize : Usize).val]'h5i)) := by
            unfold at!; rw [dif_pos (by rw [vstrs_size]; omega)]; simp [vstrs]
          have hlen5 : (alloc.vec.Vec.deref (p.split.val[(5#usize : Usize).val]'h5i)).val.length < 2^62 := by
            rw [deref_valA]; exact lt_trans (hspL' _ hm) (by norm_num)
          simp only [h5', ite_true, vec_index_eq' p.split 5#usize h5i, bind_ok]
          rw [net.parse.parse_double_default_refines _ (validStr_of _ (hspV' _ hm)) hlen5, bind_ok, strV_deref]
          rw [hat, except_bind_ok]
          obtain ⟨r2, h2, h2r⟩ := lift_net_exceptI beatmap.errors.W_SPINNER_END id id (fun _ => rfl)
            (Parsing.parseDouble (strV (p.split.val[(5#usize : Usize).val]'h5i))) "spinner end"
          rw [h2, bind_ok]
          cases hx : liftNet "spinner end" (Parsing.parseDouble (strV (p.split.val[(5#usize : Usize).val]'h5i))) with
          | error m =>
            rw [hx] at h2r
            rcases r2 with t | e
            · simp [hRel] at h2r
            · exact ⟨_, rfl, rfl, trivial⟩
          | ok t =>
            rw [hx] at h2r
            rcases r2 with t' | e
            on_goal 2 => simp [hRel] at h2r
            simp only [hRel, id] at h2r; subst t'
            have hD0 : beatmap.hit_object_parser.D0 = ok (0 : F64) := by
              unfold beatmap.hit_object_parser.D0; simp; decide
            have hf3 : float.F32.from_bits 1132462080#u32 = ok (256 : F32) := by simp; decide
            have hf4 : float.F32.from_bits 1128267776#u32 = ok (192 : F32) := by simp; decide
            simp only [float.F64.add, float.F64.sub, bind_ok, hD0, hop_he_max, hf3, hf4]
            obtain ⟨o, ho, hov⟩ := beatmap.hit_object_parser.new_object_refines p.start_time ⟨256, 192⟩ p.combo 0#i32
              (beatmap.types.ConvertKind.Spinner (F64.max 0 (t + st.offset - p.start_time)))
            have hos := hop_new_object_st _ _ _ _ _ o ho
            simp only [ho, bind_ok]
            have hobj : choS o = ({ startTime := p.start_time, position := { x := 256, y := 192 }, newCombo := p.combo, comboOffset := 0, kind := ConvertKind.spinner (F64.max 0 (t + (psS st).offset - p.start_time)) } : ConvertHitObject) := by
              rw [hov]; simp [ckS, hz, bv2S, psS]
            have hfin := fun (r1 : core.result.Result beatmap.types.ConvertHitObject beatmap.hit_object_parser.DecodeError)
                (r' : DecodeM ConvertHitObject) (hr : hRel choS r1 r') (hro : ∀ o', r1 = .Ok o' → o' = o) =>
              hop_finish_ok { st with last_object_is_spinner := true } r1 r' hr p.start_time
                (by intro o' ho'; rw [hro o' ho', hos])
            rw [vstrs_size]
            by_cases h6 : p.split.val.length > 6
            · have h6' : alloc.vec.Vec.len p.split > 6#usize := by show (6#usize : Usize).val < (alloc.vec.Vec.len p.split).val; simpa using h6
              have h6i : (6#usize : Usize).val < p.split.val.length := by simpa using h6
              have hm6 := List.getElem_mem h6i
              obtain ⟨q, hq, hqr⟩ := beatmap.hit_object_parser.read_custom_sample_banks_refines _ (validStr_of _ (hspV' _ hm6))
                (by simp; exact hspM _ hm6) false
              rw [strV_deref] at hqr
              have hg : (vstrs p.split.val)[6]! = strV (p.split.val[(6#usize : Usize).val]'h6i) := vstrs_get! _ _ _
              simp only [h6', ite_true, h6, vec_index_eq' p.split 6#usize h6i, bind_ok, hq, hg]
              cases q with
              | Ok u =>
                simp only [bind_ok]
                obtain ⟨q', hq', hq1, hq2⟩ := hfin (.Ok o)
                  (ConvertHitObjectParser.readCustomSampleBanks (strV (p.split.val[(6#usize : Usize).val]'h6i)) false >>= fun _ => pure ({ startTime := p.start_time, position := { x := 256, y := 192 }, newCombo := p.combo, comboOffset := 0, kind := ConvertKind.spinner (F64.max 0 (t + (psS st).offset - p.start_time)) } : ConvertHitObject))
                  (by rw [rel_ok hqr]; exact hobj) (by intro o' h; simp at h; exact h.symm)
                exact ⟨q', hq', hq1, hq2⟩
              | Err e =>
                simp only [bind_ok]
                obtain ⟨q', hq', hq1, hq2⟩ := hfin (.Err e)
                  (ConvertHitObjectParser.readCustomSampleBanks (strV (p.split.val[(6#usize : Usize).val]'h6i)) false >>= fun _ => pure ({ startTime := p.start_time, position := { x := 256, y := 192 }, newCombo := p.combo, comboOffset := 0, kind := ConvertKind.spinner (F64.max 0 (t + (psS st).offset - p.start_time)) } : ConvertHitObject))
                  (rel_err hqr _ _) (by intro o' h; cases h)
                exact ⟨q', hq', hq1, hq2⟩
            · have h6' : ¬ alloc.vec.Vec.len p.split > 6#usize := by show ¬ (6#usize : Usize).val < (alloc.vec.Vec.len p.split).val; simpa using h6
              simp only [h6', ite_false, h6, bind_ok]
              obtain ⟨q', hq', hq1, hq2⟩ := hfin (.Ok o) (pure ({ startTime := p.start_time, position := { x := 256, y := 192 }, newCombo := p.combo, comboOffset := 0, kind := ConvertKind.spinner (F64.max 0 (t + (psS st).offset - p.start_time)) } : ConvertHitObject)) hobj (by intro o' h; simp at h; exact h.symm)
              exact ⟨q', hq', hq1, hq2⟩
        · have h5' : ¬ alloc.vec.Vec.len p.split > 5#usize := by show ¬ (5#usize : Usize).val < (alloc.vec.Vec.len p.split).val; simpa using h5
          have hat : ∃ m, at! (vstrs p.split.val) 5 = .error m := by
            unfold at!; rw [dif_neg (by rw [vstrs_size]; omega)]; exact ⟨_, rfl⟩
          obtain ⟨m, hm⟩ := hat
          simp only [h5', ite_false, bind_ok, hm, except_bind_error]
          exact ⟨_, rfl, rfl, trivial⟩
      · simp only [hc3, ite_false, Bool.false_eq_true]
        by_cases hc4 : (p.otype &&& beatmap.hit_object_parser.HOLD != 0#i32) = true
        · simp only [hc4, ite_true]
          obtain ⟨r1, hr1, hr1r⟩ := beatmap.hit_object_parser.parse_hold_end_refines p hspV'
            (by intro l hl; have := hspL' l hl; omega) hspM
          simp only [hr1, bind_ok]
          cases r1 with
          | Ok et =>
            have hsv := rel_ok hr1r
            rw [hsv]
            simp only [id, float.F64.add, float.F64.sub, bind_ok]
            obtain ⟨o, ho, hov⟩ := beatmap.hit_object_parser.new_object_refines p.start_time p.pos false 0#i32
              (beatmap.types.ConvertKind.Hold (et + st.offset - p.start_time))
            have hos := hop_new_object_st _ _ _ _ _ o ho
            simp only [ho, bind_ok]
            obtain ⟨q', hq', hq1, hq2⟩ := hop_finish_ok { st with last_object_is_spinner := false } (.Ok o)
              (.ok ({ startTime := p.start_time, position := bv2S p.pos, newCombo := false, comboOffset := 0, kind := ConvertKind.hold (et + (psS st).offset - p.start_time) } : ConvertHitObject))
              (by show choS o = _; rw [hov]; simp [ckS, hz, psS]) p.start_time (by intro o' h; simp at h; rw [← h, hos])
            exact ⟨q', hq', hq1, hq2⟩
          | Err e =>
            cases hx : hop_holdS (vstrs p.split.val) p.start_time with
            | ok y => rw [hx] at hr1r; simp [hRel] at hr1r
            | error m => exact ⟨_, rfl, rfl, trivial⟩
        · simp only [hc4, ite_false, Bool.false_eq_true]
          exact ⟨_, rfl, rfl, trivial⟩

end OsuProofs
