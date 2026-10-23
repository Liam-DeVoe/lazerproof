/-
`beatmap::hit_object_parser` (Rust) refines `ConvertHitObjectParser` (`HitObjectParser.lean`), part 1:
representation maps (`ptS`, `pcpS`, `choS`, `psS`), the error relation `hRel` (both values related,
or both errors: a failing line is dropped, the message is informational), `liftNet`, `at!`, `char0`,
`readCustomSampleBanks`, `parseCoord`, `readPoint`, `isLinear`, `convertPathType`.
-/
import OsuProofs.Beatmap.DecoderStr
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.deprecated false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

/-! ## representation maps -/
def ptS : beatmap.types.PathType → PathType
  | .Catmull => .catmull
  | .BSpline d => .bspline (d.map i32S)
  | .Linear => .linear
  | .PerfectCurve => .perfectCurve
def pcpS (p : beatmap.types.PathControlPoint) : PathControlPoint := ⟨bv2S p.position, p.ptype.map ptS⟩
def pcpsS (l : List beatmap.types.PathControlPoint) : _root_.Array PathControlPoint := (l.map pcpS).toArray
def ckS : beatmap.types.ConvertKind → ConvertKind
  | .Circle => .circle
  | .Slider cps d r => .slider (pcpsS cps.val) d (i32S r)
  | .Spinner d => .spinner d
  | .Hold d => .hold d
def choS (h : beatmap.types.ConvertHitObject) : ConvertHitObject :=
  ⟨h.start_time, bv2S h.position, h.new_combo, i32S h.combo_offset, ckS h.kind, h.generate_ticks, h.slider_velocity_multiplier⟩
def psS (p : beatmap.hit_object_parser.ParserState) : ParserState :=
  ⟨p.offset, i32S p.format_version, p.first_object, p.last_object_is_spinner⟩

/-- Rust `Result<T, DecodeError>` vs spec `DecodeM`: equal values, or both errors (the message is
informational: a failing line is dropped). -/
def hRel {α β} (f : α → β) : core.result.Result α beatmap.hit_object_parser.DecodeError → Except String β → Prop
  | .Ok a, .ok b => f a = b
  | .Err _, .error _ => True
  | _, _ => False

theorem bind_rel {α α' β β'} (r : core.result.Result α beatmap.hit_object_parser.DecodeError) (x : Except String α')
    (f : α → α') (h : hRel f r x)
    (kR : α → Result (core.result.Result β beatmap.hit_object_parser.DecodeError)) (kS : α' → Except String β')
    (g : β → β') (hk : ∀ a, ∃ r', kR a = ok r' ∧ hRel g r' (kS (f a))) :
    ∃ r', (match r with | .Ok a => kR a | .Err e => ok (.Err e)) = ok r' ∧ hRel g r' (x >>= kS) := by
  cases r with
  | Ok a =>
    cases x with
    | ok b => simp only [hRel] at h; subst h; obtain ⟨r', h1, h2⟩ := hk a; exact ⟨r', h1, h2⟩
    | error e => simp [hRel] at h
  | Err e =>
    cases x with
    | ok b => simp [hRel] at h
    | error e' => exact ⟨.Err e, rfl, trivial⟩

theorem beatmap.hit_object_parser.lift_net_refines {α β} (what : U32) (f : α → β) (x : Except OsuModel.Net.NetExn β)
    (r : core.result.Result α net.basic.NetExn) (h : ∀ e, x = .error e → ∃ e', r = .Err e')
    (h2 : ∀ b, x = .ok b → ∃ a, r = .Ok a ∧ f a = b) (s : String) :
    ∃ r', beatmap.hit_object_parser.lift_net what r = ok r' ∧ hRel f r' (liftNet s x) := by
  unfold beatmap.hit_object_parser.lift_net liftNet
  cases x with
  | ok b => obtain ⟨a, rfl, hf⟩ := h2 b rfl; exact ⟨_, rfl, hf⟩
  | error e => obtain ⟨e', rfl⟩ := h e rfl; exact ⟨_, rfl, trivial⟩

/-- `liftNet` of a result given as `exceptI`. -/
theorem lift_net_exceptI {α β} (what : U32) (g : β → α) (f : α → β) (hfg : ∀ b, f (g b) = b) (x : Except OsuModel.Net.NetExn β) (s : String) :
    ∃ r', beatmap.hit_object_parser.lift_net what (exceptI g x) = ok r' ∧ hRel f r' (liftNet s x) := by
  apply beatmap.hit_object_parser.lift_net_refines
  · intro e he; subst he; exact ⟨_, rfl⟩
  · intro b hb; subst hb; exact ⟨g b, rfl, hfg b⟩

def vstrs (v : List (alloc.vec.Vec U32)) : _root_.Array String := (v.map strV).toArray

theorem beatmap.hit_object_parser.at_refines (a : Slice (alloc.vec.Vec U32)) (i : Usize) :
    ∃ r, beatmap.hit_object_parser.at a i = ok r ∧ hRel strV r (at! (vstrs a.val) i.val) ∧
      ∀ v, r = .Ok v → v ∈ a.val := by
  unfold beatmap.hit_object_parser.at at!
  by_cases h : i.val < a.val.length
  · have h' : i < Slice.len a := by show i.val < (Slice.len a).val; simpa using h
    have h2 : i.val < (vstrs a.val).size := by simpa [vstrs] using h
    refine ⟨.Ok (a.val[i.val]'h), by simp [h', index_eq a i h], ?_, fun v hv => by cases hv; exact List.getElem_mem h⟩
    simp [h, hRel, vstrs]
  · have h' : ¬ i < Slice.len a := by show ¬ i.val < (Slice.len a).val; simpa using h
    have h2 : ¬ i.val < (vstrs a.val).size := by simpa [vstrs] using h
    exact ⟨.Err (.Msg beatmap.errors.M_INDEX_OUT_OF_RANGE), by simp [h'], by simp [h2, hRel], fun v hv => by cases hv⟩

theorem beatmap.hit_object_parser.char0_refines (s : Slice U32) :
    ∃ r, beatmap.hit_object_parser.char0 s = ok r ∧ hRel chOf r (char0 (String.ofList (strS s))) ∧
      ∀ c, r = .Ok c → c ∈ s.val := by
  unfold beatmap.hit_object_parser.char0 char0
  rw [String.toList_ofList]
  cases hl : s.val with
  | nil =>
    have : ¬ Slice.len s > 0#usize := by show ¬ (0#usize : Usize).val < (Slice.len s).val; simp [hl]
    exact ⟨.Err (.Msg beatmap.errors.M_INDEX_0_OUT_OF_RANGE_EMPTY_STRING), by simp [this], by simp [strS, hl, hRel], fun c hc => by cases hc⟩
  | cons c t =>
    have : Slice.len s > 0#usize := by show (0#usize : Usize).val < (Slice.len s).val; simp [hl]
    have h0 : (0#usize : Usize).val < s.val.length := by simp [hl]
    refine ⟨.Ok c, by simp [this, index_eq s 0#usize h0, hl], by simp [strS, hl, hRel], fun c' hc => by cases hc; simp [hl]⟩

theorem vstrs_get! (l : List (alloc.vec.Vec U32)) (i : Nat) (h : i < l.length) : (vstrs l)[i]! = strV (l[i]'h) := by
  rw [getElem!_pos _ i (by simpa [vstrs] using h)]; simp [vstrs]
theorem vstrs_size (l : List (alloc.vec.Vec U32)) : (vstrs l).size = l.length := by simp [vstrs]
theorem strV_deref (v : alloc.vec.Vec U32) : String.ofList (strS (alloc.vec.Vec.deref v)) = strV v := by
  simp [strS, strV, ds_deref_val]

/-- `liftNet what (Parsing.parseInt s)` on a Rust string. -/
theorem pint_rel (v : alloc.vec.Vec U32) (hv : ValidL v.val) (w : U32) (what : String) :
    ∃ r, (do let r1 ← net.parse.parse_int_default (alloc.vec.Vec.deref v); beatmap.hit_object_parser.lift_net w r1) = ok r ∧
      hRel i32S r (liftNet what (OsuModel.Net.Parsing.parseInt (strV v))) := by
  rw [net.parse.parse_int_default_refines _ (validStr_of v hv), bind_ok, strV_deref]
  exact lift_net_exceptI w i32I i32S (fun _ => rfl) _ what

theorem intercalate_len_le {α} (c : α) : ∀ (L : List (List α)) (m : List α), m ∈ L → m.length ≤ ([c].intercalate L).length
  | [], m, h => by simp at h
  | [a], m, h => by simp at h; subst h; simp
  | a :: b :: L, m, h => by
    rw [List.intercalate_cons_cons]
    rcases List.mem_cons.mp h with h | h
    · subst h; simp
    · have := intercalate_len_le c (b :: L) m h; simp at this ⊢; omega

/-- split a Rust string on a literal separator, with the spec's `Beatmap.split`. -/
theorem split_rel (s : Slice U32) (hs : ValidStr s) (hn : s.val.length < Usize.max) (c : U32) (hc : c.val.isValidChar) :
    ∃ sp, beatmap.dotnet.split s c = ok sp ∧ vstrs sp.val = split (String.ofList (strS s)) (chOf c) ∧
      (∀ l ∈ sp.val, ValidL l.val) ∧ (∀ l ∈ sp.val, l.val.length ≤ s.val.length) := by
  obtain ⟨sp, h1, h2, h3⟩ := beatmap.dotnet.split_refines s hs c hc hn
  refine ⟨sp, h1, h2, h3, ?_⟩
  intro l hl
  have hmem : strV l ∈ (split (String.ofList (strS s)) (chOf c)).toList := by
    rw [← h2]; simp [List.mem_map]; exact ⟨l, hl, rfl⟩
  simp only [split, splitOn_char, List.toList_toArray, List.mem_map] at hmem
  obtain ⟨m, hm, hme⟩ := hmem
  have hlen : (strV l).length = l.val.length := by simp [strV]
  have := intercalate_len_le (chOf c) (List.splitOn (chOf c) (strS s)) m hm
  rw [List.intercalate_splitOn] at this
  have h4 : m.length = l.val.length := by rw [← hlen, ← hme]; simp
  simp [strS] at this; omega

@[simp] theorem deref_valA {α} (v : alloc.vec.Vec α) : (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref]

theorem rel_err {α β γ δ} {f : α → β} {e : beatmap.hit_object_parser.DecodeError} {x : Except String β}
    (h : hRel f (.Err e) x) (k : β → Except String γ) (g : δ → γ) : hRel g (.Err e) (x >>= k) := by
  cases x with
  | ok b => simp [hRel] at h
  | error m => trivial
theorem rel_ok {α β} {f : α → β} {a : α} {x : Except String β} (h : hRel f (.Ok a) x) : x = .ok (f a) := by
  cases x with
  | ok b => simp only [hRel] at h; rw [h]
  | error m => simp [hRel] at h

theorem colon_lit : chOf 58#u32 = ':' := by decide

theorem beatmap.hit_object_parser.read_custom_sample_banks_refines (s : Slice U32) (hs : ValidStr s)
    (hn : s.val.length < Usize.max) (bo : Bool) :
    ∃ r, beatmap.hit_object_parser.read_custom_sample_banks s bo = ok r ∧
      hRel id r (ConvertHitObjectParser.readCustomSampleBanks (String.ofList (strS s)) bo) := by
  unfold beatmap.hit_object_parser.read_custom_sample_banks ConvertHitObjectParser.readCustomSampleBanks
  by_cases h0 : s.val = []
  · have : Slice.len s = 0#usize := by apply UScalar.eq_of_val_eq; simp [h0]
    exact ⟨.Ok (), by simp [this], by simp [strS, h0, hRel]⟩
  have hne : ¬ Slice.len s = 0#usize := by intro h; apply h0; have := congrArg UScalar.val h; simpa using this
  have hse : (String.ofList (strS s)).isEmpty = false := by simp [strS, h0]
  obtain ⟨sp, hsp, hspv, hspV, hspL⟩ := split_rel s hs hn 58#u32 (by decide)
  rw [colon_lit] at hspv
  simp only [hne, if_false, hse, Bool.false_eq_true, hsp, bind_ok]
  rw [← hspv]
  have e0 : (0#usize : Usize).val = 0 := rfl
  have e1 : (1#usize : Usize).val = 1 := rfl
  have hV : ∀ v ∈ sp.val, ValidL v.val := hspV
  obtain ⟨r0, hr0, hr0v, hr0m⟩ := beatmap.hit_object_parser.at_refines (alloc.vec.Vec.deref sp) 0#usize
  rw [deref_valA, e0] at hr0v; rw [deref_valA] at hr0m
  simp only [hr0, bind_ok]
  rcases r0 with v0 | e0
  case Err => exact ⟨.Err e0, rfl, rel_err hr0v _ _⟩
  rw [rel_ok hr0v]; simp only [except_bind_ok]
  have hv0 := hV v0 (hr0m v0 rfl)
  rw [net.parse.parse_int_default_refines _ (validStr_of v0 hv0), bind_ok, strV_deref]
  obtain ⟨r1, hr1, hr1v⟩ := lift_net_exceptI beatmap.errors.W_BANK i32I i32S (fun _ => rfl)
    (OsuModel.Net.Parsing.parseInt (strV v0)) "bank"
  simp only [hr1, bind_ok]
  rcases r1 with a1 | e1
  case Err => exact ⟨.Err e1, rfl, rel_err hr1v _ _⟩
  rw [rel_ok hr1v]; simp only [except_bind_ok]
  obtain ⟨r2, hr2, hr2v, hr2m⟩ := beatmap.hit_object_parser.at_refines (alloc.vec.Vec.deref sp) 1#usize
  rw [deref_valA, e1] at hr2v; rw [deref_valA] at hr2m
  simp only [hr2, bind_ok]
  rcases r2 with v1 | e2
  case Err => exact ⟨.Err e2, rfl, rel_err hr2v _ _⟩
  rw [rel_ok hr2v]; simp only [except_bind_ok]
  have hv1 := hV v1 (hr2m v1 rfl)
  rw [net.parse.parse_int_default_refines _ (validStr_of v1 hv1), bind_ok, strV_deref]
  obtain ⟨r3, hr3, hr3v⟩ := lift_net_exceptI beatmap.errors.W_ADDBANK i32I i32S (fun _ => rfl)
    (OsuModel.Net.Parsing.parseInt (strV v1)) "addBank"
  simp only [hr3, bind_ok]
  rcases r3 with a3 | e3
  case Err => exact ⟨.Err e3, rfl, rel_err hr3v _ _⟩
  rw [rel_ok hr3v]; simp only [except_bind_ok]
  cases bo
  case true => exact ⟨.Ok (), rfl, rfl⟩
  simp only [Bool.false_eq_true, if_false, vstrs_size]
  -- the optional fields
  have P3 : ∃ r, (if alloc.vec.Vec.len sp > 3#usize then do
        let v3 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (alloc.vec.Vec U32)) sp 3#usize
        let r8 ← net.parse.parse_int_default (alloc.vec.Vec.deref v3)
        let r9 ← beatmap.hit_object_parser.lift_net beatmap.errors.W_VOLUME r8
        match r9 with
        | core.result.Result.Ok _ => ok (core.result.Result.Ok ())
        | core.result.Result.Err e => ok (core.result.Result.Err e)
      else ok (core.result.Result.Ok ())) = ok r ∧
      hRel id r (if sp.val.length > 3 then do
          let _ ← liftNet "volume" (OsuModel.Net.Parsing.parseInt (vstrs sp.val)[3]!)
          pure ()
        else pure ()) := by
    by_cases h3 : sp.val.length > 3
    · have h3' : alloc.vec.Vec.len sp > 3#usize := by show (3#usize : Usize).val < (alloc.vec.Vec.len sp).val; simpa using h3
      have hv3 := hV _ (List.getElem_mem h3)
      have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (alloc.vec.Vec U32)) sp 3#usize =
          ok (sp.val[3]'h3) := vec_index_eq' sp 3#usize (by simpa using h3)
      simp only [h3', h3, if_true, hidx, bind_ok, vstrs_get! _ 3 h3]
      rw [net.parse.parse_int_default_refines _ (validStr_of _ hv3), bind_ok, strV_deref]
      obtain ⟨r9, hr9, hr9v⟩ := lift_net_exceptI beatmap.errors.W_VOLUME i32I i32S (fun _ => rfl)
        (OsuModel.Net.Parsing.parseInt (strV (sp.val[3]'h3))) "volume"
      simp only [hr9, bind_ok]
      rcases r9 with a9 | e9
      · rw [rel_ok hr9v]; exact ⟨.Ok (), rfl, rfl⟩
      · exact ⟨.Err e9, rfl, rel_err hr9v _ _⟩
    · have h3' : ¬ alloc.vec.Vec.len sp > 3#usize := by show ¬ (3#usize : Usize).val < (alloc.vec.Vec.len sp).val; simpa using h3
      simp only [h3', h3, if_false]; exact ⟨.Ok (), rfl, rfl⟩
  obtain ⟨q3, hq3, hq3v⟩ := P3
  by_cases h2 : sp.val.length > 2
  · have h2' : alloc.vec.Vec.len sp > 2#usize := by show (2#usize : Usize).val < (alloc.vec.Vec.len sp).val; simpa using h2
    have hv2 := hV _ (List.getElem_mem h2)
    have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (alloc.vec.Vec U32)) sp 2#usize =
        ok (sp.val[2]'h2) := vec_index_eq' sp 2#usize (by simpa using h2)
    simp only [h2', h2, if_true, hidx, bind_ok, vstrs_get! _ 2 h2]
    rw [net.parse.parse_int_default_refines _ (validStr_of _ hv2), bind_ok, strV_deref]
    obtain ⟨r7, hr7, hr7v⟩ := lift_net_exceptI beatmap.errors.W_CUSTOMSAMPLEBANK i32I i32S (fun _ => rfl)
      (OsuModel.Net.Parsing.parseInt (strV (sp.val[2]'h2))) "customSampleBank"
    simp only [hr7, bind_ok]
    rcases r7 with a7 | e7
    · rw [rel_ok hr7v]; simp only [except_bind_ok]; exact ⟨q3, hq3, hq3v⟩
    · exact ⟨.Err e7, rfl, rel_err hr7v _ _⟩
  · have h2' : ¬ alloc.vec.Vec.len sp > 2#usize := by show ¬ (2#usize : Usize).val < (alloc.vec.Vec.len sp).val; simpa using h2
    simp only [h2', h2, if_false]; exact ⟨q3, hq3, hq3v⟩

theorem i32S_ge_iff (x : I32) (k : Int) (hk1 : -2^31 ≤ k) (hk2 : k < 2^31) :
    (i32S x ≥ Int32.ofInt k) ↔ x.val ≥ k := by
  rw [ge_iff_le, Int32.le_iff_toInt_le, i32S_toInt, Int32.toInt_ofInt_of_le (by omega) (by omega)]
theorem i32S_lt_iff (x : I32) (k : Int) (hk1 : -2^31 ≤ k) (hk2 : k < 2^31) :
    (i32S x < Int32.ofInt k) ↔ x.val < k := by
  rw [Int32.lt_iff_toInt_lt, i32S_toInt, Int32.toInt_ofInt_of_le (by omega) (by omega)]

theorem beatmap.hit_object_parser.parse_coord_refines (fv : I32) (s : Slice U32) (hs : ValidStr s)
    (hn : s.val.length < 2^62) :
    ∃ r, beatmap.hit_object_parser.parse_coord fv s = ok r ∧
      hRel id r (ConvertHitObjectParser.parseCoord (i32S fv) (String.ofList (strS s))) := by
  unfold beatmap.hit_object_parser.parse_coord ConvertHitObjectParser.parseCoord
  have hlim : (OsuModel.Net.Parsing.MAX_COORDINATE_VALUE.toInt) = 131072 := by decide
  simp only [lift, bind_ok, float.F32.from_i64, net.parse.MAX_COORDINATE_VALUE, hlim]
  have hc : (IScalar.cast .I64 131072#i32).val = 131072 := by simp
  rw [hc, net.parse.parsing_parse_float_refines s hs hn, bind_ok]
  obtain ⟨r1, hr1, hr1v⟩ := lift_net_exceptI beatmap.errors.W_COORDINATE id id (fun _ => rfl)
    (OsuModel.Net.Parsing.parseFloat (String.ofList (strS s)) (OsuModel.Net.F32.ofInt 131072) false) "coordinate"
  simp only [hr1, bind_ok]
  rcases r1 with v | e
  · rw [rel_ok hr1v]; simp only [except_bind_ok]
    have hF : FIRST_LAZER_VERSION = Int32.ofInt 128 := by decide
    by_cases hv : fv.val ≥ 128
    · have : fv ≥ beatmap.hit_object_parser.FIRST_LAZER_VERSION := by
        unfold beatmap.hit_object_parser.FIRST_LAZER_VERSION; show (128#i32 : I32).val ≤ fv.val; simpa using hv
      simp only [this, if_true, hF, (i32S_ge_iff fv 128 (by decide) (by decide)).mpr hv]
      exact ⟨_, rfl, rfl⟩
    · have : ¬ fv ≥ beatmap.hit_object_parser.FIRST_LAZER_VERSION := by
        unfold beatmap.hit_object_parser.FIRST_LAZER_VERSION; show ¬ (128#i32 : I32).val ≤ fv.val; simpa using hv
      have h2 : ¬ (i32S fv ≥ Int32.ofInt 128) := fun h => hv ((i32S_ge_iff fv 128 (by decide) (by decide)).mp h)
      simp only [this, if_false, hF, h2, float.F32.to_i32_sat, float.F32.from_i64, bind_ok, lift]
      refine ⟨_, rfl, ?_⟩
      simp [hRel, OsuModel.Net.F32.ofInt32]
  · exact ⟨.Err e, rfl, rel_err hr1v _ _⟩

theorem beatmap.hit_object_parser.is_linear_refines (p0 p1 p2 : net.osutk.Vector2) :
    beatmap.hit_object_parser.is_linear p0 p1 p2 = ok (ConvertHitObjectParser.isLinear (bv2S p0) (bv2S p1) (bv2S p2)) := by
  unfold beatmap.hit_object_parser.is_linear ConvertHitObjectParser.isLinear
  have h0 : Float32.ofBits 0 = (0 : OsuModel.Net.F32) := by decide
  simp [h0, beatmap.vector2.almost_equals_f32_refines, bv2S]

theorem beatmap.hit_object_parser.read_point_refines (fv : I32) (value : Slice U32) (hs : ValidStr value)
    (hn : value.val.length < 2^62) (hn2 : value.val.length < Usize.max) (sp : net.osutk.Vector2) :
    ∃ r, beatmap.hit_object_parser.read_point fv value sp = ok r ∧
      hRel bv2S r (ConvertHitObjectParser.readPoint (i32S fv) (String.ofList (strS value)) (bv2S sp)) := by
  unfold beatmap.hit_object_parser.read_point ConvertHitObjectParser.readPoint
  obtain ⟨vs, hvs, hvsv, hvsV, hvsL⟩ := split_rel value hs hn2 58#u32 (by decide)
  rw [colon_lit] at hvsv
  simp only [hvs, bind_ok]
  rw [← hvsv]
  have e0 : (0#usize : Usize).val = 0 := rfl
  have e1 : (1#usize : Usize).val = 1 := rfl
  obtain ⟨r0, hr0, hr0v, hr0m⟩ := beatmap.hit_object_parser.at_refines (alloc.vec.Vec.deref vs) 0#usize
  rw [deref_valA, e0] at hr0v; rw [deref_valA] at hr0m
  simp only [hr0, bind_ok]
  rcases r0 with v0 | e
  case Err => exact ⟨.Err e, rfl, rel_err hr0v _ _⟩
  rw [rel_ok hr0v]; simp only [except_bind_ok]
  have hm0 := hr0m v0 rfl
  obtain ⟨c0, hc0, hc0v⟩ := beatmap.hit_object_parser.parse_coord_refines fv (alloc.vec.Vec.deref v0)
    (validStr_of v0 (hvsV v0 hm0)) (by simp; have := hvsL v0 hm0; omega)
  rw [strV_deref] at hc0v
  simp only [hc0, bind_ok]
  rcases c0 with x | e
  case Err => exact ⟨.Err e, rfl, rel_err hc0v _ _⟩
  rw [rel_ok hc0v]; simp only [except_bind_ok]
  obtain ⟨r1, hr1, hr1v, hr1m⟩ := beatmap.hit_object_parser.at_refines (alloc.vec.Vec.deref vs) 1#usize
  rw [deref_valA, e1] at hr1v; rw [deref_valA] at hr1m
  simp only [hr1, bind_ok]
  rcases r1 with v1 | e
  case Err => exact ⟨.Err e, rfl, rel_err hr1v _ _⟩
  rw [rel_ok hr1v]; simp only [except_bind_ok]
  have hm1 := hr1m v1 rfl
  obtain ⟨c1, hc1, hc1v⟩ := beatmap.hit_object_parser.parse_coord_refines fv (alloc.vec.Vec.deref v1)
    (validStr_of v1 (hvsV v1 hm1)) (by simp; have := hvsL v1 hm1; omega)
  rw [strV_deref] at hc1v
  simp only [hc1, bind_ok]
  rcases c1 with y | e
  case Err => exact ⟨.Err e, rfl, rel_err hc1v _ _⟩
  rw [rel_ok hc1v]; simp only [except_bind_ok]
  rw [beatmap.vector2.sub_refines]
  refine ⟨.Ok (bv2I ((bv2S ⟨x, y⟩).sub (bv2S sp))), by simp only [bind_ok], ?_⟩
  show bv2S (bv2I _) = _
  rw [bv2S_I]; rfl

theorem chOf_eq_of_valid (u : U32) (hu : u.val.isValidChar) (c : Char) : chOf u = c ↔ u.val = c.toNat := by
  constructor
  · intro h; rw [← h, chOf_toNat u hu]
  · intro h; unfold chOf; rw [h]; simp

theorem beatmap.hit_object_parser.convert_path_type_refines (input : Slice U32) (hs : ValidStr input) :
    ∃ r, beatmap.hit_object_parser.convert_path_type input = ok r ∧
      hRel ptS r (ConvertHitObjectParser.convertPathType (String.ofList (strS input))) := by
  unfold beatmap.hit_object_parser.convert_path_type ConvertHitObjectParser.convertPathType
  obtain ⟨r0, hr0, hr0v, hr0m⟩ := beatmap.hit_object_parser.char0_refines input
  simp only [hr0, bind_ok]
  rcases r0 with v | e
  case Err => exact ⟨.Err e, rfl, rel_err hr0v _ _⟩
  rw [rel_ok hr0v]; simp only [except_bind_ok]
  have hv := hs v (hr0m v rfl)
  by_cases hB : v = 66#u32
  · subst hB
    rw [show chOf 66#u32 = 'B' by decide]
    by_cases hl : input.val.length > 1
    · have hl' : Slice.len input > 1#usize := by show (1#usize : Usize).val < (Slice.len input).val; simpa using hl
      have hl2 : (String.ofList (strS input)).length > 1 := by simpa [strS] using hl
      obtain ⟨w, hw, hwv⟩ := beatmap.dotnet.sub_str_refines input 1#usize (Slice.len input) (by simp; omega) (by simp)
      have hwV : ValidL w.val := fun u hu => hs u (by
        rw [hwv] at hu; exact List.mem_of_mem_drop (List.mem_of_mem_take hu))
      have hws : strS (alloc.vec.Vec.deref w) = (String.ofList (strS input)).toList.drop 1 := by
        simp [strS, ds_deref_val, hwv, List.map_drop, List.map_take]
      simp only [hl', if_true, hl2, hw, bind_ok]
      rw [net.parse.int_parse_refines _ (validStr_of w hwV), hws]
      simp only [OsuModel.Net.intParse, String.toList_ofList]
      cases hp : OsuModel.Net.intParseChars ((strS input).drop 1) with
      | ok d =>
        simp only [exceptI]
        have hdv : (i32I d).val = d.toInt := by rw [← i32S_toInt, i32S_i32I]
        by_cases hd : (0 : Int32) < d
        · have hd' : (0 : Int) < (i32I d).val := by rw [hdv]; simpa [Int32.lt_iff_toInt_lt] using hd
          simp only [hd, if_true]
          exact ⟨.Ok (.BSpline (some (i32I d))), by simp [hd'], by simp [hRel, ptS]⟩
        · have hd' : ¬ (0 : Int) < (i32I d).val := by rw [hdv]; simpa [Int32.lt_iff_toInt_lt] using hd
          simp only [hd, if_false]
          exact ⟨.Ok (.BSpline none), by simp [hd'], by simp [hRel, ptS]⟩
      | error e => exact ⟨.Ok (.BSpline none), by simp [exceptI], rfl⟩
    · have hl' : ¬ Slice.len input > 1#usize := by show ¬ (1#usize : Usize).val < (Slice.len input).val; simpa using hl
      have hl2 : ¬ (String.ofList (strS input)).length > 1 := by simpa [strS] using hl
      simp only [hl', if_false, hl2]; exact ⟨_, rfl, rfl⟩
  · have hB' : chOf v ≠ 'B' := fun h => hB (UScalar.eq_of_val_eq (by rw [(chOf_eq_of_valid v hv 'B').mp h]; rfl))
    simp only [hB, if_false]
    by_cases hL : v = 76#u32
    · subst hL; rw [show chOf 76#u32 = 'L' by decide]; exact ⟨_, rfl, rfl⟩
    · have hL' : chOf v ≠ 'L' := fun h => hL (UScalar.eq_of_val_eq (by rw [(chOf_eq_of_valid v hv 'L').mp h]; rfl))
      simp only [hL, if_false]
      by_cases hP : v = 80#u32
      · subst hP; rw [show chOf 80#u32 = 'P' by decide]; exact ⟨_, rfl, rfl⟩
      · have hP' : chOf v ≠ 'P' := fun h => hP (UScalar.eq_of_val_eq (by rw [(chOf_eq_of_valid v hv 'P').mp h]; rfl))
        simp only [hP, if_false]
        exact ⟨_, rfl, rfl⟩

end OsuProofs
