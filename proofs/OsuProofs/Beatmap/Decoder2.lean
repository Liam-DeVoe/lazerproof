/-
`beatmap::decoder` part 2: `strip_comments` (the spec's `String.splitOn "//"` is characterised by the list
splitter `dec_ss2`, through an invariant over the legacy `String.splitOnAux` matcher states, and the Rust scan
loop finds the first `//`) and `handle_timing_point` (the spec body with its `do` join points is first shown
equal to the straight-line `dec_htp`-style chain `dec_htp_eq`, by case analysis; then the Rust steps
`tp_*` are matched one by one). Helper names are prefixed `dec_`.
-/
import OsuProofs.Beatmap.Decoder
import OsuProofs.Beatmap.DotNetStr
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

def dec_TS (sp : _root_.Array String) : DecodeM Int32 :=
  if sp.size ≥ 3 then
    (do let c ← char0 sp[2]!
        if c != '0' then
          (do let n ← liftNet "timeSignature" (Parsing.parseInt sp[2]!)
              if n ≤ 0 then throw "TimeSignature numerator must be positive" else pure n)
        else pure 4) else pure 4
def dec_CI (sp : _root_.Array String) (k : Nat) (what : String) : DecodeM Unit :=
  if sp.size ≥ k + 1 then (do let _ ← liftNet what (Parsing.parseInt sp[k]!); pure ()) else pure ()
def dec_TC (sp : _root_.Array String) : DecodeM Bool :=
  if sp.size ≥ 7 then (do let c ← char0 sp[6]!; pure (c == '1')) else pure true
def dec_KI (sp : _root_.Array String) : DecodeM Bool :=
  if sp.size ≥ 8 then (do let flags ← liftNet "effectFlags" (Parsing.parseInt sp[7]!); pure (flags &&& 1 != 0)) else pure false
def dec_TM (time bl : F64) (ts : Int32) (tc : Bool) : DecodeM (Option TimingPoint) :=
  if tc = true then
    (if bl.isNaN = true then throw "Beat length cannot be NaN in a timing control point"
      else pure (some ({ time, beatLength := clampBeatLength bl, timeSignature := ts } : TimingPoint)))
  else pure none

def dec_htp (s : DecoderState) (line : String) : DecodeM DecoderState := do
  let sp := split line ','
  let t0 ← at! sp 0
  let tv ← liftNet "time" (Parsing.parseDouble (trim t0))
  let time := LegacyBeatmapDecoder.offsetTime s tv
  let b1 ← at! sp 1
  let beatLength ← liftNet "beatLength" (Parsing.parseDouble (trim b1) Parsing.MAX_PARSE_VALUE true)
  let sm : F64 := if beatLength < 0 then 100.0 / -beatLength else 1
  let ts ← dec_TS sp
  dec_CI sp 3 "sampleSet"
  dec_CI sp 4 "customSampleBank"
  dec_CI sp 5 "sampleVolume"
  let tc ← dec_TC sp
  let kiai ← dec_KI sp
  let timing ← dec_TM time beatLength ts tc
  pure (LegacyBeatmapDecoder.addLinePoints s time timing
    { time, sliderVelocity := clampSV sm, generateTicks := !beatLength.isNaN }
    { time, kiai, scrollSpeed := if (s.rulesetId == 1 || s.rulesetId == 3) = true then clampScrollSpeed sm else 1 } tc)

theorem dec_TS_join {β : Type} (sp : _root_.Array String) (K : Unit → Int32 → DecodeM β) :
    (if sp.size ≥ 3 then do
      let __do_lift ← char0 sp[2]!
      if (__do_lift != '0') = true then do
          let n ← liftNet "timeSignature" (Parsing.parseInt sp[2]!)
          if n ≤ 0 then do
              let __r ← throw "TimeSignature numerator must be positive"
              (fun (_ : Unit) => K () n) __r
            else K () n
        else K () 4
    else K () 4) = dec_TS sp >>= K () := by
  unfold dec_TS
  split
  · cases char0 sp[2]! with
    | error e => rfl
    | ok c =>
      simp only [except_bind_ok]
      split
      · cases liftNet "timeSignature" (Parsing.parseInt sp[2]!) with
        | error e => rfl
        | ok n =>
          simp only [except_bind_ok]
          split <;> rfl
      · rfl
  · rfl

/-- `handleTimingPoint` after `let split := ...` (verbatim copy of the spec source). -/
def dec_htpBody (s : DecoderState) (split : _root_.Array String) : DecodeM DecoderState := do
  let time := LegacyBeatmapDecoder.offsetTime s (← liftNet "time" (Parsing.parseDouble (trim (← at! split 0))))
  let beatLength ← liftNet "beatLength" (Parsing.parseDouble (trim (← at! split 1)) Parsing.MAX_PARSE_VALUE true)
  let speedMultiplier : F64 := if beatLength < 0 then 100.0 / -beatLength else 1
  let mut timeSignature : Int32 := 4
  if split.size ≥ 3 then
    if (← char0 split[2]!) != '0' then
      let n ← liftNet "timeSignature" (Parsing.parseInt split[2]!)
      if n ≤ 0 then throw "TimeSignature numerator must be positive"
      timeSignature := n
  if split.size ≥ 4 then let _ ← liftNet "sampleSet" (Parsing.parseInt split[3]!)
  if split.size ≥ 5 then let _ ← liftNet "customSampleBank" (Parsing.parseInt split[4]!)
  if split.size ≥ 6 then let _ ← liftNet "sampleVolume" (Parsing.parseInt split[5]!)
  let mut timingChange := true
  if split.size ≥ 7 then timingChange := (← char0 split[6]!) == '1'
  let mut kiai := false
  if split.size ≥ 8 then
    let flags ← liftNet "effectFlags" (Parsing.parseInt split[7]!)
    kiai := flags &&& 1 != 0
  let mut timing : Option TimingPoint := none
  if timingChange then
    if beatLength.isNaN then throw "Beat length cannot be NaN in a timing control point"
    timing := some { time, beatLength := clampBeatLength beatLength, timeSignature }
  let diff : DifficultyPoint :=
    { time, sliderVelocity := clampSV speedMultiplier, generateTicks := !beatLength.isNaN }
  let eff : EffectPoint :=
    { time, kiai, scrollSpeed := if s.rulesetId == 1 || s.rulesetId == 3 then clampScrollSpeed speedMultiplier else 1 }
  return LegacyBeatmapDecoder.addLinePoints s time timing diff eff timingChange

theorem dec_htp_body (s : DecoderState) (line : String) :
    LegacyBeatmapDecoder.handleTimingPoint s line = dec_htpBody s (split line ',') := rfl

set_option maxHeartbeats 4000000 in
theorem dec_htp_eq (s : DecoderState) (sp : _root_.Array String) :
    dec_htpBody s sp = (do
      let t0 ← at! sp 0
      let tv ← liftNet "time" (Parsing.parseDouble (trim t0))
      let b1 ← at! sp 1
      let bl ← liftNet "beatLength" (Parsing.parseDouble (trim b1) Parsing.MAX_PARSE_VALUE true)
      let ts ← dec_TS sp
      dec_CI sp 3 "sampleSet"
      dec_CI sp 4 "customSampleBank"
      dec_CI sp 5 "sampleVolume"
      let tc ← dec_TC sp
      let kiai ← dec_KI sp
      let timing ← dec_TM (LegacyBeatmapDecoder.offsetTime s tv) bl ts tc
      pure (LegacyBeatmapDecoder.addLinePoints s (LegacyBeatmapDecoder.offsetTime s tv) timing
        { time := LegacyBeatmapDecoder.offsetTime s tv, sliderVelocity := clampSV (if bl < 0 then 100.0 / -bl else 1),
          generateTicks := !bl.isNaN }
        { time := LegacyBeatmapDecoder.offsetTime s tv, kiai,
          scrollSpeed := if (s.rulesetId == 1 || s.rulesetId == 3) = true then
            clampScrollSpeed (if bl < 0 then 100.0 / -bl else 1) else 1 } tc)) := by
  unfold dec_htpBody dec_TS dec_CI dec_TC dec_KI dec_TM
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  cases at! sp 0 <;> simp only []
  rename_i t0
  cases liftNet "time" (Parsing.parseDouble (trim t0)) <;> simp only []
  cases at! sp 1 <;> simp only []
  rename_i tv b1
  cases liftNet "beatLength" (Parsing.parseDouble (trim b1) Parsing.MAX_PARSE_VALUE true) <;> simp only []
  rename_i bl
  by_cases h3 : sp.size ≥ 3 <;> by_cases h4 : sp.size ≥ 4 <;> by_cases h5 : sp.size ≥ 5 <;>
    by_cases h6 : sp.size ≥ 6 <;> by_cases h7 : sp.size ≥ 7 <;> by_cases h8 : sp.size ≥ 8 <;>
    (try (exfalso; omega)) <;> simp only [h3, h4, h5, h6, h7, h8, ite_true, ite_false]
  all_goals (repeat' split)
  all_goals first | rfl | assumption | (exfalso; omega) | (simp only [Except.error.injEq, Except.ok.injEq, reduceCtorEq] at *; done) | (simp_all; done) | (simp only [Except.ok.injEq] at *; subst_vars; simp_all; done) | (rename_i h; split at h <;> simp_all; done)

/-- List-level split on the two-character separator `//`. -/
def dec_ss2 : List Char → List (List Char)
  | [] => [[]]
  | c :: t => if c = '/' ∧ t.head? = some '/' then [] :: dec_ss2 (t.drop 1) else (dec_ss2 t).modifyHead (c :: ·)
termination_by l => l.length
decreasing_by all_goals simp_wf; all_goals (try simp); all_goals omega

theorem dec_ss2_nil : dec_ss2 [] = [[]] := by rw [dec_ss2]
theorem dec_ss2_slash2 (t : List Char) : dec_ss2 ('/' :: '/' :: t) = [] :: dec_ss2 t := by
  rw [dec_ss2]; simp
theorem dec_ss2_ne (c : Char) (t : List Char) (h : c ≠ '/') : dec_ss2 (c :: t) = (dec_ss2 t).modifyHead (c :: ·) := by
  rw [dec_ss2]; simp [h]
theorem dec_ss2_sl_ne (x : Char) (t : List Char) (h : x ≠ '/') :
    dec_ss2 ('/' :: x :: t) = (dec_ss2 (x :: t)).modifyHead ('/' :: ·) := by
  rw [dec_ss2]; simp [h]
theorem dec_ss2_sl_nil : dec_ss2 ['/'] = [['/']] := by
  rw [dec_ss2]; simp [dec_ss2_nil]

theorem dec_sep : ("//" : String) = String.ofList ['/', '/'] := by decide
theorem dec_sl_size : ('/' : Char).utf8Size = 1 := by decide

def dec_P0 (r : List Char) : Prop := ∀ (l m : List Char) (acc : List String),
  String.splitOnAux (String.ofList (l ++ m ++ r)) "//" ⟨BStr.utf8Len l⟩ ⟨BStr.utf8Len l + BStr.utf8Len m⟩ 0 acc =
    acc.reverse ++ ((dec_ss2 r).modifyHead (m ++ ·)).map String.ofList
def dec_P1 (r : List Char) : Prop := ∀ (l m : List Char) (acc : List String),
  String.splitOnAux (String.ofList (l ++ m ++ '/' :: r)) "//" ⟨BStr.utf8Len l⟩ ⟨BStr.utf8Len l + BStr.utf8Len m + 1⟩ ⟨1⟩ acc =
    acc.reverse ++ ((dec_ss2 ('/' :: r)).modifyHead (m ++ ·)).map String.ofList

theorem dec_sep_get0 : String.Pos.Raw.get ("//" : String) 0 = '/' := by
  rw [dec_sep]; have := BStr.get_of_valid [] ['/', '/']; simpa using this
theorem dec_sep_next0 : String.Pos.Raw.next ("//" : String) 0 = ⟨1⟩ := by
  rw [dec_sep]; have := BStr.next_of_valid [] '/' ['/']; simpa [dec_sl_size] using this
theorem dec_sep_get1 : String.Pos.Raw.get ("//" : String) ⟨1⟩ = '/' := by
  rw [dec_sep]; have := BStr.get_of_valid ['/'] ['/']; simpa [dec_sl_size] using this
theorem dec_sep_next1 : String.Pos.Raw.next ("//" : String) ⟨1⟩ = ⟨2⟩ := by
  rw [dec_sep]; have := BStr.next_of_valid ['/'] '/' []; simpa [dec_sl_size] using this
theorem dec_sep_end1 : (⟨1⟩ : String.Pos.Raw).atEnd ("//" : String) = false := by
  rw [dec_sep]; unfold String.Pos.Raw.atEnd; dsimp only; rw [BStr.utf8ByteSize_ofList]; simp [BStr.utf8Len, dec_sl_size]
theorem dec_sep_end2 : (⟨2⟩ : String.Pos.Raw).atEnd ("//" : String) = true := by
  rw [dec_sep]; unfold String.Pos.Raw.atEnd; dsimp only; rw [BStr.utf8ByteSize_ofList]; simp [BStr.utf8Len, dec_sl_size]

theorem dec_sep_raw : String.rawEndPos ("//" : String) = ⟨2⟩ := by
  rw [dec_sep, BStr.rawEndPos_ofList]; simp [dec_sl_size]

theorem dec_P0_nil : dec_P0 [] := by
  intro l m acc
  rw [String.splitOnAux]
  simp only [List.append_nil, BStr.atEnd_iff, BStr.rawEndPos_ofList, BStr.utf8Len_append]
  have := BStr.extract_of_valid l m []
  simp at this
  simp [this, dec_ss2_nil]

theorem dec_P1_nil : dec_P1 [] := by
  intro l m acc
  have e1 : l ++ m ++ ['/'] = l ++ (m ++ ['/']) ++ [] := by simp
  have e2 : BStr.utf8Len l + BStr.utf8Len m + 1 = BStr.utf8Len l + BStr.utf8Len (m ++ ['/']) := by
    simp [dec_sl_size]; omega
  rw [e1, e2, String.splitOnAux, BStr.extract_of_valid]
  have hend : (⟨BStr.utf8Len l + BStr.utf8Len (m ++ ['/'])⟩ : String.Pos.Raw).atEnd
      (String.ofList (l ++ (m ++ ['/']) ++ [])) = true := by
    simp only [BStr.atEnd_iff, BStr.rawEndPos_ofList, BStr.utf8Len_append, BStr.utf8Len_nil, String.Pos.Raw.le_iff]
    omega
  rw [if_pos hend]
  simp [dec_ss2_sl_nil]

theorem dec_P0_cons (x : Char) (r : List Char) (h1 : dec_P1 r) (h0 : dec_P0 r) : dec_P0 (x :: r) := by
  intro l m acc
  rw [String.splitOnAux]
  have hne : ¬ (String.rawEndPos (String.ofList (l ++ m ++ x :: r)) ≤ ⟨BStr.utf8Len l + BStr.utf8Len m⟩) := by
    rw [BStr.rawEndPos_ofList]; simp only [BStr.utf8Len_append, BStr.utf8Len_cons, String.Pos.Raw.le_iff]
    have := Char.utf8Size_pos x; omega
  have hget : String.Pos.Raw.get (String.ofList (l ++ m ++ x :: r)) ⟨BStr.utf8Len l + BStr.utf8Len m⟩ = x := by
    have := BStr.get_of_valid (l ++ m) (x :: r); simpa using this
  have hnext : String.Pos.Raw.next (String.ofList (l ++ m ++ x :: r)) ⟨BStr.utf8Len l + BStr.utf8Len m⟩ =
      ⟨BStr.utf8Len l + BStr.utf8Len m + x.utf8Size⟩ := by
    have := BStr.next_of_valid (l ++ m) x r; simpa using this
  simp only [BStr.atEnd_iff, hne, decide_false, Bool.false_eq_true, ite_false, hget, dec_sep_get0]
  by_cases hx : x = '/'
  · subst hx
    simp only [beq_self_eq_true, ite_true, hnext, dec_sep_next0, dec_sep_end1, Bool.false_eq_true, ite_false,
      dec_sl_size]
    exact h1 l m acc
  · have hx' : (x == '/') = false := by simpa using hx
    simp only [hx', Bool.false_eq_true, ite_false]
    have hu : (⟨BStr.utf8Len l + BStr.utf8Len m⟩ : String.Pos.Raw).unoffsetBy 0 = ⟨BStr.utf8Len l + BStr.utf8Len m⟩ := by
      simp [String.Pos.Raw.unoffsetBy]
    rw [hu, hnext]
    have := h0 l (m ++ [x]) acc
    simp only [BStr.utf8Len_append, BStr.utf8Len_cons, BStr.utf8Len_nil, Nat.zero_add,
      List.append_assoc, List.singleton_append, List.cons_append, List.nil_append, Nat.add_assoc] at this ⊢
    rw [this, dec_ss2_ne x r hx, List.modifyHead_modifyHead]
    simp [Function.comp_def]

theorem dec_P1_cons (x : Char) (r : List Char) (h0r : dec_P0 r) (h0xr : dec_P0 (x :: r)) : dec_P1 (x :: r) := by
  intro l m acc
  rw [String.splitOnAux]
  have hne : ¬ (String.rawEndPos (String.ofList (l ++ m ++ '/' :: x :: r)) ≤ ⟨BStr.utf8Len l + BStr.utf8Len m + 1⟩) := by
    rw [BStr.rawEndPos_ofList]; simp only [BStr.utf8Len_append, BStr.utf8Len_cons, String.Pos.Raw.le_iff, dec_sl_size]
    have := Char.utf8Size_pos x; omega
  have hget : String.Pos.Raw.get (String.ofList (l ++ m ++ '/' :: x :: r)) ⟨BStr.utf8Len l + BStr.utf8Len m + 1⟩ = x := by
    have := BStr.get_of_valid (l ++ m ++ ['/']) (x :: r); simpa [dec_sl_size, Nat.add_assoc] using this
  have hnext : String.Pos.Raw.next (String.ofList (l ++ m ++ '/' :: x :: r)) ⟨BStr.utf8Len l + BStr.utf8Len m + 1⟩ =
      ⟨BStr.utf8Len l + BStr.utf8Len m + 1 + x.utf8Size⟩ := by
    have := BStr.next_of_valid (l ++ m ++ ['/']) x r; simpa [dec_sl_size, Nat.add_assoc] using this
  simp only [BStr.atEnd_iff, hne, decide_false, Bool.false_eq_true, ite_false, hget, dec_sep_get1]
  by_cases hx : x = '/'
  · subst hx
    simp only [beq_self_eq_true, ite_true, hnext, dec_sep_next1, dec_sep_end2, dec_sl_size, dec_sep_raw, le_refl,
      not_true_eq_false, imp_false, Classical.not_not]
    have hu : (⟨BStr.utf8Len l + BStr.utf8Len m + 1 + 1⟩ : String.Pos.Raw).unoffsetBy ⟨2⟩ =
        ⟨BStr.utf8Len l + BStr.utf8Len m⟩ := by
      simp [String.Pos.Raw.unoffsetBy]
    rw [hu, BStr.extract_of_valid l m ('/' :: '/' :: r)]
    have := h0r (l ++ m ++ ['/', '/']) [] (String.ofList m :: acc)
    simp only [BStr.utf8Len_append, BStr.utf8Len_cons, BStr.utf8Len_nil, Nat.zero_add, Nat.add_zero, dec_sl_size,
      List.append_assoc, List.cons_append, List.nil_append, List.append_nil] at this ⊢
    rw [show BStr.utf8Len l + BStr.utf8Len m + 1 + 1 = BStr.utf8Len l + (BStr.utf8Len m + (1 + 1)) by omega]
    rw [this, dec_ss2_slash2]
    cases h : dec_ss2 r <;> simp
  · have hx' : (x == '/') = false := by simpa using hx
    simp only [hx', Bool.false_eq_true, ite_false]
    have hu : (⟨BStr.utf8Len l + BStr.utf8Len m + 1⟩ : String.Pos.Raw).unoffsetBy ⟨1⟩ =
        ⟨BStr.utf8Len l + BStr.utf8Len m⟩ := by
      simp [String.Pos.Raw.unoffsetBy]
    have hn2 : String.Pos.Raw.next (String.ofList (l ++ m ++ '/' :: x :: r)) ⟨BStr.utf8Len l + BStr.utf8Len m⟩ =
        ⟨BStr.utf8Len l + BStr.utf8Len m + 1⟩ := by
      have := BStr.next_of_valid (l ++ m) '/' (x :: r); simpa [dec_sl_size] using this
    rw [hu, hn2]
    have := h0xr l (m ++ ['/']) acc
    simp only [BStr.utf8Len_append, BStr.utf8Len_cons, BStr.utf8Len_nil, Nat.zero_add, dec_sl_size,
      List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] at this ⊢
    rw [show BStr.utf8Len l + BStr.utf8Len m + 1 = BStr.utf8Len l + (BStr.utf8Len m + 1) by omega]
    rw [this, dec_ss2_sl_ne x r hx, List.modifyHead_modifyHead]
    simp [Function.comp_def]

theorem dec_P_all : ∀ n, (∀ r : List Char, r.length ≤ n → dec_P0 r) ∧ (∀ r : List Char, r.length ≤ n → dec_P1 r) := by
  intro n
  induction n with
  | zero =>
    constructor
    · intro r hr; cases r with
      | nil => exact dec_P0_nil
      | cons _ _ => simp at hr
    · intro r hr; cases r with
      | nil => exact dec_P1_nil
      | cons _ _ => simp at hr
  | succ n ih =>
    have h0 : ∀ r : List Char, r.length ≤ n + 1 → dec_P0 r := by
      intro r hr
      cases r with
      | nil => exact dec_P0_nil
      | cons x r' => exact dec_P0_cons x r' (ih.2 r' (by simp at hr; omega)) (ih.1 r' (by simp at hr; omega))
    refine ⟨h0, ?_⟩
    intro r hr
    cases r with
    | nil => exact dec_P1_nil
    | cons x r' => exact dec_P1_cons x r' (ih.1 r' (by simp at hr; omega)) (h0 (x :: r') hr)

theorem dec_splitOn_ss (l : List Char) : (String.ofList l).splitOn "//" = (dec_ss2 l).map String.ofList := by
  unfold String.splitOn
  have hne : (("//" : String) == "") = false := by decide
  rw [hne]; simp only [Bool.false_eq_true, ite_false]
  have := (dec_P_all l.length).1 l le_rfl [] [] []
  simp only [List.nil_append, List.append_nil, BStr.utf8Len_nil, Nat.add_zero, List.reverse_nil] at this
  exact this.trans (by cases h : dec_ss2 l <;> simp)

theorem dec_ss2_cons_of (c : Char) (t : List Char) (h : ¬ (c = '/' ∧ t.head? = some '/')) :
    dec_ss2 (c :: t) = (dec_ss2 t).modifyHead (c :: ·) := by
  rw [dec_ss2]; simp only [h, ite_false]

theorem dec_ss2_ne_nil : ∀ l : List Char, dec_ss2 l ≠ []
  | [] => by rw [dec_ss2_nil]; simp
  | c :: t => by
    rw [dec_ss2]; split
    · simp
    · have := dec_ss2_ne_nil t
      cases h : dec_ss2 t with
      | nil => exact absurd h this
      | cons _ _ => simp
termination_by l => l.length

/-- No `//` starts before position `i`. -/
def dec_noOcc (cs : List Char) (i : Nat) : Prop :=
  ∀ p, p < i → p + 1 < cs.length → ¬ (cs[p]! = '/' ∧ cs[p+1]! = '/')

theorem dec_ss2_prefix : ∀ (i : Nat) (cs : List Char), i ≤ cs.length → dec_noOcc cs i →
    dec_ss2 cs = (dec_ss2 (cs.drop i)).modifyHead (cs.take i ++ ·)
  | 0, cs, _, _ => by simp only [List.drop_zero, List.take_zero, List.nil_append]; cases dec_ss2 cs <;> rfl
  | i+1, [], h, _ => by simp at h
  | i+1, c :: t, h, hn => by
    have h0 : ¬ (c = '/' ∧ t.head? = some '/') := by
      rintro ⟨rfl, ht⟩
      cases t with
      | nil => simp at ht
      | cons d t' =>
        simp at ht; subst ht
        exact hn 0 (by omega) (by simp) (by simp)
    rw [dec_ss2_cons_of c t h0, dec_ss2_prefix i t (by simp at h; omega)
      (by intro p hp hp1 hc; exact hn (p+1) (by omega) (by simp; omega) (by simpa using hc))]
    rw [List.modifyHead_modifyHead]
    simp [Function.comp_def]

theorem dec_ss2_none : ∀ (cs : List Char), dec_noOcc cs cs.length → dec_ss2 cs = [cs]
  | [] => fun _ => dec_ss2_nil
  | c :: t => fun hn => by
    have h0 : ¬ (c = '/' ∧ t.head? = some '/') := by
      rintro ⟨rfl, ht⟩
      cases t with
      | nil => simp at ht
      | cons d t' =>
        simp at ht; subst ht
        exact hn 0 (by simp) (by simp) (by simp)
    rw [dec_ss2_cons_of c t h0, dec_ss2_none t
      (by intro p hp hp1 hc; exact hn (p+1) (by simp; omega) (by simp; omega) (by simpa using hc))]
    simp

theorem dec_sl47 (u : U32) : (chOf u = '/') ↔ u.val = 47 := chOf_eq_lit u '/' (by decide)

theorem dec_sc_loop (line : Slice U32) : ∀ j (i : Usize), i.val + j = line.val.length →
    (i.val = 0 ∨ i.val < line.val.length) → dec_noOcc (strS line) i.val →
    ∃ k f, beatmap.decoder.strip_comments_loop line i false = ok (k, f) ∧
      (f = true → k.val + 1 < line.val.length ∧ dec_noOcc (strS line) k.val ∧
          (strS line).drop k.val = '/' :: '/' :: (strS line).drop (k.val + 2)) ∧
      (f = false → dec_noOcc (strS line) line.val.length) := by
  have hmax : line.val.length ≤ Usize.max := line.property
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro i hij hi hn
  have hn1 : 1 ≤ Usize.max := by have := Usize.bounds_eq; simp [U32.max_eq, U64.max_eq] at this; omega
  obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
  by_cases hlt : i.val + 1 < line.val.length
  · have hlt' : i1 < Slice.len line := by show i1.val < (Slice.len line).val; simp; omega
    have hil : i.val < line.val.length := by omega
    have hidx := index_eq line i hil
    have hi1l : i1.val < line.val.length := by omega
    have hidx1 : Slice.index_usize line i1 = ok (line.val[i1.val]'hi1l) := index_eq line i1 hi1l
    by_cases hocc : (line.val[i.val]'hil).val = 47 ∧ (line.val[i1.val]'hi1l).val = 47
    · -- found: one more iteration returns done (i, true)
      have hb : beatmap.decoder.strip_comments_loop.body line i false = ok (.cont (i, true)) := by
        have e1 : line.val[i.val]'hil = 47#u32 := by apply UScalar.eq_of_val_eq; simpa using hocc.1
        have e2 : line.val[i1.val]'hi1l = 47#u32 := by apply UScalar.eq_of_val_eq; simpa using hocc.2
        simp [beatmap.decoder.strip_comments_loop.body, hi1, hlt', hidx, hidx1, e1, e2, hil, hi1l]
      have hb2 : beatmap.decoder.strip_comments_loop.body line i true = ok (.done (i, true)) := by
        simp [beatmap.decoder.strip_comments_loop.body]
      refine ⟨i, true, ?_, ?_, by simp⟩
      · unfold beatmap.decoder.strip_comments_loop
        rw [loop_unfold]; simp only [hb, bind_ok]
        rw [loop_unfold]; simp only [hb2, bind_ok]
      · intro _
        refine ⟨hlt, hn, ?_⟩
        have hl : i.val + 1 < (strS line).length := by simp [strS]; omega
        rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons hl]
        have g1 : (strS line)[i.val]'(by omega) = '/' := by simp [strS]; exact (dec_sl47 _).mpr hocc.1
        have g2 : (strS line)[i.val + 1]'hl = '/' := by
          simp [strS]; have := (dec_sl47 (line.val[i1.val]'hi1l)).mpr hocc.2
          simpa [hi1v] using this
        rw [g1, g2]
    · have hb : beatmap.decoder.strip_comments_loop.body line i false = ok (.cont (i1, false)) := by
        by_cases h1 : (line.val[i.val]'hil).val = 47
        · have e1 : line.val[i.val]'hil = 47#u32 := by apply UScalar.eq_of_val_eq; simpa using h1
          have e2 : ¬ line.val[i1.val]'hi1l = 47#u32 := by
            intro h; apply hocc; exact ⟨h1, by rw [h]; rfl⟩
          simp [beatmap.decoder.strip_comments_loop.body, hi1, hlt', hidx, hidx1, e1, e2, hil, hi1l]
        · have e1 : ¬ line.val[i.val]'hil = 47#u32 := by intro h; apply h1; rw [h]; rfl
          simp [beatmap.decoder.strip_comments_loop.body, hi1, hlt', hidx, e1, hil, hi1l]
      obtain ⟨k, f, hk, hf1, hf0⟩ := ih (j - 1) (by omega) i1 (by omega) (by omega) (by
        intro p hp hp1 hc
        by_cases hpi : p < i.val
        · exact hn p hpi hp1 hc
        · have : p = i.val := by omega
          subst this
          apply hocc
          have hl : i.val + 1 < (strS line).length := by simp [strS]; omega
          rw [getElem!_pos (strS line) i.val (by omega), getElem!_pos (strS line) (i.val + 1) hl] at hc
          simp [strS] at hc
          exact ⟨(dec_sl47 _).mp hc.1, by have := (dec_sl47 _).mp hc.2; simpa [hi1v] using this⟩)
      refine ⟨k, f, ?_, hf1, hf0⟩
      unfold beatmap.decoder.strip_comments_loop
      rw [loop_unfold]; simp only [hb, bind_ok]
      unfold beatmap.decoder.strip_comments_loop at hk
      simpa using hk
  · have hlt' : ¬ i1 < Slice.len line := by show ¬ i1.val < (Slice.len line).val; simp; omega
    have hb : beatmap.decoder.strip_comments_loop.body line i false = ok (.done (i, false)) := by
      have hn1l : ¬ i1.val < line.val.length := by omega
      simp [beatmap.decoder.strip_comments_loop.body, hi1, hlt', hn1l]
    refine ⟨i, false, ?_, by simp, ?_⟩
    · unfold beatmap.decoder.strip_comments_loop
      rw [loop_unfold]; simp only [hb, bind_ok]
    · intro _ p hp hp1
      by_cases hpi : p < i.val
      · exact hn p hpi hp1
      · simp [strS] at hp1; omega

theorem beatmap.decoder.strip_comments_refines (line : Slice U32) :
    ∃ v, beatmap.decoder.strip_comments line = ok v ∧
      strV v = LegacyBeatmapDecoder.stripComments (String.ofList (strS line)) := by
  obtain ⟨k, f, hk, hf1, hf0⟩ := dec_sc_loop line line.val.length 0#usize (by simp) (by simp)
    (by intro p hp; simp at hp)
  have hlen : (strS line).length = line.val.length := by simp [strS]
  have hall : ∃ v, beatmap.dotnet.sub_str line 0#usize (Slice.len line) = ok v ∧ strV v = String.ofList (strS line) := by
    obtain ⟨v, hv, hvv⟩ := beatmap.dotnet.sub_str_refines line 0#usize (Slice.len line) (by simp) (by simp)
    refine ⟨v, hv, ?_⟩
    simp [strV, hvv, strS]
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
      refine ⟨v, hv, ?_⟩
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

theorem dec_err_bind {α β γ} {f : α → β} {e : beatmap.hit_object_parser.DecodeError} {x : Except String β}
    (h : hRel f (.Err e) x) (k : β → Except String γ) : ∃ m, (x >>= k) = .error m := by
  cases x with
  | ok b => simp [hRel] at h
  | error m => exact ⟨m, rfl⟩

macro "dec_dstep " r:term:max h:term:max v:ident : tactic =>
  `(tactic| (rcases $r:term with $v:ident | e; (on_goal 2 => exact ⟨_, rfl, Or.inr ⟨⟨e, rfl⟩, dec_err_bind $h _, rfl⟩⟩); simp only [rel_ok $h, except_bind_ok, id_eq]))

theorem beatmap.decoder.handle_timing_point_refines (s : beatmap.decoder.DecoderState) (line : Slice U32)
    (hs : ValidStr line) (hn : line.val.length < 2^62) (hn2 : line.val.length < Usize.max)
    (k : Nat) (hc : dec_cpiOk s.cpi (k+1))
    (hp : s.pending.timing.val.length + 1 < Usize.max ∧ s.pending.difficulty.val.length + 1 < Usize.max ∧
      s.pending.effect.val.length + 1 < Usize.max) :
    ∃ p, beatmap.decoder.handle_timing_point s line = ok p ∧
      dec_hRel s p (LegacyBeatmapDecoder.handleTimingPoint (dec_dsS s) (String.ofList (strS line))) := by
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
  dec_dstep r0 h0r v
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
    · exact ⟨_, rfl, Or.inr ⟨⟨e, rfl⟩, ⟨m, rfl⟩, rfl⟩⟩
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
  dec_dstep r3 h3r v3
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
    · exact ⟨_, rfl, Or.inr ⟨⟨e, rfl⟩, ⟨m, rfl⟩, rfl⟩⟩
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
  dec_dstep r6 h6r ts
  -- three int checks
  obtain ⟨r7, h7, h7r⟩ := beatmap.decoder.tp_check_int_refines (alloc.vec.Vec.deref sp) hV' 3#usize
    beatmap.errors.W_SAMPLESET "sampleSet"
  rw [deref_valA] at h7r
  change hRel id r7 (dec_CI (vstrs sp.val) 3 "sampleSet") at h7r
  simp only [h7, bind_ok]
  dec_dstep r7 h7r u7
  obtain ⟨r8, h8, h8r⟩ := beatmap.decoder.tp_check_int_refines (alloc.vec.Vec.deref sp) hV' 4#usize
    beatmap.errors.W_CUSTOMSAMPLEBANK "customSampleBank"
  rw [deref_valA] at h8r
  change hRel id r8 (dec_CI (vstrs sp.val) 4 "customSampleBank") at h8r
  simp only [h8, bind_ok]
  dec_dstep r8 h8r u8
  obtain ⟨r9, h9, h9r⟩ := beatmap.decoder.tp_check_int_refines (alloc.vec.Vec.deref sp) hV' 5#usize
    beatmap.errors.W_SAMPLEVOLUME "sampleVolume"
  rw [deref_valA] at h9r
  change hRel id r9 (dec_CI (vstrs sp.val) 5 "sampleVolume") at h9r
  simp only [h9, bind_ok]
  dec_dstep r9 h9r u9
  -- timing change, kiai
  obtain ⟨r10, h10, h10r⟩ := beatmap.decoder.tp_timing_change_refines (alloc.vec.Vec.deref sp) hV'
  rw [deref_valA] at h10r
  change hRel id r10 (dec_TC (vstrs sp.val)) at h10r
  simp only [h10, bind_ok]
  dec_dstep r10 h10r tc
  obtain ⟨r11, h11, h11r⟩ := beatmap.decoder.tp_kiai_refines (alloc.vec.Vec.deref sp) hV'
  rw [deref_valA] at h11r
  change hRel id r11 (dec_KI (vstrs sp.val)) at h11r
  simp only [h11, bind_ok]
  dec_dstep r11 h11r kiai
  -- timing point
  obtain ⟨r12, h12, h12r⟩ := beatmap.decoder.tp_timing_refines (LegacyBeatmapDecoder.offsetTime (dec_dsS s) t) bl ts tc
  change hRel (Option.map tpS) r12 (dec_TM (LegacyBeatmapDecoder.offsetTime (dec_dsS s) t) bl (i32S ts) tc) at h12r
  simp only [h12, bind_ok]
  dec_dstep r12 h12r timing
  simp only [beatmap.control_points.clamp_sv_refines, float.F64.is_nan, beatmap.decoder.tp_scroll_speed_refines, bind_ok]
  obtain ⟨s', hs', hs'v, -⟩ := beatmap.decoder.add_line_points_refines s k hc hp
    (LegacyBeatmapDecoder.offsetTime (dec_dsS s) t) timing
    { time := LegacyBeatmapDecoder.offsetTime (dec_dsS s) t, slider_velocity := clampSV (if bl < 0 then 100.0 / -bl else 1),
      generate_ticks := decide (¬ (bl.isNaN = true)) }
    { time := LegacyBeatmapDecoder.offsetTime (dec_dsS s) t, kiai := kiai,
      scroll_speed := if (i32S s.ruleset_id == 1 || i32S s.ruleset_id == 3) = true then
        clampScrollSpeed (if bl < 0 then 100.0 / -bl else 1) else 1 } tc
  simp only [hs', bind_ok]
  refine ⟨_, rfl, Or.inl ⟨rfl, ?_⟩⟩
  rw [hs'v]
  simp [dpS, epS, dec_dsS]

end OsuProofs
