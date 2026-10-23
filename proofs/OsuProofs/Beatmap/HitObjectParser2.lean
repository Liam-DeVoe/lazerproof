/-
`beatmap::hit_object_parser` part 2: `ps_repeat_count`, `ps_length`, `ps_check_banks`, `new_object`, `finish`,
`extract_v`, `append_range`, `convert_points` (segment loop in lockstep with the spec loop, `hop_cpG`),
`convert_path_string` (both loops; the spec loops are `forIn` over the parts / `List.range'`, related through
the final result `FIN`). Helper names are prefixed `hop_`.
-/
import OsuProofs.Beatmap.HitObjectParser
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

theorem hop_net_max_eq (a b : F64) : net.max a b = ok (F64.max a b) := by
  unfold net.max F64.max
  by_cases h : (a == b) = true
  · have := beq_not_nan_right h
    simp [h, f64_is_negative_eq b this]
  · simp only [Bool.not_eq_true] at h
    simp [h]
    split <;> simp_all

theorem i32S_sub_one (v : I32) : i32S (core.num.I32.wrapping_sub v 1#i32) = i32S v - 1 := by
  unfold i32S; simp [core.num.I32.wrapping_sub]

theorem beatmap.hit_object_parser.ps_repeat_count_refines (sp : Slice (alloc.vec.Vec U32)) (hV : ∀ l ∈ sp.val, ValidL l.val) :
    ∃ r, beatmap.hit_object_parser.ps_repeat_count sp = ok r ∧
      hRel i32S r (do
        let rc0 ← liftNet "repeatCount" (OsuModel.Net.Parsing.parseInt (← at! (vstrs sp.val) 6))
        if rc0 > 9000 then throw "Repeat count is way too high"
        else pure (if rc0 - 1 < 0 then 0 else rc0 - 1)) := by
  unfold beatmap.hit_object_parser.ps_repeat_count
  obtain ⟨r0, hr0, hr0v, hr0m⟩ := beatmap.hit_object_parser.at_refines sp 6#usize
  simp only [show (6#usize : Usize).val = 6 from rfl] at hr0v
  simp only [hr0, bind_ok]
  rcases r0 with v | e
  case Err => exact ⟨.Err e, rfl, rel_err hr0v _ _⟩
  rw [rel_ok hr0v]; simp only [except_bind_ok]
  have hv := hV v (hr0m v rfl)
  rw [net.parse.parse_int_default_refines _ (validStr_of v hv), bind_ok, strV_deref]
  obtain ⟨r1, hr1, hr1v⟩ := lift_net_exceptI beatmap.errors.W_REPEATCOUNT i32I i32S (fun _ => rfl)
    (OsuModel.Net.Parsing.parseInt (strV v)) "repeatCount"
  simp only [hr1, bind_ok]
  rcases r1 with a | e
  case Err => exact ⟨.Err e, rfl, rel_err hr1v _ _⟩
  rw [rel_ok hr1v]; simp only [except_bind_ok]
  have h9 : (i32S a > 9000) ↔ a > 9000#i32 := by
    show Int32.ofInt 9000 < i32S a ↔ (9000#i32 : I32).val < a.val
    rw [Int32.lt_iff_toInt_lt, i32S_toInt, Int32.toInt_ofInt_of_le (by decide) (by decide)]; simp
  by_cases k : a > 9000#i32
  · have k' : i32S a > 9000 := h9.mpr k
    simp only [k, k', if_true]
    exact ⟨_, rfl, trivial⟩
  · have k' : ¬ i32S a > 9000 := fun h => k (h9.mp h)
    simp only [k, k', if_false, lift, bind_ok]
    have h0 : ∀ x : I32, (x < 0#i32) ↔ (i32S x < 0) := by
      intro x; show x.val < (0#i32 : I32).val ↔ i32S x < Int32.ofInt 0
      rw [Int32.lt_iff_toInt_lt, i32S_toInt, Int32.toInt_ofInt_of_le (by decide) (by decide)]; simp
    by_cases k0 : core.num.I32.wrapping_sub a 1#i32 < 0#i32
    · have : i32S a - 1 < 0 := by rw [← i32S_sub_one]; exact (h0 _).mp k0
      simp only [k0, this, if_true]; exact ⟨_, rfl, rfl⟩
    · have : ¬ i32S a - 1 < 0 := by rw [← i32S_sub_one]; exact fun h => k0 ((h0 _).mpr h)
      simp only [k0, this, if_false]; exact ⟨_, rfl, by show i32S _ = _; rw [i32S_sub_one]⟩

theorem beatmap.hit_object_parser.ps_length_refines (sp : Slice (alloc.vec.Vec U32)) (hV : ∀ l ∈ sp.val, ValidL l.val)
    (hL : ∀ l ∈ sp.val, l.val.length < 2^62) :
    ∃ r, beatmap.hit_object_parser.ps_length sp = ok r ∧
      hRel id r (if (vstrs sp.val).size > 7 then do
          let l := F64.max 0 (← liftNet "length" (Parsing.parseDouble (vstrs sp.val)[7]! (F64.ofInt Parsing.MAX_COORDINATE_VALUE.toInt)))
          pure (if l == 0 then none else some l)
        else pure none) := by
  unfold beatmap.hit_object_parser.ps_length
  rw [vstrs_size]
  by_cases h7 : sp.val.length > 7
  · have h7' : Slice.len sp > 7#usize := by show (7#usize : Usize).val < (Slice.len sp).val; simpa using h7
    have hlim : (Parsing.MAX_COORDINATE_VALUE.toInt) = 131072 := by decide
    have hc : (IScalar.cast .I64 131072#i32).val = 131072 := by simp
    have hm := List.getElem_mem h7
    have hidx : Slice.index_usize sp 7#usize = ok (sp.val[7]'h7) := index_eq sp 7#usize (by simpa using h7)
    simp only [h7', h7, if_true, lift, bind_ok, float.F64.from_i64, net.parse.MAX_COORDINATE_VALUE, hc, hlim,
      hidx, vstrs_get! _ 7 h7]
    rw [net.parse.parsing_parse_double_refines _ (validStr_of _ (hV _ hm)) (by simp; exact hL _ hm), bind_ok, strV_deref]
    obtain ⟨r1, hr1, hr1v⟩ := lift_net_exceptI beatmap.errors.W_LENGTH id id (fun _ => rfl)
      (Parsing.parseDouble (strV (sp.val[7]'h7)) (F64.ofInt 131072) false) "length"
    simp only [hr1, bind_ok]
    rcases r1 with v | e
    · rw [rel_ok hr1v]; simp only [except_bind_ok]
      have h0 : beatmap.hit_object_parser.D0 = ok (0 : F64) := by
        unfold beatmap.hit_object_parser.D0; simp; decide
      simp only [h0, bind_ok, hop_net_max_eq, float.F64.eq]
      split <;> rename_i hb <;> exact ⟨_, rfl, by simp [hRel, hb]⟩
    · exact ⟨.Err e, rfl, rel_err hr1v _ _⟩
  · have h7' : ¬ Slice.len sp > 7#usize := by show ¬ (7#usize : Usize).val < (Slice.len sp).val; simpa using h7
    simp only [h7', h7, if_false]; exact ⟨_, rfl, rfl⟩

theorem beatmap.hit_object_parser.ps_check_banks_refines (sp : Slice (alloc.vec.Vec U32)) (hV : ∀ l ∈ sp.val, ValidL l.val)
    (hL : ∀ l ∈ sp.val, l.val.length < Usize.max) :
    ∃ r, beatmap.hit_object_parser.ps_check_banks sp = ok r ∧
      hRel id r (if (vstrs sp.val).size > 10 then ConvertHitObjectParser.readCustomSampleBanks (vstrs sp.val)[10]! true
        else pure ()) := by
  unfold beatmap.hit_object_parser.ps_check_banks
  rw [vstrs_size]
  by_cases h : sp.val.length > 10
  · have h' : Slice.len sp > 10#usize := by show (10#usize : Usize).val < (Slice.len sp).val; simpa using h
    have hm := List.getElem_mem h
    have hidx : Slice.index_usize sp 10#usize = ok (sp.val[10]'h) := index_eq sp 10#usize (by simpa using h)
    simp only [h', h, if_true, hidx, bind_ok, vstrs_get! _ 10 h]
    obtain ⟨r, hr, hrv⟩ := beatmap.hit_object_parser.read_custom_sample_banks_refines _ (validStr_of _ (hV _ hm))
      (by simp; exact hL _ hm) true
    rw [strV_deref] at hrv
    exact ⟨r, hr, hrv⟩
  · have h' : ¬ Slice.len sp > 10#usize := by show ¬ (10#usize : Usize).val < (Slice.len sp).val; simpa using h
    simp only [h', h, if_false]; exact ⟨_, rfl, rfl⟩

theorem beatmap.hit_object_parser.new_object_refines (st : F64) (pos : net.osutk.Vector2) (nc : Bool) (co : I32)
    (k : beatmap.types.ConvertKind) :
    ∃ o, beatmap.hit_object_parser.new_object st pos nc co k = ok o ∧
      choS o = { startTime := st, position := bv2S pos, newCombo := nc, comboOffset := i32S co, kind := ckS k } := by
  unfold beatmap.hit_object_parser.new_object
  have h1 : float.F64.from_bits 4607182418800017408#u64 = ok (1 : F64) := by simp; decide
  simp only [h1, bind_ok]
  exact ⟨_, rfl, rfl⟩

/-- Helper (spec: the local `finish` of `ConvertHitObjectParser.parse`). -/
theorem beatmap.hit_object_parser.finish_refines (st2 : beatmap.hit_object_parser.ParserState)
    (r : core.result.Result beatmap.types.ConvertHitObject beatmap.hit_object_parser.DecodeError)
    (r' : DecodeM ConvertHitObject) (h : hRel choS r r') (startTime : F64)
    (hs : ∀ o, r = .Ok o → o.start_time = startTime) :
    ∃ p, beatmap.hit_object_parser.finish st2 r = ok p ∧ psS p.1 = (match r' with
        | .ok _ => { psS st2 with firstObject := false }
        | .error _ => psS st2) ∧
      hRel choS p.2 (match r' with
        | .ok o => .ok { o with startTime }
        | .error e => .error e) := by
  unfold beatmap.hit_object_parser.finish
  rcases r with o | e <;> cases r' <;> simp [hRel] at h
  · subst h; refine ⟨_, rfl, rfl, ?_⟩; simp [hRel, choS, hs o rfl]
  · exact ⟨_, rfl, rfl, trivial⟩

theorem hop_take_drop_succ {α} (l : List α) (i hi : Nat) (h1 : i < hi) (h2 : i < l.length) :
    (l.drop i).take (hi - i) = l[i] :: (l.drop (i+1)).take (hi - (i+1)) := by
  rw [List.drop_eq_getElem_cons h2, show hi - i = (hi - (i+1)) + 1 by omega, List.take_succ_cons]

theorem hop_take_drop_end {α} (l : List α) (i hi : Nat) (h : ¬ (i < hi ∧ i < l.length)) :
    (l.drop i).take (hi - i) = [] := by
  by_cases h1 : i < hi
  · have : l.length ≤ i := by omega
    simp [List.drop_eq_nil_of_le this]
  · simp [show hi - i = 0 by omega]

theorem beatmap.hit_object_parser.extract_v_refines (a : Slice net.osutk.Vector2) (lo hi : Usize) :
    ∃ v, beatmap.hit_object_parser.extract_v a lo hi = ok v ∧ v.val = (a.val.drop lo.val).take (hi.val - lo.val) := by
  unfold beatmap.hit_object_parser.extract_v beatmap.hit_object_parser.extract_v_loop
  have hmax : a.val.length ≤ Usize.max := a.property
  obtain ⟨y, hy, hq⟩ := loop_ok (fun (x : alloc.vec.Vec net.osutk.Vector2 × Usize) => beatmap.hit_object_parser.extract_v_loop.body a hi x.1 x.2)
    (fun x => a.val.length - x.2.val)
    (fun x => x.1.val.length ≤ x.2.val - lo.val ∧ lo.val ≤ x.2.val ∧
      x.1.val ++ (a.val.drop x.2.val).take (hi.val - x.2.val) = (a.val.drop lo.val).take (hi.val - lo.val))
    (fun y => y.val = (a.val.drop lo.val).take (hi.val - lo.val))
    (by
      rintro ⟨o, i⟩ ⟨hl, hlo, he⟩
      dsimp only at hl hlo he ⊢
      by_cases hc : i.val < hi.val ∧ i.val < a.val.length
      · right
        have h1 : i < hi := hc.1
        have h2 : i < Slice.len a := by show i.val < (Slice.len a).val; simpa using hc.2
        obtain ⟨o1, ho1, ho1v⟩ := push_eq o (a.val[i.val]'hc.2) (by omega)
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
        refine ⟨(o1, i1), by simp [beatmap.hit_object_parser.extract_v_loop.body, h1, h2, index_eq a i hc.2, ho1, hi1],
          ⟨by dsimp only; rw [ho1v]; simp; omega, by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
        dsimp only; rw [← he, ho1v, hi1v, hop_take_drop_succ _ _ _ hc.1 hc.2]; simp
      · left
        refine ⟨o, ?_, ?_⟩
        · by_cases h1 : i < hi
          · have h2 : ¬ i < Slice.len a := by
              show ¬ i.val < (Slice.len a).val; simp; exact Nat.le_of_not_lt (fun h => hc ⟨h1, h⟩)
            simp [beatmap.hit_object_parser.extract_v_loop.body, h1, h2]
          · simp [beatmap.hit_object_parser.extract_v_loop.body, h1]
        · rw [← he, hop_take_drop_end _ _ _ hc]; simp)
    (alloc.vec.Vec.new _, lo) ⟨by simp [alloc.vec.Vec.new], le_refl _, by simp [alloc.vec.Vec.new]⟩
  exact ⟨y, hy, hq⟩

theorem beatmap.hit_object_parser.append_range_refines (out : alloc.vec.Vec beatmap.types.PathControlPoint)
    (vs : Slice beatmap.types.PathControlPoint) (lo hi : Usize) (hb : out.val.length + vs.val.length ≤ Usize.max) :
    ∃ v, beatmap.hit_object_parser.append_range out vs lo hi = ok v ∧
      v.val = out.val ++ (vs.val.drop lo.val).take (hi.val - lo.val) := by
  unfold beatmap.hit_object_parser.append_range beatmap.hit_object_parser.append_range_loop
  have hmax : vs.val.length ≤ Usize.max := vs.property
  obtain ⟨y, hy, hq⟩ := loop_ok (fun (x : alloc.vec.Vec beatmap.types.PathControlPoint × Usize) => beatmap.hit_object_parser.append_range_loop.body vs hi x.1 x.2)
    (fun x => vs.val.length - x.2.val)
    (fun x => x.1.val.length ≤ out.val.length + (x.2.val - lo.val) ∧ lo.val ≤ x.2.val ∧
      x.1.val ++ (vs.val.drop x.2.val).take (hi.val - x.2.val) = out.val ++ (vs.val.drop lo.val).take (hi.val - lo.val))
    (fun y => y.val = out.val ++ (vs.val.drop lo.val).take (hi.val - lo.val))
    (by
      rintro ⟨o, i⟩ ⟨hl, hlo, he⟩
      dsimp only at hl hlo he ⊢
      by_cases hc : i.val < hi.val ∧ i.val < vs.val.length
      · right
        have h1 : i < hi := hc.1
        have h2 : i < Slice.len vs := by show i.val < (Slice.len vs).val; simpa using hc.2
        obtain ⟨o1, ho1, ho1v⟩ := push_eq o (vs.val[i.val]'hc.2) (by omega)
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
        refine ⟨(o1, i1), by simp [beatmap.hit_object_parser.append_range_loop.body, h1, h2, index_eq vs i hc.2, ho1, hi1],
          ⟨by dsimp only; rw [ho1v]; simp; omega, by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
        dsimp only; rw [← he, ho1v, hi1v, hop_take_drop_succ _ _ _ hc.1 hc.2]; simp
      · left
        refine ⟨o, ?_, ?_⟩
        · by_cases h1 : i < hi
          · have h2 : ¬ i < Slice.len vs := by
              show ¬ i.val < (Slice.len vs).val; simp; exact Nat.le_of_not_lt (fun h => hc ⟨h1, h⟩)
            simp [beatmap.hit_object_parser.append_range_loop.body, h1, h2]
          · simp [beatmap.hit_object_parser.append_range_loop.body, h1]
        · rw [← he, hop_take_drop_end _ _ _ hc]; simp)
    (out, lo) ⟨by simp, le_refl _, rfl⟩
  exact ⟨y, hy, hq⟩

/-- Lockstep with exactly `j` spec iterations (`iterEx`, body never fails). -/
theorem hop_loop_iterEx_exact {α β σ ε : Type} (body : α → Result (ControlFlow α β)) (g : σ → Except ε (ForInStep σ))
    (R : Nat → α → σ → Prop) (Q : β → σ → Prop)
    (h0 : ∀ x s, R 0 x s → ∃ y, body x = ok (.done y) ∧ Q y s)
    (hs : ∀ j x s, R (j+1) x s → ∃ x' s', body x = ok (.cont x') ∧ g s = .ok (.yield s') ∧ R j x' s') :
    ∀ j x s, R j x s → ∃ y s', loop body x = ok y ∧ iterEx g j s = .ok s' ∧ Q y s' := by
  intro j
  induction j with
  | zero => intro x s hr; obtain ⟨y, hy, hq⟩ := h0 x s hr; exact ⟨y, s, by rw [loop_unfold, hy]; simp, rfl, hq⟩
  | succ j ih =>
    intro x s hr
    obtain ⟨x', s', hb, hg, hr'⟩ := hs j x s hr
    obtain ⟨y, s'', hy, hit, hq⟩ := ih x' s' hr'
    exact ⟨y, s'', by rw [loop_unfold, hb]; simpa using hy, by simp only [iterEx, hg]; exact hit, hq⟩

theorem hop_pt_eq (a b : beatmap.types.PathType) :
    beatmap.types.PathType.Insts.CoreCmpPartialEqPathType.eq a b = ok (ptS a == ptS b) := by
  unfold beatmap.types.PathType.Insts.CoreCmpPartialEqPathType.eq
  cases a <;> cases b <;> simp [ptS, beatmap.types.PathType.read_discriminant] <;> try rfl
  rename_i d1 d2
  have hb : ∀ a b : Option Int32, (PathType.bspline a == PathType.bspline b) = (a == b) := fun _ _ => rfl
  rw [hb]
  cases d1 <;> cases d2 <;> simp [core.option.Option.Insts.CoreCmpPartialEqOption.eq, core.cmp.PartialEqI32, liftFun2]
  rename_i x y
  have : (x = y) ↔ (i32S x = i32S y) := by
    constructor
    · intro h; rw [h]
    · intro h; have := congrArg Int32.toInt h; rw [i32S_toInt, i32S_toInt] at this
      exact IScalar.eq_of_val_eq this
  by_cases h : x = y
  · simp [h]
  · have h' : ¬ i32S x = i32S y := fun e => h (this.mpr e)
    simp [h, h']

abbrev CPS := _root_.Array PathControlPoint × _root_.Array PathControlPoint × Nat × Nat
abbrev CPX := alloc.vec.Vec beatmap.types.PathControlPoint × alloc.vec.Vec beatmap.types.PathControlPoint × Usize × Usize × Usize

/-- one iteration of the `convertPoints` segment loop (spec) -/
def hop_cpG (formatVersion : Int32) (type : PathType) (__s : CPS) : Except String (ForInStep CPS) :=
  have vertices := __s.1
  have __s := __s.2
  have out := __s.1
  have __s := __s.2
  have startIndex := __s.1
  have endIndex := __s.2
  have endIndex := endIndex + 1
  if endIndex < vertices.size then
    if (!vertices[endIndex]!.position.eq vertices[endIndex - 1]!.position) = true then
      pure (ForInStep.yield (vertices, out, startIndex, endIndex))
    else
      if (type == PathType.catmull && decide (endIndex > 1) && decide (formatVersion < FIRST_LAZER_VERSION)) = true then
        pure (ForInStep.yield (vertices, out, startIndex, endIndex))
      else
        if (endIndex == vertices.size - 1) = true then
          pure (ForInStep.yield (vertices, out, startIndex, endIndex))
        else
          have vertices := vertices.set! (endIndex - 1)
            (have __src := vertices[endIndex - 1]!; { position := __src.position, type := some type })
          have out := out ++ vertices.extract startIndex endIndex
          have startIndex := endIndex + 1
          pure (ForInStep.yield (vertices, out, startIndex, endIndex))
  else pure (ForInStep.yield (vertices, out, startIndex, endIndex))

def hop_pcpsA (v : alloc.vec.Vec beatmap.types.PathControlPoint) : _root_.Array PathControlPoint := (v.val.map pcpS).toArray

def hop_cpR (fv : I32) (n : Nat) (j : Nat) (x : CPX) (s : CPS) : Prop :=
  s = (hop_pcpsA x.1, hop_pcpsA x.2.1, x.2.2.1.val, x.2.2.2.1.val) ∧ x.2.2.2.1.val = x.2.2.2.2.val ∧
  x.2.2.2.2.val + j = n ∧ x.1.val.length = n ∧ x.2.1.val.length ≤ x.2.2.1.val ∧ x.2.2.1.val ≤ x.2.2.2.1.val + 1

theorem hop_pcpsA_get! (V : alloc.vec.Vec beatmap.types.PathControlPoint) (i : Nat) (h : i < V.val.length) :
    (hop_pcpsA V)[i]! = pcpS (V.val[i]'h) := by
  rw [getElem!_pos _ i (by simpa [hop_pcpsA] using h)]; simp [hop_pcpsA]

theorem hop_cp_step (fv : I32) (pt : beatmap.types.PathType) (n : Usize) (hn : 2 * n.val + 2 ≤ Usize.max) (j : Nat)
    (x : CPX) (s : CPS) (hr : hop_cpR fv n.val (j+1) x s) :
    ∃ x' s', beatmap.hit_object_parser.convert_points_loop1.body fv pt n x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 = ok (.cont x') ∧
      hop_cpG (i32S fv) (ptS pt) s = .ok (.yield s') ∧ hop_cpR fv n.val j x' s' := by
  obtain ⟨V, O, si, ei, k⟩ := x
  obtain ⟨rfl, hek, hkj, hVl, hOl, hse⟩ := hr
  dsimp only at hek hkj hVl hOl hse ⊢
  have hk : k < n := by show k.val < n.val; omega
  obtain ⟨e1, he1, he1v⟩ := usize_add_one ei (by omega)
  obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by omega)
  have hsz : (hop_pcpsA V).size = n.val := by simp [hop_pcpsA, hVl]
  have hk' : k.val < n.val := hk
  by_cases hlt : e1.val < n.val
  · have hlt' : e1 < n := hlt
    have hiv : e1.val < V.val.length := by omega
    have hiv0 : ei.val < V.val.length := by omega
    obtain ⟨i0, hi0, hi0v⟩ := eq_ok_of_spec (Usize.sub_spec (x := e1) (y := 1#usize) (by simp; omega))
    have hi0v' : i0.val = ei.val := by simp at hi0v; omega
    have hi0e : i0 = ei := UScalar.eq_of_val_eq hi0v'
    subst hi0e
    have hidx1 := vec_index_eq' V e1 hiv
    have hidx0 := vec_index_eq' V i0 hiv0
    have hg1 := hop_pcpsA_get! V e1.val hiv
    have hg0 := hop_pcpsA_get! V i0.val hiv0
    have he1m : e1.val - 1 = i0.val := by omega
    have hpe := beatmap.vector2.eq_refines (V.val[e1.val]'hiv).position (V.val[i0.val]'hiv0).position
    by_cases hb : Vec2.eq (bv2S (V.val[e1.val]'hiv).position) (bv2S (V.val[i0.val]'hiv0).position) = true
    · have hpt := hop_pt_eq pt beatmap.types.PathType.Catmull
      have hFL : beatmap.hit_object_parser.FIRST_LAZER_VERSION.val = 128 := by
        unfold beatmap.hit_object_parser.FIRST_LAZER_VERSION; rfl
      have hFS : FIRST_LAZER_VERSION = Int32.ofInt 128 := by decide
      obtain ⟨nm1, hnm1, hnm1v⟩ := eq_ok_of_spec (Usize.sub_spec (x := n) (y := 1#usize) (by simp; omega))
      have hnm1v' : nm1.val = n.val - 1 := by simp at hnm1v; omega
      have hcond : ((ptS pt == PathType.catmull && decide (e1.val > 1) && decide (i32S fv < FIRST_LAZER_VERSION)) = true) ↔
          ((ptS pt == ptS beatmap.types.PathType.Catmull) = true ∧ 1 < e1.val ∧ fv.val < 128) := by
        rw [hFS]; simp only [Bool.and_eq_true, decide_eq_true_eq, i32S_lt_iff fv 128 (by decide) (by decide)]
        simp [ptS, and_assoc]
      by_cases hlast : e1.val = n.val - 1
      · have he : e1 = nm1 := UScalar.eq_of_val_eq (by omega)
        refine ⟨(V, O, si, e1, k1), (hop_pcpsA V, hop_pcpsA O, si.val, e1.val), ?_, ?_, ⟨rfl, by dsimp only; omega,
          by dsimp only; omega, hVl, by dsimp only; omega, by dsimp only; omega⟩⟩
        · simp only [beatmap.hit_object_parser.convert_points_loop1.body, hk, if_true, he1, bind_ok, hlt', hidx1, hi0,
            hidx0, hpe, hb, hpt, hnm1, eq_true he, if_true]
          split <;> (try split) <;> (try split) <;> simp [hk1, hFL]
        · simp only [hop_cpG, hsz, ← he1v, hlt, if_true, he1m, hg1, hg0, pcpS, hb, Bool.not_true, Bool.false_eq_true, if_false]
          have : (e1.val == n.val - 1) = true := by simp [hlast]
          split <;> simp [this]
      · have hne : ¬ e1 = nm1 := fun h => hlast (by rw [h, hnm1v'])
        have hlast' : (e1.val == n.val - 1) = false := by simp [hlast]
        by_cases kc : (ptS pt == ptS beatmap.types.PathType.Catmull) = true ∧ 1 < e1.val ∧ fv.val < 128
        · obtain ⟨kc1, kc2, kc3⟩ := kc
          have kc3' : fv.val < beatmap.hit_object_parser.FIRST_LAZER_VERSION.val := by rw [hFL]; exact kc3
          refine ⟨(V, O, si, e1, k1), (hop_pcpsA V, hop_pcpsA O, si.val, e1.val), ?_, ?_, ⟨rfl, by dsimp only; omega,
            by dsimp only; omega, hVl, by dsimp only; omega, by dsimp only; omega⟩⟩
          · simp only [beatmap.hit_object_parser.convert_points_loop1.body, hk, if_true, he1, bind_ok, hlt', hidx1, hi0,
              hidx0, hpe, hb, hpt, kc1, if_true]
            simp [kc2, kc3', hk1]
          · simp only [hop_cpG, hsz, ← he1v, hlt, if_true, he1m, hg1, hg0, pcpS, hb, Bool.not_true, Bool.false_eq_true, if_false]
            rw [if_pos ((hcond).mpr ⟨kc1, kc2, kc3⟩)]; rfl
        · have hidxm := vec_index_mut_eq V i0 hiv0
          let V2 := alloc.vec.Vec.set V i0 { (V.val[i0.val]'hiv0) with ptype := some pt }
          have hV2 : V2.val = V.val.set i0.val { (V.val[i0.val]'hiv0) with ptype := some pt } := by
            simp [V2, alloc.vec.Vec.set_val_eq]
          have hV2l : V2.val.length = n.val := by rw [hV2]; simp [hVl]
          obtain ⟨O2, hO2, hO2v⟩ := beatmap.hit_object_parser.append_range_refines O (alloc.vec.Vec.deref V2) si e1
            (by rw [deref_valA, hV2l]; omega)
          rw [deref_valA] at hO2v
          obtain ⟨s2, hs2, hs2v⟩ := usize_add_one e1 (by omega)
          refine ⟨(V2, O2, s2, e1, k1), (hop_pcpsA V2, hop_pcpsA O2, s2.val, e1.val), ?_, ?_, ⟨rfl, by dsimp only; omega,
            by dsimp only; omega, hV2l, ?_, by dsimp only; omega⟩⟩
          · simp only [beatmap.hit_object_parser.convert_points_loop1.body, hk, if_true, he1, bind_ok, hlt', hidx1, hi0,
              hidx0, hpe, hb, hpt, hidxm, hnm1, hne, if_false]
            by_cases kc1 : (ptS pt == ptS beatmap.types.PathType.Catmull) = true
            · by_cases kc2 : 1 < e1.val
              · have kc3 : ¬ fv.val < beatmap.hit_object_parser.FIRST_LAZER_VERSION.val := by
                  rw [hFL]; exact fun h => kc ⟨kc1, kc2, h⟩
                simp [kc1, kc2, kc3, hnm1, hne, hidxm, hO2, hs2, hk1, V2]
              · simp [kc1, kc2, hnm1, hne, hidxm, hO2, hs2, hk1, V2]
            · simp [kc1, hnm1, hne, hidxm, hO2, hs2, hk1, V2]
          · simp only [hop_cpG, hsz, ← he1v, hlt, if_true, he1m, hg1, hg0, pcpS, hb, Bool.not_true, Bool.false_eq_true, if_false]
            rw [if_neg (fun h => kc ((hcond).mp h)), hlast']
            simp only [Bool.false_eq_true, if_false]
            have hA : (hop_pcpsA V).set! i0.val { position := bv2S (V.val[i0.val]'hiv0).position, type := some (ptS pt) } =
                hop_pcpsA V2 := by
              apply Array.toList_inj.mp
              simp [hop_pcpsA, hV2, List.map_set, pcpS]
            rw [hA, hs2v]
            have hB : hop_pcpsA O ++ (hop_pcpsA V2).extract si.val e1.val = hop_pcpsA O2 := by
              apply Array.toList_inj.mp
              simp [hop_pcpsA, hO2v, List.map_take, List.map_drop]
            rw [hB]; rfl
          · dsimp only; rw [hO2v]; simp; omega
    · have hb' : Vec2.eq (bv2S (V.val[e1.val]'hiv).position) (bv2S (V.val[i0.val]'hiv0).position) = false := by simpa using hb
      refine ⟨(V, O, si, e1, k1), (hop_pcpsA V, hop_pcpsA O, si.val, e1.val), ?_, ?_, ⟨rfl, by dsimp only; omega,
        by dsimp only; omega, hVl, by dsimp only; omega, by dsimp only; omega⟩⟩
      · simp only [beatmap.hit_object_parser.convert_points_loop1.body, hk, if_true, he1, bind_ok, hlt', hidx1, hi0,
          hidx0, hpe, hb', Bool.false_eq_true, if_false]
        simp [hk1]
      · simp only [hop_cpG, hsz, ← he1v, hlt, if_true, he1m, hg1, hg0, pcpS, hb', Bool.not_false]; rfl
  · have hlt' : ¬ e1 < n := hlt
    refine ⟨(V, O, si, e1, k1), (hop_pcpsA V, hop_pcpsA O, si.val, e1.val), ?_, ?_, ⟨rfl, by dsimp only; omega,
      by dsimp only; omega, hVl, by dsimp only; omega, by dsimp only; omega⟩⟩
    · simp [beatmap.hit_object_parser.convert_points_loop1.body, hk, he1, hlt', hlt, hk1]
    · simp only [hop_cpG, hsz, ← he1v, hlt, if_false]; rfl

def hop_cpType (fv : Int32) (type0 : PathType) (points : _root_.Array Vec2) (ep : Option Vec2) : PathType :=
  if (type0 == .perfectCurve) = true then
    if fv < FIRST_LAZER_VERSION then
      if (points.size + (if ep.isSome = true then 1 else 0) != 3) = true then .bspline none
      else if ConvertHitObjectParser.isLinear points[0]! points[1]! (ep.getD points[2]!) = true then .linear
      else type0
    else if points.size + (if ep.isSome = true then 1 else 0) > 3 then .bspline none else type0
  else type0

def hop_cpTail (fv : Int32) (T : PathType) (vertices : _root_.Array PathControlPoint) : DecodeM (_root_.Array PathControlPoint) :=
  if (vertices.size == 0) = true then throw "index 0 out of range (no vertices)"
  else do
    let vertices := vertices.set! 0 { position := vertices[0]!.position, type := some T }
    let __s ← forIn [:vertices.size] (vertices, (#[] : _root_.Array PathControlPoint), 0, 0) (fun _ __s => hop_cpG fv T __s)
    if __s.2.2.1 < __s.2.2.2 then pure (__s.2.1 ++ __s.1.extract __s.2.2.1 __s.2.2.2) else pure __s.2.1

theorem hop_convertPoints_eq (fv : Int32) (type0 : PathType) (points : _root_.Array Vec2) (ep : Option Vec2) :
    ConvertHitObjectParser.convertPoints fv type0 points ep =
      hop_cpTail fv (hop_cpType fv type0 points ep) (points.map fun p => { position := p }) := by
  unfold ConvertHitObjectParser.convertPoints hop_cpType hop_cpTail hop_cpG
  by_cases c1 : (type0 == PathType.perfectCurve) = true
  · simp only [c1, if_true]
    by_cases c2 : fv < FIRST_LAZER_VERSION
    · simp only [c2, if_true]
      by_cases c3 : ((points.map fun p => ({ position := p } : PathControlPoint)).size + (if ep.isSome = true then 1 else 0) != 3) = true
      · have c3' : (points.size + (if ep.isSome = true then 1 else 0) != 3) = true := by simpa using c3
        simp only [c3, c3', if_true]; rfl
      · have c3' : ¬ (points.size + (if ep.isSome = true then 1 else 0) != 3) = true := by simpa using c3
        simp only [c3, c3', if_false, Bool.false_eq_true]
        by_cases c4 : ConvertHitObjectParser.isLinear points[0]! points[1]! (ep.getD points[2]!) = true
        · simp only [c4, if_true]; rfl
        · simp only [c4, if_false, Bool.false_eq_true]; rfl
    · simp only [c2, if_false]
      by_cases c3 : (points.map fun p => ({ position := p } : PathControlPoint)).size + (if ep.isSome = true then 1 else 0) > 3
      · have c3' : points.size + (if ep.isSome = true then 1 else 0) > 3 := by simpa using c3
        simp only [c3, c3', if_true]; rfl
      · have c3' : ¬ points.size + (if ep.isSome = true then 1 else 0) > 3 := by simpa using c3
        simp only [c3, c3', if_false]; rfl
  · simp only [c1, if_false, Bool.false_eq_true]; rfl

theorem hop_cp_tail2 (fv : I32) (V2 : alloc.vec.Vec beatmap.types.PathControlPoint) (X : beatmap.types.PathType)
    (hn : 2 * V2.val.length + 2 ≤ Usize.max) :
    ∃ r, (do
        let (vertices3, out, start_index, end_index) ←
          beatmap.hit_object_parser.convert_points_loop1 fv V2
            X (alloc.vec.Vec.new beatmap.types.PathControlPoint) 0#usize
            0#usize (alloc.vec.Vec.len V2) 0#usize
        if start_index < end_index
        then
          let s := alloc.vec.Vec.deref vertices3
          let out1 ←
            beatmap.hit_object_parser.append_range out s start_index end_index
          ok (core.result.Result.Ok out1)
        else ok (core.result.Result.Ok out) : Result _) = ok r ∧
      hRel hop_pcpsA r (do
        let __s ← forIn [:(hop_pcpsA V2).size] (hop_pcpsA V2, (#[] : _root_.Array PathControlPoint), 0, 0)
          (fun _ __s => hop_cpG (i32S fv) (ptS X) __s)
        if __s.2.2.1 < __s.2.2.2 then pure (__s.2.1 ++ __s.1.extract __s.2.2.1 __s.2.2.2) else pure __s.2.1) ∧
      ∀ v, r = .Ok v → v.val.length ≤ V2.val.length + 1 := by
  have hn2 : (alloc.vec.Vec.len V2).val = V2.val.length := by simp
  obtain ⟨y, s', hy, hit, hq⟩ := hop_loop_iterEx_exact
    (fun (x : CPX) => beatmap.hit_object_parser.convert_points_loop1.body fv X (alloc.vec.Vec.len V2) x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (hop_cpG (i32S fv) (ptS X)) (hop_cpR fv V2.val.length)
    (fun y s => s = (hop_pcpsA y.1, hop_pcpsA y.2.1, y.2.2.1.val, y.2.2.2.val) ∧ y.2.1.val.length ≤ y.2.2.1.val ∧
      y.2.2.1.val ≤ y.2.2.2.val + 1 ∧ y.1.val.length = V2.val.length ∧ y.2.2.2.val = V2.val.length)
    (by
      rintro ⟨V, O, si, ei, k⟩ s ⟨rfl, hek, hkj, hVl, hOl, hse⟩
      dsimp only at hek hkj hVl hOl hse ⊢
      have : ¬ k < alloc.vec.Vec.len V2 := by show ¬ k.val < (alloc.vec.Vec.len V2).val; rw [hn2]; omega
      exact ⟨(V, O, si, ei), by simp [beatmap.hit_object_parser.convert_points_loop1.body, this], rfl, hOl, hse, hVl, by dsimp only; omega⟩)
    (by
      intro j x s hr
      have := hop_cp_step fv X (alloc.vec.Vec.len V2) (by rw [hn2]; omega) j x s (by rw [hn2]; exact hr)
      rw [hn2] at this; exact this)
    V2.val.length (V2, alloc.vec.Vec.new _, 0#usize, 0#usize, 0#usize) (hop_pcpsA V2, #[], 0, 0)
    ⟨by simp [hop_pcpsA, alloc.vec.Vec.new], rfl, by simp, rfl, by simp [alloc.vec.Vec.new], by simp⟩
  have hl : beatmap.hit_object_parser.convert_points_loop1 fv V2 X (alloc.vec.Vec.new _) 0#usize 0#usize
      (alloc.vec.Vec.len V2) 0#usize = ok y := by
    unfold beatmap.hit_object_parser.convert_points_loop1; exact hy
  rw [hl, bind_ok]
  have hsz2 : (hop_pcpsA V2).size = V2.val.length := by simp [hop_pcpsA]
  rw [hsz2, forIn_range_ex' _ (fun _ _ => rfl), hit]
  obtain ⟨V3, O, si, ei⟩ := y
  obtain ⟨rfl, hOl, hse, hV3l, hei⟩ := hq
  dsimp only at hOl hse hV3l hei ⊢
  by_cases hlt : si.val < ei.val
  · have hlt' : si < ei := hlt
    obtain ⟨O2, hO2, hO2v⟩ := beatmap.hit_object_parser.append_range_refines O (alloc.vec.Vec.deref V3) si ei
      (by rw [deref_valA]; omega)
    rw [deref_valA] at hO2v
    refine ⟨.Ok O2, ?_, ?_, fun v hv => by cases hv; rw [hO2v]; simp; omega⟩
    · show (if si < ei then (beatmap.hit_object_parser.append_range O (alloc.vec.Vec.deref V3) si ei >>=
          fun out1 => ok (core.result.Result.Ok out1)) else ok (core.result.Result.Ok O)) = ok (.Ok O2)
      rw [if_pos hlt', hO2]; simp
    simp only [hlt, if_true, except_bind_ok]
    show hop_pcpsA O2 = _
    apply Array.toList_inj.mp
    simp [hop_pcpsA, hO2v, List.map_take, List.map_drop]
  · have hlt' : ¬ si < ei := hlt
    refine ⟨.Ok O, ?_, ?_, fun v hv => by cases hv; omega⟩
    · show (if si < ei then (beatmap.hit_object_parser.append_range O (alloc.vec.Vec.deref V3) si ei >>=
          fun out1 => ok (core.result.Result.Ok out1)) else ok (core.result.Result.Ok O)) = ok (.Ok O)
      rw [if_neg hlt']
    simp only [hlt, if_false, except_bind_ok]
    rfl

theorem hop_cp_tail (fv : I32) (V1 : alloc.vec.Vec beatmap.types.PathControlPoint) (X : beatmap.types.PathType)
    (hn : 2 * V1.val.length + 2 ≤ Usize.max) :
    ∃ r, (do
      let i1 := alloc.vec.Vec.len V1
      if i1 = 0#usize
      then
        ok (core.result.Result.Err (beatmap.hit_object_parser.DecodeError.Msg
          beatmap.errors.M_INDEX_0_OUT_OF_RANGE_NO_VERTICES))
      else
        let (pcp, index_mut_back) ←
          alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
            beatmap.types.PathControlPoint) V1 0#usize
        let vertices2 := index_mut_back { pcp with ptype := (some X) }
        let n := alloc.vec.Vec.len vertices2
        let (vertices3, out, start_index, end_index) ←
          beatmap.hit_object_parser.convert_points_loop1 fv vertices2
            X (alloc.vec.Vec.new beatmap.types.PathControlPoint) 0#usize
            0#usize n 0#usize
        if start_index < end_index
        then
          let s := alloc.vec.Vec.deref vertices3
          let out1 ←
            beatmap.hit_object_parser.append_range out s start_index end_index
          ok (core.result.Result.Ok out1)
        else ok (core.result.Result.Ok out) : Result _) = ok r ∧
      hRel hop_pcpsA r (hop_cpTail (i32S fv) (ptS X) (hop_pcpsA V1)) ∧
      ∀ v, r = .Ok v → v.val.length ≤ V1.val.length + 1 := by
  unfold hop_cpTail
  have hsz1 : (hop_pcpsA V1).size = V1.val.length := by simp [hop_pcpsA]
  by_cases h0 : V1.val.length = 0
  · have : alloc.vec.Vec.len V1 = 0#usize := by apply UScalar.eq_of_val_eq; simp [h0]
    have h0' : ((hop_pcpsA V1).size == 0) = true := by simp [hsz1, h0]
    simp only [this, if_true, h0']
    exact ⟨_, rfl, trivial, fun v hv => by cases hv⟩
  have hne : ¬ alloc.vec.Vec.len V1 = 0#usize := by
    intro h; apply h0; have := congrArg UScalar.val h; simpa using this
  have h0' : ((hop_pcpsA V1).size == 0) = false := by simp [hsz1, h0]
  have hl0 : (0#usize : Usize).val < V1.val.length := by simp; omega
  rw [if_neg hne, h0']
  simp only [Bool.false_eq_true, if_false]
  rw [vec_index_mut_eq V1 0#usize hl0, bind_ok]
  have hV2 : (alloc.vec.Vec.set V1 0#usize { (V1.val[(0#usize : Usize).val]'hl0) with ptype := some X }).val =
      V1.val.set 0 { (V1.val[(0#usize : Usize).val]'hl0) with ptype := some X } := by simp [alloc.vec.Vec.set_val_eq]
  obtain ⟨r, hr, hrel, hrl⟩ := hop_cp_tail2 fv (alloc.vec.Vec.set V1 0#usize { (V1.val[(0#usize : Usize).val]'hl0) with ptype := some X }) X
    (by rw [hV2]; simp; omega)
  refine ⟨r, hr, ?_, fun v hv => by have := hrl v hv; rw [hV2] at this; simpa using this⟩
  have hinit : (hop_pcpsA V1).set! 0 { position := (hop_pcpsA V1)[0]!.position, type := some (ptS X) } =
      hop_pcpsA (alloc.vec.Vec.set V1 0#usize { (V1.val[(0#usize : Usize).val]'hl0) with ptype := some X }) := by
    apply Array.toList_inj.mp
    rw [hop_pcpsA_get! V1 0 (by omega)]
    simp [hop_pcpsA, hV2, List.map_set, pcpS]
  simp only [hinit]
  exact hrel

theorem hop_cp_loop0 (points : Slice net.osutk.Vector2) :
    ∃ V1, beatmap.hit_object_parser.convert_points_loop0 points
      (alloc.vec.Vec.with_capacity beatmap.types.PathControlPoint (Slice.len points)) 0#usize = ok V1 ∧
      V1.val = points.val.map (fun p => ⟨p, none⟩) := by
  unfold beatmap.hit_object_parser.convert_points_loop0
  have hmax : points.val.length ≤ Usize.max := points.property
  obtain ⟨y, hy, hq⟩ := loop_ok (fun (x : alloc.vec.Vec beatmap.types.PathControlPoint × Usize) =>
      beatmap.hit_object_parser.convert_points_loop0.body points x.1 x.2)
    (fun x => points.val.length - x.2.val)
    (fun x => x.2.val ≤ points.val.length ∧ x.1.val = (points.val.take x.2.val).map (fun p => ⟨p, none⟩))
    (fun y => y.val = points.val.map (fun p => ⟨p, none⟩))
    (by
      rintro ⟨V, i⟩ ⟨hi, hV⟩
      dsimp only at hi hV ⊢
      by_cases hlt : i.val < points.val.length
      · right
        have hlt' : i < Slice.len points := by show i.val < (Slice.len points).val; simpa using hlt
        obtain ⟨V', hV', hV'v⟩ := push_eq V ⟨points.val[i.val]'hlt, none⟩ (by rw [hV]; simp; omega)
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
        refine ⟨(V', i1), by simp [beatmap.hit_object_parser.convert_points_loop0.body, hlt', index_eq points i hlt, hV', hi1],
          ⟨by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
        dsimp only; rw [hV'v, hV, hi1v, List.take_add_one (l := points.val), List.getElem?_eq_getElem hlt]
        simp only [List.map_append, Option.toList_some, List.map_cons, List.map_nil]
      · left
        have hlt' : ¬ i < Slice.len points := by show ¬ i.val < (Slice.len points).val; simpa using hlt
        refine ⟨V, by simp [beatmap.hit_object_parser.convert_points_loop0.body, hlt'], ?_⟩
        rw [hV, List.take_of_length_le (by omega)])
    (alloc.vec.Vec.with_capacity _ _, 0#usize) ⟨by simp, by simp [alloc.vec.Vec.with_capacity]⟩
  exact ⟨y, hy, hq⟩

def hop_ptsA (points : Slice net.osutk.Vector2) : _root_.Array Vec2 := (points.val.map bv2S).toArray

theorem beatmap.hit_object_parser.convert_points_refines (fv : I32) (type0 : beatmap.types.PathType)
    (points : Slice net.osutk.Vector2) (ep : Option net.osutk.Vector2) (hn : 2 * points.val.length + 2 ≤ Usize.max) :
    ∃ r, beatmap.hit_object_parser.convert_points fv type0 points ep = ok r ∧
      hRel hop_pcpsA r (ConvertHitObjectParser.convertPoints (i32S fv) (ptS type0) (hop_ptsA points) (ep.map bv2S)) ∧
      ∀ v, r = .Ok v → v.val.length ≤ points.val.length + 1 := by
  obtain ⟨V1, hV1, hV1v⟩ := hop_cp_loop0 points
  have hverts : (hop_ptsA points).map (fun p => ({ position := p } : PathControlPoint)) = hop_pcpsA V1 := by
    apply Array.toList_inj.mp; simp [hop_ptsA, hop_pcpsA, hV1v, pcpS]
  have hV1l : V1.val.length = points.val.length := by simp [hV1v]
  have hp : ∀ {A : Result _} {B : DecodeM _}, (∃ r, A = ok r ∧ hRel hop_pcpsA r B ∧ ∀ v, r = .Ok v → v.val.length ≤ V1.val.length + 1) →
      ∃ r, A = ok r ∧ hRel hop_pcpsA r B ∧ ∀ v, r = .Ok v → v.val.length ≤ points.val.length + 1 := by
    intro A B ⟨r, h1, h2, h3⟩; exact ⟨r, h1, h2, fun v hv => by have := h3 v hv; omega⟩
  rw [hop_convertPoints_eq, hverts]
  unfold beatmap.hit_object_parser.convert_points
  simp only [hV1, bind_ok, hop_pt_eq]
  have hsz : (hop_ptsA points).size = points.val.length := by simp [hop_ptsA]
  have hFL : beatmap.hit_object_parser.FIRST_LAZER_VERSION.val = 128 := by
    unfold beatmap.hit_object_parser.FIRST_LAZER_VERSION; rfl
  have hFS : FIRST_LAZER_VERSION = Int32.ofInt 128 := by decide
  have hfv : (i32S fv < FIRST_LAZER_VERSION) ↔ fv < beatmap.hit_object_parser.FIRST_LAZER_VERSION := by
    rw [hFS, i32S_lt_iff fv 128 (by decide) (by decide)]; show _ ↔ fv.val < _; rw [hFL]
  have hepl : (if (ep.map bv2S).isSome = true then 1 else 0) = (if core.option.Option.is_some ep = true then 1 else 0) := by
    cases ep <;> rfl
  unfold hop_cpType
  by_cases c1 : (ptS type0 == ptS beatmap.types.PathType.PerfectCurve) = true
  · have c1' : (ptS type0 == PathType.perfectCurve) = true := c1
    simp only [c1, c1', if_true]
    have hepl' : ∃ e : Usize, (if core.option.Option.is_some ep = true then ok 1#usize else ok 0#usize) = ok e ∧
        e.val = (if core.option.Option.is_some ep = true then 1 else 0) := by
      cases ep <;> simp [core.option.Option.is_some]
    obtain ⟨e, he, hev⟩ := hepl'
    rw [hepl, ← hev]
    simp only [he, bind_ok]
    have he1 : e.val ≤ 1 := by rw [hev]; split <;> simp
    obtain ⟨i2, hi2, hi2v⟩ := usize_add_k (alloc.vec.Vec.len V1) e (by simp; omega)
    by_cases c2 : fv < beatmap.hit_object_parser.FIRST_LAZER_VERSION
    · simp only [c2, if_true, (hfv).mpr c2, hi2, bind_ok]
      by_cases c3 : i2.val = 3
      · have c3' : (i2 != 3#usize) = false := by
          have : i2 = 3#usize := UScalar.eq_of_val_eq (by simpa using c3)
          simp [this]
        have c3s : (points.val.length + e.val != 3) = false := by simp at hi2v ⊢; omega
        simp only [c3', Bool.false_eq_true, if_false, hsz, c3s]
        have hl2 : 2 ≤ points.val.length := by simp at hi2v; omega
        have hget : ∀ k (hk : k < points.val.length), (hop_ptsA points)[k]! = bv2S (points.val[k]'hk) := by
          intro k hk; rw [getElem!_pos _ k (by simpa [hop_ptsA] using hk)]; simp [hop_ptsA]
        have i0 := index_eq points 0#usize (by simp; omega)
        have i1 := index_eq points 1#usize (by simp; omega)
        cases ep with
        | some q =>
          simp only [bind_ok, i0, i1, beatmap.hit_object_parser.is_linear_refines, Option.map_some, Option.getD_some,
            hget 0 (by omega), hget 1 (by omega)]
          simp only [show (0#usize : Usize).val = 0 from rfl, show (1#usize : Usize).val = 1 from rfl]
          by_cases hl : ConvertHitObjectParser.isLinear (bv2S (points.val[0]'(by omega)))
              (bv2S (points.val[1]'(by omega))) (bv2S q) = true
          · simp only [hl, if_true, bind_ok]
            exact hp (hop_cp_tail fv V1 .Linear (by omega))
          · simp only [hl, if_false, Bool.false_eq_true, bind_ok]
            exact hp (hop_cp_tail fv V1 type0 (by omega))
        | none =>
          have hl3 : 2 < points.val.length := by simp [core.option.Option.is_some] at hev; simp at hi2v; omega
          have i2' := index_eq points 2#usize (by simp; omega)
          simp only [bind_ok, i0, i1, i2', beatmap.hit_object_parser.is_linear_refines, Option.map_none, Option.getD_none,
            hget 0 (by omega), hget 1 (by omega), hget 2 hl3]
          simp only [show (0#usize : Usize).val = 0 from rfl, show (1#usize : Usize).val = 1 from rfl,
            show (2#usize : Usize).val = 2 from rfl]
          by_cases hl : ConvertHitObjectParser.isLinear (bv2S (points.val[0]'(by omega)))
              (bv2S (points.val[1]'(by omega))) (bv2S (points.val[2]'hl3)) = true
          · simp only [hl, if_true, bind_ok]
            exact hp (hop_cp_tail fv V1 .Linear (by omega))
          · simp only [hl, if_false, Bool.false_eq_true, bind_ok]
            exact hp (hop_cp_tail fv V1 type0 (by omega))
      · have c3' : (i2 != 3#usize) = true := by
          have : i2 ≠ 3#usize := fun h => c3 (by rw [h]; rfl)
          simpa using this
        have c3s : (points.val.length + e.val != 3) = true := by simp only [bne_iff_ne, ne_eq]; simp at hi2v; omega
        simp only [c3', if_true, hsz, c3s, bind_ok]
        exact hp (hop_cp_tail fv V1 (.BSpline none) (by omega))
    · have c2' : ¬ i32S fv < FIRST_LAZER_VERSION := fun h => c2 ((hfv).mp h)
      simp only [c2, c2', if_false, hi2, bind_ok, hsz]
      by_cases c3 : i2.val > 3
      · have c3' : i2 > 3#usize := c3
        have c3s : points.val.length + e.val > 3 := by simp at hi2v; omega
        simp only [c3', c3s, if_true, bind_ok]
        exact hp (hop_cp_tail fv V1 (.BSpline none) (by omega))
      · have c3' : ¬ i2 > 3#usize := c3
        have c3s : ¬ points.val.length + e.val > 3 := by simp at hi2v; omega
        simp only [c3', c3s, if_false, bind_ok]
        exact hp (hop_cp_tail fv V1 type0 (by omega))
  · have c1' : ¬ (ptS type0 == PathType.perfectCurve) = true := c1
    simp only [c1, c1', if_false, Bool.false_eq_true, bind_ok]
    exact hp (hop_cp_tail fv V1 type0 (by omega))

abbrev CPSS := _root_.Array Vec2 × _root_.Array (PathType × Nat)

/-- the body of the first loop of `convertPathString` (spec) -/
def hop_cpsF (fv : Int32) (offset : Vec2) (s : String) (__s : CPSS) : DecodeM (ForInStep CPSS) :=
  have points := __s.1
  have segments := __s.2
  do
  let c ← char0 s
  if charIsLetter c = true then do
      let pathType ← ConvertHitObjectParser.convertPathType s
      have segments : _root_.Array (PathType × ℕ) := segments.push (pathType, points.size)
      if (points.size == 0) = true then
          have points := points.push Vec2.zero
          pure (ForInStep.yield (points, segments))
        else pure (ForInStep.yield (points, segments))
    else do
      let __do_lift ← ConvertHitObjectParser.readPoint fv s offset
      have points : _root_.Array Vec2 := points.push __do_lift
      pure (ForInStep.yield (points, segments))

def hop_ptsV (v : alloc.vec.Vec net.osutk.Vector2) : _root_.Array Vec2 := (v.val.map bv2S).toArray
def hop_segsV (v : alloc.vec.Vec (beatmap.types.PathType × Usize)) : _root_.Array (PathType × Nat) :=
  (v.val.map (fun q => (ptS q.1, q.2.val))).toArray

abbrev CPS0X := alloc.vec.Vec net.osutk.Vector2 × alloc.vec.Vec (beatmap.types.PathType × Usize) ×
  Option beatmap.hit_object_parser.DecodeError × Usize

theorem hop_cps_loop0 (fv : I32) (offset : net.osutk.Vector2) (parts : alloc.vec.Vec (alloc.vec.Vec U32))
    (hV : ∀ l ∈ parts.val, ValidL l.val) (hL : ∀ l ∈ parts.val, l.val.length < 2^62)
    (hL2 : ∀ l ∈ parts.val, l.val.length < Usize.max) (hpn : parts.val.length + 1 < Usize.max) (FIN : DecodeM CPSS)
    (hFIN : forIn (parts.val.map strV) ((#[] : _root_.Array Vec2), (#[] : _root_.Array (PathType × Nat)))
      (hop_cpsF (i32S fv) (bv2S offset)) = FIN) :
    ∃ y, beatmap.hit_object_parser.convert_path_string_loop0 fv offset parts (alloc.vec.Vec.new _) (alloc.vec.Vec.new _)
        none 0#usize = ok y ∧ y.1.val.length ≤ parts.val.length + 1 ∧ y.2.1.val.length ≤ parts.val.length ∧
      y.2.1.val.Pairwise (fun a b => a.2.val ≤ b.2.val) ∧ (∀ q ∈ y.2.1.val, q.2.val ≤ y.1.val.length) ∧
      ((y.2.2 = none ∧ FIN = .ok (hop_ptsV y.1, hop_segsV y.2.1)) ∨ (y.2.2.isSome ∧ ∃ m, FIN = .error m)) := by
  have hmax : parts.val.length ≤ Usize.max := parts.property
  unfold beatmap.hit_object_parser.convert_path_string_loop0
  obtain ⟨y, hy, hq⟩ := loop_ok (fun (x : CPS0X) =>
      beatmap.hit_object_parser.convert_path_string_loop0.body fv offset parts x.1 x.2.1 x.2.2.1 x.2.2.2)
    (fun x => parts.val.length + 1 - x.2.2.2.val - (if x.2.2.1.isSome then 1 else 0))
    (fun x => x.2.2.2.val ≤ parts.val.length ∧ x.1.val.length ≤ x.2.2.2.val + 1 ∧ x.2.1.val.length ≤ x.2.2.2.val ∧
      x.2.1.val.Pairwise (fun a b => a.2.val ≤ b.2.val) ∧ (∀ q ∈ x.2.1.val, q.2.val ≤ x.1.val.length) ∧
      ((x.2.2.1 = none ∧ forIn ((parts.val.map strV).drop x.2.2.2.val) (hop_ptsV x.1, hop_segsV x.2.1)
          (hop_cpsF (i32S fv) (bv2S offset)) = FIN) ∨ (x.2.2.1.isSome ∧ ∃ m, FIN = .error m)))
    (fun y => y.1.val.length ≤ parts.val.length + 1 ∧ y.2.1.val.length ≤ parts.val.length ∧
      y.2.1.val.Pairwise (fun a b => a.2.val ≤ b.2.val) ∧ (∀ q ∈ y.2.1.val, q.2.val ≤ y.1.val.length) ∧
      ((y.2.2 = none ∧ FIN = .ok (hop_ptsV y.1, hop_segsV y.2.1)) ∨ (y.2.2.isSome ∧ ∃ m, FIN = .error m)))
    (by
      rintro ⟨pts, segs, err, i⟩ ⟨hi, hpl, hsl, hpw, hsb, hst⟩
      dsimp only at hi hpl hsl hpw hsb hst ⊢
      rcases hst with ⟨rfl, hfin⟩ | ⟨hsome, m, hm⟩
      · by_cases hlt : i.val < parts.val.length
        · right
          have hlt' : i < alloc.vec.Vec.len parts := by show i.val < (alloc.vec.Vec.len parts).val; simpa using hlt
          obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
          have hm := List.getElem_mem hlt
          have hsV := hV _ hm
          have hd : (parts.val.map strV).drop i.val = strV (parts.val[i.val]'hlt) :: (parts.val.map strV).drop (i.val + 1) := by
            rw [List.drop_eq_getElem_cons (by simpa using hlt)]; simp
          rw [hd, List.forIn_cons] at hfin
          obtain ⟨r0, hr0, hr0v, hr0m⟩ := beatmap.hit_object_parser.char0_refines (alloc.vec.Vec.deref (parts.val[i.val]'hlt))
          rw [strV_deref] at hr0v
          rw [ds_deref_val] at hr0m
          have base : ∀ (pts' : alloc.vec.Vec net.osutk.Vector2) (segs' : alloc.vec.Vec (beatmap.types.PathType × Usize))
              (e' : Option beatmap.hit_object_parser.DecodeError), True := fun _ _ _ => trivial
          rcases r0 with c | e
          · have hc0 := rel_ok hr0v
            have hc := hsV c (hr0m c rfl)
            by_cases hlet : charIsLetter (chOf c) = true
            · obtain ⟨r1, hr1, hr1v⟩ := beatmap.hit_object_parser.convert_path_type_refines (alloc.vec.Vec.deref (parts.val[i.val]'hlt))
                (validStr_of _ hsV)
              rw [strV_deref] at hr1v
              rcases r1 with pt | e
              · have hpt0 := rel_ok hr1v
                obtain ⟨sg, hsg, hsgv⟩ := push_eq segs (pt, alloc.vec.Vec.len pts) (by omega)
                by_cases hp0 : pts.val.length = 0
                · have hp0' : alloc.vec.Vec.len pts = 0#usize := by apply UScalar.eq_of_val_eq; simp [hp0]
                  obtain ⟨pz, hpz, hpzv⟩ := push_eq pts (bv2I Vec2.zero) (by omega)
                  refine ⟨(pz, sg, none, i1), ?_, ⟨by dsimp only; omega, by dsimp only; rw [hpzv]; simp; omega,
                    by dsimp only; rw [hsgv]; simp; omega, by dsimp only; rw [hsgv]; exact List.pairwise_append.mpr ⟨hpw, by simp, fun a ha b hb => by simp at hb; rw [hb]; exact hsb a ha⟩,
                    fun q hq => by rw [hsgv] at hq; rw [hpzv]; simp at hq ⊢; rcases hq with hq | hq
                                   · have := hsb q hq; omega
                                   · rw [hq]; simp [hp0],
                    Or.inl ⟨rfl, ?_⟩⟩, by dsimp only; simp; omega⟩
                  · simp [beatmap.hit_object_parser.convert_path_string_loop0.body, hlt', vec_index_eq' parts i hlt, hr0,
                      beatmap.chartable.char_is_letter_refines c hc, hlet, hr1, hsg, eq_true hp0', hpz, hi1]
                  · dsimp only; rw [hi1v, ← hfin]
                    have hF : hop_cpsF (i32S fv) (bv2S offset) (strV (parts.val[i.val]'hlt)) (hop_ptsV pts, hop_segsV segs) =
                        .ok (.yield (hop_ptsV pz, hop_segsV sg)) := by
                      have : ((hop_ptsV pts).size == 0) = true := by simp [hop_ptsV, hp0]
                      simp only [hop_cpsF, hc0, hpt0, except_bind_ok, hlet, if_true, this]
                      congr 3 <;> apply Array.toList_inj.mp <;> simp [hop_ptsV, hop_segsV, hpzv, hsgv, hp0]
                    rw [hF]; rfl
                · have hp0' : ¬ alloc.vec.Vec.len pts = 0#usize := by
                    intro h; apply hp0; have := congrArg UScalar.val h; simpa using this
                  refine ⟨(pts, sg, none, i1), ?_, ⟨by dsimp only; omega, by dsimp only; omega,
                    by dsimp only; rw [hsgv]; simp; omega, by dsimp only; rw [hsgv]; exact List.pairwise_append.mpr ⟨hpw, by simp, fun a ha b hb => by simp at hb; rw [hb]; exact hsb a ha⟩,
                    fun q hq => by rw [hsgv] at hq; simp at hq; rcases hq with hq | hq
                                   · exact hsb q hq
                                   · rw [hq]; simp,
                    Or.inl ⟨rfl, ?_⟩⟩, by dsimp only; simp; omega⟩
                  · simp [beatmap.hit_object_parser.convert_path_string_loop0.body, hlt', vec_index_eq' parts i hlt, hr0,
                      beatmap.chartable.char_is_letter_refines c hc, hlet, hr1, hsg, hp0', hi1]
                  · dsimp only; rw [hi1v, ← hfin]
                    have hF : hop_cpsF (i32S fv) (bv2S offset) (strV (parts.val[i.val]'hlt)) (hop_ptsV pts, hop_segsV segs) =
                        .ok (.yield (hop_ptsV pts, hop_segsV sg)) := by
                      have : ((hop_ptsV pts).size == 0) = false := by simp [hop_ptsV, hp0]
                      simp only [hop_cpsF, hc0, hpt0, except_bind_ok, hlet, if_true, this, Bool.false_eq_true, if_false]
                      congr 3; apply Array.toList_inj.mp; simp [hop_segsV, hsgv, hop_ptsV]
                    rw [hF]; rfl
              · refine ⟨(pts, segs, some e, i1), ?_, ⟨by dsimp only; omega, by dsimp only; omega,
                  by dsimp only; omega, hpw, hsb, Or.inr ⟨rfl, ?_⟩⟩, by dsimp only; simp; omega⟩
                · simp [beatmap.hit_object_parser.convert_path_string_loop0.body, hlt', vec_index_eq' parts i hlt, hr0,
                    beatmap.chartable.char_is_letter_refines c hc, hlet, hr1, hi1]
                · rw [← hfin]
                  cases h : ConvertHitObjectParser.convertPathType (strV (parts.val[i.val]'hlt)) with
                  | ok _ => rw [h] at hr1v; simp [hRel] at hr1v
                  | error m => exact ⟨m, by simp [hop_cpsF, hc0, hlet, h]⟩
            · have hlet' : charIsLetter (chOf c) = false := by simpa using hlet
              obtain ⟨r1, hr1, hr1v⟩ := beatmap.hit_object_parser.read_point_refines fv (alloc.vec.Vec.deref (parts.val[i.val]'hlt))
                (validStr_of _ hsV) (by simp; exact hL _ hm) (by simp; exact hL2 _ hm) offset
              rw [strV_deref] at hr1v
              rcases r1 with p | e
              · have hp1 := rel_ok hr1v
                obtain ⟨pz, hpz, hpzv⟩ := push_eq pts p (by omega)
                refine ⟨(pz, segs, none, i1), ?_, ⟨by dsimp only; omega, by dsimp only; rw [hpzv]; simp; omega,
                  by dsimp only; omega, hpw, fun q hq => by have := hsb q hq; rw [hpzv]; simp; omega,
                  Or.inl ⟨rfl, ?_⟩⟩, by dsimp only; simp; omega⟩
                · simp [beatmap.hit_object_parser.convert_path_string_loop0.body, hlt', vec_index_eq' parts i hlt, hr0,
                    beatmap.chartable.char_is_letter_refines c hc, hlet', hr1, hpz, hi1]
                · dsimp only; rw [hi1v, ← hfin]
                  have hF : hop_cpsF (i32S fv) (bv2S offset) (strV (parts.val[i.val]'hlt)) (hop_ptsV pts, hop_segsV segs) =
                      .ok (.yield (hop_ptsV pz, hop_segsV segs)) := by
                    simp only [hop_cpsF, hc0, hp1, except_bind_ok, hlet', Bool.false_eq_true, if_false]
                    congr 3; apply Array.toList_inj.mp; simp [hop_ptsV, hpzv]
                  rw [hF]; rfl
              · refine ⟨(pts, segs, some e, i1), ?_, ⟨by dsimp only; omega, by dsimp only; omega,
                  by dsimp only; omega, hpw, hsb, Or.inr ⟨rfl, ?_⟩⟩, by dsimp only; simp; omega⟩
                · simp [beatmap.hit_object_parser.convert_path_string_loop0.body, hlt', vec_index_eq' parts i hlt, hr0,
                    beatmap.chartable.char_is_letter_refines c hc, hlet', hr1, hi1]
                · rw [← hfin]
                  cases h : ConvertHitObjectParser.readPoint (i32S fv) (strV (parts.val[i.val]'hlt)) (bv2S offset) with
                  | ok _ => rw [h] at hr1v; simp [hRel] at hr1v
                  | error m => exact ⟨m, by simp [hop_cpsF, hc0, hlet', h]⟩
          · refine ⟨(pts, segs, some e, i1), ?_, ⟨by dsimp only; omega, by dsimp only; omega,
              by dsimp only; omega, hpw, hsb, Or.inr ⟨rfl, ?_⟩⟩, by dsimp only; simp; omega⟩
            · simp [beatmap.hit_object_parser.convert_path_string_loop0.body, hlt', vec_index_eq' parts i hlt, hr0, hi1]
            · rw [← hfin]
              cases h : char0 (strV (parts.val[i.val]'hlt)) with
              | ok _ => rw [h] at hr0v; simp [hRel] at hr0v
              | error m => exact ⟨m, by simp [hop_cpsF, h]⟩
        · left
          have hlt' : ¬ i < alloc.vec.Vec.len parts := by show ¬ i.val < (alloc.vec.Vec.len parts).val; simpa using hlt
          refine ⟨(pts, segs, none), by simp [beatmap.hit_object_parser.convert_path_string_loop0.body, hlt'],
            by dsimp only; omega, by dsimp only; omega, hpw, hsb, Or.inl ⟨rfl, ?_⟩⟩
          rw [← hfin, List.drop_eq_nil_of_le (by simp; omega)]; rfl
      · left
        obtain ⟨e, rfl⟩ := Option.isSome_iff_exists.mp hsome
        exact ⟨(pts, segs, some e), by simp [beatmap.hit_object_parser.convert_path_string_loop0.body],
          by dsimp only; omega, by dsimp only; omega, hpw, hsb, Or.inr ⟨rfl, m, hm⟩⟩)
    (alloc.vec.Vec.new _, alloc.vec.Vec.new _, none, 0#usize)
    ⟨by simp, by simp [alloc.vec.Vec.new], by simp [alloc.vec.Vec.new], by simp [alloc.vec.Vec.new],
      by simp [alloc.vec.Vec.new],
      Or.inl ⟨rfl, by simpa [hop_ptsV, hop_segsV, alloc.vec.Vec.new] using hFIN⟩⟩
  exact ⟨y, hy, hq⟩

theorem hop_cps_append (cp cps : alloc.vec.Vec beatmap.types.PathControlPoint) (h : cp.val.length + cps.val.length ≤ Usize.max) :
    ∃ v, beatmap.hit_object_parser.convert_path_string_loop1_loop0 cp cps 0#usize = ok v ∧ v.val = cp.val ++ cps.val := by
  unfold beatmap.hit_object_parser.convert_path_string_loop1_loop0
  obtain ⟨y, hy, hq⟩ := loop_ok (fun (x : alloc.vec.Vec beatmap.types.PathControlPoint × Usize) =>
      beatmap.hit_object_parser.convert_path_string_loop1_loop0.body cps x.1 x.2)
    (fun x => cps.val.length - x.2.val)
    (fun x => x.2.val ≤ cps.val.length ∧ x.1.val = cp.val ++ cps.val.take x.2.val)
    (fun y => y.val = cp.val ++ cps.val)
    (by
      rintro ⟨o, k⟩ ⟨hk, ho⟩
      dsimp only at hk ho ⊢
      by_cases hlt : k.val < cps.val.length
      · right
        have hlt' : k < alloc.vec.Vec.len cps := by show k.val < (alloc.vec.Vec.len cps).val; simpa using hlt
        obtain ⟨o1, ho1, ho1v⟩ := push_eq o (cps.val[k.val]'hlt) (by rw [ho]; simp; omega)
        obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := cps.property; omega)
        refine ⟨(o1, k1), by simp [beatmap.hit_object_parser.convert_path_string_loop1_loop0.body, hlt', vec_index_eq' cps k hlt, ho1, hk1],
          ⟨by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
        dsimp only; rw [ho1v, ho, hk1v, List.take_add_one, List.getElem?_eq_getElem hlt]; simp
      · left
        have hlt' : ¬ k < alloc.vec.Vec.len cps := by show ¬ k.val < (alloc.vec.Vec.len cps).val; simpa using hlt
        refine ⟨o, by simp [beatmap.hit_object_parser.convert_path_string_loop1_loop0.body, hlt'], ?_⟩
        rw [ho, List.take_of_length_le (by omega)])
    (cp, 0#usize) ⟨by simp, by simp⟩
  exact ⟨y, hy, hq⟩

/-- the body of the second loop of `convertPathString` (spec) -/
def hop_cpsG (fv : Int32) (points : _root_.Array Vec2) (segments : _root_.Array (PathType × Nat)) (i : Nat)
    (__s : _root_.Array PathControlPoint) : DecodeM (ForInStep (_root_.Array PathControlPoint)) :=
  have controlPoints := __s
  match segments[i]! with
  | (type, startIndex) =>
    if i < segments.size - 1 then
      have endIndex := segments[i + 1]!.2
      have endPoint := points[endIndex]?.getD Vec2.zero
      do
      let __do_lift ← ConvertHitObjectParser.convertPoints fv type (points.extract startIndex endIndex) (some endPoint)
      have controlPoints : _root_.Array PathControlPoint := controlPoints ++ __do_lift
      pure (ForInStep.yield controlPoints)
    else do
      let __do_lift ← ConvertHitObjectParser.convertPoints fv type (points.extract startIndex) none
      have controlPoints : _root_.Array PathControlPoint := controlPoints ++ __do_lift
      pure (ForInStep.yield controlPoints)

theorem hop_convertPathString_eq (fv : Int32) (pointString : String) (offset : Vec2) :
    ConvertHitObjectParser.convertPathString fv pointString offset = (do
      let s ← forIn (split pointString '|') ((#[] : _root_.Array Vec2), (#[] : _root_.Array (PathType × Nat))) (hop_cpsF fv offset)
      forIn (List.range' 0 s.2.size) (#[] : _root_.Array PathControlPoint) (hop_cpsG fv s.1 s.2)) := by
  unfold ConvertHitObjectParser.convertPathString
  simp only []
  congr 1
  funext st
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure]
  rfl

def hop_segStart (pts : alloc.vec.Vec net.osutk.Vector2) (segs : alloc.vec.Vec (beatmap.types.PathType × Usize)) (j : Nat) : Nat :=
  if h : j < segs.val.length then (segs.val[j]'h).2.val else pts.val.length

abbrev CPS1X := Option beatmap.hit_object_parser.DecodeError × alloc.vec.Vec beatmap.types.PathControlPoint × Usize

theorem hop_ptsV_get! (v : alloc.vec.Vec net.osutk.Vector2) (i : Nat) (h : i < v.val.length) : (hop_ptsV v)[i]! = bv2S (v.val[i]'h) := by
  rw [getElem!_pos _ i (by simpa [hop_ptsV] using h)]; simp [hop_ptsV]
theorem hop_segsV_get! (v : alloc.vec.Vec (beatmap.types.PathType × Usize)) (i : Nat) (h : i < v.val.length) :
    (hop_segsV v)[i]! = (ptS (v.val[i]'h).1, (v.val[i]'h).2.val) := by
  rw [getElem!_pos _ i (by simpa [hop_segsV] using h)]; simp [hop_segsV]

theorem hop_cps_loop1 (fv : I32) (pts : alloc.vec.Vec net.osutk.Vector2) (segs : alloc.vec.Vec (beatmap.types.PathType × Usize))
    (hpw : segs.val.Pairwise (fun a b => a.2.val ≤ b.2.val)) (hsb : ∀ q ∈ segs.val, q.2.val ≤ pts.val.length)
    (hB : 2 * (pts.val.length + segs.val.length) + 4 ≤ Usize.max) (FIN : DecodeM (_root_.Array PathControlPoint))
    (hFIN : forIn (List.range' 0 segs.val.length) (#[] : _root_.Array PathControlPoint)
      (hop_cpsG (i32S fv) (hop_ptsV pts) (hop_segsV segs)) = FIN) :
    ∃ y, beatmap.hit_object_parser.convert_path_string_loop1 fv pts segs none (alloc.vec.Vec.new _) 0#usize = ok y ∧
      ((y.1 = none ∧ FIN = .ok (hop_pcpsA y.2)) ∨ (y.1.isSome ∧ ∃ m, FIN = .error m)) := by
  have hsz : (hop_segsV segs).size = segs.val.length := by simp [hop_segsV]
  unfold beatmap.hit_object_parser.convert_path_string_loop1
  obtain ⟨y, hy, hq⟩ := loop_ok (fun (x : CPS1X) =>
      beatmap.hit_object_parser.convert_path_string_loop1.body fv pts segs x.1 x.2.1 x.2.2)
    (fun x => segs.val.length + 1 - x.2.2.val - (if x.1.isSome then 1 else 0))
    (fun x => x.2.2.val ≤ segs.val.length ∧
      ((x.1 = none ∧ forIn (List.range' x.2.2.val (segs.val.length - x.2.2.val)) (hop_pcpsA x.2.1)
          (hop_cpsG (i32S fv) (hop_ptsV pts) (hop_segsV segs)) = FIN ∧
          x.2.1.val.length ≤ hop_segStart pts segs x.2.2.val + x.2.2.val) ∨ (x.1.isSome ∧ ∃ m, FIN = .error m)))
    (fun y => (y.1 = none ∧ FIN = .ok (hop_pcpsA y.2)) ∨ (y.1.isSome ∧ ∃ m, FIN = .error m))
    (by
      rintro ⟨err, cp, j⟩ ⟨hj, hst⟩
      dsimp only at hj hst ⊢
      rcases hst with ⟨rfl, hfin, hcl⟩ | ⟨hsome, m, hm⟩
      · by_cases hlt : j.val < segs.val.length
        · right
          have hlt' : j < alloc.vec.Vec.len segs := by show j.val < (alloc.vec.Vec.len segs).val; simpa using hlt
          obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by omega)
          have hr' : List.range' j.val (segs.val.length - j.val) = j.val :: List.range' (j.val + 1) (segs.val.length - (j.val + 1)) := by
            rw [show segs.val.length - j.val = (segs.val.length - (j.val + 1)) + 1 by omega, List.range'_succ]
          rw [hr', List.forIn_cons] at hfin
          have hseg := vec_index_eq' segs j hlt
          generalize hq : segs.val[j.val]'hlt = q at hseg
          obtain ⟨pt, si⟩ := q
          have hqm : (pt, si) ∈ segs.val := by rw [← hq]; exact List.getElem_mem hlt
          have hsi := hsb _ hqm
          obtain ⟨nm1, hnm1, hnm1v⟩ := eq_ok_of_spec (Usize.sub_spec (x := alloc.vec.Vec.len segs) (y := 1#usize) (by simp; omega))
          have hnm1v' : nm1.val = segs.val.length - 1 := by simp at hnm1v; omega
          have hsg := hop_segsV_get! segs j.val hlt
          rw [hq] at hsg
          -- common continuation: given the converted segment `r`
          have cont : ∀ (r : core.result.Result (alloc.vec.Vec beatmap.types.PathControlPoint) beatmap.hit_object_parser.DecodeError)
              (sp : DecodeM (_root_.Array PathControlPoint)) (lb : Nat),
              hRel hop_pcpsA r sp → (∀ v, r = .Ok v → v.val.length ≤ lb) →
              hop_cpsG (i32S fv) (hop_ptsV pts) (hop_segsV segs) j.val (hop_pcpsA cp) =
                (do let d ← sp; pure (ForInStep.yield (hop_pcpsA cp ++ d))) →
              cp.val.length + lb ≤ hop_segStart pts segs (j.val + 1) + (j.val + 1) →
              ∃ x', (match r with
                | core.result.Result.Ok cps => do
                  let control_points1 ← beatmap.hit_object_parser.convert_path_string_loop1_loop0 cp cps 0#usize
                  let j1 ← j + 1#usize
                  ok (ControlFlow.cont (none, control_points1, j1))
                | core.result.Result.Err e => do
                  let j1 ← j + 1#usize
                  ok (ControlFlow.cont (some e, cp, j1)) : Result (ControlFlow CPS1X
                    (Option beatmap.hit_object_parser.DecodeError × alloc.vec.Vec beatmap.types.PathControlPoint))) =
                  ok (ControlFlow.cont x') ∧
                (x'.2.2.val ≤ segs.val.length ∧
                  ((x'.1 = none ∧ forIn (List.range' x'.2.2.val (segs.val.length - x'.2.2.val)) (hop_pcpsA x'.2.1)
                    (hop_cpsG (i32S fv) (hop_ptsV pts) (hop_segsV segs)) = FIN ∧
                    x'.2.1.val.length ≤ hop_segStart pts segs x'.2.2.val + x'.2.2.val) ∨ (x'.1.isSome ∧ ∃ m, FIN = .error m))) ∧
                (segs.val.length + 1 - x'.2.2.val - (if x'.1.isSome then 1 else 0)) <
                  (segs.val.length + 1 - j.val - (if (none : Option beatmap.hit_object_parser.DecodeError).isSome then 1 else 0)) := by
            intro r sp lb hrel hlb hGe hbound
            rcases r with cps | e
            · have hsp := rel_ok hrel
              have hcl : cp.val.length + cps.val.length ≤ Usize.max := by
                have := hlb cps rfl
                have : hop_segStart pts segs (j.val + 1) ≤ pts.val.length := by
                  unfold hop_segStart; split
                  · exact hsb _ (List.getElem_mem _)
                  · exact le_refl _
                omega
              obtain ⟨cp', hcp', hcp'v⟩ := hop_cps_append cp cps hcl
              refine ⟨(none, cp', j1), by simp [hcp', hj1], ⟨by dsimp only; omega, Or.inl ⟨rfl, ?_, ?_⟩⟩, by dsimp only; simp; omega⟩
              · dsimp only; rw [hj1v, ← hfin, hGe, hsp]
                have : hop_pcpsA cp ++ hop_pcpsA cps = hop_pcpsA cp' := by
                  apply Array.toList_inj.mp; simp [hop_pcpsA, hcp'v]
                simp only [except_bind_ok, except_pure, this]
              · dsimp only; rw [hcp'v, hj1v]; simp; have := hlb cps rfl; omega
            · refine ⟨(some e, cp, j1), by simp [hj1], ⟨by dsimp only; omega, Or.inr ⟨rfl, ?_⟩⟩, by dsimp only; simp; omega⟩
              cases hspc : sp with
              | ok _ => rw [hspc] at hrel; simp [hRel] at hrel
              | error m => exact ⟨m, by rw [← hfin, hGe, hspc]; rfl⟩
          have hP := hpw
          rw [List.pairwise_iff_getElem] at hP
          by_cases hlast : j.val < segs.val.length - 1
          · have hlast' : j < nm1 := by show j.val < nm1.val; omega
            have hl1 : j1.val < segs.val.length := by omega
            have hseg1 := vec_index_eq' segs j1 hl1
            have hle : si.val ≤ (segs.val[j1.val]'hl1).2.val := by
              have := hP j.val j1.val hlt hl1 (by omega); rw [hq] at this; exact this
            generalize hq1 : segs.val[j1.val]'hl1 = q1 at hseg1 hle
            obtain ⟨pt1, ei⟩ := q1
            have hle' : si.val ≤ ei.val := hle
            have hsg1 := hop_segsV_get! segs j1.val hl1
            rw [hq1, hj1v] at hsg1
            have hei : ei.val ≤ pts.val.length := hsb (pt1, ei) (by rw [← hq1]; exact List.getElem_mem hl1)
            obtain ⟨v, hv, hvv⟩ := beatmap.hit_object_parser.extract_v_refines (alloc.vec.Vec.deref pts) si ei
            rw [deref_valA] at hvv
            have hvl : v.val.length ≤ ei.val - si.val := by rw [hvv]; simp
            obtain ⟨ep, hep, hepv⟩ : ∃ ep : net.osutk.Vector2,
                (if ei < alloc.vec.Vec.len pts then alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice net.osutk.Vector2) pts ei
                  else beatmap.vector2.ZERO) = ok ep ∧ bv2S ep = (hop_ptsV pts)[ei.val]?.getD Vec2.zero := by
              by_cases he : ei.val < pts.val.length
              · have he' : ei < alloc.vec.Vec.len pts := by show ei.val < (alloc.vec.Vec.len pts).val; simpa using he
                exact ⟨pts.val[ei.val]'he, by simp only [he', if_true]; exact vec_index_eq' pts ei he, by simp [hop_ptsV, he]⟩
              · have he' : ¬ ei < alloc.vec.Vec.len pts := by show ¬ ei.val < (alloc.vec.Vec.len pts).val; simpa using he
                exact ⟨bv2I Vec2.zero, by simp [he'], by simp [hop_ptsV, he]⟩
            obtain ⟨r, hr, hrv, hrl⟩ := beatmap.hit_object_parser.convert_points_refines fv pt (alloc.vec.Vec.deref v) (some ep)
              (by rw [deref_valA]; omega)
            have hpa : hop_ptsA (alloc.vec.Vec.deref v) = (hop_ptsV pts).extract si.val ei.val := by
              apply Array.toList_inj.mp; simp [hop_ptsA, hop_ptsV, hvv, List.map_take, List.map_drop]
            rw [hpa] at hrv; rw [deref_valA] at hrl
            generalize hz : (0#usize : Usize) = z at cont
            obtain ⟨x', hx', hx'r, hx'm⟩ := cont r _ (v.val.length + 1) hrv hrl
              (by
                simp only [hop_cpsG, hsg, hsz, show j.val < segs.val.length - 1 from hlast, if_true, hsg1, Option.map_some, hepv])
              (by
                unfold hop_segStart at hcl
                rw [dif_pos hlt, hq] at hcl; dsimp only at hcl
                have e : segs.val[j.val + 1]'(by omega) = (pt1, ei) := by rw [← hq1]; simp [hj1v]
                unfold hop_segStart; rw [dif_pos (by omega), e]; dsimp only; omega)
            refine ⟨x', ?_, hx'r, hx'm⟩
            simp only [beatmap.hit_object_parser.convert_path_string_loop1.body, core.option.Option.is_none, if_true, hlt', hseg, bind_ok,
              hnm1, hlast', hj1, hseg1, hep, hv, hr]
            rw [← hz] at hx'
            simp only [Option.isNone_none, if_true]
            show (do
              let r ← (do
                let end_point ← (if ei < alloc.vec.Vec.len pts then
                    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice net.osutk.Vector2) pts ei
                  else beatmap.vector2.ZERO)
                let v ← beatmap.hit_object_parser.extract_v (alloc.vec.Vec.deref pts) si ei
                beatmap.hit_object_parser.convert_points fv pt (alloc.vec.Vec.deref v) (some end_point))
              match r with
              | core.result.Result.Ok cps => do
                let control_points1 ← beatmap.hit_object_parser.convert_path_string_loop1_loop0 cp cps 0#usize
                ok (ControlFlow.cont (none, control_points1, j1))
              | core.result.Result.Err e => ok (ControlFlow.cont (some e, cp, j1))) = ok (ControlFlow.cont x')
            rw [hep, bind_ok, hv, bind_ok, hr, bind_ok]
            rcases r with cps | e
            · simp only [hj1, bind_ok] at hx'; exact hx'
            · simp only [hj1, bind_ok] at hx'; exact hx'
          · have hlast' : ¬ j < nm1 := by show ¬ j.val < nm1.val; omega
            have hsi' : si.val ≤ pts.val.length := hsi
            obtain ⟨v, hv, hvv⟩ := beatmap.hit_object_parser.extract_v_refines (alloc.vec.Vec.deref pts) si (alloc.vec.Vec.len pts)
            rw [deref_valA] at hvv
            have hvl : v.val.length ≤ pts.val.length - si.val := by rw [hvv]; simp
            obtain ⟨r, hr, hrv, hrl⟩ := beatmap.hit_object_parser.convert_points_refines fv pt (alloc.vec.Vec.deref v) none
              (by rw [deref_valA]; omega)
            have hpa : hop_ptsA (alloc.vec.Vec.deref v) = (hop_ptsV pts).extract si.val := by
              apply Array.toList_inj.mp; simp [hop_ptsA, hop_ptsV, hvv, List.map_take, List.map_drop]
            rw [hpa] at hrv; rw [deref_valA] at hrl
            generalize hz : (0#usize : Usize) = z at cont
            obtain ⟨x', hx', hx'r, hx'm⟩ := cont r _ (v.val.length + 1) hrv hrl
              (by
                simp only [hop_cpsG, hsg, hsz, show ¬ j.val < segs.val.length - 1 from hlast, if_false, Option.map_none])
              (by
                unfold hop_segStart at hcl
                rw [dif_pos hlt, hq] at hcl; dsimp only at hcl
                unfold hop_segStart; rw [dif_neg (by omega)]; omega)
            refine ⟨x', ?_, hx'r, hx'm⟩
            simp only [beatmap.hit_object_parser.convert_path_string_loop1.body, core.option.Option.is_none, if_true, hlt', hseg,
              bind_ok, hnm1, hlast', if_false, hv, hr, hj1]
            rw [← hz] at hx'
            simp only [Option.isNone_none, if_true]
            show (do
              let r ← (do
                let v ← beatmap.hit_object_parser.extract_v (alloc.vec.Vec.deref pts) si (alloc.vec.Vec.len pts)
                beatmap.hit_object_parser.convert_points fv pt (alloc.vec.Vec.deref v) none)
              match r with
              | core.result.Result.Ok cps => do
                let control_points1 ← beatmap.hit_object_parser.convert_path_string_loop1_loop0 cp cps 0#usize
                ok (ControlFlow.cont (none, control_points1, j1))
              | core.result.Result.Err e => ok (ControlFlow.cont (some e, cp, j1))) = ok (ControlFlow.cont x')
            rw [hv, bind_ok, hr, bind_ok]
            rcases r with cps | e
            · simp only [hj1, bind_ok] at hx'; exact hx'
            · simp only [hj1, bind_ok] at hx'; exact hx'
        · left
          have hlt' : ¬ j < alloc.vec.Vec.len segs := by show ¬ j.val < (alloc.vec.Vec.len segs).val; simpa using hlt
          refine ⟨(none, cp), by simp [beatmap.hit_object_parser.convert_path_string_loop1.body, hlt'], Or.inl ⟨rfl, ?_⟩⟩
          rw [← hfin, show segs.val.length - j.val = 0 by omega]; rfl
      · left
        obtain ⟨e, rfl⟩ := Option.isSome_iff_exists.mp hsome
        exact ⟨(some e, cp), by simp [beatmap.hit_object_parser.convert_path_string_loop1.body], Or.inr ⟨rfl, m, hm⟩⟩)
    (none, alloc.vec.Vec.new _, 0#usize)
    ⟨by simp, Or.inl ⟨rfl, by simpa [hop_pcpsA, alloc.vec.Vec.new] using hFIN, by simp [alloc.vec.Vec.new]⟩⟩
  exact ⟨y, hy, hq⟩

theorem hop_splitOnP_len {α} (p : α → Bool) : ∀ l : List α, (l.splitOnP p).length ≤ l.length + 1
  | [] => by simp
  | x :: xs => by
    rw [List.splitOnP_cons]
    have := hop_splitOnP_len p xs
    split <;> simp <;> omega

theorem hop_split_count (s : Slice U32) (hs : ValidStr s) (hn : s.val.length < Usize.max) (c : U32) (hc : c.val.isValidChar)
    (sp : alloc.vec.Vec (alloc.vec.Vec U32)) (h : vstrs sp.val = split (String.ofList (strS s)) (chOf c)) :
    sp.val.length ≤ s.val.length + 1 := by
  have h2 := congrArg Array.size h
  simp only [vstrs, List.size_toArray, List.length_map, split, splitOn_char, List.splitOn_eq_splitOnP] at h2
  rw [h2]
  have := hop_splitOnP_len (· == chOf c) (strS s)
  have hl : (strS s).length = s.val.length := by simp [strS]
  omega

theorem pipe_lit : chOf 124#u32 = '|' := by decide

theorem beatmap.hit_object_parser.convert_path_string_refines (fv : I32) (ps : Slice U32) (hs : ValidStr ps)
    (hn : 4 * ps.val.length + 16 ≤ Usize.max) (hn2 : ps.val.length < 2^62) (offset : net.osutk.Vector2) :
    ∃ r, beatmap.hit_object_parser.convert_path_string fv ps offset = ok r ∧
      hRel hop_pcpsA r (ConvertHitObjectParser.convertPathString (i32S fv) (String.ofList (strS ps)) (bv2S offset)) := by
  obtain ⟨parts, hp, hpv, hpV, hpL⟩ := split_rel ps hs (by omega) 124#u32 (by decide)
  have hcnt := hop_split_count ps hs (by omega) 124#u32 (by decide) parts hpv
  rw [pipe_lit] at hpv
  rw [hop_convertPathString_eq, ← hpv]
  unfold beatmap.hit_object_parser.convert_path_string
  simp only [hp, bind_ok]
  obtain ⟨y, hy, hyl1, hyl2, hypw, hysb, hyr⟩ := hop_cps_loop0 fv offset parts hpV (fun l hl => by have := hpL l hl; omega)
    (fun l hl => by have := hpL l hl; omega) (by omega) _ rfl
  rw [hy, bind_ok]
  have hfa : forIn (vstrs parts.val) ((#[] : _root_.Array Vec2), (#[] : _root_.Array (PathType × Nat))) (hop_cpsF (i32S fv) (bv2S offset)) =
      forIn (parts.val.map strV) ((#[] : _root_.Array Vec2), (#[] : _root_.Array (PathType × Nat))) (hop_cpsF (i32S fv) (bv2S offset)) := by
    rw [← Array.forIn_toList]; simp [vstrs]
  rw [hfa]
  obtain ⟨pts, segs, err⟩ := y
  dsimp only at hyl1 hyl2 hypw hysb hyr
  rcases hyr with ⟨rfl, hF⟩ | ⟨hsome, m, hm⟩
  · rw [hF]
    simp only [except_bind_ok]
    obtain ⟨z, hz, hzr⟩ := hop_cps_loop1 fv pts segs hypw hysb (by omega) _ rfl
    have hsz : (hop_segsV segs).size = segs.val.length := by simp [hop_segsV]
    simp only [hsz]
    have hl1 : beatmap.hit_object_parser.convert_path_string_loop1 fv pts segs none (alloc.vec.Vec.new _) 0#usize = ok z := hz
    show ∃ r, (do
        let (err1, control_points) ← beatmap.hit_object_parser.convert_path_string_loop1 fv pts segs none
          (alloc.vec.Vec.new beatmap.types.PathControlPoint) 0#usize
        match err1 with
        | none => ok (core.result.Result.Ok control_points)
        | some e => ok (core.result.Result.Err e)) = ok r ∧ _
    rw [hl1, bind_ok]
    obtain ⟨err1, cpts⟩ := z
    dsimp only at hzr ⊢
    rcases hzr with ⟨rfl, hF1⟩ | ⟨hsome1, m1, hm1⟩
    · exact ⟨.Ok cpts, rfl, by rw [hF1]; rfl⟩
    · obtain ⟨e1, rfl⟩ := Option.isSome_iff_exists.mp hsome1
      exact ⟨.Err e1, rfl, by rw [hm1]; trivial⟩
  · obtain ⟨e, rfl⟩ := Option.isSome_iff_exists.mp hsome
    rw [hm]
    exact ⟨.Err e, rfl, trivial⟩

end OsuProofs
