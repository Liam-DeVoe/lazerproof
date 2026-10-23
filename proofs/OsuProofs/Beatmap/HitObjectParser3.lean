/-
`beatmap::hit_object_parser` part 3: `ps_node_banks` (+ its loop, in lockstep with the spec's `Except` `for` loop),
`parse_hold_end` (the hold branch of `Parse`; the `":".intercalate` rebuild loop is related to
`List.intercalate [':']` and bounded by the original piece length), `pre_parse` (the `pre` block of `Parse`).
Helper names are prefixed `hop_`.
-/
import OsuProofs.Beatmap.HitObjectParser2
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

def hop_nbF (sets : _root_.Array String) (i : Nat) (_ : PUnit) : DecodeM (ForInStep PUnit) :=
  if i < sets.size then do
    ConvertHitObjectParser.readCustomSampleBanks sets[i]!
    pure (ForInStep.yield PUnit.unit)
  else pure (ForInStep.yield PUnit.unit)

def hop_nbRel : Option beatmap.hit_object_parser.DecodeError → Except String PUnit → Prop
  | none, .ok _ => True
  | some _, .error _ => True
  | _, _ => False

theorem hop_nb_loop (sets : Slice (alloc.vec.Vec U32)) (hV : ∀ l ∈ sets.val, ValidL l.val)
    (hL : ∀ l ∈ sets.val, l.val.length < Usize.max) (nodes : Usize) :
    ∀ k (i : Usize), i.val + k = nodes.val →
      ∃ r, beatmap.hit_object_parser.ps_node_banks_loop_loop sets nodes none i = ok r ∧
        hop_nbRel r (forIn (List.range' i.val k) PUnit.unit (hop_nbF (vstrs sets.val))) := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have hn : ¬ i < nodes := by show ¬ i.val < nodes.val; omega
    refine ⟨none, ?_, by simp [hop_nbRel]⟩
    unfold beatmap.hit_object_parser.ps_node_banks_loop_loop
    rw [loop_unfold]
    simp [beatmap.hit_object_parser.ps_node_banks_loop_loop.body, hn]
  | succ k ih =>
    intro i hi
    have hn : i < nodes := by show i.val < nodes.val; omega
    have hmx : nodes.val ≤ Usize.max := by scalar_tac
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
    obtain ⟨r, hr, hrr⟩ := ih i1 (by omega)
    rw [List.range'_succ, List.forIn_cons]
    by_cases hs : i.val < sets.val.length
    · have hs' : i < Slice.len sets := by show i.val < (Slice.len sets).val; simpa using hs
      have hm := List.getElem_mem hs
      obtain ⟨q, hq, hqr⟩ := beatmap.hit_object_parser.read_custom_sample_banks_refines _ (validStr_of _ (hV _ hm))
        (by simp; exact hL _ hm) false
      rw [strV_deref] at hqr
      have hF : hop_nbF (vstrs sets.val) i.val PUnit.unit =
          (do ConvertHitObjectParser.readCustomSampleBanks (strV (sets.val[i.val]'hs)) false
              pure (ForInStep.yield PUnit.unit)) := by
        rw [hop_nbF, if_pos (by rw [vstrs_size]; exact hs), vstrs_get! _ _ hs]
      rw [hF]
      cases q with
      | Ok u =>
        cases hx : ConvertHitObjectParser.readCustomSampleBanks (strV (sets.val[i.val]'hs)) false with
        | error e => rw [hx] at hqr; simp [hRel] at hqr
        | ok v =>
          have hb : beatmap.hit_object_parser.ps_node_banks_loop_loop.body sets nodes none i = ok (.cont (none, i1)) := by
            simp [beatmap.hit_object_parser.ps_node_banks_loop_loop.body, hn, hs', index_eq sets i hs, hq, hi1]
          refine ⟨r, ?_, ?_⟩
          · unfold beatmap.hit_object_parser.ps_node_banks_loop_loop
            rw [loop_unfold]; simp only [hb, bind_ok]
            unfold beatmap.hit_object_parser.ps_node_banks_loop_loop at hr
            simpa using hr
          · rw [hi1v] at hrr; exact hrr
      | Err e =>
        cases hx : ConvertHitObjectParser.readCustomSampleBanks (strV (sets.val[i.val]'hs)) false with
        | ok v => rw [hx] at hqr; simp [hRel] at hqr
        | error e' =>
          refine ⟨some e, ?_, by exact trivial⟩
          have hb : beatmap.hit_object_parser.ps_node_banks_loop_loop.body sets nodes none i = ok (.cont (some e, i1)) := by
            simp [beatmap.hit_object_parser.ps_node_banks_loop_loop.body, hn, hs', index_eq sets i hs, hq, hi1]
          have hb2 : beatmap.hit_object_parser.ps_node_banks_loop_loop.body sets nodes (some e) i1 = ok (.done (some e)) := by
            simp [beatmap.hit_object_parser.ps_node_banks_loop_loop.body]
          unfold beatmap.hit_object_parser.ps_node_banks_loop_loop
          rw [loop_unfold]; simp only [hb, bind_ok]
          rw [loop_unfold]; simp only [hb2, bind_ok]
    · have hs' : ¬ i < Slice.len sets := by show ¬ i.val < (Slice.len sets).val; simpa using hs
      have hF : hop_nbF (vstrs sets.val) i.val PUnit.unit = pure (ForInStep.yield PUnit.unit) := by
        simp [hop_nbF, vstrs_size, hs]
      rw [hF]
      have hb : beatmap.hit_object_parser.ps_node_banks_loop_loop.body sets nodes none i = ok (.cont (none, i1)) := by
        simp [beatmap.hit_object_parser.ps_node_banks_loop_loop.body, hn, hs', hi1]
      refine ⟨r, ?_, ?_⟩
      · unfold beatmap.hit_object_parser.ps_node_banks_loop_loop
        rw [loop_unfold]; simp only [hb, bind_ok]
        unfold beatmap.hit_object_parser.ps_node_banks_loop_loop at hr
        simpa using hr
      · rw [hi1v] at hrr; exact hrr

theorem beatmap.hit_object_parser.ps_node_banks_loop_refines (sets : Slice (alloc.vec.Vec U32))
    (hV : ∀ l ∈ sets.val, ValidL l.val) (hL : ∀ l ∈ sets.val, l.val.length < Usize.max) (nodes : Usize) :
    ∃ r, beatmap.hit_object_parser.ps_node_banks_loop sets nodes = ok r ∧
      hRel id r (do
        for i in [0:nodes.val] do
          if i < (vstrs sets.val).size then ConvertHitObjectParser.readCustomSampleBanks (vstrs sets.val)[i]!
        : DecodeM Unit) := by
  obtain ⟨r, hr, hrr⟩ := hop_nb_loop sets hV hL nodes nodes.val 0#usize (by simp)
  unfold beatmap.hit_object_parser.ps_node_banks_loop
  rw [hr, bind_ok]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  have hz : (0#usize : Usize).val = 0 := rfl
  rw [hz] at hrr
  have hF : (fun i (__s : PUnit) => if i < (vstrs sets.val).size then do
            ConvertHitObjectParser.readCustomSampleBanks (vstrs sets.val)[i]!
            pure (ForInStep.yield PUnit.unit)
          else (pure (ForInStep.yield PUnit.unit) : DecodeM (ForInStep PUnit))) = hop_nbF (vstrs sets.val) := rfl
  rw [hF]
  cases r with
  | none =>
    cases hx : forIn (List.range' 0 nodes.val) PUnit.unit (hop_nbF (vstrs sets.val)) with
    | ok u => exact ⟨_, rfl, rfl⟩
    | error e => rw [hx] at hrr; simp [hop_nbRel] at hrr
  | some e =>
    cases hx : forIn (List.range' 0 nodes.val) PUnit.unit (hop_nbF (vstrs sets.val)) with
    | ok u => rw [hx] at hrr; simp [hop_nbRel] at hrr
    | error e' => exact ⟨_, rfl, trivial⟩

theorem hop_nb_pipe : chOf 124#u32 = '|' := by decide

theorem beatmap.hit_object_parser.ps_node_banks_refines (sp : Slice (alloc.vec.Vec U32))
    (hV : ∀ l ∈ sp.val, ValidL l.val) (hL : ∀ l ∈ sp.val, l.val.length < Usize.max) (nodes : Usize) :
    ∃ r, beatmap.hit_object_parser.ps_node_banks sp nodes = ok r ∧
      hRel id r (if (vstrs sp.val).size > 9 && (vstrs sp.val)[9]!.length > 0 then (do
        let sets := split (vstrs sp.val)[9]! '|'
        for i in [0:nodes.val] do
          if i < sets.size then ConvertHitObjectParser.readCustomSampleBanks sets[i]!
        : DecodeM Unit) else pure ()) := by
  unfold beatmap.hit_object_parser.ps_node_banks
  rw [vstrs_size]
  by_cases h : sp.val.length > 9
  · have h' : Slice.len sp > 9#usize := by show (9#usize : Usize).val < (Slice.len sp).val; simpa using h
    have hm := List.getElem_mem h
    have hidx : Slice.index_usize sp 9#usize = ok (sp.val[9]'h) := index_eq sp 9#usize (by simpa using h)
    have hlen : (vstrs sp.val)[9]!.length = (sp.val[9]'h).val.length := by
      rw [vstrs_get! _ 9 h]; simp [strV]
    rw [hlen]
    by_cases h0 : (sp.val[9]'h).val.length > 0
    · have h0' : alloc.vec.Vec.len (sp.val[9]'h) > 0#usize := by
        show (0#usize : Usize).val < (alloc.vec.Vec.len (sp.val[9]'h)).val; simpa using h0
      obtain ⟨v1, hv1, hv1s, hv1V, hv1L⟩ := split_rel (alloc.vec.Vec.deref (sp.val[9]'h)) (validStr_of _ (hV _ hm))
        (by simp; exact hL _ hm) 124#u32 (by decide)
      rw [hop_nb_pipe, strV_deref] at hv1s
      obtain ⟨r, hr, hrr⟩ := beatmap.hit_object_parser.ps_node_banks_loop_refines (alloc.vec.Vec.deref v1)
        (by intro l hl; rw [deref_valA] at hl; exact hv1V l hl)
        (by intro l hl; rw [deref_valA] at hl; have := hv1L l hl; have := hL _ hm; simp at *; omega) nodes
      refine ⟨r, ?_, ?_⟩
      · simp only [h', if_true, hidx, bind_ok, h0', hv1, hr]
      · rw [deref_valA, hv1s] at hrr
        rw [vstrs_get! _ 9 h]
        simpa [h, h0] using hrr
    · have h0' : ¬ alloc.vec.Vec.len (sp.val[9]'h) > 0#usize := by
        show ¬ (0#usize : Usize).val < (alloc.vec.Vec.len (sp.val[9]'h)).val; simpa using h0
      refine ⟨core.result.Result.Ok (), by simp only [h', ite_true, hidx, bind_ok, h0', ite_false], ?_⟩
      simp [h0]; rfl
  · have h' : ¬ Slice.len sp > 9#usize := by show ¬ (9#usize : Usize).val < (Slice.len sp).val; simpa using h
    refine ⟨core.result.Result.Ok (), by simp only [h', ite_false], ?_⟩
    simp [h]; rfl

theorem hop_icl_snoc {α} (x : α) (L : List (List α)) (y : List α) :
    [x].intercalate (L ++ [y]) = (if L = [] then y else [x].intercalate L ++ x :: y) := by
  induction L with
  | nil => simp [List.intercalate_singleton]
  | cons a t ih =>
    cases t with
    | nil => simp [List.intercalate_cons_cons, List.intercalate_singleton]
    | cons b t' =>
      simp only [List.cons_append, List.intercalate_cons_cons] at ih ⊢
      simp only [reduceCtorEq, if_false] at ih ⊢
      rw [ih]; simp

theorem hop_icl_len_cons {α} (x : α) (a : List α) (t : List (List α)) (h : t ≠ []) :
    ([x].intercalate (a :: t)).length = a.length + 1 + ([x].intercalate t).length := by
  rw [List.intercalate_cons_of_ne_nil h]; simp; omega

theorem hop_icl_take_le {α} (x : α) : ∀ (L : List (List α)) (n : Nat),
    ([x].intercalate (L.take n)).length ≤ ([x].intercalate L).length
  | [], n => by simp
  | a :: t, 0 => by simp
  | a :: t, n+1 => by
    rw [List.take_succ_cons]
    by_cases ht : t = []
    · subst ht; simp
    · rw [hop_icl_len_cons x a t ht]
      by_cases ht' : t.take n = []
      · rw [ht']; simp [List.intercalate_singleton]; omega
      · rw [hop_icl_len_cons x a _ ht']
        have := hop_icl_take_le x t n
        omega

theorem hop_icl_drop1_le {α} (x : α) (L : List (List α)) :
    ([x].intercalate (L.drop 1)).length ≤ ([x].intercalate L).length := by
  cases L with
  | nil => simp
  | cons a t =>
    simp only [List.drop_succ_cons, List.drop_zero]
    by_cases ht : t = []
    · subst ht; simp
    · rw [hop_icl_len_cons x a t ht]; omega

theorem hop_icl_map {α β} (f : α → β) (x : α) : ∀ (L : List (List α)),
    ([x].intercalate L).map f = [f x].intercalate (L.map (List.map f))
  | [] => by simp
  | [a] => by simp [List.intercalate_singleton]
  | a :: b :: t => by
    rw [List.intercalate_cons_cons, List.map_cons, List.map_cons, List.intercalate_cons_cons]
    have := hop_icl_map f x (b :: t)
    simp only [List.map_cons] at this
    simp [this]

theorem hop_he_inner (ss : alloc.vec.Vec (alloc.vec.Vec U32)) (k : Usize) (hk : k.val < ss.val.length) :
    ∀ j (rest : alloc.vec.Vec U32) (m : Usize), m.val + j = (ss.val[k.val]'hk).val.length →
      rest.val.length + j ≤ Usize.max →
      ∃ r', beatmap.hit_object_parser.parse_hold_end_loop0_loop0 ss rest k m = ok r' ∧
        r'.val = rest.val ++ (ss.val[k.val]'hk).val.drop m.val := by
  intro j
  induction j with
  | zero =>
    intro rest m hm hb
    have hn : ¬ m < alloc.vec.Vec.len (ss.val[k.val]'hk) := by
      show ¬ m.val < (alloc.vec.Vec.len (ss.val[k.val]'hk)).val; simp; omega
    have hb0 : beatmap.hit_object_parser.parse_hold_end_loop0_loop0.body ss k rest m = ok (.done rest) := by
      have hn' : ¬ m.val < (ss.val[k.val]'hk).val.length := by omega
      simp [beatmap.hit_object_parser.parse_hold_end_loop0_loop0.body, vec_index_eq' ss k hk, hn']
    refine ⟨rest, ?_, by simp [List.drop_eq_nil_of_le (by omega : (ss.val[k.val]'hk).val.length ≤ m.val)]⟩
    unfold beatmap.hit_object_parser.parse_hold_end_loop0_loop0
    rw [loop_unfold]; simp only [hb0, bind_ok]
  | succ j ih =>
    intro rest m hm hb
    have hml : m.val < (ss.val[k.val]'hk).val.length := by omega
    have hn : m < alloc.vec.Vec.len (ss.val[k.val]'hk) := by
      show m.val < (alloc.vec.Vec.len (ss.val[k.val]'hk)).val; simpa using hml
    obtain ⟨m1, hm1, hm1v⟩ := usize_add_one m (by have := (ss.val[k.val]'hk).property; scalar_tac)
    have hp := vec_push_ok rest ((ss.val[k.val]'hk).val[m.val]'hml) (by omega)
    have hpv := vpush_val rest ((ss.val[k.val]'hk).val[m.val]'hml) (by omega)
    generalize vpush rest _ _ = rest1 at hp hpv
    obtain ⟨r', hr', hr'v⟩ := ih rest1 m1 (by omega) (by rw [hpv]; simp; omega)
    have hb0 : beatmap.hit_object_parser.parse_hold_end_loop0_loop0.body ss k rest m = ok (.cont (rest1, m1)) := by
      simp [beatmap.hit_object_parser.parse_hold_end_loop0_loop0.body, vec_index_eq' ss k hk, hml,
        vec_index_eq' _ m hml, vec_index_usize_eq _ m hml, hp, hm1]
    refine ⟨r', ?_, ?_⟩
    · unfold beatmap.hit_object_parser.parse_hold_end_loop0_loop0
      rw [loop_unfold]; simp only [hb0, bind_ok]
      unfold beatmap.hit_object_parser.parse_hold_end_loop0_loop0 at hr'
      simpa using hr'
    · rw [hr'v, hpv, hm1v, List.drop_eq_getElem_cons hml]; simp

theorem hop_he_outer (ss : alloc.vec.Vec (alloc.vec.Vec U32))
    (hF : ([58#u32].intercalate ((ss.val.map (·.val)).drop 1)).length ≤ Usize.max) :
    ∀ j (rest : alloc.vec.Vec U32) (k : Usize), k.val + j = ss.val.length → 1 ≤ k.val →
      rest.val = [58#u32].intercalate (((ss.val.map (·.val)).drop 1).take (k.val - 1)) →
      ∃ r', beatmap.hit_object_parser.parse_hold_end_loop0 ss rest k = ok r' ∧
        r'.val = [58#u32].intercalate ((ss.val.map (·.val)).drop 1) := by
  intro j
  induction j with
  | zero =>
    intro rest k hk h1 hr
    have hn : ¬ k < alloc.vec.Vec.len ss := by show ¬ k.val < (alloc.vec.Vec.len ss).val; simp; omega
    have hb0 : beatmap.hit_object_parser.parse_hold_end_loop0.body ss rest k = ok (.done rest) := by
      have hn' : ¬ k.val < ss.val.length := by omega
      simp [beatmap.hit_object_parser.parse_hold_end_loop0.body, hn']
    refine ⟨rest, ?_, ?_⟩
    · unfold beatmap.hit_object_parser.parse_hold_end_loop0
      rw [loop_unfold]; simp only [hb0, bind_ok]
    · rw [hr, List.take_of_length_le (by simp; omega)]
  | succ j ih =>
    intro rest k hk h1 hr
    have hkl : k.val < ss.val.length := by omega
    have hn : k < alloc.vec.Vec.len ss := by show k.val < (alloc.vec.Vec.len ss).val; simpa using hkl
    set P := ss.val.map (·.val) with hP
    have hPk : (P.drop 1)[k.val - 1]? = some (ss.val[k.val]'hkl).val := by
      simp [hP, List.getElem?_drop, show 1 + (k.val - 1) = k.val by omega, Nat.sub_add_cancel h1, List.getElem?_eq_getElem hkl]
    have htk : (P.drop 1).take k.val = (P.drop 1).take (k.val - 1) ++ [(ss.val[k.val]'hkl).val] := by
      have : k.val = (k.val - 1) + 1 := by omega
      conv_lhs => rw [this]
      rw [List.take_add_one, hPk]; rfl
    have hnew : [58#u32].intercalate ((P.drop 1).take k.val) =
        rest.val ++ (if 1 < k.val then [58#u32] else []) ++ (ss.val[k.val]'hkl).val := by
      rw [htk, hop_icl_snoc, ← hr]
      by_cases hk1 : k.val = 1
      · have : (P.drop 1).take (k.val - 1) = [] := by rw [hk1]; simp
        rw [if_pos this, hr, this]; simp [hk1]
      · have : (P.drop 1).take (k.val - 1) ≠ [] := by
          intro h; have := congrArg List.length h; simp [hP] at this; omega
        rw [if_neg this, if_pos (by omega)]; simp
    have hle : ([58#u32].intercalate ((P.drop 1).take k.val)).length ≤ Usize.max :=
      le_trans (hop_icl_take_le _ _ _) hF
    rw [hnew] at hle
    simp only [List.length_append] at hle
    obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := ss.property; omega)
    -- the separator push
    obtain ⟨rest1, hr1, hr1v⟩ : ∃ rest1 : alloc.vec.Vec U32,
        (if k > 1#usize then alloc.vec.Vec.push rest 58#u32 else ok rest) = ok rest1 ∧
        rest1.val = rest.val ++ (if 1 < k.val then [58#u32] else []) := by
      by_cases hk1 : 1 < k.val
      · have hg : k > 1#usize := by show (1#usize : Usize).val < k.val; simpa using hk1
        have hlt : rest.val.length < Usize.max := by simp [hk1] at hle; omega
        exact ⟨_, by rw [if_pos hg]; exact vec_push_ok rest 58#u32 hlt, by simp [hk1]⟩
      · have hg : ¬ k > 1#usize := by show ¬ (1#usize : Usize).val < k.val; simpa using hk1
        exact ⟨rest, by rw [if_neg hg], by simp [hk1]⟩
    obtain ⟨rest2, hr2, hr2v⟩ := hop_he_inner ss k hkl (ss.val[k.val]'hkl).val.length rest1 0#usize (by simp)
      (by rw [hr1v]; simp only [List.length_append] at hle ⊢; omega)
    obtain ⟨r', hr', hr'v⟩ := ih rest2 k1 (by omega) (by omega)
      (by rw [hr2v, hr1v, hk1v]; simp only [Nat.add_sub_cancel]; rw [hnew]; simp)
    have hb0 : beatmap.hit_object_parser.parse_hold_end_loop0.body ss rest k = ok (.cont (rest2, k1)) := by
      simp only [beatmap.hit_object_parser.parse_hold_end_loop0.body, hn, if_true, hr1, bind_ok, hr2, hk1]
    refine ⟨r', ?_, hr'v⟩
    unfold beatmap.hit_object_parser.parse_hold_end_loop0
    rw [loop_unfold]; simp only [hb0, bind_ok]
    unfold beatmap.hit_object_parser.parse_hold_end_loop0 at hr'
    simpa using hr'

theorem hop_icl_mem {α} (x : α) : ∀ (L : List (List α)) (u : α), u ∈ [x].intercalate L → u = x ∨ ∃ l ∈ L, u ∈ l
  | [], u, h => by simp at h
  | [a], u, h => by simp [List.intercalate_singleton] at h; exact .inr ⟨a, by simp, h⟩
  | a :: b :: t, u, h => by
    rw [List.intercalate_cons_cons] at h
    simp only [List.mem_append, List.mem_singleton] at h
    rcases h with (h | h) | h
    · exact .inr ⟨a, by simp, h⟩
    · exact .inl h
    · rcases hop_icl_mem x (b :: t) u h with h | ⟨l, hl, hu⟩
      · exact .inl h
      · exact .inr ⟨l, List.mem_cons_of_mem _ hl, hu⟩

theorem hop_he_join (ss : alloc.vec.Vec (alloc.vec.Vec U32)) (S5 : String) (hss : vstrs ss.val = split S5 ':') :
    ([58#u32].intercalate ((ss.val.map (·.val)).drop 1)).length ≤ S5.length ∧
    String.ofList (([58#u32].intercalate ((ss.val.map (·.val)).drop 1)).map chOf) =
      ":".intercalate ((vstrs ss.val).toList.drop 1) := by
  have hc : chOf 58#u32 = ':' := by decide
  have hP : (ss.val.map (·.val)).map (List.map chOf) = (vstrs ss.val).toList.map String.toList := by
    simp [vstrs, strV, Function.comp_def]
  have hS : (vstrs ss.val).toList.map String.toList = S5.toList.splitOn ':' := by
    rw [hss]
    have := splitOn_char S5.toList ':'
    rw [String.ofList_toList] at this
    simp only [split, List.toList_toArray]
    rw [this, List.map_map]
    simp [Function.comp_def]
  constructor
  · rw [← List.length_map (f := chOf), hop_icl_map, hc, List.map_drop, hP, hS]
    refine le_trans (hop_icl_drop1_le _ _) ?_
    rw [List.intercalate_splitOn]
    first | exact le_of_eq String.length_toList | exact le_of_eq (String.length_toList _) | simp [String.length]
  · rw [hop_icl_map, hc, List.map_drop, hP]
    apply String.toList_injective
    rw [String.toList_ofList, String.toList_intercalate]
    simp [List.map_drop]

theorem hop_he_max (a b : F64) : net.max a b = ok (F64.max a b) := by
  unfold net.max F64.max
  by_cases h : (a == b) = true
  · have := beq_not_nan_right h
    simp [h, f64_is_negative_eq b this]
  · simp only [Bool.not_eq_true] at h
    simp [h]
    split <;> simp_all

/-- The hold branch of `ConvertHitObjectParser.parse` (end time), verbatim. -/
def hop_holdS (S : _root_.Array String) (startTime : F64) : DecodeM F64 := do
  let mut endTime := F64.max startTime (← liftNet "hold end" (Parsing.parseDouble (← at! S 2)))
  if S.size > 5 && !S[5]!.isEmpty then
    let ss := split S[5]! ':'
    endTime := F64.max startTime (← liftNet "hold end" (Parsing.parseDouble ss[0]!))
    ConvertHitObjectParser.readCustomSampleBanks (":".intercalate (ss.toList.drop 1))
  return endTime

theorem beatmap.hit_object_parser.parse_hold_end_refines (pre : beatmap.hit_object_parser.PreParse)
    (hV : ∀ l ∈ pre.split.val, ValidL l.val) (hL : ∀ l ∈ pre.split.val, l.val.length < 2^62)
    (hLm : ∀ l ∈ pre.split.val, l.val.length < Usize.max) :
    ∃ r, beatmap.hit_object_parser.parse_hold_end pre = ok r ∧
      hRel id r (hop_holdS (vstrs pre.split.val) pre.start_time) := by
  unfold beatmap.hit_object_parser.parse_hold_end hop_holdS
  obtain ⟨r0, h0, h0r, h0m⟩ := beatmap.hit_object_parser.at_refines (alloc.vec.Vec.deref pre.split) 2#usize
  rw [deref_valA] at h0r h0m
  simp only [h0, bind_ok]
  cases r0 with
  | Err e =>
    cases hx : at! (vstrs pre.split.val) (2#usize : Usize).val with
    | ok v => rw [hx] at h0r; simp [hRel] at h0r
    | error e' =>
      have h2 : (2#usize : Usize).val = 2 := rfl
      rw [h2] at hx
      simp only [hx]
      exact ⟨_, rfl, trivial⟩
  | Ok v =>
    have hvm := h0m v rfl
    cases hx : at! (vstrs pre.split.val) (2#usize : Usize).val with
    | error e' => rw [hx] at h0r; simp [hRel] at h0r
    | ok sv =>
      rw [hx] at h0r; simp only [hRel, id] at h0r; subst h0r
      have h2 : (2#usize : Usize).val = 2 := rfl
      rw [h2] at hx
      simp only [hx, except_bind_ok]
      rw [net.parse.parse_double_default_refines _ (validStr_of v (hV v hvm)) (by simp; exact hL v hvm), bind_ok,
        strV_deref]
      obtain ⟨r2, h2r, h2v⟩ := lift_net_exceptI beatmap.errors.W_HOLD_END id id (fun _ => rfl)
        (Parsing.parseDouble (strV v)) "hold end"
      rw [h2r, bind_ok]
      cases r2 with
      | Err a =>
        cases hy : liftNet "hold end" (Parsing.parseDouble (strV v)) with
        | ok y => rw [hy] at h2v; simp [hRel] at h2v
        | error e' => simp only [hy]; exact ⟨_, rfl, trivial⟩
      | Ok x =>
        cases hy : liftNet "hold end" (Parsing.parseDouble (strV v)) with
        | error e' => rw [hy] at h2v; simp [hRel] at h2v
        | ok y =>
        rw [hy] at h2v; simp only [hRel, id] at h2v; subst h2v
        simp only [except_bind_ok, hop_he_max, bind_ok, vstrs_size]
        by_cases h5 : pre.split.val.length > 5
        · have h5' : alloc.vec.Vec.len pre.split > 5#usize := by
            show (5#usize : Usize).val < (alloc.vec.Vec.len pre.split).val; simpa using h5
          have hm5 := List.getElem_mem h5
          have hidx5 : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (alloc.vec.Vec U32)) pre.split 5#usize =
              ok (pre.split.val[5]'h5) := vec_index_eq' pre.split 5#usize h5
          have hE : (strV (pre.split.val[5]'h5)).isEmpty = decide ((pre.split.val[5]'h5).val.length = 0) := by
            unfold strV; cases h : (pre.split.val[5]'h5).val <;> simp [h, String.isEmpty_iff]
          simp only [h5', ite_true, h5, decide_true, Bool.true_and, hidx5, bind_ok,
            vstrs_get! _ 5 h5, hE]
          by_cases h50 : (pre.split.val[5]'h5).val.length = 0
          · have h50' : ¬ ((alloc.vec.Vec.len (pre.split.val[5]'h5) != 0#usize) = true) := by
              simp only [bne_iff_ne, ne_eq, Decidable.not_not]
              apply UScalar.eq_of_val_eq; simpa using h50
            simp only [h50', ite_false, h50, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact ⟨_, rfl, rfl⟩
          · have h50' : (alloc.vec.Vec.len (pre.split.val[5]'h5) != 0#usize) = true := by
              simp only [bne_iff_ne, ne_eq]
              intro hc; apply h50; have := congrArg UScalar.val hc; simpa using this
            simp only [h50', ite_true, h50, decide_false, Bool.not_false, ↓reduceIte]
            set v5 := pre.split.val[5]'h5 with hv5
            obtain ⟨ss, hs1, hss, hssV, hssL⟩ := split_rel (alloc.vec.Vec.deref v5) (validStr_of _ (hV _ hm5))
              (by simp; exact hLm _ hm5) 58#u32 (by decide)
            rw [colon_lit, strV_deref] at hss
            have hss0 : 0 < ss.val.length := by
              have := congrArg _root_.Array.size hss
              rw [vstrs_size] at this
              rw [this]
              simp only [split, List.size_toArray, strV]
              rw [splitOn_char]; simp only [List.length_map]
              have := List.splitOn_ne_nil ':' (v5.val.map chOf)
              cases h : List.splitOn ':' (v5.val.map chOf) with
              | nil => exact absurd h this
              | cons _ _ => simp
            have hm0 := List.getElem_mem hss0
            have hidx0 : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (alloc.vec.Vec U32)) ss 0#usize =
                ok (ss.val[0]'hss0) := vec_index_eq' ss 0#usize hss0
            simp only [hs1, bind_ok, hidx0, ← hss, vstrs_get! _ 0 hss0]
            have hl0 : (ss.val[0]'hss0).val.length < 2^62 := by
              have := hssL _ hm0; have := hL _ hm5; simp at *; omega
            rw [net.parse.parse_double_default_refines _ (validStr_of _ (hssV _ hm0)) (by simpa using hl0), bind_ok,
              strV_deref]
            obtain ⟨r4, h4r, h4v⟩ := lift_net_exceptI beatmap.errors.W_HOLD_END id id (fun _ => rfl)
              (Parsing.parseDouble (strV (ss.val[0]'hss0))) "hold end"
            rw [h4r, bind_ok]
            cases r4 with
            | Err a =>
              cases hz : liftNet "hold end" (Parsing.parseDouble (strV (ss.val[0]'hss0))) with
              | ok z => rw [hz] at h4v; simp [hRel] at h4v
              | error e' => simp only [hz]; exact ⟨_, rfl, trivial⟩
            | Ok x4 =>
              cases hz : liftNet "hold end" (Parsing.parseDouble (strV (ss.val[0]'hss0))) with
              | error e' => rw [hz] at h4v; simp [hRel] at h4v
              | ok z =>
              rw [hz] at h4v; simp only [hRel, id] at h4v; subst h4v
              simp only [except_bind_ok, hop_he_max, bind_ok]
              obtain ⟨hJl, hJs⟩ := hop_he_join ss (strV v5) hss
              have hv5l : (strV v5).length = v5.val.length := by simp [strV]
              have hF : ([58#u32].intercalate ((ss.val.map (·.val)).drop 1)).length < Usize.max := by
                have := hLm _ hm5; omega
              obtain ⟨rest, hrs, hrv⟩ := hop_he_outer ss (le_of_lt hF) (ss.val.length - 1) (alloc.vec.Vec.new U32) 1#usize
                (by simp; omega) (by simp) (by simp)
              rw [hrs, bind_ok]
              have hrV : ValidStr (alloc.vec.Vec.deref rest) := by
                intro u hu
                rw [deref_valA, hrv] at hu
                rcases hop_icl_mem _ _ u hu with h | ⟨l, hl, hul⟩
                · subst h; decide
                · have hl' := List.mem_of_mem_drop hl
                  simp only [List.mem_map] at hl'
                  obtain ⟨w, hw, rfl⟩ := hl'
                  exact hssV w hw u hul
              obtain ⟨q, hq, hqr⟩ := beatmap.hit_object_parser.read_custom_sample_banks_refines _ hrV
                (by rw [deref_valA, hrv]; exact hF) false
              rw [strV_deref] at hqr
              have hstr : strV rest = ":".intercalate ((vstrs ss.val).toList.drop 1) := by
                rw [← hJs]; simp [strV, hrv]
              rw [hstr] at hqr
              rw [hq, bind_ok]
              cases q with
              | Ok u =>
                cases hw : ConvertHitObjectParser.readCustomSampleBanks
                    (":".intercalate (List.drop 1 (vstrs ss.val).toList)) false with
                | error e' => rw [hw] at hqr; simp [hRel] at hqr
                | ok w => simp only [hw]; exact ⟨_, rfl, rfl⟩
              | Err e =>
                cases hw : ConvertHitObjectParser.readCustomSampleBanks
                    (":".intercalate (List.drop 1 (vstrs ss.val).toList)) false with
                | ok w => rw [hw] at hqr; simp [hRel] at hqr
                | error e' => simp only [hw]; exact ⟨_, rfl, trivial⟩
        · have h5' : ¬ alloc.vec.Vec.len pre.split > 5#usize := by
            show ¬ (5#usize : Usize).val < (alloc.vec.Vec.len pre.split).val; simpa using h5
          simp only [h5', ite_false, h5, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          exact ⟨_, rfl, rfl⟩

macro "hop_rstep " r:term:max h:term:max v:ident : tactic =>
  `(tactic| (rcases $r:term with $v:ident | e; (on_goal 2 => exact ⟨_, rfl, rel_err $h _ _⟩); rw [rel_ok $h, except_bind_ok]))

/-- `bind_rel` whose continuation may use the fact that `r = .Ok a`. -/
theorem hop_bind_rel' {α α' β β'} (r : core.result.Result α beatmap.hit_object_parser.DecodeError) (x : Except String α')
    (f : α → α') (h : hRel f r x)
    (kR : α → Result (core.result.Result β beatmap.hit_object_parser.DecodeError)) (kS : α' → Except String β')
    (g : β → β') (hk : ∀ a, r = .Ok a → ∃ r', kR a = ok r' ∧ hRel g r' (kS (f a))) :
    ∃ r', (match r with | .Ok a => kR a | .Err e => ok (.Err e)) = ok r' ∧ hRel g r' (x >>= kS) := by
  cases r with
  | Ok a =>
    cases x with
    | ok b => simp only [hRel] at h; subst h; obtain ⟨r', h1, h2⟩ := hk a rfl; exact ⟨r', h1, h2⟩
    | error e => simp [hRel] at h
  | Err e =>
    cases x with
    | ok b => simp [hRel] at h
    | error e' => exact ⟨.Err e, rfl, trivial⟩

theorem hop_i32S_and (a b : I32) : i32S (a &&& b) = i32S a &&& i32S b := by unfold i32S; simp
theorem hop_i32S_not (a : I32) : i32S (~~~ a) = ~~~ i32S a := by unfold i32S; simp
theorem hop_i32S_shr4 (a : I32) : ∃ c, a >>> 4#i32 = ok c ∧ i32S c = i32S a >>> 4 := by
  refine ⟨⟨a.bv.sshiftRight 4⟩, ?_, ?_⟩
  · show IScalar.shiftRight_IScalar a 4#i32 = _
    simp [IScalar.shiftRight_IScalar, IScalar.shiftRight]
  · unfold i32S
    apply Int32.toBitVec_inj.mp
    simp [Int32.toBitVec_shiftRight]

def hop_preS (p : beatmap.hit_object_parser.PreParse) : Vec2 × F64 × Int32 × Bool × Int32 × _root_.Array String :=
  (bv2S p.pos, p.start_time, i32S p.combo_offset, p.combo, i32S p.otype, vstrs p.split.val)

/-- The `pre` block of `ConvertHitObjectParser.parse`, verbatim. -/
def hop_preSpec (st : ParserState) (text : String) : DecodeM (Vec2 × F64 × Int32 × Bool × Int32 × _root_.Array String) := do
    let split := OsuModel.Beatmap.split text ','
    let pos : Vec2 := ⟨← ConvertHitObjectParser.parseCoord st.formatVersion (← at! split 0),
      ← ConvertHitObjectParser.parseCoord st.formatVersion (← at! split 1)⟩
    let startTime := (← liftNet "startTime" (Parsing.parseDouble (← at! split 2))) + st.offset
    let type0 ← liftNet "type" (Parsing.parseInt (← at! split 3))
    let comboOffset : Int32 := (type0 &&& ConvertHitObjectParser.COMBO_OFFSET) >>> 4
    let type1 := type0 &&& ~~~ConvertHitObjectParser.COMBO_OFFSET
    let combo := type1 &&& ConvertHitObjectParser.NEW_COMBO != 0
    let type := type1 &&& ~~~ConvertHitObjectParser.NEW_COMBO
    let _soundType ← liftNet "soundType" (Parsing.parseInt (← at! split 4))
    return (pos, startTime, comboOffset, combo, type, split)

theorem beatmap.hit_object_parser.pre_parse_refines (st : beatmap.hit_object_parser.ParserState) (text : Slice U32)
    (hs : ValidStr text) (hn : text.val.length < 2^62) (hn2 : text.val.length < Usize.max) :
    ∃ r, beatmap.hit_object_parser.pre_parse st text = ok r ∧
      hRel hop_preS r (hop_preSpec (psS st) (String.ofList (strS text))) := by
  unfold beatmap.hit_object_parser.pre_parse hop_preSpec
  obtain ⟨sp, hsp, hspv, hspV, hspL⟩ := split_rel text hs hn2 44#u32 (by decide)
  have hc : chOf 44#u32 = ',' := by decide
  rw [hc] at hspv
  simp only [psS]
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
  hop_rstep r0 h0r v
  have hvm := h0m v rfl
  obtain ⟨r1, h1, h1r⟩ := beatmap.hit_object_parser.parse_coord_refines st.format_version _ (hVv v hvm) (hLv v hvm)
  rw [strV_deref] at h1r
  simp only [h1, bind_ok]
  hop_rstep r1 h1r x
  obtain ⟨r2, h2, h2r, h2m⟩ := beatmap.hit_object_parser.at_refines (alloc.vec.Vec.deref sp) 1#usize
  rw [deref_valA, e1] at h2r; rw [deref_valA] at h2m
  simp only [h2, bind_ok]
  hop_rstep r2 h2r v2
  have hvm2 := h2m v2 rfl
  obtain ⟨r3, h3, h3r⟩ := beatmap.hit_object_parser.parse_coord_refines st.format_version _ (hVv v2 hvm2) (hLv v2 hvm2)
  rw [strV_deref] at h3r
  simp only [h3, bind_ok]
  hop_rstep r3 h3r y
  obtain ⟨r4, h4, h4r, h4m⟩ := beatmap.hit_object_parser.at_refines (alloc.vec.Vec.deref sp) 2#usize
  rw [deref_valA, e2] at h4r; rw [deref_valA] at h4m
  simp only [h4, bind_ok]
  hop_rstep r4 h4r v4
  have hvm4 := h4m v4 rfl
  simp only [net.parse.parse_double_default_refines _ (hVv v4 hvm4) (hLv v4 hvm4), bind_ok, strV_deref]
  obtain ⟨r6, h6, h6r⟩ := lift_net_exceptI beatmap.errors.W_STARTTIME id id (fun _ => rfl)
    (Parsing.parseDouble (strV v4)) "startTime"
  simp only [h6, bind_ok]
  hop_rstep r6 h6r t
  simp only [float.F64.add, bind_ok, id]
  obtain ⟨r7, h7, h7r, h7m⟩ := beatmap.hit_object_parser.at_refines (alloc.vec.Vec.deref sp) 3#usize
  rw [deref_valA, e3] at h7r; rw [deref_valA] at h7m
  simp only [h7, bind_ok]
  hop_rstep r7 h7r v6
  have hvm6 := h7m v6 rfl
  simp only [net.parse.parse_int_default_refines _ (hVv v6 hvm6), bind_ok, strV_deref]
  obtain ⟨r9, h9, h9r⟩ := lift_net_exceptI beatmap.errors.W_TYPE i32I i32S (fun _ => rfl)
    (Parsing.parseInt (strV v6)) "type"
  simp only [h9, bind_ok]
  hop_rstep r9 h9r v7
  obtain ⟨c, hc4, hcv⟩ := hop_i32S_shr4 (v7 &&& beatmap.hit_object_parser.COMBO_OFFSET)
  simp only [lift, bind_ok, hc4]
  obtain ⟨r10, h10, h10r, h10m⟩ := beatmap.hit_object_parser.at_refines (alloc.vec.Vec.deref sp) 4#usize
  rw [deref_valA, e4] at h10r; rw [deref_valA] at h10m
  simp only [h10, bind_ok]
  hop_rstep r10 h10r v8
  have hvm8 := h10m v8 rfl
  simp only [net.parse.parse_int_default_refines _ (hVv v8 hvm8), bind_ok, strV_deref]
  obtain ⟨r12, h12, h12r⟩ := lift_net_exceptI beatmap.errors.W_SOUNDTYPE i32I i32S (fun _ => rfl)
    (Parsing.parseInt (strV v8)) "soundType"
  simp only [h12, bind_ok]
  hop_rstep r12 h12r w
  refine ⟨_, rfl, ?_⟩
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

end OsuProofs
