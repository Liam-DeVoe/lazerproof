/-
`replay::frames` (Rust) refines `OsuModel.Replay` Frames: the `ActList` helpers (spec `List Action` operations,
`ActList` ↦ its first `len` items, `len ≤ 3` as a hypothesis = the invariant of every list built by `act_push`),
frame conversion and the stable fixups, the `.osr` frame-text parser.
-/
import OsuProofs.Sim2.Schedule
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

@[simp] theorem s2_action_eq (x y : replay.frames.Action) :
    replay.frames.Action.Insts.CoreCmpPartialEqAction.eq x y = ok (s2_actS x == s2_actS y) := by
  cases x <;> cases y <;> simp [replay.frames.Action.Insts.CoreCmpPartialEqAction.eq, read_discriminant,
    replay.frames.Action.read_discriminant, s2_actS] <;> decide
@[simp] theorem s2_action_ne (x y : replay.frames.Action) :
    core.cmp.PartialEq.ne.trait_default replay.frames.Action.Insts.CoreCmpPartialEqAction x y = ok (s2_actS x != s2_actS y) := by
  simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, bne]

theorem s2_arr_index {α : Type} {n : Usize} (v : Std.Array α n) (i : Usize) (h : i.val < v.val.length) :
    Std.Array.index_usize v i = ok (v.val[i.val]'h) := by
  obtain ⟨x, hx, hx'⟩ := eq_ok_of_spec (Std.Array.index_usize_spec v i h)
  rw [hx, hx']

theorem s2_arr3 {α : Type} (v : Std.Array α 3#usize) : ∃ x0 x1 x2, v.val = [x0, x1, x2] := by
  have hp := v.property
  match h : v.val, hp with
  | [x0, x1, x2], _ => exact ⟨x0, x1, x2, rfl⟩

theorem s2_arr3_i0 {α : Type} {v : Std.Array α 3#usize} {x0 x1 x2 : α} (h : v.val = [x0, x1, x2]) :
    Std.Array.index_usize v 0#usize = ok x0 := by
  rw [s2_arr_index v 0#usize (by simp [h])]; simp [h]
theorem s2_arr3_i1 {α : Type} {v : Std.Array α 3#usize} {x0 x1 x2 : α} (h : v.val = [x0, x1, x2]) :
    Std.Array.index_usize v 1#usize = ok x1 := by
  rw [s2_arr_index v 1#usize (by simp [h])]; simp [h]
theorem s2_arr3_i2 {α : Type} {v : Std.Array α 3#usize} {x0 x1 x2 : α} (h : v.val = [x0, x1, x2]) :
    Std.Array.index_usize v 2#usize = ok x2 := by
  rw [s2_arr_index v 2#usize (by simp [h])]; simp [h]

theorem s2_usize_succ (a b : Usize) (h : b.val = a.val + 1) (hb : a.val + 1 ≤ Usize.max) : a + 1#usize = ok b := by
  obtain ⟨z, hz, hzv⟩ := usize_add_one a hb
  rw [hz]; congr 1; exact UScalar.eq_of_val_eq (by rw [hzv, h])
@[simp] theorem s2_usize_01 : (0#usize : Usize) + 1#usize = ok 1#usize := s2_usize_succ _ _ (by simp) (by simp; scalar_tac)
@[simp] theorem s2_usize_12 : (1#usize : Usize) + 1#usize = ok 2#usize := s2_usize_succ _ _ (by simp) (by simp; scalar_tac)
@[simp] theorem s2_usize_23 : (2#usize : Usize) + 1#usize = ok 3#usize := s2_usize_succ _ _ (by simp) (by simp; scalar_tac)

theorem s2_usize_cases (u : Usize) (h : u.val ≤ 3) : u = 0#usize ∨ u = 1#usize ∨ u = 2#usize ∨ u = 3#usize := by
  have : u.val = 0 ∨ u.val = 1 ∨ u.val = 2 ∨ u.val = 3 := by omega
  rcases this with h | h | h | h
  · left; exact UScalar.eq_of_val_eq (by simp [h])
  · right; left; exact UScalar.eq_of_val_eq (by simp [h])
  · right; right; left; exact UScalar.eq_of_val_eq (by simp [h])
  · right; right; right; exact UScalar.eq_of_val_eq (by simp [h])

theorem replay.frames.act_contains_refines (l : replay.frames.ActList) (a : replay.frames.Action)
    (hl : l.len.val ≤ 3) :
    replay.frames.act_contains l a = ok ((abs l : List OsuModel.Replay.Action).contains (abs a)) := by
  have hp := l.items.property
  obtain ⟨items, len⟩ := l
  simp only at hl hp ⊢
  unfold replay.frames.act_contains replay.frames.act_contains_loop
  obtain ⟨x0, x1, x2, hx⟩ := s2_arr3 items
  rcases s2_usize_cases len hl with h | h | h | h <;> subst h <;>
  · repeat (rw [loop_unfold]; simp [replay.frames.act_contains_loop.body, s2_arr3_i0 hx, s2_arr3_i1 hx, s2_arr3_i2 hx])
    all_goals simp [abs, s2_actListS, actListS, actS, hx]
    all_goals (cases a <;> cases x0 <;> cases x1 <;> cases x2 <;> rfl)

theorem s2_empty_val : replay.frames.ACTLIST_EMPTY.items.val = [.Left, .Left, .Left] ∧ replay.frames.ACTLIST_EMPTY.len = 0#usize := by
  unfold replay.frames.ACTLIST_EMPTY; simp [Std.Array.make]

theorem replay.frames.act_push_refines (l : replay.frames.ActList) (a : replay.frames.Action) (hl : l.len.val < 3) :
    ∃ r, replay.frames.act_push l a = ok r ∧ (abs r : List OsuModel.Replay.Action) = abs l ++ [abs a] ∧
      r.len.val = l.len.val + 1 ∧ r.items.val = l.items.val.set l.len.val a := by
  obtain ⟨items, len⟩ := l
  simp only at hl ⊢
  have hlt : len < 3#usize := by scalar_tac
  have hp := items.property
  obtain ⟨i1, hi1, hi1v⟩ := usize_add_one len (by scalar_tac)
  obtain ⟨v, hv, hvv⟩ := eq_ok_of_spec (Std.Array.update_spec items len a (by simp; omega))
  refine ⟨⟨v, i1⟩, by simp [replay.frames.act_push, hlt, hv, hi1], ?_, by simp [hi1v], by simp [hvv, Std.Array.set]⟩
  obtain ⟨x0, x1, x2, hx⟩ := s2_arr3 items
  have : len.val = 0 ∨ len.val = 1 ∨ len.val = 2 := by omega
  rcases this with h | h | h <;> simp [abs, s2_actListS, actListS, actS, hvv, Std.Array.set, hx, hi1v, h]

/-- the `r = act_push(r, items[i])`-if-`p` loops over an `ActList` (`act_remove`, `act_minus`) -/
theorem s2_items_len (l : replay.frames.ActList) : l.items.val.length = 3 := by
  have := l.items.property; simpa using this

theorem s2_act_filter_loop (l : replay.frames.ActList) (p : replay.frames.Action → Bool) (hl : l.len.val ≤ 3)
    (body : replay.frames.ActList × Usize → Result (ControlFlow (replay.frames.ActList × Usize) replay.frames.ActList))
    (hstep : ∀ r (i : Usize) (h : i.val < l.len.val), body (r, i) = (do
        let r1 ← if p (l.items.val[i.val]'(by rw [s2_items_len]; omega)) then
          replay.frames.act_push r (l.items.val[i.val]'(by rw [s2_items_len]; omega)) else ok r
        let i1 ← i + 1#usize
        ok (.cont (r1, i1))))
    (hend : ∀ r (i : Usize), l.len.val ≤ i.val → body (r, i) = ok (.done r)) :
    ∀ (k : Nat) (r : replay.frames.ActList) (i : Usize), l.len.val - i.val = k → r.len.val ≤ i.val → i.val ≤ l.len.val →
      ∃ r', loop body (r, i) = ok r' ∧ r'.len.val ≤ 3 ∧
        (abs r' : List OsuModel.Replay.Action) = abs r ++ (((l.items.val.take l.len.val).drop i.val).filter p).map s2_actS := by
  have hp := s2_items_len l
  intro k
  induction k with
  | zero =>
    intro r i hk hr hi
    refine ⟨r, by rw [loop_unfold, hend r i (by omega)]; simp, by omega, ?_⟩
    simp [List.drop_eq_nil_of_le (show (l.items.val.take l.len.val).length ≤ i.val by simp; omega)]
  | succ k ih =>
    intro r i hk hr hi
    have hlt : i.val < l.len.val := by omega
    have hil : i.val < l.items.val.length := by omega
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by scalar_tac)
    have hdrop : (l.items.val.take l.len.val).drop i.val = l.items.val[i.val] :: (l.items.val.take l.len.val).drop i1.val := by
      rw [hi1v, List.drop_eq_getElem_cons (by simp; omega)]; simp
    by_cases hc : p (l.items.val[i.val]) = true
    · obtain ⟨r1, hr1, ar1, lr1, _⟩ := replay.frames.act_push_refines r (l.items.val[i.val]) (by omega)
      obtain ⟨r', hl', hlen', ar'⟩ := ih r1 i1 (by omega) (by omega) (by omega)
      refine ⟨r', ?_, hlen', ?_⟩
      · rw [loop_unfold, hstep r i hlt]; simp [hc, hr1, hi1]; exact hl'
      · rw [ar', ar1, hdrop]; simp [hc, abs]
    · obtain ⟨r', hl', hlen', ar'⟩ := ih r i1 (by omega) (by omega) (by omega)
      refine ⟨r', ?_, hlen', ?_⟩
      · rw [loop_unfold, hstep r i hlt]; simp [hc, hi1]; exact hl'
      · rw [ar', hdrop]; simp [hc]

theorem s2_abs_empty : (abs replay.frames.ACTLIST_EMPTY : List OsuModel.Replay.Action) = [] := by
  simp [abs, s2_actListS, actListS, actS, s2_empty_val.2]

theorem replay.frames.act_remove_refines (l : replay.frames.ActList) (a : replay.frames.Action) (hl : l.len.val ≤ 3) :
    ∃ r, replay.frames.act_remove l a = ok r ∧ r.len.val ≤ 3 ∧
      (abs r : List OsuModel.Replay.Action) = (abs l : List OsuModel.Replay.Action).filter (· != abs a) := by
  obtain ⟨r', hl', hlen, ar⟩ := s2_act_filter_loop l (fun x => s2_actS x != s2_actS a) hl
    (fun x => replay.frames.act_remove_loop.body l a x.1 x.2)
    (by intro r i h
        have hi : i < l.len := by scalar_tac
        simp [replay.frames.act_remove_loop.body, hi, s2_arr_index _ _ (by rw [s2_items_len]; omega : i.val < l.items.val.length)])
    (by intro r i h
        have hi : ¬ (i < l.len) := by scalar_tac
        simp [replay.frames.act_remove_loop.body, hi])
    l.len.val replay.frames.ACTLIST_EMPTY 0#usize (by simp) (by simp [s2_empty_val.2]) (by simp)
  refine ⟨r', ?_, hlen, ?_⟩
  · unfold replay.frames.act_remove replay.frames.act_remove_loop; exact hl'
  · rw [ar, s2_abs_empty]; simp only [abs, s2_actListS, actListS, actS, List.drop_zero, List.nil_append, show (0#usize : Usize).val = 0 from rfl]
    rw [List.filter_map]; rfl

theorem replay.frames.act_minus_refines (l other : replay.frames.ActList) (hl : l.len.val ≤ 3) (ho : other.len.val ≤ 3) :
    ∃ r, replay.frames.act_minus l other = ok r ∧ r.len.val ≤ 3 ∧
      (abs r : List OsuModel.Replay.Action) =
        (abs l : List OsuModel.Replay.Action).filter (fun x => !(abs other : List OsuModel.Replay.Action).contains x) := by
  obtain ⟨r', hl', hlen, ar⟩ := s2_act_filter_loop l (fun x => !(abs other : List OsuModel.Replay.Action).contains (s2_actS x)) hl
    (fun x => replay.frames.act_minus_loop.body l other x.1 x.2)
    (by intro r i h
        have hi : i < l.len := by scalar_tac
        simp only [replay.frames.act_minus_loop.body, hi, ite_true, s2_arr_index _ _ (by rw [s2_items_len]; omega : i.val < l.items.val.length),
          replay.frames.act_contains_refines other _ ho, bind_ok]
        cases (abs other : List OsuModel.Replay.Action).contains (abs (l.items.val[i.val]'(by rw [s2_items_len]; omega))) <;> rfl)
    (by intro r i h
        have hi : ¬ (i < l.len) := by scalar_tac
        simp [replay.frames.act_minus_loop.body, hi])
    l.len.val replay.frames.ACTLIST_EMPTY 0#usize (by simp) (by simp [s2_empty_val.2]) (by simp)
  refine ⟨r', ?_, hlen, ?_⟩
  · unfold replay.frames.act_minus replay.frames.act_minus_loop; exact hl'
  · rw [ar, s2_abs_empty]; simp only [abs, s2_actListS, actListS, actS, List.drop_zero, List.nil_append, show (0#usize : Usize).val = 0 from rfl]
    rw [List.filter_map]; rfl

instance s2_lawfulAction : LawfulBEq OsuModel.Replay.Action where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | (exact absurd h (by decide))
  rfl {a} := by cases a <;> decide

theorem s2_beq_act (x y : replay.frames.Action) : (s2_actS x == s2_actS y) = decide (s2_actS x = s2_actS y) := by
  cases x <;> cases y <;> rfl
theorem s2_bne_act (x y : replay.frames.Action) : (s2_actS x != s2_actS y) = !(decide (s2_actS x = s2_actS y)) := by
  simp [bne, s2_beq_act]

theorem replay.frames.act_eq_refines (a b : replay.frames.ActList) (ha : a.len.val ≤ 3) (hb : b.len.val ≤ 3) :
    replay.frames.act_eq a b = ok ((abs a : List OsuModel.Replay.Action) == abs b) := by
  obtain ⟨ia, la⟩ := a
  obtain ⟨ib, lb⟩ := b
  simp only at ha hb ⊢
  obtain ⟨x0, x1, x2, hx⟩ := s2_arr3 ia
  obtain ⟨y0, y1, y2, hy⟩ := s2_arr3 ib
  unfold replay.frames.act_eq
  by_cases hne : la = lb
  · subst hne
    have : (la != la) = false := by simp
    simp only [this, Bool.false_eq_true, ite_false]
    unfold replay.frames.act_eq_loop
    rcases s2_usize_cases la ha with h | h | h | h <;> subst h
    all_goals (repeat (rw [loop_unfold]; simp [replay.frames.act_eq_loop.body, s2_arr3_i0 hx, s2_arr3_i1 hx, s2_arr3_i2 hx, s2_arr3_i0 hy, s2_arr3_i1 hy, s2_arr3_i2 hy]))
    all_goals simp [abs, s2_actListS, actListS, hx, hy, s2_bne_act]
    all_goals (try simp [s2_beq_act, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc])
  · have : (la != lb) = true := by simpa using hne
    simp only [this, ite_true]
    have hl : la.val ≠ lb.val := fun h => hne (UScalar.eq_of_val_eq h)
    congr 1
    symm; rw [beq_eq_false_iff_ne]
    intro h
    have := congrArg List.length h
    simp [abs, s2_actListS, actListS, actS] at this
    omega

theorem replay.frames.button_bit_refines (b k : U32) (hk : k.val < 32) :
    replay.frames.button_bit b k = ok ((UInt32.ofBitVec b.bv >>> UInt32.ofBitVec k.bv) &&& 1 == 1) := by
  unfold replay.frames.button_bit
  have := U32.ShiftRight_spec b k (by simpa using hk)
  obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec this
  simp only [hz, bind_ok, lift]
  congr 1
  have hk' : k.bv.toNat = k.val := rfl
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, beq_iff_eq]
  rw [← UInt32.toBitVec_inj]
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_shiftRight, UInt32.toBitVec_ofNat]
  rw [UScalar.eq_equiv_bv_eq]
  simp only [UScalar.bv_and, hzv.2]
  have e : b.bv >>> (k.bv % 32) = b.bv >>> k.val := by
    rw [BitVec.ushiftRight_eq']; congr 1
    simp [BitVec.toNat_umod, hk', Nat.mod_eq_of_lt hk]
  rw [e]; rfl
end OsuProofs
namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_cond_push (c : Bool) (r : replay.frames.ActList) (a : replay.frames.Action) (h : r.len.val < 3) :
    ∃ r', (if c then replay.frames.act_push r a else ok r) = ok r' ∧
      (abs r' : List OsuModel.Replay.Action) = abs r ++ (if c then [abs a] else []) ∧ r'.len.val ≤ r.len.val + 1 := by
  cases c
  · exact ⟨r, rfl, by simp, by omega⟩
  · obtain ⟨r', h1, h2, h3, _⟩ := replay.frames.act_push_refines r a h
    exact ⟨r', by simpa using h1, by simpa using h2, by omega⟩

theorem s2_hcast_u32 (x : I32) : UInt32.ofBitVec (IScalar.hcast .U32 x).bv = (i32S x).toUInt32 := by
  rw [IScalar.hcast_bv_eq]
  apply UInt32.toBitVec_inj.mp
  simp [i32S]

theorem replay.frames.convert_frame_refines (f : replay.frames.LegacyFrame) :
    ∃ r, replay.frames.convert_frame f = ok r ∧ OsuModel.Replay.convertFrame (abs f) = abs r ∧ r.actions.len.val ≤ 3 := by
  have hb0 := replay.frames.button_bit_refines (IScalar.hcast .U32 f.buttons) 0#u32 (by simp)
  have hb1 := replay.frames.button_bit_refines (IScalar.hcast .U32 f.buttons) 1#u32 (by simp)
  have hb2 := replay.frames.button_bit_refines (IScalar.hcast .U32 f.buttons) 2#u32 (by simp)
  have hb3 := replay.frames.button_bit_refines (IScalar.hcast .U32 f.buttons) 3#u32 (by simp)
  have hb4 := replay.frames.button_bit_refines (IScalar.hcast .U32 f.buttons) 4#u32 (by simp)
  rw [s2_hcast_u32] at hb0 hb1 hb2 hb3 hb4
  have e0 : UInt32.ofBitVec (0#u32 : U32).bv = 0 := rfl
  have e1 : UInt32.ofBitVec (1#u32 : U32).bv = 1 := rfl
  have e2 : UInt32.ofBitVec (2#u32 : U32).bv = 2 := rfl
  have e3 : UInt32.ofBitVec (3#u32 : U32).bv = 3 := rfl
  have e4 : UInt32.ofBitVec (4#u32 : U32).bv = 4 := rfl
  rw [e0] at hb0; rw [e1] at hb1; rw [e2] at hb2; rw [e3] at hb3; rw [e4] at hb4
  have hE := s2_empty_val
  obtain ⟨a1, ha1, ea1, la1⟩ := s2_cond_push ((i32S f.buttons).toUInt32 >>> 0 &&& 1 == 1 || (i32S f.buttons).toUInt32 >>> 2 &&& 1 == 1)
    replay.frames.ACTLIST_EMPTY .Left (by simp [hE.2])
  obtain ⟨a2, ha2, ea2, la2⟩ := s2_cond_push ((i32S f.buttons).toUInt32 >>> 1 &&& 1 == 1 || (i32S f.buttons).toUInt32 >>> 3 &&& 1 == 1)
    a1 .Right (by simp [hE.2] at la1; omega)
  obtain ⟨a3, ha3, ea3, la3⟩ := s2_cond_push ((i32S f.buttons).toUInt32 >>> 4 &&& 1 == 1)
    a2 .Smoke (by simp [hE.2] at la1; omega)
  refine ⟨⟨f.time, ⟨f.mouse_x, f.mouse_y⟩, a3⟩, ?_, ?_, ?_⟩
  · unfold replay.frames.convert_frame
    simp only [lift, bind_ok, hb0, hb1, hb2, hb3, hb4]
    have o1 : ∀ (x y : Bool), (if x = true then (ok true : Result Bool) else ok y) = ok (x || y) := by
      intro x y; cases x <;> rfl
    simp only [o1, bind_ok, ha1, ha2]
    cases hs : ((i32S f.buttons).toUInt32 >>> 4 &&& 1 == 1)
    · simp only [hs] at ha3; simp at ha3; subst ha3; simp
    · simp only [hs] at ha3; simp only [ite_true] at ha3; simp [ha3]
  · have ea : (abs a3 : List OsuModel.Replay.Action) = s2_actListS a3 := rfl
    rw [s2_abs_empty] at ea1
    simp only [abs, s2_frameS, OsuModel.Replay.convertFrame]
    rw [show actListS a3 = (abs a3 : List OsuModel.Replay.Action) from rfl, ea3, ea2, ea1]
    simp [abs, s2_actS, actS]
  · simp [hE.2] at la1; simp; omega

@[simp] theorem s2_F32_256 : replay.frames.F32_256 = ok (256 : F32) := by
  unfold replay.frames.F32_256; simp; decide +kernel
@[simp] theorem s2_F32_M500 : replay.frames.F32_M500 = ok (-500 : F32) := by
  unfold replay.frames.F32_M500; simp; decide +kernel

/-- `isSkipPos` (a `private def` of the spec, inlined here). -/
theorem replay.frames.is_skip_pos_refines (f : replay.frames.LegacyFrame) :
    replay.frames.is_skip_pos f = ok ((abs f : OsuModel.Replay.LegacyFrame).mouseX == (256 : F32) &&
      (abs f : OsuModel.Replay.LegacyFrame).mouseY == (-500 : F32)) := by
  unfold replay.frames.is_skip_pos
  cases h : f.mouse_x == (256 : F32) <;> simp [float.F32.eq, h, abs]

theorem s2_erase_take {α : Type} (l : List α) (k i : Nat) (hi : i < l.length) :
    (l.take (i + 1)).eraseIdx k = if i ≠ k then (l.take i).eraseIdx k ++ [l[i]] else (l.take i).eraseIdx k := by
  rw [List.take_succ, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some]
  by_cases hik : i = k
  · subst hik
    rw [if_neg (by simp), List.eraseIdx_append_of_length_le (by simp),
      List.eraseIdx_of_length_le (l := l.take i) (by simp)]
    simp; omega
  · simp only [hik, ne_eq, not_false_eq_true, ite_true]
    by_cases hlt : k < i
    · rw [List.eraseIdx_append_of_lt_length (by simp; omega)]
    · rw [List.eraseIdx_of_length_le (by simp; omega), List.eraseIdx_of_length_le (by simp; omega)]

theorem replay.frames.erase_idx_refines (fs : Slice replay.frames.LegacyFrame) (k : Usize) :
    ∃ r, replay.frames.erase_idx fs k = ok r ∧ r.val = fs.val.eraseIdx k.val := by
  have hmax := fs.property
  suffices h : ∀ (n : Nat) (out : alloc.vec.Vec replay.frames.LegacyFrame) (i : Usize), fs.val.length - i.val = n →
      i.val ≤ fs.val.length → out.val = (fs.val.take i.val).eraseIdx k.val →
      ∃ r, replay.frames.erase_idx_loop fs k out i = ok r ∧ r.val = fs.val.eraseIdx k.val by
    obtain ⟨r, h1, h2⟩ := h _ (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
    exact ⟨r, h1, h2⟩
  intro n
  induction n with
  | zero =>
    intro out i hn hi hout
    refine ⟨out, ?_, ?_⟩
    · unfold replay.frames.erase_idx_loop; rw [loop_unfold]
      have : ¬ (i < Slice.len fs) := by rw [slice_lt_len_iff]; omega
      simp [replay.frames.erase_idx_loop.body, this]
    · rw [hout, List.take_of_length_le (by omega)]
  | succ n ih =>
    intro out i hn hi hout
    have hlt : i.val < fs.val.length := by omega
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
    have hlen : out.val.length < Usize.max := by
      rw [hout]; have := List.length_eraseIdx_le (fs.val.take i.val) k.val; simp at this ⊢; omega
    by_cases hik : i = k
    · obtain ⟨r, h1, h2⟩ := ih out i1 (by omega) (by omega) (by rw [hout, hi1v, s2_erase_take _ _ _ hlt]; simp [hik])
      refine ⟨r, ?_, h2⟩
      have hb : replay.frames.erase_idx_loop.body fs k out i = ok (.cont (out, i1)) := by
        subst hik; simp [replay.frames.erase_idx_loop.body, slice_lt_len_iff, hlt, hi1]
      unfold replay.frames.erase_idx_loop; rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]
      unfold replay.frames.erase_idx_loop at h1; exact h1
    · have hik' : i.val ≠ k.val := fun h => hik (UScalar.eq_of_val_eq h)
      obtain ⟨r, h1, h2⟩ := ih (vpush out (fs.val[i.val]'hlt) hlen) i1 (by omega) (by omega)
        (by rw [vpush_val, hout, hi1v, s2_erase_take _ _ _ hlt]; simp [hik'])
      refine ⟨r, ?_, h2⟩
      have hb : replay.frames.erase_idx_loop.body fs k out i = ok (.cont (vpush out (fs.val[i.val]'hlt) hlen, i1)) := by
        simp [replay.frames.erase_idx_loop.body, slice_lt_len_iff, hlt, hik, hi1, slice_index_ok _ _ hlt, vec_push_ok _ _ hlen]
      unfold replay.frames.erase_idx_loop; rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]
      unfold replay.frames.erase_idx_loop at h1; exact h1

/-- the backwards-time filter step on Rust frames -/
def s2_dbR (out : List replay.frames.LegacyFrame) (f : replay.frames.LegacyFrame) : List replay.frames.LegacyFrame :=
  match out.getLast? with
  | some cur => if f.time < cur.time then out else out ++ [f]
  | none => out ++ [f]

theorem s2_dbR_len (l : List replay.frames.LegacyFrame) : ∀ out, (l.foldl s2_dbR out).length ≤ out.length + l.length := by
  induction l with
  | nil => intro out; simp
  | cons f t ih =>
    intro out; simp only [List.foldl_cons]
    have := ih (s2_dbR out f)
    have h2 : (s2_dbR out f).length ≤ out.length + 1 := by
      unfold s2_dbR; split
      · split <;> simp
      · simp
    simp; omega

theorem s2_drop_backwards_rust (fs : Slice replay.frames.LegacyFrame) :
    ∃ r, replay.frames.drop_backwards fs = ok r ∧ r.val = fs.val.foldl s2_dbR [] := by
  have hmax := fs.property
  suffices h : ∀ (n : Nat) (out : alloc.vec.Vec replay.frames.LegacyFrame) (i : Usize), fs.val.length - i.val = n →
      i.val ≤ fs.val.length → out.val.length ≤ i.val →
      ∃ r, replay.frames.drop_backwards_loop fs out i = ok r ∧ r.val = (fs.val.drop i.val).foldl s2_dbR out.val by
    obtain ⟨r, h1, h2⟩ := h _ (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
    exact ⟨r, h1, by simpa using h2⟩
  intro n
  induction n with
  | zero =>
    intro out i hn hi hout
    refine ⟨out, ?_, ?_⟩
    · unfold replay.frames.drop_backwards_loop; rw [loop_unfold]
      have : ¬ (i < Slice.len fs) := by rw [slice_lt_len_iff]; omega
      simp [replay.frames.drop_backwards_loop.body, this]
    · rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | succ n ih =>
    intro out i hn hi hout
    have hlt : i.val < fs.val.length := by omega
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
    have hlen : out.val.length < Usize.max := by omega
    have hdrop : fs.val.drop i.val = fs.val[i.val] :: fs.val.drop i1.val := by
      rw [hi1v]; exact List.drop_eq_getElem_cons hlt
    rw [hdrop, List.foldl_cons]
    let f := fs.val[i.val]
    by_cases h0 : out.val.length = 0
    · have hn0 : alloc.vec.Vec.len out = 0#usize := by scalar_tac
      obtain ⟨r, h1, h2⟩ := ih (vpush out f hlen) i1 (by omega) (by omega) (by simp; omega)
      refine ⟨r, ?_, ?_⟩
      · have hb : replay.frames.drop_backwards_loop.body fs out i = ok (.cont (vpush out f hlen, i1)) := by
          simp [replay.frames.drop_backwards_loop.body, slice_lt_len_iff, hlt, hn0, hi1, slice_index_ok _ _ hlt, vec_push_ok _ _ hlen, f]
        unfold replay.frames.drop_backwards_loop; rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]
        unfold replay.frames.drop_backwards_loop at h1; exact h1
      · rw [h2]; congr 1
        have : out.val = [] := List.eq_nil_of_length_eq_zero h0
        simp [s2_dbR, this, f]
    · have hn0 : ¬ (alloc.vec.Vec.len out = 0#usize) := by intro h; apply h0; scalar_tac
      obtain ⟨m, hm, hmv⟩ := usize_sub_one (alloc.vec.Vec.len out) (by simp; omega)
      have hml : m.val < out.val.length := by simp at hmv; omega
      have hlast : out.val.getLast? = some (out.val[m.val]'hml) := by
        rw [List.getLast?_eq_getElem?, ← List.getElem?_eq_getElem hml]; simp at hmv; rw [hmv]
      by_cases hc : f.time < (out.val[m.val]'hml).time
      · obtain ⟨r, h1, h2⟩ := ih out i1 (by omega) (by omega) (by omega)
        refine ⟨r, ?_, ?_⟩
        · have hb : replay.frames.drop_backwards_loop.body fs out i = ok (.cont (out, i1)) := by
            simp [replay.frames.drop_backwards_loop.body, slice_lt_len_iff, hlt, hn0, hi1, slice_index_ok _ _ hlt, hm,
              vec_index_usize_ok _ _ hml, float.F64.lt, hc, f]
          unfold replay.frames.drop_backwards_loop; rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]
          unfold replay.frames.drop_backwards_loop at h1; exact h1
        · rw [h2]; congr 1; simp [s2_dbR, hlast, hc, f]
      · obtain ⟨r, h1, h2⟩ := ih (vpush out f hlen) i1 (by omega) (by omega) (by simp; omega)
        refine ⟨r, ?_, ?_⟩
        · have hb : replay.frames.drop_backwards_loop.body fs out i = ok (.cont (vpush out f hlen, i1)) := by
            simp [replay.frames.drop_backwards_loop.body, slice_lt_len_iff, hlt, hn0, hi1, slice_index_ok _ _ hlt, hm,
              vec_index_usize_ok _ _ hml, float.F64.lt, hc, vec_push_ok _ _ hlen, f]
          unfold replay.frames.drop_backwards_loop; rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]
          unfold replay.frames.drop_backwards_loop at h1; exact h1
        · rw [h2]; congr 1; simp [s2_dbR, hlast, hc, f]

def s2_lfS (f : replay.frames.LegacyFrame) : OsuModel.Replay.LegacyFrame := abs f

/-- the spec's backwards-time filter step (the loop body at the end of `fixupFrames`) -/
def s2_dbS (out : _root_.Array OsuModel.Replay.LegacyFrame) (f : OsuModel.Replay.LegacyFrame) :
    _root_.Array OsuModel.Replay.LegacyFrame :=
  match out.back? with
  | some cur => if f.time < cur.time then out else out.push f
  | none => out.push f

theorem s2_db_map (l : List replay.frames.LegacyFrame) : ∀ out : List replay.frames.LegacyFrame,
    ((l.foldl s2_dbR out).map s2_lfS).toArray = l.foldl (fun A f => s2_dbS A (s2_lfS f)) (out.map s2_lfS).toArray := by
  induction l with
  | nil => intro out; rfl
  | cons f t ih =>
    intro out
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    unfold s2_dbR s2_dbS
    have hb : (out.map s2_lfS).toArray.back? = out.getLast?.map s2_lfS := by
      simp [Array.back?, List.getLast?_eq_getElem?]
    rw [hb]
    cases out.getLast? with
    | none => simp
    | some cur =>
      simp only [Option.map_some]
      have e1 : (s2_lfS f).time = f.time := rfl
      have e2 : (s2_lfS cur).time = cur.time := rfl
      rw [e1, e2]
      split <;> simp

theorem replay.frames.drop_backwards_refines (fs : Slice replay.frames.LegacyFrame) :
    ∃ r, replay.frames.drop_backwards fs = ok r ∧
      (abs fs : _root_.Array OsuModel.Replay.LegacyFrame).foldl s2_dbS #[] = abs r := by
  obtain ⟨r, h1, h2⟩ := s2_drop_backwards_rust fs
  refine ⟨r, h1, ?_⟩
  have := s2_db_map fs.val []
  rw [← h2] at this
  have ea : (abs r : _root_.Array OsuModel.Replay.LegacyFrame) = (r.val.map s2_lfS).toArray := rfl
  have eb : (abs fs : _root_.Array OsuModel.Replay.LegacyFrame) = (fs.val.map s2_lfS).toArray := rfl
  rw [ea, this, eb, List.foldl_toArray' (h := rfl), List.foldl_map]; rfl

end OsuProofs
