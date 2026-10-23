/-
`beatmap::mod_settings`, part 7: `int_to_str` (= `toString` on `Int`), `enumString`, and the
`beatmap::dotnet::lit_str` helper (byte literal → scalar-value string).
-/
import OsuProofs.Beatmap.ModSettings6
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap OsuModel.Net.Framework

namespace OsuProofs
open OsuImpl

/-! ## `lit_str` -/

theorem lit_str_loop_ok (s : Slice U8) :
    ∀ (out : alloc.vec.Vec U32) (i : Usize), i.val ≤ s.val.length → out.val.length + (s.val.length - i.val) ≤ s.val.length →
      ∃ v, beatmap.dotnet.lit_str_loop s out i = ok v ∧
        v.val.map (·.val) = out.val.map (·.val) ++ (s.val.drop i.val).map (·.val) := by
  intro out i hi0 hlen
  unfold beatmap.dotnet.lit_str_loop
  refine loop_ok _ (fun (x : alloc.vec.Vec U32 × Usize) => s.val.length - x.2.val)
    (fun (x : alloc.vec.Vec U32 × Usize) => x.2.val ≤ s.val.length ∧ x.1.val.length + (s.val.length - x.2.val) ≤ s.val.length ∧
      x.1.val.map (·.val) ++ (s.val.drop x.2.val).map (·.val) = out.val.map (·.val) ++ (s.val.drop i.val).map (·.val))
    (fun (v : alloc.vec.Vec U32) => v.val.map (·.val) = out.val.map (·.val) ++ (s.val.drop i.val).map (·.val)) ?_ (out, i)
    ⟨hi0, hlen, rfl⟩
  rintro ⟨o, j⟩ ⟨hj, hol, heq⟩
  dsimp only at hj hol heq ⊢
  by_cases hlt : j.val < s.val.length
  · right
    have hlt' : j < Slice.len s := by show j.val < (Slice.len s).val; simpa using hlt
    obtain ⟨o1, ho1, ho1v⟩ := push_eq o (UScalar.cast .U32 (s.val[j.val]'hlt)) (by have := s.property; have := usize_ge_32; omega)
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := s.property; omega)
    refine ⟨(o1, j1), by simp [beatmap.dotnet.lit_str_loop.body, hlt', index_eq s j hlt, lift, ho1, hj1], ?_, by dsimp only; omega⟩
    refine ⟨by dsimp only; omega, by dsimp only; rw [ho1v]; simp; omega, ?_⟩
    dsimp only
    rw [ho1v, hj1v, ← heq, List.drop_eq_getElem_cons hlt]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.singleton_append, cast_u8_val]
  · left
    have hlt' : ¬ j < Slice.len s := by show ¬ j.val < (Slice.len s).val; simpa using hlt
    refine ⟨o, by simp [beatmap.dotnet.lit_str_loop.body, hlt'], ?_⟩
    rw [← heq, List.drop_eq_nil_of_le (by omega)]; simp

/-- `lit_str` (no spec def): the scalar values of the bytes. -/
theorem beatmap.dotnet.lit_str_refines (s : Slice U8) :
    ∃ v, beatmap.dotnet.lit_str s = ok v ∧ v.val.map (·.val) = s.val.map (·.val) := by
  obtain ⟨v, hv, hvv⟩ := lit_str_loop_ok s (alloc.vec.Vec.new U32) 0#usize (by simp) (by simp)
  exact ⟨v, hv, by simpa using hvv⟩

theorem vstrS_of_vals (v : alloc.vec.Vec U32) (l : List Nat) (h : v.val.map (·.val) = l) :
    vstrS v = String.ofList (l.map Char.ofNat) := by
  rw [← h, vstrS, List.map_map]; rfl

theorem VValid_of_vals (v : alloc.vec.Vec U32) (l : List Nat) (h : v.val.map (·.val) = l)
    (hl : ∀ n ∈ l, n.isValidChar) : VValid v := by
  intro u hu; apply hl; rw [← h]; exact List.mem_map_of_mem hu

/-! ## `int_to_str` -/

/-- decimal digits, least significant first (`[]` for 0) -/
def dl (n : Nat) : List Nat := if n = 0 then [] else n % 10 :: dl (n / 10)
termination_by n
decreasing_by omega

theorem dl_lt (n : Nat) : ∀ d ∈ dl n, d < 10 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [dl]; split
    · simp
    · intro d hd; simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · omega
      · exact ih (n / 10) (by omega) d hd

theorem dl_length (n : Nat) (h : n < 2^128) : (dl n).length ≤ 39 := by
  have : ∀ k n, n < 10^k → (dl n).length ≤ k := by
    intro k; induction k with
    | zero => intro n h; rw [dl]; simp at h; simp [h]
    | succ k ih => intro n h; rw [dl]; split
                   · simp
                   · simp only [List.length_cons]; have := ih (n / 10) (by rw [Nat.pow_succ] at h; omega); omega
  exact this 39 n (by omega)

theorem toDigitsCore_dl (n : Nat) (hn : 0 < n) : ∀ fuel ds, n < fuel →
    Nat.toDigitsCore 10 fuel n ds = ((dl n).map Nat.digitChar).reverse ++ ds := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro fuel ds hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [Nat.toDigitsCore, dl, if_neg (show ¬ n = 0 by omega)]
    by_cases h0 : n / 10 = 0
    · rw [if_pos h0, h0, dl]; simp
    · rw [if_neg h0]
      rw [ih (n / 10) (by omega) (by omega) f _ (by omega)]
      simp

theorem toDigits_dl (n : Nat) (hn : 0 < n) : Nat.toDigits 10 n = ((dl n).map Nat.digitChar).reverse := by
  rw [Nat.toDigits, toDigitsCore_dl n hn _ _ (by omega), List.append_nil]

/-- the Rust digit character `'0' + d` -/
def dU (d : Nat) : U32 := ⟨BitVec.ofNat 32 (48 + d)⟩

theorem dU_val (d : Nat) (h : d < 10) : (dU d).val = 48 + d := by
  show (BitVec.ofNat 32 (48 + d)).toNat = _; rw [BitVec.toNat_ofNat]; omega

theorem chOf_dU (d : Nat) (h : d < 10) : chOf (dU d) = Nat.digitChar d := by
  unfold chOf; rw [dU_val d h]
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem its_loop0_ok : ∀ (n : Nat) (m : I128) (digits : alloc.vec.Vec U32), m.val = n →
    digits.val.length + (dl n).length < 2^32 - 1 →
    ∃ d1, beatmap.mod_settings.int_to_str_loop0 m digits = ok d1 ∧ d1.val = digits.val ++ (dl n).map dU := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m digits hm hlen
    have hb := m.hBounds
    unfold beatmap.mod_settings.int_to_str_loop0
    rw [loop_unfold]
    by_cases hpos : 0 < n
    · have hgt : m > 0#i128 := by show (0#i128).val < m.val; simp; omega
      obtain ⟨r, hr, hrv⟩ := eq_ok_of_spec (IScalar.rem_spec m (y := 10#i128) (by simp))
      obtain ⟨q, hq, hqv⟩ := IScalar.div_spec (x := m) (y := 10#i128) (by simp) (by simp [IScalar.min] <;> omega)
      have h10 : ((10#i128 : I128).val) = 10 := by simp
      have hrv' : r.val = ((n % 10 : Nat) : Int) := by
        rw [hrv, hm, h10, Int.tmod_eq_emod_of_nonneg (Int.natCast_nonneg n)]; omega
      have hqv' : q.val = ((n / 10 : Nat) : Int) := by
        rw [hqv, hm, h10, Int.tdiv_eq_ediv_of_nonneg (Int.natCast_nonneg n)]; omega
      have hc : (IScalar.hcast .U32 r).val = n % 10 := by rw [IScalar.hcast_val_eq, hrv']; simp; omega
      have h48 : (48#u32 : U32).val = 48 := by simp
      have hmax : (48#u32 : U32).val + (IScalar.hcast .U32 r).val ≤ UScalar.max .U32 := by
        simp only [UScalar.max, h48]; rw [IScalar.hcast_val_eq, hrv']; simp; omega
      obtain ⟨a, ha, hav⟩ := eq_ok_of_spec (UScalar.add_spec hmax)
      have hae : a = dU (n % 10) := by
        apply UScalar.eq_of_val_eq; rw [hav, hc, dU_val (n % 10) (by omega), h48]
      obtain ⟨o1, ho1, ho1v⟩ := push_eq digits a (by have := usize_ge_32; omega)
      have hdl : (dl n).length = (dl (n / 10)).length + 1 := by rw [dl.eq_1 n, if_neg (by omega)]; rfl
      obtain ⟨d1, hd1, hd1v⟩ := ih (n / 10) (by omega) q o1 hqv' (by rw [ho1v]; simp; omega)
      refine ⟨d1, ?_, ?_⟩
      · have hbody : beatmap.mod_settings.int_to_str_loop0.body m digits = ok (ControlFlow.cont (q, o1)) := by
          simp only [beatmap.mod_settings.int_to_str_loop0.body, hgt, ite_true, hr, bind_ok, lift, ha, ho1, hq]
        dsimp only
        rw [hbody, bind_ok]
        unfold beatmap.mod_settings.int_to_str_loop0 at hd1
        exact hd1
      · rw [hd1v, ho1v, hae, dl.eq_1 n, if_neg (show ¬ n = 0 by omega)]; simp
    · have hgt : ¬ m > 0#i128 := by show ¬ (0#i128).val < m.val; simp; omega
      refine ⟨digits, by simp [beatmap.mod_settings.int_to_str_loop0.body, hgt], ?_⟩
      rw [show n = 0 by omega, dl]; simp

theorem its_loop1_ok (d : alloc.vec.Vec U32) : ∀ (k : Nat) (out : alloc.vec.Vec U32) (kk : Usize), kk.val = k →
    k ≤ d.val.length → out.val.length + k ≤ 2^32 - 1 →
    ∃ o, beatmap.mod_settings.int_to_str_loop1 d out kk = ok o ∧ o.val = out.val ++ (d.val.take k).reverse := by
  intro k
  induction k with
  | zero =>
    intro out kk hk _ _
    have hgt : ¬ kk > 0#usize := by show ¬ (0#usize).val < kk.val; simp; omega
    refine ⟨out, ?_, by simp⟩
    unfold beatmap.mod_settings.int_to_str_loop1; rw [loop_unfold]
    simp [beatmap.mod_settings.int_to_str_loop1.body, hgt]
  | succ k ih =>
    intro out kk hk hkl hlen
    have hgt : kk > 0#usize := by show (0#usize).val < kk.val; simp; omega
    obtain ⟨k1, hk1, hk1v, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := kk) (y := 1#usize) (by simp; omega))
    simp at hk1v
    have hl : k1.val < d.val.length := by omega
    obtain ⟨o1, ho1, ho1v⟩ := push_eq out (d.val[k1.val]'hl) (by have := usize_ge_32; omega)
    obtain ⟨o, ho, hov⟩ := ih o1 k1 (by omega) (by omega) (by rw [ho1v]; simp; omega)
    refine ⟨o, ?_, ?_⟩
    · unfold beatmap.mod_settings.int_to_str_loop1; rw [loop_unfold]
      have hbody : beatmap.mod_settings.int_to_str_loop1.body d out kk = ok (ControlFlow.cont (o1, k1)) := by
        simp only [beatmap.mod_settings.int_to_str_loop1.body, hgt, ite_true, hk1, bind_ok, vec_index_eq' d k1 hl, ho1]
      dsimp only
      rw [hbody, bind_ok]
      unfold beatmap.mod_settings.int_to_str_loop1 at ho
      exact ho
    · rw [hov, ho1v, show k + 1 = k1.val + 1 by omega, take_succ_get d.val k1.val hl, show k = k1.val by omega]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc, List.singleton_append]

theorem chOf_45 : chOf 45#u32 = '-' := by decide
theorem chOf_48 : chOf 48#u32 = '0' := by decide

theorem toDigits_chars (n : Nat) :
    Nat.toDigits 10 n = (if n = 0 then ['0'] else ((dl n).map Nat.digitChar).reverse) := by
  split
  · rename_i h; subst h; decide
  · exact toDigits_dl n (by omega)

/-- `int_to_str` (no spec def): `toString` of the integer. -/
theorem beatmap.mod_settings.int_to_str_refines (v : I64) :
    ∃ w, beatmap.mod_settings.int_to_str v = ok w ∧ vstrS w = toString v.val ∧ VValid w ∧ w.val.length ≤ 41 := by
  have hb := v.hBounds
  have hb' : -2^63 ≤ v.val ∧ v.val < 2^63 := by simpa [IScalarTy.numBits] using hb
  -- `m = |v|` as an i128
  obtain ⟨m, hm, hmv⟩ : ∃ m : I128, (if v < 0#i64 then (do let i ← lift (IScalar.cast .I128 v); -. i)
      else ok (IScalar.cast .I128 v)) = ok m ∧ m.val = (v.val.natAbs : Int) := by
    have hc : (IScalar.cast .I128 v).val = v.val := by
      rw [IScalar.cast_val_eq]; simp [IScalarTy.numBits] at hb ⊢; try omega
    by_cases hneg : v < 0#i64
    · have hneg' : v.val < 0 := by simpa using hneg
      obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (IScalar.neg_step (IScalar.cast .I128 v)
        (by intro h; rw [hc] at h; simp [IScalar.min, IScalarTy.numBits, I128.min_eq] at h; omega))
      refine ⟨z, ?_, by rw [hzv, hc]; omega⟩
      simp only [hneg, ite_true, lift, bind_ok]; exact hz
    · have hneg' : ¬ v.val < 0 := by simpa using hneg
      exact ⟨IScalar.cast .I128 v, by simp [hneg], by rw [hc]; omega⟩
  have hn128 : v.val.natAbs < 2^128 := by omega
  have hdl := dl_length _ hn128
  -- initial digit list
  obtain ⟨d0, hd0, hd0v⟩ : ∃ d0, (if m = 0#i128 then alloc.vec.Vec.push (alloc.vec.Vec.new U32) 48#u32
      else ok (alloc.vec.Vec.new U32)) = ok d0 ∧
      d0.val = (if v.val.natAbs = 0 then [48#u32] else []) := by
    by_cases hz : v.val.natAbs = 0
    · have : m = 0#i128 := by apply IScalar.eq_of_val_eq; rw [hmv, hz]; simp
      obtain ⟨w, hw, hwv⟩ := push_eq (alloc.vec.Vec.new U32) 48#u32 (by simp; have := usize_ge_32; omega)
      exact ⟨w, by simp [this, hw], by rw [hwv, if_pos hz]; simp⟩
    · have : ¬ m = 0#i128 := by intro h; have := congrArg IScalar.val h; rw [hmv] at this; simp at this; omega
      exact ⟨alloc.vec.Vec.new U32, by simp [this], by rw [if_neg hz]; rfl⟩
  obtain ⟨d1, hd1, hd1v⟩ := its_loop0_ok v.val.natAbs m d0 hmv
    (by rw [hd0v]; split <;> simp <;> omega)
  obtain ⟨o0, ho0, ho0v⟩ : ∃ o0, (if v < 0#i64 then alloc.vec.Vec.push (alloc.vec.Vec.new U32) 45#u32
      else ok (alloc.vec.Vec.new U32)) = ok o0 ∧ o0.val = (if v.val < 0 then [45#u32] else []) := by
    by_cases hneg : v < 0#i64
    · have hneg' : v.val < 0 := by simpa using hneg
      obtain ⟨w, hw, hwv⟩ := push_eq (alloc.vec.Vec.new U32) 45#u32 (by simp; have := usize_ge_32; omega)
      exact ⟨w, by simp [hneg, hw], by rw [hwv, if_pos hneg']; simp⟩
    · have hneg' : ¬ v.val < 0 := by simpa using hneg
      exact ⟨alloc.vec.Vec.new U32, by simp [hneg], by rw [if_neg hneg']; rfl⟩
  have hd1len : d1.val.length ≤ 40 := by
    rw [hd1v, hd0v]; split <;> simp <;> omega
  obtain ⟨o, ho, hov⟩ := its_loop1_ok d1 d1.val.length o0 (alloc.vec.Vec.len d1) (by simp) le_rfl
    (by rw [ho0v]; split <;> simp <;> omega)
  refine ⟨o, ?_, ?_, ?_, ?_⟩
  · unfold beatmap.mod_settings.int_to_str
    simp only [hm, bind_ok, hd0, hd1, ho0, ho]
  · have e : ((dl v.val.natAbs).map dU).map chOf = (dl v.val.natAbs).map Nat.digitChar := by
      rw [List.map_map]; apply List.map_congr_left; intro d hd; exact chOf_dU d (dl_lt _ d hd)
    have hchars : o.val.map chOf = (if v.val < 0 then ['-'] else []) ++ Nat.toDigits 10 v.val.natAbs := by
      rw [hov, ho0v, List.take_length, hd1v, hd0v, toDigits_chars]
      by_cases hz : v.val.natAbs = 0 <;> by_cases hneg : v.val < 0 <;>
        simp only [hz, hneg, if_true, if_false, ite_true, ite_false, List.map_append, List.map_cons, List.map_nil,
          List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.append_nil,
          List.map_reverse, e, chOf_45, chOf_48, List.singleton_append, Bool.false_eq_true, decide_false, decide_true]
      all_goals (rw [dl]; simp)
    rw [vstrS, hchars, Int.toString_eq_repr, Int.repr_eq_ite]
    by_cases hneg : v.val < 0
    · rw [if_pos hneg, if_neg (by omega), Nat.repr, show (-v.val).toNat = v.val.natAbs by omega]
      simp
    · rw [if_neg hneg, if_pos (by omega), Nat.repr, show v.val.toNat = v.val.natAbs by omega]
      simp
  · intro u hu
    rw [hov, ho0v, List.take_length, hd1v, hd0v] at hu
    simp only [List.mem_append, List.mem_reverse, List.mem_map] at hu
    rcases hu with h | h | ⟨d, hd, rfl⟩
    · split at h <;> simp at h; subst h; decide
    · split at h <;> simp at h; subst h; decide
    · rw [dU_val d (dl_lt _ d hd)]; unfold Nat.isValidChar; have := dl_lt _ d hd; omega
  · rw [hov, ho0v, List.take_length]; simp only [List.length_append, List.length_reverse]
    split <;> simp <;> omega

/-! ## `enumString` -/

theorem clone_vec_u32 (s : alloc.vec.Vec U32) : alloc.vec.CloneVec.clone core.clone.CloneU32 s = ok s := by
  obtain ⟨s', hs, hss⟩ := eq_ok_of_spec (Slice.clone_spec (clone := core.clone.CloneU32.clone) (s := s.slice)
    (by intro x _; rfl))
  rw [alloc.vec.CloneVec.clone, hs, ← hss]; simp

theorem beatmap.mod_settings.enum_string_refines (j : beatmap.mod_settings.JsonVal) (hj : JOk j) :
    ∃ r, beatmap.mod_settings.enum_string j = ok r ∧ r.map vstrS = Settings.enumString (jvS j) ∧
      ∀ w, r = some w → VValid w ∧ (w.val.length ≤ 41 ∨ j = .Str w) := by
  cases j with
  | Long v =>
    obtain ⟨w, hw, hwv, hwok, hwl⟩ := beatmap.mod_settings.int_to_str_refines v
    exact ⟨some w, by simp [beatmap.mod_settings.enum_string, hw], by simp [Settings.enumString, jvS, hwv],
      by intro w' h; cases h; exact ⟨hwok, Or.inl hwl⟩⟩
  | Big => exact ⟨none, rfl, rfl, by simp⟩
  | Null => exact ⟨none, rfl, rfl, by simp⟩
  | Str s =>
    exact ⟨some s, by simp [beatmap.mod_settings.enum_string, clone_vec_u32], rfl, by intro w h; cases h; exact ⟨hj.1, Or.inr rfl⟩⟩
  | Bool b =>
    cases b
    · (obtain ⟨w, hw, hwv⟩ := beatmap.dotnet.lit_str_refines (Array.to_slice (Array.make 5#usize [70#u8, 97#u8, 108#u8, 115#u8, 101#u8] (by simp)))
       have hwv' : w.val.map (·.val) = [70, 97, 108, 115, 101] := by rw [hwv]; simp [Array.to_slice, Array.make]
       refine ⟨some w, ?_, ?_, ?_⟩
       · simp only [beatmap.mod_settings.enum_string, lift, bind_ok, hw]; simp
       · simp only [Option.map_some, Settings.enumString, jvS, vstrS_of_vals w _ hwv']; decide
       · intro w' h; cases h; exact ⟨VValid_of_vals w _ hwv' (by decide), Or.inl (by have := congrArg List.length hwv'; simp at this; omega)⟩)
    · (obtain ⟨w, hw, hwv⟩ := beatmap.dotnet.lit_str_refines (Array.to_slice (Array.make 4#usize [84#u8, 114#u8, 117#u8, 101#u8] (by simp)))
       have hwv' : w.val.map (·.val) = [84, 114, 117, 101] := by rw [hwv]; simp [Array.to_slice, Array.make]
       refine ⟨some w, ?_, ?_, ?_⟩
       · simp only [beatmap.mod_settings.enum_string, lift, bind_ok, hw]; simp
       · simp only [Option.map_some, Settings.enumString, jvS, vstrS_of_vals w _ hwv']; decide
       · intro w' h; cases h; exact ⟨VValid_of_vals w _ hwv' (by decide), Or.inl (by have := congrArg List.length hwv'; simp at this; omega)⟩)
  | Double v =>
    have hD : beatmap.mod_settings.D1E15 = ok (1e15 : F64) := by
      simp [beatmap.mod_settings.D1E15, float.F64.from_bits] <;> decide
    by_cases hnan : v.isNaN = true
    · exact ⟨none, by simp [beatmap.mod_settings.enum_string, float.F64.is_nan, hnan], by
        simp [Settings.enumString, jvS, hnan], by simp⟩
    by_cases hinf : v.isInf = true
    · exact ⟨none, by simp [beatmap.mod_settings.enum_string, float.F64.is_nan, hnan, net.basic.f64_is_inf_refines,
        hinf], by simp [Settings.enumString, jvS, hnan, hinf], by simp⟩
    by_cases htr : (F64.truncate v == v) = true
    swap
    · exact ⟨none, by simp [beatmap.mod_settings.enum_string, float.F64.is_nan, hnan, net.basic.f64_is_inf_refines,
        hinf, float.F64.trunc, float.F64.eq, htr], by simp [Settings.enumString, jvS, hnan, hinf, htr], by simp⟩
    by_cases hab : F64.abs v < 1e15
    swap
    · exact ⟨none, by simp [beatmap.mod_settings.enum_string, float.F64.is_nan, hnan, net.basic.f64_is_inf_refines,
        hinf, float.F64.trunc, float.F64.eq, htr, float.F64.abs, hD, float.F64.lt, hab],
        by simp [Settings.enumString, jvS, hnan, hinf, htr, hab], by simp⟩
    -- the integral case
    generalize hi : (IScalar.mk (ty := .I64) (F64.toInt64 v).toBitVec) = i
    have hiv : i.val = (F64.toInt64 v).toInt := by rw [← hi]; rfl
    have hpre : beatmap.mod_settings.enum_string (.Double v) = (do
        if i = 0#i64 then do
          let i1 ← float.F64.to_bits v
          let i2 ← i1 >>> 63#i32
          if i2 = 1#u64 then do
            let s ← lift (Array.to_slice (Array.make 2#usize [45#u8, 48#u8]))
            let v1 ← beatmap.dotnet.lit_str s
            ok (some v1)
          else do let v1 ← beatmap.mod_settings.int_to_str i; ok (some v1)
        else do let v1 ← beatmap.mod_settings.int_to_str i; ok (some v1)) := by
      simp [beatmap.mod_settings.enum_string, float.F64.is_nan, hnan, net.basic.f64_is_inf_refines,
        hinf, float.F64.trunc, float.F64.eq, htr, float.F64.abs, hD, float.F64.lt, hab, float.F64.to_i64_sat, hi]
    have hspec : Settings.enumString (jvS (.Double v)) =
        some (if (F64.toInt64 v).toInt == 0 && v.toBits >>> 63 == 1 then "-0" else toString (F64.toInt64 v).toInt) := by
      simp [Settings.enumString, jvS, hnan, hinf, htr, hab]
    rw [hpre, hspec]
    obtain ⟨w, hw, hwv, hwok, hwl⟩ := beatmap.mod_settings.int_to_str_refines i
    by_cases hz : i = 0#i64
    · have hz' : (F64.toInt64 v).toInt = 0 := by rw [← hiv, hz]; rfl
      obtain ⟨z, hzs, hzv, _⟩ := eq_ok_of_spec (UScalar.ShiftRight_IScalar_spec
        (⟨(v.toBits).toBitVec⟩ : U64) (63#i32) (by simp) (by simp))
      have hzv' : z.val = v.toBits.toNat >>> 63 := by rw [hzv]; simp; rfl
      have hsh : (v.toBits >>> 63 == 1) = decide (v.toBits.toNat >>> 63 = 1) := by
        rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, decide_eq_true_eq]
        constructor
        · intro h; have := congrArg UInt64.toNat h; simpa [UInt64.toNat_shiftRight] using this
        · intro h; apply UInt64.toNat_inj.mp; simp [UInt64.toNat_shiftRight, h]
      have hzb : (z = 1#u64) ↔ v.toBits.toNat >>> 63 = 1 := by
        rw [← hzv']; exact ⟨fun h => by rw [h]; rfl, fun h => UScalar.eq_of_val_eq (by rw [h]; rfl)⟩
      rw [if_pos hz, f64_to_bits_eq v (by simpa using hnan), bind_ok, hzs, bind_ok]
      by_cases hs : v.toBits.toNat >>> 63 = 1
      · obtain ⟨w0, hw0, hw0v⟩ := beatmap.dotnet.lit_str_refines (Array.to_slice (Array.make 2#usize [45#u8, 48#u8] (by simp)))
        have hw0v' : w0.val.map (·.val) = [45, 48] := by rw [hw0v]; simp [Array.to_slice, Array.make]
        refine ⟨some w0, by simp [hzb.mpr hs, lift, hw0], ?_, ?_⟩
        · simp only [Option.map_some, hz', hsh, hs, vstrS_of_vals w0 _ hw0v']; decide
        · intro w' h; cases h; exact ⟨VValid_of_vals w0 _ hw0v' (by decide), Or.inl (by have := congrArg List.length hw0v'; simp at this; omega)⟩
      · refine ⟨some w, by simp [show ¬ z = 1#u64 from fun h => hs (hzb.mp h), hw], ?_, by intro w' h; cases h; exact ⟨hwok, Or.inl hwl⟩⟩
        simp [hsh, hs, hwv, hiv]
    · have hz' : ¬ (F64.toInt64 v).toInt = 0 := by rw [← hiv]; intro h; exact hz (IScalar.eq_of_val_eq (by simpa using h))
      refine ⟨some w, by simp [hz, hw], ?_, by intro w' h; cases h; exact ⟨hwok, Or.inl hwl⟩⟩
      simp [hz', hwv, hiv]

end OsuProofs
