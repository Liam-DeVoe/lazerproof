/-
`beatmap::dotnet` (Rust) refines `OsuModel.Beatmap` .NET helpers (`DotNet.lean`): `CompareTo`,
`%`, whitespace predicates, `List.Insert`, binary search, sorts, string helpers.
-/
import OsuProofs.Beatmap.CharTable
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

theorem beatmap.dotnet.is_white_space_refines (c : U32) (h : c.val.isValidChar) :
    beatmap.dotnet.is_white_space c = ok (isWhiteSpace (chOf c)) := by
  simp [beatmap.dotnet.is_white_space, net.parse.is_unicode_white_space_refines c h, isWhiteSpace]

theorem beatmap.dotnet.nat_sub_refines (a b : Usize) :
    ∃ r, beatmap.dotnet.nat_sub a b = ok r ∧ r.val = a.val - b.val := by
  unfold beatmap.dotnet.nat_sub
  by_cases h : b.val ≤ a.val
  · have h' : a >= b := h
    obtain ⟨r, hr, hrv, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := a) (y := b) h)
    exact ⟨r, by simp [h', hr], hrv⟩
  · have h' : ¬ a >= b := h
    exact ⟨0#usize, by simp [h'], by simp; omega⟩

theorem beatmap.dotnet.compare_f64_refines (a b : F64) :
    ∃ r, beatmap.dotnet.compare_f64 a b = ok r ∧ r.val = compareF64 a b := by
  unfold beatmap.dotnet.compare_f64 compareF64
  by_cases h1 : a < b
  · exact ⟨(-1)#i32, by simp [h1], by simp [h1]⟩
  · by_cases h2 : b < a
    · exact ⟨1#i32, by simp [h1, h2], by simp [h1, h2]⟩
    · by_cases h3 : (a == b) = true
      · exact ⟨0#i32, by simp [h1, h2, h3], by simp [h1, h2, h3]⟩
      · cases h4 : a.isNaN <;> cases h5 : b.isNaN
        · exact ⟨1#i32, by simp [h1, h2, h3, h4, h5, float.F64.is_nan], by simp [h1, h2, h3, h4, h5]⟩
        · exact ⟨1#i32, by simp [h1, h2, h3, h4, h5, float.F64.is_nan], by simp [h1, h2, h3, h4, h5]⟩
        · exact ⟨(-1)#i32, by simp [h1, h2, h3, h4, h5, float.F64.is_nan], by simp [h1, h2, h3, h4, h5]⟩
        · exact ⟨0#i32, by simp [h1, h2, h3, h4, h5, float.F64.is_nan], by simp [h1, h2, h3, h4, h5]⟩

/-- `fmod_f64` is the trusted primitive `float.F64.fmod`, which is *defined* as the spec `fmodF64`. -/
theorem beatmap.dotnet.fmod_f64_refines (a b : F64) :
    beatmap.dotnet.fmod_f64 a b = ok (fmodF64 a b) := rfl

theorem beatmap.dotnet.fmod_f32_refines (a b : F32) :
    beatmap.dotnet.fmod_f32 a b = ok (fmodF32 a b) := by
  simp [beatmap.dotnet.fmod_f32, beatmap.dotnet.fmod_f64_refines, fmodF32, float.F32.to_f64, float.F64.to_f32]

theorem f64_isInf_beq (x : F64) : (x == F64.posInf || x == F64.negInf) = x.isInf := by
  simp only [BEq.beq, Float.beq, Float.isInf, Float.Model.beq, Float.Model.isInf, F64.posInf, F64.negInf]
  have e1 : Float.inf.toModel.unpack = .infinity .positive := rfl
  have e2 : (-Float.inf).toModel.unpack = .infinity .negative := rfl
  rw [e1, e2]
  generalize x.toModel.unpack = u
  cases u with
  | infinity s => cases s <;> rfl
  | _ => simp [Float.Model.UnpackedFloat.beq, Float.Model.UnpackedFloat.compare, Float.Model.UnpackedFloat.isInf] <;> rfl

theorem nanN_eq : F64.ofBitsN Fmt.f64.encNaN = F64.nan := by decide

theorem dn_F64_ONE : beatmap.dotnet.F64_ONE = ok (1 : F64) := by simp [beatmap.dotnet.F64_ONE] <;> decide
theorem dn_F64_ZERO : beatmap.dotnet.F64_ZERO = ok (0 : F64) := by simp [beatmap.dotnet.F64_ZERO] <;> decide

theorem beatmap.dotnet.fmod1_refines (x : F64) : beatmap.dotnet.fmod1 x = ok (fmod1 x) := by
  unfold beatmap.dotnet.fmod1 fmod1
  cases hn : x.isNaN
  · simp only [float.F64.is_nan, hn, bind_ok, Bool.false_eq_true, ite_false, Bool.false_or,
      net.basic.f64_is_inf_refines, f64_isInf_beq]
    cases hi : x.isInf
    · simp only [ite_false, Bool.false_eq_true, float.F64.abs, dn_F64_ONE, dn_F64_ZERO, bind_ok, float.F64.lt,
        float.F64.trunc, float.F64.sub, float.F64.eq]
      by_cases h1 : F64.abs x < 1
      · simp [h1]
      · have h0 : (0 : F64).isNaN = false := by decide
        simp [h1, net.basic.f64_copy_sign_refines _ _ h0 hn]
    · simp [nanN_eq]
  · simp [float.F64.is_nan, hn, nanN_eq]

theorem beatmap.dotnet.log2_refines (n : Usize) :
    ∃ r, beatmap.dotnet.log2 n = ok r ∧ r.val = IntroSort.log2 n.val := by
  have hn := n.hBounds
  have hl : Nat.log2 n.val < 2^32 - 1 := by
    have := Nat.log2_le_self n.val
    by_cases h0 : n.val = 0
    · simp [h0]
    · have h64 : n.val < 2^64 := by
        have : 2^UScalarTy.Usize.numBits ≤ 2^64 := by
          rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.Usize_numBits_eq, h]
        omega
      have := (Nat.log2_lt h0).mpr h64
      omega
  unfold beatmap.dotnet.log2 beatmap.dotnet.log2_loop IntroSort.log2
  refine loop_ok _ (fun (x : Usize × Usize) => x.2.val) (fun (x : Usize × Usize) => x.1.val + Nat.log2 x.2.val = Nat.log2 n.val)
    (fun (r : Usize) => r.val = Nat.log2 n.val) ?_ (0#usize, n) (by simp)
  rintro ⟨r, m⟩ hx
  dsimp only at hx ⊢
  by_cases hm : 1 < m.val
  · right
    have hm' : m > 1#usize := hm
    obtain ⟨m1, hm1, hm1v⟩ := eq_ok_of_spec (Usize.div_spec m (y := 2#usize) (by simp))
    have hd := Nat.log2_def m.val
    have hc2 : 2 ≤ m.val := by omega
    simp only [hc2, ite_true] at hd
    simp at hm1v
    obtain ⟨r1, hr1, hr1v⟩ := usize_add_one r (by have := usize_ge_32; omega)
    exact ⟨(r1, m1), by simp [beatmap.dotnet.log2_loop.body, hm', hm1, hr1], by
      dsimp only; rw [hr1v, hm1v]; omega, by dsimp only; rw [hm1v]; omega⟩
  · left
    have hm' : ¬ m > 1#usize := hm
    refine ⟨r, by simp [beatmap.dotnet.log2_loop.body, hm'], ?_⟩
    have hc2 : ¬ 2 ≤ m.val := by omega
    have : Nat.log2 m.val = 0 := by rw [Nat.log2_def]; simp only [hc2, ite_false]
    omega

/-! ## `List<T>.Insert` -/

theorem vec_index_eq' {α} (v : alloc.vec.Vec α) (i : Usize) (h : i.val < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok (v.val[i.val]'h) := by
  rw [alloc.vec.Vec.index_slice_index]
  obtain ⟨x, hx, hx'⟩ := eq_ok_of_spec (alloc.vec.Vec.index_usize_spec v i h)
  rw [hx, hx']

theorem vec_index_usize_eq {α} (v : alloc.vec.Vec α) (i : Usize) (h : i.val < v.val.length) :
    alloc.vec.Vec.index_usize v i = ok (v.val[i.val]'h) := by
  obtain ⟨x, hx, hx'⟩ := eq_ok_of_spec (alloc.vec.Vec.index_usize_spec v i h)
  rw [hx, hx']

theorem vec_index_mut_eq {α} (v : alloc.vec.Vec α) (i : Usize) (h : i.val < v.val.length) :
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) v i = ok (v.val[i.val]'h, alloc.vec.Vec.set v i) := by
  rw [alloc.vec.Vec.index_mut_slice_index]
  obtain ⟨⟨a, b⟩, hx, hx1, hx2⟩ := eq_ok_of_spec (alloc.vec.Vec.index_mut_usize_spec v i h)
  rw [hx, hx1, hx2]

theorem insert_at_loop {T : Type} (C : core.clone.Clone T) (hC : ∀ x, C.clone x = ok x)
    (v : List T) (k : Usize) :
    ∀ (w : alloc.vec.Vec T) (i : Usize), k.val ≤ i.val → i.val ≤ v.length →
      (∃ d, w.val = v.take i.val ++ d :: v.drop i.val) →
      ∃ w', beatmap.dotnet.insert_at_loop C w k i = ok w' ∧ ∃ d, w'.val = v.take k.val ++ d :: v.drop k.val := by
  intro w i hki hiv hw
  unfold beatmap.dotnet.insert_at_loop
  refine loop_ok _ (fun (x : alloc.vec.Vec T × Usize) => x.2.val)
    (fun (x : alloc.vec.Vec T × Usize) => k.val ≤ x.2.val ∧ x.2.val ≤ v.length ∧
      ∃ d, x.1.val = v.take x.2.val ++ d :: v.drop x.2.val)
    (fun (w' : alloc.vec.Vec T) => ∃ d, w'.val = v.take k.val ++ d :: v.drop k.val) ?_ (w, i) ⟨hki, hiv, hw⟩
  rintro ⟨w, i⟩ ⟨hki, hiv, d, hw⟩
  dsimp only at hki hiv hw ⊢
  by_cases hik : k.val < i.val
  · right
    have hik' : i > k := hik
    obtain ⟨i1, hi1, hi1v0, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := i) (y := 1#usize) (by simp; omega))
    have hi1v : i1.val = i.val - 1 := by rw [hi1v0]; simp
    have hwl : w.val.length = v.length + 1 := by rw [hw]; simp; omega
    have hl1 : i1.val < w.val.length := by omega
    have hl2 : i.val < w.val.length := by omega
    have hget : w.val[i1.val]'hl1 = v[i.val - 1]'(by omega) := by
      simp only [hw, hi1v]
      rw [List.getElem_append_left (by simp; omega)]
      simp
    refine ⟨(alloc.vec.Vec.set w i (v[i.val - 1]'(by omega)), i1), ?_, ⟨by dsimp only; omega, by dsimp only; omega, ?_⟩,
      by dsimp only; omega⟩
    · simp [beatmap.dotnet.insert_at_loop.body, hik', hi1, vec_index_usize_eq w i1 hl1, hget, hC, vec_index_mut_eq w i hl2]
    · refine ⟨v[i.val - 1]'(by omega), ?_⟩
      dsimp only
      rw [alloc.vec.Vec.set_val_eq, hw, hi1v]
      have e1 : v.take i.val = v.take (i.val - 1) ++ [v[i.val - 1]'(by omega)] := by
        have e : i.val = (i.val - 1) + 1 := by omega
        conv_lhs => rw [e]
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; simp
      have e2 : v.drop (i.val - 1) = v[i.val - 1]'(by omega) :: v.drop i.val := by
        rw [List.drop_eq_getElem_cons (by omega)]; congr 2; omega
      rw [e2, e1]; simp only [List.append_assoc, List.singleton_append]
      rw [List.set_append_right _ _ (by simp)]
      have hl : (v.take (i.val - 1)).length = i.val - 1 := by simp; try omega
      rw [hl]
      have h1 : i.val - (i.val - 1) = 1 := by omega
      rw [h1]; rfl
  · left
    have hik' : ¬ i > k := hik
    refine ⟨w, by simp [beatmap.dotnet.insert_at_loop.body, hik'], ⟨d, ?_⟩⟩
    have : i.val = k.val := by omega
    rw [← this]; exact hw

theorem insertIdx_take_drop {α} (x : α) : ∀ (l : List α) (i : Nat), i ≤ l.length →
    l.insertIdx i x = l.take i ++ x :: l.drop i
  | [], 0, _ => rfl
  | [], _+1, h => by simp at h
  | _ :: _, 0, _ => by simp [List.insertIdx_zero]
  | a :: l, i+1, h => by
    rw [List.insertIdx_succ_cons, insertIdx_take_drop x l i (by simp at h; omega)]; simp

theorem beatmap.dotnet.insert_at_refines {T : Type} (C : core.clone.Clone T) (hC : ∀ x, C.clone x = ok x)
    (v : alloc.vec.Vec T) (k : Usize) (x : T) (hk : k.val ≤ v.val.length) (hl : v.val.length < Usize.max) :
    ∃ w, beatmap.dotnet.insert_at C v k x = ok w ∧ w.val = v.val.insertIdx k.val x := by
  obtain ⟨v1, hv1, hv1v⟩ := push_eq v x hl
  have hlen : (alloc.vec.Vec.len v1).val = v.val.length + 1 := by simp [hv1v]
  obtain ⟨i1, hi1, hi1v0, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := alloc.vec.Vec.len v1) (y := 1#usize) (by simp [hlen]))
  have hi1v : i1.val = v.val.length := by rw [hi1v0]; simp [hlen]
  obtain ⟨w2, hw2, d, hw2v⟩ := insert_at_loop C hC v.val k v1 i1 (by omega) (by omega) ⟨x, by rw [hv1v, hi1v]; simp⟩
  have hw2l : k.val < w2.val.length := by rw [hw2v]; simp; omega
  refine ⟨alloc.vec.Vec.set w2 k x, ?_, ?_⟩
  · simp only [beatmap.dotnet.insert_at, hC, hv1, hi1, hw2, bind_ok, vec_index_mut_eq w2 k hw2l]; rfl
  · rw [alloc.vec.Vec.set_val_eq, hw2v, insertIdx_take_drop x _ _ hk]
    rw [List.set_append_right _ _ (by simp)]
    have hl2 : (v.val.take k.val).length = k.val := by simp; omega
    rw [hl2, Nat.sub_self]; rfl

end OsuProofs
