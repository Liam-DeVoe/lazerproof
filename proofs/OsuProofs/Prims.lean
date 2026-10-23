/-
Basic facts about the float primitives and the Aeneas-generated constants.
Everything here is proven (no axioms beyond Lean's + the trusted primitive identifications
in `Generated/{TypesExternal,FunsExternal}.lean`).
-/
import OsuProofs.Generated.Funs
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

/-- `ok` commutes with `if` (simp doesn't do this by itself). -/
@[simp] theorem ite_ok {α} (c : Prop) [Decidable c] (a b : α) :
    (if c then (ok a : Result α) else ok b) = ok (if c then a else b) := by
  split <;> rfl

theorem from_bits_eq (b : Std.U64) : float.F64.from_bits b = ok (Float.ofBits b.bv.toNat.toUInt64) := rfl

/-- Constants: `F64::from_bits(K)` is a spec literal iff the kernel says so. -/
theorem from_bits_lit (b : Std.U64) (x : Float) (h : Float.ofBits b.bv.toNat.toUInt64 = x) :
    float.F64.from_bits b = ok x := by rw [from_bits_eq, h]

/-! Aeneas helper lemmas: turn the library's Hoare triples into equations. -/

theorem eq_ok_of_spec {α} {m : Result α} {p : α → Prop} (h : WP.spec m p) : ∃ v, m = ok v ∧ p v := by
  cases m with
  | ret r => exact ⟨r, rfl, by simpa using h⟩
  | vis i k => simp at h
  | div => simp at h

theorem usize_add_one (i : Usize) (h : i.val + 1 ≤ Usize.max) :
    ∃ z, i + 1#usize = ok z ∧ z.val = i.val + 1 := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (Usize.add_spec (x := i) (y := 1#usize) (by simpa using h))
  exact ⟨z, hz, by simpa using hv⟩

theorem i64_add_one (i : I64) (h1 : -9223372036854775808 ≤ i.val + 1) (h2 : i.val + 1 ≤ 9223372036854775807) :
    ∃ z, i + 1#i64 = ok z ∧ z.val = i.val + 1 := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (I64.add_spec (x := i) (y := 1#i64)
    (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
  exact ⟨z, hz, by simpa using hv⟩

theorem i64_sub_one (i : I64) (h1 : -9223372036854775808 ≤ i.val - 1) (h2 : i.val - 1 ≤ 9223372036854775807) :
    ∃ z, i - 1#i64 = ok z ∧ z.val = i.val - 1 := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (I64.sub_spec (x := i) (y := 1#i64)
    (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
  exact ⟨z, hz, by simpa using hv⟩

theorem u32_sub_one (x : U32) (h : 1 ≤ x.val) : ∃ z, x - 1#u32 = ok z ∧ z.val = x.val - 1 := by
  obtain ⟨z, hz, hv, _⟩ := eq_ok_of_spec (U32.sub_spec (x := x) (y := 1#u32) (by simpa using h))
  exact ⟨z, hz, by simpa using hv⟩

theorem index_eq {α} (v : Slice α) (i : Usize) (h : i.val < v.val.length) :
    Slice.index_usize v i = ok (v.val[i.val]'h) := by
  obtain ⟨x, hx, hx'⟩ := eq_ok_of_spec (Slice.index_usize_spec v i h)
  rw [hx, hx']

theorem push_eq {α} (v : alloc.vec.Vec α) (x : α) (h : v.val.length < Usize.max) :
    ∃ w, alloc.vec.Vec.push v x = ok w ∧ w.val = v.val ++ [x] :=
  eq_ok_of_spec (alloc.vec.Vec.push_spec v x h)

/-- IEEE `==` true implies neither side is NaN (Lean core float model). -/
theorem beq_not_nan_left {a b : Float} (h : (a == b) = true) : a.isNaN = false := by
  revert h
  simp only [BEq.beq, Float.beq, Float.isNaN, Float.Model.beq, Float.Model.isNaN,
    Float.Model.UnpackedFloat.beq]
  generalize a.toModel.unpack = x
  generalize b.toModel.unpack = y
  cases x <;> cases y <;> simp [Float.Model.UnpackedFloat.compare, Float.Model.UnpackedFloat.isNaN] <;> rfl

theorem beq_not_nan_right {a b : Float} (h : (a == b) = true) : b.isNaN = false := by
  revert h
  simp only [BEq.beq, Float.beq, Float.isNaN, Float.Model.beq, Float.Model.isNaN,
    Float.Model.UnpackedFloat.beq]
  generalize a.toModel.unpack = x
  generalize b.toModel.unpack = y
  cases x <;> cases y <;> simp [Float.Model.UnpackedFloat.compare, Float.Model.UnpackedFloat.isNaN] <;> rfl

/-! ## `net.rs` = `OsuModel.Net.F64.{max,min,clamp}` -/

theorem max_refines (a b : F64) : net.max a b = ok (F64.max a b) := by
  unfold net.max F64.max
  by_cases h : (a == b) = true
  · have := beq_not_nan_right h
    simp [float.F64.eq, float.F64.is_negative, float.F64.is_nan, F64.isNaN, h, this]
  · simp only [Bool.not_eq_true] at h
    simp [float.F64.eq, float.F64.is_nan, float.F64.lt, F64.isNaN, h]
    split <;> simp_all

theorem min_refines (a b : F64) : net.min a b = ok (F64.min a b) := by
  unfold net.min F64.min
  by_cases h : (a == b) = true
  · have := beq_not_nan_left h
    simp [float.F64.eq, float.F64.is_negative, float.F64.is_nan, F64.isNaN, h, this]
  · simp only [Bool.not_eq_true] at h
    simp [float.F64.eq, float.F64.is_nan, float.F64.lt, F64.isNaN, h]
    split <;> simp_all

/-- `Option` ↔ `Except NetExn` for `Math.Clamp` (`none` = ArgumentException). -/
def exceptToOption {α} : Except NetExn α → Option α
  | .ok v => some v
  | .error _ => none

theorem clamp_refines (v lo hi : F64) : net.clamp v lo hi = ok (exceptToOption (F64.clamp v lo hi)) := by
  unfold net.clamp F64.clamp
  by_cases h1 : hi < lo <;> by_cases h2 : v < lo <;> by_cases h3 : hi < v <;>
    simp [float.F64.lt, exceptToOption, h1, h2, h3]

end OsuProofs
