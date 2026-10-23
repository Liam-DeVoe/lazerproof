/-
Type-directed abstraction maps (Rust translation value ↦ spec value) used by the automatically
generated refinement statements: `∃ r, f a = ok r ∧ spec (abs a) = abs r`.
Instances are selected by both source and target type, so one Rust type can map to several spec
types (e.g. `I32` to `Int32` or `Int`).
-/
import OsuProofs.Manual
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

/-- Abstraction map; the target type is chosen by the expected type. -/
class AbsTo (α : Type) (β : Type) where
  abs : α → β

export AbsTo (abs)

instance (priority := low) {α} : AbsTo α α := ⟨id⟩
instance : AbsTo U32 Nat := ⟨(·.val)⟩
instance : AbsTo Usize Nat := ⟨(·.val)⟩
instance : AbsTo U8 Nat := ⟨(·.val)⟩
instance : AbsTo U64 Nat := ⟨(·.val)⟩
instance : AbsTo U128 Nat := ⟨(·.val)⟩
instance : AbsTo I32 Int := ⟨(·.val)⟩
instance : AbsTo I64 Int := ⟨(·.val)⟩
instance : AbsTo I32 Int32 := ⟨i32S⟩
instance : AbsTo I64 Int64 := ⟨fun x => Int64.ofBitVec x.bv⟩
instance : AbsTo U32 UInt32 := ⟨fun x => UInt32.ofBitVec x.bv⟩
instance : AbsTo U64 UInt64 := ⟨fun x => UInt64.ofBitVec x.bv⟩
instance : AbsTo U8 UInt8 := ⟨fun x => UInt8.ofBitVec x.bv⟩
instance : AbsTo U32 Char := ⟨chOf⟩
instance : AbsTo (Slice U32) String := ⟨fun s => String.ofList (strS s)⟩
instance : AbsTo (alloc.vec.Vec U32) String := ⟨fun s => String.ofList (s.val.map chOf)⟩
instance : AbsTo (Slice U32) (List Char) := ⟨strS⟩
instance : AbsTo (alloc.vec.Vec U32) (List Char) := ⟨fun s => s.val.map chOf⟩
instance : AbsTo net.basic.NetExn NetExn := ⟨exnS⟩
instance {α β} [AbsTo α β] : AbsTo (alloc.vec.Vec α) (_root_.Array β) := ⟨fun v => (v.val.map abs).toArray⟩
instance {α β} [AbsTo α β] : AbsTo (alloc.vec.Vec α) (List β) := ⟨fun v => v.val.map abs⟩
instance {α β} [AbsTo α β] : AbsTo (Slice α) (_root_.Array β) := ⟨fun v => (v.val.map abs).toArray⟩
instance {α β} [AbsTo α β] : AbsTo (Slice α) (List β) := ⟨fun v => v.val.map abs⟩
instance {α β} [AbsTo α β] : AbsTo (Option α) (Option β) := ⟨fun o => o.map abs⟩
instance {α β γ δ} [AbsTo α β] [AbsTo γ δ] : AbsTo (α × γ) (β × δ) := ⟨fun p => (abs p.1, abs p.2)⟩
instance {α β} [AbsTo α β] : AbsTo (core.result.Result α net.basic.NetExn) (Except NetExn β) :=
  ⟨fun | .Ok a => .ok (abs a) | .Err e => .error (exnS e)⟩
instance {α β} [AbsTo α β] {n : Usize} : AbsTo (Std.Array α n) (_root_.Array β) := ⟨fun v => (v.val.map abs).toArray⟩
instance {α β} [AbsTo α β] {n : Usize} : AbsTo (Std.Array α n) (List β) := ⟨fun v => v.val.map abs⟩
instance : AbsTo net.osutk.Vector2 Vec2 := ⟨bv2S⟩
instance : AbsTo net.osutk.Vector2 OsuTK.Vector2 := ⟨v2S⟩

theorem spec_of_ex {α} {m : Result α} {P : α → Prop} (h : ∃ r, m = ok r ∧ P r) : WP.spec m P := by
  obtain ⟨r, rfl, hr⟩ := h; exact (WP.spec_ok r).mpr hr

theorem spec_of_eq {α} {m : Result α} {v : α} (h : m = ok v) : WP.spec m (fun r => r = v) := by
  rw [h]; exact (WP.spec_ok v).mpr rfl

@[simp] theorem abs_i32S_lt_iff (a b : I32) : i32S a < i32S b ↔ a.val < b.val := by
  rw [Int32.lt_iff_toInt_lt, i32S_toInt, i32S_toInt]
@[simp] theorem abs_i32S_le_iff (a b : I32) : i32S a ≤ i32S b ↔ a.val ≤ b.val := by
  rw [Int32.le_iff_toInt_le, i32S_toInt, i32S_toInt]
@[simp] theorem abs_i32S_inj (a b : I32) : i32S a = i32S b ↔ a = b := by
  constructor
  · intro h; have := congrArg Int32.toInt h; rw [i32S_toInt, i32S_toInt] at this; exact IScalar.eq_of_val_eq this
  · intro h; rw [h]

@[simp] theorem abs_id {α} (x : α) : (abs x : α) = x := rfl

end OsuProofs
