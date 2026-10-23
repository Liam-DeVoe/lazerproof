/-
Representation maps between the Aeneas translation (`OsuImpl.*`) and the spec (`OsuModel.*`),
plus the simp setup shared by all refinement proofs. A theorem `impl x = ok (toImpl (spec (toSpec x)))`
is the `impl x = ok (spec x)` statement modulo these (field-for-field) maps.
-/
import OsuProofs.Prims
import OsuModel.Net
import OsuModel.Beatmap
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

/-! ## Float primitives unfold by `simp` (each is `ok (spec op)`, see Generated/FunsExternal.lean) -/
attribute [simp] float.F64.from_bits float.F64.add float.F64.sub float.F64.mul float.F64.div
  float.F64.neg float.F64.lt float.F64.le float.F64.eq float.F64.is_nan float.F64.abs float.F64.floor
  float.F64.ceil float.F64.trunc float.F64.sqrt float.F64.to_f32 float.F64.from_i64 float.F64.from_u64
  float.F64.to_i32_sat float.F64.to_i64_sat float.F64.sin float.F64.cos float.F64.log
  float.F64.atan2 float.F64.pow float.F64.exp float.F64.acos float.F64.fmod
  float.F32.from_bits float.F32.add float.F32.sub float.F32.mul float.F32.div float.F32.neg
  float.F32.lt float.F32.le float.F32.eq float.F32.is_nan float.F32.abs float.F32.floor
  float.F32.ceil float.F32.trunc float.F32.sqrt float.F32.to_f64 float.F32.from_i64
  float.F32.from_u64 float.F32.to_i32_sat float.F32.sin float.F32.cos float.F32.atan2

/-- `to_bits` on a non-NaN value. -/
theorem f64_to_bits_eq (a : F64) (h : a.isNaN = false) : float.F64.to_bits a = ok ⟨a.toBits.toBitVec⟩ := by
  simp [float.F64.to_bits]; exact h
theorem f32_to_bits_eq (a : F32) (h : a.isNaN = false) : float.F32.to_bits a = ok ⟨a.toBits.toBitVec⟩ := by
  simp [float.F32.to_bits]; exact h
theorem f64_is_negative_eq (a : F64) (h : a.isNaN = false) : float.F64.is_negative a = ok (F64.isNegative a) := by
  simp [float.F64.is_negative]; exact h
theorem f32_is_negative_eq (a : F32) (h : a.isNaN = false) : float.F32.is_negative a = ok (F32.isNegative a) := by
  simp [float.F32.is_negative]; exact h

/-! ## Scalar ↔ UInt bits -/
theorem u32_ofNat_val (x : U32) : UInt32.ofNat x.val = UInt32.ofBitVec x.bv := by
  apply UInt32.toBitVec_inj.mp
  simp only [UInt32.toBitVec_ofNat, UInt32.toBitVec_ofBitVec]
  show BitVec.ofNat 32 x.bv.toNat = x.bv
  exact BitVec.ofNat_toNat ..

theorem u64_ofNat_val (x : U64) : UInt64.ofNat x.val = UInt64.ofBitVec x.bv := by
  apply UInt64.toBitVec_inj.mp
  simp only [UInt64.toBitVec_ofNat, UInt64.toBitVec_ofBitVec]
  show BitVec.ofNat 64 x.bv.toNat = x.bv
  exact BitVec.ofNat_toNat ..

/-! ## Maps -/
def v2S (v : net.osutk.Vector2) : OsuTK.Vector2 := ⟨v.x, v.y⟩
def v2I (v : OsuTK.Vector2) : net.osutk.Vector2 := ⟨v.x, v.y⟩
def v3S (v : net.osutk.Vector3) : OsuTK.Vector3 := ⟨v.x, v.y, v.z⟩
def v3I (v : OsuTK.Vector3) : net.osutk.Vector3 := ⟨v.x, v.y, v.z⟩
def m3S (m : net.osutk.Matrix3) : OsuTK.Matrix3 := ⟨v3S m.row0, v3S m.row1, v3S m.row2⟩
def m3I (m : OsuTK.Matrix3) : net.osutk.Matrix3 := ⟨v3I m.row0, v3I m.row1, v3I m.row2⟩
/-- `OsuModel.Beatmap.Vec2` is a separate (identical) structure in the spec. -/
def bv2S (v : net.osutk.Vector2) : OsuModel.Beatmap.Vec2 := ⟨v.x, v.y⟩
def bv2I (v : OsuModel.Beatmap.Vec2) : net.osutk.Vector2 := ⟨v.x, v.y⟩

def exnS : net.basic.NetExn → NetExn
  | .Format => .format | .Overflow => .overflow | .Argument => .argument
  | .ArgumentOutOfRange => .argumentOutOfRange | .Arithmetic => .arithmetic
def exnI : NetExn → net.basic.NetExn
  | .format => .Format | .overflow => .Overflow | .argument => .Argument
  | .argumentOutOfRange => .ArgumentOutOfRange | .arithmetic => .Arithmetic

/-- Spec `Except NetExn α` ↦ Rust `Result<T, NetExn>` (with a value map). -/
def exceptI {α β} (f : α → β) : Except NetExn α → core.result.Result β net.basic.NetExn
  | .ok a => .Ok (f a)
  | .error e => .Err (exnI e)

/-- Lean `Int32` (C# `int`) ↦ Aeneas `I32` (same bits). -/
def i32I (x : Int32) : I32 := ⟨x.toBitVec⟩

@[simp] theorem v2S_I (v : OsuTK.Vector2) : v2S (v2I v) = v := rfl
@[simp] theorem v2I_S (v : net.osutk.Vector2) : v2I (v2S v) = v := rfl
@[simp] theorem bv2S_I (v : OsuModel.Beatmap.Vec2) : bv2S (bv2I v) = v := rfl
@[simp] theorem bv2I_S (v : net.osutk.Vector2) : bv2I (bv2S v) = v := rfl

@[simp] theorem v3S_I (v : OsuTK.Vector3) : v3S (v3I v) = v := rfl
@[simp] theorem v3I_S (v : net.osutk.Vector3) : v3I (v3S v) = v := rfl
@[simp] theorem m3S_I (m : OsuTK.Matrix3) : m3S (m3I m) = m := rfl
@[simp] theorem m3I_S (m : net.osutk.Matrix3) : m3I (m3S m) = m := rfl
theorem v2_neg_def (a : OsuTK.Vector2) : -a = OsuTK.Vector2.neg a := rfl

@[simp] theorem v2S_x (v : net.osutk.Vector2) : (v2S v).x = v.x := rfl
@[simp] theorem v2S_y (v : net.osutk.Vector2) : (v2S v).y = v.y := rfl
@[simp] theorem v2S_mk (a b : F32) : v2S ⟨a, b⟩ = ⟨a, b⟩ := rfl
@[simp] theorem v2I_x (v : OsuTK.Vector2) : (v2I v).x = v.x := rfl
@[simp] theorem v2I_y (v : OsuTK.Vector2) : (v2I v).y = v.y := rfl

/-! ## `Except` monad simp lemmas (the spec is written in `Except NetExn`) -/
@[simp] theorem except_bind_ok {ε α β} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl
@[simp] theorem except_bind_error {ε α β} (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = Except.error e := rfl
@[simp] theorem except_throw {ε α} (e : ε) : (throw e : Except ε α) = Except.error e := rfl
@[simp] theorem except_pure {ε α} (a : α) : (pure a : Except ε α) = Except.ok a := rfl
@[simp] theorem except_map_error {ε α β} (f : α → β) (e : ε) : (f <$> (Except.error e : Except ε α)) = Except.error e := rfl
@[simp] theorem except_map_ok {ε α β} (f : α → β) (a : α) : (f <$> (Except.ok a : Except ε α)) = Except.ok (f a) := rfl

end OsuProofs
