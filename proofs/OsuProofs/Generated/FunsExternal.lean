/-
Hand-written: Lean meaning of each Rust float primitive (`impl/osu_eval_core/src/float.rs`,
opaque to Charon). Each definition is one line and *is* the corresponding `OsuModel.Net` spec
operation. TRUSTED: "the Rust primitive computes this IEEE value" (table in
docs/proof-pipeline.md, "Trusted primitives").
Primitives whose identification only holds on part of the domain fail (`fail .panic`) outside
it, so every refinement proof `impl = ok spec` must show the call site stays in the domain.
-/
import Aeneas
import OsuProofs.Generated.Types
import OsuModel.Beatmap.DotNet
open Aeneas Aeneas.Std Result ControlFlow Error
open OsuModel.Net

/-! ## binary64 -/
-- `f64::from_bits` (Lean canonicalises NaN payloads, see TypesExternal)
def float.F64.from_bits (b : Std.U64) : Result float.F64 := ok (Float.ofBits b.bv.toNat.toUInt64)
-- raw bits; only identified on non-NaN values (Rust sees the real NaN payload, the model one NaN)
def float.F64.to_bits (a : float.F64) : Result Std.U64 :=
  if OsuModel.Net.F64.isNaN a then fail .panic else ok ⟨a.toBits.toBitVec⟩
-- IEEE binary64 RNE `+ - * /` (SSE2 addsd/subsd/mulsd/divsd, same as RyuJIT); sign flip
def float.F64.add (a b : float.F64) : Result float.F64 := ok (a + b)
def float.F64.sub (a b : float.F64) : Result float.F64 := ok (a - b)
def float.F64.mul (a b : float.F64) : Result float.F64 := ok (a * b)
def float.F64.div (a b : float.F64) : Result float.F64 := ok (a / b)
def float.F64.neg (a : float.F64) : Result float.F64 := ok (-a)
-- IEEE comparisons (false on NaN; +0 == -0)
def float.F64.lt (a b : float.F64) : Result Bool := ok (decide (a < b))
def float.F64.le (a b : float.F64) : Result Bool := ok (decide (a ≤ b))
def float.F64.eq (a b : float.F64) : Result Bool := ok (a == b)
def float.F64.is_nan (a : float.F64) : Result Bool := ok (OsuModel.Net.F64.isNaN a)
-- sign bit; only identified on non-NaN inputs
def float.F64.is_negative (a : float.F64) : Result Bool :=
  if OsuModel.Net.F64.isNaN a then fail .panic else ok (OsuModel.Net.F64.isNegative a)
-- `Math.Abs/Floor/Ceiling/Truncate/Sqrt`, `(float)double`: the spec's kernel-computable models
def float.F64.abs (a : float.F64) : Result float.F64 := ok (OsuModel.Net.F64.abs a)
def float.F64.floor (a : float.F64) : Result float.F64 := ok (OsuModel.Net.F64.floor a)
def float.F64.ceil (a : float.F64) : Result float.F64 := ok (OsuModel.Net.F64.ceiling a)
def float.F64.trunc (a : float.F64) : Result float.F64 := ok (OsuModel.Net.F64.truncate a)
def float.F64.sqrt (a : float.F64) : Result float.F64 := ok (OsuModel.Net.F64.sqrt a)
def float.F64.to_f32 (a : float.F64) : Result float.F32 := ok (OsuModel.Net.F64.toF32 a)
-- integer -> double (one RNE rounding)
def float.F64.from_i64 (n : Std.I64) : Result float.F64 := ok (OsuModel.Net.F64.ofInt n.val)
def float.F64.from_u64 (n : Std.U64) : Result float.F64 := ok (OsuModel.Net.F64.ofInt n.val)
-- saturating double -> integer casts (Rust `as` = .NET 9+: truncate, clamp, NaN -> 0)
def float.F64.to_i32_sat (a : float.F64) : Result Std.I32 := ok ⟨(OsuModel.Net.F64.toInt32 a).toBitVec⟩
def float.F64.to_i64_sat (a : float.F64) : Result Std.I64 := ok ⟨(OsuModel.Net.F64.toInt64 a).toBitVec⟩
-- glibc libm (2.39), the same entry points .NET calls (opaque in the spec too)
def float.F64.sin (a : float.F64) : Result float.F64 := ok (OsuModel.Net.F64.sin a)
def float.F64.cos (a : float.F64) : Result float.F64 := ok (OsuModel.Net.F64.cos a)
def float.F64.acos (a : float.F64) : Result float.F64 := ok (OsuModel.Net.F64.acos a)
def float.F64.atan2 (y x : float.F64) : Result float.F64 := ok (OsuModel.Net.F64.atan2 y x)
def float.F64.exp (a : float.F64) : Result float.F64 := ok (OsuModel.Net.F64.exp a)
def float.F64.log (a : float.F64) : Result float.F64 := ok (OsuModel.Net.F64.log a)
def float.F64.pow (a b : float.F64) : Result float.F64 := ok (OsuModel.Net.F64.pow a b)
-- C# `%` on doubles = IEEE `fmod` (exact)
def float.F64.fmod (a b : float.F64) : Result float.F64 := ok (OsuModel.Beatmap.fmodF64 a b)

/-- Value of a digit-value string (most significant first); `none` if some entry is not 0..9. -/
def digitsVal (l : List Std.U8) : Option Nat :=
  l.foldl (fun acc d => acc.bind fun a => if d.val < 10 then some (10 * a + d.val) else none) (some 0)

-- correctly rounded decimal -> binary64 (Rust `dec2flt` on the rendered `[-]D..De<exp>`);
-- only identified for digit values 0..9
def float.F64.parse_decimal (neg : Bool) (digits : Slice Std.U8) (exp10 : Std.I64) : Result float.F64 :=
  match digitsVal digits.val with
  | none => fail .panic
  | some m => ok (OsuModel.Net.F64.ofBitsN (OsuModel.Net.Parse.decToBits OsuModel.Net.Fmt.f64 neg m exp10.val))

/-! ## binary32 -/
def float.F32.from_bits (b : Std.U32) : Result float.F32 := ok (Float32.ofBits b.bv.toNat.toUInt32)
def float.F32.to_bits (a : float.F32) : Result Std.U32 :=
  if OsuModel.Net.F32.isNaN a then fail .panic else ok ⟨a.toBits.toBitVec⟩
def float.F32.add (a b : float.F32) : Result float.F32 := ok (a + b)
def float.F32.sub (a b : float.F32) : Result float.F32 := ok (a - b)
def float.F32.mul (a b : float.F32) : Result float.F32 := ok (a * b)
def float.F32.div (a b : float.F32) : Result float.F32 := ok (a / b)
def float.F32.neg (a : float.F32) : Result float.F32 := ok (-a)
def float.F32.lt (a b : float.F32) : Result Bool := ok (decide (a < b))
def float.F32.le (a b : float.F32) : Result Bool := ok (decide (a ≤ b))
def float.F32.eq (a b : float.F32) : Result Bool := ok (a == b)
def float.F32.is_nan (a : float.F32) : Result Bool := ok (OsuModel.Net.F32.isNaN a)
def float.F32.is_negative (a : float.F32) : Result Bool :=
  if OsuModel.Net.F32.isNaN a then fail .panic else ok (OsuModel.Net.F32.isNegative a)
def float.F32.abs (a : float.F32) : Result float.F32 := ok (OsuModel.Net.F32.abs a)
def float.F32.floor (a : float.F32) : Result float.F32 := ok (OsuModel.Net.F32.floor a)
def float.F32.ceil (a : float.F32) : Result float.F32 := ok (OsuModel.Net.F32.ceiling a)
def float.F32.trunc (a : float.F32) : Result float.F32 := ok (OsuModel.Net.F32.truncate a)
def float.F32.sqrt (a : float.F32) : Result float.F32 := ok (OsuModel.Net.F32.sqrt a)
-- `(double)float` (exact)
def float.F32.to_f64 (a : float.F32) : Result float.F64 := ok (OsuModel.Net.F32.toF64 a)
def float.F32.from_i64 (n : Std.I64) : Result float.F32 := ok (OsuModel.Net.F32.ofInt n.val)
def float.F32.from_u64 (n : Std.U64) : Result float.F32 := ok (OsuModel.Net.F32.ofInt n.val)
def float.F32.to_i32_sat (a : float.F32) : Result Std.I32 := ok ⟨(OsuModel.Net.F32.toInt32 a).toBitVec⟩
def float.F32.sin (a : float.F32) : Result float.F32 := ok (OsuModel.Net.F32.sin a)
def float.F32.cos (a : float.F32) : Result float.F32 := ok (OsuModel.Net.F32.cos a)
def float.F32.atan2 (y x : float.F32) : Result float.F32 := ok (OsuModel.Net.F32.atan2 y x)
def float.F32.parse_decimal (neg : Bool) (digits : Slice Std.U8) (exp10 : Std.I64) : Result float.F32 :=
  match digitsVal digits.val with
  | none => fail .panic
  | some m => ok (OsuModel.Net.F32.ofBitsN (OsuModel.Net.Parse.decToBits OsuModel.Net.Fmt.f32 neg m exp10.val))


/-! ## `derive(Clone)` of the opaque wrappers (bit copy) -/
def float.F64.Insts.CoreCloneClone.clone (a : float.F64) : Result float.F64 := ok a
def float.F32.Insts.CoreCloneClone.clone (a : float.F32) : Result float.F32 := ok a

/-! ## Rust `core`/`alloc` items not modelled by the Aeneas library
Std semantics, TRUSTED like the Aeneas library's own models: each is the documented behaviour of
the std function. -/
-- `Option::<T>::clone`
def core.option.Option.Insts.CoreCloneClone.clone {T : Type _} (cloneCloneInst : core.clone.Clone T) :
    Option T → Result (Option T)
  | none => ok none
  | some x => do let y ← cloneCloneInst.clone x; ok (some y)
-- `<Option<T> as PartialEq>::eq`
def core.option.Option.Insts.CoreCmpPartialEqOption.eq {T : Type _} (cmpPartialEqInst : core.cmp.PartialEq T T) :
    Option T → Option T → Result Bool
  | none, none => ok true
  | some a, some b => cmpPartialEqInst.eq a b
  | _, _ => ok false
-- `Vec::<T>::pop`: removes and returns the last element
def alloc.vec.Vec.pop {T : Type _} (_A : Type _) (v : alloc.vec.Vec T) : Result ((Option T) × (alloc.vec.Vec T)) :=
  ok (v.val.getLast?, alloc.vec.Vec.from v.val.dropLast (by have := alloc.vec.Vec.property v; simp; omega))
