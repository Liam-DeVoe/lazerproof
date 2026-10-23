/-
Hand-written: the Rust float wrapper types (opaque to Charon, `impl/osu_eval_core/src/float.rs`)
are *identified* with the spec's float types. Rust `F64(u64)` / `F32(u32)` holding IEEE bit
patterns ↦ `OsuModel.Net.F64 = Float` / `F32 = Float32` (IEEE bit patterns with one canonical
NaN): every Rust NaN corresponds to the single Lean NaN. TRUSTED (docs/proof-poc.md §Trust).
-/
import Aeneas
import OsuModel.Net
open Aeneas Aeneas.Std Result ControlFlow Error

abbrev float.F64 : Type := OsuModel.Net.F64
abbrev float.F32 : Type := OsuModel.Net.F32
