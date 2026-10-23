/-
Hand-written: the error type of the trusted LZMA boundary (`impl/osu_eval_core/src/lzma.rs`, opaque to
Charon, docs/proof-pipeline.md §4 "LZMA"). Same variants, same order as the Rust `enum LzmaErr`
(each stands for one message string of the C shim `model/c/lzma_shim.c`, see `lzmaErrOfMsg` in
EvalFunsExternal.lean). TRUSTED (as TypesExternal.lean).
-/
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error

inductive lzma.LzmaErr where
  | InitFailed | OutOfMemory | OutputTooLarge | Format | Data | Truncated | Other
