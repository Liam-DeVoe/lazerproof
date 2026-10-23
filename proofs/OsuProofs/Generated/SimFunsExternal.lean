/-
Hand-written: Lean meaning of the Rust float primitives (`impl/osu_eval_core/src/float.rs`, opaque to
Charon) that the sim+replay translation uses in addition to the net+beatmap ones
(Generated/FunsExternal.lean). Same convention: each definition is one line and *is* the corresponding
`OsuModel.Net` spec operation. TRUSTED (docs/proof-pipeline.md §4, "Trusted primitives").
The exact list is the `axiom` list of SimFunsExternal_Template.lean.
-/
import Aeneas
import OsuProofs.Generated.SimTypes
import OsuModel.Net
open Aeneas Aeneas.Std Result ControlFlow Error

-- glibc libm (2.39) `powf`, `asinf`: the same entry points .NET's `MathF.Pow`/`MathF.Asin` call (opaque in the spec too)
def float.F32.pow (a b : float.F32) : Result float.F32 := ok (OsuModel.Net.F32.pow a b)
def float.F32.asin (a : float.F32) : Result float.F32 := ok (OsuModel.Net.F32.asin a)
