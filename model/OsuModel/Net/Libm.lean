import OsuModel.Net.Basic

/-!
# Transcendental functions — trusted, extern (glibc libm)

On linux-x64, CoreCLR implements `Math.Sin/Cos/Tan/Asin/Acos/Atan/Atan2/Exp/Log/Log10/Pow/Cbrt`
and the `MathF` variants as FCalls in `src/coreclr/classlibnative/float/floatdouble.cpp` /
`floatsingle.cpp` that directly call the C library (`return sin(x);` …). `libcoreclr.so` imports
them from glibc's `libm.so.6` (`nm -D`: `sin@GLIBC_2.2.5`, `pow@GLIBC_2.2.5`, `powf@GLIBC_2.27`, …);
RyuJIT does not expand them inline on x64 (it only constant-folds calls with constant arguments,
using the same libm via `libclrjit.so`).

Lean core already declares exactly these as `@[extern "sin"] opaque Float.sin : Float → Float`
etc. (and `sinf`, … for `Float32`), so the model reuses them. They are **not** kernel-reducible:
proofs can only treat them as uninterpreted functions; evaluation happens in compiled code and
calls the system glibc. Trusted base: glibc 2.39 (Ubuntu GLIBC 2.39-0ubuntu8.x) on x86-64;
both .NET and the compiled Lean model must run against the same `libm.so.6` for bit-exactness
(glibc ≥ 2.41 replaced several binary32 functions with CORE-MATH correctly-rounded versions).

The differential tester checks the compiled Lean values against .NET bit-for-bit.
-/

namespace OsuModel.Net
namespace F64
/-- `Math.Sin` → glibc `sin` -/ @[inline] def sin (x : F64) : F64 := Float.sin x
/-- `Math.Cos` → glibc `cos` -/ @[inline] def cos (x : F64) : F64 := Float.cos x
/-- `Math.Tan` → glibc `tan` -/ @[inline] def tan (x : F64) : F64 := Float.tan x
/-- `Math.Asin` → glibc `asin` -/ @[inline] def asin (x : F64) : F64 := Float.asin x
/-- `Math.Acos` → glibc `acos` -/ @[inline] def acos (x : F64) : F64 := Float.acos x
/-- `Math.Atan` → glibc `atan` -/ @[inline] def atan (x : F64) : F64 := Float.atan x
/-- `Math.Atan2(y, x)` → glibc `atan2(y, x)` -/ @[inline] def atan2 (y x : F64) : F64 := Float.atan2 y x
/-- `Math.Exp` → glibc `exp` -/ @[inline] def exp (x : F64) : F64 := Float.exp x
/-- `Math.Log` → glibc `log` -/ @[inline] def log (x : F64) : F64 := Float.log x
/-- `Math.Log10` → glibc `log10` -/ @[inline] def log10 (x : F64) : F64 := Float.log10 x
/-- `Math.Pow` → glibc `pow` -/ @[inline] def pow (x y : F64) : F64 := Float.pow x y
/-- `Math.Cbrt` → glibc `cbrt` -/ @[inline] def cbrt (x : F64) : F64 := Float.cbrt x
/-- `Math.Log(a, newBase)` (managed: special cases, then `Log(a) / Log(newBase)`). -/
def logBase (a newBase : F64) : F64 :=
  if a.isNaN then a
  else if newBase.isNaN then newBase
  else if newBase == 1 then F64.nan
  else if !(a == 1) && (newBase == 0 || newBase == F64.posInf) then F64.nan
  else log a / log newBase
end F64

namespace F32
/-- `MathF.Sin` → `sinf` -/ @[inline] def sin (x : F32) : F32 := Float32.sin x
/-- `MathF.Cos` → `cosf` -/ @[inline] def cos (x : F32) : F32 := Float32.cos x
/-- `MathF.Tan` → `tanf` -/ @[inline] def tan (x : F32) : F32 := Float32.tan x
/-- `MathF.Asin` → `asinf` -/ @[inline] def asin (x : F32) : F32 := Float32.asin x
/-- `MathF.Acos` → `acosf` -/ @[inline] def acos (x : F32) : F32 := Float32.acos x
/-- `MathF.Atan` → `atanf` -/ @[inline] def atan (x : F32) : F32 := Float32.atan x
/-- `MathF.Atan2(y, x)` → `atan2f` -/ @[inline] def atan2 (y x : F32) : F32 := Float32.atan2 y x
/-- `MathF.Exp` → `expf` -/ @[inline] def exp (x : F32) : F32 := Float32.exp x
/-- `MathF.Log` → `logf` -/ @[inline] def log (x : F32) : F32 := Float32.log x
/-- `MathF.Pow` → `powf` -/ @[inline] def pow (x y : F32) : F32 := Float32.pow x y
end F32
end OsuModel.Net
