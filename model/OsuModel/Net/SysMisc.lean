import OsuModel.Net.Convert
import OsuModel.Net.MathOps

/-!
# Small BCL helpers: `float/double.DegreesToRadians/RadiansToDegrees`, `Enumerable.Average`

Sources: decompiled `System.Private.CoreLib` / `System.Linq` 10.0.13.
Differential test: `nettest` ops 220–226.
-/

namespace OsuModel.Net
namespace SysMisc

/-- `float.Pi` = `(float)Math.PI` = 3.14159274f -/
def f32Pi : F32 := Float32.ofBits 0x40490FDB
def f32_180 : F32 := Float32.ofBits 0x43340000
/-- `Math.PI` -/
def f64Pi : F64 := Float.ofBits 0x400921FB54442D18
def f64_180 : F64 := Float.ofBits 0x4066800000000000

namespace F32
/-- `float.DegreesToRadians(d) = d * (float)Math.PI / 180f` = `(d * π_f) / 180f` -/
def degreesToRadians (d : F32) : F32 := d * f32Pi / f32_180
/-- `float.RadiansToDegrees(r) = r * 180f / (float)Math.PI` = `(r * 180f) / π_f` -/
def radiansToDegrees (r : F32) : F32 := r * f32_180 / f32Pi
end F32

namespace F64
/-- `double.DegreesToRadians(d) = d * Math.PI / 180.0` -/
def degreesToRadians (d : F64) : F64 := d * f64Pi / f64_180
/-- `double.RadiansToDegrees(r) = r * 180.0 / Math.PI` -/
def radiansToDegrees (r : F64) : F64 := r * f64_180 / f64Pi
end F64

/-- `Enumerable.Average(IEnumerable<double>)` for a `List<double>`/array (span path):
`Sum` is a plain sequential loop from `+0.0` (no SIMD for double: only int/long sums are
vectorised), then `/ (double)count`. Empty → InvalidOperationException (`.argument` here). -/
def averageF64 (xs : List F64) : Except NetExn F64 :=
  if xs.isEmpty then .error .argument
  else .ok (xs.foldl (· + ·) 0 / OsuModel.Net.F64.ofInt xs.length)

end SysMisc
end OsuModel.Net
