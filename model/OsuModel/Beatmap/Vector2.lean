import OsuModel.Net
import OsuModel.Beatmap.DotNet

/-!
# `osuTK.Vector2` (float32) and `osu.Framework.Utils.Precision`

Transcribed from the decompiled `ppy.osuTK.NS20 1.0.211` (`osuTK.Vector2`; checked with ilspycmd,
including IL: unary minus is `neg`, i.e. a sign flip) and osu-framework 2026.921.1
(`osu.Framework/Graphics/Vector2Extensions.cs`, `osu.Framework/Utils/Precision.cs`).
All arithmetic is single precision, evaluated exactly in source order (RyuJIT: SSE, no FMA).
-/

namespace OsuModel.Beatmap
open OsuModel.Net

/-- `osuTK.Vector2` -/
structure Vec2 where
  x : F32
  y : F32
deriving Inhabited, Repr

namespace Vec2

def zero : Vec2 := ⟨0, 0⟩
/-- `new Vector2(v)` (both components) -/
def splat (v : F32) : Vec2 := ⟨v, v⟩

/-- `operator +` -/
@[inline] def add (a b : Vec2) : Vec2 := ⟨a.x + b.x, a.y + b.y⟩
/-- `operator -` -/
@[inline] def sub (a b : Vec2) : Vec2 := ⟨a.x - b.x, a.y - b.y⟩
/-- unary `operator -` (IL `neg`) -/
@[inline] def neg (a : Vec2) : Vec2 := ⟨-a.x, -a.y⟩
/-- `operator *(Vector2, float)` / `operator *(float, Vector2)` -/
@[inline] def scale (a : Vec2) (s : F32) : Vec2 := ⟨a.x * s, a.y * s⟩
/-- `operator /(Vector2, float)` (true division per component) -/
@[inline] def div (a : Vec2) (s : F32) : Vec2 := ⟨a.x / s, a.y / s⟩

instance : Add Vec2 := ⟨add⟩
instance : Sub Vec2 := ⟨sub⟩
instance : Neg Vec2 := ⟨neg⟩
instance : HMul Vec2 F32 Vec2 := ⟨scale⟩
instance : HMul F32 Vec2 Vec2 := ⟨fun s a => scale a s⟩
instance : HDiv Vec2 F32 Vec2 := ⟨div⟩

/-- `operator ==` / `Equals(Vector2)`: `X == other.X && Y == other.Y` (float `==`). -/
@[inline] def eq (a b : Vec2) : Bool := a.x == b.x && a.y == b.y

/-- `LengthSquared => X * X + Y * Y` -/
@[inline] def lengthSquared (a : Vec2) : F32 := a.x * a.x + a.y * a.y

/-- `Length => (float)Math.Sqrt(X * X + Y * Y)` (float sum, double sqrt, cast back). -/
def length (a : Vec2) : F32 := (F64.sqrt (F32.toF64 (a.x * a.x + a.y * a.y))).toF32

/-- `Normalized()`: `num = 1f / Length; X *= num; Y *= num`. -/
def normalized (a : Vec2) : Vec2 :=
  let num : F32 := 1 / a.length
  ⟨a.x * num, a.y * num⟩

/-- `osuTK.Vector2.Distance(vec1, vec2)`:
`(float)Math.Sqrt((vec2.X - vec1.X) * (vec2.X - vec1.X) + (vec2.Y - vec1.Y) * (vec2.Y - vec1.Y))`. -/
def distance (v1 v2 : Vec2) : F32 :=
  (F64.sqrt (F32.toF64 ((v2.x - v1.x) * (v2.x - v1.x) + (v2.y - v1.y) * (v2.y - v1.y)))).toF32

/-- `osu.Framework.Graphics.Vector2Extensions.Distance(vec1, vec2)` (`Vector2Extensions.cs:39-54`):
`MathF.Sqrt((vec2.X - vec1.X) * (vec2.X - vec1.X) + (vec2.Y - vec1.Y) * (vec2.Y - vec1.Y))`. -/
def distanceFw (v1 v2 : Vec2) : F32 :=
  F32.sqrt ((v2.x - v1.x) * (v2.x - v1.x) + (v2.y - v1.y) * (v2.y - v1.y))

/-- `Vector2.Dot(a, b) = a.X * b.X + a.Y * b.Y` -/
@[inline] def dot (a b : Vec2) : F32 := a.x * b.x + a.y * b.y

end Vec2

/-! ## `osu.Framework.Utils.Precision` (`Precision.cs:18-86`) -/
namespace Precision
/-- `FLOAT_EPSILON = 1e-3f` -/
def FLOAT_EPSILON : F32 := 1e-3
/-- `DOUBLE_EPSILON = 1e-7` -/
def DOUBLE_EPSILON : F64 := 1e-7
/-- `AlmostEquals(float, float, eps) => Math.Abs(value1 - value2) <= eps` -/
def almostEqualsF32 (a b : F32) (eps : F32 := FLOAT_EPSILON) : Bool := F32.abs (a - b) ≤ eps
/-- `AlmostEquals(double, double, eps) => Math.Abs(value1 - value2) <= eps` -/
def almostEqualsF64 (a b : F64) (eps : F64 := DOUBLE_EPSILON) : Bool := F64.abs (a - b) ≤ eps
/-- `DefinitelyBigger(double, double, eps) => value1 - eps > value2` -/
def definitelyBiggerF64 (a b : F64) (eps : F64 := DOUBLE_EPSILON) : Bool := b < a - eps
end Precision

end OsuModel.Beatmap
