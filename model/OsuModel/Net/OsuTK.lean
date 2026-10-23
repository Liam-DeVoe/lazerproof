import OsuModel.Net.Convert
import OsuModel.Net.MathOps
import OsuModel.Net.Libm

/-!
# osuTK (`ppy.osuTK.NS20 1.0.211`): `Vector2`, `Vector3`, `Matrix3`, `MathHelper`

Transcribed from the decompiled `osuTK.dll` (ilspycmd). All arithmetic is binary32 in exact source
order (RyuJIT x64: SSE, no FMA contraction, no reassociation). Differential test: `nettest`
ops 120–139 call the real `osuTK.dll`.

Note: ILSpy renders the IL `neg` instruction of `operator -(Vector2)` as `0f - X`; it is a sign
flip (`-(+0) = -0`; checked by op 128).

These are the canonical definitions for `OsuModel.Net` users; `OsuModel.Beatmap.Vec2` and
`OsuModel.Sim.Vec2` are structurally identical copies.
-/

namespace OsuModel.Net
namespace OsuTK

/-- `osuTK.Vector2` -/
structure Vector2 where
  x : F32
  y : F32
deriving Inhabited, Repr

/-- `osuTK.Vector3` -/
structure Vector3 where
  x : F32
  y : F32
  z : F32
deriving Inhabited, Repr

namespace Vector2
def zero : Vector2 := ⟨0, 0⟩
def one : Vector2 := ⟨1, 1⟩
@[inline] def add (a b : Vector2) : Vector2 := ⟨a.x + b.x, a.y + b.y⟩
@[inline] def sub (a b : Vector2) : Vector2 := ⟨a.x - b.x, a.y - b.y⟩
/-- unary `operator -` (IL `neg`, sign flip) -/
@[inline] def neg (a : Vector2) : Vector2 := ⟨-a.x, -a.y⟩
/-- `operator *(Vector2, float)` and `operator *(float, Vector2)`: `vec.X *= scale` -/
@[inline] def scale (a : Vector2) (s : F32) : Vector2 := ⟨a.x * s, a.y * s⟩
/-- `operator *(Vector2, Vector2)` (componentwise) -/
@[inline] def mul (a b : Vector2) : Vector2 := ⟨a.x * b.x, a.y * b.y⟩
/-- `operator /(Vector2, float)` -/
@[inline] def divS (a : Vector2) (s : F32) : Vector2 := ⟨a.x / s, a.y / s⟩
/-- `Vector2.Divide(Vector2, Vector2)` (componentwise) -/
@[inline] def divide (a b : Vector2) : Vector2 := ⟨a.x / b.x, a.y / b.y⟩
/-- `operator ==` / `Equals`: `X == other.X && Y == other.Y` (float `==`) -/
@[inline] def eq (a b : Vector2) : Bool := a.x == b.x && a.y == b.y

instance : Add Vector2 := ⟨add⟩
instance : Sub Vector2 := ⟨sub⟩
instance : Neg Vector2 := ⟨neg⟩
instance : HMul Vector2 F32 Vector2 := ⟨scale⟩
instance : HMul F32 Vector2 Vector2 := ⟨fun s a => scale a s⟩
instance : HDiv Vector2 F32 Vector2 := ⟨divS⟩

/-- `LengthSquared => X * X + Y * Y` -/
@[inline] def lengthSquared (a : Vector2) : F32 := a.x * a.x + a.y * a.y
/-- `Length => (float)Math.Sqrt(X * X + Y * Y)` -/
def length (a : Vector2) : F32 := F64.toF32 (F64.sqrt (F32.toF64 (a.x * a.x + a.y * a.y)))
/-- `PerpendicularRight => new Vector2(Y, -X)`, `PerpendicularLeft => new Vector2(-Y, X)` -/
def perpendicularRight (a : Vector2) : Vector2 := ⟨a.y, -a.x⟩
def perpendicularLeft (a : Vector2) : Vector2 := ⟨-a.y, a.x⟩
/-- `Normalized()` / `Normalize()` / `Vector2.Normalize(v)`: `num = 1f / Length; X *= num; Y *= num` -/
def normalized (a : Vector2) : Vector2 :=
  let num : F32 := 1 / a.length
  ⟨a.x * num, a.y * num⟩
/-- `Vector2.Distance(v1, v2) = (float)Math.Sqrt((v2.X - v1.X) * (v2.X - v1.X) + (v2.Y - v1.Y) * (v2.Y - v1.Y))` -/
def distance (v1 v2 : Vector2) : F32 :=
  F64.toF32 (F64.sqrt (F32.toF64 ((v2.x - v1.x) * (v2.x - v1.x) + (v2.y - v1.y) * (v2.y - v1.y))))
/-- `Vector2.DistanceSquared(v1, v2)` -/
def distanceSquared (v1 v2 : Vector2) : F32 :=
  (v2.x - v1.x) * (v2.x - v1.x) + (v2.y - v1.y) * (v2.y - v1.y)
/-- `Vector2.Dot(a, b) = a.X * b.X + a.Y * b.Y` -/
@[inline] def dot (a b : Vector2) : F32 := a.x * b.x + a.y * b.y
/-- `Vector2.PerpDot(a, b) = a.X * b.Y - a.Y * b.X` -/
@[inline] def perpDot (a b : Vector2) : F32 := a.x * b.y - a.y * b.x
/-- `Vector2.Lerp(a, b, blend)`: `blend * (b.X - a.X) + a.X` per component -/
def lerp (a b : Vector2) (blend : F32) : Vector2 :=
  ⟨blend * (b.x - a.x) + a.x, blend * (b.y - a.y) + a.y⟩
/-- `Vector2.Clamp(vec, min, max)`: `x = vec.X < min.X ? min.X : (vec.X > max.X ? max.X : vec.X)`
(min test first: if `min > max` the result is `min`; a NaN component passes through). -/
def clamp (v lo hi : Vector2) : Vector2 :=
  let c (x l h : F32) : F32 := if x < l then l else if h < x then h else x
  ⟨c v.x lo.x hi.x, c v.y lo.y hi.y⟩
/-- `Vector2.ComponentMin/ComponentMax`: `a.X < b.X ? a.X : b.X` / `a.X > b.X ? a.X : b.X` -/
def componentMin (a b : Vector2) : Vector2 :=
  ⟨if a.x < b.x then a.x else b.x, if a.y < b.y then a.y else b.y⟩
def componentMax (a b : Vector2) : Vector2 :=
  ⟨if b.x < a.x then a.x else b.x, if b.y < a.y then a.y else b.y⟩
end Vector2

namespace Vector3
@[inline] def add (a b : Vector3) : Vector3 := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩
@[inline] def sub (a b : Vector3) : Vector3 := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩
@[inline] def scale (a : Vector3) (s : F32) : Vector3 := ⟨a.x * s, a.y * s, a.z * s⟩
instance : Add Vector3 := ⟨add⟩
instance : Sub Vector3 := ⟨sub⟩
instance : HMul Vector3 F32 Vector3 := ⟨scale⟩
end Vector3

/-- `osuTK.Matrix3` (row-major: `Row0 = (M11, M12, M13)` …). -/
structure Matrix3 where
  row0 : Vector3
  row1 : Vector3
  row2 : Vector3
deriving Inhabited, Repr

namespace Matrix3
def identity : Matrix3 := ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩⟩
def zero : Matrix3 := ⟨⟨0, 0, 0⟩, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩⟩
/-- the 9 entries `M11 … M33` in row order -/
def toList (m : Matrix3) : List F32 :=
  [m.row0.x, m.row0.y, m.row0.z, m.row1.x, m.row1.y, m.row1.z, m.row2.x, m.row2.y, m.row2.z]
def ofList : List F32 → Matrix3
  | [a, b, c, d, e, f, g, h, i] => ⟨⟨a, b, c⟩, ⟨d, e, f⟩, ⟨g, h, i⟩⟩
  | _ => zero
/-- `Matrix3.Mult(left, right)` / `operator *`: `r.Row0.X = x*x4 + y*x5 + z*x6` … -/
def mult (l r : Matrix3) : Matrix3 :=
  let row (a : Vector3) : Vector3 :=
    ⟨a.x * r.row0.x + a.y * r.row1.x + a.z * r.row2.x,
     a.x * r.row0.y + a.y * r.row1.y + a.z * r.row2.y,
     a.x * r.row0.z + a.y * r.row1.z + a.z * r.row2.z⟩
  ⟨row l.row0, row l.row1, row l.row2⟩
end Matrix3

/-! ## `osuTK.MathHelper` -/
namespace MathHelper
/-- `MathHelper.Pi` = `(float)Math.PI` = 3.14159274f -/
def pi : F32 := Float32.ofBits 0x40490FDB
/-- `TwoPi`, `PiOver2`, `PiOver4` (compile-time float constants) -/
def twoPi : F32 := Float32.ofBits 0x40C90FDB
def piOver2 : F32 := Float32.ofBits 0x3FC90FDB
def piOver4 : F32 := Float32.ofBits 0x3F490FDB
/-- the folded constants `MathF.PI / 180f` and `180f / MathF.PI` -/
def degToRadF : F32 := Float32.ofBits 0x3C8EFA35
def radToDegF : F32 := Float32.ofBits 0x42652EE0
/-- `Math.PI / 180.0`, `180.0 / Math.PI` -/
def degToRadD : F64 := Float.ofBits 0x3F91DF46A2529D39
def radToDegD : F64 := Float.ofBits 0x404CA5DC1A63C1F8

/-- `MathHelper.InverseSqrtFast(float x)`:
`xh = 0.5f * x; i = 0x5f375a86 - (bits(x) >> 1) (arithmetic shift); y = asfloat(i); y *= 1.5f - xh * y * y`. -/
def inverseSqrtFast (x : F32) : F32 :=
  let xh : F32 := half * x
  let i : Int32 := (0x5f375a86 : Int32) - (x.toBits.toInt32 >>> 1)
  let y := Float32.ofBits i.toUInt32
  y * (threeHalves - xh * y * y)
where
  half : F32 := Float32.ofBits 0x3F000000
  threeHalves : F32 := Float32.ofBits 0x3FC00000

/-- `Vector2.LengthFast => 1f / MathHelper.InverseSqrtFast(X * X + Y * Y)` -/
def lengthFast (a : Vector2) : F32 := 1 / inverseSqrtFast (a.x * a.x + a.y * a.y)
/-- `Vector2.NormalizeFast`: `num = InverseSqrtFast(X*X + Y*Y); X *= num; Y *= num` -/
def normalizeFast (a : Vector2) : Vector2 :=
  let num := inverseSqrtFast (a.x * a.x + a.y * a.y)
  ⟨a.x * num, a.y * num⟩

/-- `MathHelper.DegreesToRadians(float) = degrees * (MathF.PI / 180f)` (folded constant) -/
def degreesToRadiansF (d : F32) : F32 := d * degToRadF
def radiansToDegreesF (r : F32) : F32 := r * radToDegF
def degreesToRadiansD (d : F64) : F64 := d * degToRadD
def radiansToDegreesD (r : F64) : F64 := r * radToDegD
end MathHelper

end OsuTK
end OsuModel.Net
