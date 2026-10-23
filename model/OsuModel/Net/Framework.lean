import OsuModel.Net.OsuTK
import OsuModel.Net.Decimal
import OsuModel.Net.SysMisc

/-!
# osu-framework 2026.921.1 helpers (double/float exact)

Sources (pinned checkout `~/lazerproof/osu-framework`, identical to the `ppy.osu.Framework
2026.921.1` nupkg that lazer references):
* `osu.Framework/Utils/Precision.cs`
* `osu.Framework/Utils/Interpolation.cs` (`Lerp`, `Damp`, `DampContinuously`, `ValueAt` for
  double / float / int / Vector2, `GenericInterpolation<TEasing>`)
* `osu.Framework/Graphics/Transforms/DefaultEasingFunction.cs`, `Graphics/Easing.cs`
* `osu.Framework/Graphics/Vector2Extensions.cs`, `Extensions/MatrixExtensions/MatrixExtensions.cs`,
  `Graphics/DrawInfo.cs`
* `osu.Framework/Bindables/BindableNumber.cs`, `RangeConstrainedBindable.cs`

Differential test: `nettest` ops 140–149 and 210–219 call the real `osu.Framework.dll`.
Easing functions call glibc `pow/sin/cos` (trusted externs, `Libm.lean`); everything else is
kernel-computable.
-/

namespace OsuModel.Net
namespace Framework
open OsuTK

/-! ## `Precision` -/
namespace Precision
/-- `FLOAT_EPSILON = 1e-3f` -/
def FLOAT_EPSILON : F32 := Float32.ofBits 0x3A83126F
/-- `DOUBLE_EPSILON = 1e-7` -/
def DOUBLE_EPSILON : F64 := Float.ofBits 0x3E7AD7F29ABCAF48
/-- `DefinitelyBigger(a, b, e) = a - e > b` -/
def definitelyBiggerF (a b : F32) (e := FLOAT_EPSILON) : Bool := b < a - e
def definitelyBiggerD (a b : F64) (e := DOUBLE_EPSILON) : Bool := b < a - e
/-- `AlmostBigger(a, b, e) = a > b - e` -/
def almostBiggerF (a b : F32) (e := FLOAT_EPSILON) : Bool := b - e < a
def almostBiggerD (a b : F64) (e := DOUBLE_EPSILON) : Bool := b - e < a
/-- `AlmostEquals(a, b, e) = Math.Abs(a - b) <= e` -/
def almostEqualsF (a b : F32) (e := FLOAT_EPSILON) : Bool := F32.abs (a - b) ≤ e
def almostEqualsD (a b : F64) (e := DOUBLE_EPSILON) : Bool := F64.abs (a - b) ≤ e
def almostEqualsV (a b : Vector2) (e := FLOAT_EPSILON) : Bool := almostEqualsF a.x b.x e && almostEqualsF a.y b.y e
end Precision

/-! ## `DefaultEasingFunction` -/

/-- `osu.Framework.Graphics.Easing` (enum order = numeric value). -/
inductive Easing where
  | none | out | in_ | inQuad | outQuad | inOutQuad | inCubic | outCubic | inOutCubic
  | inQuart | outQuart | inOutQuart | inQuint | outQuint | inOutQuint
  | inSine | outSine | inOutSine | inExpo | outExpo | inOutExpo | inCirc | outCirc | inOutCirc
  | inElastic | outElastic | outElasticHalf | outElasticQuarter | inOutElastic
  | inBack | outBack | inOutBack | inBounce | outBounce | inOutBounce | outPow10
deriving Repr, DecidableEq, Inhabited

namespace Easing
def all : List Easing :=
  [none, out, in_, inQuad, outQuad, inOutQuad, inCubic, outCubic, inOutCubic, inQuart, outQuart,
   inOutQuart, inQuint, outQuint, inOutQuint, inSine, outSine, inOutSine, inExpo, outExpo, inOutExpo,
   inCirc, outCirc, inOutCirc, inElastic, outElastic, outElasticHalf, outElasticQuarter, inOutElastic,
   inBack, outBack, inOutBack, inBounce, outBounce, inOutBounce, outPow10]
/-- numeric value → enum (out-of-range values hit the `default:` branch = identity, like `none`). -/
def ofIndex (n : Nat) : Easing := all.getD n none
end Easing

namespace EasingConst
-- `const double`s (Roslyn folds them with the same IEEE double operations, left to right)
def pi : F64 := Float.ofBits 0x400921FB54442D18
def elastic_const : F64 := 2 * pi / 0.3
def elastic_const2 : F64 := 0.3 / 4
def back_const : F64 := 1.70158
def back_const2 : F64 := back_const * 1.525
def back_const_p1 : F64 := back_const + 1
def back_const2_p1 : F64 := back_const2 + 1
def bounce_const : F64 := 1 / 2.75
def b2 : F64 := 2 * bounce_const
def b25 : F64 := 2.5 * bounce_const
def b15 : F64 := 1.5 * bounce_const
def b225 : F64 := 2.25 * bounce_const
def b2625 : F64 := 2.625 * bounce_const
def one_m_ec2 : F64 := 1 - elastic_const2
def ec2_15 : F64 := elastic_const2 * 1.5
def one_m_ec2_15 : F64 := 1 - ec2_15
-- `static readonly` (computed at type init with glibc pow/sin)
def expo_offset : F64 := F64.pow 2 (-10)
def elastic_offset_full : F64 := F64.pow 2 (-11)
def elastic_offset_half : F64 := F64.pow 2 (-10) * F64.sin ((0.5 - elastic_const2) * elastic_const)
def elastic_offset_quarter : F64 := F64.pow 2 (-10) * F64.sin ((0.25 - elastic_const2) * elastic_const)
def in_out_elastic_offset : F64 := F64.pow 2 (-10) * F64.sin ((1 - elastic_const2 * 1.5) * elastic_const / 1.5)
def c7_5625 : F64 := 7.5625
def c0_75 : F64 := 0.75
def c0_9375 : F64 := 0.9375
def c0_984375 : F64 := 0.984375
def half : F64 := 0.5
def quarter : F64 := 0.25
end EasingConst

open EasingConst in
/-- `DefaultEasingFunction.OutBounce` branch (also used by `InOutBounce`). -/
def outBounce (time : F64) : F64 :=
  if time < bounce_const then c7_5625 * time * time
  else if time < b2 then (let t := time - b15; c7_5625 * t * t + c0_75)
  else if time < b25 then (let t := time - b225; c7_5625 * t * t + c0_9375)
  else (let t := time - b2625; c7_5625 * t * t + c0_984375)

open EasingConst in
/-- `DefaultEasingFunction.ApplyEasing(time)`, literal transcription (`--time` = `time - 1`
evaluated before the rest of the expression; `time *= 2` likewise). -/
def applyEasing (e : Easing) (time : F64) : F64 :=
  match e with
  | .none => time
  | .in_ | .inQuad => time * time
  | .out | .outQuad => time * (2 - time)
  | .inOutQuad => if time < half then time * time * 2 else (let t := time - 1; t * t * (-2) + 1)
  | .inCubic => time * time * time
  | .outCubic => let t := time - 1; t * t * t + 1
  | .inOutCubic => if time < half then time * time * time * 4 else (let t := time - 1; t * t * t * 4 + 1)
  | .inQuart => time * time * time * time
  | .outQuart => let t := time - 1; 1 - t * t * t * t
  | .inOutQuart => if time < half then time * time * time * time * 8 else (let t := time - 1; t * t * t * t * (-8) + 1)
  | .inQuint => time * time * time * time * time
  | .outQuint => let t := time - 1; t * t * t * t * t + 1
  | .inOutQuint => if time < half then time * time * time * time * time * 16 else (let t := time - 1; t * t * t * t * t * 16 + 1)
  | .inSine => 1 - F64.cos (time * pi * half)
  | .outSine => F64.sin (time * pi * half)
  | .inOutSine => half - half * F64.cos (pi * time)
  | .inExpo => F64.pow 2 (10 * (time - 1)) + expo_offset * (time - 1)
  | .outExpo => -(F64.pow 2 (-10 * time)) + 1 + expo_offset * time
  | .inOutExpo =>
    if time < half then half * (F64.pow 2 (20 * time - 10) + expo_offset * (2 * time - 1))
    else 1 - half * (F64.pow 2 (-20 * time + 10) + expo_offset * (-2 * time + 1))
  | .inCirc => 1 - F64.sqrt (1 - time * time)
  | .outCirc => let t := time - 1; F64.sqrt (1 - t * t)
  | .inOutCirc =>
    let t := time * 2
    if t < 1 then half - half * F64.sqrt (1 - t * t)
    else (let t := t - 2; half * F64.sqrt (1 - t * t) + half)
  | .inElastic => (-(F64.pow 2 (-10 + 10 * time))) * F64.sin ((one_m_ec2 - time) * elastic_const) + elastic_offset_full * (1 - time)
  | .outElastic => F64.pow 2 (-10 * time) * F64.sin ((time - elastic_const2) * elastic_const) + 1 - elastic_offset_full * time
  | .outElasticHalf => F64.pow 2 (-10 * time) * F64.sin ((half * time - elastic_const2) * elastic_const) + 1 - elastic_offset_half * time
  | .outElasticQuarter => F64.pow 2 (-10 * time) * F64.sin ((quarter * time - elastic_const2) * elastic_const) + 1 - elastic_offset_quarter * time
  | .inOutElastic =>
    let t := time * 2
    if t < 1 then
      (-half) * (F64.pow 2 (-10 + 10 * t) * F64.sin ((one_m_ec2_15 - t) * elastic_const / 1.5) - in_out_elastic_offset * (1 - t))
    else
      let t := t - 1
      half * (F64.pow 2 (-10 * t) * F64.sin ((t - ec2_15) * elastic_const / 1.5) - in_out_elastic_offset * t) + 1
  | .inBack => time * time * (back_const_p1 * time - back_const)
  | .outBack => let t := time - 1; t * t * (back_const_p1 * t + back_const) + 1
  | .inOutBack =>
    let t := time * 2
    if t < 1 then half * t * t * (back_const2_p1 * t - back_const2)
    else (let t := t - 2; half * (t * t * (back_const2_p1 * t + back_const2) + 2))
  | .inBounce =>
    let t := 1 - time
    if t < bounce_const then 1 - c7_5625 * t * t
    else if t < b2 then (let t := t - b15; 1 - (c7_5625 * t * t + c0_75))
    else if t < b25 then (let t := t - b225; 1 - (c7_5625 * t * t + c0_9375))
    else (let t := t - b2625; 1 - (c7_5625 * t * t + c0_984375))
  | .outBounce => outBounce time
  | .inOutBounce =>
    if time < half then half - half * outBounce (1 - time * 2)
    else outBounce ((time - half) * 2) * half + half
  | .outPow10 => let t := time - 1; t * F64.pow t 10 + 1

/-! ## `Interpolation` -/
namespace Interpolation
/-- `Lerp(start, final, amount) = start + (final - start) * amount` -/
def lerp (start final amount : F64) : F64 := start + (final - start) * amount
/-- `Damp(start, final, base, exponent)`; base ∉ [0,1] throws. -/
def damp (start final base exponent : F64) : Except NetExn F64 :=
  if base < 0 || 1 < base then .error .argumentOutOfRange
  else .ok (lerp start final (1 - F64.pow base exponent))
def half : F64 := 0.5
/-- `DampContinuously(current, target, halfTime, elapsed) = Damp(current, target, 0.5, elapsed / halfTime)` -/
def dampContinuously (current target halfTime elapsed : F64) : F64 :=
  lerp current target (1 - F64.pow half (elapsed / halfTime))

/-- `ValueAt(double time, double val1, double val2, double startTime, double endTime, easing)` -/
def valueAtD (time val1 val2 startTime endTime : F64) (e : Easing) : F64 :=
  if val1 == val2 then val1
  else
    let current := time - startTime
    let duration := endTime - startTime
    if current == 0 then val1
    else if duration == 0 then val2
    else
      let t := applyEasing e (current / duration)
      val1 + t * (val2 - val1)

/-- `ValueAt(…, float val1, float val2, …) = (float)ValueAt(time, (double)val1, (double)val2, …)` -/
def valueAtF (time : F64) (val1 val2 : F32) (startTime endTime : F64) (e : Easing) : F32 :=
  F64.toF32 (valueAtD time (F32.toF64 val1) (F32.toF64 val2) startTime endTime e)

/-- `ValueAt(…, int val1, int val2, …) = (int)Math.Round(ValueAt(time, (double)val1, val2, …))` -/
def valueAtI (time : F64) (val1 val2 : Int32) (startTime endTime : F64) (e : Easing) : Int32 :=
  F64.toInt32 (F64.round (valueAtD time (F64.ofInt32 val1) (F64.ofInt32 val2) startTime endTime e))

/-- `ValueAt(…, Vector2 val1, Vector2 val2, …)`:
`current = (float)(time - startTime); duration = (float)(endTime - startTime);
if (duration == 0 || current == 0) return val1; t = (float)ease((double)(current / duration));
return val1 + t * (val2 - val1)`. -/
def valueAtV (time : F64) (val1 val2 : Vector2) (startTime endTime : F64) (e : Easing) : Vector2 :=
  let current := F64.toF32 (time - startTime)
  let duration := F64.toF32 (endTime - startTime)
  if duration == 0 || current == 0 then val1
  else
    let t := F64.toF32 (applyEasing e (F32.toF64 (current / duration)))
    val1 + t * (val2 - val1)
end Interpolation

/-! ## `Vector2Extensions` (framework, not osuTK) -/
namespace Vector2Extensions
/-- `Transform(pos, mat)`: `x = M11*x + M21*y + M31`, `y = M12*x + M22*y + M32` -/
def transform (p : Vector2) (m : Matrix3) : Vector2 :=
  ⟨m.row0.x * p.x + m.row1.x * p.y + m.row2.x, m.row0.y * p.x + m.row1.y * p.y + m.row2.y⟩
/-- `Vector2Extensions.Distance` uses `MathF.Sqrt` (unlike osuTK's `Vector2.Distance`). -/
def distance (v1 v2 : Vector2) : F32 :=
  F32.sqrt ((v2.x - v1.x) * (v2.x - v1.x) + (v2.y - v1.y) * (v2.y - v1.y))
def distanceSquared (v1 v2 : Vector2) : F32 :=
  (v2.x - v1.x) * (v2.x - v1.x) + (v2.y - v1.y) * (v2.y - v1.y)
end Vector2Extensions

/-! ## `MatrixExtensions` -/
namespace MatrixExtensions
/-- `m.Row2 += m.Row0 * v.X + m.Row1 * v.Y` -/
def translateFromLeft (m : Matrix3) (v : Vector2) : Matrix3 :=
  { m with row2 := m.row2 + (m.row0 * v.x + m.row1 * v.y) }
/-- `M11 += M13 * v.X; M21 += M23 * v.X; M31 += M33 * v.X; M12 += M13 * v.Y; …` -/
def translateFromRight (m : Matrix3) (v : Vector2) : Matrix3 :=
  let r (a : Vector3) : Vector3 := ⟨a.x + a.z * v.x, a.y + a.z * v.y, a.z⟩
  ⟨r m.row0, r m.row1, r m.row2⟩
/-- `row0 = Row0*cos + Row1*sin; Row1 = Row1*cos - Row0*sin; Row0 = row0` (cosf/sinf) -/
def rotateFromLeft (m : Matrix3) (radians : F32) : Matrix3 :=
  let c := F32.cos radians
  let s := F32.sin radians
  { m with row0 := m.row0 * c + m.row1 * s, row1 := m.row1 * c - m.row0 * s }
/-- per row: `m1 = M1*cos - M2*sin; M2 = M2*cos + M1*sin; M1 = m1` -/
def rotateFromRight (m : Matrix3) (radians : F32) : Matrix3 :=
  let c := F32.cos radians
  let s := F32.sin radians
  let r (a : Vector3) : Vector3 := ⟨a.x * c - a.y * s, a.y * c + a.x * s, a.z⟩
  ⟨r m.row0, r m.row1, r m.row2⟩
/-- `Row0 *= v.X; Row1 *= v.Y` -/
def scaleFromLeft (m : Matrix3) (v : Vector2) : Matrix3 :=
  { m with row0 := m.row0 * v.x, row1 := m.row1 * v.y }
/-- `M11 *= v.X; M21 *= v.X; M31 *= v.X; M12 *= v.Y; …` -/
def scaleFromRight (m : Matrix3) (v : Vector2) : Matrix3 :=
  let r (a : Vector3) : Vector3 := ⟨a.x * v.x, a.y * v.y, a.z⟩
  ⟨r m.row0, r m.row1, r m.row2⟩
/-- `row0 = Row0 + Row1 * v.Y + Row0 * v.X * v.Y; Row1 += Row0 * v.X; Row0 = row0` -/
def shearFromLeft (m : Matrix3) (v : Vector2) : Matrix3 :=
  { m with row0 := m.row0 + m.row1 * v.y + m.row0 * v.x * v.y, row1 := m.row1 + m.row0 * v.x }
/-- `xy = v.X*v.Y; m11 = M11 + M12*v.X; M12 += M11*v.Y + M12*xy; M11 = m11` per row -/
def shearFromRight (m : Matrix3) (v : Vector2) : Matrix3 :=
  let xy := v.x * v.y
  let r (a : Vector3) : Vector3 := ⟨a.x + a.y * v.x, a.y + (a.x * v.y + a.y * xy), a.z⟩
  ⟨r m.row0, r m.row1, r m.row2⟩
end MatrixExtensions

/-! ## `DrawInfo` -/
structure DrawInfo where
  matrix : Matrix3
  matrixInverse : Matrix3
deriving Inhabited, Repr

namespace DrawInfo
/-- `Math.Sign(scale.X == 0 ? 1 : scale.X) * Precision.FLOAT_EPSILON` (int × float) -/
def clampScaleComp (s : F32) : F32 :=
  if F32.abs s < Precision.FLOAT_EPSILON then
    let sg : F32 := if s == 0 then 1 else if s < 0 then -1 else 1
    sg * Precision.FLOAT_EPSILON
  else s

/-- `DrawInfo.ApplyTransform(translation, scale, rotation, shear, origin)` (`DrawInfo.cs:31-73`). -/
def applyTransform (di : DrawInfo) (translation scale : Vector2) (rotation : F32) (shear origin : Vector2) :
    DrawInfo := Id.run do
  let mut m := di.matrix
  let mut mi := di.matrixInverse
  if !translation.eq Vector2.zero then
    m := MatrixExtensions.translateFromLeft m translation
    mi := MatrixExtensions.translateFromRight mi (-translation)
  if !(rotation == 0) then
    let radians := SysMisc.F32.degreesToRadians rotation
    m := MatrixExtensions.rotateFromLeft m radians
    mi := MatrixExtensions.rotateFromRight mi (-radians)
  if !shear.eq Vector2.zero then
    m := MatrixExtensions.shearFromLeft m (-shear)
    mi := MatrixExtensions.shearFromRight mi shear
  if !scale.eq Vector2.one then
    let s : Vector2 := ⟨clampScaleComp scale.x, clampScaleComp scale.y⟩
    m := MatrixExtensions.scaleFromLeft m s
    mi := MatrixExtensions.scaleFromRight mi (Vector2.divide Vector2.one s)
  if !origin.eq Vector2.zero then
    m := MatrixExtensions.translateFromLeft m (-origin)
    mi := MatrixExtensions.translateFromRight mi origin
  return ⟨m, mi⟩
end DrawInfo

/-! ## `BindableNumber<T>.Value` setter (`BindableNumber.cs:69-90`, `RangeConstrainedBindable.cs:256`)

```
setValue(v):
  decPrecision = decimal.CreateTruncating(Precision)
  if decPrecision > 0:
      a = decimal.CreateTruncating(T.Clamp(v, MinValue, MaxValue))
      a = Math.Round(a / decPrecision) * decPrecision          // decimal, ToEven
      base.Value = T.CreateTruncating(a)                       // decimal -> T
  else base.Value = v
RangeConstrainedBindable.Value = T.Clamp(that, MinValue, MaxValue)
```
Then `Bindable.Value` stores it only if it is not `Equals` to the current value (so `±0`
keep the old sign). `T.Clamp` is `double.Clamp`/`float.Clamp` = `Min(Max(v, min), max)` (IEEE 754:2019 min/max, so
`-0` clamped to `[0, …]` becomes `+0`, NaN stays NaN; `min > max` throws ArgumentException) — *not*
`Math.Clamp`. NaN with a precision: `CreateTruncating(NaN) = 0m`, so the value becomes `clamp(0)`.
-/
namespace Bindable

def clampD (v lo hi : F64) : Except NetExn F64 :=
  if hi < lo then .error .argument else .ok (F64.min (F64.max v lo) hi)
def clampF (v lo hi : F32) : Except NetExn F32 :=
  if hi < lo then .error .argument else .ok (F32.min (F32.max v lo) hi)

/-- `EqualityComparer<double>.Default.Equals` = `double.Equals`: `a == b || (NaN a && NaN b)`
(so `+0` equals `-0`). -/
def equalsD (a b : F64) : Bool := a == b || (a.isNaN && b.isNaN)
def equalsF (a b : F32) : Bool := a == b || (a.isNaN && b.isNaN)

/-- The value the `BindableNumber` setter hands to `RangeConstrainedBindable` (decimal snapping
when `(decimal)Precision > 0`, else the value itself). -/
def snapD (lo hi p v : F64) : Except NetExn F64 := do
  let dp ← NetDecimal.createTruncatingF64 p
  if dp.isPositive then
    let c ← clampD v lo hi
    let a ← NetDecimal.createTruncatingF64 c
    let q ← NetDecimal.div a dp
    let r ← NetDecimal.mul (NetDecimal.round q) dp
    return r.toF64
  else return v

def snapF (lo hi p v : F32) : Except NetExn F32 := do
  let dp ← NetDecimal.createTruncatingF32 p
  if dp.isPositive then
    let c ← clampF v lo hi
    let a ← NetDecimal.createTruncatingF32 c
    let q ← NetDecimal.div a dp
    let r ← NetDecimal.mul (NetDecimal.round q) dp
    return r.toF32
  else return v

/-- The candidate stored value of `bindable.Value = v` (`BindableNumber.setValue` then
`RangeConstrainedBindable.setValue`), before the `Bindable.Value` equality check. -/
def setDouble (lo hi p v : F64) : Except NetExn F64 := do clampD (← snapD lo hi p v) lo hi
def setFloat (lo hi p v : F32) : Except NetExn F32 := do clampF (← snapF lo hi p v) lo hi

/-- State of a `BindableDouble` (value, `MinValue`, `MaxValue`, `Precision`). -/
structure BD where
  value : F64
  minV : F64
  maxV : F64
  prec : F64
deriving Inhabited

/-- `Bindable<T>.Value` setter: `if (EqualityComparer<T>.Default.Equals(this.value, value)) return;`
— so assigning `-0` over `+0` (or `+0` over `-0`) keeps the old zero. -/
def BD.store (s : BD) (v : F64) : BD := if equalsD s.value v then s else { s with value := v }
/-- `RangeConstrainedBindable.setValue(v)` (private): clamp, then store. -/
def BD.rcSet (s : BD) (v : F64) : Except NetExn BD := do return s.store (← clampD v s.minV s.maxV)
/-- `BindableNumber.Value = v` -/
def BD.setValue (s : BD) (v : F64) : Except NetExn BD := do s.rcSet (← snapD s.minV s.maxV s.prec v)
def dblMax : F64 := Float.ofBits 0x7FEFFFFFFFFFFFFF
def dblEps : F64 := Float.ofBits 1
/-- `new BindableDouble(defaultValue)`: `Bindable` stores the default, `RangeConstrainedBindable`
re-applies it with the type's min/max, `BindableNumber` re-applies it with `double.Epsilon`
precision (`(decimal)double.Epsilon = 0m`: no snapping). -/
def BD.create (d : F64) : Except NetExn BD := do
  let s : BD := { value := d, minV := -dblMax, maxV := dblMax, prec := dblEps }
  let s ← s.rcSet d
  s.setValue s.value
/-- `MinValue = m`: no-op if `Equals(m, MinValue)`, else set and re-apply the value (clamp only). -/
def BD.setMin (s : BD) (m : F64) : Except NetExn BD :=
  if equalsD m s.minV then .ok s else { s with minV := m }.rcSet s.value
def BD.setMax (s : BD) (m : F64) : Except NetExn BD :=
  if equalsD m s.maxV then .ok s else { s with maxV := m }.rcSet s.value
/-- `Precision = p`: no-op if `precision == p` (IEEE `==`); `p <= 0` throws ArgumentOutOfRange;
else set and re-apply the value through the snapping setter. -/
def BD.setPrecision (s : BD) (p : F64) : Except NetExn BD :=
  if p == s.prec then .ok s
  else if p ≤ 0 then .error .argumentOutOfRange
  else { s with prec := p }.setValue s.value

/-- `new BindableDouble(d) { MinValue = lo, MaxValue = hi, Precision = p }` (initialiser order). -/
def BD.init (d lo hi p : F64) : Except NetExn BD := do
  let s ← BD.create d
  let s ← s.setMin lo
  let s ← s.setMax hi
  s.setPrecision p

/-- `BindableFloat` state (same structure, binary32). -/
structure BF where
  value : F32
  minV : F32
  maxV : F32
  prec : F32
deriving Inhabited

def BF.store (s : BF) (v : F32) : BF := if equalsF s.value v then s else { s with value := v }
def BF.rcSet (s : BF) (v : F32) : Except NetExn BF := do return s.store (← clampF v s.minV s.maxV)
def BF.setValue (s : BF) (v : F32) : Except NetExn BF := do s.rcSet (← snapF s.minV s.maxV s.prec v)
def fltMax : F32 := Float32.ofBits 0x7F7FFFFF
def fltEps : F32 := Float32.ofBits 1
def BF.create (d : F32) : Except NetExn BF := do
  let s : BF := { value := d, minV := -fltMax, maxV := fltMax, prec := fltEps }
  let s ← s.rcSet d
  s.setValue s.value
def BF.setMin (s : BF) (m : F32) : Except NetExn BF :=
  if equalsF m s.minV then .ok s else { s with minV := m }.rcSet s.value
def BF.setMax (s : BF) (m : F32) : Except NetExn BF :=
  if equalsF m s.maxV then .ok s else { s with maxV := m }.rcSet s.value
def BF.setPrecision (s : BF) (p : F32) : Except NetExn BF :=
  if p == s.prec then .ok s
  else if p ≤ 0 then .error .argumentOutOfRange
  else { s with prec := p }.setValue s.value
def BF.init (d lo hi p : F32) : Except NetExn BF := do
  let s ← BF.create d
  let s ← s.setMin lo
  let s ← s.setMax hi
  s.setPrecision p

end Bindable

end Framework
end OsuModel.Net
