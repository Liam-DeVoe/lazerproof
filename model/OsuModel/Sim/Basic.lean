import OsuModel.Net

/-!
# Sim basics: float32 vectors / 3x3 matrices (osuTK), `HitResult`, small .NET helpers

All arithmetic is in the exact source order of the C# code it models (RyuJIT x64: SSE, no FMA
contraction), using the bit-exact primitives of `OsuModel.Net`.
-/

namespace OsuModel.Sim
open OsuModel.Net

/-- `osuTK.Vector2` (float32). -/
structure Vec2 where
  x : F32
  y : F32
deriving Inhabited, Repr

namespace Vec2
def zero : Vec2 := ⟨0, 0⟩
@[inline] def add (a b : Vec2) : Vec2 := ⟨a.x + b.x, a.y + b.y⟩
@[inline] def sub (a b : Vec2) : Vec2 := ⟨a.x - b.x, a.y - b.y⟩
@[inline] def neg (a : Vec2) : Vec2 := ⟨-a.x, -a.y⟩
/-- `Vector2 * float` -/
@[inline] def scale (a : Vec2) (s : F32) : Vec2 := ⟨a.x * s, a.y * s⟩
/-- `Vector2 * Vector2` (componentwise) -/
@[inline] def mul (a b : Vec2) : Vec2 := ⟨a.x * b.x, a.y * b.y⟩
/-- `Vector2.Divide(a, b)` (componentwise) -/
@[inline] def cdiv (a b : Vec2) : Vec2 := ⟨a.x / b.x, a.y / b.y⟩
/-- `operator ==` (float `==` per component) -/
@[inline] def eq (a b : Vec2) : Bool := a.x == b.x && a.y == b.y
/-- `LengthSquared => X * X + Y * Y` -/
@[inline] def lengthSquared (a : Vec2) : F32 := a.x * a.x + a.y * a.y
/-- `Vector2.DistanceSquared(a, b)`: `(a.X - b.X)^2 + (a.Y - b.Y)^2` as `dx * dx + dy * dy`. -/
@[inline] def distanceSquared (a b : Vec2) : F32 :=
  let dx := a.x - b.x
  let dy := a.y - b.y
  dx * dx + dy * dy
instance : Add Vec2 := ⟨add⟩
instance : Sub Vec2 := ⟨sub⟩
instance : Neg Vec2 := ⟨neg⟩
end Vec2

/-- `osuTK.Matrix3` (row-major, `RowK = (M(K+1)1, M(K+1)2, M(K+1)3)`), float32. -/
structure Mat3 where
  m11 : F32
  m12 : F32
  m13 : F32
  m21 : F32
  m22 : F32
  m23 : F32
  m31 : F32
  m32 : F32
  m33 : F32
deriving Inhabited, Repr

namespace Mat3
def identity : Mat3 := ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩
def bitEq (a b : Mat3) : Bool :=
  a.m11.toBits == b.m11.toBits && a.m12.toBits == b.m12.toBits && a.m13.toBits == b.m13.toBits &&
  a.m21.toBits == b.m21.toBits && a.m22.toBits == b.m22.toBits && a.m23.toBits == b.m23.toBits &&
  a.m31.toBits == b.m31.toBits && a.m32.toBits == b.m32.toBits && a.m33.toBits == b.m33.toBits

/-- `MatrixExtensions.TranslateFromLeft(ref m, v)`: `m.Row2 += m.Row0 * v.X + m.Row1 * v.Y`
(`osu.Framework/Extensions/MatrixExtensions/MatrixExtensions.cs:11-14`; `Vector3` ops componentwise). -/
def translateFromLeft (m : Mat3) (v : Vec2) : Mat3 :=
  { m with
    m31 := m.m31 + (m.m11 * v.x + m.m21 * v.y)
    m32 := m.m32 + (m.m12 * v.x + m.m22 * v.y)
    m33 := m.m33 + (m.m13 * v.x + m.m23 * v.y) }

/-- `MatrixExtensions.TranslateFromRight(ref m, v)` (`:16-27`). -/
def translateFromRight (m : Mat3) (v : Vec2) : Mat3 :=
  let m11 := m.m11 + m.m13 * v.x
  let m21 := m.m21 + m.m23 * v.x
  let m31 := m.m31 + m.m33 * v.x
  let m12 := m.m12 + m.m13 * v.y
  let m22 := m.m22 + m.m23 * v.y
  let m32 := m.m32 + m.m33 * v.y
  { m with m11, m21, m31, m12, m22, m32 }

/-- `MatrixExtensions.ScaleFromLeft(ref m, v)`: `m.Row0 *= v.X; m.Row1 *= v.Y` (`:61-65`). -/
def scaleFromLeft (m : Mat3) (v : Vec2) : Mat3 :=
  { m with
    m11 := m.m11 * v.x, m12 := m.m12 * v.x, m13 := m.m13 * v.x
    m21 := m.m21 * v.y, m22 := m.m22 * v.y, m23 := m.m23 * v.y }

/-- `MatrixExtensions.ScaleFromRight(ref m, v)` (`:67-78`). -/
def scaleFromRight (m : Mat3) (v : Vec2) : Mat3 :=
  { m with
    m11 := m.m11 * v.x, m21 := m.m21 * v.x, m31 := m.m31 * v.x
    m12 := m.m12 * v.y, m22 := m.m22 * v.y, m32 := m.m32 * v.y }

/-- `Vector2Extensions.Transform(pos, mat)`
(`osu.Framework/Graphics/Vector2Extensions.cs:27-31`):
`X = M.Row0.X * pos.X + M.Row1.X * pos.Y + M.Row2.X`, same for Y. -/
@[inline] def transform (m : Mat3) (p : Vec2) : Vec2 :=
  ⟨m.m11 * p.x + m.m21 * p.y + m.m31, m.m12 * p.x + m.m22 * p.y + m.m32⟩
end Mat3

/-- `osu.Framework.Graphics.DrawInfo` (`Graphics/DrawInfo.cs`). -/
structure DrawInfo where
  matrix : Mat3
  inverse : Mat3
deriving Inhabited, Repr

namespace DrawInfo
/-- `DrawInfo.ApplyTransform(translation, scale, rotation = 0, shear = 0, origin)` (`DrawInfo.cs:31-71`),
restricted to rotation 0 and shear 0 (the only case reachable without BarrelRoll-type mods). The
`!= Vector2.Zero` / `!= Vector2.One` tests are float comparisons. Zero-scale clamping (FLOAT_EPSILON)
is included for completeness. -/
def applyTransform (di : DrawInfo) (translation scale origin : Vec2) : DrawInfo := Id.run do
  let mut m := di.matrix
  let mut mi := di.inverse
  if !(translation.eq Vec2.zero) then
    m := m.translateFromLeft translation
    mi := mi.translateFromRight (-translation)
  if !(scale.eq ⟨1, 1⟩) then
    -- Precision.FLOAT_EPSILON = 1e-3f; `Math.Sign(scale.X == 0 ? 1 : scale.X) * FLOAT_EPSILON`.
    let eps : F32 := Float32.ofBits 0x3A83126F
    let fix (s : F32) : F32 :=
      if F32.abs s < eps then (if s == 0 then eps else if s < 0 then -eps else eps) else s
    let s : Vec2 := ⟨fix scale.x, fix scale.y⟩
    m := m.scaleFromLeft s
    mi := mi.scaleFromRight ⟨1 / s.x, 1 / s.y⟩
  if !(origin.eq Vec2.zero) then
    m := m.translateFromLeft (-origin)
    mi := mi.translateFromRight origin
  return ⟨m, mi⟩

/-- `RotateFromLeft(m, rad)`: `row0' = Row0*cos + Row1*sin; Row1 = Row1*cos - Row0*sin` (`MatrixExtensions.cs`, cosf/sinf). -/
def rotL (m : Mat3) (rad : F32) : Mat3 :=
  let c := F32.cos rad
  let s := F32.sin rad
  { m with m11 := m.m11 * c + m.m21 * s, m12 := m.m12 * c + m.m22 * s, m13 := m.m13 * c + m.m23 * s
           m21 := m.m21 * c - m.m11 * s, m22 := m.m22 * c - m.m12 * s, m23 := m.m23 * c - m.m13 * s }
/-- `RotateFromRight(m, rad)`: per row `m1 = M1*cos - M2*sin; M2 = M2*cos + M1*sin; M1 = m1`. -/
def rotR (m : Mat3) (rad : F32) : Mat3 :=
  let c := F32.cos rad
  let s := F32.sin rad
  { m with m11 := m.m11 * c - m.m12 * s, m12 := m.m12 * c + m.m11 * s
           m21 := m.m21 * c - m.m22 * s, m22 := m.m22 * c + m.m21 * s
           m31 := m.m31 * c - m.m32 * s, m32 := m.m32 * c + m.m31 * s }

/-- `DrawInfo.ApplyTransform(translation, scale, rotation, shear = 0, origin)` (`DrawInfo.cs:31-71`; same as
`Net.Framework.DrawInfo.applyTransform`, nettest op 143). Rotation `float.DegreesToRadians(r) = (r * Pi) / 180f`. -/
def applyTransformR (di : DrawInfo) (translation scale : Vec2) (rotation : F32) (origin : Vec2) : DrawInfo :=
  if rotation == 0 then di.applyTransform translation scale origin else Id.run do
  let mut m := di.matrix
  let mut mi := di.inverse
  if !(translation.eq Vec2.zero) then
    m := m.translateFromLeft translation
    mi := mi.translateFromRight (-translation)
  let rad := SysMisc.F32.degreesToRadians rotation
  m := rotL m rad
  mi := rotR mi (-rad)
  if !(scale.eq ⟨1, 1⟩) then
    let eps : F32 := Float32.ofBits 0x3A83126F
    let fix (s : F32) : F32 :=
      if F32.abs s < eps then (if s == 0 then eps else if s < 0 then -eps else eps) else s
    let s : Vec2 := ⟨fix scale.x, fix scale.y⟩
    m := m.scaleFromLeft s
    mi := mi.scaleFromRight ⟨1 / s.x, 1 / s.y⟩
  if !(origin.eq Vec2.zero) then
    m := m.translateFromLeft (-origin)
    mi := mi.translateFromRight origin
  return ⟨m, mi⟩

def toScreen (di : DrawInfo) (p : Vec2) : Vec2 := di.matrix.transform p
def toLocal (di : DrawInfo) (p : Vec2) : Vec2 := di.inverse.transform p
end DrawInfo

/-- `osu.Game.Rulesets.Scoring.HitResult` (declaration order = enum values; `LegacyComboIncrease = 99`). -/
inductive HitResult where
  | none | miss | meh | ok | good | great | perfect
  | smallTickMiss | smallTickHit | largeTickMiss | largeTickHit
  | smallBonus | largeBonus | ignoreMiss | ignoreHit | comboBreak | sliderTailHit
  | legacyComboIncrease
deriving Inhabited, Repr, DecidableEq, BEq

namespace HitResult
def all : List HitResult :=
  [none, miss, meh, ok, good, great, perfect, smallTickMiss, smallTickHit, largeTickMiss, largeTickHit,
   smallBonus, largeBonus, ignoreMiss, ignoreHit, comboBreak, sliderTailHit, legacyComboIncrease]

def toNat : HitResult → Nat
  | none => 0 | miss => 1 | meh => 2 | ok => 3 | good => 4 | great => 5 | perfect => 6
  | smallTickMiss => 7 | smallTickHit => 8 | largeTickMiss => 9 | largeTickHit => 10
  | smallBonus => 11 | largeBonus => 12 | ignoreMiss => 13 | ignoreHit => 14 | comboBreak => 15
  | sliderTailHit => 16 | legacyComboIncrease => 99

/-- C# `ToString()` of the enum value (as printed by the oracle). -/
def name : HitResult → String
  | none => "None" | miss => "Miss" | meh => "Meh" | ok => "Ok" | good => "Good" | great => "Great"
  | perfect => "Perfect" | smallTickMiss => "SmallTickMiss" | smallTickHit => "SmallTickHit"
  | largeTickMiss => "LargeTickMiss" | largeTickHit => "LargeTickHit" | smallBonus => "SmallBonus"
  | largeBonus => "LargeBonus" | ignoreMiss => "IgnoreMiss" | ignoreHit => "IgnoreHit"
  | comboBreak => "ComboBreak" | sliderTailHit => "SliderTailHit" | legacyComboIncrease => "LegacyComboIncrease"

def ofName? (s : String) : Option HitResult := all.find? (·.name == s)

/-- `HitResultExtensions.AffectsCombo` (`osu.Game/Rulesets/Scoring/HitResult.cs`). -/
def affectsCombo : HitResult → Bool
  | miss | meh | ok | good | great | perfect | largeTickHit | largeTickMiss | legacyComboIncrease
  | comboBreak | sliderTailHit => true
  | _ => false

/-- `HitResultExtensions.IsHit` -/
def isHit : HitResult → Bool
  | none | ignoreMiss | miss | smallTickMiss | largeTickMiss | comboBreak => false
  | _ => true

def increasesCombo (r : HitResult) : Bool := r.affectsCombo && r.isHit
def breaksCombo (r : HitResult) : Bool := r.affectsCombo && !r.isHit

def isBonus : HitResult → Bool
  | smallBonus | largeBonus => true
  | _ => false

def isTick : HitResult → Bool
  | largeTickHit | largeTickMiss | smallTickHit | smallTickMiss | sliderTailHit => true
  | _ => false

/-- `IsScorable`: `LegacyComboIncrease`, `ComboBreak`, `SliderTailHit` → true; else `Miss <= r < IgnoreMiss`. -/
def isScorable (r : HitResult) : Bool :=
  match r with
  | legacyComboIncrease | comboBreak | sliderTailHit => true
  | _ => 1 ≤ r.toNat && r.toNat < 13

/-- `AffectsAccuracy` -/
def affectsAccuracy (r : HitResult) : Bool :=
  match r with
  | legacyComboIncrease | comboBreak => false
  | _ => r.isScorable && !r.isBonus

def isBasic (r : HitResult) : Bool :=
  match r with
  | legacyComboIncrease | comboBreak => false
  | _ => r.isScorable && !r.isTick && !r.isBonus
end HitResult

/-- `Precision.AlmostEquals(double, double, 1e-7)`: `Math.Abs(a - b) <= acceptableDifference`. -/
def almostEqualsD (a b : F64) (eps : F64 := Float.ofBits 0x3E7AD7F29ABCAF48) : Bool :=
  F64.abs (a - b) ≤ eps

/-- `Array.BinarySearch` / `List<T>.BinarySearch` (`ArraySortHelper<T>.BinarySearch`): inclusive bounds
`lo = 0, hi = n - 1`, probe `i = lo + ((hi - lo) >> 1)`, `cmp(array[i], value)`; returns the index or the bitwise
complement of the insertion point (negative). Written over the half-open range `[lo, hi)` (`hi` = inclusive bound + 1)
so that every access is provably in bounds. -/
def bsearchBy {α : Type} (a : Array α) (cmp : α → Int) (lo hi : Nat) (h : hi ≤ a.size) : Int :=
  if hlt : lo < hi then
    let mid := lo + (hi - 1 - lo) / 2
    have hm : mid < a.size := by omega
    let c := cmp a[mid]
    if c == 0 then (mid : Int)
    else if c < 0 then bsearchBy a cmp (mid + 1) hi h
    else bsearchBy a cmp lo mid (by omega)
  else -(lo : Int) - 1
termination_by hi - lo

/-- Insertion point for a stable insertion sort: scanning from the end, after the last element `e` with `!(lt x e)`
(`while (i > 0 && lt(x, out[i-1])) i--`). -/
def insPos {α : Type} (lt : α → α → Bool) (out : Array α) (x : α) : (i : Nat) → i ≤ out.size → Nat
  | 0, _ => 0
  | i + 1, h => if lt x (out[i]'(by omega)) then insPos lt out x i (by omega) else i + 1

/-- Stable insertion sort. -/
def stableSortBy {α : Type} (xs : Array α) (lt : α → α → Bool) : Array α := Id.run do
  let mut out : Array α := #[]
  for x in xs do
    let p := insPos lt out x out.size (Nat.le_refl _)
    out := (out.extract 0 p).push x ++ out.extract p out.size
  return out

def bsearch {α : Type} (a : Array α) (cmp : α → Int) : Int := bsearchBy a cmp 0 a.size (Nat.le_refl _)

/-- C# `x % y` for doubles is `fmod`; for `y = 1` and finite `|x| < 2^52` it is `x - Truncate(x)`
(exact). Only used with that divisor. -/
def fmod1 (x : F64) : F64 :=
  if F64.abs x < F64.integerBoundary then
    let r := x - F64.truncate x
    if r == 0 then F64.copySign 0 x else r
  else if x.isNaN || F64.abs x == F64.posInf then F64.nan
  else F64.copySign 0 x

/-- Hex helpers for raw bit dumps. -/
def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
def toHexN (n : Nat) (digits : Nat) : String := Id.run do
  let mut s := ""
  let mut v := n
  for _ in [0:digits] do
    s := (hexDigit (v % 16)).toString ++ s
    v := v / 16
  return "0x" ++ s
def F64.hex (x : F64) : String := toHexN x.toBits.toNat 16
def F32.hex (x : F32) : String := toHexN x.toBits.toNat 8

end OsuModel.Sim
