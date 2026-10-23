import OsuModel.Net

/-!
# Differential tester: .NET results (stdin, from `nettest/` C# generator) vs the Lean model.

`dotnet nettest/bin/Release/net10.0/nettest.dll gen <count> <seed> | lake exe nettest`

Float outputs are compared bit-for-bit, except that any NaN matches any NaN (the model has a
single NaN); NaN sign/payload differences are counted separately for information.
For Lean-core operations whose compiled code is the C operator (`+ - * /`, comparisons) the
tester additionally evaluates Lean's *logical* model (`Float.Model`, what the kernel computes)
and checks it against .NET too (ops ≥ 150).
-/

/-!
# Differential-test dispatch for the library primitives (Random, decimal, osuTK, osu-framework)

Generic record format (written by `nettest/Gen2.cs`): `op:u8`, then the inputs and the .NET
outputs as typed words according to `sig op` (`f` = float32 bits, `d` = float64 bits, `i` = 32-bit
integer, compared exactly). A first output of type `i` named "status" is the exception code
(0 = ok, see `exnCode`); on an exception the remaining outputs are 0 on both sides.
Variable-length ops (110 Random, 222 Average) have their own readers in `Main.lean`.
-/

open OsuModel.Net OsuModel.Net.OsuTK OsuModel.Net.Framework

namespace NetTestExtra

inductive Ty | f | d | i
deriving BEq

def wordsOf : Ty → Nat | .f => 4 | .d => 8 | .i => 4

open Ty in
/-- (inputs, outputs) per op. -/
def sig : Nat → Option (List Ty × List Ty)
  | 111 | 112 => some ([d], [i, i, i, i, i])
  | 113 | 114 => some ([f], [i, i, i, i, i])
  | 115 => some ([i, i, i, i], [d])
  | 116 => some ([i, i, i, i], [f])
  | 117 | 118 => some ([i, i, i, i, i, i, i, i], [i, i, i, i, i])
  | 119 => some ([i, i, i, i], [i, i, i, i])
  | 120 | 121 | 122 => some ([f, f], [f])
  | 131 => some ([f], [f])
  | 123 | 124 | 126 | 133 => some ([f, f, f, f], [f])
  | 125 | 132 => some ([f, f], [f, f])
  | 127 => some ([f, f, f, f, f], [f, f])
  | 128 => some ([f, f, f, f, f, f], [f, f])
  | 129 => some ([f, f], [f, f, f, f, f, f])
  | 130 => some ([f, f, f, f, f], List.replicate 14 f)
  | 134 => some ([f, f, f, f], [f, f, f, f])
  | 135 => some (List.replicate 18 f, List.replicate 9 f)
  | 136 => some ([f, d], [f, f, d, d])
  | 138 => some ([], List.replicate 6 f ++ [d, d])
  | 140 => some (List.replicate 11 f, [f, f])
  | 141 => some ([f, f, f, f], [f, f])
  | 142 => some (List.replicate 12 f, List.replicate 72 f)
  | 143 => some (List.replicate 27 f, List.replicate 18 f)
  | 144 => some ([f, f, f], [i])
  | 145 => some ([d, d, d], [i])
  | 146 => some ([d, d, d, d], [i, d])
  | 147 => some ([f, f, f, f], [i, f])
  | 148 => some ([d, d, d, d], [i, d])
  | 149 => some ([f, f, f, f], [i, f])
  | 210 => some ([i, d], [d])
  | 211 => some ([i, d, d, d, d, d], [d])
  | 212 => some ([i, d, f, f, d, d], [f])
  | 213 => some ([i, d, f, f, f, f, d, d], [f, f])
  | 214 => some ([i, d, i, i, d, d], [i])
  | 215 => some ([d, d, d, d], [d, d, i, d])
  | 220 => some ([f], [f, f])
  | 221 => some ([d], [d, d])
  | 230 => some ([d, d, d, d, d], [d])
  | 231 => some ([f, f, f, f, d], [f])
  | _ => none

def name : Nat → String
  | 110 => "System.Random(seed) sequences" | 111 => "decimal.CreateTruncating(double)"
  | 112 => "(decimal)double" | 113 => "decimal.CreateTruncating(float)" | 114 => "(decimal)float"
  | 115 => "(double)decimal" | 116 => "(float)decimal" | 117 => "decimal / decimal"
  | 118 => "decimal * decimal" | 119 => "Math.Round(decimal)"
  | 120 => "osuTK Vector2.Length" | 121 => "osuTK Vector2.LengthSquared" | 122 => "osuTK Vector2.LengthFast"
  | 123 => "osuTK Vector2.Distance" | 124 => "osuTK Vector2.DistanceSquared" | 125 => "osuTK Vector2.Normalized"
  | 126 => "osuTK Vector2.Dot" | 127 => "osuTK Vector2.Lerp" | 128 => "osuTK Vector2.Clamp"
  | 129 => "osuTK Vector2 neg/PerpRight/PerpLeft" | 130 => "osuTK Vector2 + - *s s* *v /s Divide"
  | 131 => "osuTK MathHelper.InverseSqrtFast" | 132 => "osuTK Vector2.NormalizeFast" | 133 => "osuTK Vector2.PerpDot"
  | 134 => "osuTK Vector2.ComponentMin/Max" | 135 => "osuTK Matrix3.Mult"
  | 136 => "osuTK MathHelper.Deg/Rad (float, double)" | 138 => "osuTK MathHelper constants"
  | 140 => "fw Vector2Extensions.Transform" | 141 => "fw Vector2Extensions.Distance(Squared)"
  | 142 => "fw MatrixExtensions (8 ops)" | 143 => "fw DrawInfo.ApplyTransform"
  | 144 => "fw Precision (float)" | 145 => "fw Precision (double)"
  | 146 => "fw BindableDouble.Value=" | 147 => "fw BindableFloat.Value="
  | 148 => "fw BindableDouble initialiser" | 149 => "fw BindableFloat initialiser"
  | 210 => "fw Easing (DefaultEasingFunction)" | 211 => "fw Interpolation.ValueAt(double)"
  | 212 => "fw Interpolation.ValueAt(float)" | 213 => "fw Interpolation.ValueAt(Vector2)"
  | 214 => "fw Interpolation.ValueAt(int)" | 215 => "fw Lerp/DampContinuously/Damp"
  | 220 => "float.DegreesToRadians/RadiansToDegrees" | 221 => "double.DegreesToRadians/RadiansToDegrees"
  | 222 => "Enumerable.Average(List<double>)"
  | 230 => "lazer APIMod.ToMod double setting" | 231 => "lazer APIMod.ToMod float setting"
  | n => s!"op{n}"

def exnCode : NetExn → Nat
  | .format => 1 | .overflow => 2 | .argument => 3 | .argumentOutOfRange => 4 | .arithmetic => 5

@[inline] def wf (x : F32) : UInt64 := x.toBits.toUInt64
@[inline] def wd (x : F64) : UInt64 := x.toBits
@[inline] def wi (x : Int32) : UInt64 := x.toUInt32.toUInt64
@[inline] def wb (b : Bool) : Nat := if b then 1 else 0

def decWords (d : NetDecimal) : List UInt64 :=
  let (a, b, c, e) := d.getBits
  [a.toUInt64, b.toUInt64, c.toUInt64, e.toUInt64]

def withStatus (n : Nat) (r : Except NetExn (List UInt64)) : List UInt64 :=
  match r with
  | .ok ws => 0 :: ws
  | .error e => (exnCode e).toUInt64 :: List.replicate n 0

def vecW (v : Vector2) : List UInt64 := [wf v.x, wf v.y]
def matW (m : Matrix3) : List UInt64 := m.toList.map wf

/-- Evaluate the Lean model on raw input words. -/
def eval (op : Nat) (a : Array UInt64) : List UInt64 :=
  let F (k : Nat) : F32 := Float32.ofBits a[k]!.toUInt32
  let D (k : Nat) : F64 := Float.ofBits a[k]!
  let I (k : Nat) : Int32 := a[k]!.toUInt32.toInt32
  let U (k : Nat) : UInt32 := a[k]!.toUInt32
  let V (k : Nat) : Vector2 := ⟨F k, F (k+1)⟩
  let M (k : Nat) : Matrix3 := Matrix3.ofList ((List.range 9).map fun j => F (k + j))
  let DEC (k : Nat) : NetDecimal := NetDecimal.ofBits (U k) (U (k+1)) (U (k+2)) (U (k+3))
  match op with
  | 111 => withStatus 4 ((NetDecimal.createTruncatingF64 (D 0)).map decWords)
  | 112 => withStatus 4 ((NetDecimal.ofF64 (D 0)).map decWords)
  | 113 => withStatus 4 ((NetDecimal.createTruncatingF32 (F 0)).map decWords)
  | 114 => withStatus 4 ((NetDecimal.ofF32 (F 0)).map decWords)
  | 115 => [wd (DEC 0).toF64]
  | 116 => [wf (DEC 0).toF32]
  | 117 => withStatus 4 ((NetDecimal.div (DEC 0) (DEC 4)).map decWords)
  | 118 => withStatus 4 ((NetDecimal.mul (DEC 0) (DEC 4)).map decWords)
  | 119 => decWords (NetDecimal.round (DEC 0))
  | 120 => [wf (V 0).length]
  | 121 => [wf (V 0).lengthSquared]
  | 122 => [wf (MathHelper.lengthFast (V 0))]
  | 123 => [wf (Vector2.distance (V 0) (V 2))]
  | 124 => [wf (Vector2.distanceSquared (V 0) (V 2))]
  | 125 => vecW (V 0).normalized
  | 126 => [wf (Vector2.dot (V 0) (V 2))]
  | 127 => vecW (Vector2.lerp (V 0) (V 2) (F 4))
  | 128 => vecW (Vector2.clamp (V 0) (V 2) (V 4))
  | 129 => vecW (-(V 0)) ++ vecW (V 0).perpendicularRight ++ vecW (V 0).perpendicularLeft
  | 130 =>
    let x := V 0; let y := V 2; let s := F 4
    vecW (x + y) ++ vecW (x - y) ++ vecW (x * s) ++ vecW (s * x) ++ vecW (Vector2.mul x y) ++ vecW (x / s) ++
      vecW (Vector2.divide x y)
  | 131 => [wf (MathHelper.inverseSqrtFast (F 0))]
  | 132 => vecW (MathHelper.normalizeFast (V 0))
  | 133 => [wf (Vector2.perpDot (V 0) (V 2))]
  | 134 => vecW (Vector2.componentMin (V 0) (V 2)) ++ vecW (Vector2.componentMax (V 0) (V 2))
  | 135 => matW (Matrix3.mult (M 0) (M 9))
  | 136 => [wf (MathHelper.degreesToRadiansF (F 0)), wf (MathHelper.radiansToDegreesF (F 0)),
            wd (MathHelper.degreesToRadiansD (D 1)), wd (MathHelper.radiansToDegreesD (D 1))]
  | 138 => [MathHelper.pi, MathHelper.twoPi, MathHelper.piOver2, MathHelper.piOver4,
            MathHelper.degToRadF, MathHelper.radToDegF].map wf ++ [wd MathHelper.degToRadD, wd MathHelper.radToDegD]
  | 140 => vecW (Vector2Extensions.transform (V 0) (M 2))
  | 141 => [wf (Vector2Extensions.distance (V 0) (V 2)), wf (Vector2Extensions.distanceSquared (V 0) (V 2))]
  | 142 =>
    let m := M 0; let v := V 9; let r := F 11
    open MatrixExtensions in
    matW (translateFromLeft m v) ++ matW (translateFromRight m v) ++ matW (rotateFromLeft m r) ++
    matW (rotateFromRight m r) ++ matW (scaleFromLeft m v) ++ matW (scaleFromRight m v) ++
    matW (shearFromLeft m v) ++ matW (shearFromRight m v)
  | 143 =>
    let di : DrawInfo := ⟨M 0, M 9⟩
    let r := di.applyTransform (V 18) (V 20) (F 22) (V 23) (V 25)
    matW r.matrix ++ matW r.matrixInverse
  | 144 =>
    let x := F 0; let y := F 1; let e := F 2
    open Precision in
    [(wb (definitelyBiggerF x y e) ||| (wb (almostBiggerF x y e) <<< 1) ||| (wb (almostEqualsF x y e) <<< 2) |||
      (wb (definitelyBiggerF x y) <<< 3) ||| (wb (almostBiggerF x y) <<< 4) ||| (wb (almostEqualsF x y) <<< 5) |||
      (wb (almostEqualsV ⟨x, y⟩ ⟨y, x⟩ e) <<< 6)).toUInt64]
  | 145 =>
    let x := D 0; let y := D 1; let e := D 2
    open Precision in
    [(wb (definitelyBiggerD x y e) ||| (wb (almostBiggerD x y e) <<< 1) ||| (wb (almostEqualsD x y e) <<< 2) |||
      (wb (definitelyBiggerD x y) <<< 3) ||| (wb (almostBiggerD x y) <<< 4) ||| (wb (almostEqualsD x y) <<< 5)).toUInt64]
  | 146 => withStatus 1 ((Bindable.BD.init 0 (D 0) (D 1) (D 2) >>= (·.setValue (D 3))).map fun (s : Bindable.BD) => [wd s.value])
  | 147 => withStatus 1 ((Bindable.BF.init 0 (F 0) (F 1) (F 2) >>= (·.setValue (F 3))).map fun (s : Bindable.BF) => [wf s.value])
  | 148 => withStatus 1 ((Bindable.BD.init (D 0) (D 1) (D 2) (D 3)).map fun (s : Bindable.BD) => [wd s.value])
  | 149 => withStatus 1 ((Bindable.BF.init (F 0) (F 1) (F 2) (F 3)).map fun (s : Bindable.BF) => [wf s.value])
  | 210 => [wd (applyEasing (Easing.ofIndex (I 0).toInt.toNat) (D 1))]
  | 211 => [wd (Interpolation.valueAtD (D 1) (D 2) (D 3) (D 4) (D 5) (Easing.ofIndex (I 0).toInt.toNat))]
  | 212 => [wf (Interpolation.valueAtF (D 1) (F 2) (F 3) (D 4) (D 5) (Easing.ofIndex (I 0).toInt.toNat))]
  | 213 => vecW (Interpolation.valueAtV (D 1) (V 2) (V 4) (D 6) (D 7) (Easing.ofIndex (I 0).toInt.toNat))
  | 214 => [wi (Interpolation.valueAtI (D 1) (I 2) (I 3) (D 4) (D 5) (Easing.ofIndex (I 0).toInt.toNat))]
  | 215 =>
    [wd (Interpolation.lerp (D 0) (D 1) (D 2)), wd (Interpolation.dampContinuously (D 0) (D 1) (D 2) (D 3))] ++
      withStatus 1 ((Interpolation.damp (D 0) (D 1) (D 2) (D 3)).map fun x => [wd x])
  | 220 => [wf (SysMisc.F32.degreesToRadians (F 0)), wf (SysMisc.F32.radiansToDegrees (F 0))]
  | 221 => [wd (SysMisc.F64.degreesToRadians (D 0)), wd (SysMisc.F64.radiansToDegrees (D 0))]
  -- lazer: input json value (as double), real bindable's min, max, precision → stored value
  -- lazer mod setting: (default, MinValue, MaxValue, Precision) of the real bindable, JSON value
  | 230 => withStatus 1 ((Bindable.BD.init (D 0) (D 1) (D 2) (D 3) >>= (·.setValue (D 4))).map fun (s : Bindable.BD) => [wd s.value]) |>.drop 1
  | 231 => withStatus 1 ((Bindable.BF.init (F 0) (F 1) (F 2) (F 3) >>= (·.setValue (F64.toF32 (D 4)))).map fun (s : Bindable.BF) => [wf s.value]) |>.drop 1
  | _ => []

end NetTestExtra

open OsuModel.Net

structure Stat where
  pass : Nat := 0
  fail : Nat := 0
  nanDiff : Nat := 0
  shown : Nat := 0
  snan : Nat := 0
deriving Inhabited

def opName : Nat → String
  | 1 => "f64 +" | 2 => "f64 -" | 3 => "f64 *" | 4 => "f64 /" | 5 => "f64 compare"
  | 6 => "f32 +" | 7 => "f32 -" | 8 => "f32 *" | 9 => "f32 /" | 10 => "f32 compare"
  | 11 => "(float)double" | 12 => "(double)float" | 13 => "(double)int" | 14 => "(double)long"
  | 15 => "(double)ulong" | 16 => "(float)int" | 17 => "(float)long" | 18 => "(float)ulong"
  | 19 => "(double)uint" | 20 => "(float)uint"
  | 21 => "(int)double" | 22 => "(long)double" | 23 => "(uint)double" | 24 => "(ulong)double"
  | 25 => "(int)float" | 26 => "(long)float" | 27 => "(uint)float" | 28 => "(ulong)float"
  | 30 => "Math.Round" | 31 => "Math.Round(Away)" | 32 => "Math.Floor" | 33 => "Math.Ceiling"
  | 34 => "Math.Truncate" | 35 => "Math.Abs" | 36 => "Math.Sqrt" | 37 => "f64 neg"
  | 40 => "MathF.Round" | 41 => "MathF.Round(Away)" | 42 => "MathF.Floor" | 43 => "MathF.Ceiling"
  | 44 => "MathF.Truncate" | 45 => "MathF.Abs" | 46 => "MathF.Sqrt" | 47 => "f32 neg"
  | 50 => "Math.Max(double)" | 51 => "Math.Min(double)" | 52 => "MathF.Max" | 53 => "MathF.Min"
  | 54 => "Math.Clamp(double)" | 55 => "Math.Clamp(float)" | 56 => "Math.Sign(double)" | 57 => "Math.Sign(float)"
  | 58 => "Math.Round(double,digits)" | 59 => "MathF.Round(float,digits)"
  | 60 => "Math.Sin" | 61 => "Math.Cos" | 62 => "Math.Tan" | 63 => "Math.Asin" | 64 => "Math.Acos"
  | 65 => "Math.Atan" | 66 => "Math.Atan2" | 67 => "Math.Exp" | 68 => "Math.Log" | 69 => "Math.Log10"
  | 70 => "Math.Pow" | 71 => "Math.Cbrt" | 73 => "Math.Log(a,base)"
  | 80 => "MathF.Sin" | 81 => "MathF.Cos" | 82 => "MathF.Tan" | 83 => "MathF.Asin" | 84 => "MathF.Acos"
  | 85 => "MathF.Atan" | 86 => "MathF.Atan2" | 87 => "MathF.Exp" | 88 => "MathF.Log" | 90 => "MathF.Pow"
  | 100 => "double.Parse" | 101 => "float.Parse" | 102 => "int.Parse"
  | 103 => "Parsing.ParseDouble" | 104 => "Parsing.ParseFloat" | 105 => "Parsing.ParseInt"
  | 151 => "model: Float.Model +" | 152 => "model: Float.Model -" | 153 => "model: Float.Model *"
  | 154 => "model: Float.Model /" | 155 => "model: Float.Model compare"
  | 156 => "model: Float32.Model +" | 157 => "model: Float32.Model -" | 158 => "model: Float32.Model *"
  | 159 => "model: Float32.Model /" | 160 => "model: Float32.Model compare"
  | 186 => "model: Float.Model.sqrt" | 196 => "model: Float32.Model.sqrt"
  | 200 => "Lean Float.ofScientific vs double.Parse" | 201 => "Lean Float32.ofScientific vs float.Parse"
  | n => NetTestExtra.name n

def hex (n : Nat) (w : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  "0x" ++ String.ofList (List.replicate (w - s.length) '0') ++ s

@[inline] def rd8 (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat
@[inline] def rd16 (b : ByteArray) (i : Nat) : Nat := rd8 b i ||| (rd8 b (i+1) <<< 8)
@[inline] def rd32 (b : ByteArray) (i : Nat) : UInt32 :=
  (b.get! i).toUInt32 ||| ((b.get! (i+1)).toUInt32 <<< 8) ||| ((b.get! (i+2)).toUInt32 <<< 16) ||| ((b.get! (i+3)).toUInt32 <<< 24)
@[inline] def rd64 (b : ByteArray) (i : Nat) : UInt64 :=
  (rd32 b i).toUInt64 ||| ((rd32 b (i+4)).toUInt64 <<< 32)

@[inline] def nan64 (x : UInt64) : Bool := (x &&& 0x7FF0000000000000) == 0x7FF0000000000000 && (x &&& 0x000FFFFFFFFFFFFF) != 0
@[inline] def nan32 (x : UInt32) : Bool := (x &&& 0x7F800000) == 0x7F800000 && (x &&& 0x007FFFFF) != 0
/-- signaling NaN (quiet bit clear): not representable in Lean (runtime and model canonicalise NaN). -/
@[inline] def snan64 (x : UInt64) : Bool := nan64 x && (x &&& 0x0008000000000000) == 0
@[inline] def snan32 (x : UInt32) : Bool := nan32 x && (x &&& 0x00400000) == 0

/-- (match, nanPayloadDiffers) -/
@[inline] def cmp64 (exp got : UInt64) : Bool × Bool :=
  if nan64 exp then (nan64 got, nan64 got && exp != got) else (exp == got, false)
@[inline] def cmp32 (exp got : UInt32) : Bool × Bool :=
  if nan32 exp then (nan32 got, nan32 got && exp != got) else (exp == got, false)

def exnCode : NetExn → Nat
  | .format => 1 | .overflow => 2 | .argument => 3 | .argumentOutOfRange => 4 | .arithmetic => 5

def cmpFlags64 (x y : F64) : Nat :=
  (if x < y then 1 else 0) ||| (if x ≤ y then 2 else 0) ||| (if x == y then 4 else 0) |||
  (if y < x then 8 else 0) ||| (if y ≤ x then 16 else 0) ||| (if !(x == y) then 32 else 0)
def cmpFlags32 (x y : F32) : Nat :=
  (if x < y then 1 else 0) ||| (if x ≤ y then 2 else 0) ||| (if x == y then 4 else 0) |||
  (if y < x then 8 else 0) ||| (if y ≤ x then 16 else 0) ||| (if !(x == y) then 32 else 0)
def mFlags64 (x y : Float.Model) : Nat :=
  (if x.lt y then 1 else 0) ||| (if x.le y then 2 else 0) ||| (if x.beq y then 4 else 0) |||
  (if y.lt x then 8 else 0) ||| (if y.le x then 16 else 0) ||| (if !(x.beq y) then 32 else 0)
def mFlags32 (x y : Float32.Model) : Nat :=
  (if x.lt y then 1 else 0) ||| (if x.le y then 2 else 0) ||| (if x.beq y then 4 else 0) |||
  (if y.lt x then 8 else 0) ||| (if y.le x then 16 else 0) ||| (if !(x.beq y) then 32 else 0)

abbrev Stats := Array Stat

def record (st : Stats) (op : Nat) (ok nanD : Bool) (msg : Unit → String) (snanIn := false) : IO Stats := do
  let s := st[op]!
  if !ok && snanIn then return st.set! op { s with snan := s.snan + 1 }
  let s := if ok then { s with pass := s.pass + 1, nanDiff := s.nanDiff + (if nanD then 1 else 0) }
           else { s with fail := s.fail + 1 }
  let s ← if !ok && s.shown < 8 then do
      IO.eprintln s!"FAIL {opName op}: {msg ()}"; pure { s with shown := s.shown + 1 }
    else pure s
  return st.set! op s

def u64res (e : Except NetExn UInt64) : Nat × UInt64 :=
  match e with | .ok v => (0, v) | .error x => (exnCode x, 0)

/-- Process one record at `i`; returns the next offset. -/
def step (b : ByteArray) (i : Nat) (st : Stats) : IO (Nat × Stats) := do
  let op := rd8 b i
  let i := i + 1
  -- binary f64 → f64
  if op ∈ [1, 2, 3, 4, 50, 51, 66, 70, 73] then
    let a := rd64 b i; let c := rd64 b (i+8); let r := rd64 b (i+16)
    let x := Float.ofBits a; let y := Float.ofBits c
    let got : F64 := match op with
      | 1 => x + y | 2 => x - y | 3 => x * y | 4 => x / y | 50 => F64.max x y | 51 => F64.min x y
      | 66 => F64.atan2 x y | 70 => F64.pow x y | _ => F64.logBase x y
    let (ok, nd) := cmp64 r got.toBits
    let msg := fun _ => s!"{hex a.toNat 16} {hex c.toNat 16} -> .NET {hex r.toNat 16} Lean {hex got.toBits.toNat 16}"
    let mut st ← record st op ok nd msg (op ≥ 60 && (snan64 a || snan64 c))
    if op ≤ 4 then
      let mx := Float.Model.ofBits a; let my := Float.Model.ofBits c
      let mg := match op with | 1 => mx + my | 2 => mx - my | 3 => mx * my | _ => mx / my
      let (ok2, _) := cmp64 r mg.toBits
      st ← record st (op + 150) ok2 false fun _ => s!"{hex a.toNat 16} {hex c.toNat 16} -> .NET {hex r.toNat 16} model {hex mg.toBits.toNat 16}"
    return (i + 24, st)
  else if op == 5 then
    let a := rd64 b i; let c := rd64 b (i+8); let r := rd8 b (i+16)
    let g := cmpFlags64 (Float.ofBits a) (Float.ofBits c)
    let st ← record st op (g == r) false fun _ => s!"{hex a.toNat 16} {hex c.toNat 16} .NET {r} Lean {g}"
    let g2 := mFlags64 (Float.Model.ofBits a) (Float.Model.ofBits c)
    let st ← record st 155 (g2 == r) false fun _ => s!"{hex a.toNat 16} {hex c.toNat 16} .NET {r} model {g2}"
    return (i + 17, st)
  -- binary f32 → f32
  else if op ∈ [6, 7, 8, 9, 52, 53, 86, 90] then
    let a := rd32 b i; let c := rd32 b (i+4); let r := rd32 b (i+8)
    let x := Float32.ofBits a; let y := Float32.ofBits c
    let got : F32 := match op with
      | 6 => x + y | 7 => x - y | 8 => x * y | 9 => x / y | 52 => F32.max x y | 53 => F32.min x y
      | 86 => F32.atan2 x y | _ => F32.pow x y
    let (ok, nd) := cmp32 r got.toBits
    let mut st ← record st op ok nd (fun _ => s!"{hex a.toNat 8} {hex c.toNat 8} -> .NET {hex r.toNat 8} Lean {hex got.toBits.toNat 8}") (op ≥ 60 && (snan32 a || snan32 c))
    if op ≤ 9 then
      let mx := Float32.Model.ofBits a; let my := Float32.Model.ofBits c
      let mg := match op with | 6 => mx + my | 7 => mx - my | 8 => mx * my | _ => mx / my
      let (ok2, _) := cmp32 r mg.toBits
      st ← record st (op + 150) ok2 false fun _ => s!"{hex a.toNat 8} {hex c.toNat 8} -> .NET {hex r.toNat 8} model {hex mg.toBits.toNat 8}"
    return (i + 12, st)
  else if op == 10 then
    let a := rd32 b i; let c := rd32 b (i+4); let r := rd8 b (i+8)
    let g := cmpFlags32 (Float32.ofBits a) (Float32.ofBits c)
    let st ← record st op (g == r) false fun _ => s!"{hex a.toNat 8} {hex c.toNat 8} .NET {r} Lean {g}"
    let g2 := mFlags32 (Float32.Model.ofBits a) (Float32.Model.ofBits c)
    let st ← record st 160 (g2 == r) false fun _ => s!"{hex a.toNat 8} {hex c.toNat 8} .NET {r} model {g2}"
    return (i + 9, st)
  -- unary f64
  else if (30 ≤ op && op ≤ 37) || (60 ≤ op && op ≤ 71 && op != 66 && op != 70) then
    let a := rd64 b i; let r := rd64 b (i+8)
    let x := Float.ofBits a
    let got : F64 := match op with
      | 30 => F64.round x | 31 => F64.roundMode x .awayFromZero | 32 => F64.floor x | 33 => F64.ceiling x
      | 34 => F64.truncate x | 35 => F64.abs x | 36 => F64.sqrt x | 37 => -x
      | 60 => F64.sin x | 61 => F64.cos x | 62 => F64.tan x | 63 => F64.asin x | 64 => F64.acos x
      | 65 => F64.atan x | 67 => F64.exp x | 68 => F64.log x | 69 => F64.log10 x | _ => F64.cbrt x
    let (ok, nd) := cmp64 r got.toBits
    let mut st ← record st op ok nd (fun _ => s!"{hex a.toNat 16} -> .NET {hex r.toNat 16} Lean {hex got.toBits.toNat 16}") (op ≥ 60 && snan64 a)
    if op == 36 then
      let m := (Float.Model.ofBits a).sqrt
      st ← record st 186 (cmp64 r m.toBits).1 false fun _ => s!"{hex a.toNat 16} -> .NET {hex r.toNat 16} model {hex m.toBits.toNat 16}"
    return (i + 16, st)
  -- unary f32
  else if (40 ≤ op && op ≤ 47) || (80 ≤ op && op ≤ 88 && op != 86) then
    let a := rd32 b i; let r := rd32 b (i+4)
    let x := Float32.ofBits a
    let got : F32 := match op with
      | 40 => F32.round x | 41 => F32.roundMode x .awayFromZero | 42 => F32.floor x | 43 => F32.ceiling x
      | 44 => F32.truncate x | 45 => F32.abs x | 46 => F32.sqrt x | 47 => -x
      | 80 => F32.sin x | 81 => F32.cos x | 82 => F32.tan x | 83 => F32.asin x | 84 => F32.acos x
      | 85 => F32.atan x | 87 => F32.exp x | _ => F32.log x
    let (ok, nd) := cmp32 r got.toBits
    let mut st ← record st op ok nd (fun _ => s!"{hex a.toNat 8} -> .NET {hex r.toNat 8} Lean {hex got.toBits.toNat 8}") (op ≥ 60 && snan32 a)
    if op == 46 then
      let m := (Float32.Model.ofBits a).sqrt
      st ← record st 196 (cmp32 r m.toBits).1 false fun _ => s!"{hex a.toNat 8} -> .NET {hex r.toNat 8} model {hex m.toBits.toNat 8}"
    return (i + 8, st)
  -- conversions
  else if 11 ≤ op && op ≤ 28 then
    -- input width
    let inW := if op ∈ [12, 13, 16, 19, 20, 25, 26, 27, 28] then 4 else 8
    let a64 : UInt64 := if inW == 4 then (rd32 b i).toUInt64 else rd64 b i
    let a32 : UInt32 := a64.toUInt32
    -- output width
    let outW := if op ∈ [11, 16, 17, 18, 20] then 4 else 8
    let r64 : UInt64 := if outW == 4 then (rd32 b (i + inW)).toUInt64 else rd64 b (i + inW)
    let (ok, nd, gotN) : Bool × Bool × UInt64 := match op with
      | 11 => let g := (F64.toF32 (Float.ofBits a64)).toBits; let c := cmp32 r64.toUInt32 g; (c.1, c.2, g.toUInt64)
      | 12 => let g := (F32.toF64 (Float32.ofBits a32)).toBits; let c := cmp64 r64 g; (c.1, c.2, g)
      | 13 => let g := (F64.ofInt32 a32.toInt32).toBits; (g == r64, false, g)
      | 14 => let g := (F64.ofInt64 a64.toInt64).toBits; (g == r64, false, g)
      | 15 => let g := (F64.ofUInt64 a64).toBits; (g == r64, false, g)
      | 16 => let g := (F32.ofInt32 a32.toInt32).toBits.toUInt64; (g == r64, false, g)
      | 17 => let g := (F32.ofInt64 a64.toInt64).toBits.toUInt64; (g == r64, false, g)
      | 18 => let g := (F32.ofUInt64 a64).toBits.toUInt64; (g == r64, false, g)
      | 19 => let g := (F64.ofUInt32 a32).toBits; (g == r64, false, g)
      | 20 => let g := (F32.ofUInt32 a32).toBits.toUInt64; (g == r64, false, g)
      | 21 => let g := (F64.toInt32 (Float.ofBits a64)).toUInt32.toUInt64; (g == r64, false, g)
      | 22 => let g := (F64.toInt64 (Float.ofBits a64)).toUInt64; (g == r64, false, g)
      | 23 => let g := (F64.toUInt32 (Float.ofBits a64)).toUInt64; (g == r64, false, g)
      | 24 => let g := (F64.toUInt64 (Float.ofBits a64)); (g == r64, false, g)
      | 25 => let g := (F32.toInt32 (Float32.ofBits a32)).toUInt32.toUInt64; (g == r64, false, g)
      | 26 => let g := (F32.toInt64 (Float32.ofBits a32)).toUInt64; (g == r64, false, g)
      | 27 => let g := (F32.toUInt32 (Float32.ofBits a32)).toUInt64; (g == r64, false, g)
      | _ => let g := (F32.toUInt64 (Float32.ofBits a32)); (g == r64, false, g)
    let st ← record st op ok nd fun _ => s!"{hex a64.toNat 16} -> .NET {hex r64.toNat 16} Lean {hex gotN.toNat 16}"
    return (i + inW + outW, st)
  else if op == 54 then
    let v := rd64 b i; let lo := rd64 b (i+8); let hi := rd64 b (i+16); let s := rd8 b (i+24); let r := rd64 b (i+25)
    let (gs, g) := u64res ((F64.clamp (.ofBits v) (.ofBits lo) (.ofBits hi)).map Float.toBits)
    let ok := gs == s && (s != 0 || (cmp64 r g).1)
    let st ← record st op ok false fun _ => s!"{hex v.toNat 16} {hex lo.toNat 16} {hex hi.toNat 16} -> .NET {s}/{hex r.toNat 16} Lean {gs}/{hex g.toNat 16}"
    return (i + 33, st)
  else if op == 55 then
    let v := rd32 b i; let lo := rd32 b (i+4); let hi := rd32 b (i+8); let s := rd8 b (i+12); let r := rd32 b (i+13)
    let (gs, g) := u64res ((F32.clamp (.ofBits v) (.ofBits lo) (.ofBits hi)).map (·.toBits.toUInt64))
    let ok := gs == s && (s != 0 || (cmp32 r g.toUInt32).1)
    let st ← record st op ok false fun _ => s!"{hex v.toNat 8} {hex lo.toNat 8} {hex hi.toNat 8} -> .NET {s}/{hex r.toNat 8} Lean {gs}/{hex g.toNat 8}"
    return (i + 17, st)
  else if op == 56 || op == 57 then
    let w := if op == 56 then 8 else 4
    let a := if w == 8 then rd64 b i else (rd32 b i).toUInt64
    let s := rd8 b (i+w); let r := rd32 b (i+w+1)
    let res := if op == 56 then F64.sign (.ofBits a) else F32.sign (.ofBits a.toUInt32)
    let (gs, g) := u64res (res.map (·.toUInt32.toUInt64))
    let ok := gs == s && (s != 0 || g.toUInt32 == r)
    let st ← record st op ok false fun _ => s!"{hex a.toNat 16} -> .NET {s}/{r} Lean {gs}/{g}"
    return (i + w + 5, st)
  else if op == 58 then
    let a := rd64 b i; let d := rd8 b (i+8); let s := rd8 b (i+9); let r := rd64 b (i+10)
    let (gs, g) := u64res ((F64.roundDigits (.ofBits a) d).map Float.toBits)
    let ok := gs == s && (s != 0 || (cmp64 r g).1)
    let st ← record st op ok false fun _ => s!"{hex a.toNat 16} digits {d} -> .NET {s}/{hex r.toNat 16} Lean {gs}/{hex g.toNat 16}"
    return (i + 18, st)
  else if op == 59 then
    let a := rd32 b i; let d := rd8 b (i+4); let s := rd8 b (i+5); let r := rd32 b (i+6)
    let (gs, g) := u64res ((F32.roundDigits (.ofBits a) d).map (·.toBits.toUInt64))
    let ok := gs == s && (s != 0 || (cmp32 r g.toUInt32).1)
    let st ← record st op ok false fun _ => s!"{hex a.toNat 8} digits {d} -> .NET {s}/{hex r.toNat 8} Lean {gs}/{hex g.toNat 8}"
    return (i + 10, st)
  else if 100 ≤ op && op ≤ 105 then
    let len := rd16 b i
    let bytes := b.extract (i+2) (i+2+len)
    let s := rd8 b (i+2+len); let r := rd64 b (i+3+len)
    let str := (String.fromUTF8? bytes).getD "<invalid utf8>"
    let (gs, g) : Nat × UInt64 := match op with
      | 100 => u64res ((doubleParse str).map Float.toBits)
      | 101 => u64res ((floatParse str).map (·.toBits.toUInt64))
      | 102 => u64res ((intParse str).map (·.toUInt32.toUInt64))
      | 103 => u64res ((Parsing.parseDouble str).map Float.toBits)
      | 104 => u64res ((Parsing.parseFloat str).map (·.toBits.toUInt64))
      | _ => u64res ((Parsing.parseInt str).map (·.toUInt32.toUInt64))
    let isF := op == 100 || op == 101 || op == 103 || op == 104
    let is32 := op == 101 || op == 104
    let valOk := if !isF then g == r else if is32 then (cmp32 r.toUInt32 g.toUInt32).1 else (cmp64 r g).1
    let nd := s == 0 && isF && (if is32 then (cmp32 r.toUInt32 g.toUInt32).2 else (cmp64 r g).2)
    let ok := gs == s && (s != 0 || valOk)
    let mut st ← record st op ok nd fun _ => s!"{repr str} -> .NET {s}/{hex r.toNat 16} Lean {gs}/{hex g.toNat 16}"
    -- Lean core's `Float.ofScientific` (claimed correctly rounded) vs .NET, on plain numbers
    if (op == 100 || op == 101) && s == 0 then
      match Parse.parseNumber str.toList with
      | some n =>
        if n.sat.isNone && n.exp10.natAbs < 2000 && n.mant < 10 ^ 1000 then
          let neg := n.exp10 < 0
          if op == 100 then
            let v : Float := Float.ofScientific n.mant neg n.exp10.natAbs
            let v := if n.neg then -v else v
            st ← record st 200 (cmp64 r v.toBits).1 false fun _ => s!"{repr str} -> .NET {hex r.toNat 16} ofScientific {hex v.toBits.toNat 16}"
          else
            let v : Float32 := Float32.ofScientific n.mant neg n.exp10.natAbs
            let v := if n.neg then -v else v
            st ← record st 201 (cmp32 r.toUInt32 v.toBits).1 false fun _ => s!"{repr str} -> .NET {hex r.toNat 8} ofScientific {hex v.toBits.toNat 8}"
      | none => pure ()
    return (i + 11 + len, st)
  else if op == 110 then
    -- System.Random: seed, count, then (kind, a, b, result) per call
    let seed := (rd32 b i).toInt32
    let n := rd16 b (i+4)
    let mut j := i + 6
    let mut rs := NetRandom.create seed
    let mut st := st
    for _ in [0:n] do
      let kind := rd8 b j; let x := (rd32 b (j+1)).toInt32; let y := (rd32 b (j+5)).toInt32; let r := rd64 b (j+9)
      let (g, rs', isD, isF) : UInt64 × NetRandom.State × Bool × Bool := match kind with
        | 0 => let (v, s) := NetRandom.next rs; (v.toUInt32.toUInt64, s, false, false)
        | 1 => match NetRandom.nextMax rs x with
               | .ok (v, s) => (v.toUInt32.toUInt64, s, false, false) | .error _ => (0xFFFFFFFF, rs, false, false)
        | 2 => match NetRandom.nextRange rs x y with
               | .ok (v, s) => (v.toUInt32.toUInt64, s, false, false) | .error _ => (0xFFFFFFFF, rs, false, false)
        | 3 => let (v, s) := NetRandom.nextDouble rs; (v.toBits, s, true, false)
        | _ => match NetRandom.nextSingle 64 rs with
               | some (v, s) => (v.toBits.toUInt64, s, false, true) | none => (0xFFFFFFFF, rs, false, false)
      rs := rs'
      let ok := if isD then (cmp64 r g).1 else if isF then (cmp32 r.toUInt32 g.toUInt32).1 else r == g
      st ← record st 110 ok false fun _ => s!"seed {seed} call kind {kind} ({x},{y}) -> .NET {hex r.toNat 16} Lean {hex g.toNat 16}"
      j := j + 17
    return (j, st)
  else if op == 222 then
    let n := rd8 b i
    let xs := (List.range n).map fun k => Float.ofBits (rd64 b (i + 1 + 8 * k))
    let r := rd64 b (i + 1 + 8 * n)
    let g := match SysMisc.averageF64 xs with | .ok v => v.toBits | .error _ => 0
    let st ← record st 222 (cmp64 r g).1 false fun _ => s!"{xs.map (·.toBits)} -> .NET {hex r.toNat 16} Lean {hex g.toNat 16}"
    return (i + 9 + 8 * n, st)
  else match NetTestExtra.sig op with
  | some (ins, outs) =>
    let mut j := i
    let mut inW : Array UInt64 := #[]
    for t in ins do
      inW := inW.push (if t == .d then rd64 b j else (rd32 b j).toUInt64)
      j := j + NetTestExtra.wordsOf t
    let got := (NetTestExtra.eval op inW).toArray
    let mut ok := got.size == outs.length
    let mut nd := false
    let mut expW : Array UInt64 := #[]
    let mut k := 0
    for t in outs do
      let e := if t == .d then rd64 b j else (rd32 b j).toUInt64
      expW := expW.push e
      let g := got[k]!
      let (o, n2) := match t with
        | .d => cmp64 e g
        | .f => cmp32 e.toUInt32 g.toUInt32
        | .i => (e == g, false)
      ok := ok && o; nd := nd || n2
      j := j + NetTestExtra.wordsOf t
      k := k + 1
    let st ← record st op ok nd fun _ => s!"in {inW.toList.map (hex ·.toNat 8)} -> .NET {expW.toList.map (hex ·.toNat 8)} Lean {got.toList.map (hex ·.toNat 8)}"
    return (j, st)
  | none => throw (IO.userError s!"unknown op {op} at offset {i - 1}")

partial def readExact (h : IO.FS.Stream) (n : Nat) (acc : ByteArray) : IO ByteArray := do
  if acc.size ≥ n then return acc
  let chunk ← h.read (n - acc.size).toUSize
  if chunk.isEmpty then return acc
  readExact h n (acc ++ chunk)

partial def loopFrame (b : ByteArray) (i : Nat) (st : Stats) : IO Stats := do
  if i ≥ b.size then return st
  let (i', st) ← step b i st
  loopFrame b i' st

partial def loop (h : IO.FS.Stream) (st : Stats) : IO Stats := do
  let hdr ← readExact h 4 .empty
  if hdr.size < 4 then return st
  let len := (rd32 hdr 0).toNat
  let body ← readExact h len .empty
  if body.size < len then throw (IO.userError "truncated frame")
  let st ← loopFrame body 0 st
  loop h st

def main : IO UInt32 := do
  let st ← loop (← IO.getStdin) (Array.replicate 256 {})
  let mut total := 0; let mut fails := 0
  IO.println s!"{"op".pushn ' ' 40} {"pass".pushn ' ' 10} fail  nan-payload-diff  snan-input-diff"
  for k in [0:256] do
    let s := st[k]!
    if s.pass + s.fail + s.snan > 0 then
      IO.println s!"{(opName k).pushn ' ' (42 - (opName k).length)} {(toString s.pass).pushn ' ' (10 - (toString s.pass).length)} {s.fail}  {s.nanDiff}  {s.snan}"
      total := total + s.pass + s.fail; fails := fails + s.fail
  IO.println s!"TOTAL checks {total}, failures {fails}"
  return if fails == 0 then 0 else 1
