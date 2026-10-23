import OsuModel.Net.Random
import OsuModel.Net.Framework

/-!
# Kernel-checked facts about the library primitives

All checked with `decide +kernel` (pure kernel evaluation). The expected values are the .NET 10.0.13 /
osu-framework 2026.921.1 / osuTK 1.0.211 results printed by `nettest probe` and `nettest lazer`.
-/

namespace OsuModel.Net
open Framework OsuTK

/-! ### System.Random -/
-- new Random(0): Next() = 1559595546, then NextDouble() = 0.8173253595909687
example : (NetRandom.next (NetRandom.create 0)).1 = 1559595546 := by decide +kernel
example : (NetRandom.nextDouble (NetRandom.next (NetRandom.create 0)).2).1.toBits = 0x3FEA278783344F0F := by
  decide +kernel

/-! ### decimal -/
-- (decimal)1.135 = 1.135m (the double is 1.13499999999999979…; 15 significant digits)
example : NetDecimal.ofF64 1.135 = .ok ⟨false, 1135, 3⟩ := by decide +kernel
-- (decimal)(double)0.1f = 0.100000001490116m
example : NetDecimal.createTruncatingF64 (F32.toF64 0.1) = .ok ⟨false, 100000001490116, 15⟩ := by decide +kernel
-- (decimal)0.1f = 0.1m (7 digits)
example : NetDecimal.createTruncatingF32 0.1 = .ok ⟨false, 1, 1⟩ := by decide +kernel
-- decimal.CreateTruncating(NaN) = 0.0m (scale 1)
example : NetDecimal.createTruncatingF64 F64.nan = .ok ⟨false, 0, 1⟩ := by decide +kernel
-- 1m / 3m = 0.3333333333333333333333333333m
example : NetDecimal.div ⟨false, 1, 0⟩ ⟨false, 3, 0⟩ = .ok ⟨false, 3333333333333333333333333333, 28⟩ := by decide +kernel

/-! ### BindableNumber snapping (values confirmed through lazer's APIMod.ToMod) -/
-- DT speed_change 1.135 → 1.14, 1.125 → 1.12 (half-even on the 15-digit decimal)
example : (Bindable.setDouble 1.01 2 0.01 1.135).map (·.toBits) = .ok 0x3FF23D70A3D70A3D := by decide +kernel
example : (Bindable.setDouble 1.01 2 0.01 1.125).map (·.toBits) = .ok 0x3FF1EB851EB851EC := by decide +kernel
-- Wiggle: new BindableDouble(1) { MinValue = 0.1f, MaxValue = 2f, Precision = 0.1f }.Value = 1.00000001490116
example : (Bindable.BD.init 1 (F32.toF64 0.1) 2 (F32.toF64 0.1)).map (·.value.toBits) = .ok 0x3FF0000003FFFFFB := by
  decide +kernel
-- Bindable.Value keeps the old zero: assigning -0.0 over +0.0 is a no-op
example : ((Bindable.BD.create 0).bind (·.setValue (-0))).map (·.value.toBits) = .ok 0 := by decide +kernel

/-! ### osuTK / framework -/
-- OsuModRandom.playfield_diagonal = new Vector2(512, 384).LengthFast = 640.99506f (not 640)
example : (MathHelper.lengthFast ⟨512, 384⟩).toBits = 0x44203FAF := by decide +kernel
example : (Vector2.length ⟨512, 384⟩).toBits = 0x44200000 := by decide +kernel
-- OsuAutoGenerator: spin_rpm * 360 folds to 171887.34f (IL ldc.r4); radsPerMillisecond = 0.050000004f
example : (SysMisc.F32.degreesToRadians (Float32.ofBits 0x4827DBD6) / 60000).toBits = 0x3D4CCCCE := by decide +kernel
-- unary minus is a sign flip
example : (-(Vector2.zero)).x.toBits = 0x80000000 := by decide +kernel

end OsuModel.Net
