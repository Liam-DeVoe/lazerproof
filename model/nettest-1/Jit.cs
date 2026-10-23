using System;
using System.Runtime.CompilerServices;
// `nettest jit <x>`: tiny wrappers for DOTNET_JitDisasm="JitW:*" inspection and LD_PRELOAD libm interposition checks.
static class JitW {
  [MethodImpl(MethodImplOptions.NoInlining)] public static double Floor(double x) => Math.Floor(x);
  [MethodImpl(MethodImplOptions.NoInlining)] public static double Round(double x) => Math.Round(x);
  [MethodImpl(MethodImplOptions.NoInlining)] public static double Sqrt(double x) => Math.Sqrt(x);
  [MethodImpl(MethodImplOptions.NoInlining)] public static float SqrtF(float x) => MathF.Sqrt(x);
  [MethodImpl(MethodImplOptions.NoInlining)] public static double Max(double x, double y) => Math.Max(x, y);
  [MethodImpl(MethodImplOptions.NoInlining)] public static double Sin(double x) => Math.Sin(x);
  [MethodImpl(MethodImplOptions.NoInlining)] public static double Pow(double x, double y) => Math.Pow(x, y);
  [MethodImpl(MethodImplOptions.NoInlining)] public static float Atan2F(float y, float x) => MathF.Atan2(y, x);
  [MethodImpl(MethodImplOptions.NoInlining)] public static int ToInt(double x) => (int)x;
  public static void Run(string[] a) {
    double x = double.Parse(a[1], System.Globalization.CultureInfo.InvariantCulture);
    for (int i = 0; i < 3; i++)
      Console.WriteLine($"Floor {Floor(x)} Round {Round(x)} Sqrt {Sqrt(x)} SqrtF {SqrtF((float)x)} Max {Max(x, 1)} Sin {Sin(x)} Pow {Pow(x, 1.5)} Atan2F {Atan2F((float)x, 1f)} ToInt {ToInt(x)}");
  }
}
