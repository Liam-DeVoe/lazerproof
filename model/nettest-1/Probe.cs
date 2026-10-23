using System;
using System.Globalization;
static class Probe {
  static string Esc(string s) { var sb = new System.Text.StringBuilder(); foreach (char c in s) { if (c < 32 || c > 126) sb.Append($"\\u{(int)c:x4}"); else sb.Append(c);} return sb.ToString(); }
  static string P<T>(Func<T> f, Func<T,string> show) { try { return show(f()); } catch (Exception e) { return e.GetType().Name; } }
  [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)] static double R(double x) => x;
  public static void Run() {
    var sb = new System.Text.StringBuilder("ignorecase-equiv:");
    foreach (char L in "INFTYAinftya-") for (int c = 0; c < 65536; c++) { if (c >= 0xD800 && c < 0xE000) continue; char ch=(char)c; if (ch != L && char.ToUpperInvariant(ch)!=char.ToUpperInvariant(L) && string.Equals(ch.ToString(), L.ToString(), StringComparison.OrdinalIgnoreCase)) sb.Append($" {L}~{c:x4}"); }
    Console.WriteLine(sb);
    var ws = new System.Text.StringBuilder("IsWhiteSpace:"); for (int c=0;c<65536;c++) if (char.IsWhiteSpace((char)c)) ws.Append($" {c:x4}"); Console.WriteLine(ws);
    foreach (var t in new[]{"\u0131nfinity","\u00a0NaN\u3000","\u0085-Infinity","N\u0041N","+\u00a0NaN","+ NaN", "- NaN", "+-NaN", "-+NaN", "--NaN", "-\u0131nfinity", "+infinity"}) { string s2 = System.Text.RegularExpressions.Regex.Unescape(t); Console.WriteLine($"sym [{t}] d={P(() => double.Parse(s2, CultureInfo.InvariantCulture), v => BitConverter.DoubleToInt64Bits(v).ToString("X16"))}"); }
    Console.WriteLine("ToUpper i-dotless " + ((int)char.ToUpperInvariant('\u0131')).ToString("x") + " cmp " + string.Equals("\u0131", "I", StringComparison.OrdinalIgnoreCase));
    string[] ss = { "", " ", "1", " 1 ", "\t1\n", "+1", "-1", "--1", "+-1", "1.", ".5", ".", "-.5", "1e5", "1E5", "1e+5", "1e-5", "1e", "1e+", "e5",
      "1,000", ",1", "1,,0", "1,0.5", "1.0,5", "1_0", "Infinity", "infinity", "INFINITY", "-Infinity", "+Infinity", "∞", "-∞", "NaN", "nan", "-NaN", "+NaN", " NaN ",
      "1\0", "1\0\0", "1\0 ", "1 \0", "\01", "0x10", "1d", "1f", "1e400", "-1e400", "1e-400", "-0", "-0.0", "0e999999999999", "1e99999999999999999999", "1e-99999999999999999999",
      "١", "1 000", "(1)", "1-", "1+", " +1", "+ 1", "- 1", "1e 5", "Infinityx", "Infinity ", " -Infinity", "- Infinity", "1.5e3.2", "00001", "1.2.3", " 1", " 1", "\u000b1\u000c", "\u00851",
      ",", ",.", "1,", "1.,", "1.e5", ".e5", "1e,5", "-,1", "+.", "-", "+", "1e05", "1e-0", "Inf", "１", "1.5,", "1,5e3", "NaNx", "-nan", "nAn", "-INFINITY", "infinity\0", "1\0x", "\0", " \0", "0.0000000000000000000000000000000000000000000000000000000000001e61", "1,2,3.4,5" };
    foreach (var s in ss) {
      Console.WriteLine($"[{Esc(s)}] d={P(() => double.Parse(s, CultureInfo.InvariantCulture), v => BitConverter.DoubleToInt64Bits(v).ToString("X16"))} f={P(() => float.Parse(s, CultureInfo.InvariantCulture), v => BitConverter.SingleToInt32Bits(v).ToString("X8"))} i={P(() => int.Parse(s, CultureInfo.InvariantCulture), v => v.ToString())}");
    }
    string[] is_ = { "2147483647", "2147483648", "-2147483648", "-2147483649", "00000000000000000000001", "-0", "99999999999999999999999", "+2147483647\0" };
    foreach (var s in is_) Console.WriteLine($"int [{Esc(s)}] {P(() => int.Parse(s, CultureInfo.InvariantCulture), v => v.ToString())}");
    double nan = double.NaN; double z = 0.0;
    Console.WriteLine($"double.NaN bits {BitConverter.DoubleToInt64Bits(nan):X16}; 0/0 {BitConverter.DoubleToInt64Bits(z/z):X16}");
    double qn = BitConverter.Int64BitsToDouble(0x7FF8000000000123);
    Console.WriteLine($"Max(1,qnan) {BitConverter.DoubleToInt64Bits(Math.Max(1.0, qn)):X16} Max(qnan,1) {BitConverter.DoubleToInt64Bits(Math.Max(qn, 1.0)):X16} Max(NaN,qnan) {BitConverter.DoubleToInt64Bits(Math.Max(nan, qn)):X16}");
    Console.WriteLine($"Max(0,-0) {BitConverter.DoubleToInt64Bits(Math.Max(0.0, -0.0)):X16} Max(-0,0) {BitConverter.DoubleToInt64Bits(Math.Max(-0.0, 0.0)):X16} Min(0,-0) {BitConverter.DoubleToInt64Bits(Math.Min(0.0, -0.0)):X16}");
    double e10=R(1e10), m10=R(-1e10), m1=R(-1.0), m5=R(-5.0), e30=R(1e30), mh=R(-0.5);
    Console.WriteLine($"(int)NaN {(int)nan} (int)e10 {(int)e10} (int)m10 {(int)m10} (uint)m1 {(uint)m1} (ulong)m5 {(ulong)m5} (long)e30 {(long)e30} (ulong)e30 {(ulong)e30} (uint)mh {(uint)mh}");
    ulong u = 0x8000008000000001UL; Console.WriteLine($"(float)ulong {BitConverter.SingleToInt32Bits((float)u):X8} expect 5F000001; (double)(float)? {BitConverter.SingleToInt32Bits((float)(double)u):X8}");
    long l = 0x0800008000000001L; Console.WriteLine($"(float)long {BitConverter.SingleToInt32Bits((float)l):X8}");
    Console.WriteLine($"Sqrt(-0) {BitConverter.DoubleToInt64Bits(Math.Sqrt(-0.0)):X16} Sqrt(-1) {BitConverter.DoubleToInt64Bits(Math.Sqrt(-1.0)):X16} Abs(NaN) {BitConverter.DoubleToInt64Bits(Math.Abs(nan)):X16}");
    Console.WriteLine($"Round(-0.5) {BitConverter.DoubleToInt64Bits(Math.Round(-0.5)):X16} RoundAway(-0.4) {BitConverter.DoubleToInt64Bits(Math.Round(-0.4, MidpointRounding.AwayFromZero)):X16} Ceil(-0.5) {BitConverter.DoubleToInt64Bits(Math.Ceiling(-0.5)):X16}");
    Console.WriteLine($"Round(2.675,2) {Math.Round(2.675, 2):R} Round(1.005,2) {Math.Round(1.005,2):R} Round(0.125,2) {Math.Round(0.125,2):R}");
    Console.WriteLine($"Clamp(NaN,0,1) {Math.Clamp(nan,0,1)} Clamp(-0.0, 0.0, 1) {BitConverter.DoubleToInt64Bits(Math.Clamp(-0.0, 0.0, 1.0)):X16} {P(() => Math.Clamp(1.0, 2.0, 1.0), v => v.ToString())} {P(() => Math.Clamp(1.0, double.NaN, 1.0), v => v.ToString())}");
    Console.WriteLine($"Sign(NaN) {P(() => Math.Sign(nan), v => v.ToString())} Sign(-0.0) {Math.Sign(-0.0)}");
    Console.WriteLine($"Runtime {System.Runtime.InteropServices.RuntimeInformation.FrameworkDescription} {System.Runtime.InteropServices.RuntimeInformation.RuntimeIdentifier}");
    Console.WriteLine($"Sse41 {System.Runtime.Intrinsics.X86.Sse41.IsSupported} Avx2 {System.Runtime.Intrinsics.X86.Avx2.IsSupported} Fma {System.Runtime.Intrinsics.X86.Fma.IsSupported} Avx512F {System.Runtime.Intrinsics.X86.Avx512F.IsSupported} Avx10v1 {System.Runtime.Intrinsics.X86.Avx10v1.IsSupported}");
    Console.WriteLine($"sin(1e22) {BitConverter.DoubleToInt64Bits(Math.Sin(1e22)):X16} pow(1.0000001,1e7) {BitConverter.DoubleToInt64Bits(Math.Pow(1.0000001,1e7)):X16}");
    // ---- library primitives (decimal, Random, osuTK, framework) ----
    static string Db(decimal d) { var b = decimal.GetBits(d); return $"{d} [{b[0]:X8} {b[1]:X8} {b[2]:X8} {b[3]:X8}]"; }
    Console.WriteLine($"(decimal)1.135 = {Db((decimal)1.135)}; (decimal)0.1f->double = {Db(decimal.CreateTruncating((double)0.1f))}; NaN -> {Db(decimal.CreateTruncating(double.NaN))}");
    decimal q = -530.3m / 146304.8m; Console.WriteLine($"-530.3m/146304.8m = {Db(q)}; Round = {Db(Math.Round(q))}; *p = {Db(Math.Round(q) * 146304.8m)}; ->double bits {BitConverter.DoubleToInt64Bits(double.CreateTruncating(Math.Round(q) * 146304.8m)):X16}");
    Console.WriteLine($"(double)-0m bits {BitConverter.DoubleToInt64Bits((double)(-0m)):X16}; (double)new decimal(0,0,0,true,1) bits {BitConverter.DoubleToInt64Bits((double)new decimal(0,0,0,true,1)):X16}");
    Console.WriteLine($"Math.Round(-0.4m) = {Db(Math.Round(-0.4m))}; -0.4m*3m = {Db(Math.Round(-0.4m) * 3m)}");
    var bw = new osu.Framework.Bindables.BindableDouble(1) { MinValue = 0.1f, MaxValue = 2f, Precision = 0.1f };
    Console.WriteLine($"Wiggle Strength default = {bw.Value:R} bits {BitConverter.DoubleToInt64Bits(bw.Value):X16}; (decimal)(double)0.1f = {Db(decimal.CreateTruncating((double)0.1f))}");
    var r = new Random(0); Console.WriteLine($"new Random(0): {r.Next()} {r.NextDouble():R} {r.Next(100)} {r.Next(-5, 5)}");
    Console.WriteLine($"playfield_diagonal = new Vector2(512,384).LengthFast = {new osuTK.Vector2(512, 384).LengthFast:R} bits {BitConverter.SingleToInt32Bits(new osuTK.Vector2(512, 384).LengthFast):X8}; Length = {new osuTK.Vector2(512, 384).Length:R}");
    const float spin_rpm = 0.05f / (2 * MathF.PI) * 60000;
    Console.WriteLine($"OsuAutoGenerator spin_rpm (Roslyn-folded) = {spin_rpm:R} bits {BitConverter.SingleToInt32Bits(spin_rpm):X8}; spin_rpm*360 bits {BitConverter.SingleToInt32Bits(spin_rpm * 360):X8}; radsPerMs = {float.DegreesToRadians(spin_rpm * 360) / 60000:R} bits {BitConverter.SingleToInt32Bits(float.DegreesToRadians(spin_rpm * 360) / 60000):X8}");
    Console.WriteLine($"-(Vector2.Zero) bits {BitConverter.SingleToInt32Bits((-osuTK.Vector2.Zero).X):X8}");
  }
}
