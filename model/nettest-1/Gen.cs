// Differential-test vector generator: computes .NET results for each primitive on random and edge-case
// inputs and streams them (binary, framed) to stdout. Consumed by `lake exe nettest`.
// Usage: dotnet nettest.dll gen <countPerOp> <seed> [opFilter]
using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Text;

static partial class Gen
{
    static ulong s0, s1, s2, s3;
    static ulong Rotl(ulong x, int k) => (x << k) | (x >> (64 - k));
    static ulong Next()
    {
        ulong result = Rotl(s1 * 5, 7) * 9; ulong t = s1 << 17;
        s2 ^= s0; s3 ^= s1; s1 ^= s2; s0 ^= s3; s2 ^= t; s3 = Rotl(s3, 45); return result;
    }
    static int Rnd(int n) => (int)(Next() % (ulong)n);
    static bool Coin() => (Next() & 1) == 0;

    static MemoryStream frame = new MemoryStream(1 << 21);
    static BinaryWriter w = new BinaryWriter(frame);
    static Stream outp;
    static void Flush(bool force = false)
    {
        if (frame.Length < (1 << 20) && !force) return;
        var len = BitConverter.GetBytes((uint)frame.Length);
        outp.Write(len, 0, 4); outp.Write(frame.GetBuffer(), 0, (int)frame.Length);
        frame.SetLength(0);
    }

    static double D(ulong b) => BitConverter.UInt64BitsToDouble(b);
    static float F(uint b) => BitConverter.UInt32BitsToSingle(b);
    static ulong B(double d) => BitConverter.DoubleToUInt64Bits(d);
    static uint B(float f) => BitConverter.SingleToUInt32Bits(f);

    static readonly ulong[] special64 = {
        0, 0x8000000000000000, 0x7FF0000000000000, 0xFFF0000000000000, 0x7FF8000000000000, 0xFFF8000000000000,
        0x7FF0000000000001, 0x7FF4000000000000, 0x7FFFFFFFFFFFFFFF, 1, 0x8000000000000001, 0x000FFFFFFFFFFFFF, 0x0010000000000000,
        0x7FEFFFFFFFFFFFFF, 0xFFEFFFFFFFFFFFFF, 0x3FF0000000000000, 0xBFF0000000000000, 0x3FE0000000000000, 0xBFE0000000000000,
        0x3FDFFFFFFFFFFFFF, 0x3FE0000000000001, 0x4330000000000000, 0x432FFFFFFFFFFFFF, 0x4330000000000001, 0x4340000000000000,
        0x41DFFFFFFFC00000, 0x41E0000000000000, 0xC1E0000000000000, 0xC1E0000000200000, 0x43E0000000000000, 0xC3E0000000000000,
        0x43F0000000000000, 0x47EFFFFFE0000000, 0x47EFFFFFF0000000, 0x36A0000000000000, 0x3690000000000000, 0x3810000000000000,
        0x380FFFFFFFFFFFFF, 0x4024000000000000, 0x3FB999999999999A, 0x400921FB54442D18, 0x3FF0000010000000, 0x3FF0000030000000 };
    static readonly uint[] special32 = {
        0, 0x80000000, 0x7F800000, 0xFF800000, 0x7FC00000, 0xFFC00000, 0x7F800001, 0x7FFFFFFF, 1, 0x80000001, 0x007FFFFF,
        0x00800000, 0x7F7FFFFF, 0xFF7FFFFF, 0x3F800000, 0xBF800000, 0x3F000000, 0xBF000000, 0x3EFFFFFF, 0x3F000001,
        0x4B000000, 0x4AFFFFFF, 0x4B000001, 0x4B800000, 0x4EFFFFFF, 0x4F000000, 0xCF000000, 0xCF000001, 0x5F000000,
        0xDF000000, 0x5F800000, 0x40490FDB, 0x3DCCCCCD };

    // Random double with a rich distribution.
    static ulong R64()
    {
        switch (Rnd(10))
        {
            case 0: return special64[Rnd(special64.Length)];
            case 1: return Next();                                                     // uniform bits
            case 2: { ulong e = (ulong)(1023 - 64 + Rnd(128)); return (Coin() ? 0x8000000000000000UL : 0) | (e << 52) | (Next() >> 12); } // moderate
            case 3: { ulong e = (ulong)(1023 - 4 + Rnd(60)); return (Coin() ? 0x8000000000000000UL : 0) | (e << 52) | (Next() >> 12); } // ~[0.06, 2^56)
            case 4: { long n = (long)(Next() >> (Rnd(60) + 4)); double d = n + (Rnd(4) * 0.25); if (Coin()) d = -d; return B(d); } // integers/halves/quarters
            case 5: return Next() >> (12 + Rnd(40)) | (Coin() ? 0x8000000000000000UL : 0); // subnormal / tiny
            case 6: { ulong x = special64[Rnd(special64.Length)]; return x + (ulong)(Rnd(5) - 2); } // neighbours of specials
            case 7: { float f = F(R32()); return B((double)f) + (ulong)(Rnd(3) - 1) * (1UL << 28) + (ulong)Rnd(3) - 1; } // near-float values (ties for (float)x)
            case 8: { ulong e = (ulong)(1023 + 52 - Rnd(64)); return (Coin() ? 0x8000000000000000UL : 0) | (e << 52) | (Next() >> 12 & ~((1UL << Rnd(52)) - 1)); } // few low bits set: halfway cases
            default: { int k = Rnd(70); return B((Next() % 1000000) / Math.Pow(10, Rnd(8)) * (Coin() ? 1 : -1) * Math.Pow(2, k - 35)); }
        }
    }
    static uint R32()
    {
        switch (Rnd(9))
        {
            case 0: return special32[Rnd(special32.Length)];
            case 1: return (uint)Next();
            case 2: { uint e = (uint)(127 - 30 + Rnd(60)); return (Coin() ? 0x80000000u : 0) | (e << 23) | ((uint)Next() >> 9); }
            case 3: { uint e = (uint)(127 - 4 + Rnd(31)); return (Coin() ? 0x80000000u : 0) | (e << 23) | ((uint)Next() >> 9); }
            case 4: { int n = (int)((uint)Next() >> (Rnd(28) + 4)); float d = n + (Rnd(4) * 0.25f); if (Coin()) d = -d; return B(d); }
            case 5: return ((uint)Next() >> (9 + Rnd(20))) | (Coin() ? 0x80000000u : 0);
            case 6: return special32[Rnd(special32.Length)] + (uint)(Rnd(5) - 2);
            case 7: { uint e = (uint)(127 + 23 - Rnd(30)); return (Coin() ? 0x80000000u : 0) | (e << 23) | (((uint)Next() >> 9) & ~((1u << Rnd(23)) - 1)); }
            default: return B((float)((Next() % 100000) / Math.Pow(10, Rnd(6)) * (Coin() ? 1 : -1)));
        }
    }
    static ulong Near64(ulong a) { switch (Rnd(4)) { case 0: return a + (ulong)(Rnd(9) - 4); case 1: return a ^ 0x8000000000000000; case 2: return (a ^ 0x8000000000000000) + (ulong)(Rnd(5) - 2); default: return R64(); } }
    static uint Near32(uint a) { switch (Rnd(4)) { case 0: return a + (uint)(Rnd(9) - 4); case 1: return a ^ 0x80000000; case 2: return (a ^ 0x80000000) + (uint)(Rnd(5) - 2); default: return R32(); } }
    static ulong RInt64()
    {
        switch (Rnd(6))
        {
            case 0: return Next();
            case 1: return Next() >> Rnd(64);
            case 2: return (ulong)-(long)(Next() >> Rnd(64));
            case 3: return (1UL << Rnd(64)) + (ulong)(Rnd(5) - 2);
            case 4: return (ulong)(long)(int)Next();
            default: return (Next() >> Rnd(64)) & ~((1UL << Rnd(40)) - 1) | (Coin() ? (1UL << Rnd(40)) : 0);
        }
    }

    static byte Status(Exception e) => e switch
    {
        FormatException => 1, OverflowException => 2, ArgumentOutOfRangeException => 4, ArgumentException => 3, ArithmeticException => 5, _ => 6
    };

    static void Op(byte op) => w.Write(op);

    static int Main0(int count, ulong seed, HashSet<int> filter)
    {
        s0 = seed ^ 0x9E3779B97F4A7C15; s1 = seed * 0xBF58476D1CE4E5B9 + 1; s2 = 0x94D049BB133111EB; s3 = seed + 12345;
        for (int i = 0; i < 16; i++) Next();
        outp = new BufferedStream(Console.OpenStandardOutput(), 1 << 20);

        bool On(int op) => filter == null || filter.Contains(op);
        // binary f64
        foreach (int op in new[] { 1, 2, 3, 4, 5, 50, 51, 66, 70, 73 })
        {
            if (!On(op)) continue;
            int n = op >= 60 ? count / 2 : count;
            for (int i = 0; i < n; i++)
            {
                ulong a = R64(), b = Coin() ? Near64(a) : R64();
                if (op == 70 && Rnd(3) == 0) b = B((double)(Rnd(21) - 10) * (Coin() ? 1 : 0.5));
                double x = D(a), y = D(b);
                Op((byte)op); w.Write(a); w.Write(b);
                switch (op)
                {
                    case 1: w.Write(B(x + y)); break;
                    case 2: w.Write(B(x - y)); break;
                    case 3: w.Write(B(x * y)); break;
                    case 4: w.Write(B(x / y)); break;
                    case 5: w.Write((byte)((x < y ? 1 : 0) | (x <= y ? 2 : 0) | (x == y ? 4 : 0) | (x > y ? 8 : 0) | (x >= y ? 16 : 0) | (x != y ? 32 : 0))); break;
                    case 50: w.Write(B(Math.Max(x, y))); break;
                    case 51: w.Write(B(Math.Min(x, y))); break;
                    case 66: w.Write(B(Math.Atan2(x, y))); break;
                    case 70: w.Write(B(Math.Pow(x, y))); break;
                    case 73: w.Write(B(Math.Log(x, y))); break;
                }
                Flush();
            }
        }
        // binary f32
        foreach (int op in new[] { 6, 7, 8, 9, 10, 52, 53, 86, 90 })
        {
            if (!On(op)) continue;
            int n = op >= 60 ? count / 2 : count;
            for (int i = 0; i < n; i++)
            {
                uint a = R32(), b = Coin() ? Near32(a) : R32();
                if (op == 90 && Rnd(3) == 0) b = B((float)(Rnd(21) - 10) * (Coin() ? 1f : 0.5f));
                float x = F(a), y = F(b);
                Op((byte)op); w.Write(a); w.Write(b);
                switch (op)
                {
                    case 6: w.Write(B(x + y)); break;
                    case 7: w.Write(B(x - y)); break;
                    case 8: w.Write(B(x * y)); break;
                    case 9: w.Write(B(x / y)); break;
                    case 10: w.Write((byte)((x < y ? 1 : 0) | (x <= y ? 2 : 0) | (x == y ? 4 : 0) | (x > y ? 8 : 0) | (x >= y ? 16 : 0) | (x != y ? 32 : 0))); break;
                    case 52: w.Write(B(MathF.Max(x, y))); break;
                    case 53: w.Write(B(MathF.Min(x, y))); break;
                    case 86: w.Write(B(MathF.Atan2(x, y))); break;
                    case 90: w.Write(B(MathF.Pow(x, y))); break;
                }
                Flush();
            }
        }
        // unary f64 -> f64
        foreach (int op in new[] { 30, 31, 32, 33, 34, 35, 36, 37, 60, 61, 62, 63, 64, 65, 67, 68, 69, 71 })
        {
            if (!On(op)) continue;
            int n = op >= 60 ? count / 2 : count;
            for (int i = 0; i < n; i++)
            {
                ulong a = R64(); double x = D(a);
                if (op >= 60 && Rnd(4) == 0) { x = (Next() % 2000000 - 1000000) / 1000.0 * (Coin() ? 1 : 0.001); a = B(x); }
                double r = op switch
                {
                    30 => Math.Round(x), 31 => Math.Round(x, MidpointRounding.AwayFromZero), 32 => Math.Floor(x), 33 => Math.Ceiling(x),
                    34 => Math.Truncate(x), 35 => Math.Abs(x), 36 => Math.Sqrt(x), 37 => -x, 60 => Math.Sin(x), 61 => Math.Cos(x),
                    62 => Math.Tan(x), 63 => Math.Asin(x), 64 => Math.Acos(x), 65 => Math.Atan(x), 67 => Math.Exp(x), 68 => Math.Log(x),
                    69 => Math.Log10(x), _ => Math.Cbrt(x)
                };
                Op((byte)op); w.Write(a); w.Write(B(r)); Flush();
            }
        }
        // unary f32 -> f32
        foreach (int op in new[] { 40, 41, 42, 43, 44, 45, 46, 47, 80, 81, 82, 83, 84, 85, 87, 88 })
        {
            if (!On(op)) continue;
            int n = op >= 60 ? count / 2 : count;
            for (int i = 0; i < n; i++)
            {
                uint a = R32(); float x = F(a);
                if (op >= 60 && Rnd(4) == 0) { x = (Next() % 2000000 - 1000000f) / 1000f * (Coin() ? 1 : 0.001f); a = B(x); }
                float r = op switch
                {
                    40 => MathF.Round(x), 41 => MathF.Round(x, MidpointRounding.AwayFromZero), 42 => MathF.Floor(x), 43 => MathF.Ceiling(x),
                    44 => MathF.Truncate(x), 45 => MathF.Abs(x), 46 => MathF.Sqrt(x), 47 => -x, 80 => MathF.Sin(x), 81 => MathF.Cos(x),
                    82 => MathF.Tan(x), 83 => MathF.Asin(x), 84 => MathF.Acos(x), 85 => MathF.Atan(x), 87 => MathF.Exp(x), _ => MathF.Log(x)
                };
                Op((byte)op); w.Write(a); w.Write(B(r)); Flush();
            }
        }
        // conversions and casts
        for (int op = 11; op <= 28; op++)
        {
            if (!On(op)) continue;
            for (int i = 0; i < count; i++)
            {
                Op((byte)op);
                switch (op)
                {
                    case 11: { ulong a = R64(); w.Write(a); w.Write(B((float)D(a))); break; }
                    case 12: { uint a = R32(); w.Write(a); w.Write(B((double)F(a))); break; }
                    case 13: { uint a = (uint)RInt64(); w.Write(a); w.Write(B((double)(int)a)); break; }
                    case 14: { ulong a = RInt64(); w.Write(a); w.Write(B((double)(long)a)); break; }
                    case 15: { ulong a = RInt64(); w.Write(a); w.Write(B((double)a)); break; }
                    case 16: { uint a = (uint)RInt64(); w.Write(a); w.Write(B((float)(int)a)); break; }
                    case 17: { ulong a = RInt64(); w.Write(a); w.Write(B((float)(long)a)); break; }
                    case 18: { ulong a = RInt64(); w.Write(a); w.Write(B((float)a)); break; }
                    case 19: { uint a = (uint)RInt64(); w.Write(a); w.Write(B((double)a)); break; }
                    case 20: { uint a = (uint)RInt64(); w.Write(a); w.Write(B((float)a)); break; }
                    case 21: { ulong a = R64(); w.Write(a); w.Write((ulong)(uint)(int)D(a)); break; }
                    case 22: { ulong a = R64(); w.Write(a); w.Write((ulong)(long)D(a)); break; }
                    case 23: { ulong a = R64(); w.Write(a); w.Write((ulong)(uint)D(a)); break; }
                    case 24: { ulong a = R64(); w.Write(a); w.Write((ulong)D(a)); break; }
                    case 25: { uint a = R32(); w.Write(a); w.Write((ulong)(uint)(int)F(a)); break; }
                    case 26: { uint a = R32(); w.Write(a); w.Write((ulong)(long)F(a)); break; }
                    case 27: { uint a = R32(); w.Write(a); w.Write((ulong)(uint)F(a)); break; }
                    case 28: { uint a = R32(); w.Write(a); w.Write((ulong)F(a)); break; }
                }
                Flush();
            }
        }
        // clamp, sign, round digits
        if (On(54)) for (int i = 0; i < count; i++)
        {
            ulong v = R64(), lo = Coin() ? R64() : Near64(v), hi = Coin() ? R64() : Near64(v);
            if (Rnd(4) != 0 && D(lo) > D(hi)) (lo, hi) = (hi, lo);
            Op(54); w.Write(v); w.Write(lo); w.Write(hi);
            try { double r = Math.Clamp(D(v), D(lo), D(hi)); w.Write((byte)0); w.Write(B(r)); } catch (Exception e) { w.Write(Status(e)); w.Write(0UL); }
            Flush();
        }
        if (On(55)) for (int i = 0; i < count; i++)
        {
            uint v = R32(), lo = Coin() ? R32() : Near32(v), hi = Coin() ? R32() : Near32(v);
            if (Rnd(4) != 0 && F(lo) > F(hi)) (lo, hi) = (hi, lo);
            Op(55); w.Write(v); w.Write(lo); w.Write(hi);
            try { float r = Math.Clamp(F(v), F(lo), F(hi)); w.Write((byte)0); w.Write(B(r)); } catch (Exception e) { w.Write(Status(e)); w.Write(0u); }
            Flush();
        }
        if (On(56)) for (int i = 0; i < count; i++)
        {
            ulong v = R64(); Op(56); w.Write(v);
            try { int r = Math.Sign(D(v)); w.Write((byte)0); w.Write(r); } catch (Exception e) { w.Write(Status(e)); w.Write(0); }
            Flush();
        }
        if (On(57)) for (int i = 0; i < count; i++)
        {
            uint v = R32(); Op(57); w.Write(v);
            try { int r = Math.Sign(F(v)); w.Write((byte)0); w.Write(r); } catch (Exception e) { w.Write(Status(e)); w.Write(0); }
            Flush();
        }
        if (On(58)) for (int i = 0; i < count; i++)
        {
            ulong v = R64(); byte dg = (byte)(Rnd(20) == 0 ? 16 + Rnd(3) : Rnd(16));
            if (Coin()) { v = B((Next() % 100000000) / Math.Pow(10, Rnd(9)) * (Coin() ? 1 : -1)); }
            Op(58); w.Write(v); w.Write(dg);
            try { double r = Math.Round(D(v), dg); w.Write((byte)0); w.Write(B(r)); } catch (Exception e) { w.Write(Status(e)); w.Write(0UL); }
            Flush();
        }
        if (On(59)) for (int i = 0; i < count; i++)
        {
            uint v = R32(); byte dg = (byte)(Rnd(20) == 0 ? 7 + Rnd(3) : Rnd(7));
            if (Coin()) { v = B((float)((Next() % 1000000) / Math.Pow(10, Rnd(7)) * (Coin() ? 1 : -1))); }
            Op(59); w.Write(v); w.Write(dg);
            try { float r = MathF.Round(F(v), dg); w.Write((byte)0); w.Write(B(r)); } catch (Exception e) { w.Write(Status(e)); w.Write(0u); }
            Flush();
        }
        // parsing
        for (int op = 100; op <= 105; op++)
        {
            if (!On(op)) continue;
            int n = count / 2;
            for (int i = 0; i < n; i++)
            {
                string s = (op == 102 || op == 105) ? RandIntString() : RandFloatString(op == 101 || op == 104);
                byte[] bytes = Encoding.UTF8.GetBytes(s);
                Op((byte)op); w.Write((ushort)bytes.Length); w.Write(bytes);
                try
                {
                    switch (op)
                    {
                        case 100: { double r = double.Parse(s, CultureInfo.InvariantCulture); w.Write((byte)0); w.Write(B(r)); break; }
                        case 101: { float r = float.Parse(s, CultureInfo.InvariantCulture); w.Write((byte)0); w.Write((ulong)B(r)); break; }
                        case 102: { int r = int.Parse(s, CultureInfo.InvariantCulture); w.Write((byte)0); w.Write((ulong)(uint)r); break; }
                        case 103: { double r = osu.Game.Beatmaps.Formats.Parsing.ParseDouble(s); w.Write((byte)0); w.Write(B(r)); break; }
                        case 104: { float r = osu.Game.Beatmaps.Formats.Parsing.ParseFloat(s); w.Write((byte)0); w.Write((ulong)B(r)); break; }
                        case 105: { int r = osu.Game.Beatmaps.Formats.Parsing.ParseInt(s); w.Write((byte)0); w.Write((ulong)(uint)r); break; }
                    }
                }
                catch (Exception e) { w.Write(Status(e)); w.Write(0UL); }
                Flush();
            }
        }
        Main2(count, On);
        Flush(true);
        outp.Flush();
        return 0;
    }

    // ---------- string generators ----------
    static readonly string[] fixedStrings = {
        "", " ", "1", " 1 ", "\t1\n", "+1", "-1", "--1", "+-1", "1.", ".5", ".", "-.5", "1e5", "1E5", "1e+5", "1e-5", "1e", "1e+", "e5",
        "1,000", ",1", "1,,0", "1,0.5", "1.0,5", "Infinity", "infinity", "INFINITY", "-Infinity", "+Infinity", "∞", "NaN", "nan",
        "-NaN", "+NaN", " NaN ", "1\0", "1\0\0", "1\0 ", "1 \0", "\01", "0x10", "1e400", "-1e400", "1e-400", "-0", "-0.0",
        "0e999999999999", "1e99999999999999999999", "1e-99999999999999999999", "1e100000000", "1e99999999", "1e-100000000", "0.0001e100000000",
        " NaN　", "\u0085-Infinity", "+ NaN", "- NaN", "infinity\0", "2147483647", "2147483648", "-2147483648", "-2147483649",
        "2147483520", "2147483583.9999", "2147483584", "2147483647.5", "2147483904", "-2147483904", "1.7976931348623157e308",
        "1.7976931348623158e308", "1.797693134862315807937289714053e308", "4.9406564584124654e-324", "2.4703282292062327e-324",
        "2.4703282292062328e-324", "3.4028235e38", "3.40282357e38", "3.4028236e38", "1.4e-45", "7e-46", "7.1e-46", "0.1", "0.2", "0.3",
        "9007199254740993", "9007199254740993.0000000000000000000000000000001", "1.00000005960464477539062500001", "1.000000059604644775390625",
        "123,456,789.125", "1e0", "1e-0", "1e+0", "000000000000000000000000000000000000001", "0.000000000000000000000000000000000000001e39" };
    const string alphabet = "0123456789012345678901234567890123456789.,eE+-  \t\0nNaAiIfFtTyY∞ \u0085x";

    static string Digits(int n) { var sb = new StringBuilder(n); for (int i = 0; i < n; i++) sb.Append((char)('0' + Rnd(10))); return sb.ToString(); }

    static string ExactDecimal(BigInteger m, int e2) // m * 2^e2 exactly
    {
        if (e2 >= 0) return (m << e2).ToString();
        BigInteger num = m * BigInteger.Pow(5, -e2); string s = num.ToString(); int k = -e2;
        if (s.Length <= k) s = new string('0', k - s.Length + 1) + s;
        return s.Substring(0, s.Length - k) + "." + s.Substring(s.Length - k);
    }
    static string Midpoint(bool single)
    {
        // exact midpoint between two adjacent floats, optionally perturbed in the last digit
        string s;
        if (single) { uint b = R32() & 0x7F7FFFFF; if ((b >> 23) == 0xFF) b = 0x3F800000; int be = (int)(b >> 23); long m = (b & 0x7FFFFF) | (be > 0 ? 0x800000 : 0); int e = (be > 0 ? be : 1) - 150; s = ExactDecimal(2 * m + 1, e - 1); }
        else { ulong b = R64() & 0x7FEFFFFFFFFFFFFF; int be = (int)(b >> 52); long m = (long)(b & 0xFFFFFFFFFFFFF) | (be > 0 ? 1L << 52 : 0); int e = (be > 0 ? be : 1) - 1075; if (e < -1074 + 200 && Rnd(3) != 0) e = Math.Max(e, -1074 + Rnd(400)); if (e > 900) e = 900; s = ExactDecimal(2 * (BigInteger)m + 1, e - 1); }
        switch (Rnd(4))
        {
            case 0: return s;
            case 1: return s + "0000001";
            case 2: { // decrement last nonzero digit if possible
                    char[] c = s.ToCharArray(); for (int i = c.Length - 1; i >= 0; i--) if (c[i] >= '1' && c[i] <= '9') { c[i]--; break; }
                    return new string(c); }
            default: return s.Length > 30 ? s.Substring(0, 10 + Rnd(s.Length - 10)) : s;
        }
    }
    static string RandFloatString(bool single)
    {
        switch (Rnd(12))
        {
            case 0: return fixedStrings[Rnd(fixedStrings.Length)];
            case 1: { double d = D(R64()); return d.ToString(Rnd(2) == 0 ? "R" : (Rnd(2) == 0 ? "E16" : "G17"), CultureInfo.InvariantCulture); }
            case 2: { float f = F(R32()); return f.ToString(Rnd(2) == 0 ? "R" : "G9", CultureInfo.InvariantCulture); }
            case 3: case 4: return Midpoint(single);
            case 5: { var sb = new StringBuilder(); int n = 1 + Rnd(25); for (int i = 0; i < n; i++) sb.Append(alphabet[Rnd(alphabet.Length)]); return sb.ToString(); }
            case 6: { string s = Digits(1 + Rnd(30)); int p = Rnd(s.Length + 1); s = s.Substring(0, p) + "." + s.Substring(p); if (Coin()) s += "e" + (Coin() ? "-" : "") + Rnd(400); return (Coin() ? "-" : "") + s; }
            case 7: { string s = Digits(1 + Rnd(900)); int p = Rnd(s.Length + 1); s = s.Substring(0, p) + "." + s.Substring(p); if (Coin()) s += "e" + (Coin() ? "-" : "+") + Rnd(1200); return s; }
            case 8: { // lazer-like: small decimals, whitespace, commas
                    string s = ((Next() % 2000000) / Math.Pow(10, Rnd(6)) - (Coin() ? 0 : 500000)).ToString(CultureInfo.InvariantCulture);
                    if (Rnd(5) == 0) s = " " + s; if (Rnd(5) == 0) s += "\t"; if (Rnd(10) == 0) s += "\0"; return s; }
            case 9: { // mutate a valid number
                    char[] c = (D(R64()).ToString("R", CultureInfo.InvariantCulture)).ToCharArray(); int k = Rnd(c.Length); c[k] = alphabet[Rnd(alphabet.Length)]; return new string(c); }
            case 10: { string s = Digits(1 + Rnd(12)); for (int i = 0; i < 2; i++) { int p = 1 + Rnd(s.Length); s = s.Insert(Math.Min(p, s.Length), ","); } return s + (Coin() ? "." + Digits(Rnd(5)) : ""); }
            default: { string sym = new[] { "Infinity", "NaN", "-Infinity", "+Infinity", "-NaN", "+NaN" }[Rnd(6)]; var sb = new StringBuilder();
                    foreach (char ch in sym) sb.Append(Coin() ? char.ToUpperInvariant(ch) : char.ToLowerInvariant(ch));
                    string ws = " \t 　 \0\u0085"; string r = sb.ToString(); if (Coin()) r = ws[Rnd(ws.Length)] + r; if (Coin()) r += ws[Rnd(ws.Length)]; return r; }
        }
    }
    static string RandIntString()
    {
        switch (Rnd(6))
        {
            case 0: return fixedStrings[Rnd(fixedStrings.Length)];
            case 1: return ((long)(int)Next() + Rnd(5) - 2).ToString(CultureInfo.InvariantCulture);
            case 2: return new[] { "2147483647", "2147483648", "-2147483648", "-2147483649", "4294967296", "99999999999", "-0", "+0", "0000000000002147483647", "-00002147483649" }[Rnd(10)];
            case 3: { var sb = new StringBuilder(); int n = 1 + Rnd(14); for (int i = 0; i < n; i++) sb.Append(alphabet[Rnd(alphabet.Length)]); return sb.ToString(); }
            case 4: { string s = (Coin() ? "-" : "") + Digits(1 + Rnd(12)); if (Coin()) s = " " + s; if (Coin()) s += " "; if (Rnd(5) == 0) s += "\0"; return s; }
            default: return ((long)(Next() >> Rnd(64)) * (Coin() ? 1 : -1)).ToString(CultureInfo.InvariantCulture);
        }
    }

    public static int Run(string[] args)
    {
        if (args.Length < 3 || args[0] != "gen") { Console.Error.WriteLine("usage: nettest gen <countPerOp> <seed> [op,op,...]"); return 2; }
        int count = int.Parse(args[1]); ulong seed = ulong.Parse(args[2]);
        HashSet<int> filter = args.Length > 3 ? new HashSet<int>(Array.ConvertAll(args[3].Split(','), int.Parse)) : null;
        return Main0(count, seed, filter);
    }
}
