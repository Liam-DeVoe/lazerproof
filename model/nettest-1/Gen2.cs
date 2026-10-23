// Generators for the library primitives: System.Random, System.Decimal, osuTK, osu-framework,
// Enumerable.Average, float/double.DegreesToRadians. Each op calls the real implementation
// (osuTK.dll / osu.Framework.dll are the exact nupkg binaries lazer references).
// Record formats: see `sig` in NetTest/Main.lean.
using System;
using System.Collections.Generic;
using System.Linq;
using osu.Framework.Bindables;
using osu.Framework.Extensions.MatrixExtensions;
using osu.Framework.Graphics;
using osu.Framework.Graphics.Transforms;
using osu.Framework.Utils;
using osuTK;
using FwV2Ext = osu.Framework.Graphics.Vector2Extensions;

static partial class Gen
{
    static void WF(float f) => w.Write(B(f));
    static void WD(double d) => w.Write(B(d));
    static void WI(int i) => w.Write(i);
    static void WV(Vector2 v) { WF(v.X); WF(v.Y); }
    static void WM(Matrix3 m) { WF(m.M11); WF(m.M12); WF(m.M13); WF(m.M21); WF(m.M22); WF(m.M23); WF(m.M31); WF(m.M32); WF(m.M33); }
    static void WDec(decimal d) { foreach (int x in decimal.GetBits(d)) w.Write(x); }

    // "human" floats: game-scale numbers, small integers, halves; plus R32 bit soup
    static float HF()
    {
        switch (Rnd(8))
        {
            case 0: return F(R32());
            case 1: return (float)((Next() % 2000001) / 1000.0 - 1000.0);
            case 2: return (float)(Rnd(2049) - 1024) * 0.5f;
            case 3: return Rnd(1025) / 2.0f;
            case 4: return (float)((Next() % 1000001) / 1000000.0);
            case 5: return (float)((Next() % 20001) / 100.0 - 100.0);
            case 6: return new[] { 0f, -0f, 1f, -1f, 512f, 384f, 256f, 192f, 0.001f, -0.001f, 1e-4f, float.NaN, float.PositiveInfinity, float.NegativeInfinity, float.Epsilon, float.MaxValue }[Rnd(16)];
            default: return (float)((Next() % 2000001) / 100.0 - 10000.0) * (float)Math.Pow(10, Rnd(7) - 3);
        }
    }
    static double HD()
    {
        switch (Rnd(7))
        {
            case 0: return D(R64());
            case 1: return (Next() % 2000001) / 1000.0 - 1000.0;
            case 2: return (Next() % 4000001) / 10.0 - 200000.0;
            case 3: return (Next() % 1000001) / 1000000.0;
            case 4: return Rnd(2001) / 1000.0;
            case 5: return new[] { 0.0, -0.0, 1, -1, 0.5, double.NaN, double.PositiveInfinity, double.NegativeInfinity, double.Epsilon, 1e-7, -1e-7, 2, 3000, 40 }[Rnd(14)];
            default: return (Next() % 2000001) / 100.0 * Math.Pow(10, Rnd(9) - 4) * (Coin() ? 1 : -1);
        }
    }

    // ---------- decimal inputs ----------
    static readonly decimal[] decSpecial = { 0m, -0m, 1m, -1m, 0.1m, 0.01m, 0.001m, 0.05m, 0.5m, 1.135m, 10m, decimal.MaxValue, decimal.MinValue,
        0.0000000000000000000000000001m, 7.9228162514264337593543950335m, 0.100000001490116m, 0.3333333333333333333333333333m, 1.00m, 100m, 3m, 7m };
    static decimal RDec()
    {
        switch (Rnd(8))
        {
            case 0: return decSpecial[Rnd(decSpecial.Length)];
            case 1: { // arbitrary 96-bit mantissa of random bit length, random scale
                int bits = 1 + Rnd(96); ulong lo = Next(), hi = Next();
                System.Numerics.BigInteger m = ((System.Numerics.BigInteger)hi << 64 | lo) & ((System.Numerics.BigInteger.One << bits) - 1);
                byte[] b = m.ToByteArray(); int[] i3 = new int[3];
                for (int k = 0; k < 12 && k < b.Length; k++) i3[k / 4] |= b[k] << (8 * (k % 4));
                return new decimal(i3[0], i3[1], i3[2], Coin(), (byte)Rnd(29)); }
            case 2: return new decimal((int)Next(), 0, 0, Coin(), (byte)Rnd(29));
            case 3: return new decimal((int)Next(), (int)Next(), 0, Coin(), (byte)Rnd(29));
            case 4: return (decimal)((Next() % 1000000) / Math.Pow(10, Rnd(7))) * (Coin() ? 1 : -1);
            case 5: { // near PowerOvfl boundaries: floor((2^96-1)/10^k) +- small, or trailing zeros
                System.Numerics.BigInteger m = ((System.Numerics.BigInteger.One << 96) - 1) / System.Numerics.BigInteger.Pow(10, Rnd(10)) + (Rnd(7) - 3);
                if (m < 0) m = 0; if (m >= (System.Numerics.BigInteger.One << 96)) m = (System.Numerics.BigInteger.One << 96) - 1;
                byte[] b = m.ToByteArray(); int[] i3 = new int[3];
                for (int k = 0; k < 12 && k < b.Length; k++) i3[k / 4] |= b[k] << (8 * (k % 4));
                return new decimal(i3[0], i3[1], i3[2], Coin(), (byte)Rnd(29)); }
            case 6: { decimal d = (decimal)Rnd(100000) * (decimal)Math.Pow(10, Rnd(10)); return new decimal(decimal.GetBits(d)[0], decimal.GetBits(d)[1], decimal.GetBits(d)[2], Coin(), (byte)Rnd(29)); }
            default: try { return (decimal)HD(); } catch { return 1m; }
        }
    }
    static double RDouble4Dec()
    {
        switch (Rnd(6))
        {
            case 0: return D(R64());
            case 1: { ulong e = (ulong)(1023 - 100 + Rnd(200)); return D((Coin() ? 0x8000000000000000UL : 0) | (e << 52) | (Next() >> 12)); }
            case 2: return Rnd(100001) / Math.Pow(10, Rnd(6)) * (Coin() ? 1 : -1);
            case 3: return BitConverter.Int64BitsToDouble(BitConverter.DoubleToInt64Bits(Rnd(100001) / Math.Pow(10, Rnd(6))) + Rnd(5) - 2);
            case 4: return D(B(Math.Pow(2, 96)) + (ulong)(Rnd(5) - 2)) * (Coin() ? 1 : -1);
            default: return HD();
        }
    }
    static float RFloat4Dec()
    {
        switch (Rnd(5))
        {
            case 0: return F(R32());
            case 1: { uint e = (uint)(127 - 100 + Rnd(200)); if (e > 254) e = 254; return F((Coin() ? 0x80000000u : 0) | (e << 23) | ((uint)Next() >> 9)); }
            case 2: return (float)(Rnd(100001) / Math.Pow(10, Rnd(6)));
            case 3: return F(B((float)(Rnd(100001) / Math.Pow(10, Rnd(6)))) + (uint)(Rnd(5) - 2));
            default: return HF();
        }
    }

    static Matrix3 RMat()
    {
        if (Rnd(5) == 0) return Matrix3.Identity;
        return new Matrix3(HF(), HF(), HF(), HF(), HF(), HF(), HF(), HF(), Rnd(3) == 0 ? 1f : HF());
    }

    static void Main2(int count, Func<int, bool> On)
    {
        // 110: System.Random sequences
        if (On(110)) for (int i = 0; i < count / 20 + 1; i++)
        {
            int seed = Rnd(6) switch { 0 => new[] { 0, 1, -1, int.MinValue, int.MaxValue, 161803398, -161803398, 42 }[Rnd(8)], 1 => Rnd(100000), 2 => (int)(Next() % 3000000), _ => (int)Next() };
            var rng = new Random(seed);
            int n = 1 + Rnd(Rnd(4) == 0 ? 400 : 60);
            Op(110); WI(seed); w.Write((ushort)n);
            for (int k = 0; k < n; k++)
            {
                int kind = Rnd(10) < 5 ? 3 : Rnd(5);
                int a = 0, b = 0; ulong r = 0;
                switch (kind)
                {
                    case 0: r = (uint)rng.Next(); break;
                    case 1: a = Rnd(4) switch { 0 => Rnd(10), 1 => int.MaxValue - Rnd(3), 2 => (int)(Next() >> 33), _ => Rnd(1000) }; r = (uint)rng.Next(a); break;
                    case 2:
                        a = Rnd(3) switch { 0 => int.MinValue + Rnd(3), 1 => -Rnd(1000), _ => (int)Next() };
                        b = Rnd(3) switch { 0 => int.MaxValue - Rnd(3), 1 => Rnd(1000), _ => (int)Next() };
                        if (a > b) (a, b) = (b, a);
                        r = (uint)rng.Next(a, b); break;
                    case 3: r = B(rng.NextDouble()); break;
                    default: r = B(rng.NextSingle()); break;
                }
                w.Write((byte)kind); WI(a); WI(b); w.Write(r);
            }
            Flush();
        }
        // 111-114: double/float -> decimal
        foreach (int op in new[] { 111, 112, 113, 114 })
        {
            if (!On(op)) continue;
            for (int i = 0; i < count; i++)
            {
                Op((byte)op);
                decimal res = 0m; int st = 0;
                if (op <= 112)
                {
                    double x = RDouble4Dec(); WD(x);
                    try { res = op == 111 ? decimal.CreateTruncating(x) : (decimal)x; } catch (Exception e) { st = Status(e); }
                }
                else
                {
                    float x = RFloat4Dec(); WF(x);
                    try { res = op == 113 ? decimal.CreateTruncating(x) : (decimal)x; } catch (Exception e) { st = Status(e); }
                }
                WI(st); if (st == 0) WDec(res); else { WI(0); WI(0); WI(0); WI(0); }
                Flush();
            }
        }
        // 115-116: decimal -> double/float (CreateTruncating, as BindableNumber does)
        foreach (int op in new[] { 115, 116 })
        {
            if (!On(op)) continue;
            for (int i = 0; i < count; i++)
            {
                decimal d = RDec(); Op((byte)op); WDec(d);
                if (op == 115) WD(double.CreateTruncating(d)); else WF(float.CreateTruncating(d));
                Flush();
            }
        }
        // 117-118: decimal / and *
        foreach (int op in new[] { 117, 118 })
        {
            if (!On(op)) continue;
            for (int i = 0; i < count; i++)
            {
                decimal a = RDec(), b = RDec();
                if (op == 117 && Rnd(4) == 0) b = new[] { 0.1m, 0.01m, 0.05m, 0.001m, 0.100000001490116m, 10m, 0.02m, 1m, 3m, 7m, 0m }[Rnd(11)];
                if (op == 117 && Rnd(4) == 0) { try { a = (decimal)Math.Round(HD() % 1e6, Rnd(15)); } catch { } }
                Op((byte)op); WDec(a); WDec(b);
                decimal res = 0m; int st = 0;
                try { res = op == 117 ? a / b : a * b; } catch (Exception e) { st = Status(e); }
                WI(st); if (st == 0) WDec(res); else { WI(0); WI(0); WI(0); WI(0); }
                Flush();
            }
        }
        // 119: Math.Round(decimal)
        if (On(119)) for (int i = 0; i < count; i++)
        {
            decimal a = RDec(); if (Rnd(3) == 0) a = (Rnd(2001) - 1000) / 2m + (Rnd(3) - 1) * 0.0000000000000000000001m;
            Op(119); WDec(a); WDec(Math.Round(a)); Flush();
        }
        // 120-135: osuTK Vector2 / Matrix3 / MathHelper
        for (int op = 120; op <= 136; op++)
        {
            if (!On(op) || op == 137) continue;
            for (int i = 0; i < count; i++)
            {
                Vector2 a = new Vector2(HF(), HF()), b = Coin() ? new Vector2(HF(), HF()) : new Vector2(a.X + HF() * 1e-3f, a.Y - HF() * 1e-3f), c = new Vector2(HF(), HF());
                float s = HF();
                Op((byte)op);
                switch (op)
                {
                    case 120: WV(a); WF(a.Length); break;
                    case 121: WV(a); WF(a.LengthSquared); break;
                    case 122: WV(a); WF(a.LengthFast); break;
                    case 123: WV(a); WV(b); WF(Vector2.Distance(a, b)); break;
                    case 124: WV(a); WV(b); WF(Vector2.DistanceSquared(a, b)); break;
                    case 125: WV(a); WV(a.Normalized()); break;
                    case 126: WV(a); WV(b); WF(Vector2.Dot(a, b)); break;
                    case 127: WV(a); WV(b); WF(s); WV(Vector2.Lerp(a, b, s)); break;
                    case 128: WV(a); WV(b); WV(c); WV(Vector2.Clamp(a, b, c)); break;
                    case 129: WV(a); WV(-a); WV(a.PerpendicularRight); WV(a.PerpendicularLeft); break;
                    case 130: WV(a); WV(b); WF(s); WV(a + b); WV(a - b); WV(a * s); WV(s * a); WV(a * b); WV(a / s); WV(Vector2.Divide(a, b)); break;
                    case 131: { float x = Rnd(3) == 0 ? F(R32()) : Math.Abs(HF()) * (float)Math.Pow(10, Rnd(9) - 3); if (Rnd(20) == 0) x = 409600f; WF(x); WF(MathHelper.InverseSqrtFast(x)); break; }
                    case 132: WV(a); WV(Vector2.NormalizeFast(a)); break;
                    case 133: WV(a); WV(b); WF(Vector2.PerpDot(a, b)); break;
                    case 134: WV(a); WV(b); WV(Vector2.ComponentMin(a, b)); WV(Vector2.ComponentMax(a, b)); break;
                    case 135: { Matrix3 m1 = RMat(), m2 = RMat(); WM(m1); WM(m2); WM(Matrix3.Mult(m1, m2)); break; }
                    case 136: { double d = HD(); WF(s); WD(d); WF(MathHelper.DegreesToRadians(s)); WF(MathHelper.RadiansToDegrees(s)); WD(MathHelper.DegreesToRadians(d)); WD(MathHelper.RadiansToDegrees(d)); break; }
                }
                Flush();
            }
        }
        if (On(138))
        {
            Op(138);
            WF(MathHelper.Pi); WF(MathHelper.TwoPi); WF(MathHelper.PiOver2); WF(MathHelper.PiOver4);
            WF(MathHelper.DegreesToRadians(1f)); WF(MathHelper.RadiansToDegrees(1f)); WD(MathHelper.DegreesToRadians(1.0)); WD(MathHelper.RadiansToDegrees(1.0));
            Flush();
        }
        // 140-143: framework Vector2Extensions / MatrixExtensions / DrawInfo
        for (int op = 140; op <= 143; op++)
        {
            if (!On(op)) continue;
            for (int i = 0; i < count; i++)
            {
                Op((byte)op);
                Vector2 a = new Vector2(HF(), HF()), b = new Vector2(HF(), HF());
                switch (op)
                {
                    case 140: { Matrix3 m = RMat(); WV(a); WM(m); WV(FwV2Ext.Transform(a, m)); break; }
                    case 141: WV(a); WV(b); WF(FwV2Ext.Distance(a, b)); WF(FwV2Ext.DistanceSquared(a, b)); break;
                    case 142:
                    {
                        Matrix3 m = RMat(); float r = Rnd(3) == 0 ? (float)((Rnd(720) - 360) * Math.PI / 180) : HF();
                        WM(m); WV(a); WF(r);
                        Matrix3 t;
                        t = m; MatrixExtensions.TranslateFromLeft(ref t, a); WM(t);
                        t = m; MatrixExtensions.TranslateFromRight(ref t, a); WM(t);
                        t = m; MatrixExtensions.RotateFromLeft(ref t, r); WM(t);
                        t = m; MatrixExtensions.RotateFromRight(ref t, r); WM(t);
                        t = m; MatrixExtensions.ScaleFromLeft(ref t, a); WM(t);
                        t = m; MatrixExtensions.ScaleFromRight(ref t, a); WM(t);
                        t = m; MatrixExtensions.ShearFromLeft(ref t, a); WM(t);
                        t = m; MatrixExtensions.ShearFromRight(ref t, a); WM(t);
                        break;
                    }
                    case 143:
                    {
                        Matrix3 m = RMat(), mi = RMat();
                        Vector2 T = Rnd(4) == 0 ? Vector2.Zero : (Rnd(5) == 0 ? new Vector2(0, -0f) : a);
                        Vector2 S = Rnd(4) == 0 ? Vector2.One : new Vector2(Rnd(3) == 0 ? HF() * 1e-3f : HF(), Rnd(4) == 0 ? 0f : HF());
                        float R = Rnd(3) == 0 ? 0 : (Rnd(2) == 0 ? Rnd(721) - 360 : HF());
                        Vector2 SH = Rnd(4) != 0 ? Vector2.Zero : b;
                        Vector2 O = Rnd(3) == 0 ? Vector2.Zero : new Vector2(HF(), HF());
                        var di = new DrawInfo(m, mi);
                        di.ApplyTransform(T, S, R, SH, O);
                        WM(m); WM(mi); WV(T); WV(S); WF(R); WV(SH); WV(O); WM(di.Matrix); WM(di.MatrixInverse);
                        break;
                    }
                }
                Flush();
            }
        }
        // 144-145: Precision
        if (On(144)) for (int i = 0; i < count; i++)
        {
            float x = HF(), y = Coin() ? x + (Rnd(9) - 4) * 0.00025f : HF(), e = Rnd(3) == 0 ? Precision.FLOAT_EPSILON : Math.Abs(HF());
            int m = (Precision.DefinitelyBigger(x, y, e) ? 1 : 0) | (Precision.AlmostBigger(x, y, e) ? 2 : 0) | (Precision.AlmostEquals(x, y, e) ? 4 : 0)
                  | (Precision.DefinitelyBigger(x, y) ? 8 : 0) | (Precision.AlmostBigger(x, y) ? 16 : 0) | (Precision.AlmostEquals(x, y) ? 32 : 0)
                  | (Precision.AlmostEquals(new Vector2(x, y), new Vector2(y, x), e) ? 64 : 0);
            Op(144); WF(x); WF(y); WF(e); WI(m); Flush();
        }
        if (On(145)) for (int i = 0; i < count; i++)
        {
            double x = HD(), y = Coin() ? x + (Rnd(9) - 4) * 2.5e-8 : HD(), e = Rnd(3) == 0 ? Precision.DOUBLE_EPSILON : Math.Abs(HD());
            int m = (Precision.DefinitelyBigger(x, y, e) ? 1 : 0) | (Precision.AlmostBigger(x, y, e) ? 2 : 0) | (Precision.AlmostEquals(x, y, e) ? 4 : 0)
                  | (Precision.DefinitelyBigger(x, y) ? 8 : 0) | (Precision.AlmostBigger(x, y) ? 16 : 0) | (Precision.AlmostEquals(x, y) ? 32 : 0);
            Op(145); WD(x); WD(y); WD(e); WI(m); Flush();
        }
        // 146-149: BindableNumber setter
        double[] precD = { 0.01, 0.1, 0.001, 0.05, 0.02, 1, 10, 0.5, 0.1f, 0.01f, 0.05f, 0.25, 1e-5, 0.3, double.Epsilon };
        float[] precF = { 0.01f, 0.1f, 0.05f, 0.001f, 1f, 10f, 0.5f, 0.25f, 0.3f, 1e-5f, float.Epsilon };
        foreach (int op in new[] { 146, 148 })
        {
            if (!On(op)) continue;
            for (int i = 0; i < count; i++)
            {
                double lo = Rnd(4) == 0 ? double.MinValue : (Rnd(3) == 0 ? new[] { 0, 0.5, 0.51, 0.4, 0.1f, 0.02, -10, 1 }[Rnd(8)] : HD());
                double hi = Rnd(4) == 0 ? double.MaxValue : (Rnd(3) == 0 ? new[] { 2, 1.99, 2.5, 10, 11, 12, 25 }[Rnd(7)] : HD());
                if (Rnd(8) != 0 && lo > hi) (lo, hi) = (hi, lo);
                double p = Rnd(4) == 0 ? Math.Abs(HD()) : precD[Rnd(precD.Length)];
                if (!(p > 0)) p = 0.01;
                double v = Rnd(3) == 0 ? HD() : (Rnd(2) == 0 ? Rnd(3001) / 1000.0 : Rnd(200001) / 10000.0);
                if (Rnd(5) == 0) v = Math.Round(v, 2) + (Rnd(3) - 1) * 0.005;
                Op((byte)op);
                int st = 0; double res = 0;
                try
                {
                    if (op == 146) { WD(lo); WD(hi); WD(p); WD(v); var bn = new BindableDouble { MinValue = lo, MaxValue = hi, Precision = p }; bn.Value = v; res = bn.Value; }
                    else { WD(v); WD(lo); WD(hi); WD(p); var bn = new BindableDouble(v) { MinValue = lo, MaxValue = hi, Precision = p }; res = bn.Value; }
                }
                catch (Exception e) { st = Status(e); }
                WI(st); WD(st == 0 ? res : 0); Flush();
            }
        }
        foreach (int op in new[] { 147, 149 })
        {
            if (!On(op)) continue;
            for (int i = 0; i < count; i++)
            {
                float lo = Rnd(4) == 0 ? float.MinValue : (Rnd(3) == 0 ? new[] { 0f, 1f, 0.05f, -10f, 0.5f, 50f }[Rnd(6)] : HF());
                float hi = Rnd(4) == 0 ? float.MaxValue : (Rnd(3) == 0 ? new[] { 0.99f, 25f, 10f, 1f, 200f, 11f }[Rnd(6)] : HF());
                if (Rnd(8) != 0 && lo > hi) (lo, hi) = (hi, lo);
                float p = Rnd(4) == 0 ? Math.Abs(HF()) : precF[Rnd(precF.Length)];
                if (!(p > 0)) p = 0.01f;
                float v = Rnd(3) == 0 ? HF() : (Rnd(2) == 0 ? (float)(Rnd(3001) / 1000.0) : (float)(Rnd(200001) / 10000.0));
                Op((byte)op);
                int st = 0; float res = 0;
                try
                {
                    if (op == 147) { WF(lo); WF(hi); WF(p); WF(v); var bn = new BindableFloat { MinValue = lo, MaxValue = hi, Precision = p }; bn.Value = v; res = bn.Value; }
                    else { WF(v); WF(lo); WF(hi); WF(p); var bn = new BindableFloat(v) { MinValue = lo, MaxValue = hi, Precision = p }; res = bn.Value; }
                }
                catch (Exception e) { st = Status(e); }
                WI(st); WF(st == 0 ? res : 0); Flush();
            }
        }
        // 210-215: Easing / Interpolation
        int nEasing = Enum.GetValues<Easing>().Length;
        for (int op = 210; op <= 215; op++)
        {
            if (!On(op)) continue;
            for (int i = 0; i < count; i++)
            {
                int ez = Rnd(nEasing + 1); // nEasing = out of range -> default branch
                double t = Rnd(4) switch { 0 => HD(), 1 => Rnd(1001) / 1000.0, 2 => new[] { 0, 0.5, 1, -0.0, 0.25, 0.75, 1 / 2.75, 2 / 2.75, 2.5 / 2.75 }[Rnd(9)], _ => (Next() % 1000001) / 1000000.0 };
                double s0 = HD(), e0 = Rnd(5) == 0 ? s0 : (Coin() ? s0 + Math.Abs(HD()) : HD());
                double time = Rnd(4) == 0 ? new[] { s0, e0, s0 - 1, e0 + 1 }[Rnd(4)] : s0 + (e0 - s0) * t;
                Op((byte)op);
                switch (op)
                {
                    case 210: WI(ez); WD(t); WD(Interpolation.ApplyEasing((Easing)ez, t)); break;
                    case 211: { double v1 = HD(), v2 = Rnd(6) == 0 ? v1 : HD(); WI(ez); WD(time); WD(v1); WD(v2); WD(s0); WD(e0); WD(Interpolation.ValueAt(time, v1, v2, s0, e0, (Easing)ez)); break; }
                    case 212: { float v1 = HF(), v2 = Rnd(6) == 0 ? v1 : HF(); WI(ez); WD(time); WF(v1); WF(v2); WD(s0); WD(e0); WF(Interpolation.ValueAt(time, v1, v2, s0, e0, (Easing)ez)); break; }
                    case 213: { var v1 = new Vector2(HF(), HF()); var v2 = new Vector2(HF(), HF()); WI(ez); WD(time); WV(v1); WV(v2); WD(s0); WD(e0); WV(Interpolation.ValueAt(time, v1, v2, s0, e0, (Easing)ez)); break; }
                    case 214: { int v1 = Rnd(2) == 0 ? (int)Next() : Rnd(2001) - 1000, v2 = Rnd(2) == 0 ? (int)Next() : Rnd(2001) - 1000; WI(ez); WD(time); WI(v1); WI(v2); WD(s0); WD(e0); WI(Interpolation.ValueAt(time, v1, v2, s0, e0, (Easing)ez)); break; }
                    case 215:
                    {
                        double a = HD(), b = HD(), h = Rnd(3) == 0 ? HD() : new[] { 50, 3000, 40, 1520, 0.5, 0 }[Rnd(6)] * (Rnd(3) == 0 ? HD() : 1), el = Rnd(3) == 0 ? HD() : Rnd(1700) / 100.0;
                        double bs = Rnd(3) == 0 ? HD() : Rnd(1001) / 1000.0;
                        double third = Coin() ? h : bs;
                        WD(a); WD(b); WD(third); WD(el);
                        WD(Interpolation.Lerp(a, b, third)); WD(Interpolation.DampContinuously(a, b, third, el));
                        try { double r = Interpolation.Damp(a, b, third, el); WI(0); WD(r); } catch (Exception e) { WI(Status(e)); WD(0); }
                        break;
                    }
                }
                Flush();
            }
        }
        // 220-221: float/double.DegreesToRadians / RadiansToDegrees
        if (On(220)) for (int i = 0; i < count; i++) { float x = HF(); Op(220); WF(x); WF(float.DegreesToRadians(x)); WF(float.RadiansToDegrees(x)); Flush(); }
        if (On(221)) for (int i = 0; i < count; i++) { double x = HD(); Op(221); WD(x); WD(double.DegreesToRadians(x)); WD(double.RadiansToDegrees(x)); Flush(); }
        // 222: Enumerable.Average(List<double>)
        if (On(222)) for (int i = 0; i < count; i++)
        {
            int n = Rnd(5) == 0 ? 1 + Rnd(40) : 8;
            var xs = new List<double>();
            for (int k = 0; k < n; k++) xs.Add(Rnd(3) == 0 ? HD() : 0.4 + Rnd(2101) / 1000.0 * (1 + (Next() % 1000) * 1e-9));
            Op(222); w.Write((byte)n); foreach (var x in xs) WD(x); WD(xs.Average()); Flush();
        }
        // 58 (existing record format): Math.Round(double, 2) on WU/WD ramp-like values and k/200 ties
        if (On(58)) for (int i = 0; i < count; i++)
        {
            double ini = 0.5 + Rnd(150) / 100.0, fin = 0.5 + Rnd(150) / 100.0, amt = Rnd(3) == 0 ? Rnd(10001) / 10000.0 : (Next() % 1000001) / 1000000.0;
            double v = Rnd(3) == 0 ? Rnd(600) / 200.0 + (Rnd(3) - 1) * 1e-15 : ini + (fin - ini) * Math.Clamp(amt, 0, 1);
            Op(58); w.Write(B(v)); w.Write((byte)2); w.Write((byte)0); w.Write(B(Math.Round(v, 2))); Flush();
        }
    }
}
