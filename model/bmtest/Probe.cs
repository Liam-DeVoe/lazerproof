using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using osu.Game.Beatmaps.ControlPoints;
using osu.Game.Beatmaps.Formats;
using osu.Game.Rulesets.Osu.Objects;

namespace BmTest
{
    internal enum LegacyEventTypeCopy { Background = 0, Video = 1, Break = 2, Colour = 3, Sprite = 4, Sample = 5, Animation = 6 }

    public static class Probe
    {
        public static void Run()
        {
            var t = new TimingControlPoint();
            foreach (double v in new[] { 1.0, 5.9, 6.0, 70000.0, -5.0 })
            {
                t.BeatLength = v;
                Console.WriteLine($"timing.BeatLength {v} -> {t.BeatLength:R}");
            }
            foreach (double v in new[] { 333.33333333333337, 1000.0/3, 461.538461538462, 0.1+0.2, 1234.5678901234567, 59999.999999999993 })
            {
                t.BeatLength = v;
                Console.WriteLine($"timing.BeatLength {v:R} -> {t.BeatLength:R} {BitConverter.DoubleToInt64Bits(v):x} {BitConverter.DoubleToInt64Bits(t.BeatLength):x}");
            }
            var bd = new osu.Framework.Bindables.BindableDouble();
            Console.WriteLine($"precision {bd.Precision:R} dec {decimal.CreateTruncating(bd.Precision)}");
            var d = new DifficultyControlPoint();
            foreach (double v in new[] { 0.01, 0.1, 10.0, 100.0, 1e300 })
            {
                d.SliderVelocity = v;
                Console.WriteLine($"diff.SV {v} -> {d.SliderVelocity:R}");
            }
            var s = new Slider();
            foreach (double v in new[] { 0.01, 100.0 })
            {
                s.SliderVelocityMultiplier = v;
                Console.WriteLine($"slider.SVM {v} -> {s.SliderVelocityMultiplier:R}");
            }
            string[] strs = { "General", "general", " General", "General ", "0", "7", "12", "-1", "+3", "General,Events", "General, Events", "Events,HitObjects",
                "", " ", "1.0", "0x1", "00003", "99999999999", "2147483647", "4294967295", "Difficulty\t", " General", "General ", "1 ", " 1", "1,2", "Break", "2", "Break,Sprite", "Sprite,Colour", "5,", ",5", "General,", "3,Video", "-0", "+0", "Events, 1" };
            foreach (var str in strs)
            {
                bool ok = Enum.TryParse(str, out LegacyDecoder<osu.Game.Beatmaps.Beatmap>.Section sec);
                bool ok2 = Enum.TryParse(str, out LegacyEventTypeCopy ev);
                Console.WriteLine($"enum [{Escape(str)}] section {ok} {(int)sec} event {ok2} {(int)ev}");
            }
        }

        public static string Escape(string s) => string.Concat(s.Select(c => c < 32 || c > 126 ? $"\\u{(int)c:x4}" : c.ToString()));

        public static void Letters()
        {
            // print ranges [lo,hi] of BMP chars that char.IsLetter
            int start = -1;
            for (int c = 0; c <= 0x10000; c++)
            {
                bool l = c < 0x10000 && char.IsLetter((char)c);
                if (l && start < 0) start = c;
                if (!l && start >= 0) { Console.WriteLine($"{start} {c - 1}"); start = -1; }
            }
        }

        public static void WhiteSpace()
        {
            for (int c = 0; c < 0x10000; c++)
                if (char.IsWhiteSpace((char)c)) Console.WriteLine(c);
        }

        public static void SortTest(int count, int seed)
        {
            var rng = new Random(seed);
            for (int k = 0; k < count; k++)
            {
                int n = rng.Next(0, 80);
                int distinct = rng.Next(1, 10);
                var keys = new List<(double key, int tag)>();
                for (int i = 0; i < n; i++) keys.Add((rng.Next(distinct), i));
                var sorted = keys.ToList();
                sorted.Sort((a, b) => a.key.CompareTo(b.key));
                Console.WriteLine(string.Join(",", keys.Select(x => x.key)) + " " + string.Join(",", sorted.Select(x => x.tag)));
            }
        }
    }
}
