// Dump of decoded mod settings (APIMod.ToMod result) and of the beatmap-derived mod state that
// GetPlayableBeatmap leaves inside the mod instances (IApplicableToBeatmap side effects).
using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using osu.Framework.Bindables;
using osu.Game.Beatmaps;
using osu.Game.Configuration;
using osu.Game.Extensions;
using osu.Game.Rulesets.Mods;
using osu.Game.Rulesets.Objects;

namespace BmTest
{
    public static class ModDump
    {
        private static string fmt(object? o) => o switch
        {
            null => "null",
            bool b => Dumper.B(b),
            double d => Dumper.D(d),
            float f => Dumper.F(f),
            int i => i.ToString(),
            Enum e => Convert.ToInt64(e).ToString(),
            _ => "?" + o.GetType().Name,
        };

        public static IEnumerable<string> Settings(IReadOnlyList<Mod> mods)
        {
            for (int i = 0; i < mods.Count; i++)
            {
                var m = mods[i];
                if (m is UnknownMod) { yield return $"mod {i} unknown {m.Acronym}"; continue; }
                var parts = new List<string> { $"mod {i} {m.Acronym}" };
                foreach (var (_, p) in m.GetSettingsSourceProperties())
                {
                    var b = (IBindable)p.GetValue(m)!;
                    parts.Add(p.Name.ToSnakeCase() + "=" + fmt(b.GetType().GetProperty("Value")!.GetValue(b)));
                }
                yield return string.Join(" ", parts);
            }
        }

        private static string path(IBeatmap pb, HitObject? h)
        {
            if (h == null) return "null";
            for (int i = 0; i < pb.HitObjects.Count; i++)
            {
                var o = pb.HitObjects[i];
                if (ReferenceEquals(o, h)) return i.ToString();
                for (int j = 0; j < o.NestedHitObjects.Count; j++)
                    if (ReferenceEquals(o.NestedHitObjects[j], h)) return i + "." + j;
            }
            return "gone";
        }

        private static object? get(object o, Type t, string name) =>
            t.GetField(name, BindingFlags.NonPublic | BindingFlags.Instance)?.GetValue(o)
            ?? t.GetProperty(name, BindingFlags.NonPublic | BindingFlags.Public | BindingFlags.Instance)?.GetValue(o);

        public static IEnumerable<string> States(IReadOnlyList<Mod> mods, IBeatmap pb)
        {
            for (int i = 0; i < mods.Count; i++)
            {
                var m = mods[i];
                if (m is ModWithVisibilityAdjustment)
                    yield return $"modstate {i} firstobject {path(pb, (HitObject?)get(m, typeof(ModWithVisibilityAdjustment), "FirstObject"))}";
                if (m is ModTimeRamp)
                    yield return $"modstate {i} timeramp {Dumper.D((double)get(m, typeof(ModTimeRamp), "beginRampTime")!)} {Dumper.D((double)get(m, typeof(ModTimeRamp), "finalRateTime")!)}";
                if (m is ModAdaptiveSpeed)
                {
                    var dict = (Dictionary<HitObject, double>)get(m, typeof(ModAdaptiveSpeed), "precedingEndTimes")!;
                    foreach (var kv in dict)
                        yield return $"modstate {i} preceding {path(pb, kv.Key)} {Dumper.D(kv.Value)}";
                }
            }
        }
    }
}
