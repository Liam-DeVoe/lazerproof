// bmtest modinfo: lists every osu! mod with its beatmap-pipeline interfaces and settings
// (GetSettingsSourceProperties order, snake_case key, bindable type, default/min/max/precision).
using System;
using System.Linq;
using osu.Framework.Bindables;
using osu.Game.Configuration;
using osu.Game.Extensions;
using osu.Game.Rulesets.Mods;
using osu.Game.Rulesets.Osu;

namespace BmTest
{
    public static class ModInfo
    {
        public static void Run()
        {
            var ruleset = new OsuRuleset();
            foreach (var mod in ruleset.CreateAllMods())
            {
                var ifs = new[] { typeof(IApplicableToBeatmapConverter), typeof(IApplicableAfterBeatmapConversion), typeof(IApplicableToDifficulty),
                                  typeof(IApplicableToBeatmapProcessor), typeof(IApplicableToHitObject), typeof(IApplicableToBeatmap) }
                    .Where(i => i.IsInstanceOfType(mod)).Select(i => i.Name.Replace("IApplicable", ""));
                Console.WriteLine($"{mod.Acronym} {mod.GetType().FullName} [{string.Join(",", ifs)}]");
                foreach (var (_, p) in mod.GetSettingsSourceProperties())
                {
                    var b = (IBindable)p.GetValue(mod)!;
                    string extra = "";
                    var bt = b.GetType();
                    foreach (string n in new[] { "MinValue", "MaxValue", "Precision", "Default", "ExtendedMinValue", "ExtendedMaxValue" })
                    {
                        var pi = bt.GetProperty(n);
                        if (pi != null && pi.GetGetMethod() != null) extra += $" {n}={fmt(pi.GetValue(b))}";
                    }
                    Console.WriteLine($"  {p.Name.ToSnakeCase()} {bt.Name}<{string.Join(",", bt.GetGenericArguments().Select(t => t.Name))}> value={fmt(bt.GetProperty("Value")!.GetValue(b))}{extra}");
                }
            }
        }

        private static string fmt(object? o) => o switch
        {
            null => "null",
            double d => d.ToString("R") + "/" + Dumper.D(d),
            float f => f.ToString("R") + "/" + Dumper.F(f),
            _ => o.ToString() ?? "?",
        };
    }
}
