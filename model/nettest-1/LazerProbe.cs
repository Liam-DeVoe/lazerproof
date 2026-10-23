// `nettest lazer <count> <seed>`: loads lazer's own osu.Game / osu.Game.Rulesets.Osu (pinned build,
// ~/lazerproof/lazer/osu.Game.Rulesets.Osu/bin/Release/net10.0; other dependencies resolved from the
// oracle's build output) at runtime — no lazer rebuild — and
//  * prints every osu! mod's [SettingSource] properties in GetSettingsSourceProperties() order
//    (= APIMod.ToMod application order) with bindable type/default/min/max/precision (to stderr),
//  * prints targeted APIMod.ToMod results (WU/WD cross constraints, DT 1.135, Wiggle default, ...),
//  * streams op 230/231 records (APIMod.ToMod on random JSON values for every double/float setting) for
//    `lake exe nettest`, which checks them against `Framework.Bindable.BD/BF.init … setValue`.
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Runtime.Loader;
using osu.Framework.Bindables;

static partial class Gen
{
    static readonly string Root = Path.Combine(Environment.GetEnvironmentVariable("HOME") ?? "/home/exedev", "lazerproof");

    static Assembly Resolve(AssemblyLoadContext ctx, AssemblyName name)
    {
        foreach (var dir in new[] { Path.Combine(Root, "lazer/osu.Game.Rulesets.Osu/bin/Release/net10.0"), Path.Combine(Root, "oracle/bin/Release/net10.0") })
        {
            string p = Path.Combine(dir, name.Name + ".dll");
            if (File.Exists(p)) return ctx.LoadFromAssemblyPath(p);
        }
        return null;
    }

    static string Snake(string s) => string.Concat(s.Select((c, i) => i > 0 && char.IsUpper(c) ? "_" + char.ToLowerInvariant(c) : char.ToLowerInvariant(c).ToString()));

    static Type T(string n) => AppDomain.CurrentDomain.GetAssemblies().Select(a => a.GetType(n)).FirstOrDefault(t => t != null) ?? throw new Exception("type " + n);

    static object ruleset;
    static object ToMod(string acronym, Dictionary<string, object> settings)
    {
        var apiModT = T("osu.Game.Online.API.APIMod");
        var am = Activator.CreateInstance(apiModT);
        apiModT.GetProperty("Acronym").SetValue(am, acronym);
        apiModT.GetProperty("Settings").SetValue(am, settings);
        return apiModT.GetMethod("ToMod").Invoke(am, new[] { ruleset });
    }
    static IEnumerable<PropertyInfo> SettingProps(object mod)
    {
        var ext = T("osu.Game.Configuration.SettingSourceExtensions");
        var m = ext.GetMethod("GetSettingsSourceProperties");
        foreach (object tup in (System.Collections.IEnumerable)m.Invoke(null, new[] { mod }))
            yield return (PropertyInfo)tup.GetType().GetField("Item2").GetValue(tup);
    }

    public static int RunLazer(string[] args)
    {
        int count = args.Length > 1 ? int.Parse(args[1]) : 200; ulong seed = args.Length > 2 ? ulong.Parse(args[2]) : 1;
        s0 = seed ^ 0x9E3779B97F4A7C15; s1 = seed * 0xBF58476D1CE4E5B9 + 1; s2 = 0x94D049BB133111EB; s3 = seed + 12345;
        AssemblyLoadContext.Default.Resolving += Resolve;
        var rulesetAsm = AssemblyLoadContext.Default.LoadFromAssemblyPath(Path.Combine(Root, "lazer/osu.Game.Rulesets.Osu/bin/Release/net10.0/osu.Game.Rulesets.Osu.dll"));
        ruleset = Activator.CreateInstance(rulesetAsm.GetType("osu.Game.Rulesets.Osu.OsuRuleset"));
        outp = new BufferedStream(Console.OpenStandardOutput(), 1 << 20);
        var err = Console.Error;

        var allMods = ((System.Collections.IEnumerable)ruleset.GetType().GetMethod("CreateAllMods").Invoke(ruleset, null)).Cast<object>().ToList();
        var targets = new List<(string acr, string key, PropertyInfo p, bool isFloat)>();
        foreach (var mod in allMods)
        {
            string acr = (string)mod.GetType().GetProperty("Acronym").GetValue(mod);
            var parts = new List<string>();
            foreach (var p in SettingProps(mod))
            {
                object b = p.GetValue(mod);
                string d = b switch
                {
                    BindableNumber<double> bd => $"double def {bd.Default:R} [{bd.MinValue:R}, {bd.MaxValue:R}] p {bd.Precision:R}",
                    BindableNumber<float> bf => $"float def {bf.Default:R} [{bf.MinValue:R}, {bf.MaxValue:R}] p {bf.Precision:R}",
                    BindableNumber<int> bi => $"int def {bi.Default} [{bi.MinValue}, {bi.MaxValue}]",
                    _ => b.GetType().Name + " def " + (b.GetType().GetProperty("Default")?.GetValue(b) ?? "?")
                };
                parts.Add($"{Snake(p.Name)}: {d}");
                if (acr != "WU" && acr != "WD" && (b is BindableNumber<double> || b is BindableNumber<float>)) targets.Add((acr, Snake(p.Name), p, b is BindableNumber<float>));
            }
            if (parts.Count > 0) err.WriteLine($"{acr} ({mod.GetType().Name}): " + string.Join("; ", parts));
        }

        // targeted checks
        string Val(object mod, string prop) { object b = mod.GetType().GetProperty(prop).GetValue(mod); return b.GetType().GetProperty("Value").GetValue(b) switch { double x => $"{x:R}", float f => $"{f:R}f", var o => o?.ToString() ?? "null" }; }
        void Show(string acr, string json, params (string k, object v)[] kv)
        {
            var mod = ToMod(acr, kv.ToDictionary(t => t.k, t => t.v));
            var props = SettingProps(mod).Where(p => p.PropertyType.Name.Contains("Bindable")).Select(p => $"{p.Name}={Val(mod, p.Name)}");
            err.WriteLine($"ToMod {acr} {json}: " + string.Join(", ", props));
        }
        Show("WU", "{final_rate: 0.8}", ("final_rate", 0.8));
        Show("WU", "{initial_rate: 1.6, final_rate: 1.2}", ("initial_rate", 1.6), ("final_rate", 1.2));
        Show("WU", "{initial_rate: 1.99}", ("initial_rate", 1.99));
        Show("WD", "{final_rate: 1.5}", ("final_rate", 1.5));
        Show("WD", "{initial_rate: 0.6, final_rate: 0.9}", ("initial_rate", 0.6), ("final_rate", 0.9));
        Show("DT", "{speed_change: 1.135}", ("speed_change", 1.135));
        Show("DT", "{speed_change: 1.125}", ("speed_change", 1.125));
        Show("DT", "{speed_change: 3}", ("speed_change", 3L));
        Show("HT", "{speed_change: 0.755}", ("speed_change", 0.755));
        Show("WG", "{}");
        Show("WG", "{strength: 1.5}", ("strength", 1.5));
        Show("DA", "{approach_rate: 5.3, circle_size: 11.5}", ("approach_rate", 5.3), ("circle_size", 11.5));
        Show("GR", "{start_scale: 0.333}", ("start_scale", 0.333));
        Show("AS", "{initial_rate: 1.234}", ("initial_rate", 1.234));
        Show("RD", "{seed: 12345, angle_sharpness: 7.25}", ("seed", 12345L), ("angle_sharpness", 7.25));

        // op 230/231 records
        double[] specials = { 0, -0.0, 1, -1, 0.5, 1.135, 1.125, 1.145, 1.005, 1.015, 0.9095, 1.2345, 99, 1e9, -1e9, 0.05, 0.075, 0.025, 2.675 };
        int n = 0;
        foreach (var (acr, key, p, isFloat) in targets)
        {
            var fresh = ToMod(acr, new Dictionary<string, object>());
            object fb = p.GetValue(fresh);
            for (int i = 0; i < count; i++)
            {
                object jv; double vin;
                switch (Rnd(4))
                {
                    case 0: vin = specials[Rnd(specials.Length)]; jv = vin; break;
                    case 1: { long l = Rnd(30) - 5; vin = l; jv = l; break; }
                    case 2: vin = Rnd(30001) / 1000.0; jv = vin; break;
                    default: vin = HD(); jv = vin; break;
                }
                object mod;
                try { mod = ToMod(acr, new Dictionary<string, object> { [key] = jv }); } catch { continue; }
                object b = p.GetValue(mod);
                if (!isFloat)
                {
                    var bd = (BindableNumber<double>)b; var fd = (BindableNumber<double>)fb;
                    Op(230); WD(fd.Default); WD(bd.MinValue); WD(bd.MaxValue); WD(bd.Precision); WD(vin); WD(bd.Value);
                }
                else
                {
                    var bf = (BindableNumber<float>)b; var ff = (BindableNumber<float>)fb;
                    Op(231); WF(ff.Default); WF(bf.MinValue); WF(bf.MaxValue); WF(bf.Precision); WD(vin); WF(bf.Value);
                }
                n++; Flush();
            }
        }
        err.WriteLine($"emitted {n} APIMod.ToMod records over {targets.Count} double/float settings");
        Flush(true); outp.Flush();
        return 0;
    }
}
