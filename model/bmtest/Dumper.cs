// bmtest dumper: loads a .osu file through lazer exactly as the game does
// (Decoder.GetDecoder<Beatmap> -> Decode -> WorkingBeatmap.GetPlayableBeatmap(osu ruleset, mods))
// and prints every gameplay-relevant field of the playable beatmap as raw IEEE bits.
// The Lean executable `bmdump` (model/BmDump/Main.lean) prints the same format from the model.
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text;
using System.Threading;
using Newtonsoft.Json;
using osu.Game.Beatmaps;
using osu.Game.Beatmaps.Legacy;
using osu.Game.IO;
using osu.Game.Online.API;
using osu.Game.Rulesets.Mods;
using osu.Game.Rulesets.Objects;
using osu.Game.Rulesets.Objects.Types;
using osu.Game.Rulesets.Osu;
using osu.Game.Rulesets.Osu.Objects;
using osu.Game.Rulesets.Osu.Scoring;
using osu.Game.Rulesets.Scoring;
using osuTK;

namespace BmTest
{
    /// The game's ruleset store has all four official rulesets. Only `OnlineID` matters to the decoder
    /// (`Mode:` lines, mania CS clamping), so 1..3 are stub infos; 0 is the real osu! ruleset.
    public class GameRulesetStore : osu.Game.Rulesets.RulesetStore
    {
        private readonly List<osu.Game.Rulesets.RulesetInfo> rulesets = new List<osu.Game.Rulesets.RulesetInfo>
        {
            new OsuRuleset().RulesetInfo,
            new osu.Game.Rulesets.RulesetInfo("taiko", "osu!taiko", "stub", 1),
            new osu.Game.Rulesets.RulesetInfo("fruits", "osu!catch", "stub", 2),
            new osu.Game.Rulesets.RulesetInfo("mania", "osu!mania", "stub", 3),
        };

        public override IEnumerable<osu.Game.Rulesets.RulesetInfo> AvailableRulesets => rulesets;
    }

    public static class Dumper
    {
        private static bool registered;

        private static void register()
        {
            if (registered) return;
            osu.Game.Beatmaps.Formats.Decoder.RegisterDependencies(new GameRulesetStore());
            registered = true;
        }

        private static readonly FieldInfo cumulativeLengthField =
            typeof(SliderPath).GetField("cumulativeLength", BindingFlags.NonPublic | BindingFlags.Instance)!;

        public static string D(double x) => double.IsNaN(x) ? "7ff8000000000000" : BitConverter.DoubleToInt64Bits(x).ToString("x16");
        public static string F(float x) => float.IsNaN(x) ? "7fc00000" : BitConverter.SingleToInt32Bits(x).ToString("x8");
        public static string V(Vector2 v) => F(v.X) + "," + F(v.Y);
        public static string B(bool b) => b ? "1" : "0";

        private static string pathType(PathType? t)
        {
            if (t == null) return "none";
            var p = t.Value;
            switch (p.Type)
            {
                case SplineType.Catmull: return "catmull";
                case SplineType.Linear: return "linear";
                case SplineType.PerfectCurve: return "perfect";
                case SplineType.BSpline: return p.Degree == null ? "bezier" : "bspline" + p.Degree.Value;
            }
            return "?";
        }

        private static string windows(HitWindows? hw)
        {
            if (hw == null) return "null";
            if (hw is OsuHitWindows)
                return D(hw.WindowFor(HitResult.Great)) + "," + D(hw.WindowFor(HitResult.Ok)) + "," + D(hw.WindowFor(HitResult.Meh)) + "," + D(hw.WindowFor(HitResult.Miss));
            if (hw == HitWindows.Empty) return "empty";
            return "other:" + hw.GetType().Name;
        }

        private static string kind(HitObject h) => h switch
        {
            SliderHeadCircle => "head",
            SliderTailCircle => "tail",
            SliderRepeat => "repeat",
            SliderTick => "tick",
            SpinnerBonusTick => "spinbonus",
            SpinnerTick => "spintick",
            Slider => "slider",
            Spinner => "spinner",
            HitCircle => "circle",
            _ => "unknown:" + h.GetType().Name,
        };

        private static string common(OsuHitObject h)
            => $"start={D(h.StartTime)} pos={V(h.Position)} stack={h.StackHeight} scale={F(h.Scale)} radius={D(h.Radius)} preempt={D(h.TimePreempt)} fadein={D(h.TimeFadeIn)} "
               + $"stackoffset={V(h.StackOffset)} stackedpos={V(h.StackedPosition)} ci={h.ComboIndex} ciwo={h.ComboIndexWithOffsets} icc={h.IndexInCurrentCombo} "
               + $"hw={windows(h.HitWindows)} mjo={D(h.MaximumJudgementOffset)} kiai={B(h.Kiai)}";

        public static void Dump(IBeatmap pb, TextWriter w)
        {
            w.WriteLine($"version {pb.BeatmapVersion}");
            var d = pb.Difficulty;
            w.WriteLine($"difficulty hp={F(d.DrainRate)} cs={F(d.CircleSize)} od={F(d.OverallDifficulty)} ar={F(d.ApproachRate)} sm={D(d.SliderMultiplier)} tr={D(d.SliderTickRate)}");
            w.WriteLine($"stackleniency {F(pb.StackLeniency)}");
            w.WriteLine($"audioleadin {D(pb.AudioLeadIn)}");
            foreach (var t in pb.ControlPointInfo.TimingPoints)
                w.WriteLine($"timing {D(t.Time)} {D(t.BeatLength)} {t.TimeSignature.Numerator}");
            if (pb.ControlPointInfo is LegacyControlPointInfo lcpi)
                foreach (var p in lcpi.DifficultyPoints)
                    w.WriteLine($"diffpoint {D(p.Time)} {D(p.SliderVelocity)} {B(p.GenerateTicks)}");
            foreach (var e in pb.ControlPointInfo.EffectPoints)
                w.WriteLine($"effect {D(e.Time)} {B(e.KiaiMode)} {D(e.ScrollSpeed)}");
            foreach (var b in pb.Breaks)
                w.WriteLine($"break {D(b.StartTime)} {D(b.EndTime)}");

            int i = 0;
            foreach (var ho in pb.HitObjects)
            {
                var h = (OsuHitObject)ho;
                w.WriteLine($"object {i++} {kind(h)} end={D(h.GetEndTime())} {common(h)} nc={B(h.NewCombo)} co={h.ComboOffset} lic={B(h.LastInCombo)}");

                if (h is Slider s)
                {
                    w.WriteLine($"slider repeats={s.RepeatCount} vel={D(s.Velocity)} tickdist={D(s.TickDistance)} tdm={D(s.TickDistanceMultiplier)} svm={D(s.SliderVelocityMultiplier)} "
                                + $"genticks={B(s.GenerateTicks)} dist={D(s.Path.Distance)} cdist={D(s.Path.CalculatedDistance)} "
                                + $"expected={(s.Path.ExpectedDistance.Value is double e ? D(e) : "null")} duration={D(s.Duration)} spandur={D(s.SpanDuration)} "
                                + $"endpos={V(s.EndPosition)} stackedendpos={V(s.StackedEndPosition)} classic={B(s.ClassicSliderBehaviour)}");
                    foreach (var cp in s.Path.ControlPoints)
                        w.WriteLine($"cp {V(cp.Position)} {pathType(cp.Type)}");
                    foreach (var p in s.Path.CalculatedPath)
                        w.WriteLine($"pp {V(p)}");
                    foreach (double c in (List<double>)cumulativeLengthField.GetValue(s.Path)!)
                        w.WriteLine($"cl {D(c)}");
                }

                if (h is Spinner sp)
                    w.WriteLine($"spinner duration={D(sp.Duration)} req={sp.SpinsRequired} bonus={sp.MaximumBonusSpins}");

                int j = 0;
                foreach (var nho in h.NestedHitObjects)
                {
                    var n = (OsuHitObject)nho;
                    var sb = new StringBuilder($"nested {j++} {kind(n)} {common(n)}");
                    switch (n)
                    {
                        case SliderTick t:
                            sb.Append($" prog={D(t.PathProgress)} span={t.SpanIndex} spanstart={D(t.SpanStartTime)}");
                            break;
                        case SliderRepeat r:
                            sb.Append($" prog={D(r.PathProgress)} rep={r.RepeatIndex}");
                            break;
                        case SliderTailCircle tc:
                            sb.Append($" rep={tc.RepeatIndex} classic={B(tc.ClassicSliderBehaviour)} st={B(tc.GetType() != typeof(SliderTailCircle))}");
                            break;
                        case SliderHeadCircle hc:
                            sb.Append($" classic={B(hc.ClassicSliderBehaviour)}");
                            break;
                        case SpinnerTick st:
                            sb.Append($" spindur={D(st.SpinnerDuration)}");
                            break;
                    }
                    w.WriteLine(sb.ToString());
                }
            }
        }

        /// Loads and dumps one beatmap. Never throws: failures become an `error` line.
        public static void Process(string file, string? modsJson, TextWriter w)
        {
            register();
            Beatmap beatmap;

            try
            {
                byte[] bytes = File.ReadAllBytes(file);
                using (var ms = new MemoryStream(bytes))
                using (var reader = new LineBufferedReader(ms))
                    beatmap = osu.Game.Beatmaps.Formats.Decoder.GetDecoder<Beatmap>(reader).Decode(reader);
            }
            catch (Exception e)
            {
                w.WriteLine($"error decode {e.GetType().Name}");
                return;
            }

            w.WriteLine($"mode {beatmap.BeatmapInfo.Ruleset.OnlineID}");
            if (beatmap.BeatmapInfo.Ruleset.OnlineID != 0)
                return;

            IBeatmap playable;
            var mods = new List<Mod>();

            try
            {
                var ruleset = new OsuRuleset();

                if (modsJson != null)
                {
                    foreach (var am in JsonConvert.DeserializeObject<List<APIMod>>(modsJson) ?? new List<APIMod>())
                        mods.Add(am.ToMod(ruleset));
                }

                var working = new FlatWorkingBeatmap(beatmap);
                playable = working.GetPlayableBeatmap(ruleset.RulesetInfo, mods, CancellationToken.None);
            }
            catch (Exception e)
            {
                w.WriteLine($"error playable {e.GetType().Name}");
                return;
            }

            foreach (string l in ModDump.Settings(mods))
                w.WriteLine(l);
            Dump(playable, w);
            foreach (string l in ModDump.States(mods, playable))
                w.WriteLine(l);
        }

        public static int DumpOne(string file, string? modsJson)
        {
            var w = new StreamWriter(Console.OpenStandardOutput(), new UTF8Encoding(false), 1 << 16) { NewLine = "\n" };
            Process(file, modsJson, w);
            w.Flush();
            return 0;
        }

        /// batch LIST OUTDIR: LIST lines are `<osu path>\t<out name>[\t<mods json>]`.
        public static int Batch(string list, string outDir)
        {
            Directory.CreateDirectory(outDir);

            foreach (string line in File.ReadAllLines(list))
            {
                if (line.Length == 0) continue;
                string[] parts = line.Split('\t');
                using (var w = new StreamWriter(Path.Combine(outDir, parts[1]), false, new UTF8Encoding(false), 1 << 16) { NewLine = "\n" })
                    Process(parts[0], parts.Length > 2 ? parts[2] : null, w);
            }

            return 0;
        }
    }
}
