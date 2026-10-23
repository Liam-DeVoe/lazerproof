// Optional debugging/interface dumps for the formal model (docs/model-sim.md):
//  --dump-playable PATH : the playable beatmap exactly as the DrawableRuleset sees it (every hit object + nested objects,
//                         all simulation-relevant fields, floats as raw IEEE bits in hex).
//  --dump-env PATH      : screen-space DrawInfo matrices used by the hit tests (HitObjectContainer, every HitReceptor,
//                         sliders' DrawInfo/OriginPosition/DrawSize), plus the per-step input-manager mouse position.
// In batch mode PATH is a directory and files are named "<job index>.json". Neither dump changes gameplay: the env probe
// only reads (cached) DrawInfo values at the start of each frame-stable step (FrameStableComponents run before input).

using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text.Json;
using osu.Game.Beatmaps;
using osu.Game.Rulesets.Objects;
using osu.Game.Rulesets.Objects.Drawables;
using osu.Game.Rulesets.Objects.Types;
using osu.Game.Rulesets.Osu.Objects;
using osu.Game.Rulesets.Osu.Objects.Drawables;
using osu.Game.Rulesets.Osu.UI;
using osu.Game.Rulesets.Scoring;
using osu.Game.Rulesets.UI;
using osuTK;

namespace Oracle
{
    public static class Dump
    {
        public static string D(double x) => "0x" + BitConverter.DoubleToUInt64Bits(x).ToString("x16");
        public static string F(float x) => "0x" + BitConverter.SingleToUInt32Bits(x).ToString("x8");

        private static void wd(Utf8JsonWriter w, string name, double x) => w.WriteString(name, D(x));
        private static void wf(Utf8JsonWriter w, string name, float x) => w.WriteString(name, F(x));

        private static void wv(Utf8JsonWriter w, string name, Vector2 v)
        {
            w.WriteStartArray(name);
            w.WriteStringValue(F(v.X));
            w.WriteStringValue(F(v.Y));
            w.WriteEndArray();
        }

        public static void WriteMatrix(Utf8JsonWriter w, string name, Matrix3 m)
        {
            w.WriteStartArray(name);
            foreach (float f in new[] { m.M11, m.M12, m.M13, m.M21, m.M22, m.M23, m.M31, m.M32, m.M33 })
                w.WriteStringValue(F(f));
            w.WriteEndArray();
        }

        private static readonly FieldInfo calculated_path = typeof(SliderPath).GetField("calculatedPath", BindingFlags.NonPublic | BindingFlags.Instance)!;
        private static readonly FieldInfo cumulative_length = typeof(SliderPath).GetField("cumulativeLength", BindingFlags.NonPublic | BindingFlags.Instance)!;

        private static string kind(HitObject h) => h switch
        {
            SliderHeadCircle => "head",
            SliderTailCircle => "tail",
            SliderRepeat => "repeat",
            SliderTick => "tick",
            SpinnerBonusTick => "spinner_bonus_tick",
            SpinnerTick => "spinner_tick",
            Slider => "slider",
            Spinner => "spinner",
            HitCircle => "circle",
            _ => h.GetType().Name,
        };

        private static void writeCommon(Utf8JsonWriter w, OsuHitObject h)
        {
            w.WriteString("kind", kind(h));
            w.WriteString("type", h.GetType().Name);
            wd(w, "start", h.StartTime);
            wd(w, "end", h.GetEndTime());
            wv(w, "pos", h.Position);
            wv(w, "stacked", h.StackedPosition);
            w.WriteNumber("stack_height", h.StackHeight);
            wf(w, "scale", h.Scale);
            wd(w, "radius", h.Radius);
            wd(w, "preempt", h.TimePreempt);
            wd(w, "fade_in", h.TimeFadeIn);
            wd(w, "max_judgement_offset", h.MaximumJudgementOffset);
            var hw = h.HitWindows;
            w.WriteStartArray("hit_windows");
            if (hw != null)
                foreach (var r in new[] { HitResult.Great, HitResult.Ok, HitResult.Meh, HitResult.Miss })
                    w.WriteStringValue(D(hw.WindowFor(r)));
            w.WriteEndArray();
            w.WriteString("judgement", h.Judgement.GetType().Name);
            w.WriteString("max_result", h.Judgement.MaxResult.ToString());
            w.WriteString("min_result", h.Judgement.MinResult.ToString());
            w.WriteBoolean("new_combo", h.NewCombo);
            w.WriteNumber("combo_index", h.ComboIndex);
            w.WriteNumber("index_in_combo", h.IndexInCurrentCombo);
            w.WriteBoolean("last_in_combo", h.LastInCombo);
        }

        public static void WritePlayable(string path, IBeatmap playable, WorkingBeatmap working)
        {
            using var fs = File.Create(path);
            using var w = new Utf8JsonWriter(fs);
            w.WriteStartObject();
            w.WriteString("format", "playable-1");
            w.WriteNumber("beatmap_version", playable.BeatmapVersion);
            wd(w, "audio_lead_in", playable.AudioLeadIn);
            var d = playable.Difficulty;
            w.WriteStartObject("difficulty");
            wf(w, "cs", d.CircleSize);
            wf(w, "hp", d.DrainRate);
            wf(w, "od", d.OverallDifficulty);
            wf(w, "ar", d.ApproachRate);
            wd(w, "slider_multiplier", d.SliderMultiplier);
            wd(w, "slider_tick_rate", d.SliderTickRate);
            w.WriteEndObject();
            var bd = playable.BeatmapInfo.Difficulty; // unmodded (score multiplier context)
            w.WriteStartObject("base_difficulty");
            wf(w, "cs", bd.CircleSize);
            wf(w, "hp", bd.DrainRate);
            wf(w, "od", bd.OverallDifficulty);
            wf(w, "ar", bd.ApproachRate);
            w.WriteEndObject();

            w.WriteStartArray("breaks");
            foreach (var b in playable.Breaks)
            {
                w.WriteStartArray();
                w.WriteStringValue(D(b.StartTime));
                w.WriteStringValue(D(b.EndTime));
                w.WriteEndArray();
            }
            w.WriteEndArray();

            w.WriteStartArray("objects");

            foreach (var ho in playable.HitObjects)
            {
                var h = (OsuHitObject)ho;
                w.WriteStartObject();
                writeCommon(w, h);

                switch (h)
                {
                    case Slider s:
                        w.WriteNumber("span_count", s.SpanCount());
                        w.WriteNumber("repeat_count", s.RepeatCount);
                        wd(w, "duration", s.Duration);
                        wd(w, "span_duration", s.SpanDuration);
                        wd(w, "velocity", s.Velocity);
                        wd(w, "tick_distance", s.TickDistance);
                        wd(w, "tick_distance_multiplier", s.TickDistanceMultiplier);
                        wd(w, "path_distance", s.Path.Distance);
                        w.WriteBoolean("classic", s.ClassicSliderBehaviour);
                        w.WriteBoolean("generate_ticks", s.GenerateTicks);
                        wv(w, "end_position", s.EndPosition);
                        var cp = (List<Vector2>)calculated_path.GetValue(s.Path)!;
                        var cl = (List<double>)cumulative_length.GetValue(s.Path)!;
                        w.WriteStartArray("path");
                        foreach (var v in cp)
                        {
                            w.WriteStringValue(F(v.X));
                            w.WriteStringValue(F(v.Y));
                        }
                        w.WriteEndArray();
                        w.WriteStartArray("cumulative_length");
                        foreach (double c in cl)
                            w.WriteStringValue(D(c));
                        w.WriteEndArray();
                        break;

                    case Spinner sp:
                        wd(w, "duration", sp.Duration);
                        w.WriteNumber("spins_required", sp.SpinsRequired);
                        w.WriteNumber("maximum_bonus_spins", sp.MaximumBonusSpins);
                        break;
                }

                w.WriteStartArray("nested");

                foreach (var no in h.NestedHitObjects)
                {
                    var n = (OsuHitObject)no;
                    w.WriteStartObject();
                    writeCommon(w, n);

                    switch (n)
                    {
                        case SliderTick t:
                            w.WriteNumber("span_index", t.SpanIndex);
                            wd(w, "span_start", t.SpanStartTime);
                            wd(w, "path_progress", t.PathProgress);
                            break;

                        case SliderRepeat r:
                            w.WriteNumber("repeat_index", r.RepeatIndex);
                            wd(w, "path_progress", r.PathProgress);
                            break;

                        case SliderTailCircle tc:
                            w.WriteNumber("repeat_index", tc.RepeatIndex);
                            break;
                    }

                    w.WriteEndObject();
                }

                w.WriteEndArray();
                w.WriteEndObject();
            }

            w.WriteEndArray();
            w.WriteEndObject();
        }
    }

    /// <summary>
    /// Records screen-space geometry at the start of frame-stable steps. Invoked by <see cref="StepRecorder"/> (a
    /// FrameStableComponent, i.e. before the input manager of the same step), so values are those left by the previous step.
    /// </summary>
    public class EnvProbe
    {
        private readonly DrawableRuleset drawableRuleset;
        private readonly Dictionary<HitObject, int> topIndex;
        private readonly HashSet<HitObject> probed = new HashSet<HitObject>(ReferenceEqualityComparer.Instance);
        private readonly MemoryStream objects = new MemoryStream();
        private readonly Utf8JsonWriter ow;
        private readonly List<(double time, Vector2 pos, bool valid)> mouse = new List<(double, Vector2, bool)>();
        private Matrix3? hocMatrix, hocInverse;
        private bool hocChanged;
        private readonly List<(double, Matrix3, Matrix3)> hocHistory = new List<(double, Matrix3, Matrix3)>();
        private readonly int maxSliderSamples;

        public EnvProbe(DrawableRuleset drawableRuleset, IBeatmap playable, int maxSliderSamples = 1000000)
        {
            this.drawableRuleset = drawableRuleset;
            this.maxSliderSamples = maxSliderSamples;
            topIndex = new Dictionary<HitObject, int>(ReferenceEqualityComparer.Instance);
            for (int i = 0; i < playable.HitObjects.Count; i++)
                topIndex[playable.HitObjects[i]] = i;
            ow = new Utf8JsonWriter(objects);
            ow.WriteStartArray();
        }

        private int sliderSamples;

        // ORACLE_DHO_STATES=1 (with --dump-env): per step, every alive top-level DHO's and slider head's transformable state
        // (Position, Scale, Rotation, Alpha, State, IsPresent, pooled instance id) -> "dho_states" (sim model M7 debugging).
        private readonly bool dhoStates = Environment.GetEnvironmentVariable("ORACLE_DHO_STATES") == "1";
        private int probeCount2;
        private readonly MemoryStream dhoStream = new MemoryStream();
        private Utf8JsonWriter? dw;

        // ORACLE_DHO_STATES=1: the HitObjectContainer's ancestor chain (computeDrawInfo inputs, root first) at the first
        // probe and once in steady state -> "hoc_chain" (BarrelRoll needs to recompose it with a rotated container).
        private readonly List<(double, string)> chains = new List<(double, string)>();

        private string chainJson(osu.Framework.Graphics.Drawable hoc)
        {
            var list = new List<osu.Framework.Graphics.Drawable>();
            for (var d = hoc; d != null; d = d.Parent) list.Add(d);
            list.Reverse();
            using var ms = new MemoryStream();
            using (var w = new Utf8JsonWriter(ms))
            {
                w.WriteStartArray();
                foreach (var d in list)
                {
                    var pos = d.DrawPosition + d.AnchorPosition;
                    if (d.Parent != null) pos += d.Parent.ChildOffset;
                    w.WriteStartObject();
                    w.WriteString("type", d.GetType().Name);
                    w.WriteStartArray("pos"); w.WriteStringValue(Dump.F(pos.X)); w.WriteStringValue(Dump.F(pos.Y)); w.WriteEndArray();
                    var ds = (Vector2)typeof(osu.Framework.Graphics.Drawable).GetProperty("DrawScale", BindingFlags.NonPublic | BindingFlags.Instance)!.GetValue(d)!;
                    w.WriteStartArray("scale"); w.WriteStringValue(Dump.F(ds.X)); w.WriteStringValue(Dump.F(ds.Y)); w.WriteEndArray();
                    w.WriteString("rotation", Dump.F(d.Rotation));
                    w.WriteStartArray("shear"); w.WriteStringValue(Dump.F(d.Shear.X)); w.WriteStringValue(Dump.F(d.Shear.Y)); w.WriteEndArray();
                    w.WriteStartArray("origin"); w.WriteStringValue(Dump.F(d.OriginPosition.X)); w.WriteStringValue(Dump.F(d.OriginPosition.Y)); w.WriteEndArray();
                    w.WriteStartArray("draw_size"); w.WriteStringValue(Dump.F(d.DrawSize.X)); w.WriteStringValue(Dump.F(d.DrawSize.Y)); w.WriteEndArray();
                    Dump.WriteMatrix(w, "matrix", d.DrawInfo.Matrix);
                    w.WriteEndObject();
                }
                w.WriteEndArray();
            }
            return System.Text.Encoding.UTF8.GetString(ms.ToArray());
        }

        private void writeDho(DrawableHitObject d, string kind, int i)
        {
            dw!.WriteStartArray();
            dw.WriteNumberValue(i);
            dw.WriteStringValue(kind);
            dw.WriteNumberValue(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(d));
            dw.WriteStringValue(Dump.F(d.Position.X));
            dw.WriteStringValue(Dump.F(d.Position.Y));
            dw.WriteStringValue(Dump.F(d.Scale.X));
            dw.WriteStringValue(Dump.F(d.Scale.Y));
            dw.WriteStringValue(Dump.F(d.Rotation));
            dw.WriteStringValue(Dump.F(d.Alpha));
            dw.WriteStringValue(d.State.Value.ToString());
            dw.WriteBooleanValue(d.IsPresent);
            dw.WriteBooleanValue(d.IsAlive);
            if (d is DrawableSlider ds)
            {
                dw.WriteStringValue(Dump.F(ds.Size.X));
                dw.WriteStringValue(Dump.F(ds.Size.Y));
                dw.WriteStringValue(Dump.F(ds.OriginPosition.X));
                dw.WriteStringValue(Dump.F(ds.OriginPosition.Y));
            }
            if (d is DrawableSpinner dsp)
            {
                dw.WriteBooleanValue(dsp.RotationTracker.Tracking);
                dw.WriteStringValue(Dump.F(dsp.Result.TotalRotation));
            }
            dw.WriteEndArray();
        }

        private string stage = "";
        private bool treePrinted;
        private int probeCount;

        public void Probe(double time)
        {
            try
            {
                probe(time);
            }
            catch (Exception e)
            {
                throw new InvalidOperationException("env probe failed at stage " + stage, e);
            }
        }

        private void probe(double time)
        {
            stage = "start";
            if (drawableRuleset == null) throw new InvalidOperationException("probe: drawableRuleset null");
            var playfield = drawableRuleset.Playfield;
            if (playfield == null) throw new InvalidOperationException("probe: playfield null");
            var hoc = playfield.HitObjectContainer;
            if (hoc == null) throw new InvalidOperationException("probe: hoc null");
            var di = hoc.DrawInfo;

            if (hocMatrix == null)
            {
                hocMatrix = di.Matrix;
                hocInverse = di.MatrixInverse;
            }
            else if (!hocMatrix.Value.Equals(di.Matrix) || !hocInverse.Value.Equals(di.MatrixInverse))
            {
                hocChanged = true;
                hocHistory.Add((time, hocMatrix.Value, hocInverse!.Value));
                hocMatrix = di.Matrix;
                hocInverse = di.MatrixInverse;
            }

            if (Environment.GetEnvironmentVariable("ORACLE_DEBUG_TREE") == "1" && !treePrinted && ++probeCount > 100)
            {
                treePrinted = true;
                osu.Framework.Graphics.Drawable? d = hoc;
                while (d != null)
                {
                    var m = d.DrawInfo.Matrix;
                    Console.Error.WriteLine($"[tree] {d.GetType().FullName} pos={d.Position} scale={d.Scale} size={d.DrawSize} M11={m.M11} M22={m.M22} M31={m.M31} M32={m.M32}");
                    d = d.Parent;
                }
            }
            stage = "im";
            var im = (osu.Framework.Input.InputManager)drawableRuleset.GetType().GetProperty("KeyBindingInputManager", BindingFlags.NonPublic | BindingFlags.Instance)!.GetValue(drawableRuleset)!;
            mouse.Add((time, im.CurrentState.Mouse.Position, im.CurrentState.Mouse.IsPositionValid));

            if (dhoStates && (chains.Count == 0 || (chains.Count == 1 && probeCount2 == 100)))
                chains.Add((time, chainJson(hoc)));
            probeCount2++;

            if (dhoStates)
            {
                dw ??= new Utf8JsonWriter(dhoStream);
                if (dhoStream.Length == 0 && dw.BytesPending == 0) dw.WriteStartArray();
                dw.WriteStartArray();
                dw.WriteStringValue(Dump.D(time));
                foreach (var m in drawableRuleset.Mods)
                {
                    var thetaField = m.GetType().GetField("theta", BindingFlags.NonPublic | BindingFlags.Instance);
                    if (thetaField != null) dw.WriteStringValue("theta:" + Dump.F((float)thetaField.GetValue(m)!));
                }
                foreach (var dho in hoc.AliveObjects)
                {
                    if (!dho.IsLoaded) continue;
                    int ti = topIndex[dho.HitObject];
                    writeDho(dho, dho is DrawableSlider ? "slider" : dho is DrawableSpinner ? "spinner" : "circle", ti);
                    if (dho is DrawableSlider s2 && s2.HeadCircle != null)
                        writeDho(s2.HeadCircle, "head", ti);
                }
                dw.WriteEndArray();
            }

            stage = "alive";
            foreach (var dho in hoc.AliveObjects)
            {
                if (!dho.IsLoaded) continue;
                stage = "obj " + dho.GetType().Name;

                bool first = probed.Add(dho.HitObject);

                switch (dho)
                {
                    case DrawableSlider ds:
                        if (first || (ds.HeadCircle.Judged && !ds.AllJudged && sliderSamples < maxSliderSamples))
                        {
                            sliderSamples++;
                            ow.WriteStartObject();
                            ow.WriteNumber("i", topIndex[dho.HitObject]);
                            ow.WriteString("kind", "slider");
                            ow.WriteString("time", Dump.D(time));
                            Dump.WriteMatrix(ow, "matrix", ds.DrawInfo.Matrix);
                            Dump.WriteMatrix(ow, "inverse", ds.DrawInfo.MatrixInverse);
                            ow.WriteStartArray("origin");
                            ow.WriteStringValue(Dump.F(ds.OriginPosition.X));
                            ow.WriteStringValue(Dump.F(ds.OriginPosition.Y));
                            ow.WriteEndArray();
                            ow.WriteStartArray("draw_size");
                            ow.WriteStringValue(Dump.F(ds.DrawSize.X));
                            ow.WriteStringValue(Dump.F(ds.DrawSize.Y));
                            ow.WriteEndArray();
                            if (ds.SliderBody != null)
                                ow.WriteString("path_radius", Dump.F(ds.SliderBody.PathRadius));
                            var hr = ds.HeadCircle.HitArea;
                            Dump.WriteMatrix(ow, "head_receptor_matrix", hr.DrawInfo.Matrix);
                            Dump.WriteMatrix(ow, "head_receptor_inverse", hr.DrawInfo.MatrixInverse);
                            ow.WriteEndObject();
                        }

                        break;

                    case DrawableHitCircle dc when first:
                        ow.WriteStartObject();
                        ow.WriteNumber("i", topIndex[dho.HitObject]);
                        ow.WriteString("kind", "circle");
                        ow.WriteString("time", Dump.D(time));
                        Dump.WriteMatrix(ow, "receptor_matrix", dc.HitArea.DrawInfo.Matrix);
                        Dump.WriteMatrix(ow, "receptor_inverse", dc.HitArea.DrawInfo.MatrixInverse);
                        ow.WriteEndObject();
                        break;

                    case DrawableSpinner dsp when first:
                        ow.WriteStartObject();
                        ow.WriteNumber("i", topIndex[dho.HitObject]);
                        ow.WriteString("kind", "spinner");
                        ow.WriteString("time", Dump.D(time));
                        Dump.WriteMatrix(ow, "matrix", dsp.DrawInfo.Matrix);
                        Dump.WriteMatrix(ow, "inverse", dsp.DrawInfo.MatrixInverse);
                        ow.WriteStartArray("draw_size");
                        ow.WriteStringValue(Dump.F(dsp.DrawSize.X));
                        ow.WriteStringValue(Dump.F(dsp.DrawSize.Y));
                        ow.WriteEndArray();
                        ow.WriteEndObject();
                        break;
                }
            }
        }

        public void Write(string path)
        {
            ow.WriteEndArray();
            ow.Flush();

            using var fs = File.Create(path);
            using var w = new Utf8JsonWriter(fs);
            w.WriteStartObject();
            w.WriteString("format", "env-1");
            if (hocMatrix != null)
            {
                Dump.WriteMatrix(w, "hit_object_container_matrix", hocMatrix.Value);
                Dump.WriteMatrix(w, "hit_object_container_inverse", hocInverse!.Value);
            }
            w.WriteBoolean("hit_object_container_changed", hocChanged);
            // earlier matrices (superseded at the given step time); the final ones are above.
            w.WriteStartArray("hit_object_container_history");
            foreach (var (t, m, mi) in hocHistory)
            {
                w.WriteStartObject();
                w.WriteString("until", Dump.D(t));
                Dump.WriteMatrix(w, "matrix", m);
                Dump.WriteMatrix(w, "inverse", mi);
                w.WriteEndObject();
            }
            w.WriteEndArray();
            var hoc = drawableRuleset.Playfield.HitObjectContainer;
            w.WriteStartArray("hit_object_container_draw_size");
            w.WriteStringValue(Dump.F(hoc.DrawSize.X));
            w.WriteStringValue(Dump.F(hoc.DrawSize.Y));
            w.WriteEndArray();
            w.WritePropertyName("objects");
            w.WriteRawValue(objects.ToArray(), skipInputValidation: true);
            if (dw != null)
            {
                dw.WriteEndArray();
                dw.Flush();
                w.WritePropertyName("dho_states");
                w.WriteRawValue(dhoStream.ToArray(), skipInputValidation: true);
                w.WriteStartArray("hoc_chain");
                foreach (var (t, c) in chains)
                {
                    w.WriteStartObject();
                    w.WriteString("time", Dump.D(t));
                    w.WritePropertyName("chain");
                    w.WriteRawValue(c, skipInputValidation: true);
                    w.WriteEndObject();
                }
                w.WriteEndArray();
            }
            // mouse position at the start of step k = position applied by the input manager in step k-1.
            w.WriteStartArray("mouse");
            foreach (var (t, p, valid) in mouse)
            {
                w.WriteStartArray();
                w.WriteStringValue(Dump.D(t));
                w.WriteStringValue(valid ? Dump.F(p.X) : "invalid");
                w.WriteStringValue(valid ? Dump.F(p.Y) : "invalid");
                w.WriteEndArray();
            }
            w.WriteEndArray();
            w.WriteEndObject();
        }
    }
}
