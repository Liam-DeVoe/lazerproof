// Reference-clock schedules (DECISIONS.md D9) and an independent re-implementation of the FrameStabilityContainer +
// FramedReplayInputHandler stepping rule, used to verify that the recorded step sequence is exactly the function of the
// reference sequence we claim it is.

using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;

namespace Oracle
{
    public interface IReferenceSchedule
    {
        double First();
        bool TryNext(out double next);
    }

    public enum ScheduleKind
    {
        Catchup,
        PerFrame,
        Dense1ms,
        Explicit,
    }

    public class ScheduleSpec
    {
        public ScheduleKind Kind = ScheduleKind.Catchup;
        public List<double>? ExplicitTimes;
        public string? ExplicitFile;

        public string Name => Kind switch
        {
            ScheduleKind.Catchup => "catchup",
            ScheduleKind.PerFrame => "perframe",
            ScheduleKind.Dense1ms => "dense1ms",
            _ => "explicit:" + ExplicitFile,
        };

        public static ScheduleSpec Parse(string s)
        {
            if (s == "catchup") return new ScheduleSpec { Kind = ScheduleKind.Catchup };
            if (s == "perframe") return new ScheduleSpec { Kind = ScheduleKind.PerFrame };
            if (s == "dense1ms") return new ScheduleSpec { Kind = ScheduleKind.Dense1ms };

            if (s.StartsWith("explicit:", StringComparison.Ordinal))
            {
                string file = s.Substring("explicit:".Length);
                var times = File.ReadAllLines(file)
                                .Select(l => l.Trim())
                                .Where(l => l.Length > 0 && !l.StartsWith('#'))
                                .Select(l => double.Parse(l, NumberStyles.Float, CultureInfo.InvariantCulture))
                                .ToList();
                if (times.Count == 0) throw new ArgumentException("explicit schedule is empty");
                for (int i = 1; i < times.Count; i++)
                    if (times[i] < times[i - 1])
                        throw new ArgumentException($"explicit schedule must be non-decreasing (line {i + 1})");
                return new ScheduleSpec { Kind = ScheduleKind.Explicit, ExplicitTimes = times, ExplicitFile = file };
            }

            throw new ArgumentException("unknown schedule: " + s);
        }

        public IReferenceSchedule Create(double r0, double end, IReadOnlyList<double> frameTimes)
        {
            switch (Kind)
            {
                case ScheduleKind.Catchup:
                    return new ListSchedule(new[] { r0, Math.Max(r0, end) });

                case ScheduleKind.PerFrame:
                {
                    var l = new List<double> { r0 };
                    foreach (double f in frameTimes)
                        if (f > l[^1]) l.Add(f);
                    if (end > l[^1]) l.Add(end);
                    return new ListSchedule(l);
                }

                case ScheduleKind.Dense1ms:
                    return new DenseSchedule(r0, end);

                default:
                    return new ListSchedule(ExplicitTimes!);
            }
        }
    }

    public class ListSchedule : IReferenceSchedule
    {
        private readonly IReadOnlyList<double> times;
        private int i;

        public ListSchedule(IReadOnlyList<double> times) => this.times = times;

        public double First() => times[i = 0];

        public bool TryNext(out double next)
        {
            if (i + 1 >= times.Count)
            {
                next = 0;
                return false;
            }

            next = times[++i];
            return true;
        }
    }

    /// <summary>r0, then every integer millisecond after r0, up to and including the first integer >= end.</summary>
    public class DenseSchedule : IReferenceSchedule
    {
        private readonly double r0, end;
        private double cur;

        public DenseSchedule(double r0, double end)
        {
            this.r0 = r0;
            this.end = end;
        }

        public double First() => cur = r0;

        public bool TryNext(out double next)
        {
            if (cur >= end)
            {
                next = 0;
                return false;
            }

            next = cur = Math.Floor(cur) + 1;
            return true;
        }
    }

    public static class StepSimulator
    {
        private const double sixty_frame_time = 1000.0 / 60;

        /// <summary>
        /// Expected FSC step times for a given sequence of reference times (each reference is held until the FSC reaches it,
        /// with at least one step per reference). Mirrors FrameStabilityContainer.updateClock/applyFrameStability and
        /// FramedReplayInputHandler.SetFrameFromTime (FrameAccuratePlayback off, all frames received).
        /// </summary>
        public static List<double> Simulate(IReadOnlyList<double> references, IReadOnlyList<double> frames, double gameplayStartTime)
        {
            var steps = new List<double>();
            bool first = true;
            double manual = 0;
            int idx = -1;
            double handlerTime = double.NegativeInfinity;

            double frameTime(int i) => i < 0 ? double.NegativeInfinity : i >= frames.Count ? double.PositiveInfinity : frames[i];

            foreach (double r in references)
            {
                while (true)
                {
                    double proposed = r;

                    if (first)
                    {
                        manual = proposed;
                        first = false;
                    }
                    else if (manual < gameplayStartTime)
                        manual = proposed = Math.Min(gameplayStartTime, proposed);
                    else if (Math.Abs(manual - proposed) > sixty_frame_time * 1.2f)
                    {
                        proposed = proposed > manual
                            ? Math.Min(proposed, manual + sixty_frame_time)
                            : Math.Max(proposed, manual - sixty_frame_time);
                    }

                    if (frames.Count == 0)
                        handlerTime = proposed;
                    else
                    {
                        double fs = frameTime(idx), fe = frameTime(idx + 1);

                        if (fe <= proposed)
                        {
                            proposed = fe;
                            idx++;
                        }
                        else if (proposed < fs && handlerTime == fs)
                            idx--;

                        fs = frameTime(idx);
                        fe = frameTime(idx + 1);
                        handlerTime = Math.Clamp(proposed, fs, fe);
                    }

                    proposed = handlerTime;
                    manual = proposed;
                    steps.Add(manual);

                    if (proposed == r)
                        break;
                }
            }

            return steps;
        }
    }
}
