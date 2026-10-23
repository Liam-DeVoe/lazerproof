// Validation mode: run lazer's real ReplayPlayer (real-time virtual track, as a user watching the replay would) and record
// its frame-stable step times and judgements. Feeding the recorded step times back as an explicit reference schedule to the
// oracle must reproduce the judgements exactly (see README "Validation against the real ReplayPlayer").

using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Text.Json;
using osu.Framework.Allocation;
using osu.Framework.Graphics;
using osu.Framework.Screens;
using osu.Game.Beatmaps;
using osu.Game.Configuration;
using osu.Game.Graphics.Containers;
using osu.Game.Overlays;
using osu.Game.Rulesets.Judgements;
using osu.Game.Rulesets.Mods;
using osu.Game.Rulesets.Objects;
using osu.Game.Scoring;
using osu.Game.Screens;
using osu.Game.Screens.Play;

namespace Oracle
{
    public partial class RecordingReplayPlayer : ReplayPlayer
    {
        public readonly StepRecorder Recorder = new StepRecorder();
        public readonly List<JudgementRecord> Records = new List<JudgementRecord>();
        public bool Done;

        private static readonly System.Reflection.PropertyInfo raw_time =
            typeof(JudgementResult).GetProperty("RawTime", System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic)!;

        public RecordingReplayPlayer(Score score)
            : base(score, new PlayerConfiguration { AllowUserInteraction = false, ShowResults = false, AllowRestart = false })
        {
        }

        public ScoreProcessor_ Processors => new ScoreProcessor_(ScoreProcessor, HealthProcessor);

        public record ScoreProcessor_(osu.Game.Rulesets.Scoring.ScoreProcessor Score, osu.Game.Rulesets.Scoring.HealthProcessor Health);

        protected override void LoadComplete()
        {
            base.LoadComplete();

            Recorder.RefTime = () => GameplayClockContainer.CurrentTime;
            DrawableRuleset.FrameStableComponents.Add(Recorder);

            DrawableRuleset.NewResult += r => Records.Add(new JudgementRecord
            {
                Top = -1,
                Nested = -1,
                TypeName = r.HitObject.GetType().Name,
                Result = r.Type,
                RawTime = (double?)raw_time.GetValue(r) ?? double.NaN,
                TimeOffset = r.TimeOffset,
                ComboAfter = r.ComboAfterJudgement,
                HealthAfter = HealthProcessor.Health.Value,
                FailedAtJudgement = r.FailedAtJudgement,
            });
        }

        public IBeatmap Playable => GameplayState.Beatmap;
        public double GameplayClockTime => GameplayClockContainer.CurrentTime;
        public double TrueRate => GameplayClockContainer.GetTrueGameplayRate();
        public double FrameStableTime => DrawableRuleset.FrameStableClock.CurrentTime;
    }

    public class PlayerRunner : IOracleRunner
    {
        private readonly Job job;
        private readonly Options options;
        private readonly Stream stdout;
        private OracleGame game = null!;
        private RecordingReplayPlayer? player;
        private OsuScreenStack stack = null!;
        private double endTime;
        public bool Failed;

        public PlayerRunner(Job job, Options options, Stream stdout)
        {
            this.job = job;
            this.options = options;
            this.stdout = stdout;
        }

        public bool OnUnhandledException(Exception ex)
        {
            Console.Error.WriteLine("[player] unhandled: " + ex);
            Failed = true;
            return false;
        }

        public void Start(OracleGame game)
        {
            this.game = game;
            var ruleset = game.GetRulesetStore().GetRuleset("osu")!.CreateInstance();
            var (working, score, _, _) = JobRunner.Decode(job, ruleset, game.Audio);

            var mods = JobRunner.ResolveMods(job, options, score, ruleset, new List<string>());

            game.Add(new ScalingContainer(ScalingMode.Everything)
            {
                Child = stack = new OsuScreenStack { RelativeSizeAxes = Axes.Both }
            });

            game.SetGameplayBindables(working, ruleset.RulesetInfo, mods);

            double maxEnd = working.Beatmap.HitObjects.Max(h => h.GetEndTime());
            endTime = maxEnd + 1000;

            player = new RecordingReplayPlayer(score);
            stack.Push(player);
            game.OnUpdate += _ => poll();
        }

        private bool emitted;

        // oracle_fail (D80c): after a genuine fail, ReplayFailIndicator ramps the track frequency to 0 over 1000 ms of
        // gameplay time, so the gameplay clock approaches failTime + 1000 only geometrically and then stalls (no
        // double-precision progress), and FrameStableTime never reaches endTime. Once the play has failed we emit when
        // the frame-stable clock has not advanced for STALL_POLLS consecutive host updates (or when endTime is reached).
        private const int stall_polls = 120;
        private const int fail_poll_cap = 200000;
        private static readonly bool trace = Environment.GetEnvironmentVariable("ORACLE_FAIL_TRACE") == "1";
        private double? failSeenAt;
        private int failSeenSteps;
        private int pollsSinceFail, stallCount;
        private double lastFst = double.NaN;
        private string exitReason = "end";

        private bool hasFailed => player!.GameplayState.HasFailed || player.Processors.Health.HasFailed;

        private void poll()
        {
            if (emitted || player == null || !player.IsLoaded) return;

            double fst = player.FrameStableTime;
            bool failedNow = hasFailed;

            if (failedNow && failSeenAt == null)
            {
                failSeenAt = fst;
                failSeenSteps = player.Recorder.Steps.Count();
            }

            if (failedNow)
            {
                pollsSinceFail++;
                stallCount = fst == lastFst ? stallCount + 1 : 0;
                if (trace && (pollsSinceFail <= 40 || pollsSinceFail % 100 == 0))
                    Console.Error.WriteLine(FormattableString.Invariant(
                        $"[fail-trace] poll {pollsSinceFail} fst={fst:R} gct={player.GameplayClockTime:R} rate={player.TrueRate:R} d={fst - lastFst:R} steps={player.Recorder.Steps.Count()} stall={stallCount}"));
            }

            lastFst = fst;

            if (fst < endTime)
            {
                if (!failedNow) return;
                if (stallCount >= stall_polls) exitReason = "fail_stall";
                else if (pollsSinceFail >= fail_poll_cap) exitReason = "fail_cap";
                else return;
            }

            emitted = true;

            var steps = player.Recorder.Steps.ToList();
            var ms = new MemoryStream();

            using (var w = new Utf8JsonWriter(ms))
            {
                w.WriteStartObject();
                w.WriteString("mode", "replay_player_realtime");
                w.WriteString("beatmap", job.Beatmap);
                w.WriteString("replay", job.Replay);
                w.WriteBoolean("failed", player.GameplayState.HasFailed || player.Processors.Health.HasFailed);
                w.WriteString("exit", exitReason);
                if (failSeenAt is double fsa)
                {
                    w.WritePropertyName("fail_seen_fst");
                    w.WriteRawValue(fsa.ToString("R", CultureInfo.InvariantCulture));
                    w.WriteNumber("fail_seen_steps", failSeenSteps);
                    w.WriteNumber("polls_since_fail", pollsSinceFail);
                }
                w.WritePropertyName("final_fst");
                w.WriteRawValue(player.FrameStableTime.ToString("R", CultureInfo.InvariantCulture));
                w.WriteNumber("record_count", player.Records.Count);
                var si = new ScoreInfo { Ruleset = player.GameplayState.Ruleset.RulesetInfo, BeatmapInfo = player.GameplayState.Beatmap.BeatmapInfo, Mods = player.GameplayState.Mods.ToArray() };
                player.Processors.Score.PopulateScore(si);
                w.WriteString("rank", si.Rank.ToString());
                w.WriteNumber("total_score", si.TotalScore);
                w.WriteNumber("max_combo", si.MaxCombo);
                w.WritePropertyName("accuracy");
                w.WriteRawValue(si.Accuracy.ToString("R", CultureInfo.InvariantCulture));
                w.WriteStartObject("statistics");
                foreach (var kv in si.Statistics.Where(kv => kv.Value != 0).OrderBy(kv => (int)kv.Key))
                    w.WriteNumber(kv.Key.ToString(), kv.Value);
                w.WriteEndObject();
                w.WriteStartArray("judgements");

                foreach (var j in player.Records)
                {
                    w.WriteStartObject();
                    w.WriteString("type", j.TypeName);
                    w.WriteString("result", j.Result.ToString());
                    w.WritePropertyName("time");
                    w.WriteRawValue(j.RawTime.ToString("R", CultureInfo.InvariantCulture));
                    w.WriteNumber("combo", j.ComboAfter);
                    w.WritePropertyName("health");
                    w.WriteRawValue(j.HealthAfter.ToString("R", CultureInfo.InvariantCulture));
                    w.WriteEndObject();
                }

                w.WriteEndArray();
                w.WriteStartArray("steps");
                foreach (double d in steps)
                    w.WriteRawValue(d.ToString("R", CultureInfo.InvariantCulture));
                w.WriteEndArray();
                w.WriteEndObject();
            }

            stdout.Write(ms.ToArray());
            stdout.WriteByte((byte)'\n');
            stdout.Flush();

            // oracle_fail (D80c): ORACLE_FAIL_REFS_OUT=FILE writes the host-frame reference times (distinct consecutive
            // GameplayClockContainer.CurrentTime values seen at the frame-stable steps), usable as an explicit schedule.
            string? refsOut = Environment.GetEnvironmentVariable("ORACLE_FAIL_REFS_OUT");
            if (refsOut != null)
            {
                var refs = new List<double>();
                foreach (double r in player.Recorder.RefSteps)
                    if (refs.Count == 0 || r != refs[^1]) refs.Add(r);
                File.WriteAllLines(refsOut, refs.Select(d => d.ToString("R", CultureInfo.InvariantCulture)));
            }

            if (options.StepsOut != null)
                File.WriteAllLines(options.StepsOut, steps.Select(d => d.ToString("R", CultureInfo.InvariantCulture)));

            game.Exit();
        }
    }
}
