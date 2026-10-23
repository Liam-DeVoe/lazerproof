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

        private void poll()
        {
            if (emitted || player == null || !player.IsLoaded) return;

            if (player.FrameStableTime < endTime) return;

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

            if (options.StepsOut != null)
                File.WriteAllLines(options.StepsOut, steps.Select(d => d.ToString("R", CultureInfo.InvariantCulture)));

            game.Exit();
        }
    }
}
