// Reproduction of Player.load / Player.LoadComplete / Player.OnEntering wiring (osu.Game/Screens/Play/Player.cs at the pinned
// commit) around a DrawableRuleset, plus an owned reference IGameplayClock driven by an explicit reference-time schedule.

using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using osu.Framework.Allocation;
using osu.Framework.Audio;
using osu.Framework.Bindables;
using osu.Framework.Graphics;
using osu.Framework.Graphics.Containers;
using osu.Game.Beatmaps;
using osu.Game.Configuration;
using osu.Game.Graphics.Containers;
using osu.Game.Rulesets;
using osu.Game.Rulesets.Judgements;
using osu.Game.Rulesets.Mods;
using osu.Game.Rulesets.Objects;
using osu.Game.Rulesets.Scoring;
using osu.Game.Rulesets.UI;
using osu.Game.Scoring;
using osu.Game.Screens.Play;
using osu.Game.Skinning;

namespace Oracle
{
    public enum FailSemantics
    {
        /// <summary>Player: fail freezes the score at the failing judgement (subject to IApplicableFailOverride.PerformFail).</summary>
        Live,

        /// <summary>ReplayPlayer: failing suppressed until (frame-stable) time &gt;= last replay frame time.</summary>
        ReplayPlayer,
    }

    public class RunSpec
    {
        public required WorkingBeatmap Working;
        public required Score Score;
        public required Ruleset Ruleset;
        public required Mod[] Mods;
        public required ScheduleSpec Schedule;
        public required FailSemantics Semantics;
        public string? DumpPlayablePath;
        public string? DumpEnvPath;
    }

    public struct JudgementRecord
    {
        public int Top;
        public int Nested;
        public string TypeName;
        public HitResult Result;
        public double RawTime;
        public double TimeOffset;
        public int ComboAfter;
        public double HealthAfter;
        public bool FailedAtJudgement;
        public double? GameplayRate;
    }

    public class RunResult
    {
        public required FailSemantics Semantics;
        public bool Failed;
        public double? FailTime;
        public int FailTriggerCount;
        public required ScoreInfo Score;
        public bool Completed;
        public double FinalHealth;
        public required List<JudgementRecord> Judgements;
        public required List<double> Steps;
        public required List<double> References;
        public long HostFrames;
        public double RunMs;
        public double R0;
        public double End;
        public double GameplayStartTime;
        public double? LastFrameTime;
        public double TrueGameplayRateAtStart;
        public required Dictionary<string, string> Environment;
        public required IBeatmap Playable;
        public required Mod[] GameplayMods;
    }

    /// <summary>
    /// Records the time of every frame-stable step (one Update per FrameStabilityContainer sub-frame).
    /// Appended as the last FrameStableComponent so it runs after the score/health processors and break tracker.
    /// </summary>
    public partial class StepRecorder : Component
    {
        public readonly List<double> Steps = new List<double>();
        public EnvProbe? Probe;

        protected override void Update()
        {
            base.Update();
            Probe?.Probe(Clock.CurrentTime);
            Steps.Add(Clock.CurrentTime);
        }
    }

    /// <summary>
    /// Stand-in for Player, only so that IApplicableToPlayer mods can be applied. Never loaded or added to the tree.
    /// OsuModRelax / ModEasyWithExtraLives ignore the argument; Bloom / NoScope bind IsBreakTime (visual only).
    /// </summary>
    public partial class StubPlayer : Player
    {
        protected override osu.Game.Screens.Ranking.ResultsScreen CreateResults(ScoreInfo score) => throw new NotSupportedException();
    }

    /// <summary>
    /// Plays the roles of Player (dependencies, wiring) and GameplayClockContainer (reference IGameplayClock).
    /// </summary>
    [Cached(typeof(IGameplayClock))]
    public partial class OracleGameplay : Container, IGameplayClock, osu.Game.Audio.ISamplePlaybackDisabler
    {
        private static readonly Func<JudgementResult, double?> get_raw_time = (Func<JudgementResult, double?>)typeof(JudgementResult)
                                                                                .GetProperty("RawTime", BindingFlags.Instance | BindingFlags.NonPublic)!
                                                                                .GetGetMethod(true)!
                                                                                .CreateDelegate(typeof(Func<JudgementResult, double?>));

        private readonly RunSpec spec;
        public Action<RunResult>? Completed;

        private DependencyContainer dependencies = null!;

        public DrawableRuleset DrawableRuleset { get; private set; } = null!;
        public ScoreProcessor ScoreProcessor { get; private set; } = null!;
        public HealthProcessor HealthProcessor { get; private set; } = null!;
        public GameplayState GameplayState { get; private set; } = null!;

        private Mod[] gameplayMods = null!;
        private IBeatmap playable = null!;
        private BreakTracker breakTracker = null!;
        private readonly StepRecorder recorder = new StepRecorder();
        private readonly List<JudgementRecord> judgements = new List<JudgementRecord>();
        private Dictionary<HitObject, (int top, int nested)> indexOf = null!;

        private double? lastFrameTime;
        private bool failed;
        private double? failTime;
        private int failTriggers;

        private IReferenceSchedule schedule = null!;
        private bool referenceInitialised;
        private bool finished;
        private long hostFrames;
        private readonly List<double> references = new List<double>();
        private double r0, end;
        private double trueRateAtStart;
        private readonly Dictionary<string, string> environment = new Dictionary<string, string>();

        public OracleGameplay(RunSpec spec)
        {
            this.spec = spec;
            RelativeSizeAxes = Axes.Both;
        }

        protected override IReadOnlyDependencyContainer CreateChildDependencies(IReadOnlyDependencyContainer parent)
            => dependencies = new DependencyContainer(base.CreateChildDependencies(parent));

        [BackgroundDependencyLoader]
        private void load(OsuConfigManager config, IRulesetConfigCache rulesetConfigCache, SkinManager skinManager)
        {
            environment["skin"] = skinManager.CurrentSkinInfo.Value.ToString() ?? "";
            if (rulesetConfigCache.GetConfigFor(spec.Ruleset) is osu.Game.Rulesets.Osu.Configuration.OsuRulesetConfigManager rc)
            {
                environment["snaking_in_sliders"] = rc.Get<bool>(osu.Game.Rulesets.Osu.Configuration.OsuRulesetSetting.SnakingInSliders).ToString();
                environment["snaking_out_sliders"] = rc.Get<bool>(osu.Game.Rulesets.Osu.Configuration.OsuRulesetSetting.SnakingOutSliders).ToString();
            }

            var ruleset = spec.Ruleset;
            var working = spec.Working;

            // Player.load
            gameplayMods = spec.Mods.Select(m => m.DeepClone()).ToArray();

            if (gameplayMods.Any(m => m is UnknownMod))
                throw new InvalidOperationException("unknown mod");

            playable = working.GetPlayableBeatmap(ruleset.RulesetInfo, gameplayMods);

            if (spec.DumpPlayablePath != null)
                Dump.WritePlayable(spec.DumpPlayablePath, playable, working);

            if (!osu.Game.Utils.ModUtils.CheckModsBelongToRuleset(ruleset, gameplayMods))
                throw new InvalidOperationException("mod from other ruleset");

            DrawableRuleset = ruleset.CreateDrawableRulesetWith(playable, gameplayMods);
            dependencies.CacheAs(DrawableRuleset);

            ScoreProcessor = ruleset.CreateScoreProcessor();
            ScoreProcessor.Mods.Value = gameplayMods;
            ScoreProcessor.ApplyBeatmap(playable);
            dependencies.CacheAs(ScoreProcessor);

            HealthProcessor = gameplayMods.OfType<IApplicableHealthProcessor>().FirstOrDefault()?.CreateHealthProcessor(playable.HitObjects[0].StartTime);
            HealthProcessor ??= ruleset.CreateHealthProcessor(playable.HitObjects[0].StartTime);
            HealthProcessor.ApplyBeatmap(playable);
            dependencies.CacheAs(HealthProcessor);

            GameplayStartTime = DrawableRuleset.GameplayStartTime;
            StartTime = findEarliestStartTime(GameplayStartTime, working.Beatmap);

            var score = spec.Score; // ReplayPlayer: CreateScore returns the replay score
            score.ScoreInfo.BeatmapInfo = working.BeatmapInfo;
            score.ScoreInfo.BeatmapHash = working.BeatmapInfo.Hash;
            score.ScoreInfo.Ruleset = ruleset.RulesetInfo;
            score.ScoreInfo.Mods = gameplayMods;

            dependencies.CacheAs(GameplayState = new GameplayState(playable, ruleset, gameplayMods, score, ScoreProcessor, HealthProcessor, working.Storyboard));

            var rulesetSkinProvider = new RulesetSkinProvidingContainer(ruleset, playable, working.Skin);
            config.BindWith(OsuSetting.BeatmapSkins, rulesetSkinProvider.BeatmapSkins);
            config.BindWith(OsuSetting.BeatmapColours, rulesetSkinProvider.BeatmapColours);
            config.BindWith(OsuSetting.BeatmapHitsounds, rulesetSkinProvider.BeatmapHitsounds);

            breakTracker = new BreakTracker(DrawableRuleset.GameplayStartTime, ScoreProcessor)
            {
                Breaks = working.Beatmap.Breaks
            };

            InternalChild = rulesetSkinProvider;

            // createGameplayComponents()
            rulesetSkinProvider.Add(new ScalingContainer(ScalingMode.Gameplay)
            {
                Children = new Drawable[]
                {
                    DrawableRuleset.With(r =>
                        r.FrameStableComponents.Children = new Drawable[]
                        {
                            ScoreProcessor,
                            HealthProcessor,
                            new ComboEffects(ScoreProcessor),
                            breakTracker,
                            recorder, // oracle addition (passive), last.
                        }),
                }
            });

            // Player.load: result wiring. Health first, then score (order matters).
            DrawableRuleset.NewResult += r =>
            {
                HealthProcessor.ApplyResult(r);
                ScoreProcessor.ApplyResult(r);
                GameplayState.ApplyResult(r);
            };

            DrawableRuleset.RevertResult += r =>
            {
                HealthProcessor.RevertResult(r);
                ScoreProcessor.RevertResult(r);
            };

            // oracle: record after the processors have seen the result.
            DrawableRuleset.NewResult += record;

            HealthProcessor.Failed += onFail;

            ScoreProcessor.OnLoadComplete += _ =>
            {
                foreach (var mod in gameplayMods.OfType<IApplicableToScoreProcessor>())
                    mod.ApplyToScoreProcessor(ScoreProcessor);
            };

            HealthProcessor.OnLoadComplete += _ =>
            {
                foreach (var mod in gameplayMods.OfType<IApplicableToHealthProcessor>())
                    mod.ApplyToHealthProcessor(HealthProcessor);
            };

            indexOf = new Dictionary<HitObject, (int, int)>(ReferenceEqualityComparer.Instance);

            for (int i = 0; i < playable.HitObjects.Count; i++)
            {
                var h = playable.HitObjects[i];
                indexOf[h] = (i, -1);
                int j = 0;
                foreach (var n in h.NestedHitObjects)
                    indexOf[n] = (i, j++);
            }
        }

        // MasterGameplayClockContainer.findEarliestStartTime, without storyboard events (storyboards are not loaded).
        private static double findEarliestStartTime(double gameplayStartTime, IBeatmap beatmap)
        {
            double time = Math.Min(0, gameplayStartTime);
            double firstHitObjectTime = beatmap.HitObjects.First().StartTime;
            if (beatmap.AudioLeadIn > 0)
                time = Math.Min(time, firstHitObjectTime - beatmap.AudioLeadIn);
            return time;
        }

        protected override void LoadComplete()
        {
            base.LoadComplete();

            // Player.LoadComplete -> ReplayPlayer.PrepareReplay
            DrawableRuleset.SetReplayScore(spec.Score);
            lastFrameTime = spec.Score.Replay.Frames.LastOrDefault()?.Time;

            // Player.OnEntering (fired from OnLoadComplete, i.e. after LoadComplete, before any child update)
            var stub = new StubPlayer();
            ((IBindable<bool>)stub.IsBreakTime).BindTo(breakTracker.IsBreakTime);

            foreach (var mod in GameplayState.Mods.OfType<IApplicableToPlayer>())
                mod.ApplyToPlayer(stub);

            foreach (var mod in GameplayState.Mods.OfType<IApplicableToTrack>())
                mod.ApplyToTrack(AdjustmentsFromMods);

            trueRateAtStart = this.GetTrueGameplayRate();

            if (spec.DumpEnvPath != null)
                recorder.Probe = new EnvProbe(DrawableRuleset, playable);

            double maxEnd = double.NegativeInfinity;
            foreach (var h in playable.HitObjects)
            {
                maxEnd = Math.Max(maxEnd, h.GetEndTime());
                foreach (var n in h.NestedHitObjects)
                    maxEnd = Math.Max(maxEnd, n.GetEndTime());
            }

            r0 = StartTime;
            end = maxEnd + 1000;
            schedule = spec.Schedule.Create(r0, end, spec.Score.Replay.Frames.Select(f => f.Time).ToList());
        }

        /// <summary>
        /// Driver. Runs once per host frame, before the DrawableRuleset (child) updates in that host frame.
        /// The reference time only advances once the FrameStabilityContainer has reached it, so the step sequence is a
        /// function of the reference sequence only (independent of the 10ms wall-clock catch-up budget).
        /// </summary>
        protected override void Update()
        {
            base.Update();

            if (finished)
                return;

            if (!referenceInitialised)
            {
                referenceInitialised = true;
                RunTimer.Start();
                referenceTime = schedule.First();
                references.Add(referenceTime);
                hostFrames++;
                return;
            }

            if (recorder.Steps.Count > 0 && DrawableRuleset.FrameStableClock.CurrentTime == referenceTime)
            {
                if (!schedule.TryNext(out double next))
                {
                    finish();
                    return;
                }

                if (next < referenceTime)
                    throw new InvalidOperationException($"reference schedule must be non-decreasing ({next} < {referenceTime})");

                elapsed = next - referenceTime;
                referenceTime = next;
                references.Add(referenceTime);
            }
            else
                elapsed = 0;

            hostFrames++;
        }

        // Once finished, no further frame-stable steps may run (our Update runs before the children's in the same host frame).
        protected override bool RequiresChildrenUpdate => !finished && base.RequiresChildrenUpdate;

        private void finish()
        {
            finished = true;
            RunTimer.Stop();

            if (spec.DumpEnvPath != null)
                recorder.Probe?.Write(spec.DumpEnvPath);

            var si = new ScoreInfo
            {
                Ruleset = spec.Ruleset.RulesetInfo,
                BeatmapInfo = spec.Working.BeatmapInfo,
                Mods = gameplayMods,
            };
            ScoreProcessor.PopulateScore(si);


            Completed?.Invoke(new RunResult
            {
                Semantics = spec.Semantics,
                Failed = failed,
                FailTime = failTime,
                FailTriggerCount = failTriggers,
                Score = si,
                Completed = ScoreProcessor.HasCompleted.Value,
                FinalHealth = HealthProcessor.Health.Value,
                Judgements = judgements,
                Steps = recorder.Steps.ToList(),
                References = references,
                HostFrames = hostFrames,
                RunMs = RunTimer.Elapsed.TotalMilliseconds,
                R0 = r0,
                End = end,
                GameplayStartTime = GameplayStartTime,
                LastFrameTime = lastFrameTime,
                TrueGameplayRateAtStart = trueRateAtStart,
                Environment = environment,
                Playable = playable,
                GameplayMods = gameplayMods,
            });
        }

        private void record(JudgementResult r)
        {
            (int top, int nested) = indexOf.TryGetValue(r.HitObject, out var ix) ? ix : (-1, -1);

            judgements.Add(new JudgementRecord
            {
                Top = top,
                Nested = nested,
                TypeName = r.HitObject.GetType().Name,
                Result = r.Type,
                RawTime = get_raw_time(r) ?? double.NaN,
                TimeOffset = r.TimeOffset,
                ComboAfter = r.ComboAfterJudgement,
                HealthAfter = HealthProcessor.Health.Value,
                FailedAtJudgement = r.FailedAtJudgement,
                GameplayRate = r.GameplayRate,
            });
        }

        private double currentGameplayTime => DrawableRuleset.FrameStableClock.CurrentTime;

        private bool onFail()
        {
            failTriggers++;

            if (spec.Semantics == FailSemantics.ReplayPlayer)
            {
                // ReplayPlayer.CheckModsAllowFailure (uses GameplayClockContainer.CurrentTime; we use the frame-stable time,
                // which is what the reference clock tracks in real-time playback).
                if (!(currentGameplayTime >= lastFrameTime))
                    return false;
            }

            // Player.CheckModsAllowFailure (note: All() short-circuits, in mod order)
            if (!GameplayState.Mods.OfType<IApplicableFailOverride>().All(m => m.PerformFail()))
                return false;

            failed = true;
            failTime = currentGameplayTime;

            if (spec.Semantics == FailSemantics.Live)
            {
                // Player.PerformFail
                GameplayState.HasFailed = true;
                Schedule(() => ScoreProcessor.FailScore(GameplayState.Score.ScoreInfo));
            }
            else
            {
                // ReplayPlayer.PerformFail
                ScoreProcessor.FailScore(GameplayState.Score.ScoreInfo);
            }

            return true;
        }

        /// <summary>
        /// Player implements ISamplePlaybackDisabler (disabling samples while catching up / paused). We disable samples
        /// permanently: audio has no influence on judgement, and skipping playback is a large speed-up.
        /// </summary>
        IBindable<bool> osu.Game.Audio.ISamplePlaybackDisabler.SamplePlaybackDisabled { get; } = new BindableBool(true);

        public readonly System.Diagnostics.Stopwatch RunTimer = new System.Diagnostics.Stopwatch();

        #region IGameplayClock (reference clock)

        private double referenceTime;
        private double elapsed;

        public double StartTime { get; private set; }

        public double GameplayStartTime { get; private set; }

        public IAdjustableAudioComponent AdjustmentsFromMods { get; } = new AudioAdjustments();

        public IBindable<bool> IsPaused { get; } = new BindableBool();

        public bool IsRewinding => false;

        public double CurrentTime => referenceTime;

        // Track.Rate = AggregateFrequency * AggregateTempo (user playback rate 1, no other track adjustments).
        public double Rate => AdjustmentsFromMods.AggregateFrequency.Value * AdjustmentsFromMods.AggregateTempo.Value;

        public bool IsRunning => true;

        public void ProcessFrame()
        {
        }

        public double ElapsedFrameTime => elapsed;

        public double FramesPerSecond => 0;

        #endregion
    }
}
