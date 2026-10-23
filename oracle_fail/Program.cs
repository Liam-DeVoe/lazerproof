// oracle: ground-truth osu!(lazer) replay evaluator. See README.md.

using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using Newtonsoft.Json;
using osu.Framework.Logging;
using osu.Framework.Platform;
using osu.Game.Beatmaps;
using osu.Game.Beatmaps.Formats;
using osu.Game.Configuration;
using osu.Game.IO;
using osu.Game.Online.API;
using osu.Game.Rulesets;
using osu.Game.Rulesets.Mods;
using osu.Game.Rulesets.Osu.Configuration;
using osu.Game.Rulesets.Scoring;
using osu.Game.Scoring;
using osu.Game.Scoring.Legacy;
using osu.Game.Tests.Beatmaps;

namespace Oracle
{
    public class Options
    {
        public ScheduleSpec Schedule = new ScheduleSpec();
        public bool Trace;
        public bool NoClassic;
        public bool ReplaceMods;
        public bool NoJudgements;
        public bool Timing;
        public bool CheckSteps = true;
        public string? StepsOut;
        public string? DumpPlayable;
        public string? DumpEnv;
    }

    public interface IOracleRunner
    {
        void Start(OracleGame game);
        bool OnUnhandledException(Exception ex);
    }

    public class Job
    {
        public required string Beatmap;
        public required string Replay;
        public string? ModsJson;
        public int Index;
    }

    public class OracleScoreDecoder : LegacyScoreDecoder
    {
        private readonly Ruleset ruleset;
        private readonly WorkingBeatmap working;
        public string? ReplayBeatmapHash;

        public OracleScoreDecoder(Ruleset ruleset, WorkingBeatmap working)
        {
            this.ruleset = ruleset;
            this.working = working;
        }

        protected override Ruleset GetRuleset(int rulesetId)
        {
            if (rulesetId != 0)
                throw new InvalidOperationException($"only the osu! ruleset is supported (replay ruleset id {rulesetId})");
            return ruleset;
        }

        protected override WorkingBeatmap GetBeatmap(string md5Hash)
        {
            ReplayBeatmapHash = md5Hash;
            return working;
        }
    }

    public class JobRunner : IOracleRunner
    {
        private readonly Queue<Job> jobs;
        private readonly Options options;
        private readonly Stream stdout;
        private OracleGame game = null!;

        private Job? current;
        private OracleGameplay? currentGameplay;
        private Stopwatch jobTimer = new Stopwatch();
        public int Done, Errors;
        public readonly Stopwatch Total = new Stopwatch();

        public JobRunner(IEnumerable<Job> jobs, Options options, Stream stdout)
        {
            this.jobs = new Queue<Job>(jobs);
            this.options = options;
            this.stdout = stdout;
        }

        public void Start(OracleGame game)
        {
            this.game = game;
            Total.Start();
            game.Post(next);
        }

        public bool OnUnhandledException(Exception ex)
        {
            if (current == null)
                return false;

            emitError(current, ex);
            var g = currentGameplay;
            current = null;
            currentGameplay = null;
            game.Post(() =>
            {
                if (g != null && g.Parent != null)
                    game.RemoveGameplay(g);
                next();
            });
            return true;
        }

        private void next()
        {
            if (jobs.Count == 0)
            {
                Total.Stop();
                game.Exit();
                return;
            }

            var job = jobs.Dequeue();
            current = job;
            jobTimer.Restart();

            try
            {
                startJob(job);
            }
            catch (Exception ex)
            {
                emitError(job, ex);
                current = null;
                game.Post(next);
            }
        }

        private class JobState
        {
            public required Job Job;
            public required Ruleset Ruleset;
            public required string BeatmapMd5;
            public required string? ReplayBeatmapHash;
            public required bool IsLegacyScore;
            public required Mod[] DecodedMods;
            public required Mod[] Mods;
            public required List<string> Warnings;
            public required List<double> FrameTimes; // as seen by the replay handler (stable-sorted by time)
            public RunResult? Live;
            public RunResult? ReplayPlayer;
        }

        private (WorkingBeatmap working, Score score, string md5, string? replayBeatmapHash) decode(Job job, Ruleset ruleset) => Decode(job, ruleset);

        public static (WorkingBeatmap working, Score score, string md5, string? replayBeatmapHash) Decode(Job job, Ruleset ruleset, osu.Framework.Audio.AudioManager? audio = null)
        {
            byte[] osuBytes = File.ReadAllBytes(job.Beatmap);
            string md5 = Convert.ToHexStringLower(MD5.HashData(osuBytes));

            Beatmap beatmap;
            using (var ms = new MemoryStream(osuBytes))
            using (var reader = new LineBufferedReader(ms))
                beatmap = osu.Game.Beatmaps.Formats.Decoder.GetDecoder<Beatmap>(reader).Decode(reader);

            beatmap.BeatmapInfo.MD5Hash = md5;
            beatmap.BeatmapInfo.Hash = md5;
            var working = new TestWorkingBeatmap(beatmap, null, audio);

            var decoder = new OracleScoreDecoder(ruleset, working);
            Score score;
            using (var fs = File.OpenRead(job.Replay))
                score = decoder.Parse(fs);

            return (working, score, md5, decoder.ReplayBeatmapHash);
        }

        public static List<Mod> ResolveMods(Job job, Options options, Score score, Ruleset ruleset, List<string> warnings)
        {
            Mod[] decoded = score.ScoreInfo.Mods.ToArray();
            var mods = new List<Mod>(options.ReplaceMods && job.ModsJson != null ? Array.Empty<Mod>() : decoded);

            if (options.NoClassic)
                mods.RemoveAll(m => m is ModClassic);

            if (job.ModsJson != null)
            {
                var apiMods = JsonConvert.DeserializeObject<List<APIMod>>(job.ModsJson) ?? new List<APIMod>();

                foreach (var am in apiMods)
                {
                    var m = am.ToMod(ruleset);
                    if (m is UnknownMod)
                        throw new ArgumentException("unknown mod acronym: " + am.Acronym);
                    mods.RemoveAll(x => x.Acronym == m.Acronym);
                    mods.Add(m);
                }
            }

            if (!osu.Game.Utils.ModUtils.CheckCompatibleSet(mods, out var invalid))
                warnings.Add("incompatible mod combination: " + string.Join(",", invalid.Select(m => m.Acronym)));

            return mods;
        }

        private void startJob(Job job)
        {
            var ruleset = game.GetRulesetStore().GetRuleset("osu")!.CreateInstance();
            var (working, score, md5, replayHash) = decode(job, ruleset);

            var warnings = new List<string>();
            if (replayHash != null && !string.Equals(replayHash, md5, StringComparison.OrdinalIgnoreCase))
                warnings.Add($"beatmap md5 {md5} != replay beatmap hash {replayHash}");

            Mod[] decoded = score.ScoreInfo.Mods.ToArray();
            var mods = ResolveMods(job, options, score, ruleset, warnings);

            if (mods.Any(m => m is ModAutoplay))
                throw new ArgumentException("autoplay-type mods are not supported (they replace the replay)");

            var state = new JobState
            {
                Job = job,
                Ruleset = ruleset,
                BeatmapMd5 = md5,
                ReplayBeatmapHash = replayHash,
                IsLegacyScore = score.ScoreInfo.IsLegacyScore,
                DecodedMods = decoded,
                Mods = mods.ToArray(),
                Warnings = warnings,
                FrameTimes = score.Replay.Frames.Select(f => f.Time).OrderBy(t => t).ToList(),
            };

            runSemantics(state, working, score, FailSemantics.Live);
        }

        private void runSemantics(JobState state, WorkingBeatmap working, Score score, FailSemantics semantics)
        {
            var gameplay = new OracleGameplay(new RunSpec
            {
                Working = working,
                Score = score,
                Ruleset = state.Ruleset,
                Mods = state.Mods,
                Schedule = options.Schedule,
                Semantics = semantics,
                DumpPlayablePath = dumpPath(options.DumpPlayable, state.Job),
                DumpEnvPath = semantics == FailSemantics.Live ? dumpPath(options.DumpEnv, state.Job) : null,
            });

            gameplay.Completed = result =>
            {
                game.Post(() =>
                {
                    game.RemoveGameplay(gameplay);

                    if (current != state.Job) return; // errored meanwhile

                    try
                    {
                        if (semantics == FailSemantics.Live)
                        {
                            state.Live = result;

                            if (result.FailTriggerCount > 0)
                            {
                                // Fail semantics can only differ if the health processor ever tried to fail. Re-run from scratch
                                // (fresh decode, fresh mod instances) under ReplayPlayer semantics.
                                var (w2, s2, _, _) = decode(state.Job, state.Ruleset);
                                runSemantics(state, w2, s2, FailSemantics.ReplayPlayer);
                                return;
                            }
                        }
                        else
                            state.ReplayPlayer = result;

                        emit(state);
                    }
                    catch (Exception ex)
                    {
                        emitError(state.Job, ex);
                    }

                    current = null;
                    currentGameplay = null;
                    game.Post(next);
                });
            };

            currentGameplay = gameplay;
            game.Add(gameplay);
        }

        /// <summary>run: PATH is the file; batch: PATH is a directory, file "&lt;job index&gt;.json".</summary>
        private string? dumpPath(string? path, Job job)
        {
            if (path == null) return null;
            if (!batchMode) return path;
            Directory.CreateDirectory(path);
            return Path.Combine(path, job.Index.ToString(CultureInfo.InvariantCulture) + ".json");
        }

        public bool batchMode;

        private void writeLine(byte[] json)
        {
            stdout.Write(json);
            stdout.WriteByte((byte)'\n');
            stdout.Flush();
        }

        private void emitError(Job job, Exception ex)
        {
            Errors++;
            Done++;
            var ms = new MemoryStream();
            using (var w = new Utf8JsonWriter(ms))
            {
                w.WriteStartObject();
                w.WriteString("beatmap", job.Beatmap);
                w.WriteString("replay", job.Replay);
                if (job.ModsJson != null) w.WriteString("mods_arg", job.ModsJson);
                w.WriteString("error", ex.GetType().Name + ": " + ex.Message);
                w.WriteString("error_detail", ex.ToString());
                w.WriteEndObject();
            }

            writeLine(ms.ToArray());
            Console.Error.WriteLine($"[oracle] ERROR {job.Replay}: {ex.Message}");
        }

        private static string num(double d)
        {
            if (double.IsNaN(d) || double.IsInfinity(d))
                return "\"" + d.ToString("R", CultureInfo.InvariantCulture) + "\"";
            return d.ToString("R", CultureInfo.InvariantCulture);
        }

        private static void writeNum(Utf8JsonWriter w, string name, double d)
        {
            w.WritePropertyName(name);
            w.WriteRawValue(num(d), skipInputValidation: true);
        }

        private static void writeNum(Utf8JsonWriter w, double d) => w.WriteRawValue(num(d), skipInputValidation: true);

        private static void writeMods(Utf8JsonWriter w, string name, IEnumerable<Mod> mods)
        {
            w.WritePropertyName(name);
            w.WriteRawValue(JsonConvert.SerializeObject(mods.Select(m => new APIMod(m)).ToList()), skipInputValidation: true);
        }

        private static void writeStats(Utf8JsonWriter w, string name, IReadOnlyDictionary<HitResult, int> stats)
        {
            w.WriteStartObject(name);
            foreach (var kv in stats.Where(kv => kv.Value != 0).OrderBy(kv => (int)kv.Key))
                w.WriteNumber(kv.Key.ToString(), kv.Value);
            w.WriteEndObject();
        }

        private void writeResult(Utf8JsonWriter w, RunResult r)
        {
            var s = r.Score;
            w.WriteStartObject();
            w.WriteString("semantics", r.Semantics == FailSemantics.Live ? "live" : "replay_player");
            w.WriteBoolean("failed", r.Failed);
            if (r.FailTime is double ft) writeNum(w, "fail_time", ft);
            else w.WriteNull("fail_time");
            w.WriteNumber("fail_trigger_count", r.FailTriggerCount);
            w.WriteString("rank", s.Rank.ToString());
            w.WriteNumber("total_score", s.TotalScore);
            w.WriteNumber("total_score_without_mods", s.TotalScoreWithoutMods);
            writeNum(w, "accuracy", s.Accuracy);
            w.WriteNumber("max_combo", s.MaxCombo);
            w.WriteNumber("final_combo", s.Combo);
            writeNum(w, "final_health", r.FinalHealth);
            w.WriteBoolean("completed", r.Completed);
            writeStats(w, "statistics", s.Statistics);
            writeStats(w, "maximum_statistics", s.MaximumStatistics);
            w.WriteStartObject("legacy_counts");
            w.WriteNumber("300", s.GetCount300() ?? 0);
            w.WriteNumber("100", s.GetCount100() ?? 0);
            w.WriteNumber("50", s.GetCount50() ?? 0);
            w.WriteNumber("miss", s.GetCountMiss() ?? 0);
            w.WriteEndObject();
            w.WriteNumber("judgement_count", r.Judgements.Count);

            if (!options.NoJudgements)
            {
                w.WriteStartArray("judgements");

                foreach (var j in r.Judgements)
                {
                    w.WriteStartObject();
                    w.WriteNumber("i", j.Top);
                    w.WriteNumber("n", j.Nested);
                    w.WriteString("type", j.TypeName);
                    w.WriteString("result", j.Result.ToString());
                    writeNum(w, "time", j.RawTime);
                    writeNum(w, "offset", j.TimeOffset);
                    w.WriteNumber("combo", j.ComboAfter);
                    writeNum(w, "health", j.HealthAfter);
                    if (j.FailedAtJudgement) w.WriteBoolean("failed", true);
                    w.WriteEndObject();
                }

                w.WriteEndArray();
            }

            w.WriteEndObject();
        }

        private void emit(JobState st)
        {
            var live = st.Live!;
            var ms = new MemoryStream();

            using (var w = new Utf8JsonWriter(ms))
            {
                w.WriteStartObject();
                w.WriteString("oracle_version", "1");
                w.WriteString("lazer_commit", Program.LazerCommit);
                w.WriteString("lazer_version", "2026.1005.0-lazer");
                w.WriteString("framework_version", typeof(osu.Framework.Game).Assembly.GetName().Version?.ToString());
                w.WriteString("runtime", Environment.Version.ToString());

                w.WriteStartObject("environment");
                w.WriteNumber("window_width", OracleHost.WIDTH);
                w.WriteNumber("window_height", OracleHost.HEIGHT);
                writeNum(w, "draw_width", game.DrawWidth);
                writeNum(w, "draw_height", game.DrawHeight);
                writeNum(w, "ui_scale", game.Config.Get<float>(OsuSetting.UIScale));
                w.WriteString("scaling_mode", game.Config.Get<ScalingMode>(OsuSetting.Scaling).ToString());
                w.WriteBoolean("increase_first_object_visibility", game.Config.Get<bool>(OsuSetting.IncreaseFirstObjectVisibility));
                w.WriteBoolean("beatmap_skins", game.Config.Get<bool>(OsuSetting.BeatmapSkins));
                w.WriteString("beatmap_skin_loaded", "none");
                w.WriteString("storyboard", "not loaded");

                foreach (var kv in live.Environment.OrderBy(k => k.Key, StringComparer.Ordinal))
                    w.WriteString(kv.Key, kv.Value);
                w.WriteEndObject();

                w.WriteStartObject("input");
                w.WriteString("beatmap", st.Job.Beatmap);
                w.WriteString("replay", st.Job.Replay);
                w.WriteString("beatmap_md5", st.BeatmapMd5);
                w.WriteString("replay_beatmap_md5", st.ReplayBeatmapHash);
                w.WriteBoolean("beatmap_md5_match", string.Equals(st.BeatmapMd5, st.ReplayBeatmapHash, StringComparison.OrdinalIgnoreCase));
                w.WriteBoolean("is_legacy_score", st.IsLegacyScore);
                if (st.Job.ModsJson != null) w.WriteString("mods_arg", st.Job.ModsJson);
                w.WriteBoolean("no_classic", options.NoClassic);
                w.WriteBoolean("replace_mods", options.ReplaceMods);
                writeMods(w, "decoded_mods", st.DecodedMods);
                writeMods(w, "mods", live.GameplayMods);
                writeNum(w, "true_gameplay_rate", live.TrueGameplayRateAtStart);
                w.WriteNumber("hit_objects", live.Playable.HitObjects.Count);
                w.WriteStartArray("warnings");
                foreach (string s in st.Warnings) w.WriteStringValue(s);
                w.WriteEndArray();
                w.WriteEndObject();

                w.WriteStartObject("schedule");
                w.WriteString("kind", options.Schedule.Name);
                writeNum(w, "r0", live.R0);
                writeNum(w, "end", live.End);
                writeNum(w, "gameplay_start_time", live.GameplayStartTime);
                if (live.LastFrameTime is double lf) writeNum(w, "last_frame_time", lf);
                w.WriteNumber("references", live.References.Count);
                w.WriteNumber("steps", live.Steps.Count);
                if (options.Timing) w.WriteNumber("host_frames", live.HostFrames); // depends on wall-clock catch-up budget
                if (options.CheckSteps)
                    w.WriteString("step_check", checkSteps(live, st));
                w.WriteEndObject();

                w.WritePropertyName("live");
                writeResult(w, live);

                if (st.ReplayPlayer != null)
                {
                    w.WritePropertyName("replay_player");
                    writeResult(w, st.ReplayPlayer);
                }
                else
                {
                    // identical by construction: the health processor never attempted to fail.
                    w.WriteString("replay_player", "same_as_live");
                }

                if (options.Trace)
                {
                    w.WriteStartObject("trace");
                    w.WriteStartArray("references");
                    foreach (double d in live.References) writeNum(w, d);
                    w.WriteEndArray();
                    w.WriteStartArray("steps");
                    foreach (double d in live.Steps) writeNum(w, d);
                    w.WriteEndArray();
                    w.WriteEndObject();
                }

                if (options.Timing)
                    writeNum(w, "wall_ms", jobTimer.Elapsed.TotalMilliseconds);

                w.WriteEndObject();
            }

            writeLine(ms.ToArray());
            Done++;
            Console.Error.WriteLine($"[oracle] {Done} {Path.GetFileName(st.Job.Replay)} steps={live.Steps.Count} frames={live.HostFrames} run={live.RunMs:F0}ms total={jobTimer.Elapsed.TotalMilliseconds:F0}ms");
        }

        private string checkSteps(RunResult r, JobState st)
        {
            var expected = StepSimulator.Simulate(r.References, st.FrameTimes, r.GameplayStartTime);
            int n = Math.Min(expected.Count, r.Steps.Count);
            for (int i = 0; i < n; i++)
                if (expected[i] != r.Steps[i])
                    return $"MISMATCH at {i} expected={num(expected[i])} actual={num(r.Steps[i])} prev={(i > 0 ? num(r.Steps[i - 1]) : "-")}";
            if (expected.Count != r.Steps.Count)
                return $"MISMATCH count expected={expected.Count} actual={r.Steps.Count} last_expected={num(expected[^1])} last_actual={num(r.Steps[^1])}";
            return "ok";
        }
    }

    public static class Program
    {
        public static string LazerCommit =>
            typeof(Program).Assembly.GetCustomAttributes<AssemblyMetadataAttribute>().FirstOrDefault(a => a.Key == "LazerCommit")?.Value ?? "unknown";

        private static void usage()
        {
            Console.Error.WriteLine(@"usage:
  oracle run --beatmap X.osu --replay Y.osr [--mods JSON] [options]
  oracle batch --list FILE [options]        (FILE lines: ""beatmap replay [modsjson]"")
options:
  --schedule catchup|perframe|dense1ms|explicit:FILE   (default catchup)
  --trace            include reference + step times
  --no-classic       drop the auto-added Classic mod (stable replays)
  --replace-mods     --mods / per-line mods replace the decoded list instead of overriding by acronym
  --no-judgements    omit per-judgement list
  --timing           include wall_ms (non-deterministic field)
  --no-step-check    skip the step-sequence self-check
  --dump-playable P  write the playable beatmap (raw float bits) to P (batch: directory P, files <job index>.json)
  --dump-env P       write screen-space DrawInfo matrices + per-step mouse positions to P (batch: directory)
validation:
  oracle player --beatmap X.osu --replay Y.osr [--mods JSON] [--steps-out FILE]
      runs lazer's real ReplayPlayer in real time (virtual track) and records its step times + judgements");
        }

        public static int Main(string[] args)
        {
            CultureInfo.DefaultThreadCurrentCulture = CultureInfo.InvariantCulture;
            CultureInfo.DefaultThreadCurrentUICulture = CultureInfo.InvariantCulture;
            CultureInfo.CurrentCulture = CultureInfo.InvariantCulture;

            if (args.Length == 0)
            {
                usage();
                return 2;
            }

            var opts = new Options();
            string? beatmap = null, replay = null, mods = null, list = null;
            string cmd = args[0];

            try
            {
                for (int i = 1; i < args.Length; i++)
                {
                    string a = args[i];
                    string val() => i + 1 < args.Length ? args[++i] : throw new ArgumentException("missing value for " + a);

                    switch (a)
                    {
                        case "--beatmap": beatmap = val(); break;
                        case "--replay": replay = val(); break;
                        case "--mods": mods = val(); break;
                        case "--list": list = val(); break;
                        case "--schedule": opts.Schedule = ScheduleSpec.Parse(val()); break;
                        case "--trace": opts.Trace = true; break;
                        case "--no-classic": opts.NoClassic = true; break;
                        case "--replace-mods": opts.ReplaceMods = true; break;
                        case "--no-judgements": opts.NoJudgements = true; break;
                        case "--timing": opts.Timing = true; break;
                        case "--no-step-check": opts.CheckSteps = false; break;
                        case "--steps-out": opts.StepsOut = val(); break;
                        case "--dump-playable": opts.DumpPlayable = val(); break;
                        case "--dump-env": opts.DumpEnv = val(); break;
                        default: throw new ArgumentException("unknown argument " + a);
                    }
                }
            }
            catch (Exception e)
            {
                Console.Error.WriteLine(e.Message);
                usage();
                return 2;
            }

            var jobs = new List<Job>();

            if (cmd == "run" || cmd == "player")
            {
                if (beatmap == null || replay == null)
                {
                    usage();
                    return 2;
                }

                jobs.Add(new Job { Beatmap = beatmap, Replay = replay, ModsJson = mods });
            }
            else if (cmd == "batch")
            {
                if (list == null)
                {
                    usage();
                    return 2;
                }

                foreach (string raw in File.ReadLines(list))
                {
                    string line = raw.Trim();
                    if (line.Length == 0 || line.StartsWith('#')) continue;
                    string[] parts = line.Split((char[]?)null, 3, StringSplitOptions.RemoveEmptyEntries);
                    if (parts.Length < 2) throw new ArgumentException("bad list line: " + line);
                    jobs.Add(new Job { Beatmap = parts[0], Replay = parts[1], ModsJson = parts.Length > 2 ? parts[2] : mods, Index = jobs.Count });
                }
            }
            else
            {
                usage();
                return 2;
            }

            // stdout is reserved for JSON; anything else that writes to the console goes to stderr.
            var stdout = Console.OpenStandardOutput();
            Console.SetOut(Console.Error);

            string storage = Path.Combine(Path.GetTempPath(), "osu-oracle-" + Guid.NewGuid().ToString("N"));
            OracleHost.StoragePath = storage;

            var runner = new JobRunner(jobs, opts, stdout) { batchMode = cmd == "batch" };
            IOracleRunner r = cmd == "player" ? new PlayerRunner(jobs[0], opts, stdout) : runner;

            try
            {
                using (var host = new OracleHost())
                    host.Run(new OracleGame(r));
            }
            finally
            {
                try
                {
                    // only ever deletes the unique directory created above
                    if (storage.Contains("osu-oracle-", StringComparison.Ordinal) && Directory.Exists(storage))
                        Directory.Delete(storage, true);
                }
                catch
                {
                }
            }

            double secs = runner.Total.Elapsed.TotalSeconds;
            Console.Error.WriteLine($"[oracle] done {runner.Done} jobs ({runner.Errors} errors) in {secs:F1}s ({(secs > 0 ? runner.Done / secs : 0):F2}/s); GC gen0/1/2={GC.CollectionCount(0)}/{GC.CollectionCount(1)}/{GC.CollectionCount(2)} pause={GC.GetTotalPauseDuration().TotalMilliseconds:F0}ms alloc={GC.GetTotalAllocatedBytes() / 1e6:F0}MB");
            return runner.Errors > 0 ? 1 : 0;
        }
    }
}
