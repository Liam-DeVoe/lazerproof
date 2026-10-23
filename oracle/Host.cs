// Headless host + minimal OsuGameBase used purely for dependency injection (config, skins, rulesets, audio "No sound").

using System;
using System.Collections.Generic;
using System.Drawing;
using osu.Framework;
using osu.Framework.Configuration;
using osu.Framework.Graphics.Containers;
using osu.Framework.Platform;
using osu.Game;
using osu.Game.Configuration;
using osu.Game.Graphics.Containers;
using osu.Game.Online.API;

namespace Oracle
{
    /// <summary>
    /// HeadlessGameHost(realtime: false), single threaded, window/draw size 1024x768, fresh private storage.
    /// </summary>
    public class OracleHost : HeadlessGameHost
    {
        public const int WIDTH = 1024;
        public const int HEIGHT = 768;

        // Static because UserStoragePaths may be queried during base construction.
        public static string StoragePath = "";

        public OracleHost()
            : base("oracle", new HostOptions(), realtime: false)
        {
        }

        public override IEnumerable<string> UserStoragePaths => new[] { StoragePath };

        protected override void SetupConfig(IDictionary<FrameworkSetting, object> defaultOverrides)
        {
            defaultOverrides[FrameworkSetting.WindowedSize] = new Size(WIDTH, HEIGHT);
            defaultOverrides[FrameworkSetting.ExecutionMode] = ExecutionMode.SingleThread;
            base.SetupConfig(defaultOverrides);
            // Storage is fresh, but be explicit in case defaults were persisted.
            Config.SetValue(FrameworkSetting.WindowedSize, new Size(WIDTH, HEIGHT));
            Config.SetValue(FrameworkSetting.ExecutionMode, ExecutionMode.SingleThread);
        }
    }

    /// <summary>
    /// Minimal game. Mirrors <see cref="OsuGame"/> only in the root scaling container (ScalingMode.Everything, which applies
    /// UIScale); everything else is plain OsuGameBase with an offline (dummy) API.
    /// </summary>
    public partial class OracleGame : OsuGameBase
    {
        private readonly IOracleRunner runner;

        public OracleGame(IOracleRunner runner)
        {
            this.runner = runner;
            API = new DummyAPIAccess();
        }

        protected override void InitialiseFonts()
        {
            // fonts only affect text rendering; skipped as in lazer's own test runner (OsuTestSceneTestRunner).
        }

        // The stock BeatmapUpdater downloads + decompresses the online beatmap metadata cache (online.db.bz2) in the
        // background. Irrelevant for gameplay and costly (network, CPU, allocations), so it is replaced by a no-op.
        protected override osu.Game.Beatmaps.IBeatmapUpdater CreateBeatmapUpdater() => new NoopBeatmapUpdater();

        private class NoopBeatmapUpdater : osu.Game.Beatmaps.IBeatmapUpdater
        {
            public void Queue(osu.Game.Database.Live<osu.Game.Beatmaps.BeatmapSetInfo> beatmapSet, osu.Game.Beatmaps.MetadataLookupScope lookupScope) { }
            public void Process(osu.Game.Beatmaps.BeatmapSetInfo beatmapSet, osu.Game.Beatmaps.MetadataLookupScope lookupScope) { }
            public void ProcessObjectCounts(osu.Game.Beatmaps.BeatmapInfo beatmapInfo, osu.Game.Beatmaps.MetadataLookupScope lookupScope) { }
            public void Dispose() { }
        }

        protected override Container CreateScalingContainer() => new ScalingContainer(ScalingMode.Everything);

        protected override void LoadComplete()
        {
            base.LoadComplete();
            // Subscribed after OsuGameBase's own handler, so our return value wins (multicast returns the last result).
            Host.ExceptionThrown += runner.OnUnhandledException;
        }

        private int framesSinceLoad;

        protected override void Update()
        {
            base.Update();

            // Give game-level components (e.g. RulesetConfigCache, SkinManager) a few frames to finish their LoadComplete.
            if (framesSinceLoad >= 0 && ++framesSinceLoad == 5)
            {
                framesSinceLoad = -1;
                runner.Start(this);
            }
        }

        public OsuConfigManager Config => LocalConfig;

        public new void Add(osu.Framework.Graphics.Drawable d) => base.Add(d);

        public osu.Game.Rulesets.RulesetStore GetRulesetStore() => RulesetStore;

        public void SetGameplayBindables(osu.Game.Beatmaps.WorkingBeatmap working, osu.Game.Rulesets.RulesetInfo ruleset, System.Collections.Generic.IReadOnlyList<osu.Game.Rulesets.Mods.Mod> mods)
        {
            Ruleset.Value = ruleset;
            Beatmap.Value = working;
            SelectedMods.Value = mods;
        }

        public void Post(System.Action a) => Schedule(a);

        public void RemoveGameplay(osu.Framework.Graphics.Drawable d) => Remove(d, true);
    }
}
