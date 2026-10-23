#!/usr/bin/env python3
"""Line/branch coverage of the lazer + osu-framework code exercised by oracle runs (coverlet, IL instrumentation).

The instrumented oracle is a separate plain (non-R2R) Release build of oracle/oracle.csproj in
data/wip/lazer-coverage/covbin (`dotnet build -c Release -o ...`; same lazer/framework sources and dlls as the
deployed oracle, which is never touched; the result cache is never read for coverage runs). osu.Framework.pdb comes
from the nuget symbol package (ppy.osu.framework 2026.921.1 .snupkg); its CI paths (D:\\a\\osu-framework\\...) are
mapped to the local checkout at the same tag. coverlet instruments the dlls in covbin IN PLACE for the duration of
one invocation and restores them afterwards, so runs must be sequential (flock'd here).

Subcommands
  run    --list JOBS --name N [--chunk 150] [-- oracle batch options...]
         one `tools/heavy coverlet ...` call per chunk (CHUNK rule: size chunks so that one call
         takes <= ~10 min: ~40 real replays, ~110 synthetic, ~20 dense1ms); writes runs/N/cKKK.json.gz (coverlet json) and
         runs/N/cKKK.check.json (job count, errors, byte-equality of each output line vs the deployed oracle's cache
         entry when one exists). Resumable: finished chunks are skipped.
  merge  [--runs N1,N2,...]  -> merged.json.gz (sum of hits over all chunks of the given/all runs)
  report [--merged F] [--md OUT]   per-file/per-method tables + partially-taken branch list (report.json, md tables).
  branches --files REGEX [--lines]  triage listing: partial branches + never-entered methods with source lines.
"""
import argparse, fcntl, glob, gzip, hashlib, json, os, re, subprocess, sys, time, zlib

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
COV = os.path.join(ROOT, "data", "wip", "lazer-coverage")
COVBIN = os.path.join(COV, "covbin")
DOTNET = os.path.expanduser("~/.dotnet")
FW_PREFIX = "D:\\a\\osu-framework\\osu-framework\\"
FW_LOCAL = os.path.join(ROOT, "osu-framework") + "/"


def norm_path(p):
    if p.startswith(FW_PREFIX):
        return FW_LOCAL + p[len(FW_PREFIX):].replace("\\", "/")
    return p


def rel(p):
    p = norm_path(p)
    for pre, tag in ((os.path.join(ROOT, "lazer") + "/", "lazer/"), (FW_LOCAL, "osu-framework/")):
        if p.startswith(pre):
            return tag + p[len(pre):]
    return p


# ---------------------------------------------------------------- run

def cache_lookup(opts, line):
    sys.path.insert(0, os.path.join(ROOT, "tools"))
    import oracle_cache
    fp = getattr(cache_lookup, "fp", None) or oracle_cache.fingerprint()
    cache_lookup.fp = fp
    k = oracle_cache.job_key(fp, opts, line)
    if not k or not os.path.exists(oracle_cache.cache_path(k)):
        return None
    with open(oracle_cache.cache_path(k), "rb") as f:
        return zlib.decompress(f.read()).decode()


def run(a):
    jobs = [l.rstrip("\n") for l in open(a.list) if l.strip() and not l.lstrip().startswith("#")]
    if a.limit:
        jobs = jobs[:a.limit]
    out = os.path.join(COV, "runs", a.name)
    os.makedirs(out, exist_ok=True)
    opts = a.opts[1:] if a.opts[:1] == ["--"] else a.opts
    with open(os.path.join(out, "meta.json"), "w") as f:
        json.dump({"list": os.path.abspath(a.list), "opts": opts, "jobs": len(jobs), "chunk": a.chunk}, f)
    env = dict(os.environ, DOTNET_ROOT=DOTNET, DOTNET_CLI_TELEMETRY_OPTOUT="1", DOTNET_GCHeapHardLimit="0x30000000",
               PATH=DOTNET + ":" + os.path.join(DOTNET, "tools") + ":" + os.environ.get("PATH", ""))
    for k in range(0, len(jobs), a.chunk):
        tag = "c%03d" % (k // a.chunk)
        if os.path.exists(os.path.join(out, tag + ".json.gz")):
            continue
        if os.path.exists(os.path.join(COV, "STOP")):
            print("STOP file present; stopping before %s/%s" % (a.name, tag), file=sys.stderr)
            return
        chunk = jobs[k:k + a.chunk]
        lst = os.path.join(out, tag + ".list")
        with open(lst, "w") as f:
            f.write("\n".join(chunk) + "\n")
        raw = os.path.join(out, tag + ".json")
        cmd = [os.path.join(ROOT, "tools", "heavy"), os.path.join(DOTNET, "tools", "coverlet"), COVBIN,
               "--target", os.path.join(COVBIN, "oracle"),
               "--targetargs", " ".join(["batch", "--list", lst] + opts),
               "--include", "[osu.Game]*", "--include", "[osu.Game.Rulesets.Osu]*", "--include", "[osu.Framework]*",
               "--exclude-assemblies-without-sources", "None", "--format", "json", "-o", raw]
        t0 = time.time()
        with open(os.path.join(COV, ".lock"), "w") as lk:
            fcntl.flock(lk, fcntl.LOCK_EX)  # coverlet instruments covbin in place: one invocation at a time
            p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env, text=True)
        results = [l for l in p.stdout.splitlines() if l.startswith("{")]
        chk = {"jobs": len(chunk), "outputs": len(results), "errors": 0, "cache_equal": 0, "cache_diff": 0,
               "cache_absent": 0, "diff_jobs": [], "rc": p.returncode, "secs": round(time.time() - t0)}
        for line, res in zip(chunk, results):
            if '"error"' in res[:300] and json.loads(res).get("error"):
                chk["errors"] += 1
            c = cache_lookup(opts, line)
            if c is None:
                chk["cache_absent"] += 1
            elif c == res:
                chk["cache_equal"] += 1
            else:
                chk["cache_diff"] += 1
                chk["diff_jobs"].append(line)
        if not os.path.exists(raw):
            print("chunk %s FAILED rc=%d: %s" % (tag, p.returncode, p.stderr[-2000:] + p.stdout[-2000:]), file=sys.stderr)
            sys.exit(1)
        with open(raw, "rb") as fi, gzip.open(raw + ".gz.tmp", "wb", 6) as fo:
            fo.write(fi.read())
        os.replace(raw + ".gz.tmp", raw + ".gz")
        os.remove(raw)
        with gzip.open(os.path.join(out, tag + ".out.jsonl.gz"), "wt") as f:  # instrumented outputs (sanity checks)
            f.write("\n".join(results) + "\n")
        with open(os.path.join(out, tag + ".check.json"), "w") as f:
            json.dump(chk, f)
        print("%s %s/%s: %s" % (time.strftime("%H:%M:%S"), a.name, tag, json.dumps({x: chk[x] for x in chk if x != "diff_jobs"})),
              file=sys.stderr, flush=True)


# ---------------------------------------------------------------- merge

def merge(a):
    names = a.runs.split(",") if a.runs else sorted(os.listdir(os.path.join(COV, "runs")))
    M = {}  # (file) -> {"methods": {(class, method): {"lines": {ln: hits}, "br": {(ln,off,end,path,ord): hits}}}}
    nchunks = 0
    per_run = {}
    for n in names:
        files = sorted(glob.glob(os.path.join(COV, "runs", n, "c*.json.gz")))
        per_run[n] = len(files)
        for fn in files:
            nchunks += 1
            d = json.load(gzip.open(fn))
            for mod, fs in d.items():
                for f, classes in fs.items():
                    rf = rel(f)
                    fm = M.setdefault(rf, {"module": mod, "methods": {}})
                    for cl, meths in classes.items():
                        for me, body in meths.items():
                            e = fm["methods"].setdefault(cl + "\t" + me, {"lines": {}, "br": {}})
                            for ln, h in body.get("Lines", {}).items():
                                e["lines"][ln] = e["lines"].get(ln, 0) + h
                            for b in body.get("Branches", []):
                                key = "%d:%d:%d:%d:%d" % (b["Line"], b["Offset"], b["EndOffset"], b["Path"], b["Ordinal"])
                                e["br"][key] = e["br"].get(key, 0) + b["Hits"]
    with gzip.open(os.path.join(COV, "merged.json.gz.tmp"), "wt") as f:
        json.dump({"runs": per_run, "chunks": nchunks, "files": M}, f)
    os.replace(os.path.join(COV, "merged.json.gz.tmp"), os.path.join(COV, "merged.json.gz"))
    print("merged %d chunks from %s" % (nchunks, per_run))


# ---------------------------------------------------------------- report

# Gameplay/judgement-relevant code (task focus). Regexes over repo-relative paths.
FOCUS = [
    ("osu ruleset: DHOs", r"^lazer/osu\.Game\.Rulesets\.Osu/Objects/Drawables/"),
    ("osu ruleset: hit objects", r"^lazer/osu\.Game\.Rulesets\.Osu/Objects/[^/]+\.cs$"),
    ("osu ruleset: judgements/scoring", r"^lazer/osu\.Game\.Rulesets\.Osu/(Judgements|Scoring)/"),
    ("osu ruleset: mods", r"^lazer/osu\.Game\.Rulesets\.Osu/Mods/"),
    ("osu ruleset: UI (playfield, hit policies, cursor)", r"^lazer/osu\.Game\.Rulesets\.Osu/UI/"),
    ("osu ruleset: replays/input", r"^lazer/osu\.Game\.Rulesets\.Osu/(Replays/|OsuInputManager\.cs)"),
    ("osu ruleset: beatmaps", r"^lazer/osu\.Game\.Rulesets\.Osu/Beatmaps/"),
    ("osu.Game: scoring", r"^lazer/osu\.Game/Rulesets/Scoring/"),
    ("osu.Game: judgements", r"^lazer/osu\.Game/Rulesets/Judgements/"),
    ("osu.Game: DrawableHitObject / pooling", r"^lazer/osu\.Game/Rulesets/Objects/(Drawables/|Pooling/|HitObject\.cs|HitObjectLifetimeEntry|SyntheticHitObjectEntry)"),
    ("osu.Game: Rulesets.UI (DrawableRuleset, FSC, playfield, HOC)", r"^lazer/osu\.Game/Rulesets/UI/"),
    ("osu.Game: replays", r"^lazer/osu\.Game/(Rulesets/Replays|Replays|Input/Handlers)/"),
    ("osu.Game: mods (base)", r"^lazer/osu\.Game/Rulesets/Mods/"),
    ("osu.Game: legacy score decoder", r"^lazer/osu\.Game/Scoring/Legacy/"),
    ("osu.Game: scoring misc", r"^lazer/osu\.Game/Scoring/(ScoreInfo|ScoreRank|HitResultDisplay)"),
    ("osu.Game: beatmaps (control points, decoder)", r"^lazer/osu\.Game/Beatmaps/(ControlPoints/|Formats/LegacyBeatmapDecoder|Formats/LegacyDecoder|Beatmap\.cs|BeatmapProcessor|BeatmapConverter|BeatmapDifficulty|IBeatmapDifficultyInfo)"),
    ("osu.Game: gameplay clocks/breaks", r"^lazer/osu\.Game/(Screens/Play/(BreakTracker|GameplayClock|GameplayState|IGameplayClock)|Beatmaps/Timing/)"),
    ("framework: clocks", r"^osu-framework/osu\.Framework/Timing/"),
    ("framework: input (queues, states, handlers)", r"^osu-framework/osu\.Framework/Input/"),
    ("framework: transforms", r"^osu-framework/osu\.Framework/Graphics/Transforms/"),
    ("framework: lifetime/containers", r"^osu-framework/osu\.Framework/Graphics/(Containers/(Container|CompositeDrawable|LifetimeManagement)|Performance/)"),
    ("framework: Drawable", r"^osu-framework/osu\.Framework/Graphics/Drawable\.cs$"),
    ("framework: bindables", r"^osu-framework/osu\.Framework/Bindables/"),
    ("framework: utils/math", r"^osu-framework/osu\.Framework/(Utils/|Graphics/Primitives/|MathUtils)"),
]
# Judgement/score core (headline "core" numbers and the per-method table in docs/lazer-coverage.md).
CORE = re.compile(r"^lazer/osu\.Game\.Rulesets\.Osu/(Objects/Drawables/(DrawableHitCircle|DrawableSlider\w*|SliderInputManager|"
                  r"DrawableSpinner\w*|SpinnerSpinHistory|DrawableOsuHitObject)\.cs|Skinning/Default/SpinnerRotationTracker\.cs|"
                  r"UI/(OsuPlayfield|StartTimeOrderedHitPolicy|LegacyHitPolicy|DrawableOsuRuleset)\.cs|Scoring/\w+\.cs|"
                  r"Replays/OsuFramedReplayInputHandler\.cs|Replays/OsuReplayFrame\.cs|OsuInputManager\.cs|"
                  r"Objects/(Slider|Spinner|OsuHitObject|HitCircle|SliderHeadCircle|SliderTailCircle|SliderTick|SliderRepeat|"
                  r"SliderEndCircle|SpinnerTick|SpinnerBonusTick|SliderEventGenerator)\.cs|Mods/\w+\.cs)"
                  r"|^lazer/osu\.Game/(Rulesets/Scoring/(ScoreProcessor|HealthProcessor|DrainingHealthProcessor|"
                  r"LegacyDrainingHealthProcessor|JudgementProcessor|HitWindows|HitResult)\.cs|Rulesets/Judgements/(Judgement|"
                  r"JudgementResult)\.cs|Rulesets/Objects/Drawables/DrawableHitObject\.cs|Rulesets/Objects/HitObject\.cs|"
                  r"Rulesets/UI/(HitObjectContainer|Playfield|FrameStabilityContainer|RulesetInputManager)\.cs|"
                  r"Rulesets/Replays/FramedReplayInputHandler\.cs|Input/Handlers/ReplayInputHandler\.cs|"
                  r"Scoring/Legacy/LegacyScoreDecoder\.cs|Screens/Play/BreakTracker\.cs|Rulesets/Mods/Mod(AccuracyChallenge|"
                  r"SuddenDeath|Perfect|FailCondition|NoFail|Easy|EasyWithExtraLives|TimeRamp|AdaptiveSpeed|RateAdjust|"
                  r"DoubleTime|HalfTime|Classic|DifficultyAdjust)\.cs)"
                  r"|^osu-framework/osu\.Framework/(Utils/Interpolation|Timing/(FramedClock|ManualClock)|"
                  r"Input/Bindings/KeyBindingContainer)\.cs$")
GENERATED = re.compile(r"/obj/|\.g\.cs$|SourceGeneration")


def area_of(f):
    for name, rx in FOCUS:
        if re.search(rx, f):
            return name
    return None


def summarize(fm):
    lt = lh = bt = bh = mt = mh = 0
    for e in fm["methods"].values():
        n = len(e["lines"]); h = sum(1 for v in e["lines"].values() if v)
        lt += n; lh += h
        bt += len(e["br"]); bh += sum(1 for v in e["br"].values() if v)
        if n:
            mt += 1; mh += 1 if h else 0
    return lt, lh, bt, bh, mt, mh


def pct(a, b):
    return "%.1f%%" % (100.0 * a / b) if b else "-"


def short_method(m):
    m = m.split("\t", 1)[1]
    m = m.split("::", 1)[1] if "::" in m else m
    return m.replace("|", "\\|")


def report(a):
    D = json.load(gzip.open(a.merged))
    files = {f: v for f, v in D["files"].items() if not GENERATED.search(f)}
    tot = {}
    for f, fm in files.items():
        mod = fm["module"]
        s = summarize(fm)
        t = tot.setdefault(mod, [0] * 6)
        for i in range(6):
            t[i] += s[i]
    areas = {}
    for f, fm in files.items():
        ar = area_of(f)
        if ar:
            areas.setdefault(ar, []).append((f, summarize(fm)))
    # unexercised branches: branch arms with 0 hits whose sibling arm (same line+offset) was hit, or whose line was hit
    unx = []
    for f, fm in files.items():
        ar = area_of(f)
        if not ar:
            continue
        for m, e in fm["methods"].items():
            groups = {}
            for k, h in e["br"].items():
                ln, off, end, path, ordi = map(int, k.split(":"))
                groups.setdefault((ln, off), []).append((path, h))
            for (ln, off), arms in groups.items():
                hit = [p for p, h in arms if h]
                miss = [p for p, h in arms if not h]
                if miss and hit:  # the condition was evaluated, one outcome never happened
                    unx.append({"file": f, "line": ln, "method": short_method(m), "area": ar,
                                "arms": len(arms), "missed_paths": miss,
                                "hits": sum(h for _, h in arms)})
    core = [0] * 6
    for f, fm in files.items():
        if CORE.search(f):
            sm = summarize(fm)
            for i in range(6):
                core[i] += sm[i]
    out = {"core": core, "core_files": sum(1 for f in files if CORE.search(f)), "modules": tot, "areas": {k: v for k, v in areas.items()}, "partial_branches": unx,
           "runs": D["runs"], "chunks": D["chunks"]}
    with open(os.path.join(COV, "report.json"), "w") as f:
        json.dump(out, f)
    if a.md:
        write_tables(out, files, a.md)
    for mod, t in sorted(tot.items()):
        print("%-28s line %s (%d/%d) branch %s (%d/%d) method %s" % (mod, pct(t[1], t[0]), t[1], t[0], pct(t[3], t[2]), t[3], t[2], pct(t[5], t[4])))
    print("judgement core (%d files): line %s (%d/%d) branch %s (%d/%d) method %s" % (out["core_files"], pct(core[1], core[0]),
          core[1], core[0], pct(core[3], core[2]), core[3], core[2], pct(core[5], core[4])))
    print("partial branches in focus areas:", len(unx))


def write_tables(out, files, path):
    L = []
    c = out["core"]
    L.append("| scope | lines | branches | methods |\n|---|---|---|---|")
    L.append("| **judgement core (%d files)** | %s (%d/%d) | %s (%d/%d) | %s (%d/%d) |" % (out["core_files"], pct(c[1], c[0]), c[1], c[0],
             pct(c[3], c[2]), c[3], c[2], pct(c[5], c[4]), c[5], c[4]))
    for mod, t in sorted(out["modules"].items()):
        L.append("| %s | %s (%d/%d) | %s (%d/%d) | %s (%d/%d) |" % (mod, pct(t[1], t[0]), t[1], t[0], pct(t[3], t[2]), t[3], t[2], pct(t[5], t[4]), t[5], t[4]))
    L.append("")
    L.append("### Per area\n\n| area | files | lines | branches | methods |\n|---|---|---|---|---|")
    for name, _ in FOCUS:
        fl = out["areas"].get(name, [])
        s = [sum(x[1][i] for x in fl) for i in range(6)]
        L.append("| %s | %d | %s (%d/%d) | %s (%d/%d) | %s |" % (name, len(fl), pct(s[1], s[0]), s[1], s[0], pct(s[3], s[2]), s[3], s[2], pct(s[5], s[4])))
    L.append("")
    L.append("### Per file (focus areas; files with >= 1 coverable line)\n")
    for name, _ in FOCUS:
        fl = sorted(out["areas"].get(name, []))
        if not fl:
            continue
        L.append("<details><summary>%s (%d files)</summary>\n\n| file | lines | branches | methods hit |\n|---|---|---|---|" % (name, len(fl)))
        for f, s in fl:
            if s[0]:
                L.append("| %s | %s (%d/%d) | %s (%d/%d) | %d/%d |" % (f, pct(s[1], s[0]), s[1], s[0], pct(s[3], s[2]), s[3], s[2], s[5], s[4]))
        L.append("\n</details>\n")
    L.append("### Per method (judgement core files only; methods not fully covered, never-entered last)\n")
    for name, _ in FOCUS:
        rows = []
        for f, _s in sorted(out["areas"].get(name, [])):
            if not CORE.search(f):
                continue
            for m, e in files[f]["methods"].items():
                n = len(e["lines"]); h = sum(1 for v in e["lines"].values() if v)
                bt = len(e["br"]); bh = sum(1 for v in e["br"].values() if v)
                if not n or (h == n and bh == bt):
                    continue
                first = min(int(x) for x in e["lines"])
                rows.append((0 if h else 1, f, first, short_method(m), h, n, bh, bt))
        if not rows:
            continue
        rows.sort()
        L.append("<details><summary>%s: %d methods not fully covered (%d never entered)</summary>\n\n| file:line | method | lines | branches |\n|---|---|---|---|" % (
            name, len(rows), sum(r[0] for r in rows)))
        for z, f, first, m, h, n, bh, bt in rows:
            L.append("| %s:%d | `%s` | %d/%d | %d/%d |" % (f, first, m[:110], h, n, bh, bt))
        L.append("\n</details>\n")
    with open(path, "w") as fo:
        fo.write("\n".join(L) + "\n")


def src_line(f, ln, memo={}):
    p = f.replace("lazer/", os.path.join(ROOT, "lazer") + "/", 1) if f.startswith("lazer/") else \
        f.replace("osu-framework/", FW_LOCAL, 1)
    if p not in memo:
        try:
            memo[p] = open(p, encoding="utf-8-sig", errors="replace").read().splitlines()
        except OSError:
            memo[p] = []
    s = memo[p]
    return s[ln - 1].strip() if 0 < ln <= len(s) else "?"


def branches(a):
    """Triage listing: for files matching --files, every partially-taken branch point (one arm never taken) and every
    never-entered method, with the source line."""
    D = json.load(gzip.open(a.merged))
    rx = re.compile(a.files)
    for f in sorted(D["files"]):
        if GENERATED.search(f) or not rx.search(f):
            continue
        rows = []
        for m, e in D["files"][f]["methods"].items():
            if e["lines"] and not any(e["lines"].values()):
                first = min(int(x) for x in e["lines"])
                rows.append((first, "NEVER  %-60s" % short_method(m)[:60], src_line(f, first)))
                continue
            groups = {}
            for k, h in e["br"].items():
                ln, off, end, path, ordi = map(int, k.split(":"))
                groups.setdefault((ln, off), []).append((path, h))
            for (ln, off), arms in sorted(groups.items()):
                if any(h for _, h in arms) and not all(h for _, h in arms):
                    rows.append((ln, "BRANCH arms=%s" % ",".join("%d:%d" % (p, h) for p, h in sorted(arms)), src_line(f, ln)))
            if a.lines:  # contiguous runs of never-executed lines inside an entered method
                lns = sorted(int(x) for x, h in e["lines"].items() if not h)
                allx = sorted(int(x) for x in e["lines"])
                run_ = []
                for ln in lns + [None]:
                    if run_ and (ln is None or allx.index(ln) != allx.index(run_[-1]) + 1):
                        rows.append((run_[0], "UNHIT  lines %d-%d (%d)" % (run_[0], run_[-1], len(run_)), src_line(f, run_[0])))
                        run_ = []
                    if ln is not None:
                        run_.append(ln)
        if rows:
            print("== %s" % f)
            for ln, what, s in sorted(rows):
                print("  %5d %s | %s" % (ln, what, s[:140]))


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest="cmd", required=True)
    r = sp.add_parser("run")
    r.add_argument("--list", required=True)
    r.add_argument("--name", required=True)
    r.add_argument("--chunk", type=int, default=150)
    r.add_argument("--limit", type=int, default=0)
    r.add_argument("opts", nargs=argparse.REMAINDER)
    m = sp.add_parser("merge")
    m.add_argument("--runs", default="")
    p = sp.add_parser("report")
    p.add_argument("--merged", default=os.path.join(COV, "merged.json.gz"))
    p.add_argument("--md", default=None)
    b = sp.add_parser("branches")
    b.add_argument("--merged", default=os.path.join(COV, "merged.json.gz"))
    b.add_argument("--files", required=True, help="regex over repo-relative paths")
    b.add_argument("--lines", action="store_true", help="also list unhit lines")
    a = ap.parse_args()
    {"run": run, "merge": merge, "report": report, "branches": branches}[a.cmd](a)


if __name__ == "__main__":
    main()
