#!/usr/bin/env python3
"""Oracle vs server stats on LAZER scores (D13). stdlib only.

  run    --schedule catchup|perframe|dense1ms [--limit N] [--sample K] [--chunk 200] [--ids FILE]
         Runs `oracle batch` (one process at a time, restarted every --chunk jobs, GC heap limit) on downloaded
         scores (data/index_v2.sqlite status ok) and appends REDUCED results to data/oracle_v2/<schedule>.jsonl:
         judgement lists are replaced by per-HitObject-type result counts ("by_type"). Resumable (skips done ids).
  report [--md FILE] [--metrics status/metrics.json] [-v]
         Compares field by field with the server JSON and classifies every score:
           exact        all statistics, max_combo, accuracy (server rounds to 1e-6), total_score, rank, passed equal
           sched        differences explainable by schedule-sensitive objects only (slider tails/ticks/repeats,
                        the slider's own result, spinners and spinner ticks): a transport (max-flow) feasibility test
                        assigns the server's per-result counts minus the oracle's counts from non-sensitive objects
                        (HitCircle, SliderHeadCircle) to the oracle's sensitive objects using only results each
                        object type can produce; max_combo/total_score may then differ too (combo progression).
           suspicious   anything else (circle/head counts, maximum_statistics, accuracy with equal stats, mods,
                        pass/fail, oracle error ...)
  show ID [--schedule S]  print the field diff for one score.
"""
import argparse, collections, struct, json, os, random, re, sqlite3, subprocess, sys, tempfile, time

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
DB = os.path.join(ROOT, "data", "index_v2.sqlite")
OUT = os.path.join(ROOT, "data", "oracle_v2")
ORACLE = os.path.join(ROOT, "oracle", "oracle.sh")
LOCK = os.path.join(OUT, "oracle.lock")

NONSENS = {"HitCircle", "SliderHeadCircle"}
# OsuModRelax.Update returns early when playing back a non-legacy replay (OsuModRelax.cs: `if (hasReplay &&
# !legacyReplay) return;` -- the live RX presses are in the recorded frames), so RX is NOT frame-dependent for lazer
# replays. Autopilot moves the cursor in Update even during playback (OsuModAutopilot.cs:43-55).
# Mods that animate hit-area geometry (scale/position/rotation) make circle hits step-dependent too: input is
# processed before the drawables' transforms are updated for the step, so the hit test sees the geometry of the
# previous step time (cf. ISSUES G1); observed: GR scores give different circle results under catchup/perframe.
FRAME_DEP = {"AP", "MG", "RP", "AS", "GR", "DF", "TR", "WG", "SI", "DP", "BR", "BU"}
# results each object type can produce in lazer's osu! ruleset (Judgement.MaxResult/MinResult, spinner and
# classic slider use the full Great/Ok/Meh/Miss scale); unioned with whatever the oracle corpus shows.
ALLOWED = {
    "Slider": {"Great", "Ok", "Meh", "Miss", "IgnoreHit", "IgnoreMiss", "LegacyComboIncrease", "ComboBreak"},
    "SliderTailCircle": {"SliderTailHit", "IgnoreMiss", "SmallTickHit", "SmallTickMiss", "IgnoreHit"},
    "SliderTick": {"LargeTickHit", "LargeTickMiss"},
    "SliderRepeat": {"LargeTickHit", "LargeTickMiss"},
    "Spinner": {"Great", "Ok", "Meh", "Miss"},
    "HitCircle": {"Great", "Ok", "Meh", "Miss"},
    "SliderHeadCircle": {"Great", "Ok", "Meh", "Miss", "LargeTickHit", "LargeTickMiss"},
    "SpinnerTick": {"SmallBonus", "IgnoreMiss", "IgnoreHit"},
    "SpinnerBonusTick": {"LargeBonus", "IgnoreMiss", "IgnoreHit"},
}


def snake(k):
    return re.sub(r"(?<!^)([A-Z])", r"_\1", k).lower()


def camel(k):
    return "".join(p.capitalize() for p in k.split("_"))


def done_ids(path):
    s = set()
    if os.path.exists(path):
        for line in open(path):
            try:
                s.add(json.loads(line)["id"])
            except Exception:
                pass
    return s


HITS = ("Great", "Ok", "Meh")
BLOCKERS = ("HitCircle", "SliderHeadCircle")  # StartTimeOrderedHitPolicy.hitObjectCanBlockFutureHits: DrawableHitCircle (+ subclass DrawableSliderHead)


def round_flip_candidates(J):
    """Judgement groups that the replay's integer-ms frame times (LegacyScoreEncoder.cs:173, Math.Round) can flip:
    a press at exactly a blocking circle's integer StartTime is allowed (`time < StartTime` is false,
    StartTimeOrderedHitPolicy.cs:46) and force-misses it with offset 0, while the unrounded live press up to 0.5 ms
    earlier is blocked (Shake). Returns [[i, n, type, result], ...] for the forced miss and the hit(s) at that time."""
    out = []
    by_time = collections.defaultdict(list)
    for j in J:
        by_time[j["time"]].append(j)
    for j in J:
        if j["type"] in BLOCKERS and j["result"] == "Miss" and j["offset"] == 0:
            grp = [[j["i"], j["n"], j["type"], j["result"]]]
            grp += [[k["i"], k["n"], k["type"], k["result"]] for k in by_time[j["time"]]
                    if k is not j and k["type"] in BLOCKERS and k["result"] in HITS]
            out.append(grp)
    return out


def reduce_line(d, sid, keep_objects=False):
    for sem in ("live", "replay_player"):
        r = d.get(sem)
        if isinstance(r, dict) and "judgements" in r:
            J = r.pop("judgements")
            bt = collections.defaultdict(collections.Counter)
            for j in J:
                bt[j["type"]][j["result"]] += 1
            r["by_type"] = {t: dict(c) for t, c in bt.items()}
            r["round_flip"] = round_flip_candidates(J)
            if keep_objects:
                r["objres"] = [[j["i"], j["n"], j["type"], j["result"]] for j in J]
    d.pop("trace", None)
    d["id"] = sid
    return d


def fine_schedule_file(r0, end, step):
    f = tempfile.NamedTemporaryFile("w", suffix=".sched", delete=False)
    t, k = r0, 0
    while t <= end:
        f.write(repr(t) + "\n")
        k += 1
        t = r0 + k * step
    f.write(repr(end) + "\n")
    f.close()
    return f.name


def cmd_run(a):
    os.makedirs(OUT, exist_ok=True)
    out = os.path.join(OUT, a.schedule + a.out_tag + ".jsonl")
    db = sqlite3.connect(DB, timeout=60)
    rows = db.execute("select id, beatmap_path from scores where status='ok' order by id").fetchall()
    if a.ids:
        want = {int(x.split()[0]) for x in open(a.ids) if x.strip() and not x.startswith("#")}
        rows = [r for r in rows if r[0] in want]
    if a.focus:
        # only scores whose catchup result is not exact, plus a 1-in-a.focus control sample of exact ones
        meta = {sid: json.loads(js) for sid, js in db.execute("select id, json from scores where status='ok'")}
        cu = load_results("catchup")
        keep = set()
        for sid, o in cu.items():
            if sid in meta and (compare(o, meta[sid])[0] != "exact" or sid % a.focus == 0):
                keep.add(sid)
        rows = [r for r in rows if r[0] in keep]
    if a.sample:
        random.Random(1234).shuffle(rows)
        rows = rows[:a.sample]
    done = set() if a.force else done_ids(out)
    rows = [r for r in rows if r[0] not in done]
    if a.limit:
        rows = rows[:a.limit]
    print("todo %d (done %d) schedule=%s" % (len(rows), len(done), a.schedule), file=sys.stderr, flush=True)
    import fcntl
    lockf = open(LOCK, "w")
    fcntl.flock(lockf, fcntl.LOCK_EX)  # one oracle process at a time (ours)
    env = dict(os.environ, DOTNET_GCHeapHardLimit="0x30000000")
    if a.schedule.startswith("fine"):
        # explicit reference every N microseconds (fine250 = 0.25 ms) from the catchup run's r0 to end; one process per job
        step = int(a.schedule[4:]) / 1000.0
        cu = load_results("catchup")
        for sid, bp in rows:
            if sid not in cu or "schedule" not in cu[sid]:
                continue
            sf = fine_schedule_file(cu[sid]["schedule"]["r0"], cu[sid]["schedule"]["end"], step)
            t0 = time.time()
            p = subprocess.run(["nice", "-n", "10", ORACLE, "run", "--beatmap", os.path.join(ROOT, bp), "--replay",
                                os.path.join(ROOT, "data", "replays_v2", "%d.osr" % sid), "--schedule", "explicit:" + sf,
                                "--no-step-check"], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, env=env, cwd=ROOT, text=True)
            os.remove(sf)
            try:
                d = json.loads(p.stdout)
            except Exception:
                d = {"error": "no output (exit %d)" % p.returncode}
            with open(out, "a") as f:
                f.write(json.dumps(reduce_line(d, sid, a.keep_objects), separators=(",", ":")) + "\n")
            print("%s %s %d in %.0fs" % (time.strftime("%H:%M:%S"), a.schedule, sid, time.time() - t0), file=sys.stderr, flush=True)
        return
    for k in range(0, len(rows), a.chunk):
        chunk = rows[k:k + a.chunk]
        with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as lf:
            for sid, bp in chunk:
                lf.write("%s %s\n" % (os.path.join(ROOT, bp), os.path.join(ROOT, "data", "replays_v2", "%d.osr" % sid)))
            listfile = lf.name
        ids = {os.path.join(ROOT, "data", "replays_v2", "%d.osr" % sid): sid for sid, _ in chunk}
        t0 = time.time()
        p = subprocess.Popen(["nice", "-n", "10", ORACLE, "batch", "--list", listfile, "--schedule", a.schedule], stdout=subprocess.PIPE,
                             stderr=subprocess.DEVNULL, env=env, cwd=ROOT, text=True)
        n = 0
        with open(out, "a") as f:
            for line in p.stdout:
                try:
                    d = json.loads(line)
                except Exception:
                    continue
                rp = d.get("input", {}).get("replay") or d.get("replay")
                sid = ids.get(rp) or ids.get(os.path.join(ROOT, rp or ""))
                if sid is None:
                    continue
                f.write(json.dumps(reduce_line(d, sid, a.keep_objects), separators=(",", ":")) + "\n")
                f.flush()
                n += 1
        p.wait()
        os.remove(listfile)
        print("%s chunk %d: %d/%d jobs in %.0fs (exit %d)" % (time.strftime("%H:%M:%S"), k // a.chunk, n, len(chunk),
                                                              time.time() - t0, p.returncode), file=sys.stderr, flush=True)


# ---------------------------------------------------------------- comparison

def maxflow_feasible(supply, demand, allowed):
    """supply {type: n}, demand {result: n}; edges type->result if result in allowed[type]. Feasible iff max flow
    saturates both sides (sum equal)."""
    if any(v < 0 for v in demand.values()) or sum(supply.values()) != sum(demand.values()):
        return False
    types = [t for t in supply if supply[t] > 0]
    res = [r for r in demand if demand[r] > 0]
    # capacity graph: s -> t_i -> r_j -> sink
    N = 2 + len(types) + len(res)
    cap = [[0] * N for _ in range(N)]
    for i, t in enumerate(types):
        cap[0][2 + i] = supply[t]
        for j, r in enumerate(res):
            if r in allowed.get(t, ()):
                cap[2 + i][2 + len(types) + j] = 10 ** 9
    for j, r in enumerate(res):
        cap[2 + len(types) + j][1] = demand[r]
    flow = 0
    while True:
        par = [-1] * N
        par[0] = 0
        q = [0]
        while q and par[1] < 0:
            u = q.pop(0)
            for v in range(N):
                if par[v] < 0 and cap[u][v] > 0:
                    par[v] = u
                    q.append(v)
        if par[1] < 0:
            break
        b, v = 10 ** 9, 1
        while v:
            b = min(b, cap[par[v]][v]); v = par[v]
        v = 1
        while v:
            cap[par[v]][v] -= b; cap[v][par[v]] += b; v = par[v]
        flow += b
    return flow == sum(supply.values())


def _normval(v):
    # server JSON keeps what the client sent (10 vs 10.0, enum as "1" vs 1); compare values, not spellings
    if isinstance(v, bool):
        return v
    if isinstance(v, (int, float)):
        return float(v)
    if isinstance(v, str):
        try:
            return float(v)
        except ValueError:
            return v
    return v


def norm_mods(mods):
    return sorted((m["acronym"], sorted((k, _normval(v)) for k, v in (m.get("settings") or {}).items())) for m in mods)


def compare(o, s):
    """o: reduced oracle line, s: server score JSON. Returns (category, diffs dict, notes list)."""
    if "error" in o or "live" not in o:
        return "suspicious", {"oracle_error": str(o.get("error"))[:200]}, ["oracle error"]
    L = o["live"]
    diffs = {}
    srv = {camel(k): v for k, v in s["statistics"].items() if v}
    orc = {k: v for k, v in L["statistics"].items() if v}
    for k in sorted(set(srv) | set(orc)):
        if srv.get(k, 0) != orc.get(k, 0):
            diffs[k] = (orc.get(k, 0), srv.get(k, 0))
    smax = {camel(k): v for k, v in s.get("maximum_statistics", {}).items() if v}
    omax = {k: v for k, v in L["maximum_statistics"].items() if v}
    max_diff = {k: (omax.get(k, 0), smax.get(k, 0)) for k in set(smax) | set(omax) if smax.get(k, 0) != omax.get(k, 0)}
    other = {}
    if L["max_combo"] != s["max_combo"]:
        other["max_combo"] = (L["max_combo"], s["max_combo"])
    # the server stores accuracy as float32 and serves it rounded to 6 decimals (observed: 92030/108780 =
    # 0.84601949 -> f32 0.84601951 -> "0.84602"); accept exactly that transformation (or plain 6-dp rounding).
    acc_f32 = struct.unpack("<f", struct.pack("<f", L["accuracy"]))[0]
    acc_eq = s["accuracy"] in (round(acc_f32, 6), round(L["accuracy"], 6))
    if not acc_eq:
        other["accuracy"] = (L["accuracy"], s["accuracy"])
    if L["total_score"] != s["total_score"]:
        other["total_score"] = (L["total_score"], s["total_score"])
    if L["rank"] != s["rank"]:
        other["rank"] = (L["rank"], s["rank"])
    if (not L["failed"]) != bool(s["passed"]):
        other["passed"] = (not L["failed"], s["passed"])
    notes = []
    srv_mods = norm_mods(s.get("mods", []))
    dec_mods = norm_mods(o["input"].get("decoded_mods", []))
    if srv_mods != dec_mods:
        notes.append("mods differ: server %s replay %s" % (srv_mods, dec_mods))
    all_d = dict(diffs, **other)
    if max_diff:
        all_d["maximum_statistics"] = max_diff
    if not all_d and not notes:
        return "exact", {}, notes
    if max_diff or "passed" in other or notes:
        return "suspicious", all_d, notes
    if not diffs:
        # equal statistics: accuracy and rank are functions of the statistics -> must agree
        if "accuracy" in other or "rank" in other:
            return "suspicious", all_d, notes + ["stats equal but accuracy/rank differ"]
        if not any(t not in NONSENS for t in L.get("by_type", {})):
            return "suspicious", all_d, notes + ["stats equal, combo/score differ, no sensitive objects"]
        return "sched", all_d, notes + ["stats equal; combo progression"]
    bt = L.get("by_type")
    if bt is None:
        return "suspicious", all_d, notes + ["no by_type"]
    # mods whose per-frame Update logic drives judgement inputs (auto key presses, cursor or object movement,
    # gameplay rate): every object becomes schedule-sensitive (OsuModRelax/Autopilot/Magnetised/Repel and
    # ModAdaptiveSpeed implement IUpdatableByPlayfield and integrate over frame time).
    rf = [x for grp in L.get("round_flip", []) for x in grp]

    def explainable(nonsens, use_round=False):
        supply = {t: sum(c.values()) for t, c in bt.items() if t not in nonsens}
        nons = collections.Counter()
        for t in nonsens:
            nons.update(bt.get(t, {}))
        allowed = {t: set(ALLOWED.get(t, ())) | set(bt[t]) for t in supply}
        if use_round:
            for i, n, t, r in rf:
                if t in nonsens:
                    nons[r] -= 1
                    supply["Rounding"] = supply.get("Rounding", 0) + 1
            allowed["Rounding"] = {"Great", "Ok", "Meh", "Miss"}
        demand = {r: srv.get(r, 0) - nons.get(r, 0) for r in set(srv) | set(L["statistics"])}
        return all(v >= 0 for v in demand.values()) and maxflow_feasible(supply, {r: v for r, v in demand.items() if v}, allowed)

    if explainable(NONSENS):
        return "sched", all_d, notes
    # mods whose per-frame Update logic drives judgement inputs during playback (cursor or object movement,
    # gameplay rate) make every object schedule-sensitive (Autopilot/Magnetised/Repel, ModAdaptiveSpeed).
    if rf and explainable(NONSENS, True):
        return "rounding", all_d, notes + ["needs %d circle judgement(s) at integer-ms press==blocker StartTime (replay time rounding)" % len(rf)]
    fd = sorted({m["acronym"] for m in s.get("mods", [])} & FRAME_DEP)
    if fd and explainable(set()):
        return "sched-fd", all_d, notes + ["frame-dependent mods %s: circle/head results schedule-sensitive" % "".join(fd)]
    return "suspicious", all_d, notes + ["not explainable by schedule-sensitive objects"]


def load_results(schedule):
    p = os.path.join(OUT, schedule + ".jsonl")
    res = {}
    if os.path.exists(p):
        for line in open(p):
            try:
                d = json.loads(line)
            except Exception:
                continue
            res[d["id"]] = d
    return res


def out_of_range_positions(path):
    """Number of hit objects with x or y outside [0, 512] (clamped from 2026.1001.0-tachyon on, docs/lazer-builds.md)."""
    n, sec = 0, None
    try:
        for line in open(path, encoding="utf-8-sig", errors="replace"):
            line = line.strip()
            if line.startswith("["):
                sec = line
                continue
            if sec == "[HitObjects]" and line:
                p = line.split(",")
                try:
                    x, y = float(p[0]), float(p[1])
                except (ValueError, IndexError):
                    continue
                n += not (0 <= x <= 512 and 0 <= y <= 512)
    except OSError:
        return -1
    return n


_gap_cache = {}


def replay_gap(sid):
    if sid not in _gap_cache:
        from replay_gaps import object_times, worst_gap
        from rounding_check import split_osr
        db = sqlite3.connect(DB, timeout=60)
        bp = db.execute("select beatmap_path from scores where id=?", (sid,)).fetchone()[0]
        _, frames, _ = split_osr(open(os.path.join(ROOT, "data", "replays_v2", "%d.osr" % sid), "rb").read())
        _gap_cache[sid] = worst_gap(frames, object_times(os.path.join(ROOT, bp)))
    return _gap_cache[sid]


def modkey(mods):
    return "".join(sorted(m["acronym"] for m in mods)) or "NM"


def cmd_report(a):
    db = sqlite3.connect(DB, timeout=60)
    meta = {sid: (json.loads(js), eq, cv) for sid, js, eq, cv in
            db.execute("select id, json, equiv, client_version from scores where status='ok'")}
    lines = []
    P = lines.append
    metrics = {}
    counts = {}
    cats = {}
    for sch in ("catchup", "perframe", "dense1ms", "fine250"):
        res = load_results(sch)
        res.update(load_results(sch + "_obj"))  # flip-check sample (same runs + per-judgement data)
        if not res:
            continue
        c = collections.Counter()
        by_mod = collections.defaultdict(collections.Counter)
        by_combo = collections.defaultdict(collections.Counter)
        by_eq = collections.defaultdict(collections.Counter)
        field = collections.Counter()
        dirn = collections.defaultdict(collections.Counter)
        sus = []
        cat = {}
        for sid, o in res.items():
            if sid not in meta:
                continue
            s, eq, cv = meta[sid]
            k, d, notes = compare(o, s)
            if k == "suspicious":
                g = replay_gap(sid)
                if g[2] >= 5:  # the replay lost input (no frames while >= 5 objects were due): live stats unreproducible
                    k, notes = "replay-gap", notes + ["replay has no frames in [%d, %d] (%d objects)" % g]
            cat[sid] = (k, d, notes)
            c[k] += 1
            for m in s.get("mods", []) or [{"acronym": "NM"}]:
                by_mod[m["acronym"]][k] += 1
            by_combo[modkey(s.get("mods", []))][k] += 1
            by_eq[eq][k] += 1
            for f in d:
                field[f] += 1
            if k == "suspicious":
                sus.append((sid, d, notes))
            for f, v in d.items():
                if isinstance(v, (list, tuple)) and len(v) == 2 and all(isinstance(x, (int, float)) for x in v) and f != "accuracy":
                    dirn[f][(v[1] > v[0]) - (v[1] < v[0])] += 1
        cats[sch] = cat
        n = sum(c.values())
        pct = lambda x: "%d/%d (%.1f%%)" % (x, n, 100.0 * x / max(n, 1))
        P("### schedule `%s` (n=%d)\n" % (sch, n))
        P("| category | count |\n|---|---|")
        for k in ("exact", "sched", "rounding", "sched-fd", "replay-gap", "suspicious"):
            P("| %s | %s |" % (k, pct(c[k])))
        P("\nBuild class: " + ", ".join("%s: %d exact / %d sched / %d sched-fd / %d suspicious" % (e, v["exact"], v["sched"], v["sched-fd"], v["suspicious"]) for e, v in sorted(by_eq.items(), key=str)))
        P("\nFields differing (number of scores): " + ", ".join("%s %d" % kv for kv in field.most_common()))
        P("\nDirection (scores where server > oracle / server < oracle): " + ", ".join(
            "%s +%d/-%d" % (f, v[1], v[-1]) for f, v in sorted(dirn.items())))
        P("\n| mod (any combo containing it) | n | exact | sched (incl. fd) | suspicious |\n|---|---|---|---|---|")
        for m, v in sorted(by_mod.items(), key=lambda kv: -sum(kv[1].values())):
            t = sum(v.values())
            P("| %s | %d | %.1f%% | %.1f%% | %d |" % (m, t, 100.0 * v["exact"] / t, 100.0 * (v["sched"] + v["sched-fd"]) / t, v["suspicious"]))
        P("\nTop mod combinations: " + ", ".join("%s %d/%d exact" % (m, v["exact"], sum(v.values()))
                                                 for m, v in sorted(by_combo.items(), key=lambda kv: -sum(kv[1].values()))[:15]))
        if sus:
            P("\nSuspicious (first %d of %d):\n" % (min(len(sus), a.max_list), len(sus)))
            for sid, d, notes in sorted(sus)[:a.max_list]:
                P("- %d %s: %s %s" % (sid, modkey(meta[sid][0].get("mods", [])), json.dumps(d, sort_keys=True)[:300], "; ".join(notes)[:300]))
        P("")
        counts[sch] = (c, n)
    # cross-schedule: does perframe / dense reproduce more?
    if "catchup" in cats and "perframe" in cats:
        both = set(cats["catchup"]) & set(cats["perframe"])
        tr = collections.Counter((cats["catchup"][i][0], cats["perframe"][i][0]) for i in both)
        P("### catchup -> perframe category transitions (n=%d)\n" % len(both))
        P(", ".join("%s->%s: %d" % (x, y, v) for (x, y), v in sorted(tr.items())))
        P("")
    if "dense1ms" in cats:
        for base in ("catchup", "perframe"):
            if base in cats:
                both = set(cats[base]) & set(cats["dense1ms"])
                tr = collections.Counter((cats[base][i][0], cats["dense1ms"][i][0]) for i in both)
                P("### %s -> dense1ms transitions (n=%d)\n" % (base, len(both)))
                P(", ".join("%s->%s: %d" % (x, y, v) for (x, y), v in sorted(tr.items())))
                P("")
        anyx = [i for i in cats.get("catchup", {}) if any(cats.get(s, {}).get(i, ("",))[0] == "exact" for s in cats)]
        P("Exact under at least one schedule (of scores run on catchup): %d/%d\n" % (len(anyx), len(cats.get("catchup", {}))))
    nb, oor = 0, []
    for sid, bp in db.execute("select id, beatmap_path from scores where status='ok' and equiv='B'").fetchall():
        nb += 1
        k = out_of_range_positions(os.path.join(ROOT, bp))
        if k:
            oor.append(sid)
    P("Class-B scores on maps with object positions outside [0,512] (where B != pinned): %d/%d %s\n" % (len(oor), nb, oor[:20]))
    st = dict(db.execute("select status, count(*) from scores group by status"))
    names = list(FLIP_SCHEDULES) + sorted(f[:-len("_obj.jsonl")] for f in os.listdir(OUT) if f.startswith("jitter") and f.endswith("_obj.jsonl"))
    fres = {nm: load_results(nm + "_obj") for nm in names}
    fcount = collections.Counter()
    fstatus = {}
    for sid in fres["catchup"]:
        if sid in meta:
            st_ = flipcheck_one(meta[sid][0], {nm: fres[nm][sid] for nm in names if sid in fres[nm]})["status"]
            fstatus[sid] = st_
            fcount[st_] += 1
    fc = None
    if fcount:
        nf = sum(fcount.values())
        fc = "%d/%d sampled scores demonstrated (%s); %d not (yet) demonstrated = suspicious until explained" % (
            nf - fcount["NOT-demonstrated"], nf, ", ".join("%s %d" % kv for kv in sorted(fcount.items()) if kv[0] != "NOT-demonstrated"),
            fcount["NOT-demonstrated"])
        P("### flip check (per-judgement results across %s)\n\n%s\n" % (", ".join(names), fc))
    if "catchup" in counts:
        c, n = counts["catchup"]
        # scores whose remaining tail/tick deficit is covered by concrete sub-frame mechanisms found by
        # difftest/tracking_trace.py (cursor excursion / regain within 3 px, key release within 0.5 ms of the window)
        margin_ok = set()
        tsp = os.path.join(OUT, "tracking_summary.json")
        if os.path.exists(tsp):
            margin_ok = {r["id"] for r in json.load(open(tsp)) if str(r.get("status", "")).startswith("deficits covered")}
        # automatic triage (difftest/triage_v2.py) + manual demonstrations, difftest/server_demonstrated.json
        dp = os.path.join(ROOT, "difftest", "server_demonstrated.json")
        tri = {}
        if os.path.exists(dp):
            dj = json.load(open(dp))
            if "scores" in dj:
                tri = {int(k): v for k, v in dj["scores"].items()}
            else:  # v1 file (hand-written)
                tri = {int(k): {"category": "demonstrated", "mechanism": "manual"} for k in dj if k != "weak"}
                tri.update({int(k): {"category": "perturbation", "mechanism": "press-shift"} for k in dj.get("weak", {})})
        mism = {i for i, v in cats["catchup"].items() if v[0] != "exact"}
        tcat = collections.Counter()
        tmech = collections.Counter()
        final_sus, pert, untriaged_sus = set(), set(), set()
        for i in mism:
            e = tri.get(i)
            if e is None:
                h = cats["catchup"][i][0]
                if i not in margin_ok and h != "replay-gap" and (
                        (h == "suspicious" and not fstatus.get(i, "").startswith("demonstrated")) or fstatus.get(i) == "NOT-demonstrated"):
                    untriaged_sus.add(i)
                tcat["untriaged"] += 1
                continue
            k = e["category"]
            if k in ("suspicious", "unverifiable") and (fstatus.get(i, "").startswith("demonstrated") or i in margin_ok):
                k = "demonstrated"
                e = dict(e, mechanism="flip-check" if fstatus.get(i, "").startswith("demonstrated") else "tracking-margin")
            if k == "heuristic-sched" and fstatus.get(i, "").startswith("demonstrated"):
                k, e = "demonstrated", dict(e, mechanism="flip-check")
            elif k == "heuristic-sched" and fstatus.get(i) == "NOT-demonstrated" and i not in margin_ok:
                k = "suspicious"  # the stronger flip check (fine250, cursor jitter) found no flip either
            tcat[k] += 1
            if k == "demonstrated":
                tmech[e.get("mechanism", "?")] += 1
            if k in ("suspicious", "unverifiable"):
                final_sus.add(i)
            if k == "perturbation":
                pert.add(i)
        final_sus |= untriaged_sus
        P("### triage of catchup mismatches (difftest/triage_v2.py)\n")
        P("categories: " + ", ".join("%s %d" % kv for kv in sorted(tcat.items())) + "; demonstrated by mechanism: " +
          ", ".join("%s %d" % kv for kv in sorted(tmech.items())))
        # suspicious rate by mod
        bym = collections.defaultdict(lambda: [0, 0])
        for i in cats["catchup"]:
            ms = meta[i][0].get("mods", []) or [{"acronym": "NM"}]
            for mm in ms:
                bym[mm["acronym"]][0] += 1
                bym[mm["acronym"]][1] += i in final_sus
        P("\nsuspicious rate by mod (all evaluated scores containing the mod): " + ", ".join(
            "%s %d/%d (%.1f%%)" % (k, v[1], v[0], 100.0 * v[1] / v[0]) for k, v in sorted(bym.items(), key=lambda kv: -kv[1][0]) if v[0] >= 20 or v[1]))
        P("\nsuspicious ids: %s\n" % sorted(final_sus))
        metrics["lazer server agreement: suspicious mismatches (non-schedule-sensitive)"] = \
            "%d of %d evaluated (%.2f%%) [triaged suspicious/unverifiable %d + untriaged heuristic %d]; +%d reproduced only by a +-1 ms press shift (threshold not localised); triage of %d mismatches: %s; see docs/server-agreement.md" % (
                len(final_sus), n, 100.0 * len(final_sus) / max(n, 1), len(final_sus) - len(untriaged_sus), len(untriaged_sus), len(pert),
                len(mism), ", ".join("%s %d" % kv for kv in sorted(tcat.items())))
        m_ok = c["exact"] + c["sched"] + c["rounding"] + c["sched-fd"]
        metrics["lazer server agreement: exact or schedule-only (heuristic)"] = "%d/%d (%.1f%%; catchup; incl. %d replay-time-rounding, %d frame-dependent-mod; %d replays with input gaps excluded)" % (
            m_ok, n - c["replay-gap"], 100.0 * m_ok / max(n - c["replay-gap"], 1), c["rounding"], c["sched-fd"], c["replay-gap"])
        metrics["lazer server agreement: exact match"] = ", ".join(
            "%s %d/%d" % (sch, counts[sch][0]["exact"], counts[sch][1]) for sch in ("catchup", "perframe", "dense1ms") if sch in counts) + \
            " (perframe/dense1ms on catchup-mismatch-enriched subsets; remaining diffs are slider tail/tick/spinner judgements the 60fps replay can't determine; D13)"
    if fc:
        metrics["lazer server agreement: schedule-only demonstrated by flips"] = fc
    metrics["lazer scores downloaded"] = "%d (replays+beatmaps, md5-verified; equivalent builds per docs/lazer-builds.md)" % st.get("ok", 0)
    text = "\n".join(lines)
    print(text)
    if a.md:
        open(a.md, "w").write(text + "\n")
    if a.metrics:
        try:
            m = json.load(open(a.metrics))
        except Exception:
            m = {}
        for k in ("server agreement exact (catchup)", "server agreement exact or schedule-only (catchup)",
                  "suspicious mismatches", "server agreement exact (perframe)", "server agreement exact (dense1ms)",
                  "lazer scores downloaded"):
            m.pop(k, None)
        # the status page groups these rows under "B. LAZER replay playback vs LIVE server stats" with a "B: " prefix
        metrics = {("B: " + k if k.startswith("lazer server agreement") else k): v for k, v in metrics.items()}
        for k in list(m):
            if k.startswith("lazer server agreement"):
                m.pop(k)
        m.update(metrics)
        with open(a.metrics + ".part", "w") as f:
            json.dump(m, f, indent=1)
        os.replace(a.metrics + ".part", a.metrics)


FLIP_SCHEDULES = ("catchup", "perframe", "dense1ms", "fine250")


def _feasible(s, runs):
    obs = collections.defaultdict(set)
    otype = {}
    for sch, o in runs.items():
        for i, n, t, r in o["live"]["objres"]:
            obs[(i, n)].add(r)
            otype[(i, n)] = t
    rnd = set()
    for o in runs.values():
        for grp in o["live"].get("round_flip", []):
            for i, n, t, r in grp:
                rnd.add((i, n))
    srv = {camel(k): v for k, v in s["statistics"].items() if v}
    fixed = collections.Counter()
    sig = collections.Counter()
    flip_types = collections.Counter()
    for key, rs in obs.items():
        if key in rnd:
            rs = rs | {"Great", "Ok", "Meh", "Miss"}
        if len(rs) == 1:
            fixed[next(iter(rs))] += 1
        else:
            sig[frozenset(rs)] += 1
            flip_types[otype[key] + ("(rounding)" if key in rnd else "")] += 1
    demand = {r: srv.get(r, 0) - fixed.get(r, 0) for r in set(srv) | set(fixed) | {r for g in sig for r in g}}
    supply = {"S%d" % k: c for k, (g, c) in enumerate(sig.items())}
    allowed = {"S%d" % k: set(g) for k, (g, c) in enumerate(sig.items())}
    ok = all(v >= 0 for v in demand.values()) and maxflow_feasible(supply, {r: v for r, v in demand.items() if v}, allowed)
    return ok, dict(flip_types), {r: v for r, v in demand.items() if v < 0}


def flipcheck_one(s, runs):
    """runs: {name: reduced oracle line with live.objres}. Per object (i, n): the set of results observed across runs.
    Objects with a single result are fixed. The rest (plus integer-rounding candidates) may take any observed result.
    The check is feasible iff the server's per-result counts can be met (max-flow). Schedule runs are tried first,
    then schedule + cursor-jitter ("margin") runs. Runs that failed (frozen stats) are excluded but reported."""
    failed = sorted(k for k, o in runs.items() if isinstance(o.get("live"), dict) and o["live"].get("failed"))
    good = {k: o for k, o in runs.items() if isinstance(o.get("live"), dict) and "objres" in o["live"] and not o["live"].get("failed")}
    sched = {k: o for k, o in good.items() if not k.startswith("jitter")}
    res = {"runs": sorted(runs), "failed_runs": failed}
    if not sched:
        res.update(status="NOT-demonstrated", why="no passing schedule run" if failed else "no objres")
        return res
    ok, ft, unmet = _feasible(s, sched)
    if ok:
        res.update(status="demonstrated (schedule)", flippable=ft)
        return res
    ok2, ft2, unmet2 = _feasible(s, good)
    if ok2 and len(good) > len(sched):
        res.update(status="demonstrated (schedule + 1px cursor margin)", flippable=ft2)
        return res
    res.update(status="NOT-demonstrated", flippable=ft2, unmet=unmet2)
    return res


def cmd_flipcheck(a):
    db = sqlite3.connect(DB, timeout=60)
    meta = {sid: json.loads(js) for sid, js in db.execute("select id, json from scores where status='ok'")}
    names = list(FLIP_SCHEDULES) + sorted(f[:-len("_obj.jsonl")] for f in os.listdir(OUT) if f.startswith("jitter") and f.endswith("_obj.jsonl"))
    res = {n: load_results(n + "_obj") for n in names}
    ids = sorted(set().union(*[set(r) for r in res.values()]))
    out = []
    for sid in ids:
        runs = {n: res[n][sid] for n in names if sid in res[n]}
        if "catchup" not in runs or sid not in meta:
            continue
        cat = compare(runs["catchup"], meta[sid])[0]
        r = flipcheck_one(meta[sid], runs)
        r.update(id=sid, catchup_category=cat, mods=modkey(meta[sid].get("mods", [])))
        out.append(r)
        print(json.dumps(r, sort_keys=True))
    if a.json:
        json.dump(out, open(a.json, "w"), indent=0)


def cmd_show(a):
    db = sqlite3.connect(DB, timeout=60)
    s = json.loads(db.execute("select json from scores where id=?", (a.id,)).fetchone()[0])
    o = load_results(a.schedule).get(a.id)
    if o is None:
        sys.exit("no oracle result")
    k, d, notes = compare(o, s)
    print(k, json.dumps(d), notes)
    print("server mods", s.get("mods"), "replay mods", o["input"].get("decoded_mods"))
    print("by_type", json.dumps(o["live"].get("by_type")))


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--schedule", default="catchup")
    r.add_argument("--limit", type=int, default=0)
    r.add_argument("--sample", type=int, default=0, help="deterministic random subset of this size")
    r.add_argument("--chunk", type=int, default=200)
    r.add_argument("--force", action="store_true", help="re-run ids already in the output (last line wins)")
    r.add_argument("--keep-objects", action="store_true", help="store per-judgement results (for flipcheck)")
    r.add_argument("--out-tag", default="", help="suffix for the output file (e.g. _obj)")
    r.add_argument("--focus", type=int, default=0, help="only catchup non-exact scores + every N-th id as control")
    r.add_argument("--ids", help="file with score ids (first column)")
    p = sub.add_parser("report")
    p.add_argument("--md")
    p.add_argument("--metrics")
    p.add_argument("--max-list", type=int, default=40)
    s = sub.add_parser("show")
    s.add_argument("id", type=int)
    s.add_argument("--schedule", default="catchup")
    fc = sub.add_parser("flipcheck")
    fc.add_argument("--json")
    a = ap.parse_args()
    {"run": cmd_run, "report": cmd_report, "show": cmd_show, "flipcheck": cmd_flipcheck}[a.cmd](a)


if __name__ == "__main__":
    main()
