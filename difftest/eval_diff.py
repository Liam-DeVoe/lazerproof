#!/usr/bin/env python3
"""End-to-end differential test: Lean `evaltest` (.osu + .osr -> result, OsuModel.Eval) vs the oracle (lazer).

Both sides get exactly the same inputs (beatmap file, replay file, oracle-like options), so the oracle's JSON can be
compared directly; oracle batch results are cached transparently by oracle/oracle.sh (tools/oracle_cache.py).

Subcommands
  jobs   --corpus stable|v2 [--limit N] [--offset K] [--sample N]      print job lines "beatmap.osu replay.osr"
  oracle --list JOBS [--schedule S] [--mods JSON] [--replace-mods] [--no-classic] [--chunk 150]
         warm the oracle cache (chunks of <= --chunk jobs per oracle process; MEMORY rule)
  run    --list JOBS --work DIR [same options]  [--tag T]
         oracle (cached) + evaltest for every job, judgement-by-judgement comparison; DIR/results.jsonl, summary
  playable --list JOBS --work DIR [--mods JSON] [--replace-mods] [--no-classic]
         adapter losslessness: oracle --dump-playable vs `evaltest --dump-playable` (bit-exact, every emitted key)

Compared (per fail semantics live / replay_player): every judgement (i, n, type, result, RawTime, combo, health,
failed), statistics, maximum_statistics, max/final combo, total score (+ without mods), accuracy, rank, failed,
fail_time, fail_trigger_count, final_health, completed; plus decoded/effective mod acronyms, is_legacy_score,
hit_objects, schedule r0/end/gameplay_start_time/last_frame_time/steps. Errors: an oracle error must correspond to a
model rejection (reported separately, by reason).
"""
import argparse, json, os, random, sqlite3, struct, subprocess, sys, time
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
ORACLE = os.path.join(ROOT, "oracle", "oracle.sh")
EVALTEST = os.environ.get("EVALTEST") or os.path.join(ROOT, "model", ".lake", "build", "bin", "evaltest")


# ---------------------------------------------------------------- jobs

def jobs_stable():
    db = sqlite3.connect(os.path.join(ROOT, "data", "index.sqlite"))
    rows = []
    for f in sorted(os.listdir(os.path.join(ROOT, "data", "replays"))):
        if not f.endswith(".osr"):
            continue
        r = db.execute("select beatmap_id from scores where score_id=?", (int(f.split(".")[0]),)).fetchone()
        if not r:
            continue
        bm = os.path.join(ROOT, "data", "beatmaps", f"{r[0]}.osu")
        if os.path.exists(bm):
            rows.append(f"{bm} {os.path.join(ROOT, 'data', 'replays', f)}")
    return rows


def jobs_v2():
    # same line format as difftest/oracle_vs_server_v2.py (=> shared oracle cache entries)
    db = sqlite3.connect(os.path.join(ROOT, "data", "index_v2.sqlite"), timeout=60)
    rows = db.execute("select id, beatmap_path from scores where status='ok' order by id").fetchall()
    out = []
    for sid, bp in rows:
        rp = os.path.join(ROOT, "data", "replays_v2", "%d.osr" % sid)
        if bp and os.path.exists(os.path.join(ROOT, bp)) and os.path.exists(rp):
            out.append("%s %s" % (os.path.join(ROOT, bp), rp))
    return out


def read_jobs(path):
    return [l.rstrip("\n") for l in open(path) if l.strip() and not l.lstrip().startswith("#")]


def oracle_opts(a):
    o = ["--schedule", a.schedule]
    if a.mods is not None:
        o += ["--mods", a.mods]
    if a.replace_mods:
        o.append("--replace-mods")
    if a.no_classic:
        o.append("--no-classic")
    return o


def cached_results(jobs, opts):
    """Read oracle results straight from the transparent cache (tools/oracle_cache.py) when every job hits, so a
    fully cached run does not wait for a heavy-job slot. Returns None on any miss."""
    sys.path.insert(0, os.path.join(ROOT, "tools"))
    import oracle_cache, zlib
    fp = oracle_cache.fingerprint()
    out = []
    for l in jobs:
        k = oracle_cache.job_key(fp, opts, l)
        if not k or not os.path.exists(oracle_cache.cache_path(k)):
            return None
        with open(oracle_cache.cache_path(k), "rb") as f:
            out.append(json.loads(zlib.decompress(f.read()).decode()))
    return out


def run_oracle(jobs, a, work, extra=()):
    """Oracle batch over jobs in chunks; returns {job line: result dict}."""
    res = {}
    for k in range(0, len(jobs), a.chunk):
        chunk = jobs[k:k + a.chunk]
        if not extra and not os.environ.get("ORACLE_NOCACHE"):
            hit = cached_results(chunk, oracle_opts(a))
            if hit is not None:
                res.update(zip(chunk, hit))
                continue
        lst = os.path.join(work, "oracle_jobs.txt")
        with open(lst, "w") as f:
            f.write("\n".join(chunk) + "\n")
        env = dict(os.environ, DOTNET_GCHeapHardLimit="0x30000000")
        t0 = time.time()
        p = subprocess.run([ORACLE, "batch", "--list", lst] + oracle_opts(a) + list(extra), stdout=subprocess.PIPE,
                           stderr=subprocess.DEVNULL, env=env, text=True)
        lines = [json.loads(l) for l in p.stdout.splitlines() if l.strip()]
        for line, d in zip(chunk, lines):
            res[line] = d
        print("%s oracle chunk %d: %d/%d in %.0fs" % (time.strftime("%H:%M:%S"), k // a.chunk, len(lines), len(chunk),
                                                     time.time() - t0), file=sys.stderr, flush=True)
    return res


def evaltest_args(a):
    o = ["--schedule", a.schedule]
    if a.mods is not None:
        o += ["--mods", a.mods]
    if a.replace_mods:
        o.append("--replace-mods")
    if a.no_classic:
        o.append("--no-classic")
    return o


def run_evaltest(line, a, extra=()):
    bm, rp = line.split(None, 1)[:2] if len(line.split(None, 2)) < 3 else line.split(None, 2)[:2]
    mods = line.split(None, 2)[2] if len(line.split(None, 2)) > 2 else None
    args = [EVALTEST, bm, rp] + evaltest_args(a) + list(extra)
    if mods is not None:  # per-line mods override --mods (as in oracle batch)
        if "--mods" in args:
            i = args.index("--mods")
            args[i + 1] = mods
        else:
            args += ["--mods", mods]
    t0 = time.time()
    p = subprocess.run(args, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    dt = time.time() - t0
    try:
        d = json.loads(p.stdout)
    except Exception:
        d = {"error": "evaltest: no JSON output (exit %d): %s" % (p.returncode, p.stderr[-500:])}
    if "PANIC" in p.stderr or "index out of bounds" in p.stderr or "panic" in p.stderr.lower():
        d["_panic"] = p.stderr[:300]
    d["_wall"] = dt
    return d


# ---------------------------------------------------------------- comparison

def bits(x):
    """Oracle numbers (shortest round-trip double or "NaN"/"Infinity") -> IEEE bits hex (as evaltest prints)."""
    if isinstance(x, str):
        if x.startswith("0x"):
            return x
        x = {"NaN": float("nan"), "Infinity": float("inf"), "-Infinity": float("-inf")}.get(x, x)
    return "0x" + struct.pack(">d", float(x)).hex()


RESULT_KEYS = ["failed", "fail_trigger_count", "rank", "total_score", "total_score_without_mods", "max_combo",
               "final_combo", "completed", "statistics", "maximum_statistics", "legacy_counts", "judgement_count"]
BITS_KEYS = ["accuracy", "final_health"]


def cmp_result(o, m, where, diffs, live=True):
    for k in RESULT_KEYS:
        if o.get(k) != m.get(k):
            diffs.append("%s.%s: oracle=%s model=%s" % (where, k, o.get(k), m.get(k)))
    for k in BITS_KEYS:
        if bits(o[k]) != m.get(k):
            diffs.append("%s.%s: oracle=%s model=%s" % (where, k, bits(o[k]), m.get(k)))
    ft_o = None if o.get("fail_time") is None else bits(o["fail_time"])
    if ft_o != m.get("fail_time"):
        diffs.append("%s.fail_time: oracle=%s model=%s" % (where, ft_o, m.get("fail_time")))
    oj, mj = o.get("judgements", []), m.get("judgements", [])
    first = None
    for idx in range(max(len(oj), len(mj))):
        if idx >= len(oj) or idx >= len(mj):
            first = (idx, oj[idx] if idx < len(oj) else None, mj[idx] if idx < len(mj) else None)
            break
        a, b = oj[idx], mj[idx]
        ka = (a["i"], a["n"], a["type"], a["result"], bits(a["time"]))
        kb = (b["i"], b["n"], b["type"], b["result"], b["time"])
        if live or "combo" in b:  # both semantics' combo/health/failed (older evaltest: live only)
            ka += (a["combo"], bits(a["health"]), a.get("failed", False))
            kb += (b["combo"], b["health"], b.get("failed", False))
        if ka != kb:
            first = (idx, a, b)
            break
    if first:
        diffs.append("%s.judgement[%d]: oracle=%s model=%s" % (where, first[0], json.dumps(first[1]), json.dumps(first[2])))
    return len(oj)


def compare(o, m):
    diffs = []
    oi, mi = o["input"], m["input"]
    acr = lambda ms: [x["acronym"] for x in ms]
    for k in ["is_legacy_score", "hit_objects"]:
        if oi[k] != mi.get(k):
            diffs.append("input.%s: oracle=%s model=%s" % (k, oi[k], mi.get(k)))
    if acr(oi["decoded_mods"]) != mi.get("decoded_mods_acronyms"):
        diffs.append("input.decoded_mods: oracle=%s model=%s" % (acr(oi["decoded_mods"]), mi.get("decoded_mods_acronyms")))
    if acr(oi["mods"]) != mi.get("mods_acronyms"):
        diffs.append("input.mods: oracle=%s model=%s" % (acr(oi["mods"]), mi.get("mods_acronyms")))
    if bits(oi["true_gameplay_rate"]) != mi.get("true_gameplay_rate"):
        diffs.append("input.true_gameplay_rate: oracle=%s model=%s" % (bits(oi["true_gameplay_rate"]), mi.get("true_gameplay_rate")))
    os_, ms_ = o["schedule"], m["schedule"]
    for k in ["r0", "end", "gameplay_start_time", "last_frame_time"]:
        ov = None if os_.get(k) is None else bits(os_[k])
        if ov != ms_.get(k):
            diffs.append("schedule.%s: oracle=%s model=%s" % (k, ov, ms_.get(k)))
    if os_["steps"] != ms_.get("steps"):
        diffs.append("schedule.steps: oracle=%s model=%s" % (os_["steps"], ms_.get("steps")))
    nj = cmp_result(o["live"], m["live"], "live", diffs)
    orp, mrp = o["replay_player"], m["replay_player"]
    if orp == "same_as_live":
        if mrp != "same_as_live":
            diffs.append("replay_player: oracle=same_as_live model=%s" % ("differs" if isinstance(mrp, dict) else mrp))
    elif mrp == "same_as_live":
        diffs.append("replay_player: oracle=differs model=same_as_live")
    else:
        cmp_result(orp, mrp, "replay_player", diffs, live=False)
    return diffs, nj


def localise(diffs):
    """Coarse localisation of the first difference: beatmap / replay-decode / sim."""
    if not diffs:
        return None
    d = diffs[0]
    if d.startswith("input.hit_objects"):
        return "beatmap"
    if d.startswith("input.") or d.startswith("schedule.last_frame_time"):
        return "replay-decode"
    if d.startswith("schedule."):
        return "schedule/beatmap"
    return "sim (or beatmap fields; check `playable`)"


def cmd_run(a):
    os.makedirs(a.work, exist_ok=True)
    jobs = read_jobs(a.list)
    if a.limit:
        jobs = jobs[:a.limit]
    ores = run_oracle(jobs, a, a.work)
    out = open(os.path.join(a.work, "results.jsonl"), "w")
    stats = Counter()
    walls = []
    judg = 0
    rpn = 0
    for line in jobs:
        o = ores.get(line, {"error": "oracle: no output"})
        m = run_evaltest(line, a)
        rec = {"job": line, "tag": a.tag, "schedule": a.schedule, "wall": m["_wall"]}
        oerr, merr = "error" in o, ("rejected" in m or "error" in m)
        if oerr or merr:
            rec["oracle_error"] = o.get("error")
            rec["model_reject"] = m.get("rejected") or m.get("error")
            rec["status"] = "both_reject" if (oerr and merr) else ("oracle_error_only" if oerr else "model_reject_only")
        elif "_panic" in m:
            rec["status"] = "panic"
            rec["panic"] = m["_panic"]
        else:
            walls.append(m["_wall"])
            diffs, nj = compare(o, m)
            judg += nj
            rec["status"] = "match" if not diffs else "mismatch"
            rpn += isinstance(o.get("replay_player"), dict)
            rec["mods"] = [x["acronym"] for x in o["input"]["mods"]]
            rec["rp_compared"] = isinstance(o.get("replay_player"), dict)
            if diffs:
                rec["diffs"] = diffs[:8]
                rec["where"] = localise(diffs)
        stats[rec["status"]] += 1
        out.write(json.dumps(rec) + "\n")
        out.flush()
        if a.verbose or rec["status"] not in ("match", "both_reject"):
            print(rec["status"], line, (rec.get("diffs") or [rec.get("model_reject") or rec.get("oracle_error") or ""])[0][:300],
                  file=sys.stderr, flush=True)
    walls.sort()
    summ = {"tag": a.tag, "schedule": a.schedule, "jobs": len(jobs), **stats, "judgements_compared": judg,
            "replay_player_full_compared": rpn,
            "evaltest_wall_median_s": walls[len(walls) // 2] if walls else None,
            "evaltest_wall_mean_s": sum(walls) / len(walls) if walls else None}
    print(json.dumps(summ))
    with open(os.path.join(a.work, "summary.json"), "w") as f:
        json.dump(summ, f, indent=1)


def cmd_playable(a):
    """Adapter losslessness: compare evaltest --dump-playable with the oracle's --dump-playable (bit-exact on every
    key the adapter emits; oracle-only keys are counted)."""
    os.makedirs(a.work, exist_ok=True)
    jobs = read_jobs(a.list)
    if a.limit:
        jobs = jobs[:a.limit]
    ok = bad = skipped = 0
    keys_missing = Counter()
    pl = os.path.join(a.work, "oracle_playable")
    mpath = os.path.join(a.work, "model_playable.json")
    for c0 in range(0, len(jobs), a.chunk):
        chunk = jobs[c0:c0 + a.chunk]
        ores = run_oracle(chunk, a, a.work, extra=["--dump-playable", pl, "--no-judgements"])
        for idx, line in enumerate(chunk):
            opath = os.path.join(pl, "%d.json" % idx)   # oracle batch names dumps by job index
            o = ores.get(line, {})
            if os.path.exists(mpath):
                os.remove(mpath)
            m = run_evaltest(line, a, extra=["--dump-playable", mpath])
            if "error" in o or not os.path.exists(mpath) or not os.path.exists(opath):
                skipped += 1
                print("skip", line, o.get("error", "")[:100], (m.get("rejected") or m.get("error") or "")[:200],
                      file=sys.stderr, flush=True)
                continue
            od, md = json.load(open(opath)), json.load(open(mpath))
            diffs = []

            def walk(x, y, path):
                if isinstance(y, dict):
                    if not isinstance(x, dict):
                        diffs.append(path + " type")
                        return
                    for k in y:
                        if k not in x:
                            diffs.append(path + "." + k + " (not in oracle)")
                        else:
                            walk(x[k], y[k], path + "." + k)
                    for k in x:
                        if k not in y:
                            keys_missing[k] += 1
                elif isinstance(y, list):
                    if not isinstance(x, list) or len(x) != len(y):
                        diffs.append(path + " length %s vs %s" % (len(x) if isinstance(x, list) else "-", len(y)))
                    else:
                        for i, (p, q) in enumerate(zip(x, y)):
                            walk(p, q, "%s[%d]" % (path, i))
                elif x != y:
                    diffs.append("%s: oracle=%s model=%s" % (path, x, y))
            walk(od, md, "")
            if diffs:
                bad += 1
                print("MISMATCH", line, len(diffs), diffs[:6], file=sys.stderr, flush=True)
            else:
                ok += 1
            if not a.keep:
                os.remove(opath)
        print("%s playable: %d ok, %d mismatch, %d skipped" % (time.strftime("%H:%M:%S"), ok, bad, skipped),
              file=sys.stderr, flush=True)
    if os.path.exists(mpath):
        os.remove(mpath)
    summ = {"tag": a.tag, "playable_bit_exact": ok, "playable_mismatch": bad, "skipped": skipped,
            "oracle_keys_not_emitted": dict(keys_missing)}
    print(json.dumps(summ))


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest="cmd", required=True)
    j = sp.add_parser("jobs")
    j.add_argument("--corpus", choices=["stable", "v2"], required=True)
    j.add_argument("--limit", type=int, default=0)
    j.add_argument("--offset", type=int, default=0)
    j.add_argument("--sample", type=int, default=0)
    j.add_argument("--gen-mods", default=None, help="append random per-job mods (difftest/modgen_sim.py pool)")
    j.add_argument("--seed", type=int, default=1)
    for name in ["oracle", "run", "playable"]:
        p = sp.add_parser(name)
        p.add_argument("--list", required=True)
        p.add_argument("--schedule", default="catchup")
        p.add_argument("--mods", default=None)
        p.add_argument("--replace-mods", action="store_true")
        p.add_argument("--no-classic", action="store_true")
        p.add_argument("--chunk", type=int, default=150)
        p.add_argument("--limit", type=int, default=0)
        p.add_argument("--work", default=None)
        p.add_argument("--tag", default="")
        p.add_argument("-v", "--verbose", action="store_true")
        p.add_argument("--keep", action="store_true", help="playable: keep the oracle dumps")
    a = ap.parse_args()
    if a.cmd == "jobs":
        rows = jobs_stable() if a.corpus == "stable" else jobs_v2()
        if a.sample:
            random.Random(1234).shuffle(rows)
            rows = rows[:a.sample]
        rows = rows[a.offset:]
        if a.limit:
            rows = rows[:a.limit]
        if a.gen_mods:
            sys.path.insert(0, HERE)
            import modgen_sim
            rng = random.Random(a.seed)
            rows = [r + " " + json.dumps(modgen_sim.gen(rng, a.gen_mods), separators=(",", ":")) for r in rows]
        print("\n".join(rows))
    elif a.cmd == "oracle":
        import tempfile
        work = tempfile.mkdtemp(prefix="evalo-", dir=a.work or None)
        jobs = read_jobs(a.list)
        if a.limit:
            jobs = jobs[:a.limit]
        r = run_oracle(jobs, a, work)
        os.remove(os.path.join(work, "oracle_jobs.txt"))
        os.rmdir(work)
        print(json.dumps({"jobs": len(jobs), "results": len(r), "errors": sum("error" in d for d in r.values())}))
    elif a.cmd == "run":
        cmd_run(a)
    else:
        cmd_playable(a)


if __name__ == "__main__":
    main()
