#!/usr/bin/env python3
"""Automatic triage of oracle-vs-server mismatches on lazer scores (ISSUES G16, docs/server-agreement.md).

For every evaluated score whose oracle (catchup) result differs from the server, the cheapest explanations are tried
in order on the model (Lean evaltest playable dump + Rust Sim `simtest_rs`, falling back to the Lean simtest). Each
model run is gated: the unperturbed catchup run must reproduce the oracle's catchup statistics and pass/fail exactly,
otherwise the score is 'unverifiable'. "Exact" means the server's statistics (every HitResult count) and passed
flag are reproduced.

  1. replay-gap      no frames while >= 5 objects are due (incl. a late start)         -> demonstrated (data defect)
  2. note-lock       presses exactly at a circle/head's integer StartTime moved 1 ms earlier: a live press anywhere
                     in [t-0.5, t) is blocked by StartTimeOrderedHitPolicy (`time < StartTime`), the rounded one
                     at t is not                                                        -> demonstrated
  3. schedule        dense1ms (or perframe) reproduces the server                       -> demonstrated
  3b. same-frame-split  release+press frames at the same integer ms merged (RX writes both in one Update)
                     -> demonstrated
  4. spinner-alias   inter-frame spinner deltas > 120 deg against the spin direction (SpinnerRotationTracker
                     normalises to +-180) replaced by the true-direction midpoint      -> demonstrated
  (2-4 are also tried in combination: note-lock shifts x schedule x de-aliasing subsets.)
  5. press-shift     one key-down frame moved by +-1 ms (only for scores whose remaining difference involves circle
                     results or pass/fail)                                              -> reproduced by perturbation
                     (the deciding threshold is not localised inside the +-0.5 ms rounding interval)
  otherwise: remaining differences only in slider tails/ticks/repeats/spinner ticks -> heuristic-sched
             (the ordinary D13 class, not demonstrated); anything else -> suspicious.

Results go to difftest/server_demonstrated.json ("scores": {id: {category, mechanism, detail, ...}}); entries with
"source": "manual" are kept (they record analyses this script does not redo, e.g. tracking-trace margins).

Usage: python3 -I difftest/triage_v2.py [--new | --ids ID ...] [--max-shift-runs N]
"""
import argparse, bisect, collections, itertools, json, math, os, sqlite3, subprocess, sys, tempfile, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import oracle_vs_server_v2 as ov  # noqa: E402
import tail_margin as tm  # noqa: E402
from rounding_check import split_osr, perturb  # noqa: E402
from replay_gaps import object_times, worst_gap  # noqa: E402

ROOT = ov.ROOT
DEMO = os.path.join(ROOT, "difftest", "server_demonstrated.json")
# a pinned copy can be supplied via TRIAGE_EVALTEST (the build dir binary disappears while other agents relink it);
# every run is gated against the oracle anyway
# Default: pinned copies in data/oracle_v2/pinned/ if present (refresh with `cp -p` when the sims gain features),
# else the live build outputs. Env vars TRIAGE_{EVALTEST,SIMTEST_RS,SIMTEST_LEAN} override.
PINNED = os.path.join(ROOT, "data", "oracle_v2", "pinned")


def _bin(env, name, live):
    if os.environ.get(env):
        return os.environ[env]
    p = os.path.join(PINNED, name)
    return p if os.path.exists(p) else live


EVALTEST = _bin("TRIAGE_EVALTEST", "evaltest", os.path.join(ROOT, "model", ".lake", "build", "bin", "evaltest"))
SIMTEST_RS = _bin("TRIAGE_SIMTEST_RS", "simtest_rs", os.path.join(ROOT, "impl", "target", "release", "simtest_rs"))
SIMTEST_LEAN = _bin("TRIAGE_SIMTEST_LEAN", "simtest", os.path.join(ROOT, "model", ".lake", "build", "bin", "simtest"))
ENV = os.path.join(ROOT, "difftest", "env-1024x768.json")
SHIFT_BUDGET_S = float(os.environ.get("TRIAGE_SHIFT_BUDGET_S", "300"))
SCHED_ONLY = {"SliderTailHit", "IgnoreMiss", "IgnoreHit", "LargeTickHit", "LargeTickMiss", "SmallTickHit", "SmallTickMiss",
              "SmallBonus", "LargeBonus"}


def load_demo():
    try:
        d = json.load(open(DEMO))
    except Exception:
        d = {}
    if "scores" in d:
        return d
    # migrate the hand-written v1 file (id -> text, "weak": {...})
    out = {"version": 2, "scores": {}}
    for k, v in d.items():
        if k == "weak":
            for k2, v2 in v.items():
                out["scores"][k2] = {"category": "perturbation", "mechanism": "press-shift", "detail": v2, "source": "manual"}
        else:
            out["scores"][k] = {"category": "demonstrated", "mechanism": "manual", "detail": v, "source": "manual"}
    return out


def save_demo(d):
    with open(DEMO + ".part", "w") as f:
        json.dump(d, f, indent=1, sort_keys=True)
    os.replace(DEMO + ".part", DEMO)


class Model:
    def __init__(self, sid, s, bp, tmp):
        self.sid, self.s, self.bp, self.tmp = sid, s, bp, tmp
        self.mods = s.get("mods", [])
        self.playable = os.path.join(tmp, "%d.playable.json" % sid)
        self.fpath = os.path.join(tmp, "%d.frames.txt" % sid)
        self.runner = SIMTEST_RS
        self.runs = 0

    def make_playable(self):
        p = subprocess.run([EVALTEST, os.path.join(ROOT, self.bp), os.path.join(ROOT, "data/replays_v2/%d.osr" % self.sid),
                            "--no-judgements", "--dump-playable", self.playable], capture_output=True, text=True)
        return p.returncode == 0 and os.path.exists(self.playable)

    def run(self, frames, sched="catchup", judgements=False):
        with open(self.fpath, "w") as f:
            f.write(frames)
        self.runs += 1
        p = subprocess.run([self.runner, "--playable", self.playable, "--frames", self.fpath, "--env", ENV,
                            "--schedule", sched, "--mods-json", json.dumps(self.mods), "--lazer-replay"],
                           capture_output=True, text=True)
        if p.returncode != 0:
            return None
        d = json.loads(p.stdout)
        r = {"stats": d["statistics"], "failed": d["live"]["failed"], "total_score": d["live"]["total_score"],
             "max_combo": d["live"]["max_combo"]}
        if judgements:
            r["judgements"] = d["judgements"]
        return r


def exact(r, srv, passed):
    return r is not None and r["stats"] == srv and (not r["failed"]) == bool(passed)


def diff(r, srv):
    return {k: r["stats"].get(k, 0) - srv.get(k, 0) for k in set(r["stats"]) | set(srv) if r["stats"].get(k, 0) != srv.get(k, 0)}


def key_downs(frames_text):
    t, prev, out = 0, 0, []
    for f in frames_text.split(","):
        p = f.split("|")
        if len(p) < 4 or p[0] == "-12345":
            continue
        t += int(float(p[0]))
        k = int(p[3])
        if k & ~prev & 3:
            out.append(t)
        prev = k
    return out


def merge_same_time(frames_text):
    """Drop every key-up frame (no button) that directly follows a key-down state and is followed by a key-down frame
    at the same integer ms; returns (frames_text, number dropped)."""
    rows, t = [], 0
    for f in frames_text.split(","):
        p = f.split("|")
        if len(p) < 4:
            continue
        if p[0] == "-12345":
            rows.append([None, p])
            continue
        t += int(float(p[0]))
        rows.append([t, p])
    keep, n, prevk = [], 0, 0
    for k, (t, p) in enumerate(rows):
        if t is not None and k + 1 < len(rows) and rows[k + 1][0] == t and int(p[3]) & 3 == 0 and int(rows[k + 1][1][3]) & 3 \
                and prevk & 3:
            n += 1
            continue
        keep.append([t, p])
        if t is not None:
            prevk = int(p[3])
    out, prev = [], 0
    for t, p in keep:
        if t is None:
            out.append("|".join(p))
            continue
        out.append("%d|%s" % (t - prev, "|".join(p[1:])))
        prev = t
    return ",".join(out) + ",", n


def circle_starts(P):
    out = []
    for o in P["objects"]:
        if o["kind"] == "circle":
            out.append(tm.hx(o["start"]))
        elif o["kind"] == "slider":
            for n in o["nested"]:
                if n["kind"] == "head":
                    out.append(tm.hx(n["start"]))
    return sorted(out)


def dealias_variants(frames_text, P, max_cands=3):
    """Per spinner: wrong-sign |delta| > 120 deg intervals; returns list of (description, frames) for each subset."""
    rows, t = [], 0
    for f in frames_text.split(","):
        p = f.split("|")
        if len(p) < 4:
            continue
        if p[0] == "-12345":
            rows.append([None] + p)
            continue
        t += int(float(p[0]))
        rows.append([t] + p)
    cands = []
    for o in P["objects"]:
        if o["kind"] != "spinner":
            continue
        s, e = tm.hx(o["start"]), tm.hx(o["end"])
        cx, cy = (tm.hx(v) for v in o["stacked"])
        last, ds = None, []
        for k, r in enumerate(rows):
            if r[0] is not None and s <= r[0] <= e and int(r[4]):
                a = math.degrees(math.atan2(float(r[3]) - cy, float(r[2]) - cx))
                rad = math.hypot(float(r[2]) - cx, float(r[3]) - cy)
                if last is not None:
                    d = a - last[1]
                    d -= 360 if d > 180 else 0
                    d += 360 if d < -180 else 0
                    ds.append((k, d, last, rad, cx, cy))
                last = (r[0], a, rad)
        tot = sum(x[1] for x in ds)
        sgn = -1 if tot < 0 else 1
        c = [x for x in ds if x[1] * sgn < -120]
        c.sort(key=lambda x: -abs(x[1]))
        cands += [(x, sgn) for x in c[:max_cands]]
    out = []
    subsets = [(c,) for c in cands] + ([tuple(cands)] if len(cands) > 1 else [])
    for n in (1,):
        for sub in subsets:
            ins = {}
            for (k, d, last, rad, cx, cy), sgn in sub:
                r = rows[k]
                tmid = (last[0] + r[0]) // 2
                if tmid <= last[0] or tmid >= r[0]:
                    continue
                am = math.radians(last[1] + (d + 360 * sgn) / 2)
                rm = (rad + last[2]) / 2
                ins[k] = (tmid, repr(cx + rm * math.cos(am)), repr(cy + rm * math.sin(am)), r[4])
            if not ins:
                continue
            o2, prev = [], 0
            for k, r in enumerate(rows):
                if k in ins:
                    x = ins[k]
                    o2.append("%d|%s|%s|%s" % (x[0] - prev, x[1], x[2], x[3]))
                    prev = x[0]
                if r[0] is None:
                    o2.append("|".join(r[1:]))
                    continue
                o2.append("%d|%s|%s|%s" % (r[0] - prev, r[2], r[3], r[4]))
                prev = r[0]
            out.append(("de-aliased %d spinner delta(s) at %s" % (len(ins), sorted(rows[k][0] for k in ins)), ",".join(o2) + ","))
        if len(out) > 15:
            break
    return out


def triage(sid, s, bp, oracle_line, max_shift_runs, tmp):
    srv = {ov.camel(k): v for k, v in s["statistics"].items() if v}
    passed = s.get("passed", True)
    _, frames, _ = split_osr(open(os.path.join(ROOT, "data/replays_v2/%d.osr" % sid), "rb").read())
    res = {"triaged_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "source": "triage_v2"}
    # 1. replay gap (no model run needed)
    g = worst_gap(frames, object_times(os.path.join(ROOT, bp)))
    if g[2] >= 5:
        res.update(category="demonstrated", mechanism="replay-gap",
                   detail="no replay frames in [%d, %d] while %d objects were due (data defect)" % g)
        return res
    m = Model(sid, s, bp, tmp)
    if not m.make_playable():
        res.update(category="unverifiable", mechanism="model-playable-failed", detail="evaltest --dump-playable failed")
        return res
    try:
        if "live" not in oracle_line:  # oracle error line (e.g. lazer threw/OOM on this input)
            res.update(category="unverifiable", mechanism="oracle-error", detail=str(oracle_line.get("error"))[:200])
            return res
        L = oracle_line["live"]
        gate = m.run(frames, judgements=True)
        if gate is None or gate["stats"] != L["statistics"] or gate["failed"] != L["failed"]:
            m.runner = SIMTEST_LEAN
            gate = m.run(frames, judgements=True)
        if gate is None or gate["stats"] != L["statistics"] or gate["failed"] != L["failed"]:
            res.update(category="unverifiable", mechanism="sim-mismatch", detail="model catchup run does not reproduce the oracle")
            return res
        res["sim"] = "rust" if m.runner == SIMTEST_RS else "lean"
        slow = m.runner != SIMTEST_RS  # Lean simtest is ~20x slower: reduced search
        n_single = 3 if slow else 40
        if slow:
            max_shift_runs = min(max_shift_runs, 40)
        if os.path.getsize(m.playable) > 6e6:  # marathon maps (one dense1ms run takes minutes): no single-shift searches
            n_single, max_shift_runs = 0, 0
            res["reduced_search"] = True
        P = json.load(open(m.playable))
        starts = circle_starts(P)
        sset = set(starts)
        rx = any(x.get("acronym") == "RX" for x in m.mods)
        # 2-4, cheapest first; every run also tracks the closest variant for step 5
        best = [sum(abs(v) for v in diff(gate, srv).values()) + (0 if (not gate["failed"]) == bool(passed) else 100), "catchup", ""]
        bases = {"": frames}

        def attempt(desc, fb, sched, mech):
            r = m.run(fb, sched)
            if exact(r, srv, passed):
                # extra evidence: total_score/max_combo also depend on the ORDER of results (combo), not only counts
                res["score_exact"] = r["total_score"] == s.get("total_score") and r["max_combo"] == s.get("max_combo")
                res.update(category="demonstrated", mechanism=mech,
                           detail="; ".join(x for x in (desc, "" if sched == "catchup" else "%s schedule" % sched) if x) + " -> exact server statistics")
                return True
            if r is not None:
                sc = sum(abs(v) for v in diff(r, srv).values()) + (0 if (not r["failed"]) == bool(passed) else 100)
                if sc < best[0]:
                    best[:] = [sc, sched, desc]
                    bases[desc] = fb
            return False
        # 2. note-lock / integer-ms rounding: presses exactly at a circle's integer StartTime
        nl = sorted({t for t in key_downs(frames) if t in sset})
        nl_all = None
        if nl:
            # single shifts under catchup and dense1ms (a note-lock flip often coexists with schedule-sensitive
            # tails, e.g. HRNF 7737788341: one shift + dense1ms is exact, neither alone)
            t_nl = time.time() + SHIFT_BUDGET_S
            for sched in ("catchup", "dense1ms"):
                for t in nl[:n_single]:
                    if time.time() > t_nl:
                        break
                    f1, mv = perturb(frames, [t], 1.0)
                    if mv and attempt("note-lock: press at %d (= a circle StartTime) moved 1 ms earlier" % t, f1, sched, "note-lock"):
                        return res
            nl_all, mv = perturb(frames, nl, 1.0)
            d_all = "note-lock: %d press(es) exactly at a circle StartTime moved 1 ms earlier (%s)" % (mv, nl[:8])
            if mv > 1 and attempt(d_all, nl_all, "catchup", "note-lock"):
                return res
        # 3. schedules
        for sched in ("dense1ms", "perframe"):
            if attempt("", frames, sched, "schedule"):
                return res
        if nl_all is not None and attempt(d_all, nl_all, "dense1ms", "note-lock"):
            return res
        # 3b. same-live-frame key changes split by playback: a release frame followed by a press frame at the same
        # integer ms (Relax writes changeState(false); changeState(true) in ONE OsuModRelax.Update, before the DHOs
        # update in that frame; playback runs one frame-stable step per frame, so DHO updates such as a note-lock
        # blocker's expiry run in between). Merged = the release frame dropped (CLNFRX 7737904051).
        fm, nm = merge_same_time(frames)
        if nm:
            for sched in ("catchup", "dense1ms"):
                if attempt("same-frame split: %d same-ms release+press pairs merged%s" % (nm, " (RX)" if rx else ""), fm, sched,
                           "same-frame-split"):
                    return res
        # 4. spinner de-aliasing (singles and all-at-once), catchup and dense1ms
        for d2, fa in dealias_variants(frames, P):
            for sched in ("catchup", "dense1ms"):
                if attempt(d2, fa, sched, "spinner-alias"):
                    return res
        # 5. single press +-1 ms (only if circles or pass/fail still differ)
        sched = best[1]
        fb = bases.get(best[2], frames)
        rb = m.run(fb, sched)
        rem = diff(rb, srv) if rb else {}
        circle_or_fail = any(k not in SCHED_ONLY for k in rem) or (rb is not None and (not rb["failed"]) != bool(passed))
        # Classic slider judgement (CL): the Slider object itself is judged Great/Ok/Meh from the fraction of hit
        # nested objects, so one schedule-sensitive tail/tick flip also moves a Great<->Ok(<->Meh). Such a residual
        # stays schedule-only if no Miss changes, the Great/Ok/Meh deltas cancel and are covered by tick/tail flips.
        if circle_or_fail and rb is not None and (not rb["failed"]) == bool(passed) and \
                any(o["kind"] == "slider" and o.get("classic") for o in P["objects"]):
            cr = {k: v for k, v in rem.items() if k not in SCHED_ONLY}
            flips = sum(abs(rem.get(k, 0)) for k in ("SmallTickHit", "LargeTickHit", "SliderTailHit"))
            if set(cr) <= {"Great", "Ok", "Meh"} and sum(cr.values()) == 0 and abs(cr.get("Great", 0)) + abs(cr.get("Meh", 0)) <= flips:
                circle_or_fail = False
                res["classic_slider_results"] = cr
        res["remaining_diff"] = rem
        res["best_variant"] = {"schedule": sched, "base": best[2]}
        if circle_or_fail:
            downs = key_downs(fb)

            def near(t):
                q = bisect.bisect_left(starts, t)
                return any(0 <= z < len(starts) and abs(starts[z] - t) <= 400 for z in (q - 1, q))
            # most promising first: presses near circles that the gate run did not judge Great, and presses sharing
            # their integer ms with other frames (collapsed sub-ms key sequences)
            bad = sorted(tm.hx(P["objects"][j["i"]]["start"] if j["n"] < 0 else P["objects"][j["i"]]["nested"][j["n"]]["start"])
                         for j in gate["judgements"] if j["type"] in ("HitCircle", "SliderHeadCircle") and j["result"] != "Great")
            mult = collections.Counter()
            tt_ = 0
            for f in fb.split(","):
                q = f.split("|")
                if len(q) >= 4 and q[0] != "-12345":
                    tt_ += int(float(q[0]))
                    mult[tt_] += 1

            def prio(t):
                z = bisect.bisect_left(bad, t)
                dmin = min([abs(bad[w] - t) for w in (z - 1, z) if 0 <= w < len(bad)] or [1e9])
                return (0 if mult[t] > 1 else 1, dmin)
            cand = sorted((t for t in downs if near(t)), key=prio)
            n0 = m.runs
            t_end = time.time() + SHIFT_BUDGET_S  # wall-clock budget: long maps x dense1ms take ~1 min per run on the loaded VM
            for t in cand:
                for d in (1.0, -1.0):
                    if m.runs - n0 >= max_shift_runs or time.time() > t_end:
                        break
                    f2, mv = perturb(fb, [t], d)
                    if not mv:
                        continue
                    r = m.run(f2, sched)
                    if exact(r, srv, passed):
                        res["score_exact"] = r["total_score"] == s.get("total_score") and r["max_combo"] == s.get("max_combo")
                        res.update(category="perturbation", mechanism="press-shift",
                                   detail="%s%s schedule; press at %d shifted by %+d ms -> exact server statistics (threshold not localised)" % (
                                       (best[2] + "; ") if best[2] else "", sched, t, -d))
                        return res
            res["press_shift_runs"] = m.runs - n0
            res.update(category="suspicious", mechanism="none",
                       detail="circle results or pass/fail still differ after note-lock, schedules, de-aliasing and %d single-press shifts" % (m.runs - n0))
            return res
        res.update(category="heuristic-sched", mechanism="none",
                   detail="remaining differences only in slider tails/ticks/spinner ticks (%s), not flipped by dense1ms/perframe" % rem)
        return res
    finally:
        for p in (m.playable, m.fpath):
            if os.path.exists(p):
                os.remove(p)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ids", type=int, nargs="*")
    ap.add_argument("--new", action="store_true", help="only scores without a triage entry")
    ap.add_argument("--retriage", action="store_true", help="also redo existing triage_v2 entries")
    ap.add_argument("--max-shift-runs", type=int, default=600)
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--dry-run", action="store_true", help="print results, do not write server_demonstrated.json "
                    "(also triages manual entries: used to check the pipeline against hand-made demonstrations)")
    a = ap.parse_args()
    if not a.dry_run:
        import fcntl
        lockf = open(os.path.join(ov.OUT, "triage.lock"), "w")
        try:
            fcntl.flock(lockf, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError:
            print("triage already running", file=sys.stderr)
            return
    db = sqlite3.connect(ov.DB, timeout=60)
    meta = {sid: (json.loads(js), bp) for sid, js, bp in db.execute("select id, json, beatmap_path from scores where status='ok'")}
    cu = ov.load_results("catchup")
    demo = load_demo()
    todo = []
    for sid, o in sorted(cu.items()):
        if sid not in meta or (a.ids and sid not in a.ids):
            continue
        cat = ov.compare(o, meta[sid][0])[0]
        if cat == "exact":
            continue
        e = demo["scores"].get(str(sid))
        if e and not a.dry_run and (e.get("source") == "manual" or not a.retriage):
            continue
        todo.append(sid)
    if a.limit:
        todo = todo[:a.limit]
    print("triage: %d scores" % len(todo), file=sys.stderr, flush=True)
    tmp = tempfile.mkdtemp(prefix="triage_", dir=ov.OUT)
    counts = collections.Counter()
    try:
        for k, sid in enumerate(todo):
            s, bp = meta[sid]
            t0 = time.time()
            r = triage(sid, s, bp, cu[sid], a.max_shift_runs, tmp)
            r["mods"] = ov.modkey(s.get("mods", []))
            counts[r["category"]] += 1
            if a.dry_run:
                print(json.dumps({"id": sid, **r}))
            else:
                # re-read before writing: manual entries may have been added while this (long) run was going
                demo = load_demo()
                if demo["scores"].get(str(sid), {}).get("source") != "manual":
                    demo["scores"][str(sid)] = r
                    save_demo(demo)
            print("%s [%d/%d] %d %s: %s %s (%.0fs)" % (time.strftime("%H:%M:%S"), k + 1, len(todo), sid, r["mods"], r["category"],
                                                    r["mechanism"], time.time() - t0), file=sys.stderr, flush=True)
    finally:
        try:
            os.rmdir(tmp)
        except OSError:
            pass
    print(json.dumps(dict(counts)))


if __name__ == "__main__":
    main()
