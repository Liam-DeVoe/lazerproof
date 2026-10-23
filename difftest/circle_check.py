#!/usr/bin/env python3
"""Circle-level oracle-vs-server mismatch triage (docs/server-agreement.md).

For a lazer score whose server statistics differ from the oracle on circle results (Great/Ok/Meh/Miss), this:
  1. runs the bit-exact Lean simtest (catchup, the score's own mods) and checks its statistics and per-type counts
     against the oracle's catchup result;
  2. for every HitCircle/SliderHeadCircle judgement, lists the key-down presses in [start - 400, start + 400]
     with the press's cursor distance to the object minus its radius (hit-area margin, px), its offset relative to
     the hit-window edges (OsuHitWindows: floor(x) - 0.5, miss window 400), and whether an earlier unjudged circle
     with a later StartTime could have note-locked it (StartTimeOrderedHitPolicy: blocked iff press < blocker.Start);
  3. reports the judgements whose outcome sits on such an edge (hit-area margin <= 1 px, window edge within 1 ms,
     press at a blocker's integer StartTime, or the miss-window edge), i.e. the candidates for the server difference.

Usage: python3 -I difftest/circle_check.py ID [ID...]
"""
import json, math, os, sqlite3, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import oracle_vs_server_v2 as ov  # noqa: E402
import tail_margin as tm  # noqa: E402
import tracking_trace as tt  # noqa: E402


def presses(fr):
    out, prev = [], 0
    for t, x, y, k in fr:
        if k & ~prev & 3:
            out.append((t, x, y, k & ~prev))
        prev = k
    return out


def analyse(sid):
    db = sqlite3.connect(ov.DB)
    s = json.loads(db.execute("select json from scores where id=?", (sid,)).fetchone()[0])
    tt.TMP = os.environ.get("TT_TMP", tt.TMP)
    sim = tt.run_lean(sid, "catchup", s.get("mods", []))
    o = ov.load_results("catchup")[sid]
    rep = {"id": sid, "mods": ov.modkey(s.get("mods", []))}
    if sim is None:
        rep["status"] = "sim failed"
        return rep, []
    sim_bt = {}
    for i, n, t, r, _ in sim["judgements"]:
        sim_bt.setdefault(t, {}).setdefault(r, 0)
        sim_bt[t][r] += 1
    rep["sim_matches_oracle"] = sim["statistics"] == o["live"]["statistics"] and sim_bt == o["live"].get("by_type")
    srv = {ov.camel(k): v for k, v in s["statistics"].items() if v}
    rep["diff_server_minus_oracle"] = {k: srv.get(k, 0) - o["live"]["statistics"].get(k, 0)
                                      for k in set(srv) | set(o["live"]["statistics"]) if srv.get(k, 0) != o["live"]["statistics"].get(k, 0)}
    P = json.load(open(os.path.join(ov.OUT, "playable", "%d.json" % sid)))
    fr = tm.frames_of(sid)
    pr = presses(fr)
    pt = [p[0] for p in pr]
    import bisect
    jt = {(i, n): (r, t) for i, n, ty, r, t in sim["judgements"]}
    circles = []
    for i, ob in enumerate(P["objects"]):
        if ob["kind"] == "circle":
            circles.append((i, -1, ob))
        elif ob["kind"] == "slider":
            for n, x in enumerate(ob["nested"]):
                if x["kind"] == "head":
                    circles.append((i, n, x))
    starts = sorted((tm.hx(c[2]["start"]), c[0], c[1]) for c in circles)
    cands = []
    for i, n, c in circles:
        st = tm.hx(c["start"])
        cx, cy = (tm.hx(v) for v in c["stacked"])
        r = tm.hx(c["radius"])
        hw = [tm.hx(w) for w in c["hit_windows"]]  # great, ok, meh, miss
        res, jtime = jt.get((i, n), (None, None))
        lo, hi = bisect.bisect_left(pt, st - 400), bisect.bisect_right(pt, st + 400)
        for t, x, y, k in pr[lo:hi]:
            off = t - st
            m = math.hypot(x - cx, y - cy) - r
            edges = [abs(abs(off) - w) for w in hw]
            # note lock: an earlier circle with StartTime in [t, st) still unjudged at t?
            lock = None
            for s2, i2, n2 in starts:
                if s2 >= st:
                    break
                r2, t2 = jt.get((i2, n2), (None, None))
                if t2 is not None and t2 >= t and t <= s2:
                    lock = (i2, n2, round(s2 - t, 3))
            flag = []
            # live-vs-replay differences can only come from quantities the replay changes: press times are rounded
            # to integer ms (positions are stored as shortest round-trip floats, but go through a gamefield<->screen
            # float round trip, so only float-level hit-area edges matter). Hit windows are floor(x) - 0.5, so no
            # integer offset is within 0.5 ms of them; the 400 ms miss window and blocker StartTimes are integers.
            if abs(m) < 0.05:
                flag.append("float-level hit-area edge %.5f px" % m)
            if m <= 0 and abs(abs(off) - 400) <= 0.5:
                flag.append("miss-window edge: |offset| %.2f vs 400" % abs(off))
            if lock and lock[2] == 0 and m <= 0:
                flag.append("note-lock edge: press exactly at blocker %s StartTime" % (lock[:2],))
            if flag:
                cands.append({"obj": [i, n], "result": res, "press_offset": round(off, 3), "hit_margin_px": round(m, 3),
                              "lock": lock, "flags": flag})
    rep["edge_candidates"] = len(cands)
    return rep, cands


def main():
    for sid in [int(x) for x in sys.argv[1:]]:
        rep, cands = analyse(sid)
        print(json.dumps(rep))
        for c in cands:
            print("   ", json.dumps(c))


if __name__ == "__main__":
    main()
