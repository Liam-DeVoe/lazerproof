#!/usr/bin/env python3
"""Trace slider Tracking along the whole slider for disputed tails (docs/server-agreement.md).

Uses the Rust Sim (impl/target/release/tracktrace, a debugging bin of simtest_rs; bit-exact port of the Lean
model, which is diff-tested against the oracle). Inputs: the oracle's playable dump (data/oracle_v2/playable, mods
applied), the replay's frame text and difftest/env-1024x768.json. Every run is first validated judgement-by-judgement
(object, nested index, type, result) against the oracle's own catchup / dense1ms results (data/oracle_v2/*_obj.jsonl).
Only validated runs are analysed.

For every disputed tail it looks at the last time before the tail at which Tracking (SliderInputManager.updateTracking)
became false. It reports
  cause   = 'cursor' (left the 2.4r follow area with a valid key held), 'key' (no valid tracking action: released,
            or only the non-head key held while strict), or 'both';
  margin  = largest excursion (osu!px) of the interpolated cursor outside 2.4r between the last Tracking step and the
            window start (cursor causes),
  regain  = min over [loss, tail end] of (distance - r) while a valid key was held, on a 0.25 ms grid of the
            interpolated cursor (Tracking can only restart inside r);
  keygap  = for key causes, ms between the key change and the neighbouring frame (sub-frame timing).
A tail counts as live-flippable if a plausible sub-frame difference flips it: margin <= 3 px, or regain <= 3 px, or
a key cause where the release/press lies within one frame interval (<= 17 ms) of a step that would keep or restore
Tracking. Each score's tail deficit is then compared with its number of flippable tails.

Scores whose mods need sim-side support beyond NF/CL (rate mods, AP, GR, ...) run on the Lean simtest
(model/.lake/build/bin/simtest --trace-tracking, M5-M7), all others on the Rust Sim. Both are validated against the oracle.

Usage: python3 -I difftest/tracking_trace.py [IDS...]   (default: the unexplained scores of the flip check)
"""
import json, math, os, struct, subprocess, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import oracle_vs_server_v2 as ov  # noqa: E402
import tail_margin as tm  # noqa: E402
from rounding_check import split_osr  # noqa: E402

ROOT = ov.ROOT
TT = os.path.join(ROOT, "impl", "target", "release", "tracktrace")
ENV = os.path.join(ROOT, "difftest", "env-1024x768.json")
TMP = os.environ.get("TT_TMP", "/tmp/tracktrace_v2")


def run_tt(sid, sched, mods):
    os.makedirs(TMP, exist_ok=True)
    fp = os.path.join(TMP, "%d.txt" % sid)
    if not os.path.exists(fp):
        _, fr, _ = split_osr(open(os.path.join(ROOT, "data/replays_v2/%d.osr" % sid), "rb").read())
        open(fp, "w").write(fr)
    p = subprocess.run([TT, "--playable", os.path.join(ov.OUT, "playable", "%d.json" % sid), "--frames", fp, "--env", ENV,
                        "--schedule", sched, "--mods", ",".join(mods), "--lazer-replay"], capture_output=True, text=True)
    if p.returncode != 0:
        return None
    return json.loads(p.stdout)


SIMTEST = os.path.join(ROOT, "model", ".lake", "build", "bin", "simtest")


def run_lean(sid, sched, mods_json):
    """Lean simtest (M5 rate/fail mods, M6 input mods incl. AP, M7 transform mods) with --trace-tracking; returns the
    same structure as run_tt (times decoded from IEEE bits)."""
    os.makedirs(TMP, exist_ok=True)
    fp = os.path.join(TMP, "%d.txt" % sid)
    if not os.path.exists(fp):
        _, fr, _ = split_osr(open(os.path.join(ROOT, "data/replays_v2/%d.osr" % sid), "rb").read())
        open(fp, "w").write(fr)
    trf = os.path.join(TMP, "%d.%s.trace" % (sid, sched))
    p = subprocess.run([SIMTEST, "--playable", os.path.join(ov.OUT, "playable", "%d.json" % sid), "--frames", fp, "--env", ENV,
                        "--schedule", sched, "--mods-json", json.dumps(mods_json), "--lazer-replay", "--trace-tracking", trf],
                       capture_output=True, text=True)
    if p.returncode != 0:
        return None
    d = json.loads(p.stdout)
    bits = lambda h: struct.unpack("<d", struct.pack("<Q", int(h, 16) if isinstance(h, str) and h.startswith("0x") else int(h)))[0]
    out = {"judgements": [[j["i"], j["n"], j["type"], j["result"], bits(j["time"])] for j in d["judgements"]],
           "statistics": d["statistics"], "tracking": {}}
    for line in open(trf):
        q = line.split()
        if len(q) < 10:
            continue
        i, t = q[0], bits(q[1])
        tf = lambda x: x == "true"
        out["tracking"].setdefault(i, []).append([t, tf(q[2]), tf(q[3]), tf(q[4]), tf(q[5]), int(q[6]), int(q[7]),
                                                  None if q[8] == "-" else bits(q[8]), q[9]])
    os.remove(trf)
    return out


def validate(tt, oracle_line):
    a = [(j[0], j[1], j[2], j[3]) for j in tt["judgements"]]
    b = [tuple(x) for x in oracle_line["live"]["objres"]]
    return a == b


def dist_minus(P, i, cur, t, mult):
    s = P["objects"][i]
    start, dur = tm.hx(s["start"]), tm.hx(s["duration"])
    sx, sy = (tm.hx(v) for v in s["stacked"])
    r = tm.hx(s["radius"])
    cx, cy, keys = cur.at(t)
    px, py = tm.curve_pos(s, min(max((t - start) / dur, 0), 1) if dur > 0 else 0)
    return math.hypot(cx - (sx + px), cy - (sy + py)) - mult * r, keys


def analyse_tail(sid, i, n, P, cur, trace, frame_times):
    tail_t = tm.hx(P["objects"][i]["nested"][n]["start"])
    kind = P["objects"][i]["nested"][n]["kind"]
    # tail: judged at the first step >= start-36 with Tracking (TAIL_LENIENCY); tick/repeat: first step >= start
    ws = tail_t - 36 if kind == "tail" else tail_t
    tr = [e for e in trace if e[0] <= tail_t]
    if not tr:
        return {"tail": [i, n], "cause": "no-trace"}
    # last transition True -> False before/inside the window
    loss, prev = None, None
    for e in tr:
        if prev is not None and prev[1] and not e[1]:
            loss = (prev, e)
        prev = e
    ever = any(e[1] for e in tr)
    res = {"tail": [i, n], "kind": kind, "tail_time": tail_t, "ever_tracking": ever}
    if not ever:
        res["cause"] = "never-tracked"
        t0 = tm.hx(P["objects"][i]["start"])
    else:
        if loss is None:
            res["cause"] = "tracking-until-end?"
            return res
        before, e = loss
        t0 = e[0]
        in_big_before_ok = e[3]
        valid = e[4]
        res["loss_time"] = t0
        res["loss_rel_window"] = round(t0 - ws, 2)
        res["cause"] = "both" if (not in_big_before_ok and not valid) else ("cursor" if not in_big_before_ok else "key")
        if not in_big_before_ok:
            # Tracking (expanded radius 2.4r) would have had to survive from the last tracking step until a step at or
            # after the window start: the largest excursion of the interpolated cursor outside 2.4r over
            # [last tracking step, window start] is the margin by which it was lost
            t, mx = before[0], -math.inf
            while t <= max(ws, before[0]):
                m, _ = dist_minus(P, i, cur, t, 2.4)
                mx = max(mx, m)
                t += 0.25
            m_ws, _ = dist_minus(P, i, cur, ws, 2.4)
            res["margin_at_window_start"] = round(max(mx, m_ws), 2)
            # when did the interpolated cursor last cross out of 2.4r before the window start (ms before ws)?
            t, last_out = before[0], None
            inside_prev = dist_minus(P, i, cur, t, 2.4)[0] <= 0
            while t <= ws:
                ins = dist_minus(P, i, cur, t, 2.4)[0] <= 0
                if inside_prev and not ins:
                    last_out = t
                inside_prev = ins
                t += 0.25
            if last_out is not None:
                res["exit_ms_before_window"] = round(ws - last_out, 2)
            # cursor still inside 2.4r at ws: how long after ws until it leaves (a live step in that interval hits the
            # tail); P(hit) at a live framerate f with random phase = min(1, interval * f / 1000)
            if m_ws <= 0 and mx <= 0:
                t = ws
                while t <= tail_t and dist_minus(P, i, cur, t, 2.4)[0] <= 0:
                    t += 0.05
                res["inside_ms_after_window_start"] = round(t - ws, 2)
                for fps in (240, 1000):
                    res["p_hit_%dfps" % fps] = round(min(1.0, (t - ws) * fps / 1000), 2)
        if not valid:
            # key change times near the loss
            k = min(range(len(frame_times)), key=lambda q: abs(frame_times[q][0] - t0))
            res["key_event_near_loss"] = [(round(frame_times[q][0] - t0, 2), frame_times[q][3]) for q in range(max(0, k - 2), min(len(frame_times), k + 3))]
    # regain possibility: min (dist - r) while a key is held over [t0, tail end]
    best = math.inf
    t = t0
    while t <= tail_t:
        m, keys = dist_minus(P, i, cur, t, 1.0)
        if keys:
            best = min(best, m)
        t += 0.25
    res["regain_margin_r"] = round(best, 2) if best < math.inf else None
    return res


def main():
    import sqlite3
    db = sqlite3.connect(ov.DB)
    meta = {sid: json.loads(js) for sid, js in db.execute("select id, json from scores where status='ok'")}
    names = list(ov.FLIP_SCHEDULES) + sorted(f[:-len("_obj.jsonl")] for f in os.listdir(ov.OUT) if f.startswith("jitter") and f.endswith("_obj.jsonl"))
    res = {nm: ov.load_results(nm + "_obj") for nm in names}
    ids = [int(x) for x in sys.argv[1:]]
    if not ids:
        for sid in sorted(res["catchup"]):
            runs = {nm: res[nm][sid] for nm in names if sid in res[nm]}
            if sid in meta and ov.compare(runs["catchup"], meta[sid])[0] not in ("exact", "replay-gap") and \
                    ov.flipcheck_one(meta[sid], runs)["status"] == "NOT-demonstrated":
                ids.append(sid)
    summary = []
    for sid in ids:
        s = meta[sid]
        mods = [m["acronym"] for m in s.get("mods", [])]
        sim_mods = [m for m in mods if m in ("NF", "CL")]
        rec = {"id": sid, "mods": ov.modkey(s.get("mods", []))}
        # the Rust port has NF/CL only; anything with sim-side mods (rate, AP, transform mods) goes to the Lean simtest
        use_lean = bool(set(mods) - {"NF", "CL", "DA", "HR", "EZ", "HD", "MR", "RD", "SO", "TD"}) or os.environ.get("TT_LEAN")
        rec["sim"] = "lean" if use_lean else "rust"
        tts = {}
        for sch in ("catchup", "dense1ms"):
            tt = run_lean(sid, sch, s.get("mods", [])) if use_lean else run_tt(sid, sch, sim_mods)
            o = res[sch].get(sid)
            ok = tt is not None and o is not None and "objres" in o["live"] and validate(tt, o)
            tts[sch] = tt if ok else None
            rec["validated_" + sch] = ok
        if tts["catchup"] is None:
            rec["status"] = "sim does not reproduce the oracle (not analysed)"
            summary.append(rec)
            print(json.dumps(rec))
            continue
        P = json.load(open(os.path.join(ov.OUT, "playable", "%d.json" % sid)))
        fr = tm.frames_of(sid)
        cur = tm.Cursor(fr)
        jc = {(j[0], j[1]): j[3] for j in tts["catchup"]["judgements"]}
        jd = {(j[0], j[1]): j[3] for j in tts["dense1ms"]["judgements"]} if tts["dense1ms"] else {}
        tails = []
        for (i, n), r in jc.items():
            o = P["objects"][i]
            nk = o["nested"][n]["kind"] if n >= 0 else None
            if n >= 0 and ((nk == "tail" and r == "IgnoreMiss") or (nk in ("tick", "repeat") and r == "LargeTickMiss")) \
                    and jc.get((i, 0)) in ("Great", "Ok", "Meh") and jd.get((i, n), r) == r:
                a = analyse_tail(sid, i, n, P, cur, tts["catchup"]["tracking"].get(str(i), []), fr)
                fl = (a.get("cause") == "cursor" and a.get("margin_at_window_start") is not None and a["margin_at_window_start"] <= 3) or \
                     (a.get("regain_margin_r") is not None and a["regain_margin_r"] <= 3) or \
                     (a.get("cause") in ("key", "both") and a.get("loss_rel_window", -1e9) > -0.5)
                a["live_flippable"] = bool(fl)
                tails.append(a)
        # reverse direction (the oracle hit more than the server): tails/ticks HIT under both schedules whose hit
        # was marginal -- the cursor within 3 px of the 2.4r edge between the window start and the judging step
        rev = []
        jt = {(j[0], j[1]): j[4] for j in tts["catchup"]["judgements"]}
        for (i, n), r in jc.items():
            o = P["objects"][i]
            nk = o["nested"][n]["kind"] if n >= 0 else None
            if n >= 0 and ((nk == "tail" and r == "SliderTailHit") or (nk in ("tick", "repeat") and r == "LargeTickHit")) \
                    and jd.get((i, n), r) == r:
                tn = tm.hx(o["nested"][n]["start"])
                t0 = tn - 36 if nk == "tail" else tn
                t1 = max(jt[(i, n)], t0)
                t, best = t0, math.inf
                while t <= t1:
                    best = min(best, -dist_minus(P, i, cur, t, 2.4)[0])
                    t += 0.25
                if best <= 3:
                    rev.append({"obj": [i, n], "kind": nk, "inside_margin_px": round(best, 2)})
        rec["marginal_hits"] = {"tail": sum(1 for x in rev if x["kind"] == "tail"), "tick": sum(1 for x in rev if x["kind"] != "tail")}
        srv = {ov.camel(k): v for k, v in s["statistics"].items()}
        orc = tts["catchup"]["statistics"]
        rec["tail_deficit"] = srv.get("SliderTailHit", 0) - orc.get("SliderTailHit", 0)
        rec["tick_deficit"] = srv.get("LargeTickHit", 0) - orc.get("LargeTickHit", 0)
        rec["flippable_ticks"] = sum(t["live_flippable"] for t in tails if t["kind"] != "tail")
        rec["missed_tails_head_hit"] = len(tails)
        rec["flippable"] = sum(t["live_flippable"] for t in tails if t["kind"] == "tail")
        causes = {}
        for t in tails:
            causes[t.get("cause")] = causes.get(t.get("cause"), 0) + 1
        rec["causes"] = causes
        rec["tails"] = tails
        ok = rec["flippable"] >= max(rec["tail_deficit"], 0) and rec["flippable_ticks"] >= max(rec["tick_deficit"], 0) and \
            rec["marginal_hits"]["tail"] >= max(-rec["tail_deficit"], 0) and rec["marginal_hits"]["tick"] >= max(-rec["tick_deficit"], 0)
        msg = "tails %d/%d, ticks %d/%d flippable; oracle-only hits: tails %d/%d, ticks %d/%d marginal" % (
            rec["flippable"], max(rec["tail_deficit"], 0), rec["flippable_ticks"], max(rec["tick_deficit"], 0),
            rec["marginal_hits"]["tail"], max(-rec["tail_deficit"], 0), rec["marginal_hits"]["tick"], max(-rec["tick_deficit"], 0))
        other = sorted(k for k in set(srv) | set(orc) if srv.get(k, 0) != orc.get(k, 0) and k not in (
            "SliderTailHit", "IgnoreMiss", "IgnoreHit", "LargeTickHit", "LargeTickMiss"))
        if other:  # e.g. circle or spinner results: not addressed by this analysis
            ok = False
            msg += "; other results differ: " + ",".join(other)
        rec["status"] = ("deficits covered (%s)" if ok else "NOT covered (%s)") % msg
        summary.append(rec)
        print(json.dumps(rec))
    if not sys.argv[1:]:  # full run: read by oracle_vs_server_v2.py report (scores whose deficits are covered)
        json.dump(summary, open(os.path.join(ov.OUT, "tracking_summary.json"), "w"), indent=0)


if __name__ == "__main__":
    main()
