#!/usr/bin/env python3
"""Deterministic cursor-margin analysis for disputed slider tails/ticks/repeats (docs/server-agreement.md).

For each disputed nested object it measures, over the object's judgement window:
  (a) margin = min over t of |cursor(t) - followCentre(t)| - R, in osu!px. Cursor = the replay's frames linearly
      interpolated (OsuFramedReplayInputHandler.GetPosition). Centre = StackedPosition + Slider.CurvePositionAt(
      clamp((t - start) / duration)) (SliderInputManager.IsMouseInFollowArea). R = radius (r, not yet tracking) or
      2.4 r (FOLLOW_AREA, already tracking). Sampled on a 0.25 ms grid.
  (b) the fraction of the window with a key held,
  (c) the largest gap between replay frames that overlaps the window (ms).
Windows: tail [start + TAIL_LENIENCY(-36), start] (SliderInputManager.TryJudgeNestedObject); tick/repeat
[start, start + 1000/60] (judged at the first step at or after start).

Disputed objects:
  explained = objects whose result changes across the oracle schedules (flip-check runs *_obj.jsonl) in scores
              where the flip check reproduced the server counts;
  unexplained = in scores without a demonstrating flip: every tail/tick/repeat that missed under catchup (the server
              has 1-2 more hits among them). The k candidates with the smallest margin are reported, k = deficit.
Geometry comes from the oracle's --dump-playable (real lazer playable beatmap, mods applied). It is produced once
per score by an oracle batch run (catchup, no judgements) into data/oracle_v2/playable/.

Usage: python3 -I difftest/tail_margin.py [--ids FILE]   (default: every score in the flip-check sample)
"""
import argparse, bisect, fcntl, json, math, os, sqlite3, struct, subprocess, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import oracle_vs_server_v2 as ov  # noqa: E402
from rounding_check import split_osr  # noqa: E402

ROOT = ov.ROOT
PDIR = os.path.join(ov.OUT, "playable")


def hx(s):
    if isinstance(s, str) and s.startswith("0x"):
        b = int(s, 16)
        return struct.unpack("<d", struct.pack("<Q", b))[0] if len(s) == 18 else struct.unpack("<f", struct.pack("<I", b))[0]
    return s


def ensure_playable(ids):
    os.makedirs(PDIR, exist_ok=True)
    todo = [i for i in ids if not os.path.exists(os.path.join(PDIR, "%d.json" % i))]
    if not todo:
        return
    db = sqlite3.connect(ov.DB)
    lst = os.path.join(PDIR, "list.txt")
    with open(lst, "w") as f:
        for sid in todo:
            bp = db.execute("select beatmap_path from scores where id=?", (sid,)).fetchone()[0]
            f.write("%s %s\n" % (os.path.join(ROOT, bp), os.path.join(ROOT, "data/replays_v2/%d.osr" % sid)))
    tmp = os.path.join(PDIR, "tmp")
    os.makedirs(tmp, exist_ok=True)
    lockf = open(ov.LOCK, "w")
    fcntl.flock(lockf, fcntl.LOCK_EX)
    subprocess.run([ov.ORACLE, "batch", "--list", lst, "--no-judgements", "--dump-playable", tmp],
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, cwd=ROOT)
    for k, sid in enumerate(todo):
        src = os.path.join(tmp, "%d.json" % k)
        if os.path.exists(src):
            os.replace(src, os.path.join(PDIR, "%d.json" % sid))
    os.rmdir(tmp) if not os.listdir(tmp) else None
    os.remove(lst)


def frames_of(sid):
    _, text, _ = split_osr(open(os.path.join(ROOT, "data/replays_v2/%d.osr" % sid), "rb").read())
    t, out = 0.0, []
    for f in text.split(","):
        p = f.split("|")
        if len(p) < 4 or p[0] == "-12345":
            continue
        t += int(float(p[0]))
        out.append((t, float(p[1]), float(p[2]), int(p[3])))
    return out


class Cursor:
    def __init__(self, fr):
        self.fr = fr
        self.t = [f[0] for f in fr]

    def at(self, t):
        k = bisect.bisect_right(self.t, t) - 1
        if k < 0:
            return self.fr[0][1], self.fr[0][2], 0
        if k + 1 >= len(self.fr) or self.fr[k + 1][0] == self.fr[k][0]:
            return self.fr[k][1], self.fr[k][2], self.fr[k][3]
        a, b = self.fr[k], self.fr[k + 1]
        w = (t - a[0]) / (b[0] - a[0])
        return a[1] + (b[1] - a[1]) * w, a[2] + (b[2] - a[2]) * w, a[3]

    def max_gap(self, t0, t1):
        k0 = max(bisect.bisect_right(self.t, t0) - 1, 0)
        k1 = min(bisect.bisect_left(self.t, t1) + 1, len(self.t) - 1)
        return max((self.t[k + 1] - self.t[k] for k in range(k0, k1)), default=0.0)


def curve_pos(s, progress):
    spans = s["span_count"]
    p = progress * spans % 1
    if int(progress * spans) % 2 == 1:
        p = 1 - p
    path = s["path"]
    pts = [(hx(path[k]), hx(path[k + 1])) for k in range(0, len(path), 2)]
    cl = [hx(c) for c in s["cumulative_length"]]
    d = min(max(p, 0), 1) * hx(s["path_distance"])
    i = bisect.bisect_left(cl, d)
    if not pts:
        return 0.0, 0.0
    if i <= 0:
        return pts[0]
    if i >= len(pts):
        return pts[-1]
    d0, d1 = cl[i - 1], cl[i]
    if abs(d1 - d0) < 1e-3:
        return pts[i - 1]
    w = (d - d0) / (d1 - d0)
    return pts[i - 1][0] + (pts[i][0] - pts[i - 1][0]) * w, pts[i - 1][1] + (pts[i][1] - pts[i - 1][1]) * w


def analyse(sid, i, n, P, cur):
    s = P["objects"][i]
    nest = s["nested"][n]
    start, dur = hx(s["start"]), hx(s["duration"])
    sx, sy = (hx(v) for v in s["stacked"])
    r = hx(s["radius"])
    t_n = hx(nest["start"])
    if nest["kind"] == "tail":
        t0, t1 = t_n - 36, t_n
    else:
        t0, t1 = t_n, t_n + 1000 / 60
    best_small = best_big = math.inf
    held = tot = 0
    t = t0
    while t <= t1 + 1e-9:
        cx, cy, keys = cur.at(t)
        px, py = curve_pos(s, min(max((t - start) / dur, 0), 1) if dur > 0 else 0)
        dist = math.hypot(cx - (sx + px), cy - (sy + py))
        best_small = min(best_small, dist - r)
        best_big = min(best_big, dist - 2.4 * r)
        held += keys != 0
        tot += 1
        t += 0.25
    return {"id": sid, "obj": [i, n], "kind": nest["kind"], "margin_r": round(best_small, 2), "margin_2.4r": round(best_big, 2),
            "key_held_frac": round(held / max(tot, 1), 2), "max_frame_gap_ms": cur.max_gap(t0, t1), "radius": round(r, 2)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ids")
    ap.add_argument("--json")
    a = ap.parse_args()
    db = sqlite3.connect(ov.DB)
    meta = {sid: json.loads(js) for sid, js in db.execute("select id, json from scores where status='ok'")}
    names = list(ov.FLIP_SCHEDULES) + sorted(f[:-len("_obj.jsonl")] for f in os.listdir(ov.OUT) if f.startswith("jitter") and f.endswith("_obj.jsonl"))
    res = {nm: ov.load_results(nm + "_obj") for nm in names}
    ids = sorted(res["catchup"])
    if a.ids:
        want = {int(x.split()[0]) for x in open(a.ids) if x.strip()}
        ids = [i for i in ids if i in want]
    work = []
    for sid in ids:
        runs = {nm: res[nm][sid] for nm in names if sid in res[nm]}
        if sid not in meta or ov.compare(runs["catchup"], meta[sid])[0] in ("exact", "replay-gap"):
            continue
        st = ov.flipcheck_one(meta[sid], runs)["status"]
        work.append((sid, st, runs))
    ensure_playable([w[0] for w in work])
    rows = []
    for sid, st, runs in work:
        pth = os.path.join(PDIR, "%d.json" % sid)
        if not os.path.exists(pth):
            print("no playable dump for", sid, file=sys.stderr)
            continue
        P = json.load(open(pth))
        cur = Cursor(frames_of(sid))
        obs = {}
        for nm, o in runs.items():
            L = o["live"]
            if L.get("failed") or "objres" not in L:
                continue
            for i, n, t, r in L["objres"]:
                obs.setdefault((i, n, t), set()).add(r)
        cu = {(i, n): r for i, n, t, r in runs["catchup"]["live"]["objres"]}
        disputed_types = ("SliderTailCircle", "SliderTick", "SliderRepeat")
        if st.startswith("demonstrated"):
            cand = [(i, n) for (i, n, t), rs in obs.items() if t in disputed_types and len(rs) > 1]
            group = "explained"
        else:
            cand = [(i, n) for (i, n, t) in obs if t in disputed_types and cu.get((i, n)) in ("IgnoreMiss", "LargeTickMiss")]
            group = "unexplained"
        out = [analyse(sid, i, n, P, cur) for i, n in cand if n >= 0]
        if group == "unexplained":
            s = meta[sid]
            srv = {ov.camel(k): v for k, v in s["statistics"].items()}
            orc = runs["catchup"]["live"]["statistics"]
            deficit = max(1, srv.get("SliderTailHit", 0) - orc.get("SliderTailHit", 0) + srv.get("LargeTickHit", 0) - orc.get("LargeTickHit", 0))
            out = sorted(out, key=lambda d: d["margin_2.4r"])[:deficit] if out else []
        # control: tails/ticks HIT under catchup must have margin(2.4r) <= ~0 (validates the geometry code)
        hits = [(i, n) for (i, n, t) in obs if t in disputed_types and n >= 0 and cu.get((i, n)) in ("SliderTailHit", "LargeTickHit")]
        for i, n in hits[:: max(1, len(hits) // 10)][:10]:
            d = analyse(sid, i, n, P, cur)
            d.update(group="control-hit", mods=ov.modkey(meta[sid].get("mods", [])), flip_status=st)
            rows.append(d)
        for d in out:
            d.update(group=group, mods=ov.modkey(meta[sid].get("mods", [])), flip_status=st)
            rows.append(d)
            print(json.dumps(d))
    if a.json:
        json.dump(rows, open(a.json, "w"), indent=0)
    for g in ("control-hit", "explained", "unexplained"):
        R = [d for d in rows if d["group"] == g]
        if not R:
            continue
        ms = sorted(d["margin_2.4r"] for d in R)
        q = lambda f: ms[min(len(ms) - 1, int(f * len(ms)))]
        print("%s: n=%d  margin(2.4r) min %.2f median %.2f p90 %.2f max %.2f px; <=0: %d, <=3px: %d, >10px: %d; frame gap>16ms in window: %d; key held whole window: %d" % (
            g, len(R), ms[0], q(0.5), q(0.9), ms[-1], sum(m <= 0 for m in ms), sum(m <= 3 for m in ms), sum(m > 10 for m in ms),
            sum(d["max_frame_gap_ms"] > 16 for d in R), sum(d["key_held_frac"] == 1.0 for d in R)))


if __name__ == "__main__":
    main()
