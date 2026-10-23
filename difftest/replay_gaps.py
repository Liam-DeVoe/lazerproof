#!/usr/bin/env python3
"""Find lazer replays (data/replays_v2) with frame gaps that span hit objects. A gap with no frames while
objects are due means the replay lost input (the recorder writes a frame on every mouse move and key change).
Server (live) stats of such scores cannot be reproduced from the replay. Prints: score id, client_version,
(gap start, gap end, number of object start times inside the gap).

Usage: python3 -I difftest/replay_gaps.py [--min-objects 5]
"""
import argparse, bisect, collections, os, sqlite3, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rounding_check import split_osr  # noqa: E402

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))


def object_times(path):
    times, sec = [], None
    for line in open(path, encoding="utf-8-sig", errors="replace"):
        line = line.strip()
        if line.startswith("["):
            sec = line
            continue
        if sec == "[HitObjects]" and line:
            try:
                times.append(int(float(line.split(",")[2])))
            except (ValueError, IndexError):
                pass
    return sorted(times)


def worst_gap(frames, times):
    t, prev, worst = 0, None, (0, 0, 0)
    first = True
    for f in frames.split(","):
        p = f.split("|")
        if len(p) < 4 or p[0] == "-12345":
            continue
        t += int(float(p[0]))
        if first:
            first = False
            # replay starting late: objects due before the first frame (lazer writes frames from gameplay start)
            k = bisect.bisect_left(times, t)
            if t > 0 and k > worst[2]:
                worst = (times[0] if times else 0, t, k)
        if prev is not None and t - prev > 500:
            k = bisect.bisect_left(times, t) - bisect.bisect_right(times, prev)
            if k > worst[2]:
                worst = (prev, t, k)
        prev = t
    return worst


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--min-objects", type=int, default=5)
    a = ap.parse_args()
    db = sqlite3.connect(os.path.join(ROOT, "data", "index_v2.sqlite"))
    n, bad = 0, []
    for sid, bp, cv in db.execute("select id, beatmap_path, client_version from scores where status='ok'"):
        try:
            _, frames, _ = split_osr(open(os.path.join(ROOT, "data", "replays_v2", "%d.osr" % sid), "rb").read())
        except Exception:
            continue
        n += 1
        w = worst_gap(frames, object_times(os.path.join(ROOT, bp)))
        if w[2] >= a.min_objects:
            bad.append((sid, cv, w))
    for b in bad:
        print(*b)
    print("replays %d, with a frame gap spanning >= %d objects: %d" % (n, a.min_objects, len(bad)))
    print(collections.Counter(b[1] for b in bad))


if __name__ == "__main__":
    main()
