#!/usr/bin/env python3
"""Search for a single replay press whose +-1 ms shift reproduces the server statistics (docs/server-agreement.md).

The replay stores press times rounded to integer ms (LegacyScoreEncoder.cs:173), so the live press was within
+-0.5 ms of the recorded one. Shifting a key-down frame by one whole ms (the decoder rounds fractional deltas back
to integers) is the closest stand-in for "the live press landed on the other side of an integer threshold". For each
circle/head whose sim result is Miss (or whose result the server count says should change), every key-down frame within
[start - 400, start + 400] is shifted by -1 and by +1 ms. The sim (Rust if the mods allow, else Lean; both bit-exact
vs the oracle; default: Rust simtest_rs with the score's APIMod JSON) is rerun and the statistics are compared with the
server's. The unmodified run must reproduce the oracle's statistics first.

Usage: python3 -I difftest/press_shift_search.py ID [--lean] [--max-runs N]
"""
import argparse, json, os, sqlite3, subprocess, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import oracle_vs_server_v2 as ov  # noqa: E402
import tail_margin as tm  # noqa: E402
import tracking_trace as tt  # noqa: E402
from rounding_check import split_osr, perturb  # noqa: E402


SIMTEST_RS = os.path.join(ov.ROOT, "impl", "target", "release", "simtest_rs")
SCHED = ["catchup"]


def run(sid, frames_path, mods, lean):
    if lean:
        p = subprocess.run([tt.SIMTEST, "--playable", os.path.join(ov.OUT, "playable", "%d.json" % sid), "--frames", frames_path,
                            "--env", tt.ENV, "--mods-json", json.dumps(mods), "--lazer-replay"], capture_output=True, text=True)
    else:
        # simtest_rs: the Rust Sim with the M5/M6 sim-side mods (rate, fail, AL/SG/RX/AP, ...), APIMod JSON
        p = subprocess.run([SIMTEST_RS, "--playable", os.path.join(ov.OUT, "playable", "%d.json" % sid), "--frames", frames_path,
                            "--env", tt.ENV, "--mods-json", json.dumps(mods), "--lazer-replay", "--schedule", SCHED[0]],
                           capture_output=True, text=True)
    if p.returncode != 0:
        return None
    return json.loads(p.stdout)["statistics"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("id", type=int)
    ap.add_argument("--lean", action="store_true")
    ap.add_argument("--max-runs", type=int, default=2000)
    ap.add_argument("--schedule", default="catchup", help="catchup|perframe|dense1ms (Rust sim)")
    ap.add_argument("--only", type=float, nargs="*", help="only these press times")
    ap.add_argument("--base-frames", help="start from this frame text instead of the replay's (e.g. a de-aliased one)")
    ap.add_argument("--dup-only", action="store_true", help="only presses whose integer ms holds more than one frame")
    ap.add_argument("--near", type=float, default=400, help="max |press - circle start| (ms)")
    a = ap.parse_args()
    sid = a.id
    SCHED[0] = a.schedule
    tmp = os.environ.get("TT_TMP", tt.TMP)
    os.makedirs(tmp, exist_ok=True)
    db = sqlite3.connect(ov.DB)
    s = json.loads(db.execute("select json from scores where id=?", (sid,)).fetchone()[0])
    srv = {ov.camel(k): v for k, v in s["statistics"].items() if v}
    _, frames, _ = split_osr(open(os.path.join(ov.ROOT, "data/replays_v2/%d.osr" % sid), "rb").read())
    if a.base_frames:
        frames = open(a.base_frames).read()
    base_p = os.path.join(tmp, "%d.txt" % sid)
    open(base_p, "w").write(frames)
    base = run(sid, base_p, s["mods"], a.lean)
    oracle = ov.load_results("catchup")[sid]["live"]["statistics"]
    print("base sim == oracle:", base == oracle, " server-oracle:", {k: srv.get(k, 0) - oracle.get(k, 0) for k in set(srv) | set(oracle) if srv.get(k, 0) != oracle.get(k, 0)})
    if base != oracle and not a.base_frames and a.schedule == "catchup":
        print("sim does not reproduce the oracle; abort")
        return
    P = json.load(open(os.path.join(ov.OUT, "playable", "%d.json" % sid)))
    fr = tm.frames_of(sid)
    downs, prev = [], 0
    for t, x, y, k in fr:
        if k & ~prev & 3:
            downs.append(t)
        prev = k
    # candidate presses: near any circle/head start (+-400 ms); dedupe
    starts = []
    for ob in P["objects"]:
        if ob["kind"] == "circle":
            starts.append(tm.hx(ob["start"]))
        elif ob["kind"] == "slider":
            starts.append(tm.hx(ob["nested"][0]["start"]))
    import bisect
    starts.sort()
    def near(t):
        k = bisect.bisect_left(starts, t)
        return any(0 <= q < len(starts) and abs(starts[q] - t) <= a.near for q in (k - 1, k))
    import collections
    mult = collections.Counter(f[0] for f in fr)
    cand = sorted({t for t in downs if near(t) and (not a.dup_only or mult[t] > 1)})
    if a.only:
        cand = [t for t in cand if t in set(a.only)]
    print("candidate presses:", len(cand))
    runs = hits = 0
    best = None
    l1 = lambda st: sum(abs(st.get(k, 0) - srv.get(k, 0)) for k in set(st) | set(srv))
    base_l1 = l1(base)
    out_p = os.path.join(tmp, "%d.shift.txt" % sid)
    for t in cand:
        for d in (1.0, -1.0):
            if runs >= a.max_runs:
                break
            fr2, moved = perturb(frames, [t], d)
            if not moved:
                continue
            open(out_p, "w").write(fr2)
            st = run(sid, out_p, s["mods"], a.lean)
            runs += 1
            if st is not None and (best is None or l1(st) < best[0]):
                best = (l1(st), t, -d)
            if st == srv:
                hits += 1
                print("EXACT: press at %.0f shifted by %+d ms reproduces the server statistics" % (t, -d))
    print("runs %d, exact reproductions %d; base |diff| %d, best single shift %s" % (runs, hits, base_l1, best))


if __name__ == "__main__":
    main()
