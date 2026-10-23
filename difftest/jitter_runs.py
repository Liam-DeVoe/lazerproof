#!/usr/bin/env python3
"""Cursor-margin test for oracle-vs-server mismatches (docs/server-agreement.md).

A lazer replay keeps cursor positions only at the recorded frames (<= 60 fps plus key-change frames). Between them
playback interpolates, while live play saw the real mouse. Tracking judgements (slider ticks, repeats, tails,
spinners) whose outcome depends on that missing information lie within a small cursor margin of the
follow-circle/tick boundary. To test this, every *non key-down* frame position is moved by a uniform random
offset in [-A, A] osu!px on each axis (seeded). Key-down frames are kept exact, because their positions are
recorded exactly. The oracle then runs (catchup) with per-judgement output into data/oracle_v2/jitter<A>s<seed>_obj.jsonl.
`oracle_vs_server_v2.py flipcheck` treats these runs as extra observations ("margin" flips).

Usage: python3 -I difftest/jitter_runs.py --ids FILE [--amp 1.0] [--seeds 1,2,3]
"""
import argparse, fcntl, json, os, random, sqlite3, subprocess, sys, tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import oracle_vs_server_v2 as ov  # noqa: E402
from rounding_check import split_osr, write_osr  # noqa: E402

ROOT = ov.ROOT


def jitter(frames_text, amp, rng):
    fr = [f.split("|") for f in frames_text.split(",") if f]
    prev = 0
    for f in fr:
        if f[0] == "-12345":
            continue
        keys = int(f[3])
        if not (keys & ~prev):
            f[1] = repr(float(f[1]) + rng.uniform(-amp, amp))
            f[2] = repr(float(f[2]) + rng.uniform(-amp, amp))
        prev = keys
    return ",".join("|".join(f) for f in fr) + ","


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ids", required=True)
    ap.add_argument("--amp", type=float, default=1.0)
    ap.add_argument("--seeds", default="1,2,3")
    a = ap.parse_args()
    ids = [int(x.split()[0]) for x in open(a.ids) if x.strip()]
    db = sqlite3.connect(ov.DB)
    lockf = open(ov.LOCK, "w")
    fcntl.flock(lockf, fcntl.LOCK_EX)
    for seed in [int(x) for x in a.seeds.split(",")]:
        tag = "jitter%gs%d" % (a.amp, seed)
        out = os.path.join(ov.OUT, tag + "_obj.jsonl")
        done = ov.done_ids(out)
        todo = [i for i in ids if i not in done]
        if not todo:
            continue
        tmpd = tempfile.mkdtemp(prefix="jit_", dir=ov.OUT)
        lst = os.path.join(tmpd, "list.txt")
        paths = {}
        with open(lst, "w") as lf:
            for sid in todo:
                bp = db.execute("select beatmap_path from scores where id=?", (sid,)).fetchone()[0]
                prefix, frames, suffix = split_osr(open(os.path.join(ROOT, "data/replays_v2/%d.osr" % sid), "rb").read())
                p = os.path.join(tmpd, "%d.osr" % sid)
                write_osr(p, prefix, jitter(frames, a.amp, random.Random(seed * 1000003 + sid)), suffix)
                paths[p] = sid
                lf.write("%s %s\n" % (os.path.join(ROOT, bp), p))
        proc = subprocess.Popen(["nice", "-n", "10", ov.ORACLE, "batch", "--list", lst], stdout=subprocess.PIPE,
                                stderr=subprocess.DEVNULL, cwd=ROOT, text=True, env=dict(os.environ, ORACLE_NOCACHE="1"))
        with open(out, "a") as f:
            for line in proc.stdout:
                try:
                    d = json.loads(line)
                except Exception:
                    continue
                rp = d.get("input", {}).get("replay") or d.get("replay")
                sid = paths.get(rp) or paths.get(os.path.join(ROOT, rp or ""))
                if sid is None:
                    continue
                f.write(json.dumps(ov.reduce_line(d, sid, True), separators=(",", ":")) + "\n")
                f.flush()
        proc.wait()
        for p in paths:
            os.remove(p)
        os.remove(lst)
        os.rmdir(tmpd)
        print("%s done (%d)" % (tag, len(todo)), file=sys.stderr, flush=True)


if __name__ == "__main__":
    main()
