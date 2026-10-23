#!/usr/bin/env python3
"""Demonstrate replay-time-rounding flips (ISSUES G8) on lazer scores.

Lazer writes frame times rounded to integer ms (LegacyScoreEncoder.cs:173) but parses them as floats
(LegacyScoreDecoder: Parsing.ParseFloat), so we can re-create a plausible *unrounded* live press time: for each
round-flip candidate in the catchup oracle result (a press exactly at a blocking circle's integer StartTime, which
force-misses it with offset 0), move that key-down frame `--delta` ms earlier (the live press could have been
anywhere in [t-0.5, t+0.5)). Every subset of candidates (up to 2^--max-k) is evaluated with the oracle (catchup);
reports whether some subset reproduces the server statistics exactly / reduces the difference.

NOTE: LegacyScoreDecoder rounds fractional deltas back to int (int.TryParse, else Math.Round(ParseFloat)),
so the shift must be a whole ms: --delta 1 models "the live press was before StartTime" (blocked).

Usage: python3 -I difftest/rounding_check.py ID [ID...] [--delta 1]
"""
import argparse, itertools, json, lzma, os, sqlite3, struct, subprocess, sys, tempfile

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import oracle_vs_server_v2 as ov  # noqa: E402


def split_osr(b):
    """-> (prefix bytes up to the frame-data length field, frames text, suffix bytes)."""
    i = 1 + 4

    def sstr(i):
        if b[i] == 0:
            return i + 1
        i += 1
        n = s = 0
        while True:
            x = b[i]; i += 1
            n |= (x & 0x7F) << s; s += 7
            if not x & 0x80:
                break
        return i + n

    for _ in range(3):
        i = sstr(i)
    i += 12 + 4 + 2 + 1 + 4
    i = sstr(i)
    i += 8
    n, = struct.unpack_from("<i", b, i)
    data = b[i + 4:i + 4 + n]
    return b[:i], lzma.decompress(data, format=lzma.FORMAT_ALONE).decode(), b[i + 4 + n:]


def perturb(frames_text, press_times, delta):
    """Move each key-down frame at absolute time t in press_times to t - delta.

    Frames recorded at the same integer ms as the moved key-down frame on the side it moves towards (preceding ones
    when moving earlier, following ones when moving later) move with it, so the frame order is kept. (The first
    version only adjusted the moved frame's and the next frame's deltas; with a same-time neighbour that produced a
    backwards frame which the decoder drops, i.e. it silently deleted or delayed a frame instead of shifting it.)
    Returns (frames_text, number of presses moved)."""
    fr = [f.split("|") for f in frames_text.split(",") if f]
    t = 0.0
    abs_t = []
    for f in fr:
        if f[0] != "-12345":
            t += float(f[0])
        abs_t.append(t)
    real = [k for k, f in enumerate(fr) if f[0] != "-12345"]
    moved = 0
    for target in press_times:
        for q, k in enumerate(real):
            f = fr[k]
            if abs(abs_t[k] - target) > 1e-9:
                continue
            prev_keys = int(fr[real[q - 1]][3]) if q else 0
            if int(f[3]) & ~prev_keys:  # a new key goes down at this frame
                group = [k]
                step = -1 if delta > 0 else 1
                z = q + step
                while 0 <= z < len(real) and abs(abs_t[real[z]] - target) <= 1e-9:
                    group.append(real[z])
                    z += step
                # the neighbour beyond the group must not be crossed (replays can contain backwards frames); skip if so
                if 0 <= z < len(real) and (abs_t[real[z]] > target - delta if delta > 0 else abs_t[real[z]] < target - delta):
                    break
                for g in group:
                    abs_t[g] = target - delta
                moved += 1
                break
    out, prev = [], 0.0
    for k, f in enumerate(fr):
        if f[0] == "-12345":
            out.append("|".join(f))
            continue
        out.append("|".join([str(int(round(abs_t[k] - prev)))] + f[1:]))
        prev = abs_t[k]
    return ",".join(out) + ",", moved


def write_osr(path, prefix, frames, suffix):
    data = lzma.compress(frames.encode(), format=lzma.FORMAT_ALONE)
    with open(path, "wb") as f:
        f.write(prefix + struct.pack("<i", len(data)) + data + suffix)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("ids", type=int, nargs="+")
    ap.add_argument("--delta", type=float, default=1.0)
    ap.add_argument("--max-k", type=int, default=4)
    a = ap.parse_args()
    import fcntl
    lockf = open(ov.LOCK, "w")
    fcntl.flock(lockf, fcntl.LOCK_EX)  # one oracle process of ours at a time
    db = sqlite3.connect(ov.DB)
    cu = ov.load_results("catchup")
    for sid in a.ids:
        s = json.loads(db.execute("select json from scores where id=?", (sid,)).fetchone()[0])
        bp = db.execute("select beatmap_path from scores where id=?", (sid,)).fetchone()[0]
        o = cu[sid]
        groups = o["live"].get("round_flip", [])
        # press time of each candidate = the forced miss's object time (offset 0) -> recover from oracle? we only stored
        # (i, n); the press time equals the blocker's StartTime = time of the forced-miss judgement; re-run with judgements.
        tmpd = tempfile.mkdtemp(prefix="rc_", dir=ov.OUT)
        lst = os.path.join(tmpd, "list.txt")
        with open(lst, "w") as f:
            f.write("%s %s\n" % (os.path.join(ROOT, bp), os.path.join(ROOT, "data/replays_v2/%d.osr" % sid)))
        base = json.loads(subprocess.run([ov.ORACLE, "batch", "--list", lst], capture_output=True, text=True, cwd=ROOT).stdout.splitlines()[0])
        J = base["live"]["judgements"]
        cands = sorted({j["time"] for j in J if j["type"] in ov.BLOCKERS and j["result"] == "Miss" and j["offset"] == 0})
        prefix, frames, suffix = split_osr(open(os.path.join(ROOT, "data/replays_v2/%d.osr" % sid), "rb").read())
        subsets = [c for k in range(1, min(len(cands), a.max_k) + 1) for c in itertools.combinations(cands, k)]
        lines = []
        for k, sub in enumerate(subsets):
            fr2, moved = perturb(frames, sub, a.delta)
            p = os.path.join(tmpd, "%d_%d.osr" % (sid, k))
            write_osr(p, prefix, fr2, suffix)
            lines.append((sub, moved, p))
        with open(lst, "w") as f:
            for sub, moved, p in lines:
                f.write("%s %s\n" % (os.path.join(ROOT, bp), p))
        outs = subprocess.run([ov.ORACLE, "batch", "--list", lst, "--no-judgements"], capture_output=True, text=True,
                              cwd=ROOT, env=dict(os.environ, ORACLE_NOCACHE="1")).stdout.splitlines()
        cat0, d0, _ = ov.compare(o, s)
        print("score %d %s: catchup %s diff=%s candidates(press==blocker StartTime)=%s" % (
            sid, ov.modkey(s.get("mods", [])), cat0, json.dumps(d0), cands))
        best = None
        for (sub, moved, p), line in zip(lines, outs):
            r = ov.reduce_line(json.loads(line), sid)
            cat, d, _ = ov.compare(r, s)
            nd = sum(abs(v[0] - v[1]) for kk, v in d.items() if kk[0].isupper() and isinstance(v, (list, tuple)))
            print("   shift %s by -%.2f ms (moved %d): %s %s" % (list(sub), a.delta, moved, cat, json.dumps(d)))
            if best is None or nd < best[0]:
                best = (nd, sub, cat)
        print("   BEST: %s -> %s (|stat diff| %d)" % (list(best[1]), best[2], best[0]) if best else "   no candidates")
        for _, _, p in lines:
            os.remove(p)
        os.remove(lst)
        os.rmdir(tmpd)


if __name__ == "__main__":
    main()
