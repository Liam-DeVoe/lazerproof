#!/usr/bin/env python3
"""Coverage-directed synthetic inputs: one generator per lazer branch that the oracle corpora never exercised
(docs/lazer-coverage.md "Targeted tests"). Each scenario writes small .osu/.osr pairs (plus optional per-job mods)
built so that the branch is taken, with parameter sweeps around the branch's threshold so both outcomes occur.

Usage:
  python3 -I difftest/covfuzz.py --out DIR [--scenario NAME ...] [--seed S] [--count N]
Writes DIR/<scenario>/*.osu|*.osr and DIR/<scenario>/jobs.txt ("beatmap replay [modsjson]"), plus DIR/all.txt.
Then:  tools/heavy python3 -I difftest/eval_diff.py run --list DIR/all.txt --work W [--replace-mods] ...
Re-measure coverage of the new inputs with difftest/lazer_cov.py run --list DIR/all.txt --name covfuzz.
"""
import argparse, hashlib, json, math, os, random, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import osr  # noqa: E402
from synth import f32, fmt, circle_scale, hit_windows, Frames  # noqa: E402


def osu_text(objs, od=5, cs=4, ar=9, hp=5, sm=1.4, tr=1.0, timing=("0,500,4,2,0,100,1,0",), stack=0.7,
             version=14, general=(), breaks=()):
    L = ["osu file format v%d" % version, "", "[General]", "AudioFilename: audio.mp3", "AudioLeadIn: 0",
         "PreviewTime: -1", "Countdown: 0", "SampleSet: Normal", "StackLeniency: %s" % stack, "Mode: 0"]
    L += list(general)
    L += ["", "[Metadata]", "Title:covfuzz", "Artist:covfuzz", "Creator:covfuzz", "Version:covfuzz", "",
          "[Difficulty]", "HPDrainRate:%s" % hp, "CircleSize:%s" % cs, "OverallDifficulty:%s" % od,
          "ApproachRate:%s" % ar, "SliderMultiplier:%s" % sm, "SliderTickRate:%s" % tr, "", "[Events]"]
    L += ["2,%d,%d" % b for b in breaks]
    L += ["", "[TimingPoints]"] + list(timing) + ["", "[HitObjects]"]
    for i, o in enumerate(objs):
        nc = 4 if i == 0 or o.get("nc") else 0
        if o["kind"] == "circle":
            L.append("%s,%s,%d,%d,0,0:0:0:0:" % (o["x"], o["y"], o["t"], 1 | nc))
        elif o["kind"] == "spinner":
            L.append("256,192,%d,%d,0,%d,0:0:0:0:" % (o["t"], 8 | nc, o["end"]))
        else:
            pts = "|".join("%s:%s" % p for p in o["points"])
            L.append("%s,%s,%d,%d,0,%s|%s,%d,%s" % (o["x"], o["y"], o["t"], 2 | nc, o.get("curve", "L"), pts,
                                                   o["slides"], o["length"]))
    return "\n".join(L) + "\n"


class Out:
    def __init__(self, root, name):
        self.dir = os.path.join(root, name)
        os.makedirs(self.dir, exist_ok=True)
        self.name, self.jobs, self.n = name, [], 0

    def add(self, osu, frames, mods=None, lazer=True, stable_header=None, tag=""):
        k = "%s_%03d%s" % (self.name, self.n, tag)
        self.n += 1
        b = osu.encode()
        bp = os.path.join(self.dir, k + ".osu")
        open(bp, "wb").write(b)
        rp = os.path.join(self.dir, k + ".osr")
        sh = (not lazer) if stable_header is None else stable_header
        osr.write(rp, frames_text=frames.text(stable_header=sh), beatmap_md5=hashlib.md5(b).hexdigest(),
                  version=30000000 if lazer else 20250101)
        line = "%s %s" % (bp, rp)
        if mods is not None:
            line += " " + json.dumps(mods, separators=(",", ":"))
        self.jobs.append(line)

    def close(self):
        open(os.path.join(self.dir, "jobs.txt"), "w").write("\n".join(self.jobs) + "\n")
        return self.jobs


SCENARIOS = {}


def scenario(f):
    SCENARIOS[f.__name__] = f
    return f


# ----------------------------------------------------------------------------------------------------------------
# A. SliderInputManager.PostProcessHeadJudgement: allTicksInRange = false (SliderInputManager.cs:113-116, :133).
# A fast slider with a repeat returns towards its head; the head is pressed late while the ball is back near the
# cursor (inside 2.4r) but the already-passed repeat/ticks at the far end are outside 2.4r -> MissForcefully.
@scenario
def ppmiss(out, rng, count):
    for n in range(count):
        cs = rng.choice([2, 4, 5, 7])
        od = rng.choice([0, 0, 2, 5])
        length = rng.choice([120, 160, 200, 260])
        slides = rng.choice([2, 2, 3, 4])
        beat = rng.choice([60, 80, 100, 150])
        tr = rng.choice([1, 2, 4, 8])
        x0, y0 = 120, 192
        T = 2000
        objs = [{"kind": "slider", "x": x0, "y": y0, "t": T, "points": [(x0 + length, y0)], "slides": slides,
                 "length": length},
                {"kind": "circle", "x": 400, "y": 300, "t": T + 1500, "nc": 1}]
        osu = osu_text(objs, od=od, cs=cs, sm=3.6, tr=tr, timing=("0,%d,4,2,0,100,1,0" % beat,))
        g, o, m = hit_windows(od)
        span = length / (100 * 3.6) * beat
        dur = span * slides
        # press late: sweep times across the slider (ball returning towards the head on even spans)
        press = T + int(rng.uniform(span * 1.2, min(m, dur + 20)))
        px = x0 + rng.choice([0, 0, rng.uniform(-10, 10), rng.uniform(-30, 30)])
        py = y0 + rng.choice([0, rng.uniform(-10, 10)])
        fr = Frames()
        fr.add(T - 1200, 256, 192, 0)
        fr.add(T - 300, px, py, 0)
        fr.add(press, px, py, 1)
        # stay / follow the ball back to the head, then release after the end
        t = press
        while t < T + dur + 60:
            t += rng.choice([4, 8, 16, 17])
            fr.add(t, px + rng.uniform(-2, 2), py + rng.uniform(-2, 2), 1)
        fr.add(T + 1300, 400, 300, 0)
        fr.add(T + 1500, 400, 300, 2)
        fr.add(T + 1560, 400, 300, 0)
        lazer = rng.random() < 0.5
        out.add(osu, fr, lazer=lazer)


# ----------------------------------------------------------------------------------------------------------------
# B. DrainingHealthProcessor.ComputeDrainRate with <= 1 health increase -> DrainRate 0
# (DrainingHealthProcessor.cs:165-166). Needs the non-legacy processor (lazer replay, no Classic) and a map with a
# single judgement (one circle). Hit / miss / no-press variants, all fail modes.
@scenario
def onejudgement(out, rng, count):
    for n in range(count):
        od, cs, hp = rng.choice([0, 5, 10]), rng.choice([2, 5, 7]), rng.choice([0, 5, 10])
        T = rng.choice([1000, 3000, 20000])
        x, y = rng.randint(50, 460), rng.randint(50, 330)
        osu = osu_text([{"kind": "circle", "x": x, "y": y, "t": T}], od=od, cs=cs, hp=hp)
        g, o, m = hit_windows(od)
        fr = Fr()
        fr.add(0, 256, 192, 0)
        mode = rng.choice(["hit", "late", "miss", "none"])
        if mode != "none":
            off = {"hit": rng.randint(-int(g), int(g)), "late": int(m) + rng.choice([0, 1]), "miss": rng.choice([-300, 250])}[mode]
            fr.add(T - 400, x, y, 0)
            fr.add(T + off, x, y, 1)
            fr.add(T + off + 50, x, y, 0)
        fr.add(T + 3000, 256, 192, 0)
        mods = rng.choice([None, [{"acronym": "SD"}], [{"acronym": "PF"}], [{"acronym": "NF"}], [{"acronym": "AC", "settings": {"minimum_accuracy": 0.95}}]])
        out.add(osu, fr, mods=mods, lazer=True)


class Fr(Frames):
    """Frames that may also carry raw (non-integer / odd) delta strings: add_raw(delta_text, x, y, buttons)."""

    def __init__(self):
        super().__init__()
        self.raw = []

    def text(self, stable_header=True):
        if not self.raw:
            return super().text(stable_header)
        return ",".join(self.raw) + ",-12345|0|0|12345,"


# ----------------------------------------------------------------------------------------------------------------
# C. LegacyScoreDecoder.readLegacyReplay non-integer frame deltas: `diff = (int)Math.Round(Parsing.ParseFloat(..))`
# (LegacyScoreDecoder.cs:305-306), incl. banker's rounding at .5, negative deltas (backwards frames dropped,
# :341-351), exponents, leading '+' / whitespace (int.TryParse NumberStyles.Integer), huge values.
@scenario
def floatdelta(out, rng, count):
    for n in range(count):
        od, cs = rng.choice([5, 8]), rng.choice([4, 5])
        T0 = 1500
        objs = []
        t = T0
        for k in range(12):
            objs.append({"kind": "circle", "x": 100 + 30 * k, "y": 150 + (k % 3) * 40, "t": t})
            t += rng.choice([150, 300])
        osu = osu_text(objs, od=od, cs=cs)
        fr = Fr()
        lazer = rng.random() < 0.5
        if not lazer:
            fr.raw += ["0|256|-500|0", "-1|256|-500|0"]
        cur = 0.0  # what lazer's integer accumulation should give (approx; only to aim presses)
        fr.raw.append("%d|256|192|0" % (T0 - 1000))
        cur = T0 - 1000
        for ob in objs:
            target = ob["t"] + rng.randint(-60, 60)
            gap = target - cur
            # split the gap into a few deltas, some written as floats
            parts = []
            left = gap
            while left > 40:
                d = rng.randint(5, 40)
                parts.append(d)
                left -= d
            parts.append(left)
            for i, d in enumerate(parts):
                if rng.random() < 0.5:
                    style = rng.choice(["half", "frac", "exp", "plus", "space", "negfrac", "f32"])
                    if style == "half":
                        s = "%d.5" % d
                    elif style == "frac":
                        s = "%.3f" % (d + rng.uniform(-0.49, 0.49))
                    elif style == "exp":
                        s = "%se1" % ("%g" % (d / 10.0))
                    elif style == "plus":
                        s = "+%d" % d
                    elif style == "space":
                        s = " %d " % d
                    elif style == "negfrac":
                        s = "-%d.5" % rng.randint(0, 3)
                    else:
                        s = repr(f32(d + 0.25))
                else:
                    s = "%d" % d
                last = i == len(parts) - 1
                b = 1 if last else 0
                fr.raw.append("%s|%s|%s|%d" % (s, fmt(ob["x"] + rng.uniform(-5, 5)), fmt(ob["y"] + rng.uniform(-5, 5)), b))
            fr.raw.append("%s|%s|%s|0" % (rng.choice(["30", "29.5", "30.5", "1e1"]), fmt(ob["x"]), fmt(ob["y"])))
            cur = target + 30
        fr.raw.append("500|256|192|0")
        out.add(osu, fr, lazer=lazer)


# ----------------------------------------------------------------------------------------------------------------
# D. LegacyScoreDecoder header: replay versions with an int32 online id (20121008 <= v < 20140721,
# LegacyScoreDecoder.cs:109-110) and with none (v < 20121008); legacy beatmap versions < 5 (+24 ms frame offset, :98).
@scenario
def oldversion(out, rng, count):
    for n in range(count):
        ver = rng.choice([20121008, 20130101, 20140720, 20120101, 20110101, 20140721])
        bmver = rng.choice([3, 4, 5, 14])
        T = 1500
        objs = [{"kind": "circle", "x": 100 + 40 * k, "y": 200, "t": T + 200 * k} for k in range(8)]
        osu = osu_text(objs, od=8, cs=4, version=bmver)
        fr = Frames()
        fr.add(T - 800, 256, 192, 0)
        for ob in objs:
            pt = ob["t"] + rng.randint(-40, 40)
            fr.add(pt, ob["x"], ob["y"], 1)
            fr.add(pt + 40, ob["x"], ob["y"], 0)
        fr.add(T + 3000, 256, 192, 0)
        k = "%s_%03d" % (out.name, out.n)
        out.n += 1
        b = osu.encode()
        bp = os.path.join(out.dir, k + ".osu")
        open(bp, "wb").write(b)
        rp = os.path.join(out.dir, k + ".osr")
        write_versioned(rp, fr.text(stable_header=True), hashlib.md5(b).hexdigest(), ver)
        out.jobs.append("%s %s" % (bp, rp))


def write_versioned(path, frames_text, md5, version):
    """osr.write with the online-id field width of `version` (int64 >= 20140721, int32 >= 20121008, none before)."""
    import lzma, struct
    data = lzma.compress(frames_text.encode("utf-8"), format=lzma.FORMAT_ALONE)
    out = bytearray([0]) + struct.pack("<i", version)
    out += osr._wstr(md5) + osr._wstr("synth") + osr._wstr("0" * 32)
    out += struct.pack("<6H", 0, 0, 0, 0, 0, 0) + struct.pack("<i", 0) + struct.pack("<H", 0) + bytes([0]) + struct.pack("<i", 0)
    out += osr._wstr("") + struct.pack("<q", 638000000000000000) + struct.pack("<i", len(data)) + data
    if version >= 20140721:
        out += struct.pack("<q", 0)
    elif version >= 20121008:
        out += struct.pack("<i", 0)
    open(path, "wb").write(bytes(out))


# ----------------------------------------------------------------------------------------------------------------
# E. Target Practice beat generation with breaks and close timing points: isInsideBreakPeriod
# (OsuModTargetPractice.cs:352-363) and "remove beats too close to the next one" (:210-216).
@scenario
def tpbreaks(out, rng, count):
    for n in range(count):
        T = 1000
        objs, t = [], T
        breaks = []
        for k in range(30):
            objs.append({"kind": "circle", "x": rng.randint(40, 470), "y": rng.randint(40, 340), "t": t})
            if k in (9, 19):
                gap = rng.choice([3000, 5000, 8000])
                bs = t + rng.choice([200, 400, 650])
                be = t + gap - rng.choice([0, 200, 500])
                breaks.append((bs, be))
                t += gap
            else:
                t += rng.choice([250, 500])
        bl = rng.choice([500, 400, 300])
        timing = ["%d,%d,4,2,0,100,1,0" % (0, bl)]
        # extra uninherited points close to each other (beats closer than BeatLength/2 get removed)
        for _ in range(rng.randint(0, 4)):
            tt = rng.randint(T, t)
            timing.append("%d,%s,4,2,0,100,1,0" % (tt, rng.choice([bl, bl / 2, 333.3, 250])))
            timing.append("%d,%s,4,2,0,100,1,0" % (tt + rng.choice([1, 10, 60, 120]), bl))
        timing.sort(key=lambda s: float(s.split(",")[0]))
        osu = osu_text(objs, od=rng.choice([5, 8]), cs=4, timing=timing, breaks=breaks)
        fr = Frames()
        fr.add(T - 800, 256, 192, 0)
        tt = T - 800
        while tt < t + 500:   # random presses everywhere (TP objects are generated, positions unknown here)
            tt += rng.randint(30, 260)
            fr.add(tt, rng.uniform(0, 512), rng.uniform(0, 384), rng.choice([0, 1, 2]))
        mods = [{"acronym": "TP", "settings": {"seed": rng.randint(0, 10**6)}}]
        if rng.random() < 0.3:
            mods.append({"acronym": "NF"})
        out.add(osu, fr, mods=mods, lazer=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--scenario", nargs="*", default=None)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--count", type=int, default=40)
    ap.add_argument("--gen-mods", default=None, help="also append random mods (difftest/modgen_sim.py POOL) to jobs without mods")
    a = ap.parse_args()
    names = a.scenario or sorted(SCENARIOS)
    allj = []
    for nm in names:
        o = Out(a.out, nm)
        SCENARIOS[nm](o, random.Random("%s:%d" % (nm, a.seed)), a.count)
        jobs = o.close()
        if a.gen_mods:
            import modgen_sim
            mr = random.Random("mods:%s:%d" % (nm, a.seed))
            jobs = [j if j.count(" ") >= 2 else j + " " + json.dumps(modgen_sim.gen(mr, a.gen_mods), separators=(",", ":"))
                    for j in jobs]
            open(os.path.join(o.dir, "jobs.txt"), "w").write("\n".join(jobs) + "\n")
        allj += jobs
        print("%s: %d jobs" % (nm, len(o.jobs)))
    open(os.path.join(a.out, "all.txt"), "w").write("\n".join(allj) + "\n")


if __name__ == "__main__":
    main()
