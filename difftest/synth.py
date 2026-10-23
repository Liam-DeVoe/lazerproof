#!/usr/bin/env python3
"""Synthetic corpus generator for the simulation diff test (difftest/sim_diff.py).

Generates .osu maps (circle-only, or with sliders) and .osr replays with random / adversarial frames:
presses exactly around hit-window edges, cursor exactly on (and 1-3 float ulps around) the hit-circle radius,
notelock situations (overlapping / stacked / simultaneous objects, early presses on later objects),
rapid K1/K2 alternation, M1<->K1 switching without release, long holds, frame gaps around the FSC
catch-up thresholds (16.67 / 20 ms), and replays for real beatmaps (--real-map).

Usage:
  python3 -I difftest/synth.py --out DIR --count N [--seed S] [--sliders] [--real-map X.osu ...] [--lazer]
Writes DIR/*.osu, DIR/*.osr and DIR/jobs.txt ("beatmap replay" lines).
--lazer writes lazer-format replays (version 30000000: no automatic Classic mod).
"""
import argparse, hashlib, math, os, random, struct, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import osr  # noqa: E402


def f32(x):
    return struct.unpack("<f", struct.pack("<f", x))[0]


def f32_next(x, k):
    """x moved by k float32 ulps."""
    b = struct.unpack("<i", struct.pack("<f", x))[0]
    if x >= 0:
        b += k
    else:
        b -= k
    return struct.unpack("<f", struct.pack("<i", b))[0]


def fmt(x):
    """Shortest decimal that parses back (float.Parse) to the same float32."""
    x = f32(x)
    for p in range(6, 12):
        s = "%.*g" % (p, x)
        if f32(float(s)) == x:
            return s
    return repr(x)


def difficulty_range(d, mn, mid, mx):
    if d > 5:
        return mid + (mx - mid) * (d - 5) / 5
    if d < 5:
        return mid + (mid - mn) * (d - 5) / 5
    return mid


def circle_scale(cs):
    # LegacyRulesetExtensions.CalculateScaleFromCircleSize(cs, true): (float)(1.0f - 0.7f * ((cs - 5) / 5)) / 2 * 1.00041f
    cs = f32(cs)
    inner = 1.0 - f32(0.7) * ((cs - 5) / 5)   # double
    return f32(f32(f32(inner) / 2) * f32(1.00041))


class Map:
    def __init__(self, od, cs, ar, hp, objects, sliders=False, stack_leniency=0.7, sm=1.4, tr=1.0):
        self.od, self.cs, self.ar, self.hp = od, cs, ar, hp
        self.objects = objects  # list of dicts {x,y,t,kind,...}
        self.stack_leniency = stack_leniency
        self.sm, self.tr = sm, tr

    def text(self):
        L = ["osu file format v14", "", "[General]", "AudioFilename: audio.mp3", "AudioLeadIn: 0", "PreviewTime: -1",
             "Countdown: 0", "SampleSet: Normal", f"StackLeniency: {self.stack_leniency}", "Mode: 0", "",
             "[Metadata]", "Title:synth", "Artist:synth", "Creator:synth", "Version:synth", "",
             "[Difficulty]", f"HPDrainRate:{self.hp}", f"CircleSize:{self.cs}", f"OverallDifficulty:{self.od}",
             f"ApproachRate:{self.ar}", f"SliderMultiplier:{self.sm}", f"SliderTickRate:{self.tr}", "",
             "[TimingPoints]", "0,500,4,2,0,100,1,0", "", "[HitObjects]"]
        for i, o in enumerate(self.objects):
            nc = 4 if i == 0 or o.get("nc") else 0
            if o["kind"] == "circle":
                L.append(f"{o['x']},{o['y']},{o['t']},{1 | nc},0,0:0:0:0:")
            elif o["kind"] == "spinner":
                L.append(f"256,192,{o['t']},{8 | nc},0,{o['end']},0:0:0:0:")
            elif o["kind"] == "slider":
                pts = "|".join(f"{px}:{py}" for px, py in o["points"])
                L.append(f"{o['x']},{o['y']},{o['t']},{2 | nc},0,{o['curve']}|{pts},{o['slides']},{o['length']}")
        return "\n".join(L) + "\n"


def gen_map(rng, n, sliders=False, spinners=False):
    od = rng.choice([0, 2, 5, 7, 8, 8.5, 9, 9.5, 10, rng.uniform(0, 10)])
    cs = rng.choice([2, 3, 4, 4.2, 5, 6, 7, rng.uniform(0, 7)])
    ar = rng.choice([5, 8, 9, 9.3, 10, rng.uniform(3, 10)])
    od, cs, ar = round(od, 1), round(cs, 1), round(ar, 1)
    t = rng.randint(800, 2500)
    objs = []
    x, y = rng.randint(30, 480), rng.randint(30, 350)
    for i in range(n):
        r = rng.random()
        if r < 0.15:      # simultaneous object
            dt = 0
        elif r < 0.30:    # very close (notelock / overlapping windows)
            dt = rng.randint(1, 60)
        elif r < 0.45:    # stack candidate (same position, short gap)
            dt = rng.randint(60, 200)
        else:
            dt = rng.randint(80, 600)
        t += dt
        if r < 0.45 and rng.random() < 0.6:
            pass  # keep position (stacking / overlap)
        else:
            x = min(512, max(0, x + rng.randint(-150, 150)))
            y = min(384, max(0, y + rng.randint(-120, 120)))
        if spinners and rng.random() < 0.15:
            dur = rng.choice([rng.randint(50, 400), rng.randint(400, 1500), rng.randint(1500, 5000)])
            objs.append({"kind": "spinner", "x": 256, "y": 192, "t": t, "end": t + dur})
            t += dur + rng.randint(0, 300)
        elif sliders and rng.random() < 0.4:
            curve = rng.choice(["L", "B", "P", "L"])
            k = 2 if curve == "L" else 3
            pts = []
            px, py = x, y
            for _ in range(k - 1):
                px = min(512, max(0, px + rng.randint(-120, 120)))
                py = min(384, max(0, py + rng.randint(-100, 100)))
                pts.append((px, py))
            slides = rng.choice([1, 1, 1, 2, 3])
            length = rng.choice([rng.randint(20, 300), rng.randint(5, 40)])
            objs.append({"kind": "slider", "x": x, "y": y, "t": t, "curve": curve, "points": pts, "slides": slides,
                         "length": length})
            # approximate duration at SV 1 (beat 500ms, SM 1.4): length / (100*1.4) * 500 per slide
            t += int(length / 140 * 500 * slides) + rng.randint(0, 100)
        else:
            objs.append({"kind": "circle", "x": x, "y": y, "t": t})
    return Map(od, cs, ar, rng.choice([0, 5, 8, rng.uniform(0, 10)]), objs, sliders)


def hit_windows(od):
    g = math.floor(difficulty_range(od, 80, 50, 20)) - 0.5
    o = math.floor(difficulty_range(od, 140, 100, 60)) - 0.5
    m = math.floor(difficulty_range(od, 200, 150, 100)) - 0.5
    return g, o, m


class Frames:
    def __init__(self):
        self.f = []  # (time:int, x:float32, y:float32, buttons:int)

    def add(self, t, x, y, b):
        if self.f and t < self.f[-1][0]:
            t = self.f[-1][0]
        self.f.append((int(t), f32(x), f32(y), b))

    def text(self, stable_header=True):
        out = []
        last = 0
        rows = list(self.f)
        if stable_header:
            rows = [(0, 256.0, -500.0, 0), (rows[0][0] - 1 if rows else -1, 256.0, -500.0, 0)] + rows
        for t, x, y, b in rows:
            out.append(f"{t - last}|{fmt(x)}|{fmt(y)}|{b}")
            last = t
        out.append("-12345|0|0|12345")
        return ",".join(out) + ","


def boundary_point(rng, cx, cy, r):
    """A point exactly on / around the circle of radius r (float32 arithmetic), possibly nudged by ulps."""
    th = rng.choice([0, math.pi / 2, math.pi, 3 * math.pi / 2, math.pi / 4, rng.uniform(0, 2 * math.pi)])
    px = f32(cx + f32(r * math.cos(th)))
    py = f32(cy + f32(r * math.sin(th)))
    k = rng.choice([0, 0, 1, -1, 2, -2, 3, -3])
    if k:
        if abs(math.cos(th)) > 0.3:
            px = f32_next(px, k)
        else:
            py = f32_next(py, k)
    return px, py


def spin_frames(rng, fr, ob, cx, cy):
    """Cursor circling the spinner centre (gamefield 256,192) with adversarial angular steps: near +-180 degrees per
    frame (normalisation edge), reversals, through the centre, long frame gaps, key holds/releases."""
    st, en = ob["t"], ob["end"]
    t = st + rng.randint(-200, 100)
    ang = rng.uniform(0, 2 * math.pi)
    rad = rng.choice([rng.uniform(20, 120), rng.uniform(0.5, 5), 60])
    w = rng.choice([1, -1]) * rng.choice([0.003, 0.006, 0.01, 0.015, 0.02, 0.05, 0.12])  # rad per ms
    keys = rng.choice([1, 2, 5, 10, 1 | 2])
    stop = en + rng.randint(-300, 200)
    x, y = cx, cy
    while t < stop:
        dt = rng.choice([1, 2, 8, 16, 17, 20, 21, 33, rng.randint(1, 60)])
        r = rng.random()
        if r < 0.05:
            da = math.copysign(math.pi - rng.choice([0, 1e-4, 1e-2]), w)   # ~180 deg step
        elif r < 0.08:
            w = -w
            da = w * dt
        else:
            da = w * dt
        ang += da
        rr = rad if rng.random() > 0.03 else 0.0
        x, y = 256 + rr * math.cos(ang), 192 + rr * math.sin(ang)
        bt = keys if rng.random() > 0.04 else 0
        t += dt
        fr.add(t, x, y, bt)
    fr.add(t + rng.randint(1, 40), x, y, 0)
    return x, y


def gen_replay(rng, mp, style):
    g, o, m = hit_windows(mp.od)
    scale = circle_scale(mp.cs)
    r = f32(64 * scale)
    fr = Frames()
    t = mp.objects[0]["t"] - rng.randint(600, 1500)
    cx, cy = 256.0, 192.0
    fr.add(t, cx, cy, 0)
    held = 0
    key_cycle = 0
    for i, ob in enumerate(mp.objects):
        st = ob["t"]
        if ob["kind"] == "spinner":
            cx, cy = spin_frames(rng, fr, ob, cx, cy)
            held = fr.f[-1][3]
            continue
        # stacking shifts circles by (stackHeight * scale * -6.4); unknown here, so aim at the raw position
        # or at a shifted guess; boundary probing uses the raw position.
        tx, ty = float(ob["x"]), float(ob["y"])
        mode = rng.random()
        if style == "random":
            off = rng.randint(-450, 450)
        else:
            edge = rng.choice([g, o, m, 400])
            off = int(math.copysign(math.floor(edge) + rng.choice([0, 1, -1, 2]), rng.choice([-1, 1])))
            if rng.random() < 0.3:
                off = rng.randint(-int(m) - 5, int(m) + 5)
        press_t = st + off
        # approach: frames moving towards the target before the press
        nmove = rng.randint(0, 4)
        lt = fr.f[-1][0]
        for k in range(nmove):
            tt = lt + (press_t - lt) * (k + 1) / (nmove + 1)
            gap = rng.choice([1, 5, 16, 17, 18, 19, 20, 21, 33])
            tt = max(lt, int(tt) - gap % 7)
            fr.add(tt, f32(cx + (tx - cx) * (k + 1) / (nmove + 1) + rng.uniform(-3, 3)),
                   f32(cy + (ty - cy) * (k + 1) / (nmove + 1) + rng.uniform(-3, 3)), held)
        if mode < 0.35:
            px, py = boundary_point(rng, tx, ty, r)
        elif mode < 0.8:
            px, py = tx + rng.uniform(-r * 0.8, r * 0.8), ty + rng.uniform(-r * 0.8, r * 0.8)
        else:
            px, py = tx + rng.uniform(-3 * r, 3 * r), ty + rng.uniform(-3 * r, 3 * r)
        # buttons
        if style == "switch" and held:
            # M1 <-> K1 switching while held: 1 <-> 5 (no new Left press), 2 <-> 10 for Right
            b = {1: 5, 5: 1, 2: 10, 10: 2}.get(held, held)
        else:
            key_cycle += 1
            if style == "alternate":
                b = 5 if key_cycle % 2 else 10
            else:
                b = rng.choice([1, 2, 5, 10, 1 | 2, 5 | 10, 16 | 1])
            if held and rng.random() < 0.7:
                fr.add(press_t - rng.randint(1, 30), px, py, 0)
                held = 0
        fr.add(press_t, px, py, b)
        held = b
        # hold / release
        hold = rng.choice([0, 1, 8, 30, 80, 200])
        if hold and style != "switch":
            fr.add(press_t + hold, px + rng.uniform(-2, 2), py + rng.uniform(-2, 2), 0)
            held = 0
        cx, cy = px, py
        # extra random presses (notelock pokes)
        if rng.random() < 0.2:
            et = press_t + rng.randint(1, 120)
            fr.add(et, cx + rng.uniform(-r, r), cy + rng.uniform(-r, r), rng.choice([1, 2, 5, 10]))
            fr.add(et + rng.randint(1, 50), cx, cy, 0)
            held = 0
        # sliders: follow the body roughly
        if ob["kind"] == "slider":
            pts = [(ob["x"], ob["y"])] + list(ob["points"])
            dur = int(ob["length"] / 140 * 500 * ob["slides"])
            hb = rng.choice([1, 2, 5, 10])
            steps = rng.randint(2, 12)
            for k in range(steps):
                frac = (k + 1) / steps
                seg = min(len(pts) - 2, int(frac * (len(pts) - 1)))
                (ax, ay), (bx, by) = pts[seg], pts[seg + 1]
                fx, fy = ax + (bx - ax) * rng.random(), ay + (by - ay) * rng.random()
                bb = hb if rng.random() < 0.85 else 0
                fr.add(st + int(dur * frac) + rng.randint(-20, 20), fx + rng.uniform(-r, r), fy + rng.uniform(-r, r), bb)
            held = fr.f[-1][3]
    fr.add(fr.f[-1][0] + rng.randint(50, 500), cx, cy, 0)
    return fr


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--count", type=int, default=20)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--objects", type=int, default=40)
    ap.add_argument("--sliders", action="store_true")
    ap.add_argument("--spinners", action="store_true")
    ap.add_argument("--real-map", nargs="*", default=[])
    ap.add_argument("--lazer", action="store_true", help="lazer-format replays (version 30000000)")
    ap.add_argument("--nokeys", type=float, default=0.0, help="fraction of replays with all key bits cleared (Relax)")
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    rng = random.Random(args.seed)
    jobs = []
    for n in range(args.count):
        style = rng.choice(["edge", "edge", "random", "alternate", "switch"])
        if args.real_map:
            bm = rng.choice(args.real_map)
            mp = parse_real_map(bm)
            text = open(bm, "rb").read()
            bpath = os.path.abspath(bm)
        else:
            mp = gen_map(rng, args.objects, args.sliders, args.spinners)
            text = mp.text().encode()
            bpath = os.path.join(args.out, f"s{args.seed}_{n}.osu")
            open(bpath, "wb").write(text)
        md5 = hashlib.md5(text).hexdigest()
        fr = gen_replay(rng, mp, style)
        if args.nokeys and rng.random() < args.nokeys:
            fr.f = [(t, x, y, 0) for t, x, y, _ in fr.f]
        rpath = os.path.join(args.out, f"s{args.seed}_{n}.osr")
        osr.write(rpath, frames_text=fr.text(stable_header=not args.lazer), beatmap_md5=md5,
                  version=30000000 if args.lazer else 20250101)
        jobs.append(f"{bpath} {os.path.abspath(rpath)}")
    with open(os.path.join(args.out, "jobs.txt"), "w") as f:
        f.write("\n".join(jobs) + "\n")
    print(f"wrote {len(jobs)} jobs to {args.out}/jobs.txt")


def parse_real_map(path):
    """Very small .osu reader (difficulty + object times/positions) for generating frames against a real map."""
    sec = None
    d = {}
    objs = []
    for line in open(path, encoding="utf-8", errors="replace"):
        line = line.strip()
        if line.startswith("["):
            sec = line
            continue
        if sec == "[Difficulty]" and ":" in line:
            k, v = line.split(":", 1)
            d[k.strip()] = float(v)
        elif sec == "[HitObjects]" and line:
            p = line.split(",")
            try:
                x, y, t, ty = int(float(p[0])), int(float(p[1])), int(float(p[2])), int(p[3])
            except (ValueError, IndexError):
                continue
            if ty & 2 and len(p) >= 8:
                pts = []
                for q in p[5].split("|")[1:]:
                    a = q.split(":")
                    if len(a) == 2:
                        pts.append((int(float(a[0])), int(float(a[1]))))
                if not pts:
                    pts = [(x, y)]
                objs.append({"kind": "slider", "x": x, "y": y, "t": t, "points": pts, "slides": int(p[6]),
                             "length": float(p[7])})
            elif ty & 8:
                try:
                    en = int(float(p[5]))
                except (ValueError, IndexError):
                    en = t
                objs.append({"kind": "spinner", "x": 256, "y": 192, "t": t, "end": en})
            else:
                objs.append({"kind": "circle", "x": x, "y": y, "t": t})
    od = d.get("OverallDifficulty", 5)
    return Map(od, d.get("CircleSize", 5), d.get("ApproachRate", od), d.get("HPDrainRate", 5), objs)


if __name__ == "__main__":
    main()
