#!/usr/bin/env python3
"""Generate synthetic .osu files from scratch (geometry / timing / stacking stress).

usage: python3 -I gen.py OUTDIR COUNT SEED
"""
import os, sys, random

def fnum(r, lo, hi, frac=True):
    v = r.uniform(lo, hi)
    k = r.random()
    if not frac or k < 0.4:
        return str(int(v))
    if k < 0.7:
        return f'{v:.2f}'
    return repr(v)

def gen(r):
    version = r.choice([3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 14, 14, 128])
    L = [f'osu file format v{version}', '', '[General]', 'Mode: 0']
    if r.random() < 0.8:
        L.append('StackLeniency: ' + r.choice(['0.7', '0.5', '0.2', '1', '0', '0.3', fnum(r, 0, 1.5)]))
    L += ['', '[Difficulty]']
    for k in ['HPDrainRate', 'CircleSize', 'OverallDifficulty', 'ApproachRate']:
        if r.random() < 0.9:
            L.append(f'{k}:' + r.choice([fnum(r, 0, 10), str(r.randint(0, 10)), fnum(r, -2, 12)]))
    L.append('SliderMultiplier:' + r.choice(['1.4', '1', '2', '3.6', '0.4', fnum(r, 0.3, 4)]))
    L.append('SliderTickRate:' + r.choice(['1', '2', '0.5', '4', '8', '3', fnum(r, 0.3, 9)]))
    L += ['', '[Events]']
    t = r.randint(-500, 3000)
    nobj = r.randint(1, 120)
    end = t + nobj * 400
    for _ in range(r.randint(0, 3)):
        a = r.randint(t, end); L.append(f'2,{a},{a + r.randint(-100, 5000)}')
    L += ['', '[TimingPoints]']
    tp = []
    tt = t - r.randint(0, 1000)
    for i in range(r.randint(1, 12)):
        unin = i == 0 or r.random() < 0.3
        if unin:
            bl = r.choice(['500', '333.333333333333', '461.538461538462', '300', fnum(r, 3, 2000), '1', '70000'])
        else:
            bl = r.choice(['-100', '-50', '-200', '-66.6666666666667', 'NaN', '-1000', '-10', '-5', fnum(r, -1500, -1), '-1e-300'])
        tp.append(f'{tt},{bl},4,1,0,100,{1 if unin else 0},0')
        tt += r.choice([0, r.randint(1, 3000), r.randint(-500, 500)])
    if r.random() < 0.2: r.shuffle(tp)
    L += tp
    L += ['', '[HitObjects]']
    pts = [(r.randint(0, 512), r.randint(0, 384)) for _ in range(r.randint(1, 8))]
    def pos():
        if r.random() < 0.6:
            x, y = r.choice(pts)
            return x + r.choice([0, 0, 0, 1, 2, -1, 3]), y + r.choice([0, 0, 1, -2, 3])
        return r.randint(-50, 560), r.randint(-50, 430)
    for _ in range(nobj):
        t += r.choice([0, 1, 10, 50, 100, 150, 200, 300, 500, 1000, r.randint(0, 2000)])
        x, y = pos()
        if version >= 128 and r.random() < 0.5:
            x, y = x + r.random(), y + r.random()
        nc = 4 if r.random() < 0.2 else 0
        co = (r.randint(0, 7) << 4) if r.random() < 0.1 else 0
        k = r.random()
        if k < 0.4:
            L.append(f'{x},{y},{t},{1 | nc | co},0,0:0:0:0:')
        elif k < 0.9:
            ty = r.choice(['B', 'B', 'L', 'L', 'P', 'P', 'C', 'B3', 'B2', 'B1'])
            n = r.choice([1, 1, 2, 2, 3, 4, 6, 10, 20])
            ctrl = []
            px, py = x, y
            for _ in range(n):
                if r.random() < 0.15 and ctrl:
                    ctrl.append(ctrl[-1])  # red anchor
                    continue
                px += r.randint(-150, 150); py += r.randint(-150, 150)
                if version >= 128 and r.random() < 0.5:
                    ctrl.append(f'{px + r.random():.3f}:{py + r.random():.3f}')
                else:
                    ctrl.append(f'{px}:{py}')
            if ty == 'P' and r.random() < 0.3 and len(ctrl) >= 2:
                # colinear or near-colinear arcs / huge arcs
                ctrl = [f'{x + 100}:{y + r.choice([0, 1, 0.5, 200])}', f'{x + 200}:{y}']
            segs = [ty] + ctrl
            if r.random() < 0.15 and len(segs) > 3:
                segs.insert(r.randrange(2, len(segs)), r.choice(['B', 'L', 'P', 'C']))
            slides = r.choice([1, 1, 1, 2, 3, 5, 0, 10])
            length = r.choice([fnum(r, 0, 600), str(r.randint(0, 800)), '0', fnum(r, 10, 2000)]) if r.random() < 0.95 else None
            line = f'{x},{y},{t},{2 | nc | co},0,{"|".join(segs)},{slides}'
            if length is not None:
                line += f',{length}'
            L.append(line)
            t += r.randint(0, 2000)
        else:
            e = t + r.choice([r.randint(0, 5000), -10, 0, 1, 20000])
            L.append(f'256,192,{t},{8 | nc},0,{e},0:0:0:0:')
            t = max(t, e)
    if r.random() < 0.2:
        body = L[L.index('[HitObjects]') + 1:]
        r.shuffle(body)
        L = L[:L.index('[HitObjects]') + 1] + body
    return '\n'.join(L) + '\n'

def main():
    out, count, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    os.makedirs(out, exist_ok=True)
    r = random.Random(seed)
    for n in range(count):
        with open(os.path.join(out, f'g{seed}_{n}.osu'), 'w') as f:
            f.write(gen(r))

if __name__ == '__main__':
    main()
