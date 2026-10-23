#!/usr/bin/env python3
"""Generate mutated .osu files (from seed maps) for the beatmap differential test.

usage: python3 -I fuzz.py OUTDIR COUNT SEED seed1.osu [seed2.osu ...]
Each output is a seed map with a few random, mostly syntax-level mutations aimed at decoder
edge cases (number formats, missing/extra fields, path types, section headers, encodings,
format versions, line endings, out-of-order lines, extreme values).
"""
import os, sys, random

NUMS = ['0', '-0', '1', '-1', '5', '10', '11', '-5', '0.5', '1e3', '1E-3', '+3', ' 7 ', '\t3', '3\t', '1,5', '1,,0',
        '', ' ', 'NaN', 'nan', 'Infinity', '-Infinity', '∞', '0x10', '1.', '.5', '.', '5e', '1e400', '-1e400',
        '2147483647', '2147483648', '-2147483648', '131072', '131073', '-131072', '1e-320', '0.0001', '99999999999',
        '3.4028235e38', '1\x00', '١', '٣', ' 5', '5 ', '1_000', '0.30000000000000004', '256.75', '-0.0',
        '9000', '9001', '8999', '100000', '1e5', '0.1', '0.09', '1000', '60000', '6', '5.999', '-100', '-1e-300']
PATHTYPES = ['B', 'C', 'L', 'P', 'B3', 'B1', 'B0', 'B-2', 'Bx', 'B 2', 'B99', 'X', 'é', 'b', 'p', 'Ω', 'B2']

def rnum(r):
    if r.random() < 0.5:
        return r.choice(NUMS)
    k = r.random()
    if k < 0.3:
        return str(r.randint(-600, 1000))
    if k < 0.6:
        return repr(r.uniform(-1000, 100000))
    return str(r.randint(-2**31, 2**31))

def mutate_hitobject(r, line):
    f = line.split(',')
    k = r.random()
    if k < 0.25 and f:
        i = r.randrange(len(f)); f[i] = rnum(r)
    elif k < 0.35:
        f = f[:r.randrange(len(f) + 1)]
    elif k < 0.45:
        f.append(rnum(r))
    elif k < 0.55 and len(f) > 3:
        f[3] = str(r.choice([1, 2, 5, 6, 8, 12, 128, 132, 0, 3, 16, 21, 22, 37, 70, 112, 116, 255, -1, 1 | 64, 2 | 16 | 4]))
        if f[3] in ('8', '12') and len(f) > 5: f[5] = str(r.randint(-1000, 300000))
        if f[3] in ('128', '132') and len(f) > 5: f[5] = f'{r.randint(-1000, 300000)}:0:0:0:0:'
    elif len(f) > 5 and '|' in f[5]:
        parts = f[5].split('|')
        k2 = r.random()
        if k2 < 0.25:
            parts[0] = r.choice(PATHTYPES)
        elif k2 < 0.45:
            i = r.randrange(len(parts)); parts.insert(i, parts[i])  # duplicate a point / letter
        elif k2 < 0.6:
            i = r.randrange(1, len(parts) + 1); parts.insert(i, r.choice(PATHTYPES))
        elif k2 < 0.7:
            i = r.randrange(len(parts)); parts[i] = f'{rnum(r)}:{rnum(r)}'
        elif k2 < 0.8:
            parts = parts[:2]
        elif k2 < 0.9:
            # colinear / tiny perfect curves
            x, y = r.randint(0, 512), r.randint(0, 384)
            d = r.choice([0, 1, 2, 1000, 10])
            parts = ['P', f'{x + d}:{y}', f'{x + 2 * d}:{y + r.choice([0, 0, 1, d])}']
        else:
            parts = [r.choice(PATHTYPES)] + [f'{r.randint(-100, 600)}:{r.randint(-100, 500)}' for _ in range(r.randint(0, 12))]
        f[5] = '|'.join(parts)
        if len(f) > 7 and r.random() < 0.3:
            f[7] = rnum(r)
        if len(f) > 6 and r.random() < 0.2:
            f[6] = rnum(r)
    return ','.join(f)

def mutate_timing(r, line):
    f = line.split(',')
    k = r.random()
    if k < 0.4 and f:
        i = r.randrange(len(f)); f[i] = rnum(r)
    elif k < 0.5:
        f = f[:r.randrange(len(f) + 1)]
    elif k < 0.7 and len(f) > 1:
        f[1] = r.choice(['NaN', '-100', '-0', '-1e-300', '-1', '-10000', '0', '1', '5', '-50', '-1000', '333.33333333333337', '-133.33333333333334'])
    elif len(f) > 6:
        f[6] = r.choice(['0', '1', '', '2', 'x', '10'])
    return ','.join(f)

def mutate_kv(r, line):
    if ':' not in line:
        return line
    k, v = line.split(':', 1)
    return k + ':' + (rnum(r) if r.random() < 0.8 else ' ' + v + ' ')

def mutate(r, text):
    lines = text.split('\n')
    sec = [''] * len(lines)
    cur = ''
    for i, l in enumerate(lines):
        if l.strip().startswith('[') and l.strip().endswith(']'):
            cur = l.strip()
        sec[i] = cur
    nmut = r.choice([1, 1, 2, 3, 5, 10, 30])
    for _ in range(nmut):
        i = r.randrange(len(lines))
        l = lines[i].rstrip('\r')
        s = sec[i] if i < len(sec) else ''
        k = r.random()
        if k < 0.05:
            lines[i] = l + ' // comment'
        elif k < 0.08:
            lines.insert(i, r.choice(['[General]', '[Difficulty]', '[TimingPoints]', '[HitObjects]', '[Events]', '[Metadata]',
                                      '[Foo]', '[]', '[ HitObjects ]', '[7]', '[5]', '[3]', '[Events,HitObjects]', '[hitobjects]',
                                      'StackLeniency: ' + rnum(r), 'Mode: ' + r.choice(['0', '1', '3', '4', 'x']),
                                      'ApproachRate:' + rnum(r), 'OverallDifficulty:' + rnum(r), 'CircleSize:' + rnum(r),
                                      'SliderMultiplier:' + rnum(r), 'SliderTickRate:' + rnum(r),
                                      '2,' + rnum(r) + ',' + rnum(r), 'Break,' + rnum(r) + ',' + rnum(r)]))
            sec.insert(i, s)
            continue
        elif k < 0.1:
            j = r.randrange(len(lines)); lines[i], lines[j] = lines[j], lines[i]; continue
        elif k < 0.12:
            lines.insert(i, l); sec.insert(i, s); continue
        elif s == '[HitObjects]' and l and not l.startswith('['):
            lines[i] = mutate_hitobject(r, l)
        elif s == '[TimingPoints]' and l and not l.startswith('['):
            lines[i] = mutate_timing(r, l)
        elif s in ('[Difficulty]', '[General]'):
            lines[i] = mutate_kv(r, l)
        elif s == '[Events]' and l.startswith('2,'):
            f = l.split(','); f[r.randrange(len(f))] = rnum(r); lines[i] = ','.join(f)
    text = '\n'.join(lines)
    k = r.random()
    if k < 0.05:
        text = text.replace('osu file format v14', 'osu file format v' + r.choice(['3', '4', '5', '6', '7', '8', '9', '128', '200', 'x', '']), 1)
        text = text.replace('osu file format v12', 'osu file format v' + r.choice(['3', '4', '5', '7', '128']), 1)
    elif k < 0.07:
        text = '\n\n  \n' + text
    elif k < 0.09:
        text = text.replace('\r\n', '\n').replace('\n', '\r')
    elif k < 0.11:
        text = text.replace('\r\n', '\n')
    elif k < 0.12:
        text = text.split('\n', 1)[1] if '\n' in text else text
    return text

def main():
    out, count, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    seeds = []
    for a in sys.argv[4:]:
        seeds += [l.rstrip('\n') for l in open(a[1:])] if a.startswith('@') else [a]
    os.makedirs(out, exist_ok=True)
    r = random.Random(seed)
    for n in range(count):
        src = r.choice(seeds)
        raw = open(src, 'rb').read()
        bom = raw.startswith(b'\xef\xbb\xbf')
        text = raw.decode('utf-8', errors='surrogateescape')
        if bom: text = text[1:]
        t = mutate(r, text)
        data = t.encode('utf-8', errors='surrogateescape')
        k = r.random()
        if k < 0.03:
            data = b'\xef\xbb\xbf' + data
        elif k < 0.05:
            data = b'\xff\xfe' + t.encode('utf-16-le', errors='replace')
        elif k < 0.07:
            # invalid utf-8 bytes inside a random line
            p = r.randrange(len(data))
            data = data[:p] + r.choice([b'\xff', b'\xc3', b'\xe2\x82', b'\xed\xa0\x80', b'\xf4\x90\x80\x80', b'\xc0\xaf']) + data[p:]
        with open(os.path.join(out, f'f{seed}_{n}.osu'), 'wb') as f:
            f.write(data)

if __name__ == '__main__':
    main()
