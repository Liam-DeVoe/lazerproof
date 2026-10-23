#!/usr/bin/env python3
"""Copy maps with the format version header rewritten (old-version code paths on real geometry).
usage: python3 -I reversion.py OUTDIR SEED file...  (or @listfile)"""
import os, sys, random, re
out, seed = sys.argv[1], int(sys.argv[2])
files = []
for a in sys.argv[3:]:
    files += [l.rstrip('\n') for l in open(a[1:])] if a.startswith('@') else [a]
os.makedirs(out, exist_ok=True)
r = random.Random(seed)
for i, f in enumerate(files):
    b = open(f, 'rb').read()
    v = r.choice([3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 128])
    b2 = re.sub(rb'osu file format v\d+', b'osu file format v%d' % v, b, count=1)
    open(os.path.join(out, f'v{v}_{i}.osu'), 'wb').write(b2)
