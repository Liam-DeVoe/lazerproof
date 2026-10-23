#!/usr/bin/env python3
"""One-off migration (D41): seed $PROOF_REPL/c_*/committed/ from the commit chains of the running server, so that the
restart into the persisting server replays them. A request counts if its .lean starts with `--commit`, its .out says
errors=false, and it was answered after the server start and after the client's last drop (dropped.* file).
usage: repl_seed_committed.py SERVER_START_EPOCH"""
import os, sys, glob, re, shutil
R = os.environ.get('PROOF_REPL', os.path.expanduser('~/lazerproof/data/wip/proof-repl'))
t0 = float(sys.argv[1])
for c in sorted(glob.glob(R + '/c_*')):
    if not os.path.isdir(c) or os.path.exists(c + '/committed'): continue
    drops = [os.path.getmtime(f) for f in glob.glob(c + '/dropped.*') + glob.glob(c + '/committed.dropped.*')]
    tmin = max([t0] + drops)
    reqs = []
    for f in glob.glob(c + '/*.lean'):
        o = f[:-5] + '.out'
        if not os.path.exists(o) or os.path.getmtime(o) < tmin: continue
        src = open(f).read()
        if not src.startswith('--commit'): continue
        if 'errors=false' not in open(o).read(): continue
        reqs.append((os.path.getmtime(o), os.path.basename(f), src))
    if not reqs: continue
    os.makedirs(c + '/committed')
    for i, (_, n, src) in enumerate(sorted(reqs)):
        open(f'{c}/committed/{i + 1:05d}_{n}', 'w').write(src)
    print(f'{os.path.basename(c)}: {len(reqs)} committed requests seeded')
