#!/usr/bin/env python3
"""Rust port vs Lean model on beatmaps: `bmdump_rs` vs `bmdump`, byte-identical dumps required.

usage: python3 -I impl/scripts/bm_rs_vs_lean.py [--work DIR] [--limit N] [--chunk N] [--mods SPEC] [--reps K] [paths...]
--mods SPEC as in model/bmtest/run_corpus.py (random:SEED[:ACR,..] | single:SEED:ACR | json:JSON).
Default corpus = run_corpus.corpus() (data/beatmaps + lazer test resources). Reports maps/s of both.
"""
import os, sys, time, argparse, random, subprocess
ROOT = os.path.expanduser('~/lazerproof')
sys.path.insert(0, os.path.join(ROOT, 'model/bmtest'))
import run_corpus, modgen

BMDUMP = os.path.join(ROOT, 'model/.lake/build/bin/bmdump')
BMDUMP_RS = os.environ.get('BMDUMP_RS') or os.path.join(ROOT, 'impl/target/release/bmdump_rs')

def run_timed(cmd, timeout):
    t0 = time.time()
    ok = run_corpus.run_guarded(cmd, timeout=timeout)
    return ok, time.time() - t0

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--work', default='/tmp/bm_rs_vs_lean')
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--chunk', type=int, default=50)
    ap.add_argument('--mods', default=None)
    ap.add_argument('--reps', type=int, default=1)
    ap.add_argument('--keep', action='store_true')
    ap.add_argument('paths', nargs='*')
    a = ap.parse_args()
    os.makedirs(a.work, exist_ok=True)
    ext = os.path.join(a.work, 'extracted'); os.makedirs(ext, exist_ok=True)
    files = a.paths or run_corpus.corpus(ext)
    if a.limit: files = files[:a.limit]
    files = [f for f in files for _ in range(a.reps)]
    modsj = [None] * len(files)
    if a.mods:
        kind, _, rest = a.mods.partition(':')
        if kind == 'json':
            modsj = [rest] * len(files)
        else:
            seed, _, accs = rest.partition(':')
            rng = random.Random(int(seed))
            allowed = accs.split(',') if accs else None
            modsj = [modgen.gen_mods(rng, allowed, single=(accs if kind == 'single' else None)) for _ in files]
    st = dict(total=0, identical=0, mismatch=0, skipped=0, errors=0)
    tl = tr = 0.0
    nl = nr = 0
    mism = []
    t0 = time.time()
    for c in range(0, len(files), a.chunk):
        chunk = files[c:c + a.chunk]
        lst = os.path.join(a.work, 'list.txt')
        lines = [f'{p}\t{c + i}.txt' + (f'\t{modsj[c + i]}' if modsj[c + i] else '') for i, p in enumerate(chunk)]
        open(lst, 'w').write('\n'.join(lines) + '\n')
        dl, dr = os.path.join(a.work, 'lean'), os.path.join(a.work, 'rust')
        os.makedirs(dl, exist_ok=True); os.makedirs(dr, exist_ok=True)
        skip = set()
        okr, t = run_timed([BMDUMP_RS, 'batch', lst, dr], 600)
        if okr: tr += t; nr += len(chunk)
        okl, t = run_timed([BMDUMP, 'batch', lst, dl], 1200)
        if okl: tl += t; nl += len(chunk)
        if not (okl and okr):
            one = os.path.join(a.work, 'one.txt')
            for l in lines:
                name = l.split('\t')[1]
                open(one, 'w').write(l + '\n')
                if not okr and not run_corpus.run_guarded([BMDUMP_RS, 'batch', one, dr], timeout=120): skip.add(name)
                if not okl and name not in skip and not run_corpus.run_guarded([BMDUMP, 'batch', one, dl], timeout=300): skip.add(name)
        for i, p in enumerate(chunk):
            name = f'{c + i}.txt'
            st['total'] += 1
            fl, fr = os.path.join(dl, name), os.path.join(dr, name)
            if name in skip or not os.path.exists(fl) or not os.path.exists(fr):
                st['skipped'] += 1
                mism.append(('SKIP', p, modsj[c + i], '', ''))
                continue
            bl, br = open(fl, 'rb').read(), open(fr, 'rb').read()
            if bl == br:
                st['identical'] += 1
                if b'error ' in bl[:400]: st['errors'] += 1
                if not a.keep: os.remove(fl); os.remove(fr)
            else:
                st['mismatch'] += 1
                L, R = bl.decode('utf-8', 'replace').split('\n'), br.decode('utf-8', 'replace').split('\n')
                k = next(j for j in range(max(len(L), len(R))) if j >= len(L) or j >= len(R) or L[j] != R[j])
                mism.append((name, p, modsj[c + i], L[k] if k < len(L) else '<eof>', R[k] if k < len(R) else '<eof>'))
        print(f'[{time.time() - t0:.0f}s] {c + len(chunk)}/{len(files)} {st}  lean {nl / max(tl, 1e-9):.1f} maps/s  rust {nr / max(tr, 1e-9):.1f} maps/s', flush=True)
    with open(os.path.join(a.work, 'summary.txt'), 'w') as f:
        f.write(f'{st} lean_maps_per_s={nl / max(tl, 1e-9):.2f} rust_maps_per_s={nr / max(tr, 1e-9):.2f}\n')
        for m in mism:
            f.write(f'{m[0]}\t{m[1]}\t{m[2]}\n  Lean: {m[3][:300]}\n  Rust: {m[4][:300]}\n')
    print(st, f'lean {nl / max(tl, 1e-9):.2f} maps/s, rust {nr / max(tr, 1e-9):.2f} maps/s')
    for m in mism[:20]:
        print(f'{m[0]} {m[1]} mods={m[2]}\n  Lean: {m[3][:200]}\n  Rust: {m[4][:200]}')
    return 0 if st['mismatch'] == 0 else 1

if __name__ == '__main__':
    sys.exit(main())
