#!/usr/bin/env python3
"""Beatmap differential test: lazer (bmtest, C#) vs Lean model (bmdump).

usage: python3 -I run_corpus.py [--work DIR] [--limit N] [--keep] [--mods SPEC] [--reps K] [paths...]

--mods SPEC: give every map an APIMod list (third column of the batch list):
   random:SEED[:ACR,ACR..]   random combinations (in random order) of the given (default: all) mods
   single:SEED:ACR           just ACR with randomised settings
   json:JSON                 the same fixed list for every map
--reps K: test every map K times (with different random mod lists).

Corpus (default): data/beatmaps/*.osu, lazer test resources (*.osu, and *.osu inside *.osz/*.olz archives).
Writes summary to <work>/summary.txt and keeps dumps only for mismatching maps.
"""
import os, sys, subprocess, zipfile, hashlib, argparse, shutil, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import modgen

ROOT = os.path.expanduser('~/lazerproof')
MODEL = os.path.join(ROOT, 'model')
BMTEST = os.path.join(MODEL, 'bmtest/bin/Release/net10.0/bmtest.dll')
BMDUMP = os.path.join(MODEL, '.lake/build/bin/bmdump')

def corpus(extract_dir):
    files = []
    d = os.path.join(ROOT, 'data/beatmaps')
    if os.path.isdir(d):
        files += sorted(os.path.join(d, f) for f in os.listdir(d) if f.endswith('.osu'))
    for res in ['lazer/osu.Game.Tests/Resources', 'lazer/osu.Game.Rulesets.Osu.Tests/Resources']:
        for dp, _, fs in os.walk(os.path.join(ROOT, res)):
            for f in sorted(fs):
                p = os.path.join(dp, f)
                if f.endswith('.osu'):
                    files.append(p)
                elif f.endswith('.osz') or f.endswith('.olz'):
                    try:
                        with zipfile.ZipFile(p) as z:
                            for n in z.namelist():
                                if n.endswith('.osu'):
                                    h = hashlib.sha1((p + '//' + n).encode()).hexdigest()[:12]
                                    out = os.path.join(extract_dir, h + '.osu')
                                    with open(out, 'wb') as o:
                                        o.write(z.read(n))
                                    files.append(out)
                    except zipfile.BadZipFile:
                        pass
    return files

RSS_LIMIT_KB = 1_000_000      # never let one process exceed ~1GB (shared 3.8GB VM)
LEAN_TIMEOUT = 600

def rss_kb(pid):
    try:
        with open(f'/proc/{pid}/status') as f:
            for l in f:
                if l.startswith('VmRSS:'):
                    return int(l.split()[1])
    except OSError:
        pass
    return 0

def run_guarded(cmd, env=None, timeout=LEAN_TIMEOUT):
    """Run cmd; kill it if its RSS exceeds RSS_LIMIT_KB or it exceeds timeout. Returns True on success."""
    p = subprocess.Popen(cmd, env=env)
    t0 = time.time()
    while p.poll() is None:
        if rss_kb(p.pid) > RSS_LIMIT_KB or time.time() - t0 > timeout:
            p.kill(); p.wait()
            return False
        time.sleep(0.2)
    return p.returncode == 0

def norm(lines):
    # error lines: compare only the stage ("error decode" / "error playable"), not the message
    out = []
    for l in lines:
        if l.startswith('error '):
            l = ' '.join(l.split(' ')[:2])
        out.append(l)
    return out

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--work', default=os.path.join(os.environ.get('TMPDIR', '/tmp'), 'bmcorpus'))
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--chunk', type=int, default=200)
    ap.add_argument('--keep', action='store_true')
    ap.add_argument('--mods', default=None)
    ap.add_argument('--reps', type=int, default=1)
    ap.add_argument('paths', nargs='*')
    a = ap.parse_args()
    work = a.work
    os.makedirs(work, exist_ok=True)
    ext = os.path.join(work, 'extracted')
    os.makedirs(ext, exist_ok=True)
    files = a.paths or corpus(ext)
    if a.limit:
        files = files[:a.limit]
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
    # .NET: hard heap cap (fails fast with OutOfMemoryException -> "error playable OutOfMemoryException")
    env = dict(os.environ, DOTNET_ROOT=os.path.expanduser('~/.dotnet'), DOTNET_GCHeapHardLimit='0x28000000')
    dotnet = os.path.expanduser('~/.dotnet/dotnet')
    stats = dict(total=0, identical=0, mismatch=0, skipped_mode=0, both_error=0, skipped_resource=0)
    resource = []
    mism = []
    t0 = time.time()
    for c in range(0, len(files), a.chunk):
        chunk = files[c:c + a.chunk]
        lst = os.path.join(work, 'list.txt')
        with open(lst, 'w') as f:
            for i, p in enumerate(chunk):
                m = modsj[c + i]
                f.write(f'{p}\t{c + i}.txt' + (f'\t{m}' if m else '') + '\n')
        cs, ln = os.path.join(work, 'cs'), os.path.join(work, 'lean')
        for d in (cs, ln):
            os.makedirs(d, exist_ok=True)
        skip = set()
        lines = open(lst).read().splitlines()
        if not run_guarded([dotnet, BMTEST, 'batch', lst, cs], env=env):
            # fall back to one process per map
            for l in lines:
                name = l.split('\t')[1]
                one = os.path.join(work, 'one.txt')
                with open(one, 'w') as f: f.write(l + '\n')
                if not run_guarded([dotnet, BMTEST, 'batch', one, cs], env=env, timeout=300):
                    skip.add(name)
        # maps on which lazer itself runs out of (capped) memory are not run through the model
        for i, _ in enumerate(chunk):
            name = f'{c + i}.txt'
            if name in skip or 'OutOfMemoryException' in open(os.path.join(cs, name), encoding='utf-8').read(200):
                skip.add(name)
        lst2 = os.path.join(work, 'list_lean.txt')
        with open(lst2, 'w') as f:
            for l in lines:
                if l.split('\t')[1] not in skip:
                    f.write(l + '\n')
        if not run_guarded([BMDUMP, 'batch', lst2, ln]):
            # fall back to one process per map
            for l in lines:
                name = l.split('\t')[1]
                if name in skip: continue
                one = os.path.join(work, 'one.txt')
                with open(one, 'w') as f: f.write(l + '\n')
                if not run_guarded([BMDUMP, 'batch', one, ln], timeout=120):
                    skip.add(name)
        for i, p in enumerate(chunk):
            name = f'{c + i}.txt'
            if name in skip:
                stats['total'] += 1; stats['skipped_resource'] += 1; resource.append((p, modsj[c + i]))
                for d in (cs, ln):
                    if os.path.exists(os.path.join(d, name)): os.remove(os.path.join(d, name))
                continue
            a1 = open(os.path.join(cs, name), encoding='utf-8').read().split('\n')
            b1 = open(os.path.join(ln, name), encoding='utf-8').read().split('\n')
            stats['total'] += 1
            if a1 and a1[0].startswith('mode ') and a1[0] != 'mode 0' and a1 == b1:
                stats['skipped_mode'] += 1
            na, nb = norm(a1), norm(b1)
            if na == nb:
                stats['identical'] += 1
                if any(l.startswith('error') for l in na):
                    stats['both_error'] += 1
                if not a.keep:
                    os.remove(os.path.join(cs, name)); os.remove(os.path.join(ln, name))
            else:
                stats['mismatch'] += 1
                k = next(j for j in range(max(len(na), len(nb))) if j >= len(na) or j >= len(nb) or na[j] != nb[j])
                mism.append((p, name, k, na[k] if k < len(na) else '<eof>', nb[k] if k < len(nb) else '<eof>', modsj[c + i]))
                with open(os.path.join(work, 'mism.txt'), 'a') as mf:
                    m = mism[-1]
                    mf.write(f'{m[1]}\t{m[0]}\tline {m[2]}\t{m[5]}\n  C#:   {m[3][:300]}\n  Lean: {m[4][:300]}\n')
        print(f'[{time.time() - t0:.0f}s] {c + len(chunk)}/{len(files)} {stats}', flush=True)
    with open(os.path.join(work, 'summary.txt'), 'w') as f:
        f.write(repr(stats) + '\n')
        for r in resource:
            f.write(f'resource-limit\t{r[0]}\t{r[1]}\n')
        for m in mism:
            f.write(f'{m[1]}\t{m[0]}\tline {m[2]}\t{m[5]}\n  C#:   {m[3][:300]}\n  Lean: {m[4][:300]}\n')
    print(stats)
    for m in mism[:30]:
        print(f'{m[1]} {m[0]} line {m[2]} mods={m[5]}\n  C#:   {m[3][:200]}\n  Lean: {m[4][:200]}')

if __name__ == '__main__':
    main()
