#!/usr/bin/env python3
"""Install the Aeneas translation of sim+replay (impl/charon_check.sh --start-from crate::sim
--start-from crate::replay, OUT=<dir>) as a second module set on top of the net+beatmap translation:

  OsuProofs/Generated/SimTypes.lean          (imports Generated.Types)
  OsuProofs/Generated/SimFunsExternal.lean   (hand-written; only checked here, never overwritten)
  OsuProofs/Generated/SimFuns.lean           (imports Generated.Funs + SimTypes + SimFunsExternal)
  OsuProofs/Generated/Sim*_Template.lean     (for reference)

Every top-level item (doc-comment block or `mutual … end` group) whose declared names already exist in
Generated/{Types,Funs,TypesExternal,FunsExternal}.lean is dropped; the script checks that the dropped
copy is textually identical to the existing one (modulo `Source:` lines), so the reachable net/beatmap
functions are *shared* (one definition, already proved) rather than duplicated.

usage: python3 -I proofs/scripts/install_sim_generated.py <OUT>/lean/Gen
"""
import os, re, sys
SRC = sys.argv[1]
P = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
G = os.path.join(P, 'OsuProofs/Generated')

def split(path):
    L = open(path).read().split('\n')
    try:
        s = next(i for i, l in enumerate(L) if l == 'namespace OsuImpl') + 1
        e = max(i for i, l in enumerate(L) if l == 'end OsuImpl')
        head, body, tail = L[:s], L[s:e], L[e:]
    except StopIteration:  # externals templates: no namespace
        s = next(i for i, l in enumerate(L) if l.startswith('/--'))
        head, body, tail = L[:s], L[s:], []
    items = []; i = 0; cur = None
    while i < len(body):
        l = body[i]
        if l == 'mutual':
            j = i + 1
            while body[j] != 'end': j += 1
            items.append(body[i:j + 1]); cur = None; i = j + 1; continue
        if l.startswith('/--') or (cur is None and l.strip()):
            cur = [l]; items.append(cur)
        elif cur is not None: cur.append(l)
        i += 1
    return head, items, tail

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable |private )?(?:def|structure|inductive|axiom|opaque|abbrev|theorem) ([\w.«»]+)', re.M)
def names(item): return set(DECL.findall('\n'.join(item)))
def norm(item): return '\n'.join(l for l in item if not l.strip().startswith('Source:')).strip()

old = {}
for f in ['Types', 'Funs']:
    _, its, _ = split(os.path.join(G, f + '.lean'))
    for it in its:
        for n in names(it): old[n] = norm(it)
for f in ['TypesExternal', 'FunsExternal']:  # hand-written: names only
    for n in DECL.findall(open(os.path.join(G, f + '.lean')).read()): old[n] = None

def install(name, dst, imports, check_same=True):
    head, items, tail = split(os.path.join(SRC, name + '.lean'))
    kept = []; dropped = 0; diff = []
    for it in items:
        ns = names(it)
        if ns and ns <= set(old):
            dropped += 1
            if check_same and any(old[n] is not None and old[n] != norm(it) for n in ns) and not name.endswith('Template'):
                diff.append(sorted(ns)[0])
            continue
        if ns & set(old): diff.append('PARTIAL ' + ','.join(sorted(ns & set(old))))
        kept.append(it)
    head = [l for l in head if not l.startswith('import ')]
    k = next(i for i, l in enumerate(head) if l.startswith('open ')) if any(l.startswith('open ') for l in head) else 0
    head = head[:k] + ['import ' + m for m in imports] + head[k:]
    out = '\n'.join(head) + '\n' + '\n'.join('\n'.join(it) for it in kept) + '\n' + '\n'.join(tail)
    open(os.path.join(G, dst + '.lean'), 'w').write(out)
    print(f'{dst}: kept {len(kept)} items, dropped {dropped} shared; mismatching shared: {diff[:20]}')
    return kept

install('Types', 'SimTypes', ['Aeneas', 'OsuProofs.Generated.Types'])
install('TypesExternal_Template', 'SimTypesExternal_Template', ['Aeneas'])
ext = install('FunsExternal_Template', 'SimFunsExternal_Template', ['Aeneas', 'OsuProofs.Generated.SimTypes'])
install('Funs', 'SimFuns', ['Aeneas', 'OsuProofs.Generated.Funs', 'OsuProofs.Generated.SimTypes',
                            'OsuProofs.Generated.SimFunsExternal'])
print('new external fns needed in SimFunsExternal.lean:', sorted(n for it in ext for n in names(it)))
