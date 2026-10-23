#!/usr/bin/env python3
"""Install the Aeneas translation of the end-to-end layer (impl/charon_check.sh --start-from crate::eval
--opaque crate::lzma --exclude crate::eval::*text, OUT=<dir>; docs/rust-eval-port.md) as a THIRD module set
on top of net+beatmap (Generated/{Types,Funs}) and sim+replay (Generated/{SimTypes,SimFuns}):

  OsuProofs/Generated/EvalTypes.lean          (imports Generated.SimTypes + EvalTypesExternal)
  OsuProofs/Generated/EvalTypesExternal.lean  (hand-written; the opaque `lzma::LzmaErr` enum)
  OsuProofs/Generated/EvalFunsExternal.lean   (hand-written; never overwritten: the trusted lzma item)
  OsuProofs/Generated/EvalFuns.lean           (imports SimFuns + EvalTypes + EvalFunsExternal)
  OsuProofs/Generated/Eval*_Template.lean     (for reference)

As install_sim_generated.py: every item whose names all exist in the earlier module sets is dropped after
checking that it is textually identical (modulo `Source:` lines); a mismatch means the Rust changed since
that set was generated (regenerate it first).

usage: python3 -I proofs/scripts/install_eval_generated.py <OUT>/lean/Gen
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

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable |private )?(?:def|structure|inductive|axiom|opaque|abbrev|theorem|impl_def|instance)\s+([\w.«»]+)', re.M)
def names(item): return set(DECL.findall('\n'.join(item)))
def norm(item): return '\n'.join(l for l in item if not l.strip().startswith('Source:')).strip()

old = {}
for f in ['Types', 'Funs', 'SimTypes', 'SimFuns']:
    _, its, _ = split(os.path.join(G, f + '.lean'))
    for it in its:
        for n in names(it): old[n] = norm(it)
for f in ['TypesExternal', 'FunsExternal', 'SimFunsExternal']:  # hand-written: names only
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

install('Types', 'EvalTypes', ['Aeneas', 'OsuProofs.Generated.SimTypes', 'OsuProofs.Generated.EvalTypesExternal'])
install('TypesExternal_Template', 'EvalTypesExternal_Template', ['Aeneas'])
ext = install('FunsExternal_Template', 'EvalFunsExternal_Template', ['Aeneas', 'OsuProofs.Generated.EvalTypes'])
install('Funs', 'EvalFuns', ['Aeneas', 'OsuProofs.Generated.SimFuns', 'OsuProofs.Generated.EvalTypes',
                             'OsuProofs.Generated.EvalFunsExternal'])
print('new external fns needed in EvalFunsExternal.lean:', sorted(n for it in ext for n in names(it)))
