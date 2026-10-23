#!/usr/bin/env python3
"""Refinement-proof coverage: Aeneas-translated Rust fns (Generated/Funs.lean) vs `<fn>_refines`
theorems in OsuProofs/**/*.lean. Writes docs/proof-status.md and the metrics key
"refinement proofs (net+beatmap)". Only theorems listed in the last axiom audit
(`check_all.sh` output, AUDIT file) with standard axioms count as proved.

usage: python3 -I proofs/scripts/proof_status.py [--audit FILE]
Counted fns: every `def` of the translation except loop bodies/loops (`*_loop*`, `.body`),
trait-instance boilerplate (`.Insts.`), and constants (no parameters). Rust doc comments give
the spec def (`spec \\`X\\``).
"""
import os, re, sys, json, glob, argparse
ROOT = os.path.expanduser('~/lazerproof')
P = os.path.join(ROOT, 'proofs')
ap = argparse.ArgumentParser()
ap.add_argument('--audit', default=os.path.join(P, 'audit.txt'))
a = ap.parse_args()

funs = open(os.path.join(P, 'OsuProofs/Generated/Funs.lean')).read()
# sim+replay translation (second module set, D25): its fns are listed in a separate section
_sf = os.path.join(P, 'OsuProofs/Generated/SimFuns.lean')
if os.path.exists(_sf): funs += '\n' + open(_sf).read()
# eval translation (third module set, D35): own section
_ef = os.path.join(P, 'OsuProofs/Generated/EvalFuns.lean')
if os.path.exists(_ef): funs += '\n' + open(_ef).read()
blocks = re.split(r'\n(?=/-- \[osu_eval_core::)', funs)
fns = []  # (lean name, rust path, src file, line)
for b in blocks:
    m = re.match(r'/-- \[osu_eval_core::([^\]]+)\][^\n]*\n\s*Source: \'([^\']+)\', lines (\d+)', b)
    d = re.search(r'^def ([\w.]+)(.*)$', b, re.M)
    if not m or not d: continue
    name, rest = d.group(1), d.group(2)
    if '.Insts.' in name or '_loop' in name or name.endswith('.body'): continue
    # constants: `def X : T :=` (no binders before the colon)
    if re.match(r'\s*:', rest): continue
    fns.append((name, m.group(1), m.group(2), int(m.group(3))))

def spec_of(src, line):
    p = os.path.join(ROOT, 'impl', src) if src.startswith('osu_eval_core/') else os.path.join(ROOT, 'impl/osu_eval_core', src)
    if not os.path.exists(p): return ''
    L = open(p).read().split('\n')
    i = line - 2; doc = []
    while i >= 0 and L[i].strip().startswith(('///', '#[')):
        doc.insert(0, L[i]); i -= 1
    m = re.findall(r'spec `([^`]+)`', ' '.join(doc))
    if not m and src.startswith(('osu_eval_core/src/sim/', 'osu_eval_core/src/replay/')):
        m = re.findall(r'`([^`]+)`', ' '.join(doc))  # sim port: the first backticked name is the spec def
    return m[0] if m else ''

# D44 soundness bookkeeping: a refinement theorem is CONDITIONAL if it assumes another (unproved) refinement, i.e.
# (a) it carries a tag line `-- CONDITIONAL: <hyps> (<what is owed>)` right before it (or in its docstring), or
# (b) a hypothesis type contains `= ok`, `_refines` or `EvalAssumptions` whose subject is not one of the theorem's
#     own parameters (instance parameters such as `(C : Clone T) (hC : ∀ x, C.clone x = ok x)` are parametric, not
#     conditional); override a false positive with `-- NOT-CONDITIONAL: <reason>`.
# It is a FRAGMENT if tagged `-- FRAGMENT-OF: <spec def> (<bridge owed>)` (stated against a local copy of a spec body).
COND_RE = re.compile(r'=\s*ok\b|_refines\b|\bEvalAssumptions\b')
# hypotheses that are trusted boundaries / input bounds (docs/proof-pipeline.md §5), never CONDITIONAL
TRUSTED_HYPS = {'ev_lzmaBound', 'InputBounds', 'PlayableBounds', 'GpbBounds', 'LoadBounds'}
# named `def X : Prop :=` hypotheses whose body assumes a refinement (`= ok` / `_refines` / EvalAssumptions)
PROP_COND = set()
for _f in glob.glob(os.path.join(P, 'OsuProofs/**/*.lean'), recursive=True):
    if '/Generated/' in _f: continue
    for _m in re.finditer(r'^(?:@\[[^\]\n]*\]\s*)?(?:def|structure) ([\w.]+)[^\n:]*:\s*Prop\s*(?::=|where)(.*?)(?:\n\s*\n|\Z)', open(_f).read(), re.M | re.S):
        if COND_RE.search(_m.group(2)) and _m.group(1) not in TRUSTED_HYPS: PROP_COND.add(_m.group(1))
def _binders(txt, i):
    out, n = [], len(txt)
    while True:
        while i < n and txt[i] in ' \t\n': i += 1
        if i >= n or txt[i] not in '({[⦃': return out
        depth, j = 0, i
        while j < n:
            if txt[j] in '({[⦃': depth += 1
            elif txt[j] in ')}]⦄': depth -= 1
            if depth == 0: break
            j += 1
        out.append(txt[i + 1:j]); i = j + 1
def _classify(txt, m):
    blk = txt[max(0, m.start() - 1500):m.start()].split('\n\n')[-1]
    tags = {}
    for k in ('NOT-CONDITIONAL', 'CONDITIONAL', 'FRAGMENT-OF'):
        t = re.search(r'(?<![\w-])' + k + r':\s*([^\n]*?)\s*(?:-/)?\s*$', blk, re.M)
        if t: tags[k] = t.group(1)
    params, hyps = set(), []
    for b in _binders(txt, m.end()):
        if ':' not in b: continue
        nm, ty = b.split(':', 1)
        names = nm.split()
        thead = re.match(r'\s*([\w.]+)', ty)
        thead = thead.group(1) if thead else ''
        if thead in TRUSTED_HYPS or 'System.Platform.numBits' in ty: pass
        elif thead in PROP_COND:
            if not DISCHARGED.get(thead): hyps += names
        elif COND_RE.search(ty):
            body = re.sub(r'^\s*((∀|∃)[^,]*,\s*)+', '', ty.strip())
            head = re.match(r'[\w.]+', body)
            subj = head.group(0).split('.')[0] if head else ''
            if subj not in params: hyps += names
        params |= set(names)
    if 'NOT-CONDITIONAL' in tags: hyps = []
    if 'FRAGMENT-OF' in tags: return 'FRAGMENT', tags['FRAGMENT-OF']
    if 'CONDITIONAL' in tags: return 'CONDITIONAL', tags['CONDITIONAL']
    if hyps: return 'CONDITIONAL', ' '.join(hyps) + ' (auto-detected)'
    return '', ''
audit = {}
if os.path.exists(a.audit):
    txt = open(a.audit).read()
    # keyed by the full theorem name (`<fn>_refines` or a `<fn>_refines_<suffix>` variant)
    for m in re.finditer(r"'OsuProofs\.([\w.']+)' depends on axioms: \[([^\]]*)\]", txt):
        ax = set(x.strip() for x in m.group(2).split(','))
        audit[m.group(1)] = ax <= {'propext', 'Classical.choice', 'Quot.sound'}
    for m in re.finditer(r"'OsuProofs\.([\w.']+)' does not depend on any axioms", txt):
        audit[m.group(1)] = True
# a named owed-refinement Prop hypothesis is discharged if an audited theorem concludes exactly it (`theorem t .. : X :=`)
DISCHARGED = {}; _disc_cand = []
for _f in glob.glob(os.path.join(P, 'OsuProofs/**/*.lean'), recursive=True):
    if '/Generated/' in _f: continue
    _t = open(_f).read()
    for _m in re.finditer(r'^theorem ([\w.]+)[^\n]*:\s*([\w.]+)\s*(?::=|where)', _t, re.M):
        # the discharge lemma must itself be unconditional (its own hypotheses trusted / input / discharged)
        _mm = re.search(r'^theorem ' + re.escape(_m.group(1)) + r'\b', _t[_m.start():], re.M)
        if _m.group(2) in PROP_COND and audit.get(_m.group(1)): _disc_cand.append((_m.group(2), _m.group(1), _t, _m.start() + _mm.end()))
class _M:  # minimal match object for _classify
    def __init__(self, s, e): self._s, self._e = s, e
    def start(self): return self._s
    def end(self): return self._e
for _ in range(4):
    for _x, _th, _t, _e in _disc_cand:
        if _x not in DISCHARGED and not _classify(_t, _M(_e - len(_th) - 8, _e))[0]: DISCHARGED[_x] = _th
thms = {}; alts = {}
for f in glob.glob(os.path.join(P, 'OsuProofs/**/*.lean'), recursive=True):
    if '/Generated/' in f: continue
    _txt = open(f).read()
    for m in re.finditer(r'^(?:@\[[^\]\n]*\]\s*)?(?:protected\s+)?theorem ([\w.]+)_refines\b', _txt, re.M):
        thms[m.group(1)] = (os.path.relpath(f, P), m.group(1) + '_refines') + _classify(_txt, m)
    # variants `<fn>_refines_<suffix>` (e.g. `_gen`: the same statement with a conditional hypothesis discharged)
    for m in re.finditer(r'^(?:@\[[^\]\n]*\]\s*)?(?:protected\s+)?theorem ([\w.]+?)_refines_(\w+)\b', _txt, re.M):
        alts.setdefault(m.group(1), []).append((os.path.relpath(f, P), m.group(1) + '_refines_' + m.group(2))
                                               + _classify(_txt, m))
# D67 classification overrides (scripts/class_overrides.txt): CONDITIONAL tags on ordinary preconditions -> proved
OVERRIDES = {}; FRAG_OVR = {}
for l in open(os.path.join(P, 'scripts/class_overrides.txt')):
    if l.strip() and not l.startswith('#'):
        _p = l.split(None, 2)
        if len(_p) >= 2 and _p[1] == 'proved': OVERRIDES[_p[0]] = _p[2].strip() if len(_p) > 2 else ''
        if len(_p) >= 2 and _p[1] == 'fragment': FRAG_OVR[_p[0]] = _p[2].strip() if len(_p) > 2 else ''
# alias table (scripts/refines_aliases.txt): refinement theorems not named `<fn>_refines`
for l in open(os.path.join(P, 'scripts/refines_aliases.txt')):
    if not l.strip() or l.startswith('#'): continue
    fn, th, kind, note = (l.split(None, 3) + [''])[:4]
    alts.setdefault(fn, []).append(('(alias)', th, '' if kind == 'proved' else 'FRAGMENT', note.strip()))
# a fn whose `<fn>_refines` is missing / unaudited / CONDITIONAL / FRAGMENT is credited to an audited, unconditional
# variant `<fn>_refines_<suffix>` if there is one (D44: e.g. mods.apply_to_beatmap_refines_gen discharges hRD/hTP)
for fn, vs in alts.items():
    cur = thms.get(fn)
    if cur and audit.get(cur[1]) and not cur[2]: continue
    for v in vs:
        if audit.get(v[1]) and not v[2]:
            thms[fn] = v; break
    else:
        if not (cur and audit.get(cur[1])):
            for v in vs:
                if audit.get(v[1]): thms[fn] = v; break

scope = [f for f in fns if f[0].startswith(('net.', 'beatmap.')) or f[0].startswith('net')]
rows = []; proved = 0
for name, rpath, src, line in fns:
    st = 'open'
    if name in thms:
        st = 'proved' if audit.get(thms[name][1]) else 'stated (not in audit)'
        if audit.get(thms[name][1]) is False: st = 'NONSTANDARD AXIOMS'
        kind, why = thms[name][2], thms[name][3]
        if kind == 'CONDITIONAL' and name in OVERRIDES: kind, why = '', ''
        if name in FRAG_OVR and not kind: kind, why = 'FRAGMENT', FRAG_OVR[name]
        if st == 'proved' and kind: st = f'{kind} ({why})'
    if st == 'proved' and (name.startswith('net.') or name.startswith('beatmap.')): proved += 1
    rows.append((spec_of(src, line), name, rpath, thms.get(name, ('', ''))[1], st))
# D63 COVERED: a fn without its own proved refinement whose EVERY Rust call site (call graph of Generated/*Funs) lies
# inside a proved fn, or transitively inside covered ones (cycles only via an outside proved entry). Not in the
# headline "proved" count; the end-to-end finish line uses proved + covered.
fnset = {r[1] for r in rows}
def _root(n):
    if n in fnset: return n
    m = re.match(r'^(.*?)(?:_loop\d*)+(?:\.body)?$', n)
    return m.group(1) if m and m.group(1) in fnset else n
callers = {}
for b in blocks:
    d = re.search(r'^def ([\w.]+)', b, re.M)
    if not d: continue
    me = _root(d.group(1))
    for tok in set(re.findall(r'[\w.]+', b[d.start():])):
        if tok in fnset and tok != me: callers.setdefault(tok, set()).add(me)
provedset = {r[1] for r in rows if r[4] == 'proved'}
C = {f for f in fnset if f not in provedset and callers.get(f)}
changed = True
while changed:
    changed = False
    for f in list(C):
        if any(c not in provedset and c not in C for c in callers[f]): C.discard(f); changed = True
reach, todo = set(), [f for f in C if any(c in provedset for c in callers[f])]
while todo:
    f = todo.pop()
    if f in reach: continue
    reach.add(f); todo += [g for g in C if f in callers[g]]
covered = C & reach
rows = [(sp, n, rp, th, (f'COVERED (callers: {", ".join(sorted(callers[n]))}; was: {st})' if n in covered else st))
        for sp, n, rp, th, st in rows]
frag_uncovered = sorted((n, st) for sp, n, rp, th, st in rows if st.startswith('FRAGMENT'))
def _cnt(rs, k): return sum(1 for r in rs if r[4].startswith(k))
tot = sum(1 for r in rows if r[1].startswith(('net.', 'beatmap.')))
out = ['# Refinement proof status (generated by proofs/scripts/proof_status.py)', '',
       'Categories (D44): **proved** = unconditional, against the real spec def (the only ones counted); '
       '**CONDITIONAL** = assumes another refinement (hypotheses listed; tag `-- CONDITIONAL: ...` or auto-detected '
       '`= ok`/`_refines`/`EvalAssumptions` hypotheses); **FRAGMENT** = against a local copy of a spec body '
       '(tag `-- FRAGMENT-OF: ...`). Done = 0 CONDITIONAL and 0 FRAGMENT.', '',
       '**COVERED** (D63) = no own proof, but every Rust call site lies inside a proved (or covered) fn; not counted as '
       'proved; the end-to-end finish line uses proved + covered.', '',
       f'net+beatmap: **{proved}/{tot}** Rust functions proved to refine their spec def, covered '
       f'{_cnt([r for r in rows if r[1].startswith(("net.", "beatmap."))], "COVERED")} ('
       f'{_cnt([r for r in rows if r[1].startswith(("net.", "beatmap."))], "CONDITIONAL")} more CONDITIONAL, '
       f'{_cnt([r for r in rows if r[1].startswith(("net.", "beatmap."))], "FRAGMENT")} FRAGMENT) '
       '(`impl x = ok (spec x)` or the guarded form in the theorem docstring); axioms checked by '
       '`proofs/scripts/check_all.sh` (`#print axioms`). Constants, loop helpers and derive boilerplate are not counted '
       '(constants are covered inside the proofs that use them; loops by their function\'s theorem).', '',
       '| Lean spec def | Rust fn (Aeneas name) | theorem | status |', '|---|---|---|---|']
SIM = ('sim.', 'replay.')
for spec, name, rpath, thm, st in sorted(rows, key=lambda r: r[1]):
    if name.startswith(SIM) or name.startswith('eval.'): continue
    out.append(f'| {spec or "—"} | `{name}` | {("`"+thm+"`") if thm else ""} | {st} |')
srows = [r for r in rows if r[1].startswith(SIM)]
sproved = sum(1 for r in srows if r[4] == 'proved')
out += ['', '## Sim + replay (Generated/SimFuns.lean; spec OsuModel.Sim/Replay at 1b0a176, D20/D25)', '',
        f'sim+replay: **{sproved}/{len(srows)}** Rust functions proved (same counting rules); '
        f'covered {_cnt(srows, "COVERED")}; {_cnt(srows, "CONDITIONAL")} CONDITIONAL, {_cnt(srows, "FRAGMENT")} FRAGMENT.', '',
        '| Lean spec def | Rust fn (Aeneas name) | theorem | status |', '|---|---|---|---|']
for spec, name, rpath, thm, st in sorted(srows, key=lambda r: r[1]):
    out.append(f'| {spec or "—"} | `{name}` | {("`"+thm+"`") if thm else ""} | {st} |')
erows = [r for r in rows if r[1].startswith('eval.')]
eproved = sum(1 for r in erows if r[4] == 'proved')
out += ['', '## Eval (Generated/EvalFuns.lean; end-to-end layer, D35)', '',
        f'eval: **{eproved}/{len(erows)}** Rust functions proved (same counting rules); '
        f'covered {_cnt(erows, "COVERED")}; {_cnt(erows, "CONDITIONAL")} CONDITIONAL, {_cnt(erows, "FRAGMENT")} FRAGMENT.', '',
        '| Lean spec def | Rust fn (Aeneas name) | theorem | status |', '|---|---|---|---|']
for spec, name, rpath, thm, st in sorted(erows, key=lambda r: r[1]):
    out.append(f'| {spec or "—"} | `{name}` | {("`"+thm+"`") if thm else ""} | {st} |')
out += ['', '## FRAGMENT not covered (D63 call-graph check)', '',
        'FRAGMENT-tagged / aliased fns that the call graph does NOT credit as COVERED (some Rust call site is outside '
        'every proved/covered fn, or the parent is not proved yet); a `FRAGMENT-OF <parent>` tag alone never counts.', '']
for n, st in frag_uncovered:
    out.append(f'- `{n}`: {st}; callers: {", ".join(sorted(callers.get(n, ()))) or "none"}')
_ps = os.path.join(ROOT, 'docs/proof-status.md')
# keep the hand-maintained "## Hard residue" section (everything from that heading on) across regenerations
_old = open(_ps).read() if os.path.exists(_ps) else ''
_tail = _old[_old.index('\n## Hard residue'):] if '\n## Hard residue' in _old else ''
open(_ps, 'w').write('\n'.join(out) + '\n' + _tail)
mp = os.path.join(ROOT, 'status/metrics.json')
mj = json.load(open(mp))
mj['refinement proofs (net+beatmap)'] = f'{proved}/{tot} functions proved'
mj['refinement proofs (sim+replay)'] = f'{sproved}/{len(srows)} functions proved'
mj['refinement proofs (eval)'] = f'{eproved}/{len(erows)} functions proved'
mj['refinement proofs: conditional/fragment (D44)'] = f'{_cnt(rows, "CONDITIONAL")} conditional, {_cnt(rows, "FRAGMENT")} fragment (not counted as proved)'
mj['refinement proofs: covered (D63)'] = (f'net+beatmap {_cnt([r for r in rows if r[1].startswith(("net.", "beatmap."))], "COVERED")}, '
    f'sim+replay {_cnt(srows, "COVERED")}, eval {_cnt(erows, "COVERED")} (inside proved parents; not counted as proved)')
json.dump(mj, open(mp, 'w'), indent=1, ensure_ascii=False)
print(f'{proved}/{tot} (all translated incl. POC: {len(rows)}); sim+replay {sproved}/{len(srows)}; eval {eproved}/{len(erows)}; COVERED {_cnt(rows, "COVERED")}, CONDITIONAL {_cnt(rows, "CONDITIONAL")}, FRAGMENT {_cnt(rows, "FRAGMENT")}')
