#!/usr/bin/env python3
"""Batch refinement prover. For every open Rust fn (docs/proof-status.md) that has a spec def
(`/// spec \\`X\\`` in the Rust source), in translation order (callees first), it generates

  theorem <fn>_refines (args) : ∃ r, <fn> args = ok r ∧ <spec> (abs a₁) … = abs r
  @[step] theorem <fn>_step (args) : <fn> args ⦃ r => <spec> (abs a₁) … = abs r ⦄

(`abs` = `AbsTo.abs`, OsuProofs/Auto/Abs.lean + generated instances) and tries a few proof
scripts (simp evaluation of straight-line code; `step*` over registered callee specs). Blocks that
elaborate are committed to the REPL client (so later callers can use them) and written to OUT.

usage: auto_prove.py OUT [--only REGEX] [--limit N]
Env: REPL_DIR = a REPL client dir (`<repl>/c_<name>`) whose environment already contains
Auto/Abs.lean, the generated instances and constant lemmas (see RESUME "refinement proofs").
"""
import os, re, sys, argparse, time
sys.path.insert(0, os.path.dirname(__file__))
from repl_client import submit, errors
ROOT = os.path.expanduser('~/lazerproof'); P = ROOT + '/proofs'
ap = argparse.ArgumentParser()
ap.add_argument('out'); ap.add_argument('--only', default=''); ap.add_argument('--limit', type=int, default=10**9)
ap.add_argument('--timeout', type=int, default=300)
a = ap.parse_args()
client = os.environ['REPL_DIR']

PRELUDE = open(os.environ.get('AUTO_PRELUDE', P + '/scripts/auto_prelude.lean')).read()
PRIMS = ('float.F64.add float.F64.sub float.F64.mul float.F64.div float.F64.neg float.F64.lt float.F64.le '
         'float.F64.eq float.F64.is_nan float.F64.abs float.F64.floor float.F64.ceil float.F64.trunc float.F64.sqrt '
         'float.F64.to_f32 float.F64.from_i64 float.F64.from_u64 float.F64.sin float.F64.cos float.F64.acos '
         'float.F64.atan2 float.F64.exp float.F64.log float.F64.pow float.F64.fmod float.F32.add float.F32.sub '
         'float.F32.mul float.F32.div float.F32.neg float.F32.lt float.F32.le float.F32.eq float.F32.is_nan '
         'float.F32.abs float.F32.floor float.F32.ceil float.F32.trunc float.F32.sqrt float.F32.to_f64 '
         'float.F32.from_i64 float.F32.from_u64 float.F32.sin float.F32.cos float.F32.atan2 '
         'float.F64.to_i32_sat float.F64.to_i64_sat float.F32.to_i32_sat').split()
ABSL = ['i32S_toInt', 'hRel'] + ['OsuModel.Beatmap.Settings.' + x for x in 'sBool sInt sDouble sFloat sEnum sSeed sDiff rateDT rateHT'.split()]

# ---- translation defs, in file order
funs = open(P + '/OsuProofs/Generated/Funs.lean').read()
defs = []
for m in re.finditer(r'^def\s+([\w.]+)((?:\s*\([^()]*\))*)\s*:\s*\n?\s*Result ([^:]+?)\s*:=', funs, re.M):
    params = re.findall(r'\((\S+) : ([^()]*)\)', m.group(2))
    defs.append((m.group(1), params, m.group(3).strip(), m.start()))
defpos = {d[0]: d for d in defs}

# ---- spec defs: full names
specs = []; sconsts = []
for dp, _, fs in os.walk(ROOT + '/model/OsuModel'):
    for fn in fs:
        if not fn.endswith('.lean'): continue
        ns = []
        for l in open(os.path.join(dp, fn)):
            mn = re.match(r'^namespace ([\w.]+)', l)
            if mn: ns.append(mn.group(1)); continue
            me = re.match(r'^end ([\w.]+)', l)
            if me and ns and ns[-1] == me.group(1): ns.pop(); continue
            md = re.match(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |partial |noncomputable )*def ([\w.]+)(\s*:)?', l)
            if md:
                specs.append('.'.join(ns + [md.group(1)]))
                if md.group(2): sconsts.append('.'.join(ns + [md.group(1)]))
def resolve(sp):
    c = [s for s in specs if s == sp or s.endswith('.' + sp)]
    return c[0] if len(c) == 1 else None

import glob
have = set()
for f in glob.glob(P + '/OsuProofs/**/*.lean', recursive=True):
    if '/Generated/' in f: continue
    have |= set(re.findall(r'^theorem ([\w.]+)_refines\b', open(f).read(), re.M))
# hand-written equation-form refinements `f args = ok (..)` (usable as simp rewrites in the simp script)
EQS = []
for f in glob.glob(P + '/OsuProofs/**/*.lean', recursive=True):
    if '/Generated/' in f or '/Auto/' in f or '/Post/' in f or f.endswith('/Schedule.lean'): continue
    for m in re.finditer(r'^theorem ([\w.]+_refines)\b(.*?):=', open(f).read(), re.M | re.S):
        head = m.group(2)
        if '\ntheorem ' in head or '∃' in head or ' = ok ' not in head: continue
        EQS.append(m.group(1))
SC = [c for c in sconsts if c.startswith(('OsuModel.Beatmap.', 'OsuModel.Net.'))]
_out = submit(PRELUDE + '\n'.join(f'#check @{c}' for c in SC + EQS) + '\n', client, timeout=a.timeout)
_bad = {ln for ln, _, _ in errors(_out or '')}
_off = PRELUDE.count('\n') + 1
_ok = [c for k, c in enumerate(SC + EQS) if (k + _off) not in _bad]
SC = [c for c in SC if c in _ok]; EQS = [c for c in EQS if c in _ok]
print(f'{len(SC)} spec consts, {len(EQS)} equation lemmas usable', file=sys.stderr)
status = open(ROOT + '/docs/proof-status.md').read()
openf = {m.group(2): m.group(1) for m in re.finditer(r'^\| (.*?) \| `([\w.]+)` \|  \| open \|', status, re.M)}

def closing(spec):
    return f'simp_all [{spec}, abs, {", ".join(ABSL + SC)}]'
def script_simp(fn, spec):
    return (f'  refine ⟨?r, ?h1, ?h2⟩\n'
            f'  case h1 => unfold {fn}; simp [{", ".join(PRIMS + EQS)}, lift]; try rfl\n'
            f'  case h2 => {closing(spec)} <;> first | rfl | decide | skip')
def script_step(fn, spec, args):
    return (f'  apply eq_ok_of_spec\n'
            f'  unfold {fn}\n'
            f'  try simp only [{", ".join(PRIMS)}, lift, bind_ok]\n'
            f'  step* <;> {closing(spec)} <;> first | rfl | decide | skip')

S_ = 'OsuModel.Beatmap.Settings.'
OVERRIDE = {
  'beatmap.mod_settings.s_bool': S_ + 'sBool (abs key) (abs d) = abs r',
  'beatmap.mod_settings.s_bool_plain': S_ + 'sBool (abs key) (abs d) false = abs r',
  'beatmap.mod_settings.s_int': S_ + 'sInt (abs key) (abs d) (abs mn) (abs mx) = abs r',
  'beatmap.mod_settings.s_double': S_ + 'sDouble (abs key) (abs d) (abs mn) (abs mx) (abs p) = abs r',
  'beatmap.mod_settings.s_float': S_ + 'sFloat (abs key) (abs d) (abs mn) (abs mx) (abs p) (abs precision_first) = abs r',
  'beatmap.mod_settings.s_seed': S_ + 'sSeed = abs r',
  'beatmap.mod_settings.s_diff': S_ + 'sDiff (abs key) (abs ext_min) = abs r',
}
# constant-like table fns: `table_xx : Result (Vec SettingDef)`  ↦  `Settings.table "XX" = some (abs r)`
for m in re.finditer(r'^def (beatmap\.mod_settings\.table_([a-z]+))\s*\n?\s*: Result \(alloc\.vec\.Vec beatmap\.mod_settings\.SettingDef\)', funs, re.M):
    OVERRIDE[m.group(1)] = S_ + f'table "{m.group(2).upper()}" = some (abs r)'
    if m.group(1) not in defpos: defs.append((m.group(1), [], 'x', m.start()))
defs.sort(key=lambda d: d[3]); defpos = {d[0]: d for d in defs}

blocks = []
for name, params, ret, pos in defs:
    if name not in openf or name in have or not name.startswith('beatmap.'): continue
    if a.only and not re.search(a.only, name): continue
    sp = openf[name]
    full = None if name in OVERRIDE else (resolve(sp) if sp not in ('—', '') else None)
    if not full and name not in OVERRIDE: continue
    if any('Inst' in t or t.strip().startswith('(') for _, t in params): continue
    binders = ' '.join(f'({p} : {t})' for p, t in params)
    args = ' '.join(p for p, _ in params)
    aargs = ' '.join(f'(abs {p})' for p, _ in params)
    post = OVERRIDE.get(name) or f'{full} {aargs} = abs r'
    if name not in OVERRIDE and 'beatmap.hit_object_parser.DecodeError' in ret:
        # Rust `Result<T, DecodeError>` vs spec `DecodeM` (Except String): HitObjectParser.hRel (errors match as errors)
        post = f'hRel abs r ({full} {aargs})'
    full = full or (OVERRIDE[name].split()[0])
    thm = name + '_refines'
    for k, scr in enumerate([script_simp(name, full), script_step(name, full, args)]):
        blk = (f'theorem {thm} {binders} :\n    ∃ r, {name} {args} = ok r ∧ {post} := by\n{scr}\n\n'
               f'@[step] theorem {name}_step {binders} :\n    {name} {args} ⦃ r => {post} ⦄ :=\n'
               f'  spec_of_ex ({thm} {args})')
        blocks.append((name, k, blk))
    if len({b[0] for b in blocks}) >= a.limit: break

# try per fn: first script that elaborates without errors (and without sorry) is committed
kept = []; tried = 0; t0 = time.time()
byfn = {}
for n, k, b in blocks: byfn.setdefault(n, []).append(b)
for n, bs in byfn.items():
    tried += 1; ok = False
    for b in bs:
        out = submit(PRELUDE + '\n' + b + '\n', client, timeout=a.timeout)
        if out is None: print(f'TIMEOUT {n}', file=sys.stderr); break
        if not errors(out) and 'sorry' not in out:
            co = submit(PRELUDE + '\n' + b + '\n', client, commit=True, timeout=a.timeout)
            if co is None or errors(co): print(f'COMMIT-FAIL {n}', file=sys.stderr); break
            kept.append(b); ok = True; break
    print(f'{"OK  " if ok else "fail"} {n}', file=sys.stderr, flush=True)
open(a.out, 'w').write('\n\n'.join(kept) + '\n')
print('(new blocks only; append them to the body of OsuProofs/Auto/Gen.lean)', file=sys.stderr)
print(f'auto-proved {len(kept)}/{tried} candidate fns in {time.time()-t0:.0f}s')
