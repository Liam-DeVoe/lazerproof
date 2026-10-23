#!/usr/bin/env python3
"""D72 D30 regressions against the oracle: the explicit-schedule fuzz (117 cases incl. 17 `stop`), the 8 failgate
cases (oracle run, frame-stable gate) and repro0; new osu_eval (patched) vs the cached `oracle run` results."""
import json, os, subprocess, sys
ROOT = '/home/exedev/lazerproof'
sys.path.insert(0, os.path.join(ROOT, 'difftest'))
import eval_diff  # noqa
S = '/tmp/claude-1000/-home-exedev/5a067c7e-69f6-4190-93e6-f7fa504e1337/scratchpad/d72'
NEW = sys.argv[1] if len(sys.argv) > 1 else S + '/bin/osu_eval'
F = ROOT + '/data/wip/fidrun'

def modargs(parts):
    if len(parts) > 2:
        return ['--replace-mods', '--mods', parts[2][2:]] if parts[2].startswith('R:') else ['--mods', parts[2]]
    return []

def model(bm, rp, sched, mods):
    p = subprocess.run([ROOT + '/tools/heavy', NEW, bm, rp, '--schedule', sched] + mods, capture_output=True, timeout=3600)
    return json.loads(p.stdout.decode().strip().splitlines()[-1])

def load(fn):
    try:
        return json.loads(open(fn).read().strip().splitlines()[-1])
    except Exception as e:
        return {'error': 'unreadable %s' % e}

def cmp(o, m):
    oerr, merr = 'error' in o, ('error' in m or 'rejected' in m)
    if oerr or merr:
        return ('both_reject' if oerr and merr else ('oracle_error_only' if oerr else 'model_reject_only')), \
            [str(o.get('error'))[:100], str(m.get('rejected') or m.get('error'))[:100]]
    diffs, nj = eval_diff.compare(o, m)
    return ('match' if not diffs else 'mismatch'), diffs[:4]

res = []
last = {}  # a fuzz work dir is reused by later jobs of the same id/variant: its files belong to the LAST record
for l in open(F + '/fuzz/results.jsonl'):
    r = json.loads(l)
    last[os.path.join(F, 'fuzz', '%s_%s' % (r['id'], r['variant']))] = r
for w, r in last.items():
    parts = r['job'].split(None, 2)
    st, d = cmp(load(w + '/run.json'), model(parts[0], parts[1], 'explicit:' + w + '/refs.txt', modargs(parts)))
    res.append({'case': 'fuzz:%s_%s' % (r['id'], r['variant']), 'old': r['status'], 'new': st, 'd': d})
for rec in json.load(open(F + '/failgate/summary.json')):
    w = os.path.join(F, 'failgate', rec['id'])
    parts = rec['job'].split(None, 2)
    st, d = cmp(load(w + '/run.json'), model(parts[0], parts[1], 'explicit:' + w + '/steps.txt', modargs(parts)))
    res.append({'case': 'failgate:' + rec['id'], 'old': rec.get('run_vs_model'), 'new': st, 'd': d})
bm, rp = ROOT + '/data/beatmaps/505083.osu', ROOT + '/data/replays_v2/7742845812.osr'
st, d = cmp(load(F + '/repro0/run.json'), model(bm, rp, 'explicit:' + F + '/repro0/refs.txt', []))
res.append({'case': 'repro0', 'old': 'mismatch', 'new': st, 'd': d})
for f in ('empty', 'dec'):
    m = model(bm, rp, 'explicit:' + F + '/repro0/%s.txt' % f, [])
    res.append({'case': 'repro0:' + f, 'old': 'model accepted', 'new': 'model_reject: ' + str(m.get('rejected')), 'd': []})
json.dump(res, open(S + '/regress.json', 'w'), indent=1)
from collections import Counter
print(Counter((r['old'] if isinstance(r['old'], str) else 'match', r['new']) for r in res))
for r in res:
    if r['new'] != 'match': print(r)
