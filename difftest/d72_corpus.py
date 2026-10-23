#!/usr/bin/env python3
"""D72 corpus identity check: new osu_eval (patched) vs base osu_eval (main HEAD before the patch), byte-identical
stdout. base = model = oracle on these corpora (fidelity runs 2026-10-23), so identity => unchanged agreement.
usage: corpus.py OUT.jsonl  (jobs from the lists below; resumable)"""
import json, os, subprocess, sys, hashlib, concurrent.futures as cf
S = '/tmp/claude-1000/-home-exedev/5a067c7e-69f6-4190-93e6-f7fa504e1337/scratchpad/d72'
D = '/home/exedev/lazerproof/data/wip'
NEW, BASE = S + '/bin/osu_eval', S + '/bin/osu_eval_base'
out_fn = sys.argv[1]
jobs = []
for d in ['pilot', 'pilot30', 'pilot_x10', 'pilot_da', 'pilot_sd', 'failpath']:
    sf = os.path.join(D, 'fidrun', d, 'summary.json')
    if not os.path.exists(sf): continue
    for rec in json.load(open(sf)):
        st = os.path.join(D, 'fidrun', d, rec.get('id', ''), 'steps.txt')
        if 'job' not in rec or not os.path.exists(st): continue
        parts = rec['job'].split(None, 2)
        mods = []
        if len(parts) > 2:
            mods = ['--replace-mods', '--mods', parts[2][2:]] if parts[2].startswith('R:') else ['--mods', parts[2]]
        jobs.append(('pilot:' + d + ':' + rec['id'], parts[0], parts[1], mods, 'explicit:' + st))
# v2 catchup after the pilots (few jobs, explicit real-Player schedules: run them first)
for l in open(D + '/fidrun/all_v2.txt'):
    if l.strip(): jobs.append(('v2cu', l.split()[0], l.split()[1], [], 'catchup'))
done = set()
if os.path.exists(out_fn):
    for l in open(out_fn):
        try: done.add(json.loads(l)['key'])
        except Exception: pass

def run(j):
    tag, bm, rp, mods, sched = j
    key = tag + ' ' + rp + ' ' + sched
    if key in done: return None
    res = {}
    for name, b in (('new', NEW), ('base', BASE)):
        p = subprocess.run(['nice', '-n', '15', '/home/exedev/lazerproof/tools/heavy', b, bm, rp, '--schedule', sched] + mods, capture_output=True, timeout=1800)
        res[name] = (p.returncode, hashlib.sha256(p.stdout).hexdigest(), p.stdout[:120].decode('utf-8', 'replace'))
    same = res['new'][:2] == res['base'][:2]
    return {'key': key, 'same': same, 'rc': res['new'][0], 'head': res['new'][2] if not same else ''}

with open(out_fn, 'a') as f, cf.ThreadPoolExecutor(int(os.environ.get('PAR', '2'))) as ex:
    for r in ex.map(run, jobs):
        if r is None: continue
        f.write(json.dumps(r) + '\n'); f.flush()
print('jobs', len(jobs))
