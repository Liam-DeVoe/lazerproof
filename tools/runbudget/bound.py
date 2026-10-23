#!/usr/bin/env python3
"""Phase 1 of the RunBudgetS corpus check: cheap upper bound U <= steps * objects per (map, replay, schedule),
from `rbcheck bound` output (exact spec step counts, objects, unj, n). Evaluated with the replay's own mods (n) and
with Wiggle added (n + 2^31 + 2^25; WG changes neither the playable nor the schedule). Prints a summary and writes
the triples the bound cannot clear to OUT (TSV: beatmap, replay, schedule, variant).
  bound.py OUT FILE.out..."""
import json, sys
WG = 2**31 + 2**25
def ok(U, n, objs, unj):
    return (2*U + unj + 1)*(n + n + 4) + objs*(4*n + 8) + 1 < 2**64 - 1 and (U + 1)*2000000 <= 2**54
out = open(sys.argv[1], 'w')
recs = errs = 0
stats = {}
for f in sys.argv[2:]:
    for l in open(f):
        d = json.loads(l); recs += 1
        if 'error' in d: errs += 1; continue
        o, u, n = d['objects'], d['unj'], d['n']
        for sch, s in d['steps'].items():
            if not isinstance(s, int): continue
            Ub = s * o
            for var, nn in (('own', n), ('wg', n if d['wg'] else n + WG)):
                k = (sch, var)
                st = stats.setdefault(k, {'triples': 0, 'cleared': 0, 'maxUb': 0, 'maxsteps': 0})
                st['triples'] += 1; st['maxUb'] = max(st['maxUb'], Ub); st['maxsteps'] = max(st['maxsteps'], s)
                if ok(Ub, nn, o, u): st['cleared'] += 1
                else: out.write(f"{d['beatmap']}\t{d['replay']}\t{sch}\t{var}\t{Ub}\n")
print(f"records {recs}, input errors {errs}")
for k, st in sorted(stats.items()):
    print(k, st, 'residue', st['triples'] - st['cleared'])
