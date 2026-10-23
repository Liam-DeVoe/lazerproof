#!/usr/bin/env python3
"""Sensitivity check for a finished sim_diff run: re-run the model with one mod removed (or its settings dropped)
from every job that has it and count jobs whose result then differs from the oracle. A mod whose removal never
changes anything was not exercised by that corpus.

Usage: python3 -I difftest/sim_mutate.py WORKDIR ACRONYM [ACRONYM ...] [--schedule S]
"""
import json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sim_diff, osr  # noqa: E402

args = [a for a in sys.argv[1:] if not a.startswith("--")]
sched = "catchup"
if "--schedule" in sys.argv:
    sched = sys.argv[sys.argv.index("--schedule") + 1]
work, acrs = args[0], args[1:]
jobs = [l.split(None, 2) for l in open(os.path.join(work, "jobs_with_mods.txt"))]
ores = [json.loads(l) for l in open(os.path.join(work, "oracle.jsonl"))]
fp = os.path.join(work, "mut.frames.txt")
for acr in acrs:
    n = changed = 0
    for i, (bm, rp, jm) in enumerate(jobs):
        jm = json.loads(jm)
        if not any(m["acronym"] == acr for m in jm) or "error" in ores[i]:
            continue
        n += 1
        r = osr.read(rp)
        open(fp, "w").write(r["frames"])
        mut = [m for m in jm if m["acronym"] != acr]
        m = sim_diff.run_model(os.path.join(work, "playable", f"{i}.json"), fp, sched, [], sim_diff.SIMTEST, mut,
                               r["version"] >= 30000000)
        ok, _, _ = sim_diff.compare(ores[i], m, False)   # judgements only (the multiplier would always differ)
        changed += 0 if ok else 1
    print(json.dumps({"mod": acr, "jobs_with_mod": n, "changed_when_removed": changed}))
os.remove(fp) if os.path.exists(fp) else None
