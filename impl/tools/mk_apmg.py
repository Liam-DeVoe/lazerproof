#!/usr/bin/env python3
"""AP + (MG|RP) (+0-2 rate/fail mods, random settings) job-mod pairs from a pairs file: mk_apmg.py PAIRS OUT SEED (171dd71 corpus)."""
import json, random, sys
sys.path.insert(0, "/home/exedev/lazerproof/difftest")
import modgen_sim as M
rng = random.Random(int(sys.argv[3]))
out = open(sys.argv[2], "w")
for line in open(sys.argv[1]):
    a = line.split()
    if len(a) < 2: continue
    for k in range(2):
        names = ["AP", rng.choice(["MG", "RP"])] + rng.sample(["CL", "NF", "DT", "HT", "HR", "WD", "AS"], rng.randint(0, 2))
        rng.shuffle(names)
        mods = []
        for n in names:
            s = M.SETTINGS[n](rng); m = {"acronym": n}
            if s: m["settings"] = s
            mods.append(m)
        out.write(f"{a[0]} {a[1]} {json.dumps(mods, separators=(',', ':'))}\n")
