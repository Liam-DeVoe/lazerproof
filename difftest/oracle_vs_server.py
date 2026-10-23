#!/usr/bin/env python3
"""Compare oracle JSONL output against server-side score stats in data/index.sqlite (sanity check only, see D7).

Usage: python3 -I difftest/oracle_vs_server.py ORACLE.jsonl [--db data/index.sqlite] [-v]
Score id is taken from the replay file name (<score_id>.osr). Uses live-semantics results.
"""
import argparse, json, os, sqlite3, sys

ap = argparse.ArgumentParser()
ap.add_argument("jsonl")
ap.add_argument("--db", default=os.path.join(os.path.dirname(__file__), "..", "data", "index.sqlite"))
ap.add_argument("-v", action="store_true")
a = ap.parse_args()
db = sqlite3.connect(a.db)
keys = ["300", "100", "50", "miss", "maxcombo"]
agree = {k: 0 for k in keys}
allok = n = errors = 0
for line in open(a.jsonl):
    d = json.loads(line)
    if "error" in d:
        errors += 1
        continue
    sid = int(os.path.basename(d["input"]["replay"]).split(".")[0])
    row = db.execute("select count300,count100,count50,countmiss,maxcombo from scores where score_id=?", (sid,)).fetchone()
    if not row:
        continue
    lc = d["live"]["legacy_counts"]
    mine = [lc["300"], lc["100"], lc["50"], lc["miss"], d["live"]["max_combo"]]
    n += 1
    ok = True
    for k, x, y in zip(keys, mine, row):
        if x == y:
            agree[k] += 1
        else:
            ok = False
    allok += ok
    if a.v or not ok:
        print(("OK  " if ok else "DIFF"), sid, "oracle", mine, "server", list(row), "mods", [m["acronym"] for m in d["input"]["mods"]])
print(f"n={n} errors={errors} all-equal={allok}/{n}")
for k in keys:
    print(f"  {k:9s} {agree[k]}/{n} ({100.0 * agree[k] / max(n, 1):.1f}%)")
