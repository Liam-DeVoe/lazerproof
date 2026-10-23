#!/usr/bin/env python3
"""List real (crawled) replay jobs: "beatmap.osu replay.osr" for every replay whose beatmap is present.
Usage: python3 -I difftest/real_jobs.py [--limit N] [--offset K] > jobs.txt"""
import argparse, os, sqlite3
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ap = argparse.ArgumentParser()
ap.add_argument("--limit", type=int, default=0)
ap.add_argument("--offset", type=int, default=0)
a = ap.parse_args()
db = sqlite3.connect(os.path.join(ROOT, "data", "index.sqlite"))
rows = []
for f in sorted(os.listdir(os.path.join(ROOT, "data", "replays"))):
    if not f.endswith(".osr"):
        continue
    sid = int(f.split(".")[0])
    r = db.execute("select beatmap_id from scores where score_id=?", (sid,)).fetchone()
    if not r:
        continue
    bm = os.path.join(ROOT, "data", "beatmaps", f"{r[0]}.osu")
    if os.path.exists(bm):
        rows.append(f"{bm} {os.path.join(ROOT, 'data', 'replays', f)}")
rows = rows[a.offset:]
if a.limit:
    rows = rows[:a.limit]
print("\n".join(rows))
