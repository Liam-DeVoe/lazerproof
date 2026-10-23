#!/usr/bin/env python3
"""M8: confirm that visual-only mods are judgement-irrelevant, by differential test on the oracle (lazer itself):
each job runs with a base mod list and with the base list plus one visual mod (random settings, random position in
the list); the judgement lists (object, nested, type, result, RawTime, combo, health, failed), statistics, max combo,
accuracy and fail state must be identical. Score and rank may differ (multiplier, AdjustRank).

Usage: python3 -I difftest/visual_diff.py --list JOBS.txt --seed S [--schedule catchup] [--work DIR]
"""
import argparse, json, os, random, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import modgen_sim  # noqa: E402

ORACLE = os.path.join(os.path.dirname(HERE), "oracle", "oracle.sh")
VISUAL = ["TC", "FL", "BL", "BU", "AD", "NS", "BM", "MU", "SY", "SV2", "TD"]
EXTRA_SETTINGS = {
    "NS": lambda r: {"hidden_combo_count": r.randint(0, 50)},
    "BM": lambda r: {"max_size_combo_count": r.randint(5, 100), "max_cursor_size": r.choice([5, 7.5, 10, 15])},
    "MU": lambda r: {"inverse_muting": r.random() < 0.5, "enable_metronome": r.random() < 0.5,
                     "mute_combo_count": r.randint(0, 500), "affects_hit_sounds": r.random() < 0.5},
    "FL": modgen_sim.SETTINGS["FL"], "AD": modgen_sim.SETTINGS["AD"],
}
BASE_POOL = ["CL", "NF", "HR", "DT", "HD", "SD", "EZ", "AC"]


def run(jobs, schedule, out):
    lst = out + ".list"
    with open(lst, "w") as f:
        for bm, rp, m in jobs:
            f.write(f"{bm} {rp} {json.dumps(m, separators=(',', ':'))}\n")
    with open(out, "w") as fo, open(out + ".err", "w") as fe:
        subprocess.run([ORACLE, "batch", "--list", lst, "--schedule", schedule, "--replace-mods"], stdout=fo, stderr=fe)
    return [json.loads(l) for l in open(out)]


def key(o):
    lv = o["live"]
    js = [(j["i"], j["n"], j["type"], j["result"], j["time"], j["combo"], j["health"], j.get("failed", False))
          for j in lv["judgements"]]
    return (js, lv["statistics"], lv["max_combo"], lv["accuracy"], lv["failed"], lv["fail_time"])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", required=True)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--schedule", default="catchup")
    ap.add_argument("--work", default="visual_diff")
    a = ap.parse_args()
    rng = random.Random(a.seed)
    os.makedirs(a.work, exist_ok=True)
    base, vis = [], []
    for line in open(a.list):
        line = line.split("#")[0].strip()
        if not line:
            continue
        bm, rp = line.split()[:2]
        b = [{"acronym": x} for x in rng.sample(BASE_POOL, rng.randint(0, 3))]
        v = rng.choice(VISUAL)
        vm = {"acronym": v}
        s = EXTRA_SETTINGS.get(v, lambda r: {})(rng)
        if s:
            vm["settings"] = s
        w = list(b)
        w.insert(rng.randint(0, len(w)), vm)
        base.append((bm, rp, b))
        vis.append((bm, rp, w))
    ob = run(base, a.schedule, os.path.join(a.work, "base.jsonl"))
    ov = run(vis, a.schedule, os.path.join(a.work, "vis.jsonl"))
    same = diff = err = 0
    per = {}
    for (bm, rp, m), x, y in zip(vis, ob, ov):
        v = [z["acronym"] for z in m if z["acronym"] in VISUAL][0]
        if "error" in x or "error" in y:
            err += 1
            continue
        ok = key(x) == key(y)
        per.setdefault(v, [0, 0])[0 if ok else 1] += 1
        if ok:
            same += 1
        else:
            diff += 1
            print(f"DIFF {rp} mods={json.dumps(m)}")
    print(json.dumps({"jobs": len(vis), "identical": same, "different": diff, "errors": err, "per_mod": per,
                      "schedule": a.schedule, "list": a.list}))


if __name__ == "__main__":
    main()
