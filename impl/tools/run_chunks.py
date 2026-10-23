#!/usr/bin/env python3
"""Resumable, chunked driver for difftest/rust_sim_diff.py: every chunk (<= --chunk pairs) is ONE short
`tools/heavy` call (never wrap the whole plan in one heavy call; STATE.md rule). A chunk whose out file ends with
the summary JSON line is skipped on re-runs.
usage: run_chunks.py PLAN.json   PLAN = {"out": DIR, "json_out": F, "env": {...}, "items": [
   {"label": L, "pairs": FILE | "corpus": "PLDIR:JOBS", "chunk": 15, "args": [...rust_sim_diff args...]}]}"""
import json, os, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
plan = json.load(open(sys.argv[1]))
out = plan["out"]
os.makedirs(out, exist_ok=True)
env = dict(os.environ, **plan.get("env", {}))


def lines_of(item):
    if "pairs" in item:
        return [l.rstrip("\n") for l in open(item["pairs"]) if l.strip()]
    pdir, jobs = item["corpus"].split(":", 1)
    res, idx = [], 0
    for line in open(jobs):
        line = line.split("#")[0].strip()
        if not line:
            continue
        a = line.split(None, 2)
        pl = os.path.join(pdir, f"{idx}.json")
        idx += 1
        if os.path.exists(pl):
            res.append(" ".join([pl, a[1]] + ([a[2]] if len(a) > 2 else [])))
    return res


def done(fn):
    try:
        last = open(fn).read().strip().splitlines()[-1]
        return json.loads(last).get("runs") is not None
    except Exception:
        return False


for item in plan["items"]:
    ls = lines_of(item)
    n = item.get("chunk", 15)
    for k in range(0, len(ls), n):
        tag = f"{item['label'].replace(':', '_')}_{k // n}"
        ofn = os.path.join(out, tag + ".txt")
        if done(ofn):
            continue
        pf = os.path.join(out, tag + ".pairs")
        open(pf, "w").write("\n".join(ls[k:k + n]) + "\n")
        args = list(item["args"])
        if "--mods-seed" in args:   # a different random mod sequence per chunk
            q = args.index("--mods-seed") + 1
            args[q] = str(int(args[q]) * 1000 + k // n)
        cmd = [os.path.join(ROOT, "tools", "heavy"), "python3", "-I", os.path.join(ROOT, "difftest", "rust_sim_diff.py"),
               "--pairs", pf, "--json-out", plan["json_out"], "--label", f"{item['label']}#{k // n}",
               "--work", os.path.join(out, "w_" + tag)] + args
        with open(ofn, "w") as f:
            subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, env=env, cwd=ROOT)
        print(tag, open(ofn).read().strip().splitlines()[-1][:200], flush=True)
