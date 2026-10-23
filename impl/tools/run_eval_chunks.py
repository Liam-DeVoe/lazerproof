#!/usr/bin/env python3
"""Resumable, chunked driver for difftest/rust_eval_diff.py (Lean evaltest vs Rust osu_eval): every chunk
(<= "chunk" jobs) is ONE short `tools/heavy` call (STATE.md CHUNK rule). A chunk whose out file ends with the
summary JSON line is skipped on re-runs.
usage: run_eval_chunks.py PLAN.json   PLAN = {"out": DIR, "json_out": F, "env": {...}, "items": [
   {"label": L, "list": FILE, "chunk": 40, "args": [...rust_eval_diff args...]}]}"""
import json, os, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
plan = json.load(open(sys.argv[1]))
out = plan["out"]
os.makedirs(out, exist_ok=True)
env = dict(os.environ, **plan.get("env", {}))


def done(fn):
    try:
        last = open(fn).read().strip().splitlines()[-1]
        return json.loads(last).get("runs") is not None
    except Exception:
        return False


for item in plan["items"]:
    ls = [l.rstrip("\n") for l in open(item["list"]) if l.strip() and not l.lstrip().startswith("#")]
    n = item.get("chunk", 40)
    for k in range(0, len(ls), n):
        tag = f"{item['label'].replace(':', '_')}_{k // n}"
        ofn = os.path.join(out, tag + ".txt")
        if done(ofn):
            continue
        jf = os.path.join(out, tag + ".jobs")
        open(jf, "w").write("\n".join(ls[k:k + n]) + "\n")
        cmd = [os.path.join(ROOT, "tools", "heavy"), "python3", "-I", os.path.join(ROOT, "difftest", "rust_eval_diff.py"),
               "--list", jf, "--json-out", plan["json_out"], "--label", f"{item['label']}#{k // n}",
               "--work", os.path.join(out, "w_" + tag)] + list(item.get("args", []))
        with open(ofn, "w") as f:
            subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, env=env, cwd=ROOT)
        print(tag, open(ofn).read().strip().splitlines()[-1][:200], flush=True)
