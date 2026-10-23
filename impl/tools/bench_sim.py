#!/usr/bin/env python3
"""Throughput of simtest_rs (batch mode, one process) vs Lean simtest (one process per job) on a pairs list.
usage: python3 -I impl/tools/bench_sim.py PAIRS.txt WORKDIR [schedule] [mods] [n_lean]"""
import os, subprocess, sys, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "difftest"))
import osr  # noqa
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
pairs, work = sys.argv[1], sys.argv[2]
sched = sys.argv[3] if len(sys.argv) > 3 else "catchup"
mods = sys.argv[4] if len(sys.argv) > 4 else "CL"
nlean = int(sys.argv[5]) if len(sys.argv) > 5 else 30
os.makedirs(work, exist_ok=True)
env = os.path.join(ROOT, "difftest", "env-1024x768.json")
rust = os.environ.get("RUST_SIMTEST", os.path.join(ROOT, "impl", "target", "release", "simtest_rs"))
lean = os.environ.get("LEAN_SIMTEST", os.path.join(ROOT, "model", ".lake", "build", "bin", "simtest"))
jobs = []
for k, line in enumerate(open(pairs)):
    pl, rp = line.split()[:2]
    fr = os.path.join(work, f"{k}.frames.txt")
    open(fr, "w").write(osr.read(rp)["frames"])
    jobs.append((pl, fr, os.path.join(work, f"{k}.out.json")))
lst = os.path.join(work, "batch.txt")
open(lst, "w").write("".join(f"{a} {b} {c} {sched} {mods or '-'}\n" for a, b, c in jobs))
t0 = time.time()
subprocess.run([rust, "--env", env, "--batch", lst])
tr = time.time() - t0
t0 = time.time()
for pl, fr, _ in jobs[:nlean]:
    subprocess.run([lean, "--playable", pl, "--frames", fr, "--env", env, "--schedule", sched, "--mods", mods],
                   stdout=subprocess.DEVNULL)
tl = time.time() - t0
n = min(nlean, len(jobs))
print(f'{{"schedule":"{sched}","mods":"{mods}","rust_jobs":{len(jobs)},"rust_s":{tr:.2f},"rust_per_s":{len(jobs)/tr:.1f},'
      f'"lean_jobs":{n},"lean_s":{tl:.2f},"lean_per_s":{n/tl:.2f}}}')
