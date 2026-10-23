#!/usr/bin/env python3
"""End-to-end throughput: Rust osu_eval (per process and --batch) vs Lean evaltest vs the oracle (lazer, uncached).
usage: bench_eval.py JOBS [--schedule S] [--oracle-n N] [--out F]
JOBS lines "BEATMAP OSR". Each measured step is ONE tools/heavy call (CHUNK rule). Prints JSON: wall seconds,
child user CPU seconds and replays/s per evaluator (all on the same jobs; the oracle on the first N)."""
import argparse, json, os, resource, subprocess, sys, tempfile, time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
HEAVY = os.path.join(ROOT, "tools", "heavy")
LEAN = os.environ.get("LEAN_EVALTEST") or os.path.join(ROOT, "data/wip/rust-eval/evaltest_lean_1b0a176")
RUST = os.environ.get("RUST_EVAL") or os.path.join(ROOT, "impl/target/release/osu_eval")


def timed(cmd, env=None):
    """run cmd, return (wall, child user CPU) measured around the command itself"""
    r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    t = time.time()
    subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=env)
    w = time.time() - t
    r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    return w, r1.ru_utime - r0.ru_utime


def measure(cmd, heavy=True, env=None):
    """time `cmd` inside its own tools/heavy call (queue waiting excluded)"""
    if not heavy:
        return timed(cmd, env)
    p = subprocess.run([HEAVY, sys.executable, "-I", os.path.abspath(__file__), "--time"] + cmd,
                       stdout=subprocess.PIPE, env=env, text=True)
    w, u = json.loads(p.stdout.strip().splitlines()[-1])
    return w, u


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--time":
        print(json.dumps(timed(sys.argv[2:], dict(os.environ))))
        return
    ap = argparse.ArgumentParser()
    ap.add_argument("jobs")
    ap.add_argument("--schedule", default="catchup")
    ap.add_argument("--oracle-n", type=int, default=30)
    ap.add_argument("--out")
    a = ap.parse_args()
    jobs = [l.split()[:2] for l in open(a.jobs) if l.strip()]
    tmp = tempfile.mkdtemp(prefix="bench_eval_")
    sch = [] if a.schedule == "catchup" else ["--schedule", a.schedule]
    res = {"jobs": len(jobs), "schedule": a.schedule}
    # Lean evaltest, one process per job (as evaltest is used); the loop runs inside one heavy call
    script = os.path.join(tmp, "lean.sh")
    open(script, "w").write("#!/bin/sh\n" + "".join(f"{LEAN} {b} {r} {' '.join(sch)} > /dev/null\n" for b, r in jobs))
    os.chmod(script, 0o755)
    w, u = measure([script])
    res["lean_evaltest"] = {"wall_s": round(w, 2), "user_s": round(u, 2), "replays_per_s": round(len(jobs) / w, 3)}
    script = os.path.join(tmp, "rust.sh")
    open(script, "w").write("#!/bin/sh\n" + "".join(f"{RUST} {b} {r} {' '.join(sch)} > /dev/null\n" for b, r in jobs))
    os.chmod(script, 0o755)
    w, u = measure([script])
    res["rust_osu_eval_per_process"] = {"wall_s": round(w, 2), "user_s": round(u, 2), "replays_per_s": round(len(jobs) / w, 3)}
    bl = os.path.join(tmp, "batch.txt")
    open(bl, "w").write("".join(f"{b} {r} {os.path.join(tmp, 'o.json')}\n" for b, r in jobs))
    w, u = measure([RUST, "--batch", bl] + sch)
    res["rust_osu_eval_batch"] = {"wall_s": round(w, 2), "user_s": round(u, 2), "replays_per_s": round(len(jobs) / w, 3)}
    if a.oracle_n > 0:
        ol = os.path.join(tmp, "oracle.txt")
        sub = jobs[:a.oracle_n]
        open(ol, "w").write("".join(f"{b} {r}\n" for b, r in sub))
        env = dict(os.environ, ORACLE_NOCACHE="1", DOTNET_GCHeapHardLimit="0x30000000")
        # oracle.sh takes its own tools/heavy slot (nested heavy calls pass through)
        w, u = measure([os.path.join(ROOT, "oracle", "oracle.sh"), "batch", "--list", ol, "--no-judgements"] + sch, env=env)
        res["oracle_batch"] = {"jobs": len(sub), "wall_s": round(w, 2), "user_s": round(u, 2), "replays_per_s": round(len(sub) / w, 3)}
    res["load_avg"] = os.getloadavg()
    print(json.dumps(res))
    if a.out:
        with open(a.out, "a") as f:
            f.write(json.dumps(res) + "\n")


if __name__ == "__main__":
    main()
