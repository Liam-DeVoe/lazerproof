#!/usr/bin/env python3
"""Differential test: Rust Sim port (impl/target/release/simtest_rs) vs the Lean simtest (model/.lake/build/bin/simtest).

No oracle needed: both take the same (playable dump, decompressed frame text, env, schedule, mods) and must print
byte-identical JSON.

Inputs: one or more corpus specs `--corpus PLAYABLE_DIR:JOBS_FILE` where JOBS_FILE lines are
"beatmap.osu replay.osr [mods-json]" (as oracle_jobs.txt / jobs_with_mods.txt of sim_diff.py work dirs) and
PLAYABLE_DIR/<line index>.json is the playable dump of that line; or `--pairs FILE` with "playable.json replay.osr" lines.

Usage:
  python3 -I difftest/rust_sim_diff.py --corpus DIR/playable:DIR/oracle_jobs.txt [...] [--pairs F] \
      --schedules catchup,perframe,dense1ms --modsets ",CL,NF+CL,NF,CLnolock" [--work W] [--json-out F]
Mod sets: "" (no mods), "CL", "NF+CL", "NF", "CLnolock" (CL with classic_note_lock=false), "CLnohealth".
"""
import argparse, json, os, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import osr  # noqa: E402
import modgen_sim  # noqa: E402
import random  # noqa: E402

LEAN = os.environ.get("LEAN_SIMTEST", os.path.join(ROOT, "model", ".lake", "build", "bin", "simtest"))
RUST = os.environ.get("RUST_SIMTEST", os.path.join(ROOT, "impl", "target", "release", "simtest_rs"))
ENV = os.path.join(HERE, "env-1024x768.json")

MODSETS = {
    "": ["--mods", ""],
    "CL": ["--mods", "CL"],
    "NF+CL": ["--mods", "NF,CL"],
    "NF": ["--mods", "NF"],
    "CLnolock": ["--mods-json", '[{"acronym":"CL","settings":{"classic_note_lock":false}}]'],
    "CLnohealth": ["--mods-json", '[{"acronym":"CL","settings":{"classic_health":false}}]'],
}


def load_pairs(args):
    pairs = []
    for spec in args.corpus or []:
        pdir, jobs = spec.split(":", 1)
        idx = 0
        for line in open(jobs):
            line = line.split("#")[0].strip()
            if not line:
                continue
            a = line.split(None, 2)
            pl = os.path.join(pdir, f"{idx}.json")
            idx += 1
            if os.path.exists(pl) and os.path.exists(a[1]):
                pairs.append((pl, a[1], a[2] if len(a) > 2 else None))
    for fn in args.pairs or []:
        for line in open(fn):
            a = line.strip().split(None, 2)
            if len(a) >= 2:
                pairs.append((a[0], a[1], a[2] if len(a) > 2 else None))
    return pairs


def run(exe, pl, fr, sched, mods):
    t0 = time.time()
    p = subprocess.run([exe, "--playable", pl, "--frames", fr, "--env", ENV, "--schedule", sched] + mods,
                       capture_output=True)
    return p.returncode, p.stdout, p.stderr, time.time() - t0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", action="append")
    ap.add_argument("--pairs", action="append")
    ap.add_argument("--schedules", default="catchup,perframe,dense1ms")
    ap.add_argument("--modsets", default=",CL,NF+CL")
    ap.add_argument("--work", default=None)
    ap.add_argument("--json-out", default=None)
    ap.add_argument("--label", default="")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--gen-mods", default=None, choices=sorted(modgen_sim.POOLS),
                    help="add N random APIMod lists per (pair, schedule) from this pool (random subset/order/settings)")
    ap.add_argument("--mods-per-run", type=int, default=2)
    ap.add_argument("--job-mods", action="store_true", help="also run each corpus line's own mods JSON (3rd column)")
    ap.add_argument("--mods-seed", type=int, default=1)
    args = ap.parse_args()
    pairs = load_pairs(args)
    if args.limit:
        pairs = pairs[:args.limit]
    work = args.work or os.path.join("/tmp", "rsdiff-%d" % os.getpid())
    os.makedirs(work, exist_ok=True)
    scheds = [s for s in args.schedules.split(",") if s]
    modsets = [m for m in args.modsets.split(",")] if args.modsets != "none" else []
    mrng = random.Random(args.mods_seed)
    ok = bad = err = panics = 0
    tl = tr = 0.0
    nj = 0
    lines = []
    for k, (pl, rp, jobmods) in enumerate(pairs):
        r = osr.read(rp)
        fr = os.path.join(work, "frames.txt")
        with open(fr, "w") as f:
            f.write(r["frames"])
        for sched in scheds:
            variants = [(ms, MODSETS[ms]) for ms in modsets]
            if args.job_mods and jobmods:
                variants.append((jobmods, ["--mods-json", jobmods]))
            if args.gen_mods:
                for _ in range(args.mods_per_run):
                    jm = json.dumps(modgen_sim.gen(mrng, args.gen_mods), separators=(",", ":"))
                    variants.append((jm, ["--mods-json", jm]))
            for ms, margs in variants:
                mods = margs + (["--lazer-replay"] if r["version"] >= 30000000 else [])
                cl, ol, el, dl = run(LEAN, pl, fr, sched, mods)
                cr, orr, er, dr = run(RUST, pl, fr, sched, mods)
                tl += dl
                tr += dr
                if b"PANIC" in el:
                    panics += 1
                    lines.append(f"LEAN-PANIC {pl} {rp} {sched} {ms!r}: {el.decode(errors='replace')[:300]!r}")
                if cl != 0 and cl == cr and ol == orr:
                    err += 1   # both rejected identically (e.g. frame decode error)
                    lines.append(f"both-error {pl} {sched} {ms!r}: {ol[:120]!r}")
                elif cl == cr and ol == orr:
                    ok += 1
                    try:
                        nj += json.loads(ol)["judgement_count"]
                    except Exception:
                        pass
                else:
                    bad += 1
                    a, b = ol.decode(errors="replace"), orr.decode(errors="replace")
                    i = next((i for i in range(min(len(a), len(b))) if a[i] != b[i]), min(len(a), len(b)))
                    lines.append(f"MISMATCH {pl} {rp} {sched} {ms!r}: rc lean={cl} rust={cr} at {i}: "
                                 f"lean=...{a[max(0, i - 150):i + 150]!r} rust=...{b[max(0, i - 150):i + 150]!r} "
                                 f"stderr lean={el[-200:]!r} rust={er[-200:]!r}")
        if (k + 1) % 20 == 0:
            print(f"[{k + 1}/{len(pairs)}] ok={ok} bad={bad} err={err}", file=sys.stderr, flush=True)
    for l in lines:
        print(l)
    summary = {"label": args.label, "pairs": len(pairs), "schedules": scheds, "modsets": modsets, "runs": ok + bad + err,
               "identical": ok, "mismatch": bad, "both_error": err, "lean_panics": panics, "judgements": nj,
               "lean_s": round(tl, 1), "rust_s": round(tr, 1)}
    print(json.dumps(summary))
    if args.json_out:
        with open(args.json_out, "a") as f:
            f.write(json.dumps(summary) + "\n")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
