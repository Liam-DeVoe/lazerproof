#!/usr/bin/env python3
"""Differential test: Lean simulation model (model/.lake/build/bin/simtest) vs the oracle (lazer).

For each job (beatmap, replay):
  1. oracle batch (--dump-playable DIR, --schedule S, forced mod list) -> judgements + playable dump
  2. decompress the .osr frame payload (trusted LZMA boundary) -> frames text
  3. simtest --playable --frames --env --schedule --mods
  4. compare judgement by judgement (object, nested index, type, result, RawTime bits, combo) + statistics/max combo.

Usage:
  python3 -I difftest/sim_diff.py --list JOBS.txt --milestone M0 --schedule catchup [--work DIR] [-v]
JOBS.txt lines: "beatmap.osu replay.osr" (comments with #).
Milestones fix the mod list given to both sides (all with NF so that live-fail freezing does not mask judgements):
  M0: NF (no Classic: StartTimeOrderedHitPolicy)        M1/M2: NF + CL (Classic, default settings)
"""
import argparse, json, os, shutil, struct, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import osr  # noqa: E402
import modgen_sim  # noqa: E402
import random  # noqa: E402

ORACLE = os.path.join(ROOT, "oracle", "oracle.sh")
SIMTEST = os.path.join(ROOT, "model", ".lake", "build", "bin", "simtest")
ENV = os.path.join(HERE, "env-1024x768.json")

MILESTONE_MODS = {
    "M0": ([{"acronym": "NF"}], ["NF"]),
    "M1": ([{"acronym": "NF"}, {"acronym": "CL"}], ["NF", "CL"]),
    "M2": ([{"acronym": "NF"}, {"acronym": "CL"}], ["NF", "CL"]),
    "M2nc": ([{"acronym": "NF"}], ["NF"]),
    # M4: full results incl. health/fail (no NF: failing is live), Classic (legacy health) and non-Classic.
    "M4": ([{"acronym": "CL"}], ["CL"]),
    "M4nc": ([], []),
    "M4nf": ([{"acronym": "NF"}, {"acronym": "CL"}], ["NF", "CL"]),
}
FULL = {"M4", "M4nc", "M4nf"}


def bits(x):
    if isinstance(x, str):
        x = float(x)
    return "0x" + struct.pack(">d", x).hex()


def run_oracle(jobs, schedule, mods_json, work):
    lst = os.path.join(work, "oracle_jobs.txt")
    with open(lst, "w") as f:
        for bm, rp, jm in jobs:
            m = mods_json if jm is None else jm
            f.write(f"{bm} {rp} {json.dumps(m, separators=(',', ':'))}\n")
    pl = os.path.join(work, "playable")
    out = os.path.join(work, "oracle.jsonl")
    with open(out, "w") as fo, open(os.path.join(work, "oracle.err"), "w") as fe:
        subprocess.run([ORACLE, "batch", "--list", lst, "--schedule", schedule, "--replace-mods",
                        "--dump-playable", pl], stdout=fo, stderr=fe)
    res = [json.loads(l) for l in open(out)]
    return res, pl


def run_model(playable, frames_path, schedule, mods, simtest=SIMTEST, mods_json=None, lazer_replay=False):
    ma = ["--mods", ",".join(mods)] if mods_json is None else ["--mods-json", json.dumps(mods_json)]
    if lazer_replay:
        ma.append("--lazer-replay")
    p = subprocess.run([simtest, "--playable", playable, "--frames", frames_path, "--env", ENV,
                        "--schedule", schedule] + ma, capture_output=True, text=True)
    if p.returncode != 0:
        return {"error": (p.stdout + p.stderr)[-2000:]}
    if "PANIC" in p.stderr:
        # a Lean panic returns `default` and continues: never acceptable, even if the results happen to match
        return {"error": "simtest PANIC: " + p.stderr[:1000]}
    return json.loads(p.stdout)


def jkey(j, model):
    t = j["time"] if model else bits(j["time"])
    return (j["i"], j["n"], j["type"], j["result"], t, j["combo"])


def jkey_full(j, model):
    k = jkey(j, model)
    h = j["health"] if model else bits(j["health"])
    f = bool(j.get("failed", False))
    return k + (h, f)


def compare_result(o, m, sem, mult=None):
    """Final results of one fail semantics (oracle block vs model block)."""
    diffs = []
    for k in ("failed", "fail_trigger_count", "rank", "total_score", "total_score_without_mods", "max_combo",
              "final_combo", "completed", "statistics", "maximum_statistics", "legacy_counts"):
        if o[k] != m[k]:
            diffs.append(f"{sem}.{k}: oracle={o[k]} model={m[k]}")
    for k in ("accuracy", "final_health"):
        if bits(o[k]) != m[k]:
            diffs.append(f"{sem}.{k}: oracle={o[k]} ({bits(o[k])}) model={m[k]}")
    if mult is not None and o["total_score"] != round(o["total_score_without_mods"] * mult):
        diffs.append(f"{sem}.multiplier: oracle total {o['total_score']} != round({o['total_score_without_mods']} * {mult!r})")
    of = None if o["fail_time"] is None else bits(o["fail_time"])
    if of != m["fail_time"]:
        diffs.append(f"{sem}.fail_time: oracle={o['fail_time']} model={m['fail_time']}")
    return diffs


def compare(o, m, full=False):
    """Returns (ok, n_judgements, first_mismatch_description)."""
    live = o["live"]
    key = jkey_full if full else jkey
    oj = [key(j, False) for j in live["judgements"]]
    mj = [key(j, True) for j in m["judgements"]]
    n = min(len(oj), len(mj))
    for k in range(n):
        if oj[k] != mj[k]:
            ctx = [("oracle", oj[max(0, k - 2):k + 3]), ("model", mj[max(0, k - 2):k + 3])]
            return False, len(oj), f"judgement {k}: oracle={oj[k]} model={mj[k]}; context={ctx}"
    if len(oj) != len(mj):
        nxt = oj[n] if len(oj) > n else mj[n]
        return False, len(oj), f"count oracle={len(oj)} model={len(mj)}; next={nxt}"
    if live["statistics"] != m["statistics"]:
        return False, len(oj), f"statistics oracle={live['statistics']} model={m['statistics']}"
    if live["max_combo"] != m["max_combo"]:
        return False, len(oj), f"max_combo oracle={live['max_combo']} model={m['max_combo']}"
    if full:
        mult = struct.unpack(">d", bytes.fromhex(m["score_multiplier"][2:]))[0] if "score_multiplier" in m else None
        d = compare_result(live, m["live"], "live", mult)
        rp = o.get("replay_player")
        if isinstance(rp, dict):
            d += compare_result(rp, m["replay_player"], "replay_player", mult)
            rj = [jkey_full(j, False) for j in rp["judgements"]]
            mr = [(j["i"], j["n"], j["type"], j["result"], j["time"], j["rp_combo"], j["rp_health"], bool(j["rp_failed"]))
                  for j in m["judgements"]] if m["judgements"] and "rp_combo" in m["judgements"][0] else None
            if mr is not None:
                for k in range(min(len(rj), len(mr))):
                    if rj[k] != mr[k]:
                        d.append(f"replay_player judgement {k}: oracle={rj[k]} model={mr[k]}")
                        break
                if len(rj) != len(mr):
                    d.append(f"replay_player judgement count oracle={len(rj)} model={len(mr)}")
            elif [x[:5] for x in rj] != [x[:5] for x in mj]:
                d.append("replay_player judgement list differs from live (unexpected)")
        elif rp != "same_as_live":
            d.append(f"replay_player: {rp}")
        if d:
            return False, len(oj), "; ".join(d)
    return True, len(oj), ""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", required=True)
    ap.add_argument("--milestone", default="M0", choices=sorted(MILESTONE_MODS))
    ap.add_argument("--schedule", default="catchup")
    ap.add_argument("--work", default=None)
    ap.add_argument("--json-out", default=None, help="append a summary line (JSON) to this file")
    ap.add_argument("--reuse-oracle", action="store_true", help="reuse WORK/oracle.jsonl + WORK/playable from a previous run")
    ap.add_argument("--keep", action="store_true", help="keep extracted frame files")
    ap.add_argument("--gen-mods", default=None, choices=sorted(modgen_sim.POOLS),
                    help="random mod list per job from this pool (random subset, order, settings); full compare")
    ap.add_argument("--mods-seed", type=int, default=1)
    ap.add_argument("-v", action="store_true")
    args = ap.parse_args()

    jobs = []
    mrng = random.Random(args.mods_seed)
    for line in open(args.list):
        line = line.split("#")[0].strip()
        if line:
            a = line.split(None, 2)
            jm = json.loads(a[2]) if len(a) > 2 else None
            if args.gen_mods:
                jm = modgen_sim.gen(mrng, args.gen_mods)
            jobs.append((a[0], a[1], jm))
    work = args.work or os.path.join("/tmp", "simdiff-%d" % os.getpid())
    os.makedirs(work, exist_ok=True)
    if args.gen_mods:
        with open(os.path.join(work, "jobs_with_mods.txt"), "w") as f:
            for bm, rp, jm in jobs:
                f.write(f"{bm} {rp} {json.dumps(jm, separators=(',', ':'))}\n")
    mods_json, mods = MILESTONE_MODS[args.milestone]

    # private copy of the model binary (rebuilding it during a long run must not affect the run)
    simtest = os.path.join(work, "simtest.bin")
    if os.path.exists(simtest):
        os.remove(simtest)
    try:
        os.link(SIMTEST, simtest)   # hard link: survives a rebuild (new inode), costs no space
    except OSError:
        shutil.copy2(SIMTEST, simtest)
    t0 = time.time()
    if args.reuse_oracle and os.path.exists(os.path.join(work, "oracle.jsonl")):
        ores = [json.loads(l) for l in open(os.path.join(work, "oracle.jsonl"))]
        pldir = os.path.join(work, "playable")
    else:
        ores, pldir = run_oracle(jobs, args.schedule, mods_json, work)
    t1 = time.time()
    ok = bad = err = 0
    nj = 0
    lines = []
    for idx, (bm, rp, jm) in enumerate(jobs):
        o = ores[idx] if idx < len(ores) else {"error": "missing oracle output"}
        if "error" in o:
            err += 1
            lines.append(f"ORACLE-ERROR {rp}: {o['error'][:200]}")
            continue
        r = osr.read(rp)
        fpath = os.path.join(work, f"{idx}.frames.txt")
        with open(fpath, "w") as f:
            f.write(r["frames"])
        m = run_model(os.path.join(pldir, f"{idx}.json"), fpath, args.schedule, mods, simtest, jm,
                      r["version"] >= 30000000)
        if "error" in m:
            err += 1
            lines.append(f"MODEL-ERROR {rp}: {m['error'][:500]}")
            continue
        same, n, why = compare(o, m, args.milestone in FULL or jm is not None)
        nj += n
        if same:
            ok += 1
            if args.v:
                lines.append(f"ok {rp} ({n} judgements)")
        else:
            bad += 1
            lines.append(f"MISMATCH {rp} [{bm}] mods={json.dumps(jm) if jm is not None else args.milestone}: {why}")
    t2 = time.time()
    os.remove(simtest)
    if not args.keep:
        for idx in range(len(jobs)):
            for fn in (os.path.join(work, f"{idx}.frames.txt"),):
                if os.path.exists(fn):
                    os.remove(fn)
    for l in lines:
        print(l)
    summary = {"milestone": args.gen_mods or args.milestone, "mods_seed": args.mods_seed if args.gen_mods else None, "schedule": args.schedule, "jobs": len(jobs), "match": ok,
               "mismatch": bad, "errors": err, "judgements": nj, "oracle_s": round(t1 - t0, 1),
               "model_s": round(t2 - t1, 1), "list": args.list}
    print(json.dumps(summary))
    if args.json_out:
        with open(args.json_out, "a") as f:
            f.write(json.dumps(summary) + "\n")
    return 0 if bad == 0 and err == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
