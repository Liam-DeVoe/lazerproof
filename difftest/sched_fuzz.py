#!/usr/bin/env python3
"""D71(2) explicit-schedule fuzz: perturb real-ReplayPlayer step lists (from player_pilot.py work dirs) and compare
`oracle run --schedule explicit:F` with the model (osu_eval/evaltest --schedule explicit:F), full eval_diff comparison.

usage: sched_fuzz.py --pilot-dirs D1,D2,... --work DIR [--seed N] [--limit N]
Each pilot job dir must hold steps.txt and job.txt (written here from player.json's beatmap/replay + the pilot list).
Variants per job: dup  (duplicates, sub-ms midpoints, fractional jitter <= 0.49 ms),
                  gaps (entries removed to make 16-100 ms gaps, plus duplicates),
                  stop (dup variant truncated at 40-90%: completed=false),  every third job.
Caller runs this under nice -n 19; each oracle call goes through tools/heavy (oracle.sh).
"""
import argparse, json, os, random, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import eval_diff  # noqa: E402
import player_pilot as pp  # noqa: E402


def v_dup(s, rng):
    out = []
    for k, t in enumerate(s):
        if k > 0 and rng.random() < 0.10:
            t = max(s[0], t + rng.uniform(-0.49, 0.49))  # keep >= the first entry (oracle requires non-decreasing)
        out.append(t)
        if rng.random() < 0.05:
            out.append(t)
        if k + 1 < len(s) and rng.random() < 0.03:
            out.append(t + (s[k + 1] - t) * rng.random())
    return [out[0]] + sorted(out[1:])


def v_gaps(s, rng):
    out = list(s)
    span = s[-1] - s[0]
    for _ in range(30):
        t0 = s[0] + rng.random() * span
        g = rng.uniform(16, 100)
        out = [t for t in out if not (t0 <= t < t0 + g)] or out
    res = []
    for t in out:
        res.append(t)
        if rng.random() < 0.03:
            res.append(t)
    return res


def fmt(x):
    return repr(float(x))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pilot-dirs", required=True)
    ap.add_argument("--work", required=True)
    ap.add_argument("--seed", type=int, default=71)
    ap.add_argument("--limit", type=int, default=0)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    cases = []
    for d in a.pilot_dirs.split(","):
        summ = json.load(open(os.path.join(d, "summary.json")))
        for rec in summ:
            if "job" in rec and os.path.exists(os.path.join(d, rec["id"], "steps.txt")):
                cases.append((rec["id"], rec["job"], os.path.join(d, rec["id"], "steps.txt")))
    if a.limit:
        cases = cases[:a.limit]
    os.makedirs(a.work, exist_ok=True)
    out = open(os.path.join(a.work, "results.jsonl"), "a")
    for ci, (rid, line, stepsf) in enumerate(cases):
        s = [float(x) for x in open(stepsf) if x.strip()]
        parts = line.split(None, 2)
        bm, rp = parts[:2]
        mods = []
        if len(parts) > 2:
            mods = ["--replace-mods", "--mods", parts[2][2:]] if parts[2].startswith("R:") else ["--mods", parts[2]]
        variants = [("dup", v_dup(s, rng)), ("gaps", v_gaps(s, rng))]
        if ci % 3 == 0:
            d = v_dup(s, rng)
            variants.append(("stop", d[:int(len(d) * rng.uniform(0.4, 0.9))]))
        for vn, refs in variants:
            w = os.path.join(a.work, "%s_%s" % (rid, vn))
            os.makedirs(w, exist_ok=True)
            ef = os.path.join(w, "refs.txt")
            with open(ef, "w") as f:
                f.write("\n".join(fmt(x) for x in refs) + "\n")
            if not os.path.exists(os.path.join(w, "run.json")):
                pp.run([pp.ORACLE, "run", "--beatmap", bm, "--replay", rp, "--schedule", "explicit:" + ef] + mods,
                       os.path.join(w, "run.json"))
            if not os.path.exists(os.path.join(w, "model.json")):
                pp.run(["nice", "-n", "19", os.path.join(ROOT, "tools", "heavy"), pp.EVAL, bm, rp,
                        "--schedule", "explicit:" + ef] + mods, os.path.join(w, "model.json"))
            o, m = pp.load(os.path.join(w, "run.json")), pp.load(os.path.join(w, "model.json"))
            rec = {"id": rid, "variant": vn, "job": line, "refs": len(refs)}
            oerr, merr = "error" in o, ("error" in m or "rejected" in m)
            if oerr or merr:
                rec.update(status="both_reject" if oerr and merr else ("oracle_error_only" if oerr else "model_reject_only"),
                           oracle_error=o.get("error"), model=m.get("error") or m.get("rejected"))
            else:
                diffs, nj = eval_diff.compare(o, m)
                rec.update(status="match" if not diffs else "mismatch", judgements=nj, steps=o["schedule"]["steps"],
                           step_check=o["schedule"].get("step_check"), completed=o["live"].get("completed"),
                           rp_rerun=isinstance(o.get("replay_player"), dict), diffs=diffs[:6])
            out.write(json.dumps(rec) + "\n")
            out.flush()
            print(json.dumps({k: rec[k] for k in rec if k != "job"}), flush=True)


if __name__ == "__main__":
    main()
