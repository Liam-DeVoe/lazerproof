#!/usr/bin/env python3
"""D71(1) pilot: lazer's real ReplayPlayer (`oracle player`) vs `oracle run --schedule explicit:STEPS` vs the model
(osu_eval/evaltest --schedule explicit:STEPS), on the step schedule the real player actually used.

usage: player_pilot.py --list JOBS --work DIR [--stage player|run|model|compare|all]
Each stage is one process per job (oracle.sh wraps tools/heavy itself). Caller runs this under nice -n 19.
Outputs per job in DIR/<replay-id>/: player.json, steps.txt, run.json, model.json; DIR/summary.json.
"""
import argparse, json, os, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import eval_diff  # noqa: E402

ORACLE = os.path.join(ROOT, "oracle", "oracle.sh")
# D80c: ORACLE_PLAYER=oracle_fail/oracle_fail.sh runs the player stage on the separate fail-path build (emits after a
# genuine fail once the clock has stalled); `run` always uses the cached-fingerprint oracle above.
PLAYER = os.environ.get("ORACLE_PLAYER") or ORACLE
EVAL = os.environ.get("EVALTEST") or os.path.join(ROOT, "data", "wip", "d49-reg", "osu_eval_new")


def mem_ok():
    for l in open("/proc/meminfo"):
        if l.startswith("MemAvailable"):
            return int(l.split()[1]) // 1024 >= 2500
    return False


def wait_mem():
    t0 = time.time()
    while not mem_ok():
        if time.time() - t0 > 600:
            raise SystemExit("MemAvailable < 2500 MB for 10 min; stopping")
        time.sleep(30)


def run(cmd, out, timeout=900):
    wait_mem()
    env = dict(os.environ, ORACLE_NOCACHE="1")
    t0 = time.time()
    with open(out, "w") as f:
        try:
            p = subprocess.run(["timeout", "-k", "10", str(timeout)] + cmd, stdout=f, stderr=subprocess.PIPE, text=True, env=env, timeout=timeout + 30)
        except subprocess.TimeoutExpired:
            f.write(json.dumps({"error": "timeout %ds" % timeout}) + "\n")
            print("%s %s TIMEOUT" % (time.strftime("%H:%M:%S"), os.path.basename(out)), file=sys.stderr, flush=True)
            return
    print("%s %s rc=%d %.0fs" % (time.strftime("%H:%M:%S"), os.path.basename(out), p.returncode, time.time() - t0),
          file=sys.stderr, flush=True)
    if p.returncode != 0:
        with open(out + ".err", "w") as f:
            f.write(p.stderr[-5000:])


def load(p):
    try:
        return json.loads(open(p).read().strip().splitlines()[-1])
    except Exception as e:
        return {"error": "unreadable %s: %s" % (p, e)}


def cmp_player_run(pl, rn):
    """Real ReplayPlayer output vs oracle run (replay_player semantics if it differs from live)."""
    d = []
    r = rn["replay_player"] if isinstance(rn.get("replay_player"), dict) else rn["live"]
    if [eval_diff.bits(x) for x in pl["steps"]] != [eval_diff.bits(x) for x in rn["schedule"].get("steps_list", pl["steps"])]:
        d.append("steps differ")
    for k in ["rank", "total_score", "max_combo", "failed"]:
        if pl.get(k) != r.get(k):
            d.append("%s: player=%s run=%s" % (k, pl.get(k), r.get(k)))
    if eval_diff.bits(pl["accuracy"]) != eval_diff.bits(r["accuracy"]):
        d.append("accuracy: player=%s run=%s" % (pl["accuracy"], r["accuracy"]))
    if pl["statistics"] != r["statistics"]:
        d.append("statistics: player=%s run=%s" % (pl["statistics"], r["statistics"]))
    pj, rj = pl["judgements"], r["judgements"]
    if len(pj) != len(rj):
        d.append("judgement count: player=%d run=%d" % (len(pj), len(rj)))
    for k, (a, b) in enumerate(zip(pj, rj)):
        if (a["type"], a["result"], eval_diff.bits(a["time"]), a["combo"], eval_diff.bits(a["health"])) != \
                (b["type"], b["result"], eval_diff.bits(b["time"]), b["combo"], eval_diff.bits(b["health"])):
            d.append("judgement %d: player=%s run=%s" % (k, a, {x: b.get(x) for x in ("i", "n", "type", "result", "time", "combo", "health")}))
            break
    return d, len(pj)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", required=True)
    ap.add_argument("--work", required=True)
    ap.add_argument("--stage", default="all")
    a = ap.parse_args()
    jobs = eval_diff.read_jobs(a.list)
    summ = []
    for line in jobs:
        parts = line.split(None, 2)
        bm, rp = parts[:2]
        mods = ["--mods", parts[2]] if len(parts) > 2 else []
        if mods and parts[2].startswith("R:"):  # "R:<json>" = --replace-mods
            mods = ["--replace-mods", "--mods", parts[2][2:]]
        rid = os.path.basename(rp).split(".")[0] + ("_m%d" % jobs.index(line) if mods else "")
        w = os.path.join(a.work, rid)
        os.makedirs(w, exist_ok=True)
        steps = os.path.join(w, "steps.txt")
        if a.stage in ("player", "all") and not os.path.exists(os.path.join(w, "player.json")):
            run([PLAYER, "player", "--beatmap", bm, "--replay", rp, "--steps-out", steps] + mods, os.path.join(w, "player.json"))
        if a.stage in ("run", "all") and not os.path.exists(os.path.join(w, "run.json")) and os.path.exists(steps):
            run([ORACLE, "run", "--beatmap", bm, "--replay", rp, "--schedule", "explicit:" + steps, "--trace"] + mods,
                os.path.join(w, "run.json"))
        if a.stage in ("model", "all") and not os.path.exists(os.path.join(w, "model.json")) and os.path.exists(steps):
            run(["nice", "-n", "19", os.path.join(ROOT, "tools", "heavy"), EVAL, bm, rp, "--schedule", "explicit:" + steps] + mods,
                os.path.join(w, "model.json"), timeout=900)
        if a.stage in ("compare", "all"):
            pl, rn, md = (load(os.path.join(w, f)) for f in ("player.json", "run.json", "model.json"))
            rec = {"id": rid, "job": line}
            if any("error" in x for x in (pl, rn, md)):
                rec["error"] = [x.get("error") for x in (pl, rn, md)]
            else:
                rn["schedule"]["steps_list"] = (rn.get("trace") or {}).get("steps", pl["steps"])
                d1, nj = cmp_player_run(pl, rn)
                d2, _ = eval_diff.compare(rn, md)
                rec.update(mods=[m["acronym"] for m in rn["input"]["mods"]], steps=len(pl["steps"]), judgements=nj,
                           step_check=rn["schedule"].get("step_check"), completed=rn["live"].get("completed"),
                           player_failed=pl.get("failed"), rp_rerun=isinstance(rn.get("replay_player"), dict),
                           player_vs_run=d1[:6] or "match", run_vs_model=d2[:6] or "match")
            summ.append(rec)
            print(json.dumps(rec), flush=True)
    if a.stage in ("compare", "all"):
        with open(os.path.join(a.work, "summary.json"), "w") as f:
            json.dump(summ, f, indent=1)


if __name__ == "__main__":
    main()
