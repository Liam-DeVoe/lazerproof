#!/usr/bin/env python3
"""D80c fail-gate check: real ReplayPlayer (oracle_fail player, recording its host-frame reference times) vs oracle_fail
run on those references with the FST gate (= oracle/model semantics) and with ORACLE_FAIL_GATE=reference (lazer's
GameplayClockContainer.CurrentTime gate), plus osu_eval on the same references.
usage: fail_gate_check.py BEATMAP REPLAY MODSJSON WORKDIR  (prints one JSON line)"""
import json, os, subprocess, sys
sys.path.insert(0, os.path.expanduser("~/lazerproof/difftest"))
import eval_diff, player_pilot as pp
ROOT = os.path.expanduser("~/lazerproof")
OF = ROOT + "/oracle_fail/oracle_fail.sh"
bm, rp, mods, w = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
os.makedirs(w, exist_ok=True)
M = ["--mods", mods] if mods else []
def go(cmd, out, env={}):
    if os.path.exists(out): return
    pp.wait_mem()
    with open(out, "w") as f:
        subprocess.run(["timeout", "900", "nice", "-n", "19"] + cmd, stdout=f, stderr=subprocess.DEVNULL, env=dict(os.environ, ORACLE_NOCACHE="1", **env), check=False)
go([OF, "player", "--beatmap", bm, "--replay", rp, "--steps-out", w + "/steps.txt"] + M, w + "/player.json", {"ORACLE_FAIL_REFS_OUT": w + "/refs.txt"})
sch = ["--schedule", "explicit:" + w + "/refs.txt"]
go([OF, "run", "--beatmap", bm, "--replay", rp, "--trace"] + sch + M, w + "/run_fst.json")
go([OF, "run", "--beatmap", bm, "--replay", rp, "--trace"] + sch + M, w + "/run_ref.json", {"ORACLE_FAIL_GATE": "reference"})
go(["nice", "-n", "19", ROOT + "/tools/heavy", pp.EVAL, bm, rp] + sch + M, w + "/model.json")
pl = pp.load(w + "/player.json"); res = {"id": os.path.basename(w), "player_failed": pl.get("failed"), "steps": len(pl["steps"])}
for k in ("run_fst", "run_ref"):
    rn = pp.load(w + "/%s.json" % k); rn["schedule"]["steps_list"] = rn["trace"]["steps"]
    d, nj = pp.cmp_player_run(pl, rn); res["player_vs_" + k] = d[:3] or "match"; res[k + "_step_check"] = rn["schedule"].get("step_check")
    res[k + "_fail_time"] = rn["replay_player"]["fail_time"] if isinstance(rn["replay_player"], dict) else rn["live"].get("fail_time")
rf, md = pp.load(w + "/run_fst.json"), pp.load(w + "/model.json")
d, _ = eval_diff.compare(rf, md); res["run_fst_vs_model"] = d[:3] or "match"
print(json.dumps(res))
