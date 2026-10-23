#!/usr/bin/env python3
"""Byte-identical differential test: Lean `evaltest` (pinned build) vs Rust `osu_eval` (no oracle).

usage: rust_eval_diff.py --list JOBS [--schedule S] [--replace-mods] [--no-classic] [--mods JSON] [--dump-playable]
                         [--extra ARG ...] [--label L] [--json-out F] [--work DIR] [--lean-timeout SEC]
JOBS: lines "BEATMAP OSR [MODS-JSON]" (a per-job MODS-JSON is passed as --mods; --mods sets one for every job).
Every job: both binaries run with the same arguments; stdout bytes and exit codes must be identical (with
--dump-playable: also the dumped files). A Lean `PANIC` on stderr counts as `lean_panics` (must be 0).
Env: LEAN_EVALTEST, RUST_EVAL (defaults: data/wip/rust-eval/evaltest_lean_1b0a176, impl/target/release/osu_eval).
Prints mismatches and one summary JSON line (appended to --json-out with the label)."""
import argparse, json, os, subprocess, sys, time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = os.environ.get("LEAN_EVALTEST") or os.path.join(ROOT, "data/wip/rust-eval/evaltest_lean_1b0a176")
RUST = os.environ.get("RUST_EVAL") or os.path.join(ROOT, "impl/target/release/osu_eval")


def run(cmd, timeout):
    t = time.time()
    try:
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
        return p.returncode, p.stdout, p.stderr, time.time() - t
    except subprocess.TimeoutExpired:
        return "timeout", b"", b"", time.time() - t


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", required=True)
    ap.add_argument("--schedule", default="catchup")
    ap.add_argument("--replace-mods", action="store_true")
    ap.add_argument("--no-classic", action="store_true")
    ap.add_argument("--mods")
    ap.add_argument("--dump-playable", action="store_true")
    ap.add_argument("--extra", action="append", default=[])
    ap.add_argument("--label", default="")
    ap.add_argument("--json-out")
    ap.add_argument("--work", default="/tmp/rust_eval_diff")
    ap.add_argument("--lean-timeout", type=float, default=900)
    a = ap.parse_args()
    os.makedirs(a.work, exist_ok=True)
    jobs = [l.rstrip("\n") for l in open(a.list) if l.strip() and not l.lstrip().startswith("#")]
    st = dict(runs=0, identical=0, mismatch=0, identical_rejections=0, lean_panics=0, lean_timeouts=0,
              judgements=0, lean_s=0.0, rust_s=0.0)
    rej_stages = {}
    for line in jobs:
        parts = line.split(None, 2)
        bm, rp = parts[0], parts[1]
        args = [bm, rp]
        if a.schedule != "catchup":
            args += ["--schedule", a.schedule]
        mods = parts[2] if len(parts) > 2 else a.mods
        if mods is not None:
            args += ["--mods", mods]
        if a.replace_mods:
            args.append("--replace-mods")
        if a.no_classic:
            args.append("--no-classic")
        args += a.extra
        lp = os.path.join(a.work, "lean_playable.json")
        rpth = os.path.join(a.work, "rust_playable.json")
        for f in (lp, rpth):
            if os.path.exists(f):
                os.remove(f)
        lc, lo, le, lt = run([LEAN] + args + (["--dump-playable", lp] if a.dump_playable else []), a.lean_timeout)
        rc, ro, re_, rt = run([RUST] + args + (["--dump-playable", rpth] if a.dump_playable else []), a.lean_timeout)
        st["runs"] += 1
        st["lean_s"] += lt
        st["rust_s"] += rt
        if lc == "timeout":
            st["lean_timeouts"] += 1
            print("LEAN TIMEOUT", line, flush=True)
            continue
        if b"PANIC" in le:
            st["lean_panics"] += 1
            print("LEAN PANIC", line, le[:300], flush=True)
        same = (lc == rc and lo == ro)
        if same and a.dump_playable and lc == 0:
            same = os.path.exists(lp) and os.path.exists(rpth) and open(lp, "rb").read() == open(rpth, "rb").read()
        if same:
            st["identical"] += 1
            if lo.startswith(b'{"rejected"'):
                st["identical_rejections"] += 1
                try:
                    s = json.loads(lo)["stage"]
                    rej_stages[s] = rej_stages.get(s, 0) + 1
                except Exception:
                    pass
            elif lo.startswith(b'{"model"'):
                st["judgements"] += lo.count(b'"result":') // (1 if b'"replay_player":"same_as_live"' in lo else 2)
        else:
            st["mismatch"] += 1
            k = st["mismatch"]
            open(os.path.join(a.work, f"mis{k}.lean"), "wb").write(lo + b"\n--stderr--\n" + le)
            open(os.path.join(a.work, f"mis{k}.rust"), "wb").write(ro + b"\n--stderr--\n" + re_)
            print("MISMATCH", k, line, "exit", lc, rc, flush=True)
    st["rejection_stages"] = rej_stages
    st["lean_s"] = round(st["lean_s"], 2)
    st["rust_s"] = round(st["rust_s"], 2)
    st["label"] = a.label
    st["schedule"] = a.schedule
    if a.json_out:
        with open(a.json_out, "a") as f:
            f.write(json.dumps(st) + "\n")
    print(json.dumps(st), flush=True)


if __name__ == "__main__":
    main()
