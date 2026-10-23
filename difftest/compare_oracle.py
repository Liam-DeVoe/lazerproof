#!/usr/bin/env python3
"""Compare two oracle JSONL outputs (e.g. two schedules, or two runs for determinism), keyed by replay path.

Usage: python3 -I difftest/compare_oracle.py A.jsonl B.jsonl [--exact] [-v]
  default: compares results (statistics, total score, max combo, accuracy, fail) and per-judgement (object, result)
  --exact: whole JSON lines must be byte-identical (determinism check)
"""
import argparse, json

ap = argparse.ArgumentParser()
ap.add_argument("a"); ap.add_argument("b")
ap.add_argument("--exact", action="store_true")
ap.add_argument("-v", action="store_true")
args = ap.parse_args()

def load(p):
    out = {}
    for line in open(p):
        d = json.loads(line)
        out[d.get("input", d).get("replay")] = (line.rstrip("\n"), d)
    return out

A, B = load(args.a), load(args.b)
common = sorted(set(A) & set(B))
n = len(common)
if args.exact:
    same = sum(A[k][0] == B[k][0] for k in common)
    print(f"byte-identical: {same}/{n}")
    for k in common:
        if A[k][0] != B[k][0]:
            print("  DIFFERS", k)
    raise SystemExit(0 if same == n else 1)

res_diff = jr_diff = jt_diff = 0
for k in common:
    a, b = A[k][1], B[k][1]
    if "error" in a or "error" in b:
        print("error in", k); continue
    la, lb = a["live"], b["live"]
    keys = ["statistics", "total_score", "max_combo", "accuracy", "failed", "rank"]
    rd = [x for x in keys if la[x] != lb[x]]
    ja = [(j["i"], j["n"], j["result"]) for j in la.get("judgements", [])]
    jb = [(j["i"], j["n"], j["result"]) for j in lb.get("judgements", [])]
    sa = sorted(ja); sb = sorted(jb)
    jrd = sa != sb
    jtd = [(j["i"], j["n"], j["time"]) for j in la.get("judgements", [])] != [(j["i"], j["n"], j["time"]) for j in lb.get("judgements", [])]
    res_diff += bool(rd); jr_diff += jrd; jt_diff += jtd
    if args.v or rd:
        da = {x: la["statistics"].get(x, 0) - lb["statistics"].get(x, 0) for x in set(la["statistics"]) | set(lb["statistics"])}
        da = {x: v for x, v in da.items() if v}
        nd = sum(1 for x, y in zip(sorted(ja), sorted(jb)) if x != y)
        print(k, "result-diff:", rd, "stat delta(A-B):", da, "judgement result diffs:", nd, "score", la["total_score"], lb["total_score"])
print(f"replays={n} result-differs={res_diff} judgement-results-differ={jr_diff} judgement-times-or-order-differ={jt_diff}")
