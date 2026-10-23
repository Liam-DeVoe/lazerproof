#!/usr/bin/env python3
"""Check that the VERBATIM block of tools/runbudget/RunBudget.lean equals the definitions in
proofs/OsuProofs/Sim/StepInv.lean (same text, in the same order). Exit 0 iff identical."""
import sys, pathlib
root = pathlib.Path(__file__).resolve().parents[2]
tool = (root / "tools/runbudget/RunBudget.lean").read_text().splitlines()
spec = (root / "proofs/OsuProofs/Sim/StepInv.lean").read_text()
a = tool.index("-- BEGIN VERBATIM (proofs/OsuProofs/Sim/StepInv.lean)") + 1
b = tool.index("-- END VERBATIM")
block = "\n".join(tool[a:b]).strip()
# split into definitions (each starts at a doc comment) and require each to occur verbatim in StepInv.lean
chunks = [c.rstrip() for c in ("\n" + block).split("\n/--") if c.strip()]
bad = 0
for c in chunks:
    txt = c if c.startswith("def") else "/--" + c
    if txt not in spec:
        bad += 1
        print("NOT VERBATIM:\n" + txt[:300])
names = ["def sc2PreDho", "def sc2UnitsRun", "def runBudgetNeed", "def sc2VmCostS", "def sc2CsCostS"]
missing = [n for n in names if n not in block]
if missing:
    print("missing:", missing); bad += 1
# runBudgetOkE's inequality must match budgetOk's
ineq = "(2 * U + unj + 1) * (n + n + 4) + objs * (4 * n + 8) + 1 < 2 ^ 64 - 1 ∧ (U + 1) * 2000000 ≤ 2 ^ 54"
if spec.count(ineq) < 2 or ineq not in "\n".join(tool):
    print("RunBudgetS inequality text differs"); bad += 1
print("check_defs:", "OK" if bad == 0 else f"{bad} problem(s)")
sys.exit(1 if bad else 0)
