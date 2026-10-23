#!/bin/bash
# Build rbcheck against the model at git HEAD in a throwaway worktree (does not touch model/ or proofs/).
#   tools/runbudget/build.sh WORKDIR    -> WORKDIR/rbcheck
# Run each step under tools/heavy yourself if needed; the lake build is wrapped here.
set -euo pipefail
R=$HOME/lazerproof
W=${1:?workdir}
python3 -I "$R/tools/runbudget/check_defs.py"
[ -d "$W/wt" ] || git -C "$R" worktree add --detach "$W/wt" HEAD
[ -d "$W/wt/model/.lake" ] || cp -a "$R/model/.lake" "$W/wt/model/"
mkdir -p "$W/wt/model/RunBudget"
cp "$R/tools/runbudget/RunBudget.lean" "$W/wt/model/RunBudget/Main.lean"
grep -q rbcheck "$W/wt/model/lakefile.lean" || cat >> "$W/wt/model/lakefile.lean" <<'EOS'

lean_exe rbcheck where
  root := `RunBudget.Main
  moreLinkObjs := #[lzma_shim.o]
  moreLinkArgs := #["/usr/lib/x86_64-linux-gnu/liblzma.a"]
EOS
cd "$W/wt/model"
nice -n 19 "$R/tools/heavy" lake build rbcheck
cp .lake/build/bin/rbcheck "$W/rbcheck"
echo "built $W/rbcheck from $(git -C "$W/wt" rev-parse --short HEAD)"
