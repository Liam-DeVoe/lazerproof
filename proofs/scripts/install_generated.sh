#!/bin/bash
# Install an Aeneas translation produced by impl/charon_check.sh (OUT=<dir>) into
# OsuProofs/Generated/{Types,Funs}.lean (+ the *_Template.lean files for reference).
# The hand-written trusted layer (TypesExternal.lean, FunsExternal.lean) is not touched.
# usage: proofs/scripts/install_generated.sh <OUT>/lean/Gen
set -euo pipefail
SRC=$1
DST=$(cd "$(dirname "$0")/.." && pwd)/OsuProofs/Generated
for f in Types Funs TypesExternal_Template FunsExternal_Template; do
  sed -e 's/^import Gen\./import OsuProofs.Generated./' "$SRC/$f.lean" > "$DST/$f.lean"
done
echo "installed $(grep -c '^def\|^ *def ' "$DST/Funs.lean") defs into $DST"
