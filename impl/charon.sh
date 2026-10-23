#!/bin/bash
# Translate osu_eval_core to LLBC (Charon) and then to Lean (Aeneas). See docs/proof-poc.md.
set -euo pipefail
AENEAS_DIR=${AENEAS_DIR:-$HOME/tools/aeneas}
TC=nightly-2026-09-17
HERE=$(cd "$(dirname "$0")" && pwd)
SYSROOT=$("$HOME/.cargo/bin/rustc" +$TC --print sysroot)
OUT=$HERE/../proofs/OsuProofs/Generated
mkdir -p "$HERE/llbc" "$OUT"
cd "$HERE/osu_eval_core"
RUSTUP_TOOLCHAIN=$TC LD_LIBRARY_PATH=$SYSROOT/lib PATH=$HOME/.cargo/bin:$PATH \
  "$AENEAS_DIR/charon" cargo --preset=aeneas \
    --opaque 'crate::float' \
    --exclude 'crate::float::_::native' --exclude 'crate::float::_::of_native' \
    --dest-file "$HERE/llbc/osu_eval_core.llbc" "$@"
"$AENEAS_DIR/aeneas" -backend lean -use-lean-modules false -split-files -subdir OsuProofs/Generated -namespace OsuImpl \
  -dest "$HERE/../proofs" "$HERE/llbc/osu_eval_core.llbc"
