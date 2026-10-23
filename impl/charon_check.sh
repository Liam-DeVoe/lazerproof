#!/bin/bash
# Translatability check (does not touch proofs/): Charon -> LLBC -> Aeneas -> Lean into $OUT
# (default /tmp/osu_charon_check). Usage: [MODULES="net beatmap"] impl/charon_check.sh [extra charon args]
# SKIP_CHARON=1: reuse $OUT/osu_eval_core.llbc. MODULES: translate only these top-level modules (+ float) from a copy; the full crate needs ~3 GB.
set -euo pipefail
AENEAS_DIR=${AENEAS_DIR:-$HOME/tools/aeneas}
TC=nightly-2026-09-17
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${OUT:-/tmp/osu_charon_check}
SYSROOT=$("$HOME/.cargo/bin/rustc" +$TC --print sysroot)
mkdir -p "$OUT"
CRATE="$HERE/osu_eval_core"
if [ -n "${MODULES:-}" ]; then
  # translate only `float` + the listed top-level modules (Charon on the whole crate needs ~3 GB RSS):
  # copy them into a throw-away crate under $OUT/subset
  SUB="$OUT/subset"; mkdir -p "$SUB/src"
  rm -rf "$SUB/src"/*  # (literal path inside $OUT)
  cp "$CRATE/Cargo.toml" "$SUB/"; cp "$CRATE/src/float.rs" "$SUB/src/"
  { echo "extern crate alloc;"; echo "pub mod float;"; for m in $MODULES; do
      cp -r "$CRATE/src/$m" "$SUB/src/" 2>/dev/null || cp "$CRATE/src/$m.rs" "$SUB/src/"
      [ "$m" = net ] && echo "#[macro_use]"; echo "pub mod $m;"; done; } > "$SUB/src/lib.rs"
  CRATE="$SUB"
fi
cd "$CRATE"
[ -n "${SKIP_CHARON:-}" ] || RUSTUP_TOOLCHAIN=$TC LD_LIBRARY_PATH=$SYSROOT/lib PATH=$HOME/.cargo/bin:$PATH CARGO_TARGET_DIR=$OUT/target \
  "$AENEAS_DIR/charon" cargo --preset=aeneas \
    --opaque 'crate::float' --exclude 'crate::beatmap::dump' --exclude 'crate::beatmap::names::strings' --exclude 'crate::beatmap::errors::text' \
    --dest-file "$OUT/osu_eval_core.llbc" "$@"
# -sequential: Aeneas otherwise translates in parallel (several OCaml domains), which multiplies its
# peak RSS (net+beatmap was OOM-killed at 3 GB). AENEAS_ARGS e.g. "-strict-joins" (report code duplication).
"$AENEAS_DIR/aeneas" -sequential -no-progress-bar ${AENEAS_ARGS:-} -backend lean -use-lean-modules false -split-files -subdir Gen -namespace OsuImpl \
  -dest "$OUT/lean" "$OUT/osu_eval_core.llbc"
