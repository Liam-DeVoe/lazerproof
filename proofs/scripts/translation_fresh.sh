#!/bin/bash
# Translation freshness check (final audit m6): re-run Charon+Aeneas on the current impl/osu_eval_core for the three
# module sets with the recorded recipes (D29 / RESUME), install each into a throw-away copy of Generated/ with the
# normal install scripts, and diff against the committed proofs/OsuProofs/Generated/. Exit 0 = identical
# (modulo `Source: '...', lines` comments if FRESH_IGNORE_LINES=1), 1 = differs (diff in $W/diff.txt).
# Run in an announced window, REPL stopped, each step under tools/heavy (normal slot, 3 GB min-mem for charon/aeneas, D51; not exclusive, D74):
#   proofs/scripts/translation_fresh.sh            (calls tools/heavy itself; ~10-15 min)
# STEPS="net sim eval" selects the sets. Work dir: $FRESH_DIR (default data/wip/fresh).
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
W=${FRESH_DIR:-$ROOT/data/wip/fresh}
STEPS=${STEPS:-"net sim eval"}
mkdir -p "$W"
# throw-away tree: proofs/scripts (install scripts) + proofs/OsuProofs/Generated (current files, overwritten in place)
T="$W/tree"; mkdir -p "$T/proofs/scripts" "$T/proofs/OsuProofs/Generated"
cp "$ROOT"/proofs/scripts/install_generated.sh "$ROOT"/proofs/scripts/install_sim_generated.py \
   "$ROOT"/proofs/scripts/install_eval_generated.py "$T/proofs/scripts/"
cp "$ROOT"/proofs/OsuProofs/Generated/*.lean "$T/proofs/OsuProofs/Generated/"
H="$ROOT/tools/heavy"
for s in $STEPS; do
  case $s in
    net)  OUT="$W/net" MODULES="${FRESH_NET_MODULES:-net beatmap hit_windows schedule slider}" "$H" "$ROOT/impl/charon_check.sh"
          bash "$T/proofs/scripts/install_generated.sh" "$W/net/lean/Gen" ;;
    sim)  OUT="$W/sim" "$H" "$ROOT/impl/charon_check.sh" --start-from crate::sim --start-from crate::replay
          python3 -I "$T/proofs/scripts/install_sim_generated.py" "$W/sim/lean/Gen" ;;
    eval) OUT="$W/eval" "$H" "$ROOT/impl/charon_check.sh" --start-from crate::eval --opaque crate::lzma \
            --exclude crate::eval::text --exclude crate::eval::osr::text --exclude crate::eval::mods_json::text \
            --exclude crate::eval::adapter::text
          python3 -I "$T/proofs/scripts/install_eval_generated.py" "$W/eval/lean/Gen" ;;
  esac
done
if diff -r "$ROOT/proofs/OsuProofs/Generated" "$T/proofs/OsuProofs/Generated" > "$W/diff.txt"; then
  echo "translation_fresh: Generated/ is identical to a fresh translation of impl/ ($STEPS)"
elif diff -r -I '^ *Source: ' "$ROOT/proofs/OsuProofs/Generated" "$T/proofs/OsuProofs/Generated" > /dev/null; then
  # e.g. EvalFuns was installed from a crate copy: its `Source: 'src/..'` comments lack the `osu_eval_core/` prefix
  echo "translation_fresh: Generated/ = fresh translation ($STEPS) except \`Source:\` comment lines ($(grep -c '^[<>]' "$W/diff.txt") lines)"
else
  echo "translation_fresh: DIFFERS ($(grep -c '^[<>]' "$W/diff.txt") lines; $W/diff.txt):"; head -40 "$W/diff.txt"; exit 1
fi
# clean up (STATE safety rule: literal absolute paths only; a custom FRESH_DIR is left alone)
if [ -z "${FRESH_KEEP:-}" ] && [ "$W" = /home/exedev/lazerproof/data/wip/fresh ]; then
  rm -rf /home/exedev/lazerproof/data/wip/fresh/net /home/exedev/lazerproof/data/wip/fresh/sim \
    /home/exedev/lazerproof/data/wip/fresh/eval /home/exedev/lazerproof/data/wip/fresh/tree
fi
