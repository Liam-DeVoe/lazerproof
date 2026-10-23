#!/bin/bash
# Build "playable.json replay.osr" pair lists for difftest/rust_sim_diff.py using the Lean evaltest's
# --dump-playable (no oracle). usage: mk_pairs.sh JOBS.txt OUTDIR [nomod]
# With "nomod" the playable is built with --mods '[]' --replace-mods (no auto-Classic).
set -u
jobs=$1; out=$2; mode=${3:-}
EV=$HOME/lazerproof/model/.lake/build/bin/evaltest
mkdir -p "$out"
: > "$out/pairs.txt"
i=0
while read -r bm rp rest; do
  [ -z "$bm" ] && continue
  case "$bm" in \#*) continue;; esac
  p="$out/$i.json"
  if [ "$mode" = nomod ]; then
    "$EV" "$bm" "$rp" --mods '[]' --replace-mods --dump-playable "$p" >/dev/null 2>&1
  else
    "$EV" "$bm" "$rp" --dump-playable "$p" >/dev/null 2>&1
  fi
  [ -s "$p" ] && echo "$p $rp" >> "$out/pairs.txt"
  i=$((i+1))
done < "$jobs"
wc -l < "$out/pairs.txt"
