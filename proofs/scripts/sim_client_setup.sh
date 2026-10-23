#!/bin/bash
# sim_client_setup.sh CLIENT [UPTO_MODULE]: prepare a shared-REPL client (proofs/scripts/req.sh) for the sim
# refinement proofs while the server header is OsuProofs.Manual only: commits Auto/{Abs,Base,Gen}, the sim
# translation (SimTypes, SimFunsExternal, SimFuns up to the end of rust module UPTO_MODULE, default sim::scoring; NEVER all of it),
# the spec modules OsuModel.Sim.* / Replay.Frames that Manual does not import (pasted source, same names), and the
# proof files listed in OsuProofs/Sim/ORDER (one per line). Only for iteration; check_all/lake build use real imports.
set -e
C=$1; UPTO=${2:-sim::scoring}  # never the whole SimFuns: 33k lines OOM-killed the shared server (2026-10-22)
P=$(cd "$(dirname "$0")/.." && pwd); cd "$P"
S=${TMPDIR:-/tmp}/simsetup_$C; mkdir -p "$S"
F=OsuProofs/Generated/SimFuns.lean
if [ -n "$UPTO" ]; then
  last=$(grep -n "^/-- \[osu_eval_core::$UPTO" $F | tail -1 | cut -d: -f1)
  cut=$(awk -v l=$last 'NR>l && /^\/-- \[osu_eval_core::/ {print NR; exit}' $F)
  head -n $((cut-1)) $F > $S/simfuns.lean; echo "end OsuImpl" >> $S/simfuns.lean
else cp $F $S/simfuns.lean; fi
n=0
req() { n=$((n+1)); out=$(LINES_MAX=5 scripts/req.sh "$C" "$(printf 'setup%03d' $n)" --commit "$1"); echo "$1: $out" | head -3; }
req OsuProofs/Auto/Abs.lean
[ -n "${WITH_AUTO:-}" ] && { req OsuProofs/Auto/Base.lean; req OsuProofs/Auto/Gen.lean; }
# header env already has the sim translation (Manual imports Generated.SimFuns + OsuModel.Sim.Step since 9c53685)?
echo '#check @OsuImpl.sim.step.run' > $S/probe.lean
if LINES_MAX=3 scripts/req.sh "$C" probe_$(date +%s%N) $S/probe.lean | grep -q 'errors=true'; then
  req OsuProofs/Generated/SimTypes.lean; req OsuProofs/Generated/SimFunsExternal.lean; req $S/simfuns.lean
  for m in ${SPEC_MODS:-Replay/Frames Sim/Scoring}; do req ../model/OsuModel/$m.lean; done
fi
[ -f OsuProofs/Sim/ORDER ] && while read -r f; do [ -n "$f" ] && req "OsuProofs/Sim/$f.lean"; done < OsuProofs/Sim/ORDER
