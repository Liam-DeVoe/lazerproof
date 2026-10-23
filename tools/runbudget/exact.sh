#!/bin/bash
# Phase 2: exact U via `rbcheck exact` for each line of LIST (beatmap, replay, schedule, variant own|wg[, ...]).
#   tools/runbudget/exact.sh RBCHECK LIST OUT.jsonl     (one niced tools/heavy process per run; resumable)
# RB_MODE=exact1 (default) uses the one-pass loop; RB_MODE=exact the two-pass sc2UnitsRun fold.
M=${RB_MODE:-exact1}
R=$HOME/lazerproof; B=${1:?rbcheck}; L=${2:?list}; O=${3:?out}
cd "$R"; touch "$O"
while IFS=$'\t' read -r bm osr sch var _; do
  key="$bm $osr $sch $var"
  want='"one_pass":false'; [ "$M" = exact1 ] && want='"one_pass":true'
  grep -F "\"key\":\"$key\"" "$O" | grep -qF "$want" && continue   # resume: already done in this mode
  if [ "$var" = wg ]; then res=$(nice -n 19 tools/heavy "$B" "$M" "$bm" "$osr" "$sch" '[{"acronym":"WG"}]')
  else res=$(nice -n 19 tools/heavy "$B" "$M" "$bm" "$osr" "$sch"); fi
  echo "{\"key\":\"$key\",\"variant\":\"$var\",\"r\":${res:-null}}" >> "$O"
done < "$L"
