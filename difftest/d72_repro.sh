#!/bin/bash
# quick check of the repro0 cases with the worktree's evaltest and osu_eval
W=/home/exedev/osu-verified/.claude/worktrees/agent-ab4030d638366f6d6
S=/tmp/claude-1000/-home-exedev/5a067c7e-69f6-4190-93e6-f7fa504e1337/scratchpad/d72
E=$W/model/.lake/build/bin/evaltest
R=$W/impl/target/release/osu_eval
B=$W/data/beatmaps/505083.osu
O=$W/data/replays_v2/7742845812.osr
printf '0\nInfinity\n' > $S/inf.txt
printf '0\nNaN\n' > $S/nan.txt
for f in $W/data/wip/fidrun/repro0/refs.txt $W/data/wip/fidrun/repro0/empty.txt $W/data/wip/fidrun/repro0/dec.txt $S/inf.txt $S/nan.txt; do
  n=$(basename $f .txt)
  for x in $E $R; do
    timeout 300 $W/tools/heavy $x $B $O --schedule explicit:$f > $S/r_${n}_$(basename $x).json 2>&1
    echo "$n $(basename $x) rc=$?"
  done
  cmp -s $S/r_${n}_evaltest.json $S/r_${n}_osu_eval.json && echo "  same $n" || echo "  DIFF $n"
  grep -o '"total_score_without_mods":"[^"]*"\|"rejected":{[^}]*}\|"error":"[^"]*"' $S/r_${n}_osu_eval.json | head -3
done
