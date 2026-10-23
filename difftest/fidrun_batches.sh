#!/bin/bash
# D71/D76 low-priority fidelity runner: eval_diff run over list chunks, one heavy job at a time, nice 19,
# waits for MemAvailable >= 2500 MB before each chunk.  usage: fidrun_batches.sh CHUNKDIR WORKROOT [schedule]
set -u
cd "$(dirname "$0")/.."
dir=$1; root=$2; sched=${3:-catchup}
export EVALTEST=${EVALTEST:-$PWD/data/wip/d49-reg/osu_eval_new}
for c in "$dir"/c*; do
  n=$(basename "$c"); w="$root/$n"
  [ -f "$w/summary.json" ] && continue
  until [ "$(awk '/MemAvailable/{print int($2/1024)}' /proc/meminfo)" -ge 2500 ]; do sleep 30; done
  while [ "$(vmstat 5 2 | tail -1 | awk '{print $16}')" -gt 30 ]; do echo "$(date +%T) iowait high, pausing"; sleep 60; done
  echo "$(date +%T) start $n mem=$(awk '/MemAvailable/{print int($2/1024)}' /proc/meminfo)"
  nice -n 19 tools/heavy python3 difftest/eval_diff.py run --list "$c" --work "$w" --tag "early-$n" --schedule "$sched" --chunk 50 2>&1 | grep -v '^\s*$' | tail -6
done
echo "$(date +%T) all done"
