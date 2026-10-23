#!/bin/bash
# Orchestrator health check: load/mem/disk, heavy-queue stalls, background services.
# Prints one OK line, or WARN lines describing problems.
d=/tmp/osu-heavy
load=$(cut -d' ' -f1 /proc/loadavg); mem=$(awk '/MemAvailable/ {print int($2/1024)}' /proc/meminfo)
disk=$(df -BG --output=avail / | tail -1 | tr -d ' G')
warn=()
[ "$disk" -lt 8 ] && warn+=("disk free ${disk}G < 8G")
[ "$mem" -lt 900 ] && warn+=("MemAvailable ${mem}MB < 900")
# heavy wrappers whose only child is `sleep` (= mem-wait loop) for > 10 min
for p in $(pgrep -x heavy); do
  kids=$(ps -o comm= --ppid "$p" | sort -u | tr '\n' ' ')
  et=$(ps -o etimes= -p "$p" 2>/dev/null | tr -d ' ')
  if [ "$kids" = "sleep " ] && [ "${et:-0}" -gt 600 ]; then
    warn+=("heavy wrapper $p waiting (only sleep child) ${et}s: $(ps -o args= -p "$p" | cut -c1-120)")
  fi
done
holders=0; for s in "$d"/slot*; do i=$(stat -c %i "$s"); grep -q ":$i 0 EOF" /proc/locks && holders=$((holders+1)); done
waiters=$(ps -eo args | grep -c '^flock -s 8$')
if [ -e /home/exedev/lazerproof/data/oracle_v2/STOP ]; then :   # paused on purpose (D20)
else pgrep -f '^sh (difftest/oracle_v2_loop|tools/oracle_bg).sh' >/dev/null || warn+=("oracle loop (oracle_bg.sh) not running"); fi
# shared proof REPL (D22): down outside an announced check_all window = crashed (restart: proofs/scripts/repl_server.sh start)
pgrep -f '^lean --run scripts/Repl.lean' >/dev/null || pgrep -f 'check_all.sh' >/dev/null || warn+=("shared proof REPL not running (no check_all in progress)")
tri=$(pgrep -fc '^python3 -I difftest/triage_v2.py' )
line="load=$load mem=${mem}MB disk=${disk}G slots_held=$holders gate_waiters=$waiters triage_procs=$tri"
if [ ${#warn[@]} -eq 0 ]; then echo "OK $line"; else echo "WARN $line"; printf '  - %s\n' "${warn[@]}"; fi
