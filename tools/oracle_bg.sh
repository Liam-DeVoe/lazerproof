#!/bin/sh
# Background server-agreement loop at lowest priority (D65): same body as difftest/oracle_v2_loop.sh, but each round
# waits until the proofs leave room (MemAvailable >= 2800 MB, no HEAVY_EXCLUSIVE/check_all running) and runs niced.
# earlyoom already prefers dotnet/simtest/evaltest, so proofs win under memory pressure.
# Stop: touch data/oracle_v2/STOP
cd /home/exedev/lazerproof || exit 1
mkdir -p data/oracle_v2
room() {
  m=$(awk '/MemAvailable/{print int($2/1024)}' /proc/meminfo)
  [ "$m" -ge 2800 ] || return 1
  pgrep -f 'proofs/scripts/check_all.sh' >/dev/null 2>&1 && return 1
  return 0
}
while [ ! -e data/oracle_v2/STOP ]; do
  until room || [ -e data/oracle_v2/STOP ]; do sleep 60; done
  [ -e data/oracle_v2/STOP ] && break
  nice -n 19 python3 -I difftest/oracle_vs_server_v2.py run --schedule catchup --limit 50
  room && nice -n 19 python3 -I difftest/triage_v2.py --new --limit 20 --max-shift-runs 300 >> data/oracle_v2/triage.log 2>&1
  nice -n 19 python3 -I difftest/oracle_vs_server_v2.py report --md data/oracle_v2/report.md --metrics status/metrics.json > /dev/null 2>&1
  sleep 120
done
