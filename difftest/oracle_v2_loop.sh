#!/bin/sh
# Detached driver: keeps oracle results (catchup + perframe) up to date with the v2 corpus, 200 jobs per
# oracle process, one oracle process at a time (flock inside oracle_vs_server_v2.py), then triages new server
# mismatches on the model (difftest/triage_v2.py, niced, at most 60 per round) and refreshes report + metrics.
# Stop: touch data/oracle_v2/STOP
cd /home/exedev/lazerproof || exit 1
mkdir -p data/oracle_v2
while [ ! -e data/oracle_v2/STOP ]; do
  python3 -I difftest/oracle_vs_server_v2.py run --schedule catchup --limit 200
  python3 -I difftest/oracle_vs_server_v2.py run --schedule perframe --limit 100 --focus 7
  nice -n 15 python3 -I difftest/triage_v2.py --new --limit 60 --max-shift-runs 600 >> data/oracle_v2/triage.log 2>&1
  python3 -I difftest/oracle_vs_server_v2.py report --md data/oracle_v2/report.md --metrics status/metrics.json > /dev/null 2>&1
  sleep 120
done
