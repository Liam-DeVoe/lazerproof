#!/bin/sh
# Restart the resumable lazer-score crawl (fetch_v2.py) if it died (cron, every 15 min).
# Stops for good after "CRAWL V2 DONE ok=$MAX"; after "CRAWL V2 STOP disk" it is retried (exits again at once while
# disk is low). Bound raised 5000 -> 8000 on 2026-10-21 after the disk grew to 50 GB (DECISIONS.md D13 note);
# min free raised to 10 GB to respect the >= 8 GB free disk budget.
MAX=8000
cd /home/exedev/lazerproof || exit 1
pgrep -f "fetch_v2.py crawl" >/dev/null && exit 0
grep -q "CRAWL V2 DONE ok=$MAX" data/crawl_v2.log 2>/dev/null && exit 0
echo "$(date) watchdog restart" >> data/crawl_v2.log
setsid nohup python3 -I difftest/fetch_v2.py crawl --max $MAX --min-free-gb 10 --per-beatmap 1 --per-user 5 >> data/crawl_v2.log 2>&1 < /dev/null &
