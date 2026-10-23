#!/bin/sh
# Restart the resumable replay crawl if it died (cron, every 15 min).
cd /home/exedev/lazerproof || exit 1
pgrep -f "fetch_v1.py all" >/dev/null && exit 0
grep -q "CRAWL DONE" data/crawl.log 2>/dev/null && exit 0
echo "$(date) watchdog restart" >> data/crawl.log
setsid nohup python3 difftest/fetch_v1.py all --count 1500 --max 15000 >> data/crawl.log 2>&1 < /dev/null &
