#!/bin/sh
# Pause replay crawlers when free disk is low; resume when it recovers (cron, every 5 min).
avail=$(df --output=avail -k / | tail -1)
if [ "$avail" -lt 2621440 ]; then
  pkill -STOP -f "fetch_v[12].py" && echo "$(date) diskguard: paused crawlers (avail ${avail}k)" >> /home/exedev/lazerproof/status/diskguard.log
elif [ "$avail" -gt 3670016 ]; then
  pkill -CONT -f "fetch_v[12].py"
fi
