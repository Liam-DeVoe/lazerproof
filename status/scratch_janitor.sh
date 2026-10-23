#!/bin/bash
# Delete stale top-level scratch dirs (no open files, nothing modified in 6h). Cron hourly.
base=/tmp/claude-1000/-home-exedev/0a1445fc-4537-4d02-8a4a-bd6503e72f8c/scratchpad
[ -d "$base" ] || exit 0
for d in "$base"/*/; do
  d="${d%/}"; [ -d "$d" ] || continue
  case "$d" in "$base"/*) ;; *) continue ;; esac
  [ -n "$(find "$d" -newermt '-6 hours' -print -quit 2>/dev/null)" ] && continue
  [ "$(lsof +D "$d" 2>/dev/null | wc -l)" -gt 0 ] && continue
  echo "$(date) janitor: removing $d ($(du -sh "$d" | cut -f1))" >> /home/exedev/lazerproof/status/diskguard.log
  rm -rf -- "$d"
done
