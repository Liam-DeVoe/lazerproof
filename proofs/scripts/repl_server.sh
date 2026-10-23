#!/bin/bash
# Shared proof REPL server (one Lean process, ~2.3 GB private, serves several agents in parallel).
#   repl_server.sh start [HEADER_MODULES...]   (default header: OsuProofs.Manual) -- idempotent
#   repl_server.sh stop
# Root dir: $PROOF_REPL (default ~/lazerproof/data/wip/proof-repl). Each agent uses its own client dir
# $PROOF_REPL/c_<agent>/ (create it; picked up within 1 s) and submits requests with scripts/req.sh.
# Runs in a systemd scope capped at 5000M (anon grows with each client's --commit chain: drop idle clients, see req.sh).
R=${PROOF_REPL:-$HOME/lazerproof/data/wip/proof-repl}
cd "$(dirname "$0")/.."
case "$1" in
  start)
    shift
    # never start while check_all is running (it stops the server for memory; D52)
    L=/tmp/osu-heavy/check_all.lock
    if [ -e $L ] && kill -0 "$(cat $L 2>/dev/null)" 2>/dev/null; then
      echo "check_all is running (pid $(cat $L)); it restarts the server when done. Not starting."; exit 3; fi
    if pgrep -f "lean --run scripts/Repl.lean $R\$" >/dev/null; then echo "running ($R)"; exit 0; fi
    mkdir -p "$R"; [ -e "$R/stop" ] && mv -f "$R/stop" "$R/stop.old"; [ -e "$R/ready" ] && mv -f "$R/ready" "$R/ready.old"
    [ -s "$R/server.log" ] && mv -f "$R/server.log" "$R/server.log.$(date +%m%d-%H%M%S)"
    ls -t "$R"/server.log.* 2>/dev/null | tail -n +11 | while read -r f; do rm -f -- "$f"; done
    if [ $# -gt 0 ]; then printf '%s\n' "$@" > "$R/header"; elif [ ! -f "$R/header" ]; then echo OsuProofs.Manual > "$R/header"; fi
    export PATH=$HOME/.elan/bin:$PATH LEAN_NUM_THREADS=1
    nohup systemd-run --user --scope -q -p MemoryMax=5000M -p MemorySwapMax=0 \
      lake env lean --run scripts/Repl.lean "$R" > "$R/server.log" 2>&1 &
    for i in $(seq 1 900); do [ -f "$R/ready" ] && break; sleep 1; done; cat "$R/ready";;
  stop) touch "$R/stop";;
  *) echo "usage: $0 start [MODULES..] | stop"; exit 2;;
esac
