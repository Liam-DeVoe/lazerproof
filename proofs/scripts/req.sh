#!/bin/bash
# req.sh CLIENT NAME [--commit] FILES... : submit FILES (imports stripped) as one request to the shared
# REPL client $PROOF_REPL/c_CLIENT and print its messages. --commit keeps the declarations for that client.
# Request names must be new within the client (the server processes each name once, in name order).
# Memory: every client keeps its committed environment (~50-500 MB for long chains). When done or switching
# work, release it: `touch $PROOF_REPL/c_CLIENT/drop` (the next request starts fresh from the header env).
# Clients idle for 30 min are dropped automatically (their --commit envs are lost: re-commit). At most 8 clients
# are served at once; if $C/waiting appears, drop one of your other clients (keep <= 2 per agent).
# Memory watchdog: above 4300 MB server RSS one running request is cancelled (its .out says "cancelled by the
# memory watchdog"): the longest-running one if it ran >= 10 s, else the newest; above 4750 MB all running ones.
# A client that is the culprit twice within 60 min gets its committed env dropped (file watchdog_dropped.*; the .out
# says "repeat offender"): re-commit with smaller goals. Log: $PROOF_REPL/watchdog.log.
# Commit chains survive server restarts (D41): every successful --commit request is stored in
# $C/committed/ and replayed automatically when your client is next served (server restart, 30-min idle drop);
# DO NOT re-run --commit requests after a restart (duplicates fail with "already declared"). Replay failures
# (e.g. a lemma now in the header) are skipped and listed in $C/replay.log. `touch $C/drop` discards the chain.
# Restarts happen only in the announced check_all windows (STATE.md Requests) or after a crash. check_all.sh stops
# and restarts the server itself; `repl_server.sh start` refuses while /tmp/osu-heavy/check_all.lock is held (D52).
R=${PROOF_REPL:-$HOME/lazerproof/data/wip/proof-repl}
C=$R/c_$1; name=$2; shift 2; c=""
mkdir -p "$C"
if [ -e "$C/$name.lean" ]; then echo "request name $name already used in $C"; exit 2; fi
if [ "$1" = "--commit" ]; then c="--commit"; shift; fi
{ [ -n "$c" ] && echo "--commit"; echo "open Aeneas Aeneas.Std Result"; for f in "$@"; do grep -v '^import' "$f"; done; } > "$C/$name.tmp_"
mv "$C/$name.tmp_" "$C/$name.lean"
for i in $(seq 1 12000); do [ -f "$C/$name.out" ] && break; [ "$i" = 10 ] && [ -f "$C/waiting" ] && cat "$C/waiting"; sleep 0.3; done
grep -v '^%%DONE' "$C/$name.out" | head -${LINES_MAX:-80}
