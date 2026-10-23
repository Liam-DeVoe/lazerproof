#!/bin/bash
# Build all refinement proofs (lake, -j1) and write the axiom audit of every `*_refines` theorem
# to proofs/audit.txt (consumed by scripts/proof_status.py). Run under tools/heavy (the caller does:
# tools/heavy proofs/scripts/check_all.sh).
# If some modules fail to build (typically another agent's uncommitted work in progress), the audit still runs on
# every module that does not depend on a failed one (exit code 3 = PARTIAL; the failed modules are printed, their
# theorems count as "stated (not in audit)"). Exit 1 = sorry / non-standard axioms / audit failure; 3 = PARTIAL;
# 4 = headline signature differs from scripts/headline_signature.txt or a `sorry` token exists (final audit m5/m11).
set -euo pipefail
cd "$(dirname "$0")/.."
# D52: never run beside the shared REPL (3.5-4 GB): stop it first (commit chains persist, D41), restart it at the end
# (also on failure), and hold a lock so that `repl_server.sh start` refuses meanwhile. CHECK_ALL_NO_RESTART=1 skips
# the restart.
mkdir -p /tmp/osu-heavy; LOCK=/tmp/osu-heavy/check_all.lock
if [ -e $LOCK ] && kill -0 "$(cat $LOCK 2>/dev/null)" 2>/dev/null; then echo "check_all: already running (pid $(cat $LOCK))"; exit 1; fi
echo $$ > $LOCK
restart_repl() {
  rm -f $LOCK
  if [ -z "${CHECK_ALL_NO_RESTART:-}" ]; then
    nohup scripts/repl_server.sh start > /tmp/osu-heavy/repl_restart.log 2>&1 &
    echo "check_all: shared REPL restart launched ($(date -u +%H:%M))"
  fi
}
trap restart_repl EXIT
if pgrep -f "lean --run scripts/Repl.lean" > /dev/null; then
  scripts/repl_server.sh stop
  for i in $(seq 1 120); do pgrep -f "lean --run scripts/Repl.lean" > /dev/null || break; sleep 2; done
  if pgrep -f "lean --run scripts/Repl.lean" > /dev/null; then echo "check_all: cannot stop the shared REPL; refusing"; exit 1; fi
  echo "check_all: shared REPL stopped ($(date -u +%H:%M))"
fi
export PATH=$HOME/.elan/bin:$PATH LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-1}
LOG=$(mktemp /tmp/osuproofs_build.XXXXXX)
FAILED=""
if ! flock /tmp/osu-heavy/lake-proofs.lock lake build OsuProofs > "$LOG" 2>&1; then
  FAILED=$(sed -n '/^Some required targets logged failures:/,/^error: build failed/p' "$LOG" | sed -n 's/^- //p')
  if [ -z "$FAILED" ]; then grep -v '^✔\|^⣿' "$LOG" | tail -40; rm -f "$LOG"; exit 1; fi
  grep -E "^error: [^ ]+\.lean" "$LOG" | head -20 || true
  echo "check_all: BUILD FAILED in: $(echo $FAILED)"
fi
# a module whose proofs use `sorry` is treated like a failed module (excluded from the audit with its dependents)
SORRY=$(grep "uses .sorry" "$LOG" | sed -nE 's/^warning: (OsuProofs\/[^:]+)\.lean:.*/\1/p' | tr / . | sort -u || true)
if [ -n "$SORRY" ]; then echo "check_all: SORRY in: $(echo $SORRY)"; FAILED=$(printf '%s\n%s\n' "$FAILED" "$SORRY" | grep -v '^$' | sort -u); fi
rm -f "$LOG"
# modules to audit: all root/Manual imports minus failed modules and everything that imports them
MODS=$(FAILED="$FAILED" python3 -I - <<'PY'
import os, re
fail = set(os.environ['FAILED'].split())
def deps(m):
    p = m.replace('.', '/') + '.lean'
    if not os.path.exists(p): return []
    return re.findall(r'^import (OsuProofs\.[\w.]+)', open(p).read(), re.M)
memo = {}
def bad(m, stack=()):
    if m in memo: return memo[m]
    r = m in fail or any(bad(d) for d in deps(m) if d not in stack)
    memo[m] = r; return r
top = deps('OsuProofs') + deps('OsuProofs.Manual')
ok = [m for m in dict.fromkeys(top) if not bad(m)]
excl = [m for m in dict.fromkeys(top) if bad(m)]
if excl: print('#EXCL ' + ' '.join(excl))
print('\n'.join(ok))
# theorems are collected from every module reachable from the audited imports (not only the direct ones: e.g.
# Post/GenRD*.lean are imported only through Post/Playable3 -> Post/GenMods)
seen, todo = set(), list(ok)
while todo:
    m = todo.pop()
    if m in seen: continue
    seen.add(m); todo += deps(m)
print('\n'.join('#FILE ' + m for m in sorted(seen - set(ok))))
PY
)
EXCL=$(echo "$MODS" | sed -n 's/^#EXCL //p'); TRANS=$(echo "$MODS" | sed -n 's/^#FILE //p')
MODS=$(echo "$MODS" | grep -v '^#EXCL\|^#FILE')
[ -n "$EXCL" ] && echo "check_all: not audited (depend on a failed module): $EXCL"
AUD=$(mktemp /tmp/osuproofs_audit.XXXXXX.lean)
{ if [ -z "$FAILED" ]; then echo "import OsuProofs"; else echo "$MODS" | sed 's/^/import /'; fi
  FILES=$(printf '%s\n%s\n' "$MODS" "$TRANS" | grep -v '^$' | grep -v Generated | sed -E 's/\./\//g; s/$/.lean/' | sort -u)
  # final-audit m11: the headline theorem's full signature (compared with scripts/headline_signature.txt below)
  HEAD=$(head -1 scripts/headline_theorem.txt 2>/dev/null)
  if [ -n "$HEAD" ] && grep -qE "^(@\[[^]]*\] *)?(protected +)?theorem $HEAD( |$)" $FILES; then
    echo 'set_option format.width 120'; echo '#eval IO.println "%%HEADLINE_BEGIN"'; echo "#check @OsuProofs.$HEAD"
    cat scripts/headline_defs.lean   # N1: hashes of the proof-local definitions behind the headline
    echo '#eval IO.println "%%HEADLINE_END"'; fi
  grep -hoE '^(@\[[^]]*\] *)?(protected +)?theorem [A-Za-z0-9_.]+_refines(_[A-Za-z0-9_]+)?\b' $FILES \
    | sed -E 's/^.*theorem /#print axioms OsuProofs./' | sort -u
  # alias theorems (scripts/refines_aliases.txt) that are defined in an audited module
  grep -v '^#' scripts/refines_aliases.txt | awk 'NF {print $2}' | sort -u | while read -r t; do
    grep -qE "^(@\[[^]]*\] *)?(protected +)?theorem $t( |$)" $FILES && echo "#print axioms OsuProofs.$t"; done
  # discharge lemmas of named hypothesis Props (`theorem t .. : X :=` on one line), for proof_status's DISCHARGED
  grep -hoE '^theorem [A-Za-z0-9_.]+ .*: *[A-Za-z_][A-Za-z0-9_.]* *(:=|where)' $FILES | awk '{print "#print axioms OsuProofs." $2}' | sort -u; } > "$AUD"
export OSU_HEADLINE="$HEAD"
if ! lake env lean "$AUD" > audit.txt 2>&1; then
  # a `theorem X_refines` outside namespace OsuProofs gives "Unknown constant" for its #print line: not fatal, it just
  # stays unaudited (listed); any other error is fatal
  if grep "error" audit.txt | grep -vq "Unknown constant"; then grep "error" audit.txt | head -20; rm -f "$AUD"; exit 1; fi
  echo "check_all: not audited (not in namespace OsuProofs): $(grep -o "Unknown constant \`[^\`]*\`" audit.txt | tr '\n' ' ')"
fi
rm -f "$AUD"
n=$(grep -c "depends on axioms\|does not depend on any axioms" audit.txt || true)
# `#print axioms` wraps long lines: join each entry before checking its axiom list
bad=$(grep -v 'error' audit.txt | tr '\n' ' ' | tr -s ' ' | sed "s/'OsuProofs\./\n'OsuProofs./g" | grep "depends on axioms" \
  | grep -vE "depends on axioms: \[((propext|Classical\.choice|Quot\.sound)(, )?)+\] *$" || true)
echo "check_all: $n theorems audited"
# final-audit m11: no hypothesis may be added to / changed in the headline theorem silently
HEADRC=0
if [ -n "$HEAD" ]; then
  sed -n '/^%%HEADLINE_BEGIN/,/^%%HEADLINE_END/p' audit.txt | grep -v '^%%HEADLINE' > /tmp/osu-heavy/headline_sig.txt || true
  if [ ! -s /tmp/osu-heavy/headline_sig.txt ]; then echo "check_all: HEADLINE $HEAD not audited (not defined / module failed)"; HEADRC=1
  elif [ ! -f scripts/headline_signature.txt ]; then cp /tmp/osu-heavy/headline_sig.txt scripts/headline_signature.txt
    echo "check_all: HEADLINE signature of $HEAD recorded in scripts/headline_signature.txt (commit it)"
  elif ! cmp -s /tmp/osu-heavy/headline_sig.txt scripts/headline_signature.txt; then
    echo "check_all: HEADLINE SIGNATURE CHANGED ($HEAD) vs the committed allowlist scripts/headline_signature.txt:"
    { diff scripts/headline_signature.txt /tmp/osu-heavy/headline_sig.txt || true; } | head -40; HEADRC=1
  else echo "check_all: headline $HEAD signature = allowlist"; fi
fi
# final-audit m5: no `sorry` token anywhere in proofs/OsuProofs (comments excluded), even in an untaken branch
SORRYTOK=$(python3 -I - <<'PY'
import glob, re
for f in sorted(glob.glob('OsuProofs/**/*.lean', recursive=True)):
    t = open(f).read()
    t = re.sub(r'/-.*?-/', lambda m: re.sub(r'[^\n]', ' ', m.group(0)), t, flags=re.S)
    for i, l in enumerate(t.split('\n'), 1):
        if re.search(r'(?<![\w.])sorry(?![\w])', l.split('--')[0]): print(f'{f}:{i}')
PY
)
if [ -n "$SORRYTOK" ]; then echo "check_all: SORRY TOKEN in: $(echo $SORRYTOK)"; HEADRC=1; fi
if [ -n "$bad" ]; then echo "NON-STANDARD AXIOMS:"; echo "$bad"; exit 1; fi
if [ -n "$FAILED" ]; then echo "check_all: PARTIAL (failed: $(echo $FAILED))"; exit 3; fi
if [ "$HEADRC" != 0 ]; then echo "check_all: FAILED (headline signature / sorry token check, see above)"; exit 4; fi
