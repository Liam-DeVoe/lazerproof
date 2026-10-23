#!/bin/bash
# auto_setup.sh CLIENT_DIR WORK_DIR: prepare a REPL client for scripts/auto_prove.py: commit Auto/Abs.lean,
# the generated AbsTo instances and the constant lemmas (checked block by block).
set -e
C=$1; W=$2; mkdir -p "$C" "$W"; cd "$(dirname "$0")/.."
cp scripts/auto_prelude.lean $W/prelude.lean
python3 -I - "$C" <<'PY'
import sys; sys.path.insert(0,'scripts'); from repl_client import submit, errors
src='\n'.join(l for l in open('OsuProofs/Auto/Abs.lean') if not l.startswith('import'))
out=submit(src, sys.argv[1], commit=True); print('Abs:', 'ok' if not errors(out) else out[:2000])
PY
python3 -I scripts/gen_abs.py > $W/abs_gen.lean
REPL_DIR=$C python3 -I scripts/check_blocks.py $W/abs_gen.lean $W/abs_ok.lean $W/prelude.lean
python3 -I scripts/gen_consts.py > $W/consts_gen.lean
REPL_DIR=$C python3 -I scripts/check_blocks.py $W/consts_gen.lean $W/consts_ok.lean $W/prelude.lean
python3 -I scripts/gen_steps.py > $W/steps_gen.lean
REPL_DIR=$C python3 -I scripts/check_blocks.py $W/steps_gen.lean $W/steps_ok.lean $W/prelude.lean
# previously generated proofs (so callers can use their @[step] lemmas)
python3 -I - "$C" <<'PY'
import sys, re; sys.path.insert(0,'scripts'); from repl_client import submit, errors
src = open('OsuProofs/Auto/Gen.lean').read()
body = src.split('open OsuImpl\n', 1)[1].rsplit('end OsuProofs', 1)[0]
pre = open('scripts/auto_prelude.lean').read()
out = submit(pre + body, sys.argv[1], commit=True); print('Gen:', 'ok' if not errors(out) else out[:1500])
PY
