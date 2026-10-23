#!/usr/bin/env python3
"""Keep the blocks (separated by blank lines) of a Lean snippet file that elaborate in the REPL.
usage: check_blocks.py IN OUT PRELUDE   (PRELUDE: lines prepended to every request, e.g. opens)"""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from repl_client import submit, errors
inp, outp, prelude = sys.argv[1], sys.argv[2], open(sys.argv[3]).read()
client = os.environ.get('REPL_DIR', os.path.expanduser('~') + '/repl_c_auto')
blocks = [b for b in open(inp).read().split('\n\n') if b.strip()]
todo = list(blocks); kept = []
def run(bs):
    text = prelude + '\n' + '\n\n'.join(bs) + '\n'
    out = submit(text, client)
    errs = errors(out)
    starts = []; line = prelude.count('\n') + 2
    for b in bs:
        starts.append(line); line += b.count('\n') + 2
    bad = set()
    for (ln, _, _) in errs:
        for k in range(len(bs) - 1, -1, -1):
            if starts[k] <= ln: bad.add(k); break
    return bad
for it in range(30):
    if not todo: break
    bad = run(todo)
    good = [b for k, b in enumerate(todo) if k not in bad]
    if not good: break
    # good blocks may depend on bad ones: recheck alone until clean
    while good:
        b2 = run(good)
        if not b2: break
        good = [b for k, b in enumerate(good) if k not in b2]
    if not good: break
    while good:
        out = submit(prelude + '\n' + '\n\n'.join(good) + '\n', client, commit=True)
        errs = errors(out)
        if not errs: break
        starts = []; line = prelude.count('\n') + 3  # +1 for the --commit line
        for b in good:
            starts.append(line); line += b.count('\n') + 2
        b3 = set()
        for (ln, _, _) in errs:
            for k in range(len(good) - 1, -1, -1):
                if starts[k] <= ln: b3.add(k); break
        if not b3: good = []; break
        good = [b for k, b in enumerate(good) if k not in b3]
    kept += good
    todo = [b for b in todo if b not in good]
    print(f'iter {it}: kept {len(good)}, {len(todo)} left', file=sys.stderr)
open(outp, 'w').write('\n\n'.join(kept) + '\n')
open(outp + '.failed', 'w').write('\n\n'.join(todo) + '\n')
print(f'kept {len(kept)}/{len(blocks)}')
