#!/usr/bin/env python3
"""Commit into a shared-REPL client only those top-level blocks of FILE whose declared names are not yet
in the client's environment (for picking up additions to a header module, e.g. LoopsR, before the next
server restart). `syntax` blocks are skipped when present; `macro_rules` are always (re)committed.
usage: sim_commit_missing.py CLIENT FILE NAMEPREFIX"""
import os, re, sys, subprocess, tempfile
C, F, pre = sys.argv[1:4]
P = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
L = open(F).read().split('\n')
body_start = next(i for i, l in enumerate(L) if l.startswith('namespace '))
ns = L[body_start].split()[1]
blocks = []; cur = []
for l in L[body_start + 1:]:
    if re.match(r'^(/--|@\[|theorem |def |noncomputable def |syntax |macro_rules|macro |instance |end )', l) and not (cur and (cur[-1].startswith('/--') or cur[-1].startswith('@['))):
        if cur: blocks.append(cur)
        cur = [l]
    else: cur.append(l)
if cur: blocks.append(cur)
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable )?(?:theorem|def) ([\w.\']+)', re.M)
names = [(b, DECL.search('\n'.join(b))) for b in blocks]
chk = '\n'.join(f'#check @{ns}.{m.group(1)}' for b, m in names if m)
def req(name, text):
    t = tempfile.NamedTemporaryFile('w', suffix='.lean', delete=False); t.write(text); t.close()
    out = subprocess.run([os.path.join(P, 'scripts/req.sh'), C, name] + (['--commit'] if name.endswith('c') else []) + [t.name],
                         capture_output=True, text=True, env=dict(os.environ, LINES_MAX='100000')).stdout
    os.unlink(t.name); return out
import time
out = req(f'{pre}{int(time.time())}', chk)
missing = set(re.findall(r"Unknown (?:identifier|constant) `" + re.escape(ns) + r"\.([\w.\']+)`", out))
keep = [b for b, m in names if (m and m.group(1) in missing) or (not m and b[0].startswith('macro_rules'))]
text = '\n'.join(L[:body_start] if False else []) + 'set_option linter.unusedSimpArgs false\nnamespace ' + ns + '\n' + '\n'.join('\n'.join(b) for b in keep if not b[0].startswith('end ')) + '\nend ' + ns + '\n'
print('missing:', sorted(missing))
print(req(f'{pre}{int(time.time())}c', text)[-500:])
