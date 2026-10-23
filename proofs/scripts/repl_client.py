"""Tiny client for the file-driven REPL (scripts/Repl.lean): submit a request, wait, parse errors.
Env: REPL_DIR = client directory (default: $REPL_ROOT/c_auto)."""
import os, re, time, uuid
def submit(text, client_dir, commit=False, timeout=900, name=None):
    os.makedirs(client_dir, exist_ok=True)
    name = name or ('r' + time.strftime('%H%M%S') + uuid.uuid4().hex[:6])
    src = ('--commit\n' if commit else '') + text
    tmp = os.path.join(client_dir, name + '.tmp_')
    open(tmp, 'w').write(src); os.rename(tmp, os.path.join(client_dir, name + '.lean'))
    out = os.path.join(client_dir, name + '.out')
    t0 = time.time()
    while not os.path.exists(out):
        if time.time() - t0 > timeout: return None
        time.sleep(0.3)
    return open(out).read()
def errors(out, fname_prefix=None):
    """list of (line, col, message-first-line) for errors"""
    res = []
    for m in re.finditer(r'^[\w.]+\.lean:(\d+):(\d+)(?:-\d+:\d+)?: error[^:]*: (.*)$', out, re.M):
        res.append((int(m.group(1)), int(m.group(2)), m.group(3)))
    return res
