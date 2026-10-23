#!/usr/bin/env python3
"""Transparent result cache for `oracle batch` (invoked by oracle/oracle.sh).

Each batch job line is keyed by: oracle build fingerprint (hash of the oracle + lazer + framework dlls),
the batch options, the job line verbatim (paths + mods JSON), and the content hashes of the beatmap and
replay files. Hits are replayed from data/oracle-cache (zlib-compressed JSON lines); misses are run through
the real oracle in one batch, in order, and stored unless they are error lines. Output order and content are
identical to an uncached run. Set ORACLE_NOCACHE=1 to bypass.
"""
import hashlib, os, subprocess, sys, tempfile, zlib, json

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.path.join(ROOT, "oracle", "bin", "Release", "net10.0")
CACHE = os.path.join(ROOT, "data", "oracle-cache")
CACHE_MAX_BYTES = int(os.environ.get("ORACLE_CACHE_MAX_BYTES", str(400 << 20)))
FINGERPRINT_DLLS = ["oracle.dll", "osu.Game.dll", "osu.Game.Rulesets.Osu.dll", "osu.Framework.dll"]


def file_hash(path, memo={}):
    st = os.stat(path)
    k = (path, st.st_size, st.st_mtime_ns)
    if k not in memo:
        h = hashlib.sha256()
        with open(path, "rb") as f:
            for chunk in iter(lambda: f.read(1 << 20), b""):
                h.update(chunk)
        memo[k] = h.hexdigest()
    return memo[k]


def fingerprint():
    return hashlib.sha256("".join(file_hash(os.path.join(BIN, d)) for d in FINGERPRINT_DLLS).encode()).hexdigest()


def job_key(fp, opts, line):
    parts = line.split(None, 2)
    contents = []
    for p in parts[:2]:
        try:
            contents.append(file_hash(p))
        except OSError:
            return None  # missing file: let the oracle report the error, don't cache
    return hashlib.sha256("\0".join([fp, " ".join(opts), line] + contents).encode()).hexdigest()


def nondeterministic(rec):
    """True if the job used a mod whose RNG seed lazer picks at random (Random / Target Practice without a seed)."""
    mods = (rec.get("input") or {}).get("mods") or []
    return any(m.get("acronym") in ("RD", "TP") and (m.get("settings") or {}).get("seed") is None for m in mods)


def cache_path(k):
    return os.path.join(CACHE, k[:2], k + ".z")


def evict():
    files = []
    for d, _, fs in os.walk(CACHE):
        for f in fs:
            p = os.path.join(d, f)
            st = os.stat(p)
            files.append((st.st_atime, st.st_size, p))
    total = sum(s for _, s, _ in files)
    for _, s, p in sorted(files):
        if total <= CACHE_MAX_BYTES:
            break
        os.remove(p)
        total -= s


def main(argv):
    real = os.path.join(BIN, "oracle")
    list_file, opts, i = None, [], 1
    while i < len(argv):
        if argv[i] == "--list":
            list_file = argv[i + 1]; i += 2
        else:
            opts.append(argv[i]); i += 1
    lines = [l.rstrip("\n") for l in open(list_file)]
    jobs = [l for l in lines if l.strip() and not l.lstrip().startswith("#")]
    fp = fingerprint()
    keys = [job_key(fp, opts, l) for l in jobs]
    cached = {}
    for k in keys:
        if k and os.path.exists(cache_path(k)):
            with open(cache_path(k), "rb") as f:
                cached[k] = zlib.decompress(f.read()).decode()
    misses = [l for l, k in zip(jobs, keys) if k not in cached]
    proc = None
    if misses:
        tmp = tempfile.NamedTemporaryFile("w", delete=False, suffix=".list", dir=os.environ.get("TMPDIR"))
        tmp.write("\n".join(misses) + "\n"); tmp.close()
        proc = subprocess.Popen([real, "batch", "--list", tmp.name] + opts, stdout=subprocess.PIPE, text=True)
    any_error = False
    for l, k in zip(jobs, keys):
        if k in cached:
            out = cached[k]
        else:
            out = proc.stdout.readline().rstrip("\n")
            is_error = False
            try:
                rec = json.loads(out)
                is_error = "error" in rec or nondeterministic(rec)
            except ValueError:
                is_error = True
            if k and not is_error:
                os.makedirs(os.path.dirname(cache_path(k)), exist_ok=True)
                tmpc = cache_path(k) + ".tmp%d" % os.getpid()
                with open(tmpc, "wb") as f:
                    f.write(zlib.compress(out.encode(), 6))
                os.replace(tmpc, cache_path(k))
        try:
            any_error |= "error" in json.loads(out)
        except ValueError:
            any_error = True
        sys.stdout.write(out + "\n"); sys.stdout.flush()
    rc = 0
    if proc:
        proc.stdout.close(); rc = proc.wait(); os.unlink(tmp.name)
    if misses:
        evict()
    sys.exit(1 if (any_error or rc) else 0)


if __name__ == "__main__":
    main(sys.argv[1:])
