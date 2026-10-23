#!/usr/bin/env python3
"""Lazer-score corpus downloader via osu! API v2 (stdlib only, resumable).

Polls the global `GET /api/v2/scores?ruleset=osu` feed (passed scores, newest ~1000), keeps lazer scores
(legacy_score_id null, has_replay) whose build is gameplay-equivalent to the pinned lazer (docs/lazer-builds.md),
downloads the replay (`/api/v2/scores/{id}/download`, lazer .osr) and the beatmap (`https://osu.ppy.sh/osu/{id}`),
and verifies md5(.osu) == replay header beatmap md5.

Score build_id values are per-platform build rows that the changelog API does not expose, so the build -> version
map is LEARNED from the `client_version` stored in the lazer .osr (LegacyReplaySoloScoreInfo.ClientVersion):
for an unknown build_id up to --probes replays are downloaded; the build is then accepted or rejected.

Layout (all under data/, gitignored):
  index_v2.sqlite   tables: scores (full server JSON + status), builds (build_id -> client_version), beatmaps, meta
  replays_v2/{score_id}.osr
  beatmaps/{beatmap_id}.osu   (shared with fetch_v1; if an existing file has another md5, {beatmap_id}.{md5[:8]}.osu)

Usage:
  python3 -I difftest/fetch_v2.py crawl --max 15000 [--min-free-gb 4] [--per-beatmap 2] [--per-user 10]
  python3 -I difftest/fetch_v2.py stats                 # counts, builds, mod mix
  python3 -I difftest/fetch_v2.py export --out F.jsonl  # downloaded+verified scores (server JSON + paths)
Credentials: ~/.osu_credentials OSU_API_V2_CLIENT_ID / OSU_API_V2_CLIENT_SECRET (never printed).
Log line "CRAWL V2 DONE" (target reached) / "CRAWL V2 STOP disk" (low disk) tell the watchdog not to restart.
"""
import argparse, collections, hashlib, json, os, shutil, sqlite3, sys, time, urllib.error, urllib.parse, urllib.request

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
DATA = os.path.join(ROOT, "data")
DB = os.path.join(DATA, "index_v2.sqlite")
REPLAYS = os.path.join(DATA, "replays_v2")
BEATMAPS = os.path.join(DATA, "beatmaps")
UA = "lazerproof-research/0.1 (difftest; contact via osu! API app)"

# docs/lazer-builds.md. A = gameplay-identical to the pinned 2026.1005.0-lazer; B = identical except for listed
# changes (beatmap position clamp etc.), collected under a quota and analysed separately.
EQUIV_A = {"2026.918.0-tachyon", "2026.920.0-lazer", "2026.921.0-lazer", "2026.1005.0-lazer"}
EQUIV_B = {"2026.1001.0-tachyon", "2026.1004.0-tachyon", "2026.1005.1-tachyon", "2026.1013.0-tachyon"}


def log(*a):
    print(time.strftime("%Y-%m-%d %H:%M:%S"), *a, flush=True)


def load_creds():
    env = {}
    with open(os.path.expanduser("~/.osu_credentials")) as f:
        for line in f:
            line = line.strip()
            if "=" in line and not line.startswith("#"):
                k, v = line.split("=", 1)
                env[k.strip().removeprefix("export ").strip()] = v.strip().strip('"').strip("'")
    return env["OSU_API_V2_CLIENT_ID"], env["OSU_API_V2_CLIENT_SECRET"]


class Api:
    def __init__(self, interval=1.1):
        self.interval = interval
        self.last = 0.0
        self.token = None
        self.token_exp = 0.0
        self.backoff = 0.0
        self.last_dl = 0.0
        self.dl_interval = 6.5

    def _pace(self):
        d = self.last + self.interval - time.time()
        if d > 0:
            time.sleep(d)
        self.last = time.time()

    def _token(self):
        if self.token and time.time() < self.token_exp - 300:
            return self.token
        cid, sec = load_creds()
        body = urllib.parse.urlencode({"client_id": cid, "client_secret": sec, "grant_type": "client_credentials",
                                       "scope": "public"}).encode()
        self._pace()
        r = urllib.request.urlopen(urllib.request.Request("https://osu.ppy.sh/oauth/token", body,
                                                          headers={"User-Agent": UA}), timeout=60)
        d = json.load(r)
        self.token = d["access_token"]
        self.token_exp = time.time() + float(d.get("expires_in", 3600))
        log("token refreshed")
        return self.token

    def get(self, url, auth=True, accept="application/json", tries=8):
        """Returns (status, bytes). 404 -> (404, b''). Retries 429/5xx/network with exponential backoff."""
        for k in range(tries):
            hdr = {"User-Agent": UA, "Accept": accept}
            if auth:
                hdr["Authorization"] = "Bearer " + self._token()
                hdr["x-api-version"] = "20240529"
            self._pace()
            try:
                r = urllib.request.urlopen(urllib.request.Request(url, headers=hdr), timeout=120)
                b = r.read()
                self.backoff = 0.0
                return r.status, b
            except urllib.error.HTTPError as e:
                if e.code in (404, 403, 410, 422):
                    return e.code, b""
                if e.code == 401 and auth:
                    self.token = None
                wait = int(e.headers.get("Retry-After", "0") or 0) if e.code == 429 else 0
                err = "HTTP %d" % e.code
            except Exception as e:  # network
                wait, err = 0, repr(e)[:120]
            self.backoff = min(600.0, max(5.0, self.backoff * 2))
            w = max(wait, self.backoff)
            log("request failed (%s) %s; sleeping %.0fs" % (err, url.split("?")[0], w))
            time.sleep(w)
        return -1, b""


SCHEMA = """
create table if not exists scores(
  id integer primary key, beatmap_id int, user_id int, build_id int, ended_at text, modkey text,
  json text not null,               -- full server score JSON (feed or /scores/{id})
  status text not null default 'pending',  -- pending | ok | md5_mismatch | no_replay | not_lazer | build_rejected | beatmap_missing | error
  equiv text,                       -- A | B | null (decided from client_version)
  client_version text, osr_version int, osr_beatmap_md5 text, replay_bytes int, beatmap_path text,
  probe int default 0, err text, queued_at real, fetched_at real);
create index if not exists scores_status on scores(status);
create index if not exists scores_bm on scores(beatmap_id);
create index if not exists scores_user on scores(user_id);
create table if not exists builds(build_id integer primary key, client_version text, equiv text, n_seen int default 0,
  n_probe int default 0);
create table if not exists beatmaps(beatmap_id integer primary key, md5 text, path text, fetched_at real);
create table if not exists meta(k text primary key, v text);
"""


def opendb():
    os.makedirs(REPLAYS, exist_ok=True)
    os.makedirs(BEATMAPS, exist_ok=True)
    db = sqlite3.connect(DB, timeout=300)
    db.execute("pragma journal_mode=WAL")  # readers (reports) never block the crawler's commits
    db.executescript(SCHEMA)
    return db


def modkey(mods):
    return "".join(sorted(m["acronym"] for m in mods)) or "NM"


PLATFORMS = ("-windows", "-macos", "-linux", "-android", "-ios")


def base_version(ver):
    """'2026.1005.0-lazer-windows' -> '2026.1005.0-lazer' (score build rows are per platform; same source tag)."""
    for p in PLATFORMS:
        if ver.endswith(p):
            return ver[:-len(p)]
    return ver


def classify(ver):
    ver = base_version(ver)
    if ver in EQUIV_A:
        return "A"
    if ver in EQUIV_B:
        return "B"
    return "X"


def osr_info(b):
    """Parse a lazer .osr: (version, beatmap_md5, lazer_json dict or None). Raises on malformed input."""
    import lzma, struct
    i = 0

    def uleb():
        nonlocal i
        r = s = 0
        while True:
            x = b[i]; i += 1
            r |= (x & 0x7F) << s; s += 7
            if not x & 0x80:
                return r

    def sstr():
        nonlocal i
        t = b[i]; i += 1
        if t == 0:
            return None
        n = uleb(); v = b[i:i + n].decode("utf-8"); i += n
        return v

    mode = b[0]; i = 1
    version, = struct.unpack_from("<i", b, i); i += 4
    md5 = sstr(); sstr(); sstr()
    i += 12 + 4 + 2 + 1 + 4
    sstr()
    i += 8
    n, = struct.unpack_from("<i", b, i); i += 4 + n
    i += 8  # online id
    js = None
    if version >= 30000001 and i + 4 <= len(b):
        n, = struct.unpack_from("<i", b, i); i += 4
        js = json.loads(lzma.decompress(b[i:i + n], format=lzma.FORMAT_ALONE).decode("utf-8"))
    if mode != 0:
        raise ValueError("mode %d" % mode)
    return version, md5, js


def free_gb():
    return shutil.disk_usage(DATA).free / 2**30  # GiB, as df -h


def poll_feed(api, db, a):
    st, b = api.get("https://osu.ppy.sh/api/v2/scores?ruleset=osu")
    if st != 200:
        log("feed failed", st)
        return 0
    scores = json.loads(b)["scores"]
    builds = {r[0]: r[1] for r in db.execute("select build_id, equiv from builds")}
    added = 0
    now = time.time()
    for s in scores:
        bid = s.get("build_id")
        if s.get("ruleset_id") != 0 or not s.get("has_replay") or s.get("legacy_score_id") is not None or bid is None:
            continue
        db.execute("insert or ignore into builds(build_id) values(?)", (bid,))
        db.execute("update builds set n_seen = n_seen + 1 where build_id=?", (bid,))
        eq = builds.get(bid)
        if eq == "X":
            continue
        if db.execute("select 1 from scores where id=?", (s["id"],)).fetchone():
            continue
        nbm = db.execute("select count(*) from scores where beatmap_id=? and status in ('pending','ok')",
                         (s["beatmap_id"],)).fetchone()[0]
        nus = db.execute("select count(*) from scores where user_id=? and status in ('pending','ok')",
                         (s["user_id"],)).fetchone()[0]
        if nbm >= a.per_beatmap or nus >= a.per_user:
            continue
        db.execute("insert into scores(id,beatmap_id,user_id,build_id,ended_at,modkey,json,queued_at) values(?,?,?,?,?,?,?,?)",
                   (s["id"], s["beatmap_id"], s["user_id"], bid, s.get("ended_at"), modkey(s.get("mods", [])),
                    json.dumps(s, sort_keys=True), now))
        added += 1
    # drop stale pending rows (keep queue bounded)
    db.execute("delete from scores where status='pending' and queued_at < ?", (now - 6 * 3600,))
    db.commit()
    return added


def pick_next(db, a):
    """Pending score maximising diversity: least-downloaded mod combination first, then builds still needing probes."""
    known = {r[0]: r[1] for r in db.execute("select build_id, equiv from builds")}
    nprobe = {r[0]: r[1] for r in db.execute("select build_id, n_probe from builds")}
    okmods = collections.Counter(dict(db.execute("select modkey, count(*) from scores where status='ok' group by modkey")))
    nok = db.execute("select count(*) from scores where status='ok'").fetchone()[0]
    nb = db.execute("select count(*) from scores where status='ok' and equiv='B'").fetchone()[0]
    best = None
    for sid, bid, mk in db.execute("select id, build_id, modkey from scores where status='pending' order by id desc limit 5000"):
        eq = known.get(bid)
        if eq == "X":
            continue
        if eq is None:
            if nprobe.get(bid, 0) >= 3 * a.probes:
                continue  # probes keep failing (no replay etc.): give up on this build
            return sid, True
        if eq == "B" and nb > a.b_quota * max(nok, 1):
            continue
        key = okmods[mk]
        if best is None or key < best[0]:
            best = (key, sid)
    return (best[1], False) if best else (None, False)


def ensure_beatmap(api, db, bmid, want_md5):
    """Return path of a .osu for beatmap bmid whose md5 == want_md5, or (None, reason)."""
    cands = [os.path.join(BEATMAPS, "%d.osu" % bmid), os.path.join(BEATMAPS, "%d.%s.osu" % (bmid, want_md5[:8]))]
    for p in cands:
        if os.path.exists(p) and hashlib.md5(open(p, "rb").read()).hexdigest() == want_md5:
            return p, None
    st, b = api.get("https://osu.ppy.sh/osu/%d" % bmid, auth=False, accept="*/*")
    if st != 200 or not b:
        return None, "beatmap http %s" % st
    md5 = hashlib.md5(b).hexdigest()
    path = cands[0] if not os.path.exists(cands[0]) else os.path.join(BEATMAPS, "%d.%s.osu" % (bmid, md5[:8]))
    if not os.path.exists(path):
        with open(path + ".part", "wb") as f:
            f.write(b)
        os.replace(path + ".part", path)
    db.execute("insert or replace into beatmaps(beatmap_id, md5, path, fetched_at) values(?,?,?,?)",
               (bmid, md5, os.path.relpath(path, ROOT), time.time()))
    if md5 != want_md5:
        return None, "md5 mismatch (online %s, replay %s)" % (md5, want_md5)
    return path, None


def fetch_one(api, db, sid, probe):
    row = db.execute("select beatmap_id, build_id from scores where id=?", (sid,)).fetchone()
    bmid, bid = row
    if probe:
        db.execute("update builds set n_probe = n_probe + 1 where build_id=?", (bid,))
    path = os.path.join(REPLAYS, "%d.osr" % sid)
    if os.path.exists(path):
        b = open(path, "rb").read()
    else:
        # replay downloads have their own, stricter limit (observed: ~10 back-to-back, then 429 for ~75 s)
        d = api.last_dl + api.dl_interval - time.time()
        if d > 0:
            time.sleep(d)
        api.last_dl = time.time()
        st, b = api.get("https://osu.ppy.sh/api/v2/scores/%d/download" % sid, accept="application/octet-stream")
        if st != 200 or not b:
            db.execute("update scores set status=?, err=?, fetched_at=? where id=?",
                       ("no_replay" if st in (404, 403, 410, 422) else "error", "replay http %s" % st, time.time(), sid))
            return "replay http %s" % st
    try:
        ver, md5, js = osr_info(b)
    except Exception as e:
        db.execute("update scores set status='error', err=? where id=?", ("osr parse: %r" % e, sid))
        return "osr parse"
    cv = (js or {}).get("client_version") or ""
    eq = classify(cv) if ver >= 30000000 else "X"
    db.execute("update scores set osr_version=?, osr_beatmap_md5=?, client_version=?, equiv=?, replay_bytes=?, fetched_at=? where id=?",
               (ver, md5, cv, eq, len(b), time.time(), sid))
    # learn build -> version (a build row is one client binary; versions should never disagree)
    prev = db.execute("select client_version from builds where build_id=?", (bid,)).fetchone()
    if prev and prev[0] and prev[0] != cv:
        log("WARNING build %d has client_version %r and %r" % (bid, prev[0], cv))
    elif cv:
        db.execute("update builds set client_version=?, equiv=? where build_id=?", (cv, eq, bid))
    if ver < 30000000:
        db.execute("update scores set status='not_lazer' where id=?", (sid,))
        return "not lazer (v%d)" % ver
    if eq == "X":
        db.execute("update scores set status='build_rejected' where id=?", (sid,))
        if os.path.exists(path):
            os.remove(path)
        return "build %d = %r rejected" % (bid, cv)
    bpath, why = ensure_beatmap(api, db, bmid, md5)
    if bpath is None:
        db.execute("update scores set status=?, err=? where id=?",
                   ("md5_mismatch" if "md5" in why else "beatmap_missing", why, sid))
        return why
    if not os.path.exists(path):
        with open(path + ".part", "wb") as f:
            f.write(b)
        os.replace(path + ".part", path)
    db.execute("update scores set status='ok', beatmap_path=? where id=?", (os.path.relpath(bpath, ROOT), sid))
    return "ok %s %s %dB" % (cv, db.execute("select modkey from scores where id=?", (sid,)).fetchone()[0], len(b))


def crawl(a):
    db = opendb()
    api = Api(a.interval)
    api.dl_interval = a.dl_interval
    last_poll = 0.0
    log("crawl start max=%d min_free_gb=%.1f" % (a.max, a.min_free_gb))
    while True:
        nok = db.execute("select count(*) from scores where status='ok'").fetchone()[0]
        if nok >= a.max:
            log("CRAWL V2 DONE ok=%d" % nok)
            return
        if free_gb() < a.min_free_gb:
            log("CRAWL V2 STOP disk free=%.2fGB < %.1fGB (ok=%d)" % (free_gb(), a.min_free_gb, nok))
            return
        sid, probe = pick_next(db, a)
        if sid is None or time.time() - last_poll > a.poll:
            n = poll_feed(api, db, a)
            last_poll = time.time()
            npend = db.execute("select count(*) from scores where status='pending'").fetchone()[0]
            log("feed: +%d candidates, pending=%d ok=%d" % (n, npend, nok))
            if sid is None:
                time.sleep(min(a.poll, 30))
                continue
        try:
            msg = fetch_one(api, db, sid, probe)
        except Exception as e:  # never die on one score
            db.execute("update scores set status='error', err=? where id=?", (repr(e)[:300], sid))
            msg = "exception %r" % e
        db.commit()
        log("[%d/%d] %d%s: %s" % (nok, a.max, sid, " (probe)" if probe else "", msg))


def stats(a):
    db = opendb()
    print("status:", dict(db.execute("select status, count(*) from scores group by status")))
    print("equiv (ok):", dict(db.execute("select equiv, count(*) from scores where status='ok' group by equiv")))
    print("builds:")
    for r in db.execute("select build_id, client_version, equiv, n_seen, n_probe from builds order by build_id"):
        print("  ", r)
    mods = collections.Counter()
    single = collections.Counter()
    settings = collections.Counter()
    for (js,) in db.execute("select json from scores where status='ok'"):
        ms = json.loads(js).get("mods", [])
        mods[modkey(ms)] += 1
        for m in ms:
            single[m["acronym"]] += 1
            if m.get("settings"):
                settings[m["acronym"] + ":" + ",".join(sorted(m["settings"]))] += 1
    print("mod combos (ok):", mods.most_common(40))
    print("single mods (ok):", single.most_common())
    print("mods with settings (ok):", settings.most_common(30))
    tot = db.execute("select sum(replay_bytes) from scores where status='ok'").fetchone()[0] or 0
    print("replay bytes: %.1f MB" % (tot / 1e6), "free: %.2f GB" % free_gb())


def export(a):
    db = opendb()
    with open(a.out, "w") as f:
        for sid, js, bp, eq, cv in db.execute(
                "select id, json, beatmap_path, equiv, client_version from scores where status='ok' order by id"):
            f.write(json.dumps({"id": sid, "beatmap": bp, "replay": "data/replays_v2/%d.osr" % sid, "equiv": eq,
                                "client_version": cv, "score": json.loads(js)}) + "\n")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("crawl")
    c.add_argument("--max", type=int, default=15000)
    c.add_argument("--min-free-gb", type=float, default=4.0)
    c.add_argument("--per-beatmap", type=int, default=2)
    c.add_argument("--per-user", type=int, default=10)
    c.add_argument("--probes", type=int, default=2, help="replays downloaded per unknown build_id")
    c.add_argument("--b-quota", type=float, default=0.10, help="max share of 'B' (conditionally equivalent) builds")
    c.add_argument("--poll", type=float, default=120.0, help="seconds between feed polls")
    c.add_argument("--interval", type=float, default=1.1, help="min seconds between HTTP requests")
    c.add_argument("--dl-interval", type=float, default=6.5, help="min seconds between replay downloads")
    sub.add_parser("stats")
    e = sub.add_parser("export")
    e.add_argument("--out", required=True)
    a = ap.parse_args()
    {"crawl": crawl, "stats": stats, "export": export}[a.cmd](a)


if __name__ == "__main__":
    main()
