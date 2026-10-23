#!/usr/bin/env python3
"""Corpus downloader: osu!standard beatmaps + stable replays via osu! API v1.

Stdlib only. Resumable: all state lives in an sqlite index; files already on
disk are never re-downloaded.

Layout (default --data /home/exedev/lazerproof/data):
  beatmaps/{beatmap_id}.osu
  replays/{score_id}.osr          reconstructed full .osr (header + LZMA frames)
  index.sqlite                    tables: beatmaps, scores (server stats), meta

Subcommands:
  discover  --pages N          crawl get_beatmaps (m=0, ranked/approved) into the candidate pool
  select    --count N          pick N diverse beatmaps from the pool (stars x length x features)
  scores    [--per-map K]      get_scores for selected maps (top + one mod-filtered query each)
  osu                          download .osu files for selected maps (verifies md5)
  replays   --max N            download replays (get_replay, <=10/min) and write .osr
  all       --count N --max N  discover(if needed) + select + scores + osu + replays
  verify                       parse every .osr on disk and cross-check against the index
  export    --out FILE         dump the score index as jsonl

API key: env OSU_API_V1_KEY or ~/.osu_credentials (OSU_API_V1_KEY=...). Never printed.
"""
import argparse
import base64
import datetime as dt
import hashlib
import json
import os
import random
import sqlite3
import struct
import sys
import time
import urllib.error
import urllib.parse
import urllib.request

API = "https://osu.ppy.sh/api/"
OSU_URL = "https://osu.ppy.sh/osu/{}"
UA = "lazerproof-difftest/0.1 (research corpus; stdlib urllib)"

REPLAY_INTERVAL = 6.5   # get_replay documented limit: 10 requests / minute
API_INTERVAL = 0.25     # other v1 endpoints: documented 1200/min; stay far below
OSU_INTERVAL = 1.0      # /osu/{id} has no documented limit; be polite

# Mod filters used for the extra get_scores query (exact enabled_mods match).
MOD_ROTATION = [0, 8, 16, 64, 24, 72, 2, 256, 1, 1024, 4096, 80, 88, 128, 18, 66]


# --------------------------------------------------------------------------- utils

def log(*a):
    print(time.strftime("%H:%M:%S"), *a, file=sys.stderr, flush=True)


def load_key():
    k = os.environ.get("OSU_API_V1_KEY")
    if k:
        return k.strip()
    path = os.path.expanduser("~/.osu_credentials")
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line.startswith("OSU_API_V1_KEY="):
                return line.split("=", 1)[1].strip().strip('"').strip("'")
    raise SystemExit("OSU_API_V1_KEY not found")


class Throttle:
    def __init__(self, interval):
        self.interval = interval
        self.last = 0.0

    def wait(self):
        d = self.last + self.interval - time.monotonic()
        if d > 0:
            time.sleep(d)
        self.last = time.monotonic()


class Client:
    def __init__(self, key):
        self.key = key
        self.t_api = Throttle(API_INTERVAL)
        self.t_replay = Throttle(REPLAY_INTERVAL)
        self.t_osu = Throttle(OSU_INTERVAL)

    def _get(self, url, throttle, tries=6):
        delay = 10.0
        for attempt in range(tries):
            throttle.wait()
            req = urllib.request.Request(url, headers={"User-Agent": UA})
            try:
                with urllib.request.urlopen(req, timeout=60) as r:
                    return r.read()
            except urllib.error.HTTPError as e:
                if e.code in (404,):
                    return None
                if e.code in (429, 500, 502, 503, 504, 520, 521, 522, 524):
                    log(f"HTTP {e.code}; backoff {delay:.0f}s (attempt {attempt + 1}/{tries})")
                else:
                    log(f"HTTP {e.code}; retry in {delay:.0f}s")
            except (urllib.error.URLError, TimeoutError, ConnectionError, OSError) as e:
                log(f"net error {type(e).__name__}; backoff {delay:.0f}s")
            time.sleep(delay)
            delay = min(delay * 2, 600)
        raise RuntimeError("giving up after retries: " + url.split("?")[0])

    def api(self, endpoint, replay=False, **params):
        params["k"] = self.key
        url = API + endpoint + "?" + urllib.parse.urlencode(params)
        body = self._get(url, self.t_replay if replay else self.t_api)
        if body is None:
            return None
        return json.loads(body)

    def osu_file(self, beatmap_id):
        return self._get(OSU_URL.format(beatmap_id), self.t_osu)


# --------------------------------------------------------------------------- db

SCHEMA = """
CREATE TABLE IF NOT EXISTS beatmaps (
  beatmap_id INTEGER PRIMARY KEY, beatmapset_id INTEGER, approved INTEGER,
  file_md5 TEXT, stars REAL, total_length INTEGER, hit_length INTEGER,
  count_normal INTEGER, count_slider INTEGER, count_spinner INTEGER, max_combo INTEGER,
  cs REAL, od REAL, ar REAL, hp REAL, bpm REAL,
  artist TEXT, title TEXT, version TEXT, creator TEXT,
  bucket TEXT, selected INTEGER DEFAULT 0, scores_fetched INTEGER DEFAULT 0,
  osu_status TEXT, osu_md5 TEXT, raw TEXT
);
CREATE TABLE IF NOT EXISTS scores (
  score_id INTEGER PRIMARY KEY, beatmap_id INTEGER, user_id INTEGER, username TEXT,
  score INTEGER, maxcombo INTEGER,
  count300 INTEGER, count100 INTEGER, count50 INTEGER, countmiss INTEGER,
  countgeki INTEGER, countkatu INTEGER, perfect INTEGER, enabled_mods INTEGER,
  rank TEXT, pp REAL, date TEXT, replay_available INTEGER,
  wanted INTEGER DEFAULT 0, replay_status TEXT, replay_bytes INTEGER, replay_md5 TEXT,
  fetched_at TEXT, raw TEXT
);
CREATE INDEX IF NOT EXISTS scores_bm ON scores(beatmap_id);
CREATE TABLE IF NOT EXISTS meta (k TEXT PRIMARY KEY, v TEXT);
"""


def open_db(data):
    os.makedirs(os.path.join(data, "beatmaps"), exist_ok=True)
    os.makedirs(os.path.join(data, "replays"), exist_ok=True)
    db = sqlite3.connect(os.path.join(data, "index.sqlite"))
    db.row_factory = sqlite3.Row
    db.executescript(SCHEMA)
    return db


def meta_get(db, k, default=None):
    r = db.execute("SELECT v FROM meta WHERE k=?", (k,)).fetchone()
    return r[0] if r else default


def meta_set(db, k, v):
    db.execute("INSERT OR REPLACE INTO meta VALUES (?,?)", (k, str(v)))
    db.commit()


# --------------------------------------------------------------------------- beatmap selection

def bucket_of(b):
    s = b["stars"]
    sb = "s<2" if s < 2 else "s7+" if s >= 7 else f"s{int(s)}"
    L = b["hit_length"]
    lb = "short" if L < 90 else "mid" if L < 240 else "long"
    objs = max(1, b["count_normal"] + b["count_slider"] + b["count_spinner"])
    feat = "sliders" if b["count_slider"] / objs >= 0.5 else "circles"
    if b["count_spinner"] >= 2:
        feat += "+spin"
    return f"{sb}/{lb}/{feat}"


def f(x, conv=float, default=0):
    try:
        return conv(x)
    except (TypeError, ValueError):
        return default


def cmd_discover(cl, db, pages, seed):
    """Crawl get_beatmaps windows starting at random dates (each returns <=500 maps)."""
    rng = random.Random(seed + int(meta_get(db, "discover_pages", "0")))
    start, end = dt.date(2007, 10, 1), dt.date.today()
    span = (end - start).days
    n_new = 0
    for p in range(pages):
        since = start + dt.timedelta(days=rng.randrange(span))
        res = cl.api("get_beatmaps", m=0, a=0, since=since.isoformat(), limit=500) or []
        for b in res:
            if b.get("mode") != "0" or f(b.get("approved"), int) not in (1, 2):
                continue
            row = dict(
                beatmap_id=int(b["beatmap_id"]), beatmapset_id=int(b["beatmapset_id"]),
                approved=int(b["approved"]), file_md5=b["file_md5"],
                stars=f(b.get("difficultyrating")), total_length=f(b.get("total_length"), int),
                hit_length=f(b.get("hit_length"), int), count_normal=f(b.get("count_normal"), int),
                count_slider=f(b.get("count_slider"), int), count_spinner=f(b.get("count_spinner"), int),
                max_combo=f(b.get("max_combo"), int), cs=f(b.get("diff_size")), od=f(b.get("diff_overall")),
                ar=f(b.get("diff_approach")), hp=f(b.get("diff_drain")), bpm=f(b.get("bpm")),
                artist=b.get("artist"), title=b.get("title"), version=b.get("version"),
                creator=b.get("creator"), raw=json.dumps(b))
            row["bucket"] = bucket_of(row)
            cur = db.execute(
                "INSERT OR IGNORE INTO beatmaps (%s) VALUES (%s)" % (",".join(row), ",".join("?" * len(row))),
                list(row.values()))
            n_new += cur.rowcount
        db.commit()
        meta_set(db, "discover_pages", int(meta_get(db, "discover_pages", "0")) + 1)
        log(f"discover since={since}: {len(res)} maps returned, pool new total +{n_new}")
    log("pool size:", db.execute("SELECT COUNT(*) FROM beatmaps").fetchone()[0])


def cmd_select(db, count, seed):
    """Round-robin over buckets so the selection spans stars/length/features."""
    rng = random.Random(seed)
    already = db.execute("SELECT COUNT(*) FROM beatmaps WHERE selected=1").fetchone()[0]
    need = count - already
    if need <= 0:
        log(f"{already} already selected")
        return
    buckets = {}
    for r in db.execute("SELECT beatmap_id, bucket FROM beatmaps WHERE selected=0 ORDER BY beatmap_id"):
        buckets.setdefault(r["bucket"], []).append(r["beatmap_id"])
    for v in buckets.values():
        rng.shuffle(v)
    # least-represented buckets first
    have = {r[0]: r[1] for r in db.execute("SELECT bucket, COUNT(*) FROM beatmaps WHERE selected=1 GROUP BY bucket")}
    order = sorted(buckets, key=lambda k: (have.get(k, 0), rng.random()))
    picked = []
    while len(picked) < need and any(buckets.values()):
        for k in order:
            if buckets[k] and len(picked) < need:
                picked.append(buckets[k].pop())
    db.executemany("UPDATE beatmaps SET selected=1 WHERE beatmap_id=?", [(i,) for i in picked])
    db.commit()
    log(f"selected {len(picked)} new beatmaps across {len(order)} buckets")


# --------------------------------------------------------------------------- scores

SCORE_INT = ["score", "maxcombo", "count300", "count100", "count50", "countmiss",
             "countgeki", "countkatu", "perfect", "enabled_mods", "user_id", "replay_available"]


def cmd_scores(cl, db, per_map):
    rows = db.execute("SELECT beatmap_id FROM beatmaps WHERE selected=1 AND scores_fetched=0").fetchall()
    for i, r in enumerate(rows):
        bid = r["beatmap_id"]
        got = {}
        queries = [dict(limit=50), dict(limit=50, mods=MOD_ROTATION[bid % len(MOD_ROTATION)])]
        for q in queries:
            for s in cl.api("get_scores", b=bid, m=0, **q) or []:
                got[int(s["score_id"])] = s
        for sid, s in got.items():
            vals = {k: f(s.get(k), int) for k in SCORE_INT}
            db.execute(
                """INSERT OR IGNORE INTO scores (score_id, beatmap_id, user_id, username, score, maxcombo,
                   count300, count100, count50, countmiss, countgeki, countkatu, perfect, enabled_mods,
                   rank, pp, date, replay_available, raw) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                (sid, bid, vals["user_id"], s.get("username"), vals["score"], vals["maxcombo"],
                 vals["count300"], vals["count100"], vals["count50"], vals["countmiss"],
                 vals["countgeki"], vals["countkatu"], vals["perfect"], vals["enabled_mods"],
                 s.get("rank"), f(s.get("pp"), float, None), s.get("date"), vals["replay_available"],
                 json.dumps(s)))
        # choose which replays we want: maximise distinct mod combos, then spread over ranks
        avail = sorted((s for s in got.values() if s.get("replay_available") == "1"),
                       key=lambda s: -int(s["score"]))
        chosen, seen_mods = [], set()
        for s in avail:
            if len(chosen) < per_map and s["enabled_mods"] not in seen_mods:
                chosen.append(s); seen_mods.add(s["enabled_mods"])
        rest = [s for s in avail if s not in chosen]
        step = max(1, len(rest) // max(1, per_map - len(chosen))) if rest else 1
        for s in rest[::step]:
            if len(chosen) >= per_map:
                break
            chosen.append(s)
        db.executemany("UPDATE scores SET wanted=1 WHERE score_id=?", [(int(s["score_id"]),) for s in chosen])
        db.execute("UPDATE beatmaps SET scores_fetched=1 WHERE beatmap_id=?", (bid,))
        db.commit()
        log(f"[{i + 1}/{len(rows)}] b{bid}: {len(got)} scores, {len(avail)} with replay, {len(chosen)} wanted")


# --------------------------------------------------------------------------- .osu files

def cmd_osu(cl, db, data):
    rows = db.execute("SELECT beatmap_id, file_md5 FROM beatmaps WHERE selected=1 AND "
                      "(osu_status IS NULL OR osu_status='error')").fetchall()
    for r in rows:
        bid = r["beatmap_id"]
        path = os.path.join(data, "beatmaps", f"{bid}.osu")
        if os.path.exists(path):
            body = open(path, "rb").read()
        else:
            body = cl.osu_file(bid)
            if not body:
                db.execute("UPDATE beatmaps SET osu_status='missing' WHERE beatmap_id=?", (bid,))
                db.commit()
                continue
            tmp = path + ".part"
            with open(tmp, "wb") as fh:
                fh.write(body)
            os.replace(tmp, path)
        md5 = hashlib.md5(body).hexdigest()
        status = "ok" if md5 == r["file_md5"] else "md5_mismatch"
        db.execute("UPDATE beatmaps SET osu_status=?, osu_md5=? WHERE beatmap_id=?", (status, md5, bid))
        db.commit()
        log(f".osu b{bid}: {len(body)} bytes {status}")


# --------------------------------------------------------------------------- .osr writer

def uleb(n):
    out = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        if n:
            out.append(b | 0x80)
        else:
            out.append(b)
            return bytes(out)


def osr_string(s):
    if s is None:
        return b"\x00"
    e = s.encode("utf-8")
    return b"\x0b" + uleb(len(e)) + e


def windows_ticks(date_str):
    # v1 dates are "YYYY-MM-DD HH:MM:SS" (treated as UTC). .NET ticks: 100ns since 0001-01-01.
    d = dt.datetime.strptime(date_str, "%Y-%m-%d %H:%M:%S")
    return (d - dt.datetime(1, 1, 1)) // dt.timedelta(microseconds=1) * 10


def build_osr(s, beatmap_md5, lzma_data):
    """Reconstruct a stable-format .osr. `s` is a scores row; lzma_data is get_replay content."""
    date = s["date"]
    # Game version: unknown from v1; use the play date (yyyymmdd). Must stay < 30000000 so lazer
    # treats it as a legacy (stable) score (adds Classic mod), and >= 20140721 for int64 online id.
    version = max(20140721, int(date[:10].replace("-", "")))
    rank = s["rank"] or ""
    # stable's replay hash recipe (approximate; lazer ignores this field)
    rhash = hashlib.md5(
        f"{s['maxcombo']}osu{s['username']}{beatmap_md5}{s['score']}{rank}".encode()).hexdigest()
    out = bytearray()
    out += struct.pack("<Bi", 0, version)
    out += osr_string(beatmap_md5)
    out += osr_string(s["username"])
    out += osr_string(rhash)
    out += struct.pack("<HHHHHH", s["count300"], s["count100"], s["count50"],
                       s["countgeki"], s["countkatu"], s["countmiss"])
    out += struct.pack("<iH?i", s["score"], s["maxcombo"], bool(s["perfect"]), s["enabled_mods"])
    out += osr_string("")                       # life bar graph (not available)
    out += struct.pack("<q", windows_ticks(date))
    out += struct.pack("<i", len(lzma_data)) + lzma_data
    out += struct.pack("<q", s["score_id"])
    return bytes(out)


def cmd_replays(cl, db, data, max_n):
    rows = db.execute(
        """SELECT s.*, b.file_md5 FROM scores s JOIN beatmaps b USING (beatmap_id)
           WHERE s.wanted=1 AND (s.replay_status IS NULL OR s.replay_status='error')
           ORDER BY s.beatmap_id, s.score DESC LIMIT ?""", (max_n,)).fetchall()
    log(f"{len(rows)} replays to fetch (~{len(rows) * REPLAY_INTERVAL / 60:.1f} min at 10/min)")
    for i, s in enumerate(rows):
        sid = s["score_id"]
        path = os.path.join(data, "replays", f"{sid}.osr")
        if os.path.exists(path):
            db.execute("UPDATE scores SET replay_status='ok' WHERE score_id=?", (sid,))
            db.commit()
            continue
        try:
            res = cl.api("get_replay", replay=True, s=sid, m=0)
        except RuntimeError as e:
            log("replay", sid, "failed:", e)
            db.execute("UPDATE scores SET replay_status='error' WHERE score_id=?", (sid,))
            db.commit()
            continue
        if not res or "content" not in res:
            err = (res or {}).get("error", "no response")
            status = "unavailable" if "not available" in err.lower() else "error"
            if "limit" in err.lower():  # defensive: unexpected rate-limit message
                log("rate-limit message from server; sleeping 120s")
                time.sleep(120)
                status = "error"
            db.execute("UPDATE scores SET replay_status=? WHERE score_id=?", (status, sid))
            db.commit()
            log(f"[{i + 1}/{len(rows)}] {sid}: {err}")
            continue
        lz = base64.b64decode(res["content"])
        osr = build_osr(s, s["file_md5"], lz)
        tmp = path + ".part"
        with open(tmp, "wb") as fh:
            fh.write(osr)
        os.replace(tmp, path)
        db.execute("UPDATE scores SET replay_status='ok', replay_bytes=?, replay_md5=?, fetched_at=? "
                   "WHERE score_id=?", (len(lz), hashlib.md5(lz).hexdigest(),
                                        dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"), sid))
        db.commit()
        log(f"[{i + 1}/{len(rows)}] {sid} b{s['beatmap_id']} mods={s['enabled_mods']}: {len(lz)} B")


# --------------------------------------------------------------------------- verify / export

def cmd_verify(db, data):
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from osr_check import parse_osr
    ok = bad = 0
    for s in db.execute("SELECT s.*, b.osu_md5, b.file_md5 FROM scores s JOIN beatmaps b USING(beatmap_id) "
                        "WHERE replay_status='ok'"):
        path = os.path.join(data, "replays", f"{s['score_id']}.osr")
        problems = []
        try:
            r = parse_osr(open(path, "rb").read())
        except Exception as e:  # noqa: BLE001
            problems.append(f"parse error: {e}")
            r = None
        if r:
            for k_osr, k_db in [("n300", "count300"), ("n100", "count100"), ("n50", "count50"),
                                ("ngeki", "countgeki"), ("nkatu", "countkatu"), ("nmiss", "countmiss"),
                                ("score", "score"), ("max_combo", "maxcombo"), ("mods", "enabled_mods"),
                                ("online_id", "score_id")]:
                if r[k_osr] != s[k_db]:
                    problems.append(f"{k_osr} {r[k_osr]} != {s[k_db]}")
            if r["beatmap_md5"] != s["osu_md5"]:
                problems.append(f".osu md5 mismatch (osu_status) {s['osu_md5']}")
            if len(r["frames"]) < 10:
                problems.append("too few frames")
        if problems:
            bad += 1
            log(f"BAD {s['score_id']}: {'; '.join(problems)}")
        else:
            ok += 1
            fr = r["frames"]
            log(f"ok  {s['score_id']} mods={r['mods']} frames={len(fr)} "
                f"t_end={sum(x[0] for x in fr)}ms seed={r['rng_seed']}")
    log(f"verify: {ok} ok, {bad} bad")
    return bad == 0


def cmd_export(db, out):
    with open(out, "w") as fh:
        for s in db.execute("SELECT s.*, b.file_md5, b.osu_status FROM scores s JOIN beatmaps b "
                            "USING(beatmap_id) WHERE replay_status='ok'"):
            d = {k: s[k] for k in s.keys() if k != "raw"}
            fh.write(json.dumps(d) + "\n")
    log("wrote", out)


# --------------------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--data", default="/home/exedev/lazerproof/data")
    ap.add_argument("--seed", type=int, default=1234)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("discover"); p.add_argument("--pages", type=int, default=4)
    p = sub.add_parser("select"); p.add_argument("--count", type=int, required=True)
    p = sub.add_parser("scores"); p.add_argument("--per-map", type=int, default=3)
    sub.add_parser("osu")
    p = sub.add_parser("replays"); p.add_argument("--max", type=int, default=10)
    p = sub.add_parser("all")
    p.add_argument("--count", type=int, required=True, help="total selected beatmaps")
    p.add_argument("--per-map", type=int, default=3)
    p.add_argument("--max", type=int, default=10, help="max replays this run")
    p.add_argument("--pages", type=int, default=4)
    sub.add_parser("verify")
    p = sub.add_parser("export"); p.add_argument("--out", required=True)
    a = ap.parse_args()

    db = open_db(a.data)
    if a.cmd in ("verify", "export", "select"):
        if a.cmd == "verify":
            sys.exit(0 if cmd_verify(db, a.data) else 1)
        if a.cmd == "export":
            return cmd_export(db, a.out)
        return cmd_select(db, a.count, a.seed)
    cl = Client(load_key())
    if a.cmd == "discover":
        cmd_discover(cl, db, a.pages, a.seed)
    elif a.cmd == "scores":
        cmd_scores(cl, db, a.per_map)
    elif a.cmd == "osu":
        cmd_osu(cl, db, a.data)
    elif a.cmd == "replays":
        cmd_replays(cl, db, a.data, a.max)
    elif a.cmd == "all":
        if db.execute("SELECT COUNT(*) FROM beatmaps").fetchone()[0] < a.count * 5:
            cmd_discover(cl, db, a.pages, a.seed)
        cmd_select(db, a.count, a.seed)
        cmd_scores(cl, db, a.per_map)
        cmd_osu(cl, db, a.data)
        cmd_replays(cl, db, a.data, a.max)


if __name__ == "__main__":
    main()
