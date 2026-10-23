#!/usr/bin/env python3
"""Malformed / fuzzed .osr (and --mods) corpus for the Rust-vs-Lean end-to-end check (difftest/rust_eval_diff.py).
usage: mk_osr_fuzz.py OUTDIR N [SEED [info]]   -> OUTDIR/*.osr (+ a few .osu) and OUTDIR/jobs.txt ("BM OSR [MODS-JSON]")
Sources: small real replays from data/replays (stable) and data/replays_v2 (lazer) with their beatmaps.
Mutation classes (label in the file name): container (truncation, byte flips, ruleset, version, string lengths,
7-bit overflow, date ticks, byte-array lengths, legacy mod bits), payload (LZMA corruption/truncation, short
payloads, empty, re-encoded frame text: bad numbers/overflow/junk/BOMs/UTF-16/invalid UTF-8), lazer score info
JSON (mods/settings/statistics/pauses/rank variants, invalid JSON, trailing text, escapes), --mods JSON
(unknown acronyms, invalid JSON, settings types), beatmap (non-osu ruleset, empty, garbage)."""
import json, lzma, os, random, sqlite3, struct, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def rd7(b, i):
    r = s = 0
    while True:
        x = b[i]; i += 1; r |= (x & 0x7f) << s; s += 7
        if x < 0x80:
            return r, i


def parse(b):
    """field offsets of a well-formed .osr"""
    f = {"version": 1}
    i = 5
    for name in ("hash", "player", "md5"):
        f[name] = i
        if b[i] == 0:
            i += 1
        else:
            n, j = rd7(b, i + 1); i = j + n
    f["counts"] = i; i += 12
    f["score"] = i; i += 4
    f["combo"] = i; i += 2
    f["perfect"] = i; i += 1
    f["mods"] = i; i += 4
    f["hp"] = i
    if b[i] == 0:
        i += 1
    else:
        n, j = rd7(b, i + 1); i = j + n
    f["date"] = i; i += 8
    f["replay_len"] = i
    n = struct.unpack("<i", b[i:i + 4])[0]; i += 4
    f["replay"] = (i, max(n, 0)); i += max(n, 0)
    f["online_id"] = i
    ver = struct.unpack("<i", b[1:5])[0]
    i += 8 if ver >= 20140721 else (4 if ver >= 20121008 else 0)
    if ver >= 30000001:
        f["info_len"] = i
        n = struct.unpack("<i", b[i:i + 4])[0]; i += 4
        f["info"] = (i, max(n, 0)); i += max(n, 0)
    f["end"] = i
    return f


def comp(data):
    return lzma.compress(data, format=lzma.FORMAT_ALONE)


def with_payload(b, f, key, newdata):
    lo, n = f[key]
    lenpos = f["replay_len"] if key == "replay" else f["info_len"]
    return b[:lenpos] + struct.pack("<i", len(newdata)) + newdata + b[lo + n:]


def text_of(b, f, key):
    lo, n = f[key]
    return lzma.decompress(b[lo:lo + n], format=lzma.FORMAT_ALONE)


FRAME_MUTS = ["badnum", "overflow", "junk", "empty", "bom8", "utf16le", "utf16be", "badutf8", "nan", "fewfields",
              "hugeint", "negdiff", "comma", "skipmarker", "seed", "spaces", "utf32"]


def mut_frames(rng, t):
    s = t.decode("utf-8", "replace")
    fr = s.split(",")
    k = rng.randrange(max(1, len(fr) - 1))
    m = rng.choice(FRAME_MUTS)
    if m == "badnum":
        p = fr[k].split("|"); p[rng.randrange(len(p))] = rng.choice(["x", "1.2.3", "", "-", "1e", "0x10", "∞"]); fr[k] = "|".join(p)
    elif m == "overflow":
        p = fr[k].split("|"); p[0] = rng.choice(["2147483648", "-2147483649", "99999999999"]); fr[k] = "|".join(p)
    elif m == "hugeint":
        p = fr[k].split("|"); p[min(3, len(p) - 1)] = rng.choice(["4294967296", "2147483647", "-1", "1e9"]); fr[k] = "|".join(p)
    elif m == "junk":
        fr.insert(k, "".join(rng.choice("|,0123456789.-ab ") for _ in range(rng.randrange(1, 12))))
    elif m == "empty":
        return m, b""
    elif m == "nan":
        p = fr[k].split("|"); p[min(1, len(p) - 1)] = rng.choice(["NaN", "Infinity", "-Infinity", "1E+400"]); fr[k] = "|".join(p)
    elif m == "fewfields":
        fr[k] = "|".join(fr[k].split("|")[:rng.randrange(1, 4)])
    elif m == "negdiff":
        p = fr[k].split("|"); p[0] = str(-rng.randrange(1, 100000)); fr[k] = "|".join(p)
    elif m == "comma":
        fr.insert(k, "")
    elif m == "skipmarker":
        fr.insert(0, "-12345|0|0|" + rng.choice(["0", "1", "x"]))
    elif m == "seed":
        fr.append("-12345|0|0|" + str(rng.randrange(-5, 99999)))
    elif m == "spaces":
        p = fr[k].split("|"); j = rng.randrange(len(p)); p[j] = " " + p[j] + " "; fr[k] = "|".join(p)
    s = ",".join(fr)
    raw = s.encode("utf-8")
    if m == "bom8":
        raw = b"\xef\xbb\xbf" + raw
    elif m == "utf16le":
        raw = b"\xff\xfe" + s.encode("utf-16-le")
    elif m == "utf16be":
        raw = b"\xfe\xff" + s.encode("utf-16-be")
    elif m == "utf32":
        raw = b"\xff\xfe\x00\x00" + s.encode("utf-32-le")
    elif m == "badutf8":
        j = rng.randrange(len(raw) + 1); raw = raw[:j] + rng.choice([b"\xff", b"\xc3", b"\xed\xa0\x80", b"\xf4\x90\x80\x80", b"\xe2\x82"]) + raw[j:]
    return m, raw


def info_variants(rng, info):
    """lazer score info JSON mutations: (label, text bytes)"""
    try:
        d = json.loads(info)
    except Exception:
        d = {}
    m = rng.randrange(40)
    d = json.loads(json.dumps(d))
    acr_pool = ["DT", "HR", "HD", "NF", "EZ", "HT", "DA", "CL", "AT", "CN", "RD", "TP", "XX", "dt", "", "MR", "WU", "AS", "SD", "PF", "FL", "TC", "BL"]
    if m == 0:
        d.pop("mods", None)
    elif m == 1:
        d["mods"] = None
    elif m == 2:
        d["mods"] = rng.choice([{}, "DT", 3, True])
    elif m == 3:
        d["mods"] = [{"acronym": rng.choice([5, True, False, None, [], {}, 1.5])}]
    elif m == 4:
        d["mods"] = [{"acronym": rng.choice(acr_pool), "settings": rng.choice([None, [], 3, "x", {}])}]
    elif m == 5:
        d["mods"] = [rng.choice([None, 1, "DT", []])]
    elif m == 6:
        d["mods"] = [{"acronym": rng.choice(acr_pool)} for _ in range(rng.randrange(0, 4))]
    elif m == 7:
        d["mods"] = [{"acronym": "DT", "settings": {"speed_change": rng.choice([1.5, 2, "1.2", None, True, 1e400 if False else 9e99, -1, 0.5, 1.0000001, [1], {"a": 1}, 99999999999999999999])}}]
    elif m == 8:
        d["mods"] = [{"acronym": rng.choice(["RD", "TP"]), "settings": rng.choice([{}, {"seed": rng.randrange(-2**31, 2**31)}, {"seed": None}, {"seed": "12"}])}]
    elif m == 9:
        d["statistics"] = rng.choice([None, [], {"great": "1"}, {"bogus": 1}, {"Great": 1}, {"5": 2}, {"-1": 1}, {"1_0": 1}, {"great": 2**31}, {"great": 1.5}, {"great": -2**31}, {"GREAT": 3}, {"small_tick_miss": 1}, {"SmallTickMiss": 1}])
    elif m == 10:
        d["maximum_statistics"] = rng.choice([None, 5, {"miss": "x"}, {"legacy_combo_increase": 1}, {"_1": 1}])
    elif m == 11:
        d["online_id"] = rng.choice([None, "1", 2**63, -2**63, 2**63 - 1, 1.0, True, 1e5])
    elif m == 12:
        d["user_id"] = rng.choice([None, 2**31, -2**31, "5", 3.0])
    elif m == 13:
        d["total_score_without_mods"] = rng.choice([None, 2**63, 5, "5", 1.5])
    elif m == 14:
        d["client_version"] = rng.choice([None, 5, True, [], "x"])
    elif m == 15:
        d["rank"] = rng.choice([None, "S", "sh", "xh", "Q", 3, 2**40, "5", "-2", "", True, 1.5, "1_2"])
    elif m == 16:
        d["pauses"] = rng.choice([None, [], [1, 2], [1.5], ["1"], 3, [2**31]])
    elif m == 17:
        return "trailing", (json.dumps(d) + rng.choice([" x", "}", " \n\t ", ",", "\x00"])).encode()
    elif m == 18:
        s = json.dumps(d); j = rng.randrange(len(s)); return "cut", s[:j].encode()
    elif m == 19:
        return "trailcomma", json.dumps(d).replace("}", ",}", 1).encode()
    elif m == 20:
        return "null", b"null"
    elif m == 21:
        return "array", rng.choice([b"[]", b"5", b"\"x\"", b"true"])
    elif m == 22:
        s = json.dumps(d).replace("\"acronym\"", "\"acr\\u006fnym\"", 1); return "escape", s.encode()
    elif m == 23:
        return "badescape", json.dumps(d).replace("\"mods\"", rng.choice(["\"mo\\ds\"", "\"mods\\u00\"", "\"\\u12G4mods\"", "\"m\\uD800ods\""]), 1).encode()
    elif m == 24:
        d["mods"] = d.get("mods") or []
        d["mods"].append({"acronym": "HR", "acronym2": "x"})
        return "dupkey", json.dumps(d).replace("\"acronym2\": \"x\"", "\"acronym\": \"EZ\"").encode()
    elif m == 25:
        return "empty", b""
    elif m == 26:
        return "bom", b"\xef\xbb\xbf" + json.dumps(d).encode()
    elif m == 27:
        return "utf16", b"\xff\xfe" + json.dumps(d).encode("utf-16-le")
    elif m == 28:
        return "numfmt", json.dumps(d).replace(": ", ": +", 1).encode()
    elif m == 29:
        d["mods"] = [{"acronym": "DA", "settings": {rng.choice(["circle_size", "approach_rate", "drain_rate", "overall_difficulty", "extended_limits"]): rng.choice([0, 11, 12.5, -3, None, True, "7", 1e-9])}}]
    elif m == 30:
        d["mods"] = [{"acronym": rng.choice(["WU", "WD", "AS", "HT", "DC", "NC"]), "settings": {rng.choice(["initial_rate", "final_rate", "speed_change", "adjust_pitch"]): rng.choice([0.5, 2, 1.0, 0.01, 99, None, False])}}]
    elif m == 31:
        d["mods"] = [{"acronym": "AT"}] + (d.get("mods") or [])
    elif m == 32:
        return "deep", ("[" * 50 + "]" * 50).encode()
    elif m == 33:
        return "ws", (" \r\n\t" + json.dumps(d) + "\r\n").encode()
    elif m == 34:
        return "numbers", json.dumps(d).replace("\"user_id\": ", "\"user_id\": -0", 1).encode()
    else:
        d["mods"] = [{"acronym": rng.choice(acr_pool), "settings": {k: rng.choice([1, 0.5, True, None, "x", 2**40])
                      for k in rng.sample(["seed", "speed_change", "scale", "style", "retries", "restart", "minimum_accuracy", "angle_sharpness"], 2)}}]
    return "json%d" % m, json.dumps(d).encode()


MOD_ARGS = ['[{"acronym":"NF"}]', '[{"acronym":"XX"}]', '[{"acronym":"AT"}]', '[{"acronym":"DT","settings":{"speed_change":1.3}}]',
            '[{"acronym":"RD"}]', '[{"acronym":"TP","settings":{"seed":5}}]', '[', '[]', '{}', '[1]', '[{"acronym":5}]',
            '[{"acronym":"cl"}]', '[{"acronym":"HR"},{"acronym":"EZ"}]', '[{"acronym":"DA","settings":{"circle_size":11,"extended_limits":true}}]',
            'nonsense', '[{"acronym":"NF","settings":null}]', '[{"acronym":"CN"}]', '[{"acronym":"SV2"}]', '[{"acronym":"TD"}]',
            '[{"acronym":"HD","settings":{"only_fade_approach_circles":"yes"}}]', '[{"acronym":"WU","settings":{"initial_rate":2,"final_rate":0.5}}]',
            '[{"acronym":"\\u0044T"}]', '[{"acronym":"DT"} trailing', '  [ {"acronym" : "HT" } ]  ']


def main():
    out, n = sys.argv[1], int(sys.argv[2])
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    focus = sys.argv[4] if len(sys.argv) > 4 else ""   # "info": lazer replays, frame-text and score-info mutations only
    rng = random.Random(seed)
    os.makedirs(out, exist_ok=True)
    db = sqlite3.connect(os.path.join(ROOT, "data", "index_v2.sqlite"))
    v2 = []
    for sid, bp in db.execute("select id, beatmap_path from scores where status='ok' order by id"):
        rp = os.path.join(ROOT, "data", "replays_v2", "%d.osr" % sid)
        if bp and os.path.exists(os.path.join(ROOT, bp)) and os.path.exists(rp) and os.path.getsize(rp) < 60000:
            v2.append((os.path.join(ROOT, bp), rp))
    db1 = sqlite3.connect(os.path.join(ROOT, "data", "index.sqlite"))
    st = []
    for f in sorted(os.listdir(os.path.join(ROOT, "data", "replays"))):
        if not f.endswith(".osr"):
            continue
        r = db1.execute("select beatmap_id from scores where score_id=?", (int(f.split(".")[0]),)).fetchone()
        rp = os.path.join(ROOT, "data", "replays", f)
        if r and os.path.exists(os.path.join(ROOT, "data", "beatmaps", f"{r[0]}.osu")) and os.path.getsize(rp) < 60000:
            st.append((os.path.join(ROOT, "data", "beatmaps", f"{r[0]}.osu"), rp))
    rng.shuffle(v2); rng.shuffle(st)
    jobs = []
    for k in range(n):
        lazer = rng.random() < 0.55 or focus == "info"
        bm, rp = rng.choice(v2[:300] if lazer else st[:300])
        b = bytearray(open(rp, "rb").read())
        f = parse(bytes(b))
        cls = rng.randrange(52, 90) if focus == "info" else rng.randrange(100)
        mods = None
        label = ""
        if cls < 10:
            j = rng.randrange(len(b)); b = b[:j]; label = "trunc"
        elif cls < 14:
            j = rng.randrange(min(len(b), f["date"] + 8)); b = b[:j]; label = "trunchdr"
        elif cls < 20:
            for _ in range(rng.randrange(1, 4)):
                j = rng.randrange(min(len(b), f["replay"][0] + 16)); b[j] = rng.randrange(256)
            label = "fliphdr"
        elif cls < 22:
            b[0] = rng.choice([1, 2, 3, 255]); label = "ruleset"
        elif cls < 26:
            v = rng.choice([0, 20121007, 20121008, 20140720, 20140721, 29999999, 30000000, 30000001, -1, 2**31 - 1])
            b[1:5] = struct.pack("<i", v); label = "version"
        elif cls < 29:
            pos = f[rng.choice(["hash", "player", "md5", "hp"])]
            b[pos:pos + 1] = bytes([0x0b]) + rng.choice([b"\xff\xff\xff\xff\x0f", b"\xff\xff\xff\xff\x10", b"\xff\xff\xff\xff\xff",
                                                            b"\x80\x80\x80\x80\x08", b"\x7f", b"\x00", b"\xc8\x01"])
            label = "strlen"
        elif cls < 32:
            d = f["date"]; b[d:d + 8] = struct.pack("<q", rng.choice([-1, -2**63, 3155378975999999999, 3155378976000000000, 2**63 - 1, 0])); label = "date"
        elif cls < 36:
            lp = f["replay_len"]; b[lp:lp + 4] = struct.pack("<i", rng.choice([-1, 0, 4, 12, 13, 2**31 - 1, -2**31, f["replay"][1] + 5])); label = "replaylen"
        elif cls < 40:
            m = f["mods"]; b[m:m + 4] = struct.pack("<i", rng.choice([1 << rng.randrange(31) for _ in range(5)] + [rng.randrange(-2**31, 2**31), 0x7fffffff, -1]))
            label = "legacymods"
        elif cls < 46:
            lo, nn = f["replay"]
            for _ in range(rng.randrange(1, 6)):
                if nn > 0:
                    j = lo + rng.randrange(nn); b[j] = rng.randrange(256)
            label = "lzmaflip"
        elif cls < 50:
            lo, nn = f["replay"]
            cut = rng.randrange(nn) if nn else 0
            b = bytearray(with_payload(bytes(b), f, "replay", bytes(b[lo:lo + cut]))); label = "lzmacut"
        elif cls < 52:
            lo, nn = f["replay"]
            hdr = bytearray(b[lo:lo + 13]); j = rng.randrange(13); hdr[j] = rng.randrange(256)
            b = bytearray(with_payload(bytes(b), f, "replay", bytes(hdr) + bytes(b[lo + 13:lo + nn]))); label = "lzmahdr"
        elif cls < 68:
            try:
                t = text_of(bytes(b), f, "replay")
            except Exception:
                t = b""
            m, raw = mut_frames(rng, t)
            b = bytearray(with_payload(bytes(b), f, "replay", comp(raw))); label = "frames_" + m
        elif cls < 90 and "info" in f:
            try:
                info = text_of(bytes(b), f, "info")
            except Exception:
                info = b"{}"
            m, raw = info_variants(rng, info)
            b = bytearray(with_payload(bytes(b), f, "info", comp(raw) if rng.random() < 0.97 else raw[:8])); label = "info_" + m
        elif cls < 96:
            mods = rng.choice(MOD_ARGS); label = "modsarg"
        else:
            kind = rng.randrange(4)
            bmtxt = open(bm, "rb").read()
            if kind == 0:
                bmtxt = bmtxt.replace(b"Mode: 0", b"Mode: " + rng.choice([b"1", b"2", b"3", b"9", b"-1", b"x"]))
            elif kind == 1:
                bmtxt = b""
            elif kind == 2:
                bmtxt = bmtxt[:rng.randrange(len(bmtxt))]
            else:
                bmtxt = b"osu file format v14\n[HitObjects]\n" + bytes(rng.randrange(256) for _ in range(64))
            nbm = os.path.join(out, "%05d.osu" % k); open(nbm, "wb").write(bmtxt); bm = nbm; label = "beatmap%d" % kind
        fn = os.path.join(out, "%05d_%s.osr" % (k, label))
        open(fn, "wb").write(bytes(b))
        jobs.append(f"{bm} {fn}" + (f" {mods}" if mods else ""))
    open(os.path.join(out, "jobs.txt"), "w").write("\n".join(jobs) + "\n")
    print(len(jobs), "jobs")


if __name__ == "__main__":
    main()
