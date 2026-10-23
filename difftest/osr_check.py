#!/usr/bin/env python3
"""Tiny stdlib .osr parser (mirrors lazer's LegacyScoreDecoder field order).

Usage: python3 -I osr_check.py FILE.osr [...]   -> prints a summary per file, exit 1 on failure.
"""
import lzma
import struct
import sys


class R:
    def __init__(self, b):
        self.b, self.i = b, 0

    def take(self, n):
        if self.i + n > len(self.b):
            raise ValueError("truncated")
        v = self.b[self.i:self.i + n]
        self.i += n
        return v

    def unpack(self, fmt):
        return struct.unpack("<" + fmt, self.take(struct.calcsize("<" + fmt)))

    def uleb(self):
        n = shift = 0
        while True:
            c = self.take(1)[0]
            n |= (c & 0x7F) << shift
            shift += 7
            if not c & 0x80:
                return n

    def string(self):
        t = self.take(1)[0]
        if t == 0:
            return None
        if t != 0x0B:
            raise ValueError(f"bad string marker {t:#x} at {self.i - 1}")
        return self.take(self.uleb()).decode("utf-8")


def decompress(blob):
    # LZMA "alone" format: 5 props bytes + int64 uncompressed size + stream (as lazer reads it)
    return lzma.decompress(blob, format=lzma.FORMAT_ALONE)


def parse_osr(data):
    r = R(data)
    mode, version = r.unpack("Bi")
    out = dict(mode=mode, version=version, beatmap_md5=r.string(), player=r.string(), replay_md5=r.string())
    (out["n300"], out["n100"], out["n50"], out["ngeki"], out["nkatu"], out["nmiss"]) = r.unpack("HHHHHH")
    out["score"], out["max_combo"], out["perfect"], out["mods"] = r.unpack("iH?i")
    out["life"] = r.string()
    (out["ticks"],) = r.unpack("q")
    (n,) = r.unpack("i")
    lz = r.take(n) if n > 0 else b""
    if version >= 20140721:
        (out["online_id"],) = r.unpack("q")
    elif version >= 20121008:
        (out["online_id"],) = r.unpack("i")
    if version >= 30000001:
        (m,) = r.unpack("i")
        out["lazer_info"] = decompress(r.take(m)).decode() if m > 0 else None
    # lazer stops reading here; some old stable files carry extra trailing bytes (ignored).
    out["trailing"] = len(data) - r.i
    frames, seed = [], None
    text = decompress(lz).decode("ascii") if lz else ""
    for tok in text.split(","):
        if not tok:
            continue
        w, x, y, k = tok.split("|")
        w = int(w)
        if w == -12345:
            seed = int(k)
            continue
        frames.append((w, float(x), float(y), int(k)))
    out["frames"], out["rng_seed"] = frames, seed
    return out


def main(paths):
    rc = 0
    for p in paths:
        try:
            o = parse_osr(open(p, "rb").read())
            print(f"{p}: mode={o['mode']} v={o['version']} player={o['player']} mods={o['mods']} "
                  f"300/100/50/miss={o['n300']}/{o['n100']}/{o['n50']}/{o['nmiss']} combo={o['max_combo']} "
                  f"score={o['score']} frames={len(o['frames'])} seed={o['rng_seed']} id={o.get('online_id')}")
        except Exception as e:  # noqa: BLE001
            print(f"{p}: FAIL {e}")
            rc = 1
    return rc


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
