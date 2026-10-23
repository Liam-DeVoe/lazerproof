"""Minimal .osr reader/writer (header + LZMA frame payload). LZMA (FORMAT_ALONE) is the trusted boundary:
the Lean model consumes the decompressed frame text."""
import lzma
import struct


def _uleb(b, i):
    r = s = 0
    while True:
        x = b[i]
        i += 1
        r |= (x & 0x7F) << s
        s += 7
        if not x & 0x80:
            return r, i


def _str(b, i):
    t = b[i]
    i += 1
    if t == 0:
        return None, i
    if t != 0x0B:
        raise ValueError("bad string tag %r" % t)
    n, i = _uleb(b, i)
    return b[i:i + n].decode("utf-8"), i + n


def read(path):
    b = open(path, "rb").read()
    i = 0
    mode = b[i]; i += 1
    version, = struct.unpack_from("<i", b, i); i += 4
    bm_md5, i = _str(b, i)
    player, i = _str(b, i)
    replay_md5, i = _str(b, i)
    counts = struct.unpack_from("<6H", b, i); i += 12
    score, = struct.unpack_from("<i", b, i); i += 4
    max_combo, = struct.unpack_from("<H", b, i); i += 2
    perfect = b[i]; i += 1
    mods, = struct.unpack_from("<i", b, i); i += 4
    life, i = _str(b, i)
    ticks, = struct.unpack_from("<q", b, i); i += 8
    n, = struct.unpack_from("<i", b, i); i += 4
    data = b[i:i + n]; i += n
    frames = lzma.decompress(data, format=lzma.FORMAT_ALONE) if n > 0 else b""
    return {"mode": mode, "version": version, "beatmap_md5": bm_md5, "player": player, "replay_md5": replay_md5,
            "counts": counts, "score": score, "max_combo": max_combo, "perfect": perfect, "mods": mods,
            "life": life, "ticks": ticks, "frames": frames.decode("utf-8"), "rest": b[i:]}


def _wstr(s):
    if s is None:
        return b"\x00"
    e = s.encode("utf-8")
    out = bytearray(b"\x0b")
    n = len(e)
    while True:
        x = n & 0x7F
        n >>= 7
        out.append(x | (0x80 if n else 0))
        if not n:
            break
    return bytes(out) + e


def write(path, *, frames_text, beatmap_md5, version=20250101, mods=0, player="synth", online_id=0,
          lazer_json=None):
    """Write a replay. version >= 30000000 marks a lazer replay (no automatic Classic); if version >= 30000001
    lazer_json (bytes of the LegacyReplaySoloScoreInfo JSON) is appended LZMA-compressed after the online id."""
    data = lzma.compress(frames_text.encode("utf-8"), format=lzma.FORMAT_ALONE)
    out = bytearray()
    out += bytes([0])
    out += struct.pack("<i", version)
    out += _wstr(beatmap_md5) + _wstr(player) + _wstr("0" * 32)
    out += struct.pack("<6H", 0, 0, 0, 0, 0, 0)
    out += struct.pack("<i", 0) + struct.pack("<H", 0) + bytes([0]) + struct.pack("<i", mods)
    out += _wstr("") + struct.pack("<q", 638000000000000000)
    out += struct.pack("<i", len(data)) + data
    out += struct.pack("<q", online_id)
    if version >= 30000001:
        js = lzma.compress(lazer_json if lazer_json is not None else b'{"mods":[]}', format=lzma.FORMAT_ALONE)
        out += struct.pack("<i", len(js)) + js
    open(path, "wb").write(bytes(out))
