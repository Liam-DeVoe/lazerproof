#!/usr/bin/env python3
"""D80c: truncate a replay's frames at a fraction of its last frame time, keeping the header, the trailing seed frame
(-12345) and everything after the frame payload (online id, lazer JSON) byte-for-byte. Used to force a genuine fail
under the real ReplayPlayer (failing is only allowed once the frames are exhausted; the remaining objects are missed).
usage: osr_truncate.py IN.osr OUT.osr FRACTION | @MS   (@MS: keep frames up to and including the first frame with time > MS)"""
import lzma, os, struct, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import osr  # noqa: E402


def payload_offset(b):
    """Offset of the int32 frame-payload length (same field walk as osr.read)."""
    i = 1 + 4
    for _ in range(3):
        _, i = osr._str(b, i)
    i += 12 + 4 + 2 + 1 + 4
    _, i = osr._str(b, i)
    return i + 8


def main():
    src, dst, arg = sys.argv[1], sys.argv[2], sys.argv[3]
    r = osr.read(src)
    fr = [f for f in r["frames"].split(",") if f]
    t, ts = 0, []
    for f in fr:
        w = int(f.split("|")[0])
        if w != -12345:
            t += w
        ts.append(t)
    if arg.startswith("@"):
        ms = float(arg[1:])
        cut = min(x for f, x in zip(fr, ts) if x > ms and f.split("|")[0] != "-12345")
    else:
        cut = float(arg) * max(ts)
    keep = [f for f, x in zip(fr, ts) if x <= cut and f.split("|")[0] != "-12345"]
    seed = [f for f in fr if f.split("|")[0] == "-12345"]
    text = ",".join(keep + seed) + ","
    b = open(src, "rb").read()
    o = payload_offset(b)
    n, = struct.unpack_from("<i", b, o)
    assert b[o + 4 + n:] == r["rest"]
    data = lzma.compress(text.encode(), format=lzma.FORMAT_ALONE)
    open(dst, "wb").write(b[:o] + struct.pack("<i", len(data)) + data + r["rest"])
    r2 = osr.read(dst)
    assert r2["rest"] == r["rest"] and r2["frames"] == text
    print("%s: %d -> %d frames, cut at %.0f ms (last frame %d)" % (dst, len(fr), len(keep) + len(seed), cut, max(ts)))


if __name__ == "__main__":
    main()
