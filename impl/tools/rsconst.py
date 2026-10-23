#!/usr/bin/env python3
"""Rewrite float literal markers in Rust sources (in place, idempotent):
  c64!(LIT) -> F64::from_bits(0x...) /* LIT */      c32!(LIT) -> F32::from_bits(0x...) /* LIT */
LIT is a decimal literal as written in the Lean spec (correctly rounded, like Lean's OfScientific)."""
import re, struct, sys
def b64(s): return "F64::from_bits(0x%016X) /* %s */" % (struct.unpack(">Q", struct.pack(">d", float(s)))[0], s)
def b32(s): return "F32::from_bits(0x%08X) /* %s */" % (struct.unpack(">I", struct.pack(">f", float(s)))[0], s)
for p in sys.argv[1:]:
    t = open(p).read()
    u = re.sub(r"c64!\(([^)]*)\)", lambda m: b64(m.group(1).strip()), t)
    u = re.sub(r"c32!\(([^)]*)\)", lambda m: b32(m.group(1).strip()), u)
    if u != t:
        open(p, "w").write(u)
