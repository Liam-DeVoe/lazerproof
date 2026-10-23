#!/usr/bin/env python3
"""Generate `@[simp]` value lemmas for the float constants of the translation
(`def X : Result float.F64 := float.F64.from_bits N`): `X = ok (lit : F64)` where `lit` is the
shortest decimal literal that round-trips (proved by kernel evaluation).
usage: python3 -I proofs/scripts/gen_consts.py > <blocks file>"""
import os, re, struct
P = os.path.expanduser('~/lazerproof/proofs')
funs = open(os.path.join(P, 'OsuProofs/Generated/Funs.lean')).read()
out = []; seen = set()
for m in re.finditer(r'^def ([\w.]+) : Result float\.(F64|F32) :=\s*\n?\s*float\.\2\.from_bits (\d+)#u(64|32)\s*$', funs, re.M):
    name, ty, bits = m.group(1), m.group(2), int(m.group(3))
    if ty == 'F64':
        v = struct.unpack('<d', struct.pack('<Q', bits))[0]
        r = repr(v)
    else:
        v = struct.unpack('<f', struct.pack('<I', bits))[0]
        # shortest repr that round-trips through binary32
        r = None
        for p in range(1, 18):
            c = f'{v:.{p}g}'
            try:
                if struct.unpack('<f', struct.pack('<f', float(c)))[0] == v: r = c; break
            except OverflowError: pass
        r = r or repr(v)
    if r in ('nan', 'inf', '-inf'): continue
    neg = r.startswith('-')
    a = r.lstrip('-')
    if re.fullmatch(r'\d+\.0', a): a = a[:-2]
    # integral values as plain numerals: `(1e3 : F32)` elaborates via OfScientific and its `decide` times out
    if v == int(v) and abs(v) < 1e15: a = str(int(abs(v)))
    if 'e' in a:
        mant, ex = a.split('e'); a = f'{mant}e{int(ex)}'
    lit = f'(-{a} : {ty})' if neg else f'({a} : {ty})'
    short = name.replace('.', '_')
    if short in seen: continue
    seen.add(short)
    out.append(f'@[simp] theorem cst_{short} : {name} = ok {lit} := by\n  simp [{name}, float.{ty}.from_bits] <;> decide')
print('\n\n'.join(out))
