#!/usr/bin/env python3
"""Generate `AbsTo` instances (Rust translation type -> spec type) for structures and enums
whose field / constructor names correspond (snake_case <-> camelCase, PascalCase <-> camelCase).

usage: python3 -I proofs/scripts/gen_abs.py > <file>   (one `instance` block per type, separated by
blank lines; scripts/auto_prove.py checks them one by one and keeps the ones that elaborate)
"""
import os, re, sys
ROOT = os.path.expanduser('~/lazerproof')
P = os.path.join(ROOT, 'proofs')

def camel(s):
    s = s.strip('«»')
    parts = s.split('_')
    return parts[0] + ''.join(p[:1].upper() + p[1:] for p in parts[1:])

def lower1(s): return s[:1].lower() + s[1:]

RENAME = {'ptype': 'type', 'stype': 'type'}  # Rust field -> spec field where the Rust name is a keyword workaround

# ---- Rust side (Generated/Types.lean)
types = open(os.path.join(P, 'OsuProofs/Generated/Types.lean')).read()
rust = {}
for m in re.finditer(r'^(structure|inductive) ([\w.]+)( \([^)]*\))? where\n((?:(?:  |\| ).*\n)*)', types, re.M):
    kind, name, params, body = m.group(1), m.group(2), m.group(3), m.group(4)
    if params: continue  # skip parametric (trait records)
    if kind == 'structure':
        fields = re.findall(r'^  ([\w«»]+) : (.+)$', body, re.M)
        rust[name] = ('s', [f for f, _ in fields])
    else:
        ctors = []
        for c in re.findall(r'^\| (\w+)((?:.*\n?)(?:  .*\n?)*)', body, re.M):
            nargs = c[1].count('→')
            ctors.append((c[0], nargs))
        rust[name] = ('i', ctors)

# ---- spec side (model/OsuModel/**.lean): namespace-qualified structures / inductives
spec = {}
for dp, _, fs in os.walk(os.path.join(ROOT, 'model/OsuModel')):
    for fn in fs:
        if not fn.endswith('.lean'): continue
        L = open(os.path.join(dp, fn)).read().split('\n')
        ns = []
        i = 0
        while i < len(L):
            l = L[i]
            mn = re.match(r'^namespace ([\w.]+)', l)
            if mn: ns.append(mn.group(1)); i += 1; continue
            me = re.match(r'^end ([\w.]+)', l)
            if me and ns: ns.pop(); i += 1; continue
            ms = re.match(r'^(structure|inductive) (\w+)( .*)? where', l)
            if ms and not (ms.group(3) or '').strip().startswith(('(', '{', '[')):
                kind, nm = ms.group(1), ms.group(2)
                full = '.'.join(ns + [nm])
                j = i + 1; items = []; indoc = False
                while j < len(L) and (L[j].startswith(' ') or L[j].startswith('|') or L[j].strip() == '' and False):
                    t = L[j]
                    if '/--' in t: indoc = '-/' not in t.split('/--', 1)[1]
                    elif indoc:
                        if '-/' in t: indoc = False
                    elif kind == 'structure':
                        mf = re.match(r'^  (\w+) : ', t)
                        if mf: items.append(mf.group(1))
                    else:
                        mc = re.match(r'^\s*\| (\w+)(.*)$', t)
                        if mc:
                            args = mc.group(2)
                            n = len(re.findall(r'\(([^()]*)\)', args))
                            n = sum(len(g.split(':')[0].split()) for g in re.findall(r'\(([^()]*)\)', args))
                            if ':' in args and not args.strip().startswith('('):
                                n = args.split(':', 1)[1].count('→')
                            items.append((mc.group(1), n))
                    j += 1
                spec.setdefault(nm, []).append((full, kind, items))
                i = j; continue
            i += 1

out = []
for rname, (kind, items) in sorted(rust.items()):
    short = rname.split('.')[-1]
    for full, skind, sitems in spec.get(short, []):
        if kind == 's' and skind == 'structure':
            cf = lambda f: RENAME.get(f, camel(f))
            if sorted(cf(f) for f in items) != sorted(sitems): continue
            flds = ', '.join(f'{cf(f)} := abs x.{f}' for f in items)
            out.append(f'instance absTo_{rname.replace(".", "_")} : AbsTo {rname} {full} := ⟨fun x => {{ {flds} }}⟩')
        elif kind == 'i' and skind == 'inductive':
            sc = {c.lower(): c for c, n in sitems}
            if len(sc) != len(items) or any(c.lower() not in sc for c, _ in items): continue
            arms = []
            for c, n in items:
                tgt = sc[c.lower()]
                vs = ' '.join(f'a{k}' for k in range(n))
                av = ' '.join(f'(abs a{k})' for k in range(n))
                arms.append(f'  | .{c}{(" " + vs) if vs else ""} => .{tgt}{(" " + av) if av else ""}')
            out.append(f'instance absTo_{rname.replace(".", "_")} : AbsTo {rname} {full} where\n  abs x := match x with\n' + '\n'.join(arms))
# name tables of beatmap::names (setting keys, enum member names), read from the Rust literals
funs = open(os.path.join(P, 'OsuProofs/Generated/Funs.lean')).read()
def lit_table(fn):
    i = funs.index('def ' + fn); j = funs.index('\n/--', i); return funs[i:j]
kb = lit_table('beatmap.names.key_is')
keys = {int(m.group(1)): bytes(int(x) for x in re.findall(r'(\d+)#u8', m.group(2))).decode()
        for m in re.finditer(r'\| (\d+)#uscalar =>.*?Array\.make \d+#usize \[(.*?)\]', kb, re.S)}
tb = lit_table('beatmap.names.table_name_is')
tabs = {}
for tm in re.finditer(r'\| (\d+)#uscalar =>\n((?:    .*\n)+)', tb):
    names = {int(m.group(1)): bytes(int(x) for x in re.findall(r'(\d+)#u8', m.group(2))).decode()
             for m in re.finditer(r'\| (\d+) =>.*?Array\.make \d+#usize \[(.*?)\]', tm.group(2), re.S)}
    tabs[int(tm.group(1))] = [names[k] for k in sorted(names)]
kl = ', '.join('"%s"' % keys[k] for k in sorted(keys))
pre = [f'/-- `beatmap::names` setting keys (index = Rust key id). -/\ndef keyNames : List String := [{kl}]',
       'instance : AbsTo U32 String := ⟨fun k => keyNames.getD k.val ""⟩']
el = ' | '.join(f'{t} => [{", ".join(f"(\"{n}\", {i})" for i, n in enumerate(ns))}]' for t, ns in sorted(tabs.items()))
pre.append(f'/-- `beatmap::names` enum member tables (value = index). -/\ndef enumTable : Nat → List (String × Int32)\n  | {el}\n  | _ => []')
pre.append('instance : AbsTo U32 (List (String × Int32)) := ⟨fun t => enumTable t.val⟩')
pre.append('instance {α β} [AbsTo α β] : AbsTo α (Id β) := ⟨fun a => (abs a : β)⟩')
pre.append('instance : AbsTo (Slice U8) ByteArray := ⟨fun s => ⟨(s.val.map (fun b => UInt8.ofBitVec b.bv)).toArray⟩⟩')
print('\n\n'.join(pre + out))
