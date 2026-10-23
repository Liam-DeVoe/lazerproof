#!/usr/bin/env python3
"""Mutated playables that hit the G17 rejection paths (lazer would throw / malformed), x mod sets."""
import json, struct, sys
D = "/home/exedev/lazerproof/data/wip/rust-sim"
OUT = D + "/rej"
def hx(x): return "0x%016x" % struct.unpack("<Q", struct.pack("<d", x))[0]
def fx(s): return struct.unpack("<d", struct.pack("<Q", int(s, 16)))[0]
bases = []
for c in ["synB", "synC", "synD"]:
    for l in open(f"{D}/{c}/pl/pairs.txt").read().split("\n")[:6]:
        if l.strip(): bases.append(l.split()[:2])
for l in open(f"{D}/real40.txt").read().split("\n")[:6]:
    if l.strip(): bases.append(l.split()[:2])
def sliders(pl): return [o for o in pl["objects"] if o["kind"] == "slider"]
def m_notail(pl):
    s = sliders(pl); 
    if not s: return False
    s[len(s)//2]["nested"] = [n for n in s[len(s)//2]["nested"] if n["kind"] != "tail"]; return True
def m_nohead(pl):
    s = sliders(pl)
    if not s: return False
    s[-1]["nested"] = [n for n in s[-1]["nested"] if n["kind"] != "head"]; return True
def m_emptypath(pl):
    s = sliders(pl)
    if not s: return False
    s[len(s)//2]["path"] = []; s[len(s)//2]["cumulative_length"] = []; return True
def m_shortcum(pl):
    s = [o for o in sliders(pl) if len(o["cumulative_length"]) >= 2]
    if not s: return False
    o = s[0]; o["cumulative_length"] = o["cumulative_length"][:-1]; return True
def m_breakafter(pl):
    e = max(fx(o["end"]) for o in pl["objects"])
    pl["breaks"].append([hx(e + 1000), hx(e + 3000)]); return True
def m_badperiod(pl):
    ob = pl["objects"]
    if len(ob) < 3: return False
    st = fx(ob[len(ob)//2]["start"])
    pl["breaks"].append([hx(st - 10), hx(st - 5)])
    pl["breaks"].sort(key=lambda b: fx(b[0])); return True
def m_drainflip(pl):
    ob = pl["objects"]
    ob[-1]["end"] = hx(fx(ob[0]["start"]) - 5000); return True
def m_hpnan(pl):
    pl["difficulty"]["hp"] = "0x7fc00000"; return True
MUT = [m_notail, m_nohead, m_emptypath, m_shortcum, m_breakafter, m_badperiod, m_drainflip, m_hpnan]
MODS = ["[]", '[{"acronym":"CL"}]', '[{"acronym":"AL"}]', '[{"acronym":"SG"}]', '[{"acronym":"AP"}]',
        '[{"acronym":"AS"}]', '[{"acronym":"NF"},{"acronym":"MG"}]', '[{"acronym":"DT"},{"acronym":"HD"},{"acronym":"TR"}]']
pairs = []
for bi, (pl_path, osr) in enumerate(bases):
    for m in MUT:
        pl = json.load(open(pl_path))
        if not m(pl): continue
        fn = f"{OUT}/{bi}_{m.__name__[2:]}.json"
        json.dump(pl, open(fn, "w"))
        for mj in MODS:
            pairs.append(f"{fn} {osr} {mj}")
open(f"{D}/rej_pairs.txt", "w").write("\n".join(pairs) + "\n")
print(len(pairs))
