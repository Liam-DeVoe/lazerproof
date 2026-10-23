#!/usr/bin/env python3
"""Generate `@[step]` (Aeneas WP) wrappers of the hand-written refinement theorems, so that the
`step*` tactic can use them for callers:
  theorem f_refines (bs) : f xs = ok v               ⟶  @[step] f xs ⦃ r => r = v ⦄
  theorem f_refines (bs) : ∃ r, f xs = ok r ∧ P r     ⟶  @[step] f xs ⦃ r => P r ⦄
usage: gen_steps.py > blocks   (checked block by block with check_blocks.py)"""
import os, re, glob
P = os.path.expanduser('~/lazerproof/proofs')

def split_top(s, sep):
    """split s at top-level (paren/bracket depth 0) occurrences of sep"""
    out, d, cur, i = [], 0, '', 0
    while i < len(s):
        c = s[i]
        if c in '([{⟨⦃': d += 1
        elif c in ')]}⟩⦄': d -= 1
        if d == 0 and s.startswith(sep, i):
            out.append(cur); cur = ''; i += len(sep); continue
        cur += c; i += 1
    out.append(cur)
    return out

def binders_of(s):
    """parse a binder list '(a b : T) (h : P) {x : T}' -> [(names, type, explicit)]"""
    res, i = [], 0
    s = s.strip()
    while i < len(s):
        if s[i] in '({[':
            close = {'(': ')', '{': '}', '[': ']'}[s[i]]; d = 0; j = i
            while j < len(s):
                if s[j] in '({[': d += 1
                elif s[j] in ')}]': d -= 1
                if d == 0: break
                j += 1
            inner = s[i + 1:j]
            if ':' in inner:
                nm, ty = inner.split(':', 1)
                res.append((nm.split(), ty.strip(), s[i]))
            else:
                return None
            i = j + 1
        elif s[i].isspace(): i += 1
        else: return None
    return res

if __name__ == '__main__':
    out = []
    for f in sorted(glob.glob(P + '/OsuProofs/**/*.lean', recursive=True)):
        if '/Generated/' in f or '/Auto/' in f or '/Post/' in f or f.endswith('/Schedule.lean'): continue
        txt = open(f).read()
        for m in re.finditer(r'^theorem ([\w.]+_refines) (.*?):= ?(?:by)?\s*$', txt, re.M | re.S):
            name, head = m.group(1), m.group(2)
            if '\ntheorem ' in head or '\n\n' in head: continue
            parts = split_top(head, ' :')
            if len(parts) < 2: continue
            bs, concl = ' :'.join(parts[:-1]), parts[-1].strip()
            b = binders_of(bs)
            if b is None or any(e != '(' for _, _, e in b): continue
            args = ' '.join(n for ns, _, _ in b for n in ns)
            concl = ' '.join(concl.split())
            me = re.fullmatch(r'∃ (\w+), (.+?) = ok \1 ∧ (.+)', concl)
            if me:
                r, lhs, post = me.group(1), me.group(2), me.group(3)
                out.append(f'@[step] theorem {name[:-8]}_step {bs.strip()} :\n    {lhs} ⦃ {r} => {post} ⦄ :=\n  spec_of_ex ({name} {args})')
                continue
            parts = split_top(concl, ' = ok ')
            if len(parts) == 2 and not concl.startswith('∃'):
                lhs, v = parts
                out.append(f'@[step] theorem {name[:-8]}_step {bs.strip()} :\n    {lhs} ⦃ r => r = {v} ⦄ :=\n  spec_of_eq ({name} {args})')
    print('\n\n'.join(out))
