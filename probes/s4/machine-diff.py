#!/usr/bin/env python3
"""S4 review probe: compare each definition kept in the trimmed Contract/Machine.lean with
v0.3's contract-v03/RecursionFast/Contract/Machine.lean, token for token (after `ℕ` -> `Nat`
and whitespace normalisation), and print the differing ones in full."""
import re, sys
new = open(sys.argv[1]).read()
old = open(sys.argv[2]).read()
def decls(src):
    src = re.sub(r'/-.*?-/', '', src, flags=re.S)
    parts = re.split(r'\n(?=(?:def|structure|inductive|@\[[^\]]*\] def) )', src)
    out = {}
    for p in parts:
        m = re.match(r'(?:@\[[^\]]*\] )?(?:def|structure|inductive) ([\w.]+)', p)
        if m:
            body = re.split(r'\n\n|\nend |\n/-!', p)[0]
            out[m.group(1)] = ' '.join(body.replace('ℕ', 'Nat').split())
    return out
N, O = decls(new), decls(old)
for k in N:
    if k not in O: print(f"NEW      {k}")
    elif N[k] == O[k]: print(f"SAME     {k}")
    else:
        print(f"CHANGED  {k}\n  v0.3: {O[k]}\n  v2  : {N[k]}")
for k in O:
    if k not in N: print(f"REMOVED  {k}")
