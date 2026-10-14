#!/usr/bin/env python3
"""Lean line counter: total, blank, comment-only (incl. doc comments), code lines.
A line with both code and a comment counts as code. Also counts `theorem`/`lemma` lines.
Nested /- -/ block comments are handled; string literals are not special-cased."""
import sys, re
def count(path):
    depth = 0; tot = blank = comment = code = thms = 0
    for line in open(path, encoding='utf-8'):
        tot += 1
        s = line.strip()
        if not s and depth == 0: blank += 1; continue
        has_code = False; i = 0
        while i < len(s):
            if depth > 0:
                if s.startswith('-/', i): depth -= 1; i += 2
                elif s.startswith('/-', i): depth += 1; i += 2
                else: i += 1
            else:
                if s.startswith('/-', i): depth += 1; i += 2
                elif s.startswith('--', i): break
                else:
                    if not s[i].isspace(): has_code = True
                    i += 1
        if has_code: code += 1
        elif s: comment += 1
        else: blank += 1
        if re.match(r'^(@\[[^\]]*\]\s*)?(private\s+|protected\s+)?(theorem|lemma)\b', s): thms += 1
    return tot, blank, comment, code, thms
rows = [(p,) + count(p) for p in sys.argv[1:]]
print(f"{'file':60} {'total':>6} {'blank':>6} {'comment':>7} {'code':>6} {'thm':>4}")
for r in rows: print(f"{r[0]:60} {r[1]:6} {r[2]:6} {r[3]:7} {r[4]:6} {r[5]:4}")
if len(rows) > 1:
    t = [sum(r[i] for r in rows) for i in range(1, 6)]
    print(f"{'TOTAL':60} {t[0]:6} {t[1]:6} {t[2]:7} {t[3]:6} {t[4]:4}")
