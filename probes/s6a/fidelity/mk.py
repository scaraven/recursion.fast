#!/usr/bin/env python3
"""S6a review probe P2: tiny layouts fed to BOTH harness/check-chain.py and the Lean kernel.

Writes JSON (schema of harness/README.md) for the cases below into OUT/. Each case exercises
clauses of `Layout.rel` where an evaluator could plausibly diverge from Layout.lean:

  F1  (+) one chip, one row: duplicate entries at one position (they cancel: 2a + 2a = 0), a
          degree-3 term with a repeated matrix (S = [0, 0, 1]) and coefficient X^63, a full-width
          K product needing both reduction folds, the flags of a 1-row table ([r=0] = [last] = 1),
          the next row of a 1-row table (itself)
  F2  (+) three chips, three rows: transition + first-row pin + a wrap constraint that only holds
          if row 0 follows the last row; an `eq` bus and a `sub` bus against a fixed table; one
          value looked up twice; selector cells equal to X (silent) on a row whose message is NOT
          in the table; a fixed-table row with sel = 0 carrying an absent value
  F3  (-) F2 with one more selector set to 1: the `eq` bus is unbalanced (2 sent, 1 received);
          every other clause holds
  F4  (-) F1 with a wrong statement: only the public clause fails
  F5  (-) F2 with one extra row in the fixed-table chip's witness: only the fixed clause fails
  F6  (+/-) F2 at classes 6 and 5 (51 cells): only the cell clause separates them
  F7  (-) F1 with a gadget cell flipped: only the gadget clause fails
  F8  (+) a port on bus 9, beyond the JSON's bus-kind list (kind `.eq` by the README/renderer
          convention), balanced

  python3 -I probes/s6a/fidelity/mk.py OUT
"""
import json, os, sys

OUT = sys.argv[1]
os.makedirs(OUT, exist_ok=True)
M64 = (1 << 64) - 1


def kmul(a, b):                         # independent bit-loop K product (two folds by 0x1B)
    t = 0
    for i in range(64):
        if a >> i & 1:
            t ^= b << i
    for _ in range(2):
        hi, t = t >> 64, t & M64
        for i in range(64):
            if hi >> i & 1:
                t ^= 0x1B << i
    return t & M64


def hx(v):
    return f"{v:016x}"


def dump(o, p):
    with open(os.path.join(OUT, p), "w") as f:
        json.dump(o, f, indent=0)


def layout(name, chips, bus, pub=0):
    return {"schema": "recursion.fast/layout/1", "name": name, "params": {}, "chips": chips,
            "bus": bus, "pub": pub}


def chip(name, cols, cons, M, S, c, ports, fixed=None):
    return {"name": name, "cols": cols, "colnames": [f"c{i}" for i in range(cols)],
            "gadget": {"cons": cons, "t": len(M), "q": len(S),
                       "M": [[[r, col, hx(v)] for (r, col, v) in m] for m in M],
                       "S": S, "c": [hx(v) for v in c]},
            "ports": ports, "fixed": fixed}


def nogadget(name, cols, ports, fixed=None):
    return {"name": name, "cols": cols, "colnames": [f"c{i}" for i in range(cols)],
            "gadget": {"cons": 0, "t": 0, "M": [], "q": 0, "S": [], "c": []},
            "ports": ports, "fixed": fixed}


def wit(tables):
    return {"schema": "recursion.fast/witness/1",
            "tables": [{"rows": len(t), "cells": [[hx(v) for v in r] for r in t]} for t in tables]}


def stmt(x):
    return {"schema": "recursion.fast/statement/1", "x": [hx(v) for v in x]}


X = 2
X63 = 1 << 63

# ---------------------------------------------------------------- F1
# columns: 0..31 statement, 32 a, 33 b, 34 w.  Constraint 0: X^63 * b * b * 1 + w = 0, where
# M0 row 0 = 2a + 2a + b (the duplicate entries cancel) and M2 row 0 = w + 0 * b.
# Constraint 1: X^63 * ([r=0] + [last])^2 * 1 = 0 (1 + 1 = 0 on a 1-row table).
# Constraint 2: X^63 * (a' + a)^2 * 1 = 0 (the next row of a 1-row table is itself).
b = M64                                  # a full-width element: X^63 * b * b needs both folds
x0 = 0x0123456789ABCDEF
coef = kmul(kmul(X63, b), b)
cols = 35
ONE, FST, LST = 2 * cols, 2 * cols + 1, 2 * cols + 2
M0 = [(0, 32, X), (0, 32, X), (0, 33, 1),
      (1, FST, 1), (1, LST, 1),
      (2, cols + 32, 1), (2, 32, 1)]
M1 = [(0, ONE, 1), (1, ONE, 1), (2, ONE, 1)]
M2 = [(0, 34, 1), (0, 33, 0)]
F1 = layout("F1", [chip("P", cols, 3, [M0, M1, M2], [[0, 0, 1], [2]], [X63, 1], [])], ["eq"])
a = 0xDEADBEEF
row = [x0] + [i * 0x1111 for i in range(1, 32)] + [a, b, coef]
xs = row[:32]
F1w, F1x = wit([[row]]), stmt(xs)
dump(F1, "F1.layout.json"); dump(F1w, "F1.witness.json"); dump(F1x, "F1.stmt.json")
# F4: wrong statement
F4x = stmt([xs[0] ^ 1] + xs[1:])
dump(F4x, "F4.stmt.json")
# F7: gadget cell flipped (b), statement unchanged
row7 = list(row); row7[33] ^= 1 << 40
dump(wit([[row7]]), "F7.witness.json")

# ---------------------------------------------------------------- F2
# chip 0 PUB (33 cols): x0..x31, col 32 = sel (= 1); receives (x0, x1) on bus 1 (eq)
pc = 33
P_ONE = 2 * pc
pubc = chip("PUB", pc, 1, [[(0, 32, 1), (0, P_ONE, 1)], [(0, P_ONE, 1)]], [[0, 1]], [1],
            [{"bus": 1, "send": False, "sel": 32, "msg": [0, 1]}])
# chip 1 WORK (4 cols: a, s, v, t): a_0 = 1; a' = X a except on the last row; on the last row
# (and only there) the NEXT row is row 0: X^2 * a' + a = 0 holds only cyclically (a_0 = 1, a_2 = X^2)
wc = 4
W_ONE, W_FST, W_LST = 2 * wc, 2 * wc + 1, 2 * wc + 2
gates = [(0, W_FST, 1), (1, W_ONE, 1), (1, W_LST, 1), (2, W_LST, 1)]
lins = [(0, 0, 1), (0, W_ONE, 1),                    # a + 1
        (1, wc + 0, 1), (1, 0, X),                   # a' + X a
        (2, wc + 0, kmul(X, X)), (2, 0, 1)]          # X^2 a' + a
work = chip("WORK", wc, 3, [gates, lins], [[0, 1]], [1],
            [{"bus": 0, "send": False, "sel": 1, "msg": [2]},
             {"bus": 1, "send": True, "sel": 3, "msg": [0, 2]}])
# chip 2 TAB (fixed): rows (sel, v): (1, 5), (1, 7), (0, 99)
tab_rows = [[1, 5], [1, 7], [0, 99]]
tab = nogadget("TAB", 2, [{"bus": 0, "send": True, "sel": 0, "msg": [1]}],
               {"kind": "explicit", "rows": [[hx(v) for v in r] for r in tab_rows]})
F2 = layout("F2", [pubc, work, tab], ["sub", "eq"])
pubrow = [1, 5] + [0] * 30 + [1]
work_rows = [[1, 1, 5, 1],               # lookup 5, send (1, 5)
             [X, 1, 5, 0],               # lookup 5 again; no send
             [kmul(X, X), X, 99, X]]     # selectors X: silent (99 is not in the table)
F2w = wit([[pubrow], work_rows, tab_rows])
F2x = stmt(pubrow[:32])
dump(F2, "F2.layout.json"); dump(F2w, "F2.witness.json"); dump(F2x, "F2.stmt.json")
# F3: row 1 also sends (X, 5): eq bus 2 sent, 1 received
w3 = [list(r) for r in work_rows]; w3[1][3] = 1
dump(wit([[pubrow], w3, tab_rows]), "F3.witness.json")
# F5: the fixed chip's witness has an extra row (it also sends 5 again: harmless for sub)
dump(wit([[pubrow], work_rows, tab_rows + [[1, 5]]]), "F5.witness.json")

# ---------------------------------------------------------------- F8: bus 9 beyond the kind list
p8 = chip("PUB", 33, 1, [[(0, 32, 1), (0, 66, 1)], [(0, 66, 1)]], [[0, 1]], [1],
          [{"bus": 9, "send": True, "sel": 32, "msg": [0]}, {"bus": 9, "send": False, "sel": 32, "msg": [1]}])
F8 = layout("F8", [p8], ["sub"])
r8 = [7, 7] + [0] * 30 + [1]
dump(F8, "F8.layout.json"); dump(wit([[r8]]), "F8.witness.json"); dump(stmt(r8[:32]), "F8.stmt.json")
# F8n: the same with unequal messages: as `.eq` it fails, as `.sub` it would also fail; use a
# received message that IS sent but twice: `.eq` fails, `.sub` would pass -> pins the default kind
p8n = dict(p8, ports=[{"bus": 9, "send": True, "sel": 32, "msg": [0]},
                      {"bus": 9, "send": False, "sel": 32, "msg": [1]},
                      {"bus": 9, "send": False, "sel": 32, "msg": [0]}])
dump(layout("F8n", [p8n], ["sub"]), "F8n.layout.json")
print("written", sorted(os.listdir(OUT)))
