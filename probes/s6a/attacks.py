#!/usr/bin/env python3
"""S6a review probe P1: hand-built wrong witnesses against L_chain(4) (and the one-G-call harness).

Each attack edits the honest example witness/statement (harness/examples, secret 00..1f) into a
witness for a WRONG chain claim, writes it under OUT/, and runs harness/check-chain.py `check` on
it (the Python `rel` oracle). For the attacks that the real layout rejects through one mechanism,
the matching layout mutant (that mechanism removed) is also written and checked, to show that the
mechanism is load-bearing (the mutant accepts the wrong claim).

  python3 -I probes/s6a/attacks.py REPO OUT
"""
import copy, hashlib, json, os, subprocess, sys

REPO, OUT = sys.argv[1], sys.argv[2]
EX = os.path.join(REPO, "harness/examples")
CHECK = os.path.join(REPO, "harness/check-chain.py")
GEN = os.path.join(REPO, "harness/gen-chain-layout.py")
SECRET = bytes(range(32))
os.makedirs(OUT, exist_ok=True)

M64 = (1 << 64) - 1


def kmul(a, b):                       # independent K product (bit loop, two folds by 0x1B)
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


def load(p):
    with open(p) as f:
        return json.load(f)


def dump(o, p):
    with open(p, "w") as f:
        json.dump(o, f, separators=(",", ":"))


def hx(v):
    return f"{v:016x}"


class W:
    """A witness/statement pair with named-cell access."""

    def __init__(self, L, wit, st):
        self.L, self.wit, self.st = L, copy.deepcopy(wit), copy.deepcopy(st)
        self.col = [{nm: i for i, nm in enumerate(c["colnames"])} for c in L["chips"]]

    def get(self, chip, r, name):
        return int(self.wit["tables"][chip]["cells"][r][self.col[chip][name]], 16)

    def set(self, chip, r, name, v):
        self.wit["tables"][chip]["cells"][r][self.col[chip][name]] = hx(v)

    def xor(self, chip, r, name, v):
        self.set(chip, r, name, self.get(chip, r, name) ^ v)

    def xs(self, i, v):
        self.st["x"][i] = hx(v)


def check(tag, lp, w, k=24):
    wp, xp = os.path.join(OUT, f"{tag}.witness.json"), os.path.join(OUT, f"{tag}.stmt.json")
    dump(w.wit, wp)
    dump(w.st, xp)
    p = subprocess.run([sys.executable, "-I", CHECK, "check", lp, wp, xp, "--k", str(k)],
                       capture_output=True, text=True)
    fails = [ln for ln in p.stdout.splitlines() if ln.startswith("rel:") and " False" in ln]
    ok = p.returncode == 0
    print(f"[{tag}] relK {k}: {ok}" + ("" if ok else "; failing: " + " | ".join(fails)))
    return ok


def chain(s, n):
    for _ in range(n):
        s = hashlib.blake2s(s, digest_size=32).digest()
    return s


def stmt_y(st):
    return b"".join(int(v, 16).to_bytes(8, "little") for v in st["x"][:4])


def mutant(L, f, tag):
    Lm = copy.deepcopy(L)
    f(Lm)
    p = os.path.join(OUT, f"{tag}.layout.json")
    dump(Lm, p)
    return p


L4p = os.path.join(EX, "chain-n4.layout.json")
L4 = load(L4p)
W4, X4 = load(os.path.join(EX, "chain-n4.witness.json")), load(os.path.join(EX, "chain-n4.stmt.json"))
PUB, G, S0, FIN = 0, 1, 4, 24
n = 4
assert stmt_y(X4) == chain(SECRET, 4)
results = {}

print("== honest n = 4")
results["honest"] = check("honest", L4p, W(L4, W4, X4))

# ---- A1: a shorter chain claimed as n = 4 (the n = 3 witness, statement n = 4 / n = 3)
print("== A1 short chain")
w3p, x3p = os.path.join(OUT, "n3.witness.json"), os.path.join(OUT, "n3.stmt.json")
subprocess.run([sys.executable, "-I", GEN, "witness", "--n", "3", "--secret", SECRET.hex(), w3p, x3p], check=True)
L3x = W(L4, load(w3p), load(x3p))
L3x.xs(4, 4)
L3x.set(PUB, 0, "x4", 4)
results["A1a n3-witness, x4=4"] = check("A1a", L4p, L3x)
results["A1b n3-witness, x4=3"] = check("A1b", L4p, W(L4, load(w3p), load(x3p)))


def drop_lastpins(Lm):                # mutant: drop rho_last (G) and kappa_last (S0..S19, FINAL)
    for ch in Lm["chips"]:
        g = ch["gadget"]
        for nm in ("rho_last", "kappa_last"):
            if nm in g.get("names", []):
                r = g["names"].index(nm)
                for M in g["M"]:
                    M[:] = [e for e in M if e[0] != r]


results["A1a mutant nolast"] = check("A1am", mutant(L4, drop_lastpins, "A1am"), L3x)

# ---- A2: an intermediate digest presented as y (the digest after compression 2 = blake2s^3(s))
print("== A2 intermediate state as y")
a2 = W(L4, W4, X4)
Hmid = [a2.get(FIN, 2, f"H{k}") for k in range(8)]
for k in range(8):
    a2.set(PUB, 0, f"H{k}", Hmid[k])
for k in range(4):
    v = Hmid[2 * k] | Hmid[2 * k + 1] << 32
    a2.set(PUB, 0, f"x{k}", v)
    a2.xs(k, v)
assert stmt_y(a2.st) == chain(SECRET, 3)
results["A2a PUB takes FINAL row 2"] = check("A2a", L4p, a2)
a2b = copy.deepcopy(a2)               # ... and FINAL sends OUT from row 2 (la, nl moved)
a2b.set(FIN, 2, "la", 1); a2b.set(FIN, 2, "nl", 0)
a2b.set(FIN, 3, "la", 0); a2b.set(FIN, 3, "nl", 1)
results["A2b + la/nl moved to row 2"] = check("A2b", L4p, a2b)

# ---- A3: a non-boolean selector restarts the chain at compression 3 from a fresh s'
#      (FINAL row 2 stops sending MSG, S0 row 3 stops receiving: sel := X, not 0/1)
print("== A3 restart the chain through silent selectors")
s2 = bytes(range(100, 132))
w1p, x1p = os.path.join(OUT, "n1.witness.json"), os.path.join(OUT, "n1.stmt.json")
subprocess.run([sys.executable, "-I", GEN, "witness", "--n", "1", "--secret", s2.hex(), w1p, x1p], check=True)
W1 = load(w1p)
a3 = W(L4, W4, X4)
TAGS = {"rho", "kappa", "tin0", "tin1", "tin2", "tin3", "tout0", "tout1", "tout2", "tout3", "nf", "nl", "la"}
for ci, ch in enumerate(L4["chips"]):
    if ch["name"] in ("PUB", "ADD8", "NIB"):
        continue
    per = 160 if ch["name"] == "G" else 1
    for r in range(per):
        for nm, c in a3.col[ci].items():
            if nm not in TAGS:
                a3.wit["tables"][ci]["cells"][3 * per + r][c] = W1["tables"][ci]["cells"][r][c]
a3.set(FIN, 2, "nl", 2)               # X: silent
a3.set(S0, 3, "nf", 2)                # X: silent
X1 = load(x1p)
for k in range(8):
    a3.set(PUB, 0, f"H{k}", a3.get(FIN, 3, f"H{k}"))
for k in range(4):
    a3.set(PUB, 0, f"x{k}", int(X1["x"][k], 16))
    a3.xs(k, int(X1["x"][k], 16))
assert stmt_y(a3.st) == chain(s2, 1) != chain(SECRET, 4)
results["A3 real layout"] = check("A3", L4p, a3)


def drop_selpins(Lm):                 # mutant: drop the gadget rows nf (S0) and nl (FINAL)
    for ci, nm in ((S0, "nf"), (FIN, "nl")):
        g = Lm["chips"][ci]["gadget"]
        r = g["names"].index(nm)
        for M in g["M"]:
            M[:] = [e for e in M if e[0] != r]


results["A3 mutant selpin"] = check("A3m", mutant(L4, drop_selpins, "A3m"), a3)

# ---- A4: rot-7 wrap bit of the last compression aliases into y (S6-A3)
#      G-call q = 80*3 + 4*19 + 3 = 319 writes b-word V4 (diagonal slot 3); flip its wrap cell W
print("== A4 wrap aliasing in the last compression")
a4 = W(L4, W4, X4)
e = 1 | 1 << 32                       # (1 + X^32) * 1
r1 = 2 * 319 + 1
a4.xor(G, r1, "W", 1)
a4.xor(G, r1, "B", e)
a4.xor(FIN, 3, "V4", e)
a4.xor(FIN, 3, "H4", e)
a4.xor(FIN, 3, "E4_0", 1)
a4.xor(FIN, 3, "E4_3", 1 << 8)
a4.xor(PUB, 0, "H4", e)
a4.xor(PUB, 0, "x2", e)
a4.xs(2, int(a4.st["x"][2], 16) ^ e)
assert stmt_y(a4.st) != chain(SECRET, 4)
results["A4 real layout"] = check("A4", L4p, a4)


def drop_pair(Lm):
    ch = Lm["chips"][FIN]
    ch["ports"] = [p for p in ch["ports"] if p["bus"] != 2]


results["A4 mutant pairport"] = check("A4m", mutant(L4, drop_pair, "A4m"), a4)

# ---- A5: a 33-bit message word in the secret (s not a byte string)
print("== A5 33-bit secret word")
a5 = W(L4, W4, X4)
for s in range(20):
    a5.xor(S0 + s, 0, "m0", 1 << 32)
SIG0 = [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
        [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
        [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
        [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
        [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
        [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
        [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
        [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
        [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
        [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]
for q in range(80):                   # the G-calls of compression 0 that read m0 get the 33-bit X/Y
    s, gi = divmod(q, 4)
    rr, h = divmod(s, 2)
    xi, yi = SIG0[rr][8 * h + 2 * gi], SIG0[rr][8 * h + 2 * gi + 1]
    if xi == 0:
        a5.xor(G, 2 * q, "X", 1 << 32)
    if yi == 0:
        a5.xor(G, 2 * q, "Y", 1 << 32)
results["A5 real layout"] = check("A5", L4p, a5)

# ---- A6: the one-G-call harness (kernel control LG0) accepts a non-G output b' (no range check
#      of the outputs in PUBG; the chain gets it from the next decomposition)
print("== A6 one-G-call harness: out-of-range b'")
LGp = os.path.join(EX, "gcall0.layout.json")
LG = load(LGp)
a6 = W(LG, load(os.path.join(EX, "gcall0.witness.json")), load(os.path.join(EX, "gcall0.stmt.json")))
for ev in (1, 2, 15):
    a = copy.deepcopy(a6)
    Wtrue = a.get(1, 1, "W")
    a.set(1, 1, "W", Wtrue ^ ev)
    d = kmul(1 | 1 << 32, ev)
    a.xor(1, 1, "B", d)
    a.xor(0, 0, "x7", d)
    a.xs(7, int(a.st["x"][7], 16) ^ d)
    ok = check(f"A6_e{ev}", LGp, a, k=20)
    results[f"A6 harness b' ^= (1+X^32)*{ev}"] = ok
    print(f"      x7 = {a.st['x'][7]} (>= 2^32: {int(a.st['x'][7], 16) >= 1 << 32}); W := {Wtrue ^ ev}")

with open(os.path.join(OUT, "results.json"), "w") as f:
    json.dump(results, f, indent=1)
print(json.dumps(results, indent=1))
