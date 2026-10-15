#!/usr/bin/env python3
"""gen-chain-layout.py: the benchmark leaf layout L_chain(n) (DESIGN §7.1-§7.2, open item O-3).

R_chain(y, n; s) :  blake2s256^n(s) = y,  s a private 32-byte start.

Every chain link hashes a 32-byte message, i.e. one BLAKE2s compression with the unkeyed 32-byte
parameter block, counter t = 32 and last-block flag f0 = 0xFFFFFFFF (f1 = 0). The layout is the
`Layout K` of `RecursionFast/Contract/Layout.lean` (K = GF(2^64), `+` = xor, `*` = reduced
carry-less product) written as JSON; the arithmetisation is documented in `harness/CHAIN-LAYOUT.md`
(chips, columns, constraints, buses, cell counts). Python's `hashlib.blake2s` is the reference: the
witness generator asserts every compression against it.

Commands (all paths are arguments; run with `python3 -I`):

  layout  --n N [--k K]  OUT_LAYOUT                  the layout L_chain(N) (with --k: refuse unless it
                                                     fits class K)
  witness --n N [--k K] --secret-file F  OUT_WIT OUT_STMT   the honest witness and the statement
  mini    --secret-file F [--call Q] [--full-table] OUT_LAYOUT OUT_WIT OUT_STMT
          the one-G-call harness layout (the kernel control, RecursionFast/Controls/Chain.lean):
          the public chip feeds the inputs of G-call Q of the chain from the secret, takes its
          outputs and range-checks them bytewise; the add table is trimmed to the rows used unless
          --full-table
  mutant  --kind KIND --n N --secret-file F  OUT_LAYOUT OUT_WIT OUT_STMT
          a layout with one mechanism removed and a wrong witness it admits (KIND: gate, addport,
          nibport, gouttag, fixed, nolast, selpin, pairport); the original layout rejects it

The secret start is read from file F (64 hex digits), or from stdin for `-`; it is never a
command-line argument (S6a-m4). A witness file is secret material: row 0 of S0 holds the start.
  report  [--n N ...]                                cell counts per chip and the least class k
                                                     (default n = 2^8, 2^10, 2^11, 2^12)

Formats (schema `recursion.fast/layout/1`, `.../witness/1`, `.../statement/1`) are documented in
`harness/README.md`. K elements are 16 lowercase hex digits (the 64-bit word `bits`, big-endian
digits, i.e. ordinary hexadecimal notation).
"""
import argparse, hashlib, json, sys

# ---------------------------------------------------------------- K = GF(2^64), Field.lean

MASK64 = (1 << 64) - 1
ORDER = MASK64            # |K*| = 2^64 - 1; X (= 2) is primitive (checked in `report`)


def clmul(a, b):
    """Carry-less product (Field.lean `K.clmul`)."""
    r = 0
    while a:
        if a & 1:
            r ^= b
        a >>= 1
        b <<= 1
    return r


def kmul(a, b):
    """K multiplication: carry-less product, then two folds by x^64 = x^4 + x^3 + x + 1."""
    t = clmul(a, b)
    for _ in range(2):
        t = clmul(t >> 64, 0x1B) ^ (t & MASK64)
    return t & MASK64


def kpow(a, e):
    r = 1
    e %= ORDER
    while e:
        if e & 1:
            r = kmul(r, a)
        a = kmul(a, a)
        e >>= 1
    return r


def kinv(a):
    return kpow(a, ORDER - 1)


GAMMA = 2                 # the tag counter's ratio (X, a generator of K*)


_GCACHE = {}


def g(e):
    """gamma^e (e may be negative), cached."""
    e %= ORDER
    if e not in _GCACHE:
        _GCACHE[e] = kpow(GAMMA, e)
    return _GCACHE[e]


def hx(v):
    return f"{v:016x}"


# ---------------------------------------------------------------- BLAKE2s (RFC 7693)

IV = [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]
SIGMA = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]
M32 = 0xFFFFFFFF
H0 = [IV[0] ^ 0x01010020] + IV[1:]              # parameter block: digest 32, key 0, fanout/depth 1
INIT = H0 + IV[:4] + [IV[4] ^ 32, IV[5], IV[6] ^ M32, IV[7]]   # t = 32, f0 = ~0, f1 = 0


def rotr(w, n):
    return ((w >> n) | (w << (32 - n))) & M32


def words_of(b):
    return [int.from_bytes(b[4 * j:4 * j + 4], "little") for j in range(len(b) // 4)]


def bytes_of(ws):
    return b"".join(w.to_bytes(4, "little") for w in ws)


def quad(h, gi):
    """State words (a, b, c, d) of G-call `gi` in a column (h = 0) or diagonal (h = 1) step."""
    if h == 0:
        return (gi, 4 + gi, 8 + gi, 12 + gi)
    return (gi, 4 + (gi + 1) % 4, 8 + (gi + 2) % 4, 12 + (gi + 3) % 4)


def msg_idx(s, gi):
    """Message-word indices (x, y) of G-call `gi` in half-round s = 2·round + h."""
    r, h = divmod(s, 2)
    return SIGMA[r][8 * h + 2 * gi], SIGMA[r][8 * h + 2 * gi + 1]


# ---------------------------------------------------------------- layout building

ADD, ADDTOP, PAIR, NIB, GIN, GOUT, MSG, OUT = range(8)
BUS_KINDS = ["sub", "sub", "sub", "sub", "eq", "eq", "eq", "eq"]
BUS_NAMES = ["ADD", "ADDTOP", "PAIR", "NIB", "GIN", "GOUT", "MSG", "OUT"]


def bx(j):
    """The packing coefficient of byte j: X^(8j)."""
    return 1 << (8 * j)


class Gadget:
    """A row gadget in the form used by every chip of L_chain: constraint r is
    `gate_r(z) · lin_r(z) = 0`, two linear forms of the view (CCS with t = 2 matrices M0 = gates,
    M1 = linear parts, one term c = 1, S = [0, 1]; degree 2). View indices: row cell c is c, next
    row cell c is cols + c, then ONE, FIRST, LAST (DESIGN §2.1, S1-A11)."""

    def __init__(self, cols):
        self.cols = cols
        self.ONE, self.FIRST, self.LAST = 2 * cols, 2 * cols + 1, 2 * cols + 2
        self.cons = []

    def nxt(self, c):
        return self.cols + c

    def con(self, name, gate, lin):
        def norm(pairs):
            d = {}
            for i, v in pairs:
                assert 0 <= i < 2 * self.cols + 3, (name, i)
                d[i] = d.get(i, 0) ^ v
            return {i: v for i, v in sorted(d.items()) if v}
        self.cons.append((name, norm(gate), norm(lin)))

    # the gates
    def always(self):
        return [(self.ONE, 1)]

    def first(self):
        return [(self.FIRST, 1)]

    def last(self):
        return [(self.LAST, 1)]

    def notlast(self):
        return [(self.ONE, 1), (self.LAST, 1)]

    def json(self):
        if not self.cons:
            return {"cons": 0, "t": 0, "M": [], "q": 0, "S": [], "c": []}
        m0 = [[r, i, hx(v)] for r, (_, gt, _) in enumerate(self.cons) for i, v in gt.items()]
        m1 = [[r, i, hx(v)] for r, (_, _, ln) in enumerate(self.cons) for i, v in ln.items()]
        return {"cons": len(self.cons), "t": 2, "M": [m0, m1], "q": 1, "S": [[0, 1]], "c": [hx(1)],
                "names": [n for n, _, _ in self.cons]}


def drop_gates(gd, names):
    """Mutants: remove the gate entries of the named constraints (each becomes `0 = 0`)."""
    for nm in names or ():
        i = [n for n, _, _ in gd.cons].index(nm)
        n_, gt, ln = gd.cons[i]
        gd.cons[i] = (n_, {}, ln)


def port(bus, send, sel, msg):
    return {"bus": bus, "send": send, "sel": sel, "msg": list(msg)}


def chip(name, cols, colnames, gadget, ports, fixed=None):
    assert len(colnames) == cols, (name, len(colnames), cols)
    return {"name": name, "cols": cols, "colnames": colnames,
            "gadget": gadget.json() if gadget else Gadget(cols).json(), "ports": ports, "fixed": fixed}


# --- the G chip: two rows per G-call (phase 0: first half of G, phase 1: second half)

class GCols:
    ONE, PHI, PSI, RHO, ZERO = 0, 1, 2, 3, 4
    A, B, C, D, X, Y = 5, 6, 7, 8, 9, 10
    P = [11, 12, 13, 14]       # add slot 1, x operand: a (phase 0) / a1 (phase 1) bytes
    Q = [15, 16, 17, 18]       # add slot 1, y operand: b / b1
    M = [19, 20, 21, 22]       # add slot 2, y operand: x / y (message word)
    CB = [23, 24, 25, 26]      # add slot 3, x operand: c / c1
    DP = [27, 28, 29, 30]      # add slot 3, y operand: d1 / d2
    T = [31, 32, 33, 34]       # slot 1 result: a + b / a1 + b1
    AP = [35, 36, 37, 38]      # slot 2 result: a1 / a2
    CP = [39, 40, 41, 42]      # slot 3 result: c1 / c2
    K1, K2, K3 = [43, 44, 45], [46, 47, 48], [49, 50, 51]   # carries into bytes 1, 2, 3
    W = 52                     # wrap nibble: hi(u_1) (phase 0, rot 12) / bit 7 of v_0 (phase 1, rot 7)
    NCOLS = 53
    SLOTS = None


GCols.SLOTS = [(GCols.P, GCols.Q, GCols.T, GCols.K1), (GCols.T, GCols.M, GCols.AP, GCols.K2),
               (GCols.CB, GCols.DP, GCols.CP, GCols.K3)]
G_COLNAMES = (["one", "phi", "psi", "rho", "zero", "A", "B", "C", "D", "X", "Y"]
              + [f"{n}{j}" for n in ["P", "Q", "M", "Cb", "Dp", "T", "Ap", "Cp"] for j in range(4)]
              + [f"k{s}_{j}" for s in (1, 2, 3) for j in (1, 2, 3)] + ["W"])


def g_chip(calls, drop=None, ports_drop=None):
    """The G chip for `calls` G-calls (rows 2·calls; row r has tag rho = gamma^r)."""
    c = GCols
    gd = Gadget(c.NCOLS)
    one, nx = gd.ONE, gd.nxt
    ph0 = [(one, 1), (c.PHI, 1)]           # 1 + phi: phase 0
    ph1 = [(c.PHI, 1)]                     # phi: phase 1
    W1 = 1 ^ (1 << 32)                      # 1 + X^32
    # always
    gd.con("one", gd.always(), [(c.ONE, 1), (one, 1)])
    gd.con("psi", gd.always(), [(c.PSI, 1), (c.PHI, 1), (one, 1)])
    gd.con("zero", gd.always(), [(c.ZERO, 1)])
    gd.con("phi_alt", gd.always(), [(nx(c.PHI), 1), (c.PHI, 1), (one, 1)])
    gd.con("phi_first", gd.first(), [(c.PHI, 1)])
    gd.con("rho_first", gd.first(), [(c.RHO, 1), (one, 1)])
    gd.con("rho_last", gd.last(), [(c.RHO, 1), (one, g(2 * calls - 1))])
    gd.con("rho_step", gd.notlast(), [(nx(c.RHO), 1), (c.RHO, GAMMA)])
    # phase 0: decompose the inputs, link to phase 1
    gd.con("in_A", ph0, [(c.A, 1)] + [(c.P[j], bx(j)) for j in range(4)])
    gd.con("in_B", ph0, [(c.B, 1)] + [(c.Q[j], bx(j)) for j in range(4)])
    gd.con("in_C", ph0, [(c.C, 1)] + [(c.CB[j], bx(j)) for j in range(4)])
    gd.con("in_X", ph0, [(c.X, 1)] + [(c.M[j], bx(j)) for j in range(4)])
    gd.con("in_D", ph0, [(c.D, 1)] + [(c.AP[j], bx(j)) for j in range(4)]
           + [(c.DP[(j + 2) % 4], bx(j)) for j in range(4)])        # d xor a1 = rotl(d1, 16)
    for j in range(4):
        gd.con(f"a1_{j}", ph0, [(nx(c.P[j]), 1), (c.AP[j], 1)])
    for j in range(4):
        gd.con(f"c1_{j}", ph0, [(nx(c.CB[j]), 1), (c.CP[j], 1)])
    gd.con("b1", ph0, [(nx(c.Q[j]), bx(j)) for j in range(4)]       # b1 = rotr(b xor c1, 12)
           + [(c.Q[(j + 2) % 4], 1 << (8 * j + 4)) for j in range(4)]
           + [(c.CP[(j + 2) % 4], 1 << (8 * j + 4)) for j in range(4)] + [(c.W, W1)])
    gd.con("in_Y", ph0, [(c.Y, 1)] + [(nx(c.M[j]), bx(j)) for j in range(4)])
    for j in range(4):                                                # d2 = rotr(d1 xor a2, 8)
        gd.con(f"d2_{j}", ph0, [(nx(c.DP[j]), 1), (c.DP[(j + 1) % 4], 1), (nx(c.AP[(j + 1) % 4]), 1)])
    # phase 1: the outputs
    gd.con("out_A", ph1, [(c.A, 1)] + [(c.AP[j], bx(j)) for j in range(4)])
    gd.con("out_C", ph1, [(c.C, 1)] + [(c.CP[j], bx(j)) for j in range(4)])
    gd.con("out_D", ph1, [(c.D, 1)] + [(c.DP[j], bx(j)) for j in range(4)])
    gd.con("out_B", ph1, [(c.B, 1)] + [(c.Q[(j + 1) % 4], 1 << (8 * j + 1)) for j in range(4)]
           + [(c.CP[(j + 1) % 4], 1 << (8 * j + 1)) for j in range(4)] + [(c.W, W1)])  # rotr(b1 xor c2, 7)
    gd.con("out_X", ph1, [(c.X, 1)])
    gd.con("out_Y", ph1, [(c.Y, 1)])
    drop_gates(gd, drop)
    ports = []
    for (xs, ys, zs, ks) in c.SLOTS:
        ports.append(port(ADD, False, c.ONE, [xs[0], ys[0], c.ZERO, zs[0], ks[0]]))
        ports.append(port(ADD, False, c.ONE, [xs[1], ys[1], ks[0], zs[1], ks[1]]))
        ports.append(port(ADD, False, c.ONE, [xs[2], ys[2], ks[1], zs[2], ks[2]]))
        ports.append(port(ADDTOP, False, c.ONE, [xs[3], ys[3], ks[2], zs[3]]))
    ports.append(port(NIB, False, c.ONE, [c.W]))
    ports.append(port(GIN, False, c.PSI, [c.RHO, c.A, c.B, c.C, c.D, c.X, c.Y]))
    ports.append(port(GOUT, True, c.PHI, [c.RHO, c.A, c.B, c.C, c.D]))
    if ports_drop:
        ports = ports_drop(ports)
    return chip("G", c.NCOLS, G_COLNAMES, gd, ports)


# --- the state chips S_s (s = 0..19): the state before half-round s, one row per compression

def s_cols(s):
    names = ["one", "zero", "kappa"]
    if s >= 1:
        names += [f"tin{gi}" for gi in range(4)]
    names += [f"tout{gi}" for gi in range(4)]
    names += [f"V{w}" for w in range(16)] + [f"m{w}" for w in range(8)]
    if s == 0:
        names += ["nf"]
    return {nm: i for i, nm in enumerate(names)}, names


def s_chip(s, n, gout_tag=True, drop=()):
    cm, names = s_cols(s)
    gd = Gadget(len(names))
    one, nx = gd.ONE, gd.nxt
    K = cm["kappa"]
    gd.con("one", gd.always(), [(cm["one"], 1), (one, 1)])
    gd.con("zero", gd.always(), [(cm["zero"], 1)])
    if s >= 1:
        for gi in range(4):
            gd.con(f"tin{gi}", gd.always(), [(cm[f"tin{gi}"], 1), (K, g(2 * gi + 1))])
    for gi in range(4):
        gd.con(f"tout{gi}", gd.always(), [(cm[f"tout{gi}"], 1), (K, g(8 + 2 * gi))])
    gd.con("kappa_first", gd.first(), [(K, 1), (one, g(8 * (s - 1)))])
    gd.con("kappa_step", gd.notlast(), [(nx(K), 1), (K, g(160))])
    gd.con("kappa_last", gd.last(), [(K, 1), (one, g(160 * (n - 1) + 8 * (s - 1)))])
    if s == 0:
        gd.con("nf", gd.always(), [(cm["nf"], 1), (one, 1), (gd.FIRST, 1)])
        for w in range(16):
            gd.con(f"init{w}", gd.always(), [(cm[f"V{w}"], 1), (one, INIT[w])])
    drop_gates(gd, [d for d in drop if d in [nm for nm, _, _ in gd.cons]])
    V = [cm[f"V{w}"] for w in range(16)]
    m = [cm[f"m{w}"] for w in range(8)]
    ports = []
    if s >= 1:
        for gi in range(4):
            a, b, c_, d = quad((s - 1) % 2, gi)
            tag = [cm[f"tin{gi}"]] if gout_tag else []
            ports.append(port(GOUT, False, cm["one"], tag + [V[a], V[b], V[c_], V[d]]))
    for gi in range(4):
        a, b, c_, d = quad(s % 2, gi)
        xi, yi = msg_idx(s, gi)
        xc = m[xi] if xi < 8 else cm["zero"]
        yc = m[yi] if yi < 8 else cm["zero"]
        ports.append(port(GIN, True, cm["one"], [cm[f"tout{gi}"], V[a], V[b], V[c_], V[d], xc, yc]))
    ports.append(port(MSG, False, cm["nf"] if s == 0 else cm["one"], [K] + m))
    if s <= 18:
        ports.append(port(MSG, True, cm["one"], [cm["tout0"]] + m))
    return chip(f"S{s}", len(names), names, gd, ports)


# --- the final chip: finalisation h' = h xor v_lo xor v_hi, chain link, output

def f_cols():
    names = ["one", "nl", "la", "kappa"] + [f"tin{gi}" for gi in range(4)] + [f"V{w}" for w in range(16)] \
        + [f"H{k}" for k in range(8)] + [f"E{k}_{j}" for k in range(4, 8) for j in range(4)]
    return {nm: i for i, nm in enumerate(names)}, names


def final_chip(n, gout_tag=True, drop=(), pair=True):
    cm, names = f_cols()
    gd = Gadget(len(names))
    one, nx = gd.ONE, gd.nxt
    K = cm["kappa"]
    gd.con("one", gd.always(), [(cm["one"], 1), (one, 1)])
    gd.con("nl", gd.always(), [(cm["nl"], 1), (one, 1), (gd.LAST, 1)])
    gd.con("la", gd.always(), [(cm["la"], 1), (gd.LAST, 1)])
    for gi in range(4):
        gd.con(f"tin{gi}", gd.always(), [(cm[f"tin{gi}"], 1), (K, g(2 * gi + 1))])
    gd.con("kappa_first", gd.first(), [(K, 1), (one, g(152))])
    gd.con("kappa_step", gd.notlast(), [(nx(K), 1), (K, g(160))])
    gd.con("kappa_last", gd.last(), [(K, 1), (one, g(160 * (n - 1) + 152))])
    for k in range(8):
        gd.con(f"H{k}", gd.always(), [(cm[f"H{k}"], 1), (cm[f"V{k}"], 1), (cm[f"V{k + 8}"], 1), (one, H0[k])])
    for k in range(4, 8):
        gd.con(f"E{k}", gd.always(), [(cm[f"H{k}"], 1)] + [(cm[f"E{k}_{j}"], bx(j)) for j in range(4)])
    drop_gates(gd, drop)
    V = [cm[f"V{w}"] for w in range(16)]
    H = [cm[f"H{k}"] for k in range(8)]
    ports = []
    for gi in range(4):
        a, b, c_, d = quad(1, gi)
        tag = [cm[f"tin{gi}"]] if gout_tag else []
        ports.append(port(GOUT, False, cm["one"], tag + [V[a], V[b], V[c_], V[d]]))
    ports.append(port(MSG, True, cm["nl"], [K] + H))
    ports.append(port(OUT, True, cm["la"], H))
    for k in range(4, 8) if pair else ():
        ports.append(port(PAIR, False, cm["one"], [cm[f"E{k}_0"], cm[f"E{k}_1"]]))
        ports.append(port(PAIR, False, cm["one"], [cm[f"E{k}_2"], cm[f"E{k}_3"]]))
    return chip("FINAL", len(names), names, gd, ports)


# --- the public chip and the tables

def pub_chip(n):
    names = [f"x{i}" for i in range(32)] + [f"H{k}" for k in range(8)] + ["one"]
    gd = Gadget(len(names))
    one = gd.ONE
    gd.con("one", gd.always(), [(40, 1), (one, 1)])
    for k in range(4):                                  # y limb k = H_2k + X^32 H_2k+1 (S2-A1)
        gd.con(f"y{k}", gd.always(), [(k, 1), (32 + 2 * k, 1), (33 + 2 * k, 1 << 32)])
    gd.con("n", gd.always(), [(4, 1), (one, n)])
    for i in range(5, 32):
        gd.con(f"x{i}", gd.always(), [(i, 1)])
    return chip("PUB", len(names), names, gd, [port(OUT, False, 40, list(range(32, 40)))])


def add_row(r):
    """Row r of the 8-bit add-with-carry table: x = r mod 2^8, y = (r >> 8) mod 2^8, cin = r >> 16."""
    x, y, ci = r & 0xFF, (r >> 8) & 0xFF, r >> 16
    s = x + y + ci
    return [1, x, y, ci, s & 0xFF, s >> 8]


ADD_ROWS = 1 << 17


def add_chip(fixed):
    ports = [port(ADD, True, 0, [1, 2, 3, 4, 5]), port(ADDTOP, True, 0, [1, 2, 3, 4]),
             port(PAIR, True, 0, [1, 2])]
    return chip("ADD8", 6, ["sel", "x", "y", "cin", "z", "cout"], None, ports, fixed)


def nib_chip():
    rows = [[hx(1), hx(v)] for v in range(16)]
    return chip("NIB", 2, ["sel", "v"], None, [port(NIB, True, 0, [1])], {"kind": "explicit", "rows": rows})


MUTANTS = ["gate", "addport", "nibport", "gouttag", "fixed", "nolast", "selpin", "pairport"]


def chain_layout(n, mut=None):
    """L_chain(n). `mut` selects a mutant (see `mutant`)."""
    gdrop = {"gate": ["out_C"], "nolast": ["rho_last"]}.get(mut, [])
    sdrop = {"nolast": ["kappa_last"], "selpin": ["nf"]}.get(mut, [])
    fdrop = {"nolast": ["kappa_last"], "selpin": ["nl"]}.get(mut, [])
    pdrop = None
    if mut == "addport":                 # the top-byte lookup of add slot 2 (a1 / a2)
        pdrop = lambda ps: [p for i, p in enumerate(ps) if i != 7]
    if mut == "nibport":
        pdrop = lambda ps: [p for p in ps if p["bus"] != NIB]
    if mut == "gouttag":
        def pdrop(ps):
            return [dict(p, msg=p["msg"][1:]) if p["bus"] == GOUT else p for p in ps]
    gch = g_chip(80 * n, gdrop, pdrop)
    chips = [pub_chip(n), gch, add_chip(None if mut == "fixed" else {"kind": "add8"}), nib_chip()]
    chips += [s_chip(s, n, mut != "gouttag", sdrop) for s in range(20)]
    chips += [final_chip(n, mut != "gouttag", fdrop, mut != "pairport")]
    return {"schema": "recursion.fast/layout/1",
            "name": f"L_chain({n})" + (f" mutant {mut}" if mut else ""),
            "params": {"n": n, "gamma": hx(GAMMA)},
            "chips": chips, "bus": BUS_KINDS, "busnames": BUS_NAMES, "pub": 0}


# ---------------------------------------------------------------- the witness

def kbytes(w):
    return [(w >> (8 * j)) & 0xFF for j in range(4)]


def add_bytes(xb, yb):
    """Byte-wise addition with carries: result bytes and the carries into bytes 1, 2, 3."""
    z, k, c = [], [], 0
    for j in range(4):
        s = xb[j] + yb[j] + c
        z.append(s & 0xFF)
        c = s >> 8
        if j < 3:
            k.append(c)
    return z, k


def pack(bs):
    return sum(b << (8 * j) for j, b in enumerate(bs))


def g_rows(q, A, B, C, D, X, Y, fault=None, rho=None):
    """The two rows of G-call q (inputs packed 32-bit words; `rho` = gamma^(2q) if known);
    returns (rows, outputs)."""
    c = GCols
    rows = []
    rho = g(2 * q) if rho is None else rho
    # phase 0
    r0 = [0] * c.NCOLS
    r0[c.ONE], r0[c.PHI], r0[c.PSI], r0[c.RHO], r0[c.ZERO] = 1, 0, 1, rho, 0
    r0[c.A], r0[c.B], r0[c.C], r0[c.D], r0[c.X], r0[c.Y] = A, B, C, D, X, Y
    P, Q, Mb, CB = kbytes(A), kbytes(B), kbytes(X), kbytes(C)
    T, k1 = add_bytes(P, Q)
    AP, k2 = add_bytes(T, Mb)
    a1 = pack(AP)
    d1 = rotr(D ^ a1, 16)
    DP = kbytes(d1)
    CP, k3 = add_bytes(CB, DP)
    c1 = pack(CP)
    u = B ^ c1
    W0 = (u >> 12) & 0xF
    b1 = rotr(u, 12)
    for cols, vals in ((c.P, P), (c.Q, Q), (c.M, Mb), (c.CB, CB), (c.DP, DP), (c.T, T), (c.AP, AP),
                       (c.CP, CP), (c.K1, k1), (c.K2, k2), (c.K3, k3)):
        for i, v in zip(cols, vals):
            r0[i] = v
    r0[c.W] = W0
    rows.append(r0)
    # phase 1
    r1 = [0] * c.NCOLS
    r1[c.ONE], r1[c.PHI], r1[c.PSI], r1[c.RHO], r1[c.ZERO] = 1, 1, 0, kmul(rho, GAMMA), 0
    P, Q, Mb, CB = kbytes(a1), kbytes(b1), kbytes(Y), kbytes(c1)
    T, k1 = add_bytes(P, Q)
    AP, k2 = add_bytes(T, Mb)
    if fault and fault[0] == "a2top":        # a wrong top byte of a2 (no lookup checks it)
        AP[3] ^= fault[1]
    if fault and fault[0] == "a2low":        # a wrong low byte of a2, served by a false table row
        AP[0] ^= 1
    a2 = pack(AP)
    d2 = rotr(d1 ^ a2, 8)
    DP = kbytes(d2)
    CP, k3 = add_bytes(CB, DP)
    c2 = pack(CP)
    v = b1 ^ c2
    W1v = (v >> 7) & 1
    b2 = rotr(v, 7)
    for cols, vals in ((c.P, P), (c.Q, Q), (c.M, Mb), (c.CB, CB), (c.DP, DP), (c.T, T), (c.AP, AP),
                       (c.CP, CP), (c.K1, k1), (c.K2, k2), (c.K3, k3)):
        for i, val in zip(cols, vals):
            r1[i] = val
    r1[c.W] = W1v
    r1[c.A], r1[c.B], r1[c.C], r1[c.D] = a2, b2, c2, d2
    if fault and fault[0] == "c2out":        # a wrong packed output c2 (its gate dropped)
        r1[c.C] ^= fault[1]
    if fault and fault[0] == "b2out":        # a wrong output b2 through a wrong wrap cell
        r1[c.B] = b2 ^ fault[1]
        r1[c.W] = W1v ^ kmul(kinv(1 ^ (1 << 32)), fault[1])
    rows.append(r1)
    # self-checks of the two non-obvious linear constraints (b1, out_B) against the rotations
    lhs = sum(Qn << (8 * j) for j, Qn in enumerate(kbytes(b1)))
    rhs = 0
    ub = [x ^ y for x, y in zip(kbytes(B), kbytes(c1))]
    for j in range(4):
        rhs ^= ub[(j + 2) % 4] << (8 * j + 4)
    rhs ^= kmul(1 ^ (1 << 32), W0)
    assert lhs == rhs, "b1"
    vb = [x ^ y for x, y in zip(kbytes(b1), kbytes(c2))]
    rhs = 0
    for j in range(4):
        rhs ^= vb[(j + 1) % 4] << (8 * j + 1)
    rhs ^= kmul(1 ^ (1 << 32), W1v)
    assert rhs == b2, "b2"
    return rows, (r1[c.A], r1[c.B], r1[c.C], r1[c.D])


def mix_ref(a, b, c, d, x, y):
    """RFC 7693 G (Contract/Hash/Blake2s.lean `mix`), on four words."""
    a = (a + b + x) & M32
    d = rotr(d ^ a, 16)
    c = (c + d) & M32
    b = rotr(b ^ c, 12)
    a = (a + b + y) & M32
    d = rotr(d ^ a, 8)
    c = (c + d) & M32
    b = rotr(b ^ c, 7)
    return a, b, c, d


def chain_witness(n, secret, fault=None, restart=None):
    """The honest witness of L_chain(n) for the 32-byte start `secret` (or a faulty one); returns
    (tables, statement, digests). Tables are lists of rows of ints, in chip order; fixed ADD8 is
    `None` (its fixed table)."""
    G, S, F = [], [[] for _ in range(20)], []
    m = words_of(secret)
    digests = []
    rho = 1                                   # gamma^(2q) for the current G-call q
    g2, g160 = g(2), g(160)
    kap_s = [g(8 * (s - 1)) for s in range(20)]    # kappa of S_s at compression i
    kap_f = g(152)
    for i in range(n):
        if restart and i == restart[0]:      # selpin mutant: compression i starts from a fresh s'
            m = words_of(restart[1])
        v = list(INIT)
        for s in range(20):
            cm, names = s_cols(s)
            row = [0] * len(names)
            row[cm["one"]] = 1
            kap = kap_s[s]
            kap_s[s] = kmul(kap, g160)
            row[cm["kappa"]] = kap
            if s >= 1:
                for gi in range(4):
                    row[cm[f"tin{gi}"]] = kmul(kap, g(2 * gi + 1))
            for gi in range(4):
                row[cm[f"tout{gi}"]] = kmul(kap, g(8 + 2 * gi))
            for w in range(16):
                row[cm[f"V{w}"]] = v[w]
            for w in range(8):
                row[cm[f"m{w}"]] = m[w]
            if s == 0:
                row[cm["nf"]] = 0 if i == 0 else 1
            S[s].append(row)
            for gi in range(4):
                q = 80 * i + 4 * s + gi
                a, b, c_, d = quad(s % 2, gi)
                xi, yi = msg_idx(s, gi)
                X = m[xi] if xi < 8 else 0
                Y = m[yi] if yi < 8 else 0
                fl = fault[1] if fault and fault[0] == q else None
                rows, out = g_rows(q, v[a], v[b], v[c_], v[d], X, Y, fl, rho)
                rho = kmul(rho, g2)
                if fl is None:
                    assert out == mix_ref(v[a], v[b], v[c_], v[d], X, Y)
                G.extend(rows)
                v[a], v[b], v[c_], v[d] = out
        if fault and fault[0] == "swap" and i == n - 1:    # GOUT without tags: slots 0, 1 swapped
            q0, q1 = quad(1, 0), quad(1, 1)
            o0 = [v[w] for w in q0]
            o1 = [v[w] for w in q1]
            for w, val in zip(q0, o1):
                v[w] = val
            for w, val in zip(q1, o0):
                v[w] = val
        cm, names = f_cols()
        row = [0] * len(names)
        row[cm["one"]] = 1
        row[cm["nl"]], row[cm["la"]] = (0, 1) if i == n - 1 else (1, 0)
        kap = kap_f
        kap_f = kmul(kap_f, g160)
        row[cm["kappa"]] = kap
        for gi in range(4):
            row[cm[f"tin{gi}"]] = kmul(kap, g(2 * gi + 1))
        for w in range(16):
            row[cm[f"V{w}"]] = v[w]
        Hd = [H0[k] ^ v[k] ^ v[k + 8] for k in range(8)]
        for k in range(8):
            row[cm[f"H{k}"]] = Hd[k]
        for k in range(4, 8):
            for j, bt in enumerate(kbytes(Hd[k])[:3] + [Hd[k] >> 24]):   # (top byte unmasked)
                row[cm[f"E{k}_{j}"]] = bt
        F.append(row)
        if not fault:
            ref = hashlib.blake2s(bytes_of(m), digest_size=32).digest()
            assert bytes_of(Hd) == ref, f"compression {i} disagrees with hashlib"
        digests.append(bytes_of([h & M32 for h in Hd]) if fault else bytes_of(Hd))
        m = Hd
    y = m
    x = [y[2 * k] ^ (y[2 * k + 1] << 32) for k in range(4)] + [n] + [0] * 27
    pub = x + y + [1]
    nib = [[1, v_] for v_ in range(16)]
    tables = [[pub], G, None, nib] + S + [F]
    return tables, x, digests


# ---------------------------------------------------------------- the one-G-call harness

PUBG_E = 35      # PUBG columns 35 + 4i + j: byte j of output word i (statement cell 6 + i)


def mini_layout(call_inputs, rows_used):
    """Chips: PUBG (public: the call's inputs and outputs; the outputs decomposed into bytes,
    range-checked on `PAIR`, as FINAL does in L_chain), G (one call), ADD8 (trimmed to `rows_used`,
    or full when None), NIB."""
    names = [f"x{i}" for i in range(32)] + ["one", "tag0", "tag1"] \
        + [f"E{6 + i}_{j}" for i in range(4) for j in range(4)]
    gd = Gadget(len(names))
    gd.con("one", gd.always(), [(32, 1), (gd.ONE, 1)])
    gd.con("tag0", gd.always(), [(33, 1), (gd.ONE, 1)])
    gd.con("tag1", gd.always(), [(34, 1), (gd.ONE, GAMMA)])
    for i in range(10, 32):
        gd.con(f"x{i}", gd.always(), [(i, 1)])
    for i in range(4):
        gd.con(f"out{i}", gd.always(), [(6 + i, 1)] + [(PUBG_E + 4 * i + j, bx(j)) for j in range(4)])
    ports = [port(GIN, True, 32, [33, 0, 1, 2, 3, 4, 5]), port(GOUT, False, 32, [34, 6, 7, 8, 9])]
    for i in range(4):
        e = PUBG_E + 4 * i
        ports += [port(PAIR, False, 32, [e, e + 1]), port(PAIR, False, 32, [e + 2, e + 3])]
    pubg = chip("PUBG", len(names), names, gd, ports)
    if rows_used is None:
        fixed = {"kind": "add8"}
    else:
        fixed = {"kind": "explicit", "rows": [[hx(v) for v in add_row(r)] for r in rows_used],
                 "note": "add8 rows used by the witness, in add8 order"}
    return {"schema": "recursion.fast/layout/1", "name": "L_G (one G-call harness)",
            "params": {"calls": 1, "gamma": hx(GAMMA), "inputs": [hx(v) for v in call_inputs]},
            "chips": [pubg, g_chip(1), add_chip(fixed), nib_chip()],
            "bus": BUS_KINDS, "busnames": BUS_NAMES, "pub": 0}


def call_inputs_of(secret, q):
    """The inputs (a, b, c, d, x, y) of G-call q of the chain started at `secret` (q < 80·…)."""
    m = words_of(secret)
    i, rest = divmod(q, 80)
    for _ in range(i):
        m = words_of(hashlib.blake2s(bytes_of(m), digest_size=32).digest())
    v = list(INIT)
    for qq in range(rest + 1):
        s, gi = divmod(qq, 4)
        a, b, c_, d = quad(s % 2, gi)
        xi, yi = msg_idx(s, gi)
        X = m[xi] if xi < 8 else 0
        Y = m[yi] if yi < 8 else 0
        if qq == rest:
            return (v[a], v[b], v[c_], v[d], X, Y)
        v[a], v[b], v[c_], v[d] = mix_ref(v[a], v[b], v[c_], v[d], X, Y)


def add_rows_of(grows, outs=()):
    """The add8 rows a G-call's lookups use, and (cin = 0) rows for the byte pairs of `outs`."""
    used = set()
    for w in outs:
        b = kbytes(w)
        used.add(b[0] | b[1] << 8)
        used.add(b[2] | b[3] << 8)
    c = GCols
    for row in grows:
        for (xs, ys, zs, ks) in c.SLOTS:
            cin = 0
            for j in range(4):
                used.add(row[xs[j]] | (row[ys[j]] << 8) | (cin << 16))
                if j < 3:
                    cin = row[ks[j]]
    return sorted(used)


# ---------------------------------------------------------------- output

def table_json(rows):
    if rows is None:
        return {"kind": "add8"}
    if isinstance(rows, tuple):              # ("add8", extra rows): the add table, then extra rows
        return {"kind": "add8", "extra": [[hx(v) for v in r] for r in rows[1]]}
    return {"rows": len(rows), "cells": [[hx(v) for v in r] for r in rows]}


def dump(obj, path):
    with open(path, "w") as f:
        json.dump(obj, f, separators=(",", ":"))


def witness_json(tables):
    return {"schema": "recursion.fast/witness/1", "tables": [table_json(t) for t in tables]}


def stmt_json(x, extra=None):
    d = {"schema": "recursion.fast/statement/1", "x": [hx(v) for v in x]}
    if extra:
        d.update(extra)
    return d


def cells_report(n):
    lay = chain_layout(n)
    heights = {"PUB": 1, "G": 160 * n, "ADD8": ADD_ROWS, "NIB": 16, "FINAL": n}
    per = []
    for ch in lay["chips"]:
        h = heights.get(ch["name"], n)
        per.append((ch["name"], ch["cols"], h, ch["cols"] * h))
    total = sum(p[3] for p in per)
    fixed = ADD_ROWS * 6 + 16 * 2
    entries = sum(len(m) for ch in lay["chips"] for m in ch["gadget"]["M"])
    kc = (total - 1).bit_length()
    kf = (fixed - 1).bit_length() + 4
    return per, total, fixed, entries, max(kc, kf), kc, kf


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("layout"); p.add_argument("--n", type=int, required=True); p.add_argument("out")
    p.add_argument("--k", type=int, help="refuse unless L_chain(n) fits class k (cells and fixed-table cap)")
    p = sub.add_parser("witness"); p.add_argument("--n", type=int, required=True)
    p.add_argument("--k", type=int, help="refuse unless L_chain(n) fits class k")
    p.add_argument("--secret-file", required=True); p.add_argument("out_wit"); p.add_argument("out_stmt")
    p = sub.add_parser("mini"); p.add_argument("--secret-file", required=True)
    p.add_argument("--call", type=int, default=0); p.add_argument("--full-table", action="store_true")
    p.add_argument("out_layout"); p.add_argument("out_wit"); p.add_argument("out_stmt")
    p = sub.add_parser("mutant"); p.add_argument("--kind", required=True, choices=MUTANTS)
    p.add_argument("--n", type=int, required=True); p.add_argument("--secret-file", required=True)
    p.add_argument("out_layout"); p.add_argument("out_wit"); p.add_argument("out_stmt")
    p = sub.add_parser("report"); p.add_argument("--n", type=int, nargs="*", default=[2 ** 8, 2 ** 10, 2 ** 11, 2 ** 12])
    a = ap.parse_args()

    def secret_bytes(path):
        """The secret start: 64 hex digits in a file, or on stdin for `-` (never an argument)."""
        txt = sys.stdin.read() if path == "-" else open(path).read()
        try:
            b = bytes.fromhex(txt.strip())
        except ValueError:
            b = b""
        if len(b) != 32:
            raise SystemExit("secret: 32 bytes, written as 64 hex digits")
        return b

    if getattr(a, "n", None) is not None and not isinstance(a.n, list) and a.n < 1:
        raise SystemExit("n >= 1")
    if a.cmd in ("layout", "witness") and a.k is not None:
        _, total, fixed, _, kmin, _, _ = cells_report(a.n)
        if a.k < kmin:
            raise SystemExit(f"L_chain({a.n}) has {total} cells and {fixed} fixed cells: it needs class "
                             f">= {kmin}, not {a.k}")
    if a.cmd == "layout":
        dump(chain_layout(a.n), a.out)
    elif a.cmd == "witness":
        tables, x, _ = chain_witness(a.n, secret_bytes(a.secret_file))
        dump(witness_json(tables), a.out_wit)
        dump(stmt_json(x, {"n": a.n}), a.out_stmt)
    elif a.cmd == "mini":
        sec = secret_bytes(a.secret_file)
        ins = call_inputs_of(sec, a.call)
        rows, out = g_rows(0, *ins)
        assert out == mix_ref(*ins)
        used = add_rows_of(rows, out)
        lay = mini_layout(ins, None if a.full_table else used)
        x = list(ins) + list(out) + [0] * 22
        pubg = x + [1, 1, GAMMA] + [b for w in out for b in kbytes(w)]
        addt = None if a.full_table else [add_row(r) for r in used]
        tables = [[pubg], rows, addt, [[1, v_] for v_ in range(16)]]
        dump(lay, a.out_layout)
        dump(witness_json(tables), a.out_wit)
        dump(stmt_json(x, {"call": a.call}), a.out_stmt)
    elif a.cmd == "mutant":
        sec = secret_bytes(a.secret_file)
        n = a.n
        if n < (2 if a.kind in ("nolast", "selpin") else 1):
            raise SystemExit("n >= 1 (n >= 2 for nolast, selpin)")
        qlast = 80 * n - 1
        fault = {"gate": (qlast, ("c2out", 1)), "addport": (qlast, ("a2top", 0x5A)),
                 "nibport": (qlast, ("b2out", 0x12345)), "gouttag": ("swap", None),
                 "fixed": (qlast, ("a2low", None)),
                 "pairport": (qlast, ("b2out", 1 | 1 << 32))}.get(a.kind)
        if a.kind == "nolast":       # heights unpinned: the (n-1)-chain claimed as n
            tables, x, _ = chain_witness(n - 1, sec)
            x[4] = n
            tables[0][0][4] = n
        elif a.kind == "selpin":     # selectors unpinned: the last compression restarts from s'
            tables, x, _ = chain_witness(n, sec, restart=(n - 1, bytes(b ^ 0xA5 for b in sec)))
            fc, _ = f_cols()
            sc, _ = s_cols(0)
            tables[-1][n - 2][fc["nl"]] = 2          # X: FINAL row n-2 sends no MSG (silent)
            tables[4][n - 1][sc["nf"]] = 2           # X: S0 row n-1 receives none
        else:
            tables, x, _ = chain_witness(n, sec, fault)
        if a.kind == "fixed":        # ADD8 not fixed: a false add row serves byte 0 of the wrong a2
            c = GCols
            r1 = tables[1][-1]
            tables[2] = ("add8", [[1, r1[c.T[0]], r1[c.M[0]], 0, r1[c.AP[0]], r1[c.K2[0]]]])
        dump(chain_layout(n, a.kind), a.out_layout)
        dump(witness_json(tables), a.out_wit)
        dump(stmt_json(x, {"n": n, "mutant": a.kind}), a.out_stmt)
    elif a.cmd == "report":
        assert all(kpow(GAMMA, ORDER // p) != 1 for p in [3, 5, 17, 257, 641, 65537, 6700417])
        print("gamma = X is a generator of K* (order 2^64 - 1)")
        for n in a.n:
            per, total, fixed, entries, k, kc, kf = cells_report(n)
            print(f"\nn = {n}: cells {total} (2^{total.bit_length() - 1}.. ), fixed cells {fixed}, "
                  f"gadget entries {entries}; least class k = {k} (cells need {kc}, fixed table needs {kf})")
            agg = {}
            for name, cols, h, cells in per:
                key = "S0..S19" if name.startswith("S") else name
                c0, h0, ce = agg.get(key, (0, h, 0))
                agg[key] = (c0 + cols if key == "S0..S19" else cols, h, ce + cells)
            for key, (cols, h, cells) in agg.items():
                print(f"  {key:8} cols {cols:5}  rows {h:9}  cells {cells:10}  ({cells / n:9.1f} per compression)")


if __name__ == "__main__":
    main()
