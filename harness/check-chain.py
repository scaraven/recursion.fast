#!/usr/bin/env python3
"""check-chain.py: a pure-Python evaluator of `Layout.rel` and `Layout.Admissible`
(`RecursionFast/Contract/Layout.lean`), the differential oracle for the benchmark layout L_chain(n).

It shares no code with the generator: it reads the JSON files (schemas in `harness/README.md`) and
evaluates the contract's definitions clause by clause, as written in Lean:

  rowDot M z r   = sum of v * z[c] over the entries (r', c, v) of M with r' = r, in list order
  Gadget.holds   = for every r < cons: sum_i c_i * prod_{j in S_i} rowDot (M_j) z r = 0
  view C T r     = row r, row (r + 1) mod rows, then 1, [r = 0], [r + 1 = rows]
  Table.msgs T p = for r < rows with cell r sel = 1 (in order): the cells of p.msg
  traffic L w b s= the messages of the ports on bus b with direction s, over zip(chips, w)
  balanced       = eq: equal multisets (counted in N); sub: every received message is sent
  rel            = |w| = |chips|; fixed tables; every gadget on every row; every bus b balances;
                   the public table has a row whose cells 0..31 are x; sum rows*cols <= 2^k

K = GF(2^64) = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1): `+` is xor, `*` the reduced carry-less product
(Field.lean, with the same two folds). A table's cell outside its listed rows x cells is 0 (the
rendering convention of `harness/render-layout.py`; `rel` does not read such cells of an
admissible layout, Library/Layout.lean `rel_trim_iff`).

Commands (run with `python3 -I`):
  check LAYOUT WITNESS STMT --k K       evaluate Admissible and rel, clause by clause
  experiments --gen GEN --dir DIR [--n 4 16 256] [--seeds S] [--mutations M] [--log LOG]
      the differential tests (a)-(c) of Stage 6a, generating instances with GEN
      (harness/gen-chain-layout.py) in DIR
"""
import argparse, collections, hashlib, json, os, random, subprocess, sys, time

MASK64 = (1 << 64) - 1


def clmul(a, b):
    if a.bit_count() > b.bit_count():
        a, b = b, a
    r = 0
    while a:
        low = a & -a
        r ^= b << (low.bit_length() - 1)
        a ^= low
    return r


def kmul(a, b):
    """Field.lean `K.mul`: clmul, then reduce = fold (fold t) with fold t = clmul (t >> 64) 0x1B ^ low."""
    if a == 0 or b == 0:
        return 0
    if a == 1:
        return b
    if b == 1:
        return a
    t = clmul(a, b)
    for _ in range(2):
        t = clmul(t >> 64, 0x1B) ^ (t & MASK64)
    return t & MASK64


def kmul_ref(a, b):
    """The definition, bit by bit (Field.lean `clmul` folds over the 64 bits of `a`)."""
    acc = 0
    for i in range(64):
        if (a >> i) & 1:
            acc ^= (b << i) & ((1 << 128) - 1)
    for _ in range(2):
        hi = acc >> 64
        f = 0
        for i in range(64):
            if (hi >> i) & 1:
                f ^= (0x1B << i) & ((1 << 128) - 1)
        acc = f ^ (acc & MASK64)
    return acc & MASK64


def kel(h):
    if type(h) is not str or len(h) != 16 or any(ch not in "0123456789abcdef" for ch in h):
        raise ValueError(f"not a K element (16 lowercase hex digits): {h!r}")
    return int(h, 16)


# ---------------------------------------------------------------- tables

def add8_cell(r, c):
    x, y, ci = r & 0xFF, (r >> 8) & 0xFF, r >> 16
    s = x + y + ci
    return (1, x, y, ci, s & 0xFF, s >> 8)[c] if c < 6 else 0


class Tab:
    """A table: `rows` and a cell function (0 outside the listed data)."""

    def __init__(self, rows, data=None, fn=None, fnrows=0):
        self.rows, self.data, self.fn, self.fnrows = rows, data, fn, fnrows

    def cell(self, r, c):
        if self.fn is not None and r < self.fnrows:
            return self.fn(r, c)
        d = self.data
        if d is None:
            return 0
        rr = r - self.fnrows
        if 0 <= rr < len(d) and c < len(d[rr]):
            return d[rr][c]
        return 0

    def row(self, r, cols):
        if self.fn is not None and r < self.fnrows:
            return [self.fn(r, c) for c in range(cols)]
        rr = r - self.fnrows
        if self.data is not None and 0 <= rr < len(self.data):
            row = self.data[rr]
            return (row + [0] * cols)[:cols] if len(row) < cols else row[:cols]
        return [0] * cols


def table_of(spec, what):
    """A table from its JSON form: {"rows", "cells"} (explicit), or {"kind": "add8"[, "extra"]}, or
    for fixed tables {"kind": "explicit", "rows": [...]}."""
    if "kind" in spec:
        if spec["kind"] == "add8":
            extra = [[kel(v) for v in row] for row in spec.get("extra", [])]
            return Tab((1 << 17) + len(extra), extra or None, add8_cell, 1 << 17)
        if spec["kind"] == "explicit":
            rows = [[kel(v) for v in row] for row in spec["rows"]]
            return Tab(len(rows), rows)
        raise ValueError(f"{what}: unknown table kind {spec['kind']!r}")
    rows = [[kel(v) for v in row] for row in spec["cells"]]
    if spec["rows"] != len(rows):
        raise ValueError(f"{what}: rows {spec['rows']} but {len(rows)} rows listed")
    return Tab(len(rows), rows)


# ---------------------------------------------------------------- the layout

class Chip:
    pass


def load_layout(j):
    """Parse and type-check (the JSON must denote a Lean `Layout K`: `M j` entries in
    `Fin cons × Fin width × K`, `S i` entries in `Fin t`, |M| = t, |S| = |c| = q)."""
    if j.get("schema") != "recursion.fast/layout/1":
        raise ValueError("layout: unknown schema")
    chips = []
    for ci, cj in enumerate(j["chips"]):
        C = Chip()
        C.name, C.cols = cj.get("name", str(ci)), cj["cols"]
        gj = cj["gadget"]
        C.cons, C.t, C.q = gj["cons"], gj["t"], gj["q"]
        width = 2 * C.cols + 3
        if len(gj["M"]) != C.t or len(gj["S"]) != C.q or len(gj["c"]) != C.q:
            raise ValueError(f"chip {C.name}: |M| != t or |S|, |c| != q")
        C.M = []
        for m in gj["M"]:
            ent = []
            for (r, c, v) in m:
                if not (0 <= r < C.cons and 0 <= c < width):
                    raise ValueError(f"chip {C.name}: entry ({r}, {c}) outside Fin {C.cons} x Fin {width}")
                ent.append((r, c, kel(v)))
            C.M.append(ent)
        C.S = []
        for s in gj["S"]:
            if not all(0 <= j_ < C.t for j_ in s):
                raise ValueError(f"chip {C.name}: S entry outside Fin {C.t}")
            C.S.append(list(s))
        C.c = [kel(v) for v in gj["c"]]
        # rowDot's filter, grouped by row (order kept): by_row[j][r] = [(c, v), ...]
        C.by_row = []
        for ent in C.M:
            d = [[] for _ in range(C.cons)]
            for (r, c, v) in ent:
                d[r].append((c, v))
            C.by_row.append(d)
        C.ports = [(p["bus"], bool(p["send"]), p["sel"], tuple(p["msg"])) for p in cj["ports"]]
        C.fixed = None if cj["fixed"] is None else table_of(cj["fixed"], f"chip {C.name} fixed")
        C.fixed_spec = cj["fixed"]
        chips.append(C)
    kinds = j["bus"]
    if not all(k in ("eq", "sub") for k in kinds):
        raise ValueError("bus kinds: eq or sub")
    return {"chips": chips, "bus": kinds, "pub": j["pub"], "name": j.get("name", "")}


def bus_kind(L, b):
    return L["bus"][b] if b < len(L["bus"]) else "eq"


def admissible(L, k):
    """`Layout.Admissible k`, conjunct by conjunct."""
    ch = L["chips"]
    res = collections.OrderedDict()
    res["chips <= 2^8"] = len(ch) <= 2 ** 8
    pubc = ch[L["pub"]] if L["pub"] < len(ch) else None
    res["public chip has >= 32 cols"] = pubc is not None and pubc.cols >= 32
    entries = sum(len(m) for C in ch for m in C.M)
    res[f"entries {entries} <= 2^(k+4)"] = entries <= 2 ** (k + 4)
    fixed = sum(C.fixed.rows * C.cols for C in ch if C.fixed is not None)
    res[f"fixed cells {fixed} <= 2^(k-4)"] = fixed <= 2 ** max(k - 4, 0)
    ok = True
    for C in ch:
        ok &= 1 <= C.cols <= 2 ** 10 and C.t <= 2 ** 6 and C.cons <= 2 ** 8 and C.q <= 2 ** 8
        ok &= all(len(s) <= 8 for s in C.S) and len(C.ports) <= 2 ** 5
        ok &= all(b < 2 ** 8 and sel < C.cols and len(msg) <= 2 ** 4 and all(c < C.cols for c in msg)
                  for (b, _, sel, msg) in C.ports)
    res["every chip admissible"] = ok
    return res


# ---------------------------------------------------------------- the relation

def view(C, T, r):
    return T.row(r, C.cols) + T.row((r + 1) % T.rows, C.cols) + [1, 1 if r == 0 else 0,
                                                                  1 if r + 1 == T.rows else 0]


def holds_at(C, z):
    """`Gadget.holds`: None if every constraint holds, else the first failing constraint."""
    for r in range(C.cons):
        acc = 0
        for i in range(C.q):
            p = 1
            for j in reversed(C.S[i]):           # List.prod = foldr (*) 1
                rd = 0
                for (c, v) in C.by_row[j][r]:
                    zc = z[c]
                    rd ^= zc if v == 1 else kmul(v, zc)
                p = kmul(rd, p)
            acc ^= kmul(C.c[i], p)
        if acc != 0:
            return r
    return None


def msgs(T, port):
    _, _, sel, msg = port
    return [tuple(T.cell(r, c) for c in msg) for r in range(T.rows) if T.cell(r, sel) == 1]


def all_buses(L):
    return sorted({p[0] for C in L["chips"] for p in C.ports})


def traffic(L, w, b, send, cache=None):
    out = []
    for ci, (C, T) in enumerate(zip(L["chips"], w)):
        for pi, p in enumerate(C.ports):
            if p[0] == b and p[1] == send:
                if cache is not None and (ci, pi) in cache:
                    out.extend(cache[(ci, pi)])
                else:
                    out.extend(msgs(T, p))
    return out


def balanced(kind, s, r):
    if kind == "eq":
        return collections.Counter(s) == collections.Counter(r)
    ss = set(s)
    return all(m in ss for m in r)


def rel(L, k, x, w, stop=False):
    """`Layout.rel L k x w`, clause by clause: an OrderedDict clause -> (bool, detail)."""
    ch = L["chips"]
    res = collections.OrderedDict()
    res["length"] = (len(w) == len(ch), f"{len(w)} tables, {len(ch)} chips")
    bad = None
    for C, T in zip(ch, w):
        if C.fixed is not None:
            t = C.fixed
            if T.rows != t.rows:
                bad = f"{C.name}: height {T.rows} != {t.rows}"
                break
            if T is t:
                continue
            for r in range(t.rows):
                if T.row(r, C.cols) != t.row(r, C.cols):
                    bad = f"{C.name}: row {r} differs from the fixed table"
                    break
            if bad:
                break
    res["fixed"] = (bad is None, bad or "")
    if stop and not all(v for v, _ in res.values()):
        return res
    bad = None
    for C, T in zip(ch, w):
        if C.cons == 0:
            continue
        for r in range(T.rows):
            f = holds_at(C, view(C, T, r))
            if f is not None:
                bad = f"{C.name}: row {r}, constraint {f}"
                break
        if bad:
            break
    res["gadget"] = (bad is None, bad or "")
    if stop and not all(v for v, _ in res.values()):
        return res
    bad = []
    for b in all_buses(L):          # a bus no port uses carries nothing and balances (traffic_eq_zero)
        s, r = traffic(L, w, b, True), traffic(L, w, b, False)
        if not balanced(bus_kind(L, b), s, r):
            bad.append(f"bus {b} ({bus_kind(L, b)}): {len(s)} sent, {len(r)} received")
    res["bus"] = (not bad, "; ".join(bad))
    pub = L["pub"]
    ok = pub < len(w) and w[pub].rows >= 1 and all(w[pub].cell(0, i) == x[i] for i in range(32))
    res["public"] = (ok, "")
    cells = sum(T.rows * C.cols for C, T in zip(ch, w))
    res["cells"] = (cells <= 2 ** k, f"{cells} cells, 2^{k} = {2 ** k}")
    return res


def holds_all(res):
    return all(v for v, _ in res.values())


# ---------------------------------------------------------------- incremental re-evaluation (b)

class Incremental:
    """`rel` with per-row gadget results and per-port messages cached, for single-cell mutations.
    Equivalent to `rel` (cross-checked against it on the small instances)."""

    def __init__(self, L, k, x, w):
        self.L, self.k, self.x, self.w = L, k, x, w
        ch = L["chips"]
        self.bad_rows = {}                        # (chip, row) -> failing constraint
        for ci, (C, T) in enumerate(zip(ch, w)):
            if C.cons:
                for r in range(T.rows):
                    f = holds_at(C, view(C, T, r))
                    if f is not None:
                        self.bad_rows[(ci, r)] = f
        self.cnt = collections.defaultdict(collections.Counter)  # (bus, send) -> Counter
        for ci, (C, T) in enumerate(zip(ch, w)):
            for p in C.ports:
                for m in msgs(T, p):
                    self.cnt[(p[0], p[1])][m] += 1

    def bus_ok(self, b):
        s, r = self.cnt[(b, True)], self.cnt[(b, False)]
        if bus_kind(self.L, b) == "eq":
            return +s == +r
        return all(m in s and s[m] > 0 for m, v in r.items() if v > 0)

    def mutate(self, ci, r, c, val):
        """Set cell (r, c) of table ci to val (an explicit table); return the failing clauses."""
        C, T = self.L["chips"][ci], self.w[ci]
        row_msgs = lambda: [(p, tuple(T.cell(r, cc) for cc in p[3]) if T.cell(r, p[2]) == 1 else None)
                            for p in C.ports]
        old = row_msgs()
        rr = r - T.fnrows
        prev = T.data[rr][c]
        T.data[rr][c] = val
        new = row_msgs()
        for (p, m) in old:
            if m is not None:
                self.cnt[(p[0], p[1])][m] -= 1
        for (p, m) in new:
            if m is not None:
                self.cnt[(p[0], p[1])][m] += 1
        failing = []
        if C.fixed is not None and r < C.fixed.rows and c < C.cols and C.fixed.cell(r, c) != val:
            failing.append("fixed")
        g_bad = {key: v for key, v in self.bad_rows.items()}
        for rr2 in {(r - 1) % T.rows, r}:
            if C.cons:
                f = holds_at(C, view(C, T, rr2))
                g_bad.pop((ci, rr2), None)
                if f is not None:
                    g_bad[(ci, rr2)] = f
        if g_bad:
            failing.append("gadget")
        if not all(self.bus_ok(b) for b in {p[0] for p in C.ports}):
            failing.append("bus")
        pub = self.L["pub"]
        if ci == pub and r == 0 and c < 32 and val != self.x[c]:
            failing.append("public")
        # revert
        for (p, m) in new:
            if m is not None:
                self.cnt[(p[0], p[1])][m] -= 1
        for (p, m) in old:
            if m is not None:
                self.cnt[(p[0], p[1])][m] += 1
        T.data[rr][c] = prev
        return failing


# ---------------------------------------------------------------- files

def load(path):
    with open(path) as f:
        return json.load(f)


def load_instance(lp, wp, xp):
    L = load_layout(load(lp))
    wj, xj = load(wp), load(xp)
    if wj.get("schema") != "recursion.fast/witness/1" or xj.get("schema") != "recursion.fast/statement/1":
        raise ValueError("witness/statement: unknown schema")
    w = [table_of(t, f"table {i}") for i, t in enumerate(wj["tables"])]
    x = [kel(v) for v in xj["x"]]
    if len(x) != 32:
        raise ValueError("statement: 32 elements")
    return L, x, w, xj


def chain_ref(secret, n):
    d = secret
    for _ in range(n):
        d = hashlib.blake2s(d, digest_size=32).digest()
    return d


def stmt_y(x):
    return b"".join(v.to_bytes(8, "little") for v in x[:4])


# ---------------------------------------------------------------- experiments

def log(f, *a):
    s = " ".join(str(v) for v in a)
    print(s, flush=True)
    if f:
        f.write(s + "\n")
        f.flush()


def gen(genpath, *args, secret=None):
    """Run the generator; the secret goes through stdin (`--secret-file -`), never argv."""
    if secret is not None:
        args = args[:1] + ("--secret-file", "-") + args[1:]
    subprocess.run([sys.executable, "-I", genpath] + [str(a) for a in args], check=True,
                   input=None if secret is None else secret.hex(), text=True)


def layout_diff(A, B):
    """What differs between two layout JSONs: a list of short descriptions."""
    out = []
    if A["bus"] != B["bus"] or A["pub"] != B["pub"]:
        out.append("bus kinds or pub")
    for ca, cb in zip(A["chips"], B["chips"]):
        if ca == cb:
            continue
        nm = ca["name"]
        ga, gb = ca["gadget"], cb["gadget"]
        for j, (ma, mb) in enumerate(zip(ga["M"], gb["M"])):
            sa, sb = set(map(tuple, ma)), set(map(tuple, mb))
            if sa != sb:
                out.append(f"{nm}: M{j} entries removed {sorted(sa - sb)}, added {sorted(sb - sa)}")
        if len(ca["ports"]) != len(cb["ports"]):
            gone = [p for p in ca["ports"] if p not in cb["ports"]]
            out.append(f"{nm}: ports removed {gone}")
        else:
            for pa, pb in zip(ca["ports"], cb["ports"]):
                if pa != pb:
                    if dict(pa, msg=pa["msg"][1:]) == pb:
                        out.append(f"bus {pa['bus']}: first message column (the tag) dropped")
                    else:
                        out.append(f"{nm}: port {pa} -> {pb}")
        if ca["fixed"] != cb["fixed"]:
            out.append(f"{nm}: fixed {'set' if ca['fixed'] else 'none'} -> {'set' if cb['fixed'] else 'none'}")
    if len(A["chips"]) != len(B["chips"]):
        out.append("chip count")
    c = collections.Counter(out)
    return [f"{d} (x{m})" if m > 1 else d for d, m in c.items()]


def least_class(L, w):
    cells = sum(T.rows * C.cols for C, T in zip(L["chips"], w))
    kc = (cells - 1).bit_length()
    k = kc
    while not all(admissible(L, k).values()):
        k += 1
    return k, cells, kc


def experiments(a):
    os.makedirs(a.dir, exist_ok=True)
    lf = open(a.log, "a") if a.log else None
    rng = random.Random(a.rng)
    # the arithmetic, against the bit-by-bit definition
    t0 = time.time()
    for _ in range(20000):
        u, v = rng.getrandbits(64), rng.getrandbits(rng.choice([1, 8, 33, 64]))
        assert kmul(u, v) == kmul_ref(u, v) == kmul(v, u)
    log(lf, f"K arithmetic: kmul = definition on 20000 random pairs ({time.time() - t0:.1f} s)")
    for n in a.n:
        log(lf, f"\n=== n = {n} ===")
        lp = os.path.join(a.dir, f"L{n}.json")
        t0 = time.time()
        gen(a.gen, "layout", "--n", n, lp)
        lj = load(lp)
        L = load_layout(lj)
        log(lf, f"layout: {len(L['chips'])} chips, {len(all_buses(L))} buses, "
                f"{sum(len(m) for C in L['chips'] for m in C.M)} gadget entries ({time.time() - t0:.1f} s)")
        # (a) honest instances
        for sd in range(a.seeds if n <= 16 else 1):
            secret = bytes(rng.getrandbits(8) for _ in range(32))
            wp, xp = os.path.join(a.dir, f"W{n}_{sd}.json"), os.path.join(a.dir, f"X{n}_{sd}.json")
            t0 = time.time()
            gen(a.gen, "witness", "--n", n, wp, xp, secret=secret)
            tg = time.time() - t0
            t0 = time.time()
            L, x, w, xj = load_instance(lp, wp, xp)
            tl = time.time() - t0
            k, cells, kc = least_class(L, w)
            t0 = time.time()
            r = rel(L, k, x, w)
            tr = time.time() - t0
            adm = admissible(L, k)
            adm1 = admissible(L, k - 1)
            y_ok = stmt_y(x) == chain_ref(secret, n)
            fmt_ok = x[4] == n and all(v == 0 for v in x[5:])
            log(lf, f"(a) secret {secret.hex()[:16]}..: rel {holds_all(r)} {dict((c, v) for c, (v, _) in r.items())}; "
                    f"Admissible {k}: {all(adm.values())}, Admissible {k - 1}: {all(adm1.values())}; "
                    f"y = blake2s256^{n}(s): {y_ok}; x = (y, n, 0..): {fmt_ok}; cells {cells} "
                    f"(cells alone need k = {kc}; least class {k}); gen {tg:.1f} s, load {tl:.1f} s, rel {tr:.1f} s")
            assert holds_all(r) and all(adm.values()) and y_ok and fmt_ok
            if sd == 0:
                base = (secret, wp, xp)
        # (b) single-cell mutations
        secret, wp, xp = base
        L, x, w, xj = load_instance(lp, wp, xp)
        k, _, _ = least_class(L, w)
        t0 = time.time()
        inc = Incremental(L, k, x, w)
        assert not inc.bad_rows
        t_init = time.time() - t0
        cand = []
        for ci, (C, T) in enumerate(zip(L["chips"], w)):
            if T.data is None:
                continue
            for _ in range(3):           # a few in every chip with explicit data ...
                cand.append((ci, T.fnrows + rng.randrange(len(T.data)), rng.randrange(C.cols)))
        tot = sum(len(T.data) * C.cols for C, T in zip(L["chips"], w) if T.data is not None)
        for _ in range(a.mutations):     # ... and uniformly over all explicit cells
            u = rng.randrange(tot)
            for ci, (C, T) in enumerate(zip(L["chips"], w)):
                if T.data is None:
                    continue
                sz = len(T.data) * C.cols
                if u < sz:
                    cand.append((ci, T.fnrows + u // C.cols, u % C.cols))
                    break
                u -= sz
        why = collections.Counter()
        t0 = time.time()
        survivors = []
        full_checked = 0
        for (ci, r_, c_) in cand:
            T = w[ci]
            old = T.data[r_ - T.fnrows][c_]
            for val in (old ^ 1, rng.getrandbits(64)):
                if val == old:
                    continue
                f = inc.mutate(ci, r_, c_, val)
                if n <= 16 and full_checked < 40:   # cross-check the incremental path with rel
                    T.data[r_ - T.fnrows][c_] = val
                    full = rel(L, k, x, w)
                    T.data[r_ - T.fnrows][c_] = old
                    assert holds_all(full) == (not f), (ci, r_, c_, f, full)
                    full_checked += 1
                if not f:
                    survivors.append((L["chips"][ci].name, r_, c_, val))
                for cl in f:
                    why[cl] += 1
        log(lf, f"(b) {2 * len(cand)} single-cell mutations over {len(cand)} cells "
                f"(every chip with explicit cells, then uniform): survivors {len(survivors)} {survivors[:5]}; "
                f"failing clauses {dict(why)}; {full_checked} cross-checked with the full rel; "
                f"{time.time() - t0 + t_init:.1f} s")
        assert not survivors
        # (c) mutated layouts admit wrong witnesses
        for kind in a.kinds:
            mlp, mwp, mxp = (os.path.join(a.dir, f"{p}{n}_{kind}.json") for p in ("ML", "MW", "MX"))
            t0 = time.time()
            gen(a.gen, "mutant", "--kind", kind, "--n", n, mlp, mwp, mxp, secret=secret)
            diff = layout_diff(lj, load(mlp))
            Lm, xm, wm, _ = load_instance(mlp, mwp, mxp)
            r_mut = rel(Lm, k, xm, wm)
            r_orig = rel(L, k, xm, wm)
            wrong = stmt_y(xm) != chain_ref(secret, n)
            log(lf, f"(c) {kind}: mutant = original with {diff}; rel(mutant, w', x') {holds_all(r_mut)}; "
                    f"rel(original, w', x') {holds_all(r_orig)} "
                    f"(fails: {[c for c, (v, _) in r_orig.items() if not v]} "
                    f"{[d for c, (v, d) in r_orig.items() if not v]}); "
                    f"y' != blake2s256^{n}(s): {wrong}; {time.time() - t0:.1f} s")
            assert holds_all(r_mut) and not holds_all(r_orig) and wrong and len(diff) >= 1
        log(lf, f"(c) {len(a.kinds)} mutants: each accepts a wrong chain that the real layout rejects")
    if lf:
        lf.close()


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("check")
    p.add_argument("layout"); p.add_argument("witness"); p.add_argument("stmt")
    p.add_argument("--k", type=int, required=True)
    p.add_argument("--flip", type=int, nargs=3, action="append", default=[], metavar=("TABLE", "ROW", "COL"),
                   help="xor 1 into a witness cell before checking (repeatable)")
    p.add_argument("--xflip", type=int, action="append", default=[], metavar="I",
                   help="xor 1 into statement cell I before checking (repeatable)")
    p.add_argument("--xor", nargs=4, action="append", default=[], metavar=("TABLE", "ROW", "COL", "HEX"),
                   help="xor the K element HEX into a witness cell (repeatable)")
    p.add_argument("--xxor", nargs=2, action="append", default=[], metavar=("I", "HEX"),
                   help="xor the K element HEX into statement cell I (repeatable)")
    p = sub.add_parser("experiments")
    p.add_argument("--gen", required=True); p.add_argument("--dir", required=True)
    p.add_argument("--n", type=int, nargs="+", default=[4, 16, 256])
    p.add_argument("--seeds", type=int, default=3); p.add_argument("--mutations", type=int, default=200)
    p.add_argument("--kinds", nargs="*", default=["gate", "addport", "nibport", "gouttag", "fixed",
                                                  "nolast", "selpin", "pairport"])
    p.add_argument("--rng", type=int, default=20261014); p.add_argument("--log")
    a = ap.parse_args()
    if a.cmd == "check":
        t0 = time.time()
        L, x, w, _ = load_instance(a.layout, a.witness, a.stmt)
        for (ti, r, c) in a.flip:
            T = w[ti]
            T.data[r - T.fnrows][c] ^= 1
            print(f"flipped witness table {ti}, row {r}, column {c}")
        for i in a.xflip:
            x[i] ^= 1
            print(f"flipped statement cell {i}")
        for (ti, r, c, h) in a.xor:
            T, v = w[int(ti)], kel(h)
            T.data[int(r) - T.fnrows][int(c)] ^= v
            print(f"xored {h} into witness table {ti}, row {r}, column {c}")
        for (i, h) in a.xxor:
            x[int(i)] ^= kel(h)
            print(f"xored {h} into statement cell {i}")
        adm = admissible(L, a.k)
        for c, v in adm.items():
            print(f"Admissible {a.k}: {c}: {v}")
        r = rel(L, a.k, x, w)
        for c, (v, d) in r.items():
            print(f"rel: {c}: {v} {d}")
        ok = all(adm.values()) and holds_all(r)
        print(f"(L, x, w) in relK {a.k}: {ok}  ({time.time() - t0:.1f} s)")
        sys.exit(0 if ok else 1)
    experiments(a)


if __name__ == "__main__":
    main()
