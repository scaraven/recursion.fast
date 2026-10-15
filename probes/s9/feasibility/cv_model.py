#!/usr/bin/env python3
"""S9 feasibility: back-of-envelope C_V size for a FRI/BaseFold-like entry under the v2 tape grammar.

Counts BLAKE2s compressions of one NARG run (Contract/Compile.lean's grammar: no path batching, a
repeated query opened again, absorb = H(0x00 || s || m), squeeze = H(0x01 || s), D = H(key bytes)),
the tape length, and the cells of C_V (two NARG runs + nodeStmt) for three hash-gadget costs, and
finds the least class k in [20, 28] with C_V cells <= 2^k (the fixed point).

Protocol model (generic; every number below is a parameter):
  * T0 layer-0 Merkle trees, all queried at the same s positions: `wit` trees of depth k + r - f
    (witness-sized codewords, leaves of 2^f K elements) and `idx` trees of depth k + idxextra + r - f
    (index-sized: the index oracle is sized for the worst admissible layout, since idxShape is a
    protocol constant);
  * BaseFold/FRI layers over E after layer 0, folding by 2^f per layer, leaves of 2^f E elements
    (24 bytes each), until <= 2^final elements, which are sent in the clear;
  * s queries in ONE challenge round (every round's RBR error <= 2^-128, so the query round alone
    must reach 2^-128): unique decoding delta = (1 - rho)/2, Johnson delta = 1 - sqrt(rho) - eta;
  * sumcheck-style rounds: `sc_rounds` plain messages of (deg+1) E elements, each followed by a
    one-E-element challenge.
Hash-gadget costs (cells per BLAKE2s compression): S6a's L_chain G chip as built (9,225 =
80 G-calls x 106 + 697 state + 48 final), the S6a-A7 floor for byte-lookup additions (58 cells per
G-call: 80 x 58 + 697 = 5,337), and leanerVM's BLAKE2s table row (60 cells: the memory/bytecode
interface row of one compression, with NO compression constraint; shown only to say why it is not
a compression cost).
"""
import math, sys

def comp(nbytes):            # BLAKE2s compressions for an nbytes message (>= 1 block)
    return max(1, math.ceil(nbytes / 64))

def queries(rho, regime, eta=0.05, bits=128):
    delta = (1 - rho) / 2 if regime == "unique" else 1 - math.sqrt(rho) - eta
    return math.ceil(bits / -math.log2(1 - delta))

def narg(k, rho, regime, A=2, f=4, wit=2, idx=2, idxextra=4, final=6, vkLen=64, deg=3, sc_rounds=None):
    r = int(round(-math.log2(rho)))
    s = queries(rho, regime)
    la = int(math.log2(A))
    depth = lambda logleaves: math.ceil(max(0, logleaves) / la)
    node_c = comp(32 * A)                       # one internal Merkle node
    sib = (A - 1) * 32                          # tape bytes per level
    per_q_comp = per_q_tape = 0
    trees = [k + r - f] * wit + [k + idxextra + r - f] * idx
    for ll in trees:                            # layer 0: K leaves of 2^f elements
        per_q_comp += comp(8 * 2 ** f) + depth(ll) * node_c
        per_q_tape += 8 * 2 ** f + depth(ll) * sib
    logn = k + r                                # batched folding over E
    layers = 0
    while logn - f > final:
        logn -= f; layers += 1
        ll = logn - f
        per_q_comp += comp(24 * 2 ** f) + depth(ll) * node_c
        per_q_tape += 24 * 2 ** f + depth(ll) * sib
    if sc_rounds is None:
        sc_rounds = 3 * k                       # zerocheck + bus + PCS sumcheck, one variable per round
    n_roots = len(trees) - idx + layers         # prover roots (the index root is in the key)
    over = comp(8 * vkLen + 32)                 # D(key)
    over += comp(1 + 32 + 256)                  # seed: absorb x
    over += n_roots * comp(1 + 32 + 32)         # absorb each root
    over += comp(1 + 32 + 24 * 2 ** logn)       # absorb the final plain codeword
    over += sc_rounds * (comp(1 + 32 + 24 * (deg + 1)) + 1)   # plain round message + 1-element squeeze
    over += math.ceil(8 * s / 32)               # squeeze the s query indices
    tape = 32 * n_roots + 24 * 2 ** logn + sc_rounds * 24 * (deg + 1) + s * per_q_tape
    return dict(k=k, rho=rho, regime=regime, A=A, f=f, s=s, layers=layers,
                comp=s * per_q_comp + over, tape=tape)

GADGETS = {"S6a G chip (9,225)": 9225, "S6a-A7 floor (5,337)": 80 * 58 + 697, "leanerVM table row (60)": 60}

def cv_cells(n, cpc, nonhash=2_000_000):
    # two NARG runs; D(vkC), D(vkL) computed once each (they are also d0, d1); H(x1||x2) = 512 bytes
    return 2 * n["comp"] * cpc + comp(512) * cpc + nonhash

def main():
    out = []
    p = out.append
    p("# per-NARG compressions and tape (k = 24); C_V cells for the three gadgets; least fixed-point k")
    p(f"{'rho':>6} {'regime':>8} {'A':>3} {'f':>2} {'s':>4} {'lay':>3} {'comp/NARG':>10} {'tape KiB':>9} | " +
      " | ".join(f"{g}: log2 cells@24, fixed-point k" for g in GADGETS))
    for rho in (1/2, 1/4, 1/8, 1/16):
        for regime in ("unique", "johnson"):
            for A in (2, 4, 16):
                for f in (2, 4):
                    n = narg(24, rho, regime, A=A, f=f)
                    cols = []
                    for g, cpc in GADGETS.items():
                        c24 = cv_cells(n, cpc)
                        fp = next((k for k in range(20, 29) if cv_cells(narg(k, rho, regime, A=A, f=f), cpc) <= 2 ** k
                                   and narg(k, rho, regime, A=A, f=f)["tape"] <= 2 ** 20), None)
                        cols.append(f"{math.log2(c24):5.2f}, {fp if fp else 'none <= 28'}")
                    p(f"{rho:6.4f} {regime:>8} {A:3d} {f:2d} {n['s']:4d} {n['layers']:3d} {n['comp']:10d} "
                      f"{n['tape']/1024:9.0f} | " + " | ".join(cols))
    p("")
    p("# tape <= 2^20 bytes (tapeCap) is required at the fixed point too; 'none <= 28' = no k in [20, 28]")
    print("\n".join(out))

if __name__ == "__main__" and len(sys.argv) == 1:
    main()

# ---- WHIR-like variant and Merkle-cap emulation (appended; run with: cv_model.py whir) -------------
def whir(k, rho, regime, A=2, f=4, wit=2, idx=2, idxextra=4, cap=0, final=6, vkLen=64, deg=3, eta=0.05):
    """WHIR-like: round i folds f variables and halves the domain, so rate_i = rho * 2^-(f-1)i and the
    query count t_i falls; `cap` = log2 of the number of sub-oracles each tree is split into (emulates
    a Merkle cap within the grammar: 2^cap roots absorbed, paths cap/log2(A) levels shorter)."""
    la = int(math.log2(A)); node_c = comp(32 * A); sib = (A - 1) * 32
    depth = lambda ll: math.ceil(max(0, ll - cap) / la)
    r0 = int(round(-math.log2(rho)))
    def t(rate):
        d = (1 - rate) / 2 if regime == "unique" else 1 - math.sqrt(rate) - eta
        return math.ceil(128 / -math.log2(1 - d))
    total = tape = 0; roots = 0
    t0 = t(rho)
    for ll in [k + r0 - f] * wit + [k + idxextra + r0 - f] * idx:     # round 0 trees
        total += t0 * (comp(8 * 2 ** f) + depth(ll) * node_c); tape += t0 * (8 * 2 ** f + depth(ll) * sib)
        roots += 2 ** cap
    m, i, qs = k, 0, [t0]
    while m - f > final:
        m -= f; i += 1
        rate = rho * 2 ** (-(f - 1) * i)
        ti = t(rate); qs.append(ti)
        ll = m + int(round(-math.log2(rate))) - f
        total += ti * (comp(24 * 2 ** f) + depth(ll) * node_c); tape += ti * (24 * 2 ** f + depth(ll) * sib)
        roots += 2 ** cap
    sc = 3 * k
    over = comp(8 * vkLen + 32) + comp(289) + (roots - idx * 2 ** cap) * comp(65) + comp(33 + 24 * 2 ** m)
    over += sc * (comp(33 + 24 * (deg + 1)) + 1) + sum(math.ceil(8 * q / 32) for q in qs)
    tape += 32 * roots + 24 * 2 ** m + sc * 24 * (deg + 1)
    return dict(comp=total + over, tape=tape, queries=qs)

def main_whir():
    print("# WHIR-like (A = 2, f = 4): per-NARG compressions, tape, C_V log2 cells at k = 24, least fixed-point k (tape <= 2^20)")
    for rho in (1/4, 1/16):
        for regime in ("unique", "johnson"):
            for cap in (0, 6):
                n = whir(24, rho, regime, cap=cap)
                cols = []
                for g, cpc in GADGETS.items():
                    fp = next((kk for kk in range(20, 29) if cv_cells(whir(kk, rho, regime, cap=cap), cpc) <= 2 ** kk
                               and whir(kk, rho, regime, cap=cap)["tape"] <= 2 ** 20), None)
                    cols.append(f"{g}: {math.log2(cv_cells(n, cpc)):5.2f}, k*={fp if fp else 'none<=28'}")
                print(f"rho={rho:6.4f} {regime:8s} cap={cap} queries={n['queries']} comp/NARG={n['comp']} "
                      f"tape={n['tape']/1024:.0f} KiB | " + " | ".join(cols))
    print("# the orchestrator's ~10k compressions per NARG, for reference:")
    for g, cpc in GADGETS.items():
        c = 2 * 10_000 * cpc + comp(512) * cpc + 2_000_000
        print(f"  {g}: C_V = {c/1e6:.1f} M cells = 2^{math.log2(c):.2f}; least k with 2^k >= C_V: {math.ceil(math.log2(c))}")

if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "whir":
    main_whir()
