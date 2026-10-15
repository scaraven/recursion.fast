#!/usr/bin/env python3
"""S9 incentives probe (finding S9I-M1): board L is won by a protocol that sends the chain's start.

  python3 -I probes/s9/incentives/recompute_leaf.py [--n 1024] [--reps 200]

The witness of `L_chain(n)` is a function of the 32-byte start `s` (S6-A4: "the witness is unique
given s"), and the leaf prover is handed `s` (`secret.hex`, S6b-A16). A protocol whose key `VK L`
flags "this is L_chain(n)" (VK is any computable function of the layout; P_triv's VK already
decides admissibility of `L`) can, on that key, have the prover send `s` as a plain 4-element
oracle and the verifier recompute `blake2s256^n(s)` and compare it with `y`; on every other key it
falls back to a general protocol (any secure one). Its shapes are fixed (round 0: plain
`msg <2, 2>`; round 1: the fallback's committed oracle, whose root the special path never opens).

This probe builds that protocol's compiled tape on a real chain, following the byte grammar of
`Contract/Compile.lean`'s header (written independently, hashlib.blake2s), runs the compiled
verifier's acceptance condition on it, and times the special-path verification. It shows:
  * the tape is 64 bytes (cap on board L: 131,072);
  * the prover's work is writing `s` and 32 arbitrary root bytes (the root of an oracle the
    verifier never queries is absorbed but never checked);
  * the verifier's work is n BLAKE2s compressions (Lean's compiled spec: about 6 us per one-block
    hash, docs/stages/S2-RESULT.md, so about 6 ms at n = 1024; dominated by process start-up).
Security (knowledge soundness on the special key) needs no cryptography: the extractor image
recomputes the witness tables from `s` (B(24) = 2^64 steps against about 10^9 needed), and the
proof obligations are (i) completeness of `L_chain(n)` for every `s` and (ii) correctness of that
RISC-V generator; both are deterministic program verification.
"""
import argparse, hashlib, os, struct, time

H = lambda b: hashlib.blake2s(bytes(b)).digest()
kb = lambda a: (a % (1 << 64)).to_bytes(8, "little")


def chain_stmt(s, n):
    y = s
    for _ in range(n):
        y = H(y)
    return list(struct.unpack("<4Q", y)) + [n] + [0] * 27


def tape_of(s, root1=bytes(32)):
    """rounds: round 0 is plain (its 4 elements = the 32 bytes of s); round 1 is committed (its
    32-byte root, any bytes: never opened). openings: the one query (1, 0) is of a plain oracle, so
    nothing."""
    assert len(s) == 32 and len(root1) == 32
    return s + root1


def narg_special(vk, x, tape, idx_root):
    """`NARG` (Compile.lean) for this protocol on a key flagged L_chain(n): cap, 32-byte key root,
    the pass over the rounds (absorb round 0's plain bytes, round 1's root), then the query program
    `query 1 0 (fun s => done (blake2s^n(s) = y ∧ x = (y, n, 0, ...)))` against no openings, with no
    bytes left over."""
    if len(tape) > 2 ** 20 or len(idx_root) != 32:
        return False
    D = H(b"".join(kb(a) for a in vk) + idx_root)
    st = H(b"\x00" + D + b"".join(kb(a) for a in x))            # seed: absorb x
    r0, rest = tape[:32], tape[32:]
    if len(r0) < 32:
        return False
    st = H(b"\x00" + st + r0)                                    # round 0 (plain) absorbed
    r1, rest = rest[:32], rest[32:]
    if len(r1) < 32:
        return False
    st = H(b"\x00" + st + r1)                                    # round 1 (root) absorbed
    n = vk[0]                                                    # the key flags L_chain(n)
    s = r0                                                       # query (1, 0): the plain oracle
    y = s
    for _ in range(n):
        y = H(y)
    want = list(struct.unpack("<4Q", y)) + [n] + [0] * 27
    return rest == b"" and want == x                             # no leftover bytes; accept


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=1024)
    ap.add_argument("--reps", type=int, default=200)
    a = ap.parse_args()
    s = os.urandom(32)
    x = chain_stmt(s, a.n)
    vk, idx_root = [a.n], H(kb(0))                               # vkLen = 1; a one-leaf index oracle
    t = tape_of(s)
    ok = narg_special(vk, x, t, idx_root)
    bad = narg_special(vk, x, tape_of(os.urandom(32)), idx_root)
    t0 = time.perf_counter()
    for _ in range(a.reps):
        narg_special(vk, x, t, idx_root)
    dt = (time.perf_counter() - t0) / a.reps
    print(f"n = {a.n}: tape {len(t)} bytes (board-L cap 131072); honest tape accepted: {ok}; "
          f"tape with a wrong start accepted: {bad}")
    print(f"special-path verification (Python hashlib, {a.n} + 4 hashes): {dt * 1e3:.3f} ms per run; "
          f"Lean's compiled spec at ~6.1 us per one-block hash: {(a.n + 4) * 6.1e-3:.1f} ms")
    print("prover: write s (from secret.hex) and 32 arbitrary bytes; no witness generation, no commitment")


if __name__ == "__main__":
    main()
