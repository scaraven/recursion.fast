# Native prover: not delivered for `P_triv`; what a real entry's prover must produce

**This entry has no native prover, by design (O-10).** For every instance of every class,
`P_triv`'s honest tape has `5 · 2^(k+11)` bytes (160 GiB at `k = 24`; `triv_uncapped_length`).
That is beyond `tapeCap = 2^20`, so the honest compiled prover writes no tape
(`triv_prove_none`) and the compiled verifier accepts none (`triv_narg`). A program that emitted
the tape could not pass the benchmark, so none is supplied. The rest of this file is for real
entries.

## The contract for a native prover (DESIGN §3.2, §6.3)

A native prover is the submitter's untrusted program, in any language, built from source in the
sandbox with the pinned toolchains. It is never proved correct. It only has to work: for every
benchmark instance, within budget, it must write a tape that the organiser's compiled verifier
accepts:

```
NARG cfg P (index cfg P L) x tape = true        (Contract/Compile.lean; executed by the runner's compiled verifier)
```

**Interface.** See `harness/README.md` ("Prover interface", "Verifier interface") for the
runner's interface. Stage 6b is finalising it, so it is not restated here. It covers the files a
leaf or node prover reads, the `proof.bin` it writes, the sandbox and the budgets.

Two constraints hold whatever the file format:

- A native indexer may be used, but its key bytes must equal those of the Lean-compiled indexer
  (`VK`, `IDX`, committed by the trusted `index`).
- Witness material (the secret start `s`) stays outside the verifier's sandbox (S6-A9).

**Size.** `|tape| ≤ 2^20` bytes for `NARG` and on boards R and W. On board L every leaf proof must
also be `≤ 2^17` bytes. The benchmark runner enforces that on every measured leaf tape (DESIGN §6.2,
S7-A3); neither `NARG` nor the certificate does.

## The tape grammar (authoritative: the header of `Contract/Compile.lean`)

Encodings:

- An element of `K` is 8 bytes, little-endian.
- A statement is its 32 elements (256 bytes).
- A digest is 32 bytes. `H = cfg.hash` (BLAKE2s-256, unkeyed).
- There are no length fields: every length is fixed by the shapes.

```
tape     ::= rounds openings                     (leftover bytes reject)
rounds   ::= for each prover round in order: its 2^logLen elements if it has one leaf ("plain"),
             else the 32-byte Merkle root of the oracle
openings ::= for each query (j, l) that the verifier's query program makes, in order, on the
             Fiat–Shamir challenges:
               nothing                 if oracle j ≥ 1 is plain
               leaf path               otherwise (the index oracle, j = 0, is always committed)
leaf     ::= the 2^logLeaf elements of leaf l of oracle j
path     ::= depth levels, leaf level first; per level the A − 1 sibling digests in increasing
             position (the current node omitted); depth = ⌈(logLen − logLeaf) / log₂ A⌉
```

**Merkle tree.**

- Leaf `p` hashes to `H(leaf bytes)`. Positions beyond the last leaf, up to `A^depth`, hold the zero
  digest (32 zero bytes).
- Node `p` at height `h + 1` is `H(n_{A·p} ‖ … ‖ n_{A·p+A−1})`. This holds for every internal
  node, including one over all-padding children. There is no leaf/node tag.
- The index oracle uses the same hash and arity as the prover's oracles.

**Key and sponge.**

- The key bytes are the `VK` elements, then the 32-byte index root. Its digest is
  `D = H(key bytes)`.
- The sponge starts at `s₀ = D`, then absorbs `x`.
- Absorbing `m` sets `s ← H(0x00 ‖ s ‖ m)`. Each prover round absorbs its rounds-section bytes.
- A challenge round `chal nE idx` squeezes `24·nE + 8·|idx|` bytes: `⌈b/32⌉` ratchet steps
  `s ← H(0x01 ‖ s)`, outputting the successive states.
- `E` element `j` is bytes `24j … 24j+23`, as three `K` limbs. Index `j` is the low `b` bits of the
  little-endian word at byte `24·nE + 8j`.

**The queries** are those of `P.verify (VK L) x chals` run on the honest oracles. A repeated query is
opened again, since there is no batching (S3-A4). An out-of-range query rejects.

## Reference implementations

| What | Where |
|---|---|
| The honest compiled prover as a Lean specification | `prove cfg P L x w` in `RecursionFast/Library/Compile.lean`. `narg_complete_of_secure`: for a secure protocol, every tape it outputs is accepted. `prove_isSome`: on `relK k` it fails only by exceeding the cap. |
| An independent Python reference of the grammar | `probes/s3/compile_ref.py`. It recomputes the honest tape of the control protocol `cmpToy` at arity 2 and 4, byte-for-byte equal to the Lean `prove` (`#guard prove cfg2 cmpToy L0 x0 [] = some tape2`, `Controls/CompileToy.lean`). |
| An encoder written from the header alone | `probes/s3/indep_encoder.py`. It matches at arity 2, 4, 8 and 16 (S3-A12). |
| BLAKE2s | `hashlib.blake2s(m, digest_size=32)`. The Lean specification is `Contract/Hash/Blake2s.lean`, with KATs and an 8,432-case differential test (O-2). |

## What `P_triv`'s prover would write, were there no cap

1. **Rounds section.** `eWit L w` (one height per chip, then the cells row by row, as `K`
   elements), zero-padded to `2^(k+10)` elements, as `8 · 2^(k+10)` bytes. The round is plain.
2. **Openings.** For query `(0, 0)`: `eLayout L` zero-padded to `2^(k+8)` elements, with an empty
   path (depth 0). Query `(1, 0)` is plain and opens nothing.

That is `5 · 2^(k+11)` bytes, and the first `tapeCap` bytes are already exhausted inside item 1.
