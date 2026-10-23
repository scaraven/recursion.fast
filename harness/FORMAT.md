# The signed-proof file (normative)

Every proof a prover outputs, and every proof the runner, the badge `verify` and any third party
check, is one **signed proof** `p = (π, tr, σ)` (BRIEF §4.1 `Signed`) in this file format. It is
the whole input of `acc vk c p` besides the public key `vk` and the statement `c`.

## Layout

All integers are unsigned 64-bit little-endian (`u64`); digests are 32 bytes.

```
u64 |π|          π            the proof bytes
u64 m                         the number of trace entries
repeat m times:
  u64 |q_i|      q_i          the i-th query the verifier asks
                 a_i          its answer (32 bytes)
u64 j                         the one-time key index of the signature
ots_0 … ots_132               133 × 32 bytes
path_0 … path_15              16 × 32 bytes (Merkle siblings, leaf level first)
```

The file ends exactly after `path_15`. Its size is
`8 + |π| + 8 + Σ_i (8 + |q_i| + 32) + 8 + 4768` bytes.

## Rules

- **Strict.** A file that is not exactly one such encoding (a length running past the end,
  bytes after `path_15`) is not a signed proof: `verify` rejects it, whatever it contains.
- **What `acc` then checks** (contract `Submission.acc`, V4-7, V4-A3): `|π| ≤ proofCap = 2^20`;
  every `|q_i| ≤ queryCap = 2^20`; `SigOk vk (traceDigest tr) σ`; and the verifier `V vk c π`,
  run with its `i`-th oracle query answered from the `i`-th trace entry (`OProg.runSeq`), asks
  exactly `q_0, …, q_{m−1}` in order, uses every entry, and returns `true`.
- **The trace digest** is computed over the same bytes the file stores for the entries:
  `traceDigest tr = BLAKE2s-256(0x54 ‖ item_0 ‖ … ‖ item_{m−1})` with
  `item_i = u64 |q_i| ‖ q_i ‖ a_i` (BRIEF §4.2). A prover gets `(a_i)` and `σ` from one service
  `SIGN` request with `q_0, …, q_{m−1}` (`service/PROTOCOL.md` §2.2); the wire format carries the
  index as `u32`, the file as `u64`.
- **The signature** is the contract's WOTS/Merkle signature (BRIEF §4.2): `j < 2^16`, 133 chain
  values, 16 siblings; the file format fixes the two counts.
- **The trace's length**: since the contract fix pass `ea2e8ab` (review RA-M2), `acc` also
  requires `m ≤ qV` of the entry (right after the size cap); nothing in this format changes.
- **Size caps of the runner**: a file above `file_cap` (64 MiB, `harness/season.toml`) is not read.
  `π` is capped at `proofCap` by `acc`; the trace is bounded by `qV ≤ 2^16` queries of at most
  `2^20` bytes each.

## The file and the extractor's word format

The contract's extractor output (`Contract/Extractor.lean`, `readSigned`; `Library/Words.lean`,
`signedWords`) encodes a signed proof in 64-bit words: the same fields in the same order, but `π`
and every query zero-padded to a whole number of words. The library's witness-sending proof of a
node (`WitnessSending.encode`) carries its children in that word encoding, so a node prover
re-encodes each child's file by padding `π` and the queries (`harness/toy-prover/toy.c`,
`app_signed_words`). The file itself is not padded: the badge parses it at byte level
(`harness/badge/Common.lean.in`, `parseSigned`) in linear time, about 30 ms for a 9.2 MB file
(`logs/harness/accprobe.log`), where reading words through `packFast` and `Word = BitVec 64` costs
about 0.4 µs per byte (stage A RESULT §4).

## Statements and keys

The runner gives statements and keys as 64 lowercase hex characters (`vk.hex`, `child1.stmt`, …;
a trailing newline is allowed). They are never part of the file: the statement a file is checked
against is always the runner's own digest.

## A worked size

The toy prover's leaf proof (`π` the 48-byte witness-sending encoding of a leaf, no query) is
`8 + 48 + 8 + 0 + 8 + 4768 = 4840` bytes.
