# The oracle service wire protocol (normative for provers)

This is the interface between a prover and `rf-oracle`, the oracle and signing service of
recursion.fast (the signed random oracle; the rules are in [`AGENTS.md`](../AGENTS.md)). One service process lives for
one timed run (the stream; the calibration has its own). It holds a fresh secret PRF key `k` and a fresh signing key pair
`(sk, vk)`; neither ever leaves the process.

## 1. Transport

- A Unix stream socket. Its path is in the environment variable **`RF_ORACLE`** of every prover
  process (inside the sandbox it is `/run/rf/oracle.sock`). The socket is the only way to reach the
  service.
- A connection carries any number of requests, answered in order. The service reads the next
  request only after it has written the response to the previous one, so a client may pipeline
  (write a request before reading the previous response) only if it keeps reading responses while
  it writes, otherwise both sides can block on full socket buffers. The service serves each connection on
  its own thread, so **use one connection per prover thread** to hash in parallel (the service
  computes on the same CPUs as the prover; it is not a co-processor).
- At most **32** connections are open at a time; a further connection receives a `CAP` response and
  is closed.
- After any error response the service closes the connection.

## 2. Messages

### 2.0 The hash

Every hash of the service is **Keccak-256 as Ethereum uses it** (`RecursionFast/Contract/Hash/Keccak.lean`
is the normative definition): the sponge of FIPS 202 over Keccak-f[1600], lane `A[x, y]` = lane
`x + 5y` = the little-endian 64-bit word of 8 state bytes, rate **136 bytes** (capacity 512 bits),
a 32-byte output (the first 32 state bytes after the last permutation), and Keccak's original
padding: the byte `0x01` after the message, zeros to the end of the block, `0x80` XORed into the
block's last byte (a single padding byte is `0x81`). It is not SHA3-256, whose first padding byte is
`0x06`. A message of `n` bytes costs `⌊n / 136⌋ + 1` permutations. For example
`Keccak-256("") = c5d24601…5d85a470` and `Keccak-256("abc") = 4e03657a…a12d6c45`.

The service's two secrets are independent 32-byte draws; each is used as a key prefix of fixed
length, the first 32 bytes of the first block:

```
PRF_k(q)  = Keccak-256(k ‖ q)                              the oracle; q as given, no tag
sk_i(j)   = Keccak-256(seed ‖ 0x53 ‖ enc64 j ‖ byte i)     chain start i < 133 of one-time key j < 2^16 (42 bytes)
```

(`enc64 n` = 8 bytes little-endian.) Every public hash of the contract (the chain step, the
statements, the trace digest, the WOTS chain step, leaf and node) is the unkeyed Keccak-256 of an
input that starts with a one-byte domain tag; a keyed input starts with the 32 secret key bytes.
What separates the keyed hashes from the public ones, and the two keyed functions from each other,
is the PRF assumption on the secret prefix (with independent draws), not the bytes after it: the
byte `0x53` (tag `S`) in `sk_i(j)` is a domain separator kept for clarity.

All integers are little-endian. Every request and every response is a 16-byte header followed by
a body of exactly `body_len` bytes.

```
request header   op:u8      0:u8 0:u8 0:u8   count:u32   body_len:u64
response header  status:u8  0:u8 0:u8 0:u8   count:u32   body_len:u64
```

### 2.1 `QUERY` (op = 1)

Request body: `count` items, each `len:u32 ‖ q` (`len` bytes of query). `body_len` must equal
`Σ (4 + len_i)`.

Response (status 0): `count` = the request's count, body = `count` answers of 32 bytes, in request
order:

```
a_i = PRF_k(q_i) = Keccak-256(k ‖ q_i)                ⌊(32 + |q_i|) / 136⌋ + 1 permutations
```

The empty query is allowed (its answer is `Keccak-256(k)`, one permutation); a query of up to 103
bytes costs one permutation, up to 239 bytes two. Queries carry no tag: `q_i` is hashed as given. A query has at most `2^20` bytes
(`queryCap`; `acc` rejects a trace holding a longer query). Every answer is computed when
asked: the service keeps no table of answers, so the time of a call depends only on the
sizes of its queries, never on what was asked before.

### 2.2 `SIGN` (op = 2)

Request body: as `QUERY`. The service computes the answers `a_i = PRF_k(q_i)` itself, forms the
trace `tr = [(q_0, a_0), …, (q_{m−1}, a_{m−1})]` (`m = count`, possibly 0), and signs its digest
with the next unused one-time key:

```
traceDigest tr = Keccak-256(0x54 ‖ item_0 ‖ … ‖ item_{m−1}),   item_i = enc64 |q_i| ‖ q_i ‖ a_i
```

Response (status 0): `count` = m, body =

```
a_0 ‖ … ‖ a_{m−1}            m × 32 bytes
idx:u32                      the one-time key index j < 2^16
ots_0 ‖ … ‖ ots_132          133 × 32 bytes
path_0 ‖ … ‖ path_15         16 × 32 bytes (Merkle siblings, leaf level first)
```

`body_len = 32·m + 4772`. The signature is the contract's `Sig` (`RecursionFast/Contract/Signature.lean`): it verifies with
`SigOk vk (traceDigest tr) σ`. It is a Winternitz one-time signature (`w = 4`, 133 chains: the
32-byte digest's 128 base-4 digits and a 5-digit checksum) under a Merkle tree of height 16: chain
`i` of key `j` starts at `sk_i(j)` (§2.0) and steps by `F(j, i, s, x) = Keccak-256(0x57 ‖ enc64 j ‖
byte i ‖ byte s ‖ x)` (43 bytes); `ots_i` is the start after `d_i` steps; leaf `j` is
`Keccak-256(0x4B ‖ enc64 j ‖ end_0 ‖ … ‖ end_132)` (4,265 bytes, 32 permutations), `end_i` the start
after 3 steps; a node is `Keccak-256(0x4D ‖ left ‖ right)`. Each `SIGN` uses one of the **2^16** one-time keys of the service's
lifetime; after that every `SIGN` is refused with status 3. Signing the same trace twice uses two
keys and gives two different valid signatures.

The trace of a signed proof is exactly the list of queries the verifier `V` asks, in order, with
their answers, and nothing after them (`OProg.runSeq` consumes the whole trace); a prover
asks `SIGN` once per proof, with that list, after it has obtained the same answers through `QUERY`
while proving (the answers are deterministic in `k`). **`SIGN` re-evaluates every query** of the
trace: an adaptive verifier's trace costs one `QUERY` per answer while proving plus one PRF per
query again at signing; budget for it.

The one-time key index is taken by one atomic step before the signature is computed and is never
reused, even if the request fails afterwards. The index of a signature is visible to the
prover and reveals how many signatures were made before it in this service lifetime (a 16-bit
counter); it carries no other state.

### 2.3 `VK` (op = 3)

Request: `count = 0`, `body_len = 0`. Response: body = the 32-byte public key `vk` (the Merkle
root of the 2^16 one-time public keys). The runner also writes it to `DIR/vk.hex`.

### 2.4 Errors

| status | meaning |
|---|---|
| 0 | OK |
| 1 `BAD` | unknown op, non-zero reserved bytes, `VK` with a body, item lengths that do not add up to `body_len` |
| 2 `CAP` | `body_len > 2^24`; a query above `2^20` bytes; `QUERY` with `count > 2^18`; `SIGN` with `count > 2^16`; more than 32 connections |
| 3 `EXHAUSTED` | `SIGN` after all 2^16 one-time keys are used |

An error response has `count = 0` and a body holding a UTF-8 message. The connection is closed
after it. A refused call has no answers: a prover that needs them cannot produce an accepted proof
(the refusal aborts that proof as a reject).

## 3. Caps

| cap | value | why |
|---|---|---|
| query | 2^20 bytes | `queryCap` of `acc` |
| request body | 2^24 bytes (16 MiB) | bounds the service's memory per connection |
| items per `QUERY` | 2^18 | bounds the answer buffer (8 MiB) |
| items per `SIGN` | 2^16 | the verifier makes at most `qV ≤ 2^16` queries |
| signatures per service lifetime | 2^16 | the Merkle tree's height |
| connections | 32 | one per prover thread; 32 maximal connections fit the service's 2 GiB cgroup |

Larger data must be hashed in pieces by the entry's own construction (e.g. a Merkle tree), as with
any random oracle of bounded input. The service runs in its own memory cgroup, separate from the
prover's; the runner raises the prover's `oom_score_adj` so that under memory pressure the kernel
kills the prover first.

## 4. Performance notes (informative)

- Batch: one round trip costs tens of microseconds; a batch of 256–4096 queries amortises it.
  Every result publishes the service's throughput measured on its runner (`calibration.service`).
- The service computes one keyed hash after another with a portable scalar Keccak-f[1600] (no SIMD
  path); the time of a request is about proportional to its permutation count
  `Σ (⌊(32 + |q_i|) / 136⌋ + 1)`. A `SIGN` adds the trace digest and up to `133 · 4` permutations of
  the signature (the chain starts and their steps).
- Each request is computed on the connection's thread; use several connections to use several
  cores.

## 5. No logging mode

The service has one serving mode (and the chain hasher of §7, which holds no secret), and it never
writes the queries it evaluates: nothing in an evaluation checks an extractor against a log of
queries, since the extractor's correctness is the kernel-checked `Computes`.

## 6. Lifecycle (informative; the runner's)

The runner starts the service with `--socket PATH` and its stdin on a pipe. The service draws `k`
and the signing seed from `getrandom`, generates the `2^16` one-time keys and the tree
(multi-threaded), binds the socket and prints `vk <hex>`, `keygen_ms <ms>`, `simd scalar` (the one
implementation) and `ready`. When the runner closes the pipe, the service waits for in-flight requests, overwrites its
keys, prints `stats requests=… queries=… query_bytes=… signatures=… refusals=…`, removes the socket
and exits 0. The first 32 refusals of a lifetime are written to its stderr (`rf-oracle: refused
(status S): MESSAGE`); the runner copies them into the result, so that a prover that fails on a cap
can see which one. Keys are never written to disk; the process is non-dumpable
(`PR_SET_DUMPABLE = 0`).

## 7. The chain hasher (`--leaves`; the runner's, not for provers)

```
rf-oracle --leaves [--threads N]
```

hashes chains for the runner, which computes every chain digest it checks a proof against from its
own starts. It draws no key, opens no socket and holds no secret. It reads stdin to end of file, one
line per leaf, `<s: 64 lowercase hex> <n: decimal>`, and writes one line per input line, in input
order, `<leafStmt (chainEnd s n) n: 64 lowercase hex>`, where

```
chainStep d   = Keccak-256(0x43 ‖ d)              33 bytes, one permutation
chainEnd s n  = chainStep applied n times to s
leafStmt h n  = Keccak-256(0x4C ‖ h ‖ enc64 n)    41 bytes
```

(`RecursionFast/Contract/Relation.lean`). The lines are distributed over `N` threads (default: all
CPUs). It exits 0 at end of input; a malformed line (not exactly a 64-character lowercase hex
string, one space and a decimal 64-bit integer) is reported on stderr, nothing is written to
stdout, and the exit code is 2. `n` above `chainCap = 2^20` is accepted (it is only work).
