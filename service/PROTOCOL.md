# The oracle service wire protocol (normative for provers)

This is the interface between a prover and `rf-oracle`, the oracle and signing service of
recursion.fast v4 (SROM; `docs/v4/BRIEF.md` §4.3). One service process lives for one timed run
(the tree run, the stream run). It holds a fresh secret PRF key `k` and a fresh signing key pair
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
a_i = PRF_k(q_i) = BLAKE2s-256 keyed by k of q_i      (RFC 7693, key length 32, digest length 32)
```

The empty query is allowed (its answer is the keyed hash of the empty message, whose only block is
the key block). Queries carry no tag: `q_i` is hashed as given. A query has at most `2^20` bytes
(`queryCap`, V4-A3; `acc` rejects a trace holding a longer query). Every answer is computed when
asked: the service keeps no table of answers (V4-A5), so the time of a call depends only on the
sizes of its queries, never on what was asked before.

### 2.2 `SIGN` (op = 2)

Request body: as `QUERY`. The service computes the answers `a_i = PRF_k(q_i)` itself, forms the
trace `tr = [(q_0, a_0), …, (q_{m−1}, a_{m−1})]` (`m = count`, possibly 0), and signs its digest
with the next unused one-time key:

```
traceDigest tr = BLAKE2s-256(0x54 ‖ item_0 ‖ … ‖ item_{m−1}),   item_i = enc64 |q_i| ‖ q_i ‖ a_i
```

(`enc64 n` = 8 bytes little-endian). Response (status 0): `count` = m, body =

```
a_0 ‖ … ‖ a_{m−1}            m × 32 bytes
idx:u32                      the one-time key index j < 2^16
ots_0 ‖ … ‖ ots_132          133 × 32 bytes
path_0 ‖ … ‖ path_15         16 × 32 bytes (Merkle siblings, leaf level first)
```

`body_len = 32·m + 4772`. The signature is the contract's `Sig` (BRIEF §4.2): it verifies with
`SigOk vk (traceDigest tr) σ`. Each `SIGN` uses one of the **2^16** one-time keys of the service's
lifetime; after that every `SIGN` is refused with status 3. Signing the same trace twice uses two
keys and gives two different valid signatures.

The trace of a signed proof is exactly the list of queries the verifier `V` asks, in order, with
their answers, and nothing after them (`OProg.runSeq` consumes the whole trace, V4-A3); a prover
asks `SIGN` once per proof, with that list, after it has obtained the same answers through `QUERY`
while proving (the answers are deterministic in `k`). **`SIGN` re-evaluates every query** of the
trace: an adaptive verifier's trace costs one `QUERY` per answer while proving plus one PRF per
query again at signing (C-m4); budget for it.

The one-time key index is taken by one atomic step before the signature is computed and is never
reused, even if the request fails afterwards (V4-A4). The index of a signature is visible to the
prover and reveals how many signatures were made before it in this service lifetime (a 16-bit
counter, C-m2); it carries no other state.

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
(the refusal aborts that proof as a reject, V4-A5).

## 3. Caps

| cap | value | why |
|---|---|---|
| query | 2^20 bytes | `queryCap` of `acc` (V4-A3) |
| request body | 2^24 bytes (16 MiB) | bounds the service's memory per connection |
| items per `QUERY` | 2^18 | bounds the answer buffer (8 MiB) |
| items per `SIGN` | 2^16 | the verifier makes at most `qV ≤ 2^16` queries (V4-13) |
| signatures per service lifetime | 2^16 | the Merkle tree's height (V4-3) |
| connections | 32 | one per prover thread; 32 maximal connections fit the service's 2 GiB cgroup (RF-m20) |

Larger data must be hashed in pieces by the entry's own construction (e.g. a Merkle tree), as with
any random oracle of bounded input. The service runs in its own memory cgroup, separate from the
prover's; the runner raises the prover's `oom_score_adj` so that under memory pressure the kernel
kills the prover first (V4-A5).

## 4. Performance notes (informative)

- Batch: one round trip costs tens of microseconds; a batch of 256–4096 queries amortises it.
  `docs/v4/stages/B-harness-RESULT.md` §3 has the measured latency and throughput.
- Within one request the service hashes eight queries at a time with AVX2 when the CPU has it,
  grouping queries of equal block count (`⌈|q|/64⌉`); a batch of equal-size queries is fastest.
- Each request is computed on the connection's thread; use several connections to use several
  cores.

## 5. No logging mode

The service has one mode. Its liveness mode (`--log FILE`, every evaluated query written to a file
for the per-entry extractor liveness check) was removed with that check (V4-A9): the extractor's
correctness is the kernel-checked `Computes`.

## 6. Lifecycle (informative; the runner's)

The runner starts the service with `--socket PATH` and its stdin on a pipe. The service draws `k`
and the signing seed from `getrandom`, generates the `2^16` one-time keys and the tree
(multi-threaded), binds the socket and prints `vk <hex>`, `keygen_ms <ms>`, `simd <avx2|scalar>` and
`ready`. When the runner closes the pipe, the service waits for in-flight requests, overwrites its
keys, prints `stats requests=… queries=… query_bytes=… signatures=… refusals=…`, removes the socket
and exits 0. The first 32 refusals of a lifetime are written to its stderr (`rf-oracle: refused
(status S): MESSAGE`); the runner copies them into the result, so that a prover that fails on a cap
can see which one. Keys are never written to disk; the process is non-dumpable
(`PR_SET_DUMPABLE = 0`).
