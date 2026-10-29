/*
 * The toy prover of the end-to-end smoke (UNTRUSTED; harness/PROVER.md is its interface).
 *
 * It proves with the library's witness-sending argument: the proof `π` is the witness itself in the
 * encoding of the Lean library (WS_* below), the verifier makes no oracle query, so every trace is
 * empty and every proof is signed by one `SIGN` request with no items (service/PROTOCOL.md).
 * It computes the public BLAKE2s chains and statements itself, to name the children of a node. Its
 * proofs grow with every step (a node carries its children whole): it is a correct, slow entry.
 *
 *   prover setup DIR      nothing to set up
 *   prover first DIR      ready/go handshake; DIR/chainA.json, DIR/chainB.json -> DIR/proof.bin, a signed
 *                         proof of nodeStmt (leaf A) (leaf B) (V4-A11 §2)
 *   prover step DIR       ready/go handshake; DIR/prev.stmt, DIR/prev.bin, DIR/chain.json -> DIR/proof.bin,
 *                         a signed proof of nodeStmt prev (leaf)
 *
 * Built with -DBROKEN_CHAIN (proves a chain from a changed start), -DBROKEN_UNSIGNED (no SIGN, a
 * zero signature), -DBROKEN_STALE (a signature made by another service, compiled in from
 * stale_sig.h), -DBROKEN_CAP (asks a query above the service's 2^20-byte cap and gives up) or
 * -DBROKEN_OOM (allocates without bound) it is one of the smoke's deliberately broken provers. The committed assembly
 * (honest/prover.s) is `gcc -S -O2` of this file with no option, passed through
 * harness/tools/asm-compat.py (GCC 15 emits `.base64`, which the reference image's binutils 2.42 rejects).
 */
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>

#ifdef BROKEN_STALE
#include "stale_sig.h"   /* static const unsigned char stale_sig[4772]: a SIGN body of an empty trace */
#endif

/* ---- BLAKE2s-256 (RFC 7693), unkeyed ---------------------------------------------------------- */
static const uint32_t IV[8] = {0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
                               0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19};
static const uint8_t SIGMA[10][16] = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}, {14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3},
    {11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4}, {7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8},
    {9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13}, {2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9},
    {12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11}, {13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10},
    {6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5}, {10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0}};
#define ROTR(x, n) (((x) >> (n)) | ((x) << (32 - (n))))
#define G(a, b, c, d, x, y)                                                                                  \
    do {                                                                                                     \
        v[a] += v[b] + (x); v[d] = ROTR(v[d] ^ v[a], 16); v[c] += v[d]; v[b] = ROTR(v[b] ^ v[c], 12);       \
        v[a] += v[b] + (y); v[d] = ROTR(v[d] ^ v[a], 8);  v[c] += v[d]; v[b] = ROTR(v[b] ^ v[c], 7);        \
    } while (0)

static void compress(uint32_t h[8], const uint8_t blk[64], uint64_t t, int last) {
    uint32_t m[16], v[16];
    for (int i = 0; i < 16; i++) m[i] = blk[4*i] | blk[4*i+1] << 8 | blk[4*i+2] << 16 | (uint32_t)blk[4*i+3] << 24;
    for (int i = 0; i < 8; i++) { v[i] = h[i]; v[i + 8] = IV[i]; }
    v[12] ^= (uint32_t)t; v[13] ^= (uint32_t)(t >> 32);
    if (last) v[14] = ~v[14];
    for (int r = 0; r < 10; r++) {
        const uint8_t *s = SIGMA[r];
        G(0, 4, 8, 12, m[s[0]], m[s[1]]);   G(1, 5, 9, 13, m[s[2]], m[s[3]]);
        G(2, 6, 10, 14, m[s[4]], m[s[5]]);  G(3, 7, 11, 15, m[s[6]], m[s[7]]);
        G(0, 5, 10, 15, m[s[8]], m[s[9]]);  G(1, 6, 11, 12, m[s[10]], m[s[11]]);
        G(2, 7, 8, 13, m[s[12]], m[s[13]]); G(3, 4, 9, 14, m[s[14]], m[s[15]]);
    }
    for (int i = 0; i < 8; i++) h[i] ^= v[i] ^ v[i + 8];
}

static void blake2s(uint8_t out[32], const uint8_t *msg, size_t len) {
    uint32_t h[8];
    uint8_t blk[64];
    uint64_t t = 0;
    for (int i = 0; i < 8; i++) h[i] = IV[i];
    h[0] ^= 0x01010020;
    while (len > 64) { t += 64; compress(h, msg, t, 0); msg += 64; len -= 64; }
    memset(blk, 0, 64);
    memcpy(blk, msg, len);
    compress(h, blk, t + len, 1);
    for (int i = 0; i < 8; i++) for (int k = 0; k < 4; k++) out[4*i+k] = (uint8_t)(h[i] >> (8 * k));
}

/* ---- the contract's statements (v3 layouts, V4-16) ------------------------------------------- */
static void put64(uint8_t *p, uint64_t x) { for (int i = 0; i < 8; i++) p[i] = (uint8_t)(x >> (8 * i)); }
static uint64_t get64(const uint8_t *p) { uint64_t x = 0; for (int i = 7; i >= 0; i--) x = x << 8 | p[i]; return x; }

static void chain_end(uint8_t d[32], const uint8_t s[32], uint64_t n) {
    uint8_t b[33];
    memcpy(d, s, 32);
    for (uint64_t k = 0; k < n; k++) { b[0] = 0x43; memcpy(b + 1, d, 32); blake2s(d, b, 33); }
}
static void leaf_stmt(uint8_t c[32], const uint8_t h[32], uint64_t n) {
    uint8_t b[41]; b[0] = 0x4C; memcpy(b + 1, h, 32); put64(b + 33, n); blake2s(c, b, 41);
}
static void node_stmt(uint8_t c[32], const uint8_t a[32], const uint8_t b2[32]) {
    uint8_t b[65]; b[0] = 0x4E; memcpy(b + 1, a, 32); memcpy(b + 33, b2, 32); blake2s(c, b, 65);
}

/* ---- buffers and files ----------------------------------------------------------------------- */
typedef struct { uint8_t *p; size_t n; } buf;
static void die(const char *m) { fprintf(stderr, "toy prover: %s\n", m); exit(1); }
static void app(buf *b, const void *x, size_t n) {
    b->p = realloc(b->p, b->n + n + 1); if (!b->p) die("out of memory");
    memcpy(b->p + b->n, x, n); b->n += n;
}
static void app64(buf *b, uint64_t x) { uint8_t t[8]; put64(t, x); app(b, t, 8); }
static buf readfile(const char *path) {
    buf b = {0, 0}; FILE *f = fopen(path, "rb"); if (!f) die(path);
    uint8_t t[65536]; size_t k;
    while ((k = fread(t, 1, sizeof t, f)) > 0) app(&b, t, k);
    fclose(f); return b;
}
static void writefile(const char *path, buf b) {
    char tmp[512]; snprintf(tmp, sizeof tmp, "%s.tmp", path);
    FILE *f = fopen(tmp, "wb"); if (!f || fwrite(b.p, 1, b.n, f) != b.n || fclose(f)) die(path);
    if (rename(tmp, path)) die(path);
}
static int unhex(uint8_t *out, const char *s, size_t n) {
    for (size_t i = 0; i < n; i++) {
        unsigned v; if (sscanf(s + 2 * i, "%2x", &v) != 1) return -1; out[i] = (uint8_t)v;
    }
    return 0;
}

/* ---- the oracle service: one SIGN of the empty trace --------------------------------------- */
#define SIG_WIRE 4772   /* idx:u32 ‖ 133 × 32 ‖ 16 × 32 */
static int svc = -1;
static void connect_svc(void) {
    if (svc >= 0) return;
    const char *path = getenv("RF_ORACLE"); if (!path) die("RF_ORACLE unset");
    struct sockaddr_un a; memset(&a, 0, sizeof a); a.sun_family = AF_UNIX;
    strncpy(a.sun_path, path, sizeof a.sun_path - 1);
    svc = socket(AF_UNIX, SOCK_STREAM, 0);
    if (svc < 0 || connect(svc, (struct sockaddr *)&a, sizeof a)) die("cannot connect to the oracle service");
}
static void sign_empty(uint8_t sig[SIG_WIRE]) {
#if defined(BROKEN_UNSIGNED)
    memset(sig, 0, SIG_WIRE);
#elif defined(BROKEN_STALE)
    memcpy(sig, stale_sig, SIG_WIRE);
#else
    connect_svc();
    uint8_t h[16] = {2};                      /* SIGN, count 0, body 0 */
    if (write(svc, h, 16) != 16) die("SIGN write");
    size_t got = 0;
    while (got < 16) { ssize_t k = read(svc, h + got, 16 - got); if (k <= 0) die("SIGN read"); got += k; }
    if (h[0] != 0 || get64(h + 8) != SIG_WIRE) die("SIGN refused");
    got = 0;
    while (got < SIG_WIRE) { ssize_t k = read(svc, sig + got, SIG_WIRE - got); if (k <= 0) die("SIGN read"); got += k; }
#endif
}

/* ---- the witness-sending proof and the signed-proof file (harness/FORMAT.md) ---------------- */
/* The library's witness-sending encoding (RecursionFast/Library/WitnessSending.lean, `encode`): the
   little-endian bytes of the extractor output words `witWords w` (Library/Words.lean):
     leaf: u64 0 ‖ start ‖ u64 n                                   (48 bytes)
     node: u64 1 ‖ c1 ‖ c2 ‖ signedWords p1 ‖ signedWords p2
   signedWords p = u64 |π| ‖ π padded to 8 ‖ u64 m ‖ (u64 |q| ‖ q padded to 8 ‖ a)* ‖ u64 idx ‖
   133 × 32 ots ‖ 16 × 32 path: the signed-proof file with π and every query zero-padded to a
   whole word. */
static const uint8_t ZERO8[8] = {0};
static buf ws_leaf(const uint8_t s[32], uint64_t n) {
    buf b = {0, 0}; app64(&b, 0); app(&b, s, 32); app64(&b, n); return b;
}
static void app_padded(buf *b, const uint8_t *p, size_t n) {
    app64(b, n); app(b, p, n); app(b, ZERO8, (8 - n % 8) % 8);
}
/* A signed-proof file, re-encoded as signedWords; dies on a malformed file. */
static void app_signed_words(buf *b, buf f) {
    size_t o = 0;
#define NEED(k) do { if ((k) > f.n - o) die("malformed child file"); } while (0)
    NEED(8); uint64_t np = get64(f.p + o); o += 8; NEED(np); app_padded(b, f.p + o, np); o += np;
    NEED(8); uint64_t m = get64(f.p + o); o += 8; app64(b, m);
    for (uint64_t i = 0; i < m; i++) {
        NEED(8); uint64_t nq = get64(f.p + o); o += 8; NEED(nq); app_padded(b, f.p + o, nq); o += nq;
        NEED(32); app(b, f.p + o, 32); o += 32;
    }
    NEED(8 + 149 * 32); app(b, f.p + o, 8 + 149 * 32); o += 8 + 149 * 32;
    if (o != f.n) die("trailing bytes in a child file");
#undef NEED
}
static buf ws_node(const uint8_t c1[32], const uint8_t c2[32], buf f1, buf f2) {
    buf b = {0, 0}; app64(&b, 1); app(&b, c1, 32); app(&b, c2, 32);
    app_signed_words(&b, f1); app_signed_words(&b, f2); return b;
}
static buf signed_file(buf pi) {
    uint8_t sig[SIG_WIRE];
    sign_empty(sig);
    buf f = {0, 0};
    app64(&f, pi.n); app(&f, pi.p, pi.n);
    app64(&f, 0);                                       /* the trace: no query */
    uint32_t idx = sig[0] | sig[1] << 8 | sig[2] << 16 | (uint32_t)sig[3] << 24;
    app64(&f, idx); app(&f, sig + 4, SIG_WIRE - 4);
    return f;
}

static buf prove_leaf(const uint8_t s[32], uint64_t n, uint8_t c[32]) {
    uint8_t h[32], s2[32];
    memcpy(s2, s, 32);
    chain_end(h, s, n);
    leaf_stmt(c, h, n);
#ifdef BROKEN_CHAIN
    s2[0] ^= 1;                                          /* a different chain: its end is not c's */
#endif
    buf pi = ws_leaf(s2, n), f = signed_file(pi);
    free(pi.p); return f;
}

/* ---- modes ------------------------------------------------------------------------------------- */
static void handshake(void) {
    char line[64];
    printf("ready\n"); fflush(stdout);
    if (!fgets(line, sizeof line, stdin) || strncmp(line, "go", 2)) die("no go");
}

#ifdef BROKEN_CAP
/* One QUERY of 2^20 + 1 bytes: the service refuses it (status 2) and closes the connection. */
static void over_cap(void) {
    connect_svc();
    size_t n = (1u << 20) + 1;
    buf b = {0, 0};
    uint8_t h[16] = {1}; h[4] = 1; put64(h + 8, 4 + n);
    app(&b, h, 16); uint8_t l[4] = {(uint8_t)n, (uint8_t)(n >> 8), (uint8_t)(n >> 16), 0}; app(&b, l, 4);
    uint8_t *z = calloc(n, 1); app(&b, z, n);
    if (write(svc, b.p, b.n) != (ssize_t)b.n) die("QUERY write");
    if (read(svc, h, 16) != 16) die("QUERY read");
    fprintf(stderr, "toy prover: the service answered status %d to a query of 2^20 + 1 bytes\n", h[0]);
    exit(3);
}
#endif

/* A chain file {"n": N, "start": "HEX"}: its leaf's signed proof and statement. */
static buf prove_chain_file(const char *path, uint8_t c[32]) {
    buf j = readfile(path); app(&j, "", 1);
    char *p = strstr((char *)j.p, "\"n\":"), *q = strstr((char *)j.p, "\"start\":");
    if (!p || !q) die(path);
    uint8_t s[32];
    q = strchr(q + 8, '"'); if (!q || unhex(s, q + 1, 32)) die(path);
    buf f = prove_leaf(s, strtoull(p + 4, NULL, 10), c);
    free(j.p); return f;
}

static int mode_first(void) {
    handshake();
#ifdef BROKEN_CAP
    over_cap();
#endif
#ifdef BROKEN_OOM
    for (;;) { char *p = malloc(1 << 26); if (!p) die("malloc"); memset(p, 1, 1 << 26); }
#endif
    uint8_t ca[32], cb[32];
    buf fa = prove_chain_file("chainA.json", ca), fb = prove_chain_file("chainB.json", cb);
    buf pi = ws_node(ca, cb, fa, fb);
    writefile("proof.bin", signed_file(pi));
    printf("done\n"); fflush(stdout);
    return 0;
}

static void read_stmt(uint8_t c[32], const char *path) {
    buf b = readfile(path); app(&b, "", 1);
    if (b.n < 65 || unhex(c, (char *)b.p, 32)) die(path);
    free(b.p);
}

int main(int argc, char **argv) {
    if (argc != 3) die("usage: prover setup|first|step DIR");
    if (chdir(argv[2])) die("cannot enter DIR");
    if (!strcmp(argv[1], "setup")) return 0;
    if (!strcmp(argv[1], "first")) return mode_first();
    if (!strcmp(argv[1], "step")) {
        handshake();
        uint8_t c1[32], c2[32];
        read_stmt(c1, "prev.stmt");
        buf f1 = readfile("prev.bin"), f2 = prove_chain_file("chain.json", c2);
        buf pi = ws_node(c1, c2, f1, f2);
        writefile("proof.bin", signed_file(pi));
        printf("done\n"); fflush(stdout);
        return 0;
    }
    die("unknown mode");
    return 2;
}
