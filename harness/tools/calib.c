/*
 * The prover-shaped calibration workload `c_P` (TRUSTED organiser code; AGENTS.md §6).
 *
 *   calib [THREADS [ROUNDS]]     prints `calib ns=NS threads=T rounds=R sum=HEX`
 *
 * Runs THREADS threads (default: the CPUs this process may use), each doing ROUNDS rounds (default
 * 64) of the two kernels a recursive Keccak-chain prover spends its time in: Keccak-256 chain steps
 * (one Keccak-f[1600] each) on CHAINS independent chains, stepped in turn so that the core always has
 * independent work, and a read-modify-write sweep over its share of a MEM_BYTES buffer (memory
 * bandwidth: passes over traces many times larger than the caches). NS is the wall time from a
 * barrier that starts every thread to the last one's end; the sum keeps the work observable. It is
 * fixed per season (`calib_ref_ns` in the season file is its time on the reference runner) and built
 * from this source with the runner's `gcc -O2` before any entry code runs (`run-benchmark.py`).
 * Portable C (no intrinsics), so every x86-64 runner runs the same instructions. Before timing it
 * checks its Keccak-256 against known digests and exits 2 on a mismatch.
 *
 * Keccak-256 is Ethereum's: the FIPS 202 sponge over Keccak-f[1600], rate 136 bytes, Keccak's
 * original padding (0x01 … 0x80); written from FIPS 202 §3.2, the lane of A[x, y] is x + 5y.
 */
#define _GNU_SOURCE
#include <pthread.h>
#include <sched.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MEM_BYTES (128u << 20)   /* several times the last-level cache of any runner */
#define CHAINS 4                 /* independent chains per thread */
#define STEPS 3000               /* chain steps per chain per round */

static int threads, rounds;
static uint64_t *mem;
static pthread_barrier_t bar;

/* ι round constants (FIPS 202 §3.2.5) and ρ offsets of lane x + 5y (§3.2.2) */
static const uint64_t RC[24] = {
    0x0000000000000001ull, 0x0000000000008082ull, 0x800000000000808Aull, 0x8000000080008000ull,
    0x000000000000808Bull, 0x0000000080000001ull, 0x8000000080008081ull, 0x8000000000008009ull,
    0x000000000000008Aull, 0x0000000000000088ull, 0x0000000080008009ull, 0x000000008000000Aull,
    0x000000008000808Bull, 0x800000000000008Bull, 0x8000000000008089ull, 0x8000000000008003ull,
    0x8000000000008002ull, 0x8000000000000080ull, 0x000000000000800Aull, 0x800000008000000Aull,
    0x8000000080008081ull, 0x8000000000008080ull, 0x0000000080000001ull, 0x8000000080008008ull};
static const int RHO[25] = {0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39,
                            41, 45, 15, 21, 8, 18, 2, 61, 56, 14};

#define ROL(v, n) (((v) << (n)) | ((v) >> ((64 - (n)) & 63)))
/* θ: column parities and their mix; ρ and π: B[y, 2x + 3y] = rot(A[x, y] ^ D[x], r[x, y]); χ */
#define PAR(x) c[x] = a[x] ^ a[(x) + 5] ^ a[(x) + 10] ^ a[(x) + 15] ^ a[(x) + 20]
#define DEL(x) d[x] = c[((x) + 4) % 5] ^ ROL(c[((x) + 1) % 5], 1)
#define RP(x, y) b[(y) + 5 * ((2 * (x) + 3 * (y)) % 5)] = ROL(a[(x) + 5 * (y)] ^ d[x], RHO[(x) + 5 * (y)])
#define RP5(x) RP(x, 0); RP(x, 1); RP(x, 2); RP(x, 3); RP(x, 4)
#define CHI(x, y) a[(x) + 5 * (y)] = b[(x) + 5 * (y)] ^ (~b[((x) + 1) % 5 + 5 * (y)] & b[((x) + 2) % 5 + 5 * (y)])
#define CHI5(y) CHI(0, y); CHI(1, y); CHI(2, y); CHI(3, y); CHI(4, y)

/* Keccak-f[1600] on 25 lanes. */
static void keccak_f(uint64_t s[25]) {
    uint64_t a[25], b[25], c[5], d[5];
    memcpy(a, s, sizeof a);
    for (int r = 0; r < 24; r++) {
        PAR(0); PAR(1); PAR(2); PAR(3); PAR(4);
        DEL(0); DEL(1); DEL(2); DEL(3); DEL(4);
        RP5(0); RP5(1); RP5(2); RP5(3); RP5(4);
        CHI5(0); CHI5(1); CHI5(2); CHI5(3); CHI5(4);
        a[0] ^= RC[r];
    }
    memcpy(s, a, sizeof a);
}

/* Keccak-256 of a message (the self-test's byte path: absorb, pad, squeeze 32 bytes). */
static void keccak256(uint8_t out[32], const uint8_t *m, size_t len) {
    uint64_t s[25] = {0};
    uint8_t blk[136];
    for (;;) {
        size_t k = len < 136 ? len : 136;
        memset(blk, 0, 136);
        memcpy(blk, m, k);
        if (k < 136) { blk[k] ^= 0x01; blk[135] ^= 0x80; }
        for (int i = 0; i < 17; i++) for (int j = 0; j < 8; j++) s[i] ^= (uint64_t)blk[8 * i + j] << (8 * j);
        keccak_f(s);
        if (k < 136) break;
        m += 136; len -= 136;
    }
    for (int i = 0; i < 32; i++) out[i] = (uint8_t)(s[i / 8] >> (8 * (i % 8)));
}

/* chainStep d = Keccak-256(0x43 ‖ d) on d's four little-endian lanes: the 33-byte message and its
   padding fill one block, 0x43 ‖ d ‖ 0x01 ‖ 0 … 0 ‖ 0x80. */
static void chain_step(uint64_t d[4]) {
    uint64_t s[25] = {0};
    s[0] = 0x43 | d[0] << 8;
    s[1] = d[0] >> 56 | d[1] << 8;
    s[2] = d[1] >> 56 | d[2] << 8;
    s[3] = d[2] >> 56 | d[3] << 8;
    s[4] = d[3] >> 56 | 0x01ull << 8;
    s[16] = 0x80ull << 56;
    keccak_f(s);
    memcpy(d, s, 4 * sizeof *d);
}

/* The digests of the empty string and of 0x43 ‖ 00 01 … 1f (by both paths); 0 if all agree. */
static int self_test(void) {
    static const char *want[2] = {"c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
                                  "db8c51208716e57c91fc944cfa0df7336f9e784f9d3c0c04347f5fa833588e97"};
    uint8_t m[33], h[32], g[32];
    char hex[65];
    uint64_t d[4] = {0};
    m[0] = 0x43;
    for (int i = 0; i < 32; i++) { m[1 + i] = (uint8_t)i; d[i / 8] |= (uint64_t)i << (8 * (i % 8)); }
    chain_step(d);
    for (int i = 0; i < 32; i++) g[i] = (uint8_t)(d[i / 8] >> (8 * (i % 8)));
    for (int t = 0; t < 2; t++) {
        keccak256(h, m, t ? 33 : 0);
        for (int i = 0; i < 32; i++) snprintf(hex + 2 * i, 3, "%02x", h[i]);
        if (strcmp(hex, want[t])) return 1;
    }
    return memcmp(g, h, 32) != 0;
}

static void *work(void *arg) {
    long id = (long)arg;
    uint64_t sum = 0, d[CHAINS][4];
    for (int k = 0; k < CHAINS; k++)
        for (int i = 0; i < 4; i++) d[k][i] = 0x9E3779B97F4A7C15ull * (uint64_t)(id * CHAINS + k + 1) + (uint64_t)i;
    size_t words = MEM_BYTES / 8 / threads, base = words * id;
    pthread_barrier_wait(&bar);
    for (int r = 0; r < rounds; r++) {
        for (int i = 0; i < STEPS; i++)
            for (int k = 0; k < CHAINS; k++) chain_step(d[k]);
        for (size_t i = 0; i < words; i += 8) { mem[base + i] = mem[base + i] * 3 + (uint64_t)r; sum += mem[base + i]; }
    }
    for (int k = 0; k < CHAINS; k++) sum ^= d[k][0];
    return (void *)(uintptr_t)sum;
}

int main(int argc, char **argv) {
    if (self_test()) {
        fprintf(stderr, "calib: the Keccak-256 self-test failed (a miscompiled build)\n");
        return 2;
    }
    cpu_set_t cs;
    threads = (argc > 1) ? atoi(argv[1]) : (sched_getaffinity(0, sizeof cs, &cs) ? 1 : CPU_COUNT(&cs));
    rounds = (argc > 2) ? atoi(argv[2]) : 64;
    if (threads < 1 || rounds < 1) return 2;
    mem = aligned_alloc(64, MEM_BYTES);
    if (!mem) return 2;
    memset(mem, 1, MEM_BYTES);                         /* the pages exist before the clock starts */
    pthread_t *t = malloc(sizeof *t * threads);
    pthread_barrier_init(&bar, NULL, threads + 1);
    for (long i = 0; i < threads; i++) pthread_create(&t[i], NULL, work, (void *)i);
    struct timespec a, b;
    pthread_barrier_wait(&bar);
    clock_gettime(CLOCK_MONOTONIC, &a);
    uint64_t sum = 0;
    for (long i = 0; i < threads; i++) { void *s; pthread_join(t[i], &s); sum ^= (uint64_t)(uintptr_t)s; }
    clock_gettime(CLOCK_MONOTONIC, &b);
    printf("calib ns=%lld threads=%d rounds=%d sum=%016llx\n",
           (long long)(b.tv_sec - a.tv_sec) * 1000000000LL + (b.tv_nsec - a.tv_nsec), threads, rounds,
           (unsigned long long)sum);
    return 0;
}
