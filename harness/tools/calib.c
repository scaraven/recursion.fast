/*
 * The prover-shaped calibration workload `c_P` (TRUSTED organiser code; V4-A11 §5.4).
 *
 *   calib [THREADS [ROUNDS]]     prints `calib ns=NS threads=T rounds=R sum=HEX`
 *
 * Runs THREADS threads (default: the CPUs this process may use), each doing ROUNDS rounds (default
 * 64) of three kernels a recursive BLAKE2s prover spends its time in: a chain of carry-less
 * multiplications in GF(2^128) (`pclmulqdq`), 8-way AVX2 BLAKE2s compressions, and a read-modify-
 * write sweep over its share of a 256 MiB buffer (memory bandwidth). NS is the wall time from a
 * barrier that starts every thread to the last one's end; the sum keeps the work observable. It is
 * fixed per season (`calib_ref_ns` in the season file is its time on the reference runner) and
 * built from this source with the runner's `gcc` before any entry code runs (`run-benchmark.py`).
 * A CPU without AVX2 exits 2; without PCLMULQDQ (some virtual machines; every GitHub-hosted runner
 * has it, PROVER.md §1) the multiplication runs in software and the output says `clmul=soft`: such a
 * time is not comparable with `calib_ref_ns`.
 */
#define _GNU_SOURCE
#include <immintrin.h>
#include <pthread.h>
#include <sched.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MEM_BYTES (256u << 20)
#define CLMUL_ITERS 40000
#define B2S_ITERS 3000

static int threads, rounds;
static uint64_t *mem;
static pthread_barrier_t bar;

__attribute__((target("pclmul,sse4.1"))) static __m128i gf128_mul(__m128i a, __m128i b) {
    /* the 256-bit carry-less product, then x^128 = x^7 + x^2 + x + 1 folded in twice */
    __m128i lo = _mm_clmulepi64_si128(a, b, 0x00), hi = _mm_clmulepi64_si128(a, b, 0x11);
    __m128i mid = _mm_xor_si128(_mm_clmulepi64_si128(a, b, 0x01), _mm_clmulepi64_si128(a, b, 0x10));
    lo = _mm_xor_si128(lo, _mm_slli_si128(mid, 8));
    hi = _mm_xor_si128(hi, _mm_srli_si128(mid, 8));
    const __m128i R = _mm_set_epi64x(0, 0x87);
    __m128i t = _mm_clmulepi64_si128(hi, R, 0x01);
    hi = _mm_xor_si128(hi, _mm_srli_si128(t, 8));
    lo = _mm_xor_si128(lo, _mm_slli_si128(t, 8));
    return _mm_xor_si128(lo, _mm_clmulepi64_si128(hi, R, 0x00));
}

/* The same product without PCLMULQDQ: 64×64 carry-less multiplication bit by bit. */
static void clmul64(uint64_t a, uint64_t b, uint64_t *lo, uint64_t *hi) {
    uint64_t l = 0, h = 0;
    for (int i = 0; i < 64; i++)
        if (b >> i & 1) { l ^= a << i; h ^= i ? a >> (64 - i) : 0; }
    *lo = l; *hi = h;
}
__attribute__((target("sse4.1"))) static __m128i gf128_mul_soft(__m128i a, __m128i b) {
    uint64_t a0 = _mm_extract_epi64(a, 0), a1 = _mm_extract_epi64(a, 1);
    uint64_t b0 = _mm_extract_epi64(b, 0), b1 = _mm_extract_epi64(b, 1), l0, h0, l1, h1, l2, h2, l3, h3;
    clmul64(a0, b0, &l0, &h0); clmul64(a1, b1, &l1, &h1); clmul64(a0, b1, &l2, &h2); clmul64(a1, b0, &l3, &h3);
    uint64_t r0 = l0, r1 = h0 ^ l2 ^ l3, r2 = l1 ^ h2 ^ h3, r3 = h1, fl, fh;
    clmul64(r3, 0x87, &fl, &fh); r2 ^= fh; r1 ^= fl;
    clmul64(r2, 0x87, &fl, &fh); r1 ^= fh; r0 ^= fl;
    return _mm_set_epi64x((long long)r1, (long long)r0);
}
static __m128i (*mul)(__m128i, __m128i) = gf128_mul;

static const uint8_t SIGMA[10][16] = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}, {14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3},
    {11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4}, {7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8},
    {9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13}, {2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9},
    {12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11}, {13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10},
    {6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5}, {10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0}};
static const uint32_t IV[8] = {0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
                               0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19};

/* Eight independent BLAKE2s compressions, one per 32-bit lane; the output is the next message. */
__attribute__((target("avx2"))) static void b2s8(__m256i h[8], __m256i m[16]) {
    const __m256i r16 = _mm256_set_epi8(13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2,
                                        13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2);
    const __m256i r8 = _mm256_set_epi8(12, 15, 14, 13, 8, 11, 10, 9, 4, 7, 6, 5, 0, 3, 2, 1,
                                       12, 15, 14, 13, 8, 11, 10, 9, 4, 7, 6, 5, 0, 3, 2, 1);
    __m256i v[16];
    for (int i = 0; i < 8; i++) { v[i] = h[i]; v[i + 8] = _mm256_set1_epi32((int)IV[i]); }
    v[12] = _mm256_xor_si256(v[12], _mm256_set1_epi32(64));
    v[14] = _mm256_xor_si256(v[14], _mm256_set1_epi32(-1));
#define ROT(x, n) _mm256_or_si256(_mm256_srli_epi32(x, n), _mm256_slli_epi32(x, 32 - n))
#define G(a, b, c, d, x, y)                                                                           \
    v[a] = _mm256_add_epi32(_mm256_add_epi32(v[a], v[b]), x);                                         \
    v[d] = _mm256_shuffle_epi8(_mm256_xor_si256(v[d], v[a]), r16);                                    \
    v[c] = _mm256_add_epi32(v[c], v[d]); v[b] = ROT(_mm256_xor_si256(v[b], v[c]), 12);                \
    v[a] = _mm256_add_epi32(_mm256_add_epi32(v[a], v[b]), y);                                         \
    v[d] = _mm256_shuffle_epi8(_mm256_xor_si256(v[d], v[a]), r8);                                     \
    v[c] = _mm256_add_epi32(v[c], v[d]); v[b] = ROT(_mm256_xor_si256(v[b], v[c]), 7);
    for (int r = 0; r < 10; r++) {
        const uint8_t *s = SIGMA[r];
        G(0, 4, 8, 12, m[s[0]], m[s[1]]) G(1, 5, 9, 13, m[s[2]], m[s[3]])
        G(2, 6, 10, 14, m[s[4]], m[s[5]]) G(3, 7, 11, 15, m[s[6]], m[s[7]])
        G(0, 5, 10, 15, m[s[8]], m[s[9]]) G(1, 6, 11, 12, m[s[10]], m[s[11]])
        G(2, 7, 8, 13, m[s[12]], m[s[13]]) G(3, 4, 9, 14, m[s[14]], m[s[15]])
    }
    for (int i = 0; i < 8; i++) {
        h[i] = _mm256_xor_si256(h[i], _mm256_xor_si256(v[i], v[i + 8]));
        m[i] = h[i]; m[i + 8] = v[i + 8];
    }
}

__attribute__((target("avx2,pclmul,sse4.1"))) static void *work(void *arg) {
    long id = (long)arg;
    uint64_t sum = 0;
    __m128i x = _mm_set_epi64x(id + 1, 0x9E3779B97F4A7C15ull), y = _mm_set_epi64x(0x243F6A8885A308D3ull, id);
    __m256i h[8], m[16];
    for (int i = 0; i < 8; i++) h[i] = _mm256_set1_epi32((int)(IV[i] ^ id));
    for (int i = 0; i < 16; i++) m[i] = _mm256_set1_epi32(i + (int)id);
    size_t words = MEM_BYTES / 8 / threads, base = words * id;
    pthread_barrier_wait(&bar);
    for (int r = 0; r < rounds; r++) {
        for (int i = 0; i < CLMUL_ITERS; i++) x = mul(x, y);
        for (int i = 0; i < B2S_ITERS; i++) b2s8(h, m);
        for (size_t i = 0; i < words; i += 8) { mem[base + i] = mem[base + i] * 3 + (uint64_t)r; sum += mem[base + i]; }
    }
    sum ^= (uint64_t)_mm_extract_epi64(x, 0) ^ (uint64_t)_mm256_extract_epi32(h[0], 0);
    return (void *)(uintptr_t)sum;
}

int main(int argc, char **argv) {
    __builtin_cpu_init();
    if (!__builtin_cpu_supports("avx2")) {
        fprintf(stderr, "calib: this CPU lacks AVX2\n");
        return 2;
    }
    int hw = __builtin_cpu_supports("pclmul");
    if (!hw) mul = gf128_mul_soft;
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
    printf("calib ns=%lld threads=%d rounds=%d clmul=%s sum=%016llx\n",
           (long long)(b.tv_sec - a.tv_sec) * 1000000000LL + (b.tv_nsec - a.tv_nsec), threads, rounds,
           hw ? "hw" : "soft", (unsigned long long)sum);
    return 0;
}
