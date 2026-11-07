/* Keccak-256 (Ethereum's) for the service tests: an independent reference, written from FIPS 202
 * alone, not from the service's code. Not part of the runtime. `wots_ref.py` compiles it into a
 * temporary shared object and calls it through ctypes; `test_service.py` checks it against the
 * published vectors and against `harness/rfh/keccak.py`.
 *
 * The step mappings follow FIPS 202 §3.2 literally on a state A[x][y] of 64-bit lanes; the round
 * constants (Algorithms 5 and 6) and the rho offsets (Algorithm 2) are not tabulated: they are
 * computed by `rf_keccak_init`, which the caller runs once after loading. Sponge: rate 136 bytes,
 * Keccak's padding 0x01 ... 0x80 (FIPS 202's pad10*1 with no suffix bits, not SHA-3's 01), output
 * the first 32 bytes of the state. */
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#define RATE 136

static uint64_t round_const[24];
static unsigned rho_off[5][5];

static uint64_t rotl(uint64_t v, unsigned r) { r %= 64; return r ? (v << r) | (v >> (64 - r)) : v; }

/* FIPS 202 Algorithm 5: bit R[k] of the 8-bit register is bit k of `reg`. */
static int rc_bit(unsigned t) {
    unsigned reg = 1; /* R = 10000000 */
    if (t % 255 == 0) return 1;
    for (unsigned i = 1; i <= t % 255; i++) {
        reg <<= 1; /* R = 0 || R */
        unsigned r8 = (reg >> 8) & 1;
        reg ^= r8 | (r8 << 4) | (r8 << 5) | (r8 << 6);
        reg &= 0xff; /* Trunc8 */
    }
    return reg & 1;
}

void rf_keccak_init(void) {
    for (unsigned ir = 0; ir < 24; ir++) { /* Algorithm 6 */
        uint64_t rc = 0;
        for (unsigned j = 0; j <= 6; j++)
            if (rc_bit(j + 7 * ir)) rc |= (uint64_t)1 << ((1u << j) - 1);
        round_const[ir] = rc;
    }
    unsigned x = 1, y = 0; /* Algorithm 2 */
    rho_off[0][0] = 0;
    for (unsigned t = 0; t < 24; t++) {
        rho_off[x][y] = ((t + 1) * (t + 2) / 2) % 64;
        unsigned nx = y, ny = (2 * x + 3 * y) % 5;
        x = nx;
        y = ny;
    }
}

static void keccak_p(uint64_t A[5][5]) {
    uint64_t C[5], D[5], B[5][5];
    for (unsigned ir = 0; ir < 24; ir++) {
        for (unsigned x = 0; x < 5; x++) C[x] = A[x][0] ^ A[x][1] ^ A[x][2] ^ A[x][3] ^ A[x][4];
        for (unsigned x = 0; x < 5; x++) D[x] = C[(x + 4) % 5] ^ rotl(C[(x + 1) % 5], 1);
        for (unsigned x = 0; x < 5; x++)
            for (unsigned y = 0; y < 5; y++) A[x][y] ^= D[x];                      /* theta */
        for (unsigned x = 0; x < 5; x++)
            for (unsigned y = 0; y < 5; y++) A[x][y] = rotl(A[x][y], rho_off[x][y]); /* rho */
        for (unsigned x = 0; x < 5; x++)
            for (unsigned y = 0; y < 5; y++) B[x][y] = A[(x + 3 * y) % 5][x];       /* pi */
        for (unsigned x = 0; x < 5; x++)
            for (unsigned y = 0; y < 5; y++)
                A[x][y] = B[x][y] ^ (~B[(x + 1) % 5][y] & B[(x + 2) % 5][y]);       /* chi */
        A[0][0] ^= round_const[ir];                                                /* iota */
    }
}

/* XOR byte `b` into state byte `i` (byte i is bit 8i of the state string: lane i / 8, x + 5y). */
static void xor_byte(uint64_t A[5][5], size_t i, uint8_t b) {
    size_t lane = i / 8;
    A[lane % 5][lane / 5] ^= (uint64_t)b << (8 * (i % 8));
}

void rf_keccak256(const uint8_t *m, size_t n, uint8_t *out) {
    uint64_t A[5][5];
    memset(A, 0, sizeof A);
    size_t off = 0;
    for (; n - off >= RATE; off += RATE) {
        for (size_t i = 0; i < RATE; i++) xor_byte(A, i, m[off + i]);
        keccak_p(A);
    }
    for (size_t i = 0; i < n - off; i++) xor_byte(A, i, m[off + i]);
    xor_byte(A, n - off, 0x01);
    xor_byte(A, RATE - 1, 0x80);
    keccak_p(A);
    for (size_t i = 0; i < 32; i++) {
        size_t lane = i / 8;
        out[i] = (uint8_t)(A[lane % 5][lane / 5] >> (8 * (i % 8)));
    }
}

/* `count` messages of `n` bytes each, back to back in `m`; digest k goes to out[32k .. 32k + 31]. */
void rf_keccak256_many(const uint8_t *m, size_t n, size_t count, uint8_t *out) {
    for (size_t k = 0; k < count; k++) rf_keccak256(m + k * n, n, out + 32 * k);
}
