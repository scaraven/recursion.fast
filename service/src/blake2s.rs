//! BLAKE2s-256 (RFC 7693), unkeyed and keyed, in two implementations that compute the same
//! function: a portable scalar one (`compress`, `Hasher`), and an AVX2 one that hashes up to
//! eight independent messages at once (`hash_many`), used when the CPU has AVX2. Both are tested
//! against each other and against Python's `hashlib.blake2s` (`tests/service/`).
//!
//! Only 32-byte digests are produced. A keyed hash has a 32-byte key: the parameter block's key
//! length is 32 and the zero-padded key is the first message block (RFC 7693 §3.3); that block is
//! the final one exactly when the message is empty.

/// The BLAKE2s initialisation vector (RFC 7693 §2.6).
pub const IV: [u32; 8] = [
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];

/// The message schedule (RFC 7693 §2.7).
const SIGMA: [[usize; 16]; 10] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
];

/// A 32-byte digest.
pub type Digest = [u8; 32];

/// The chaining value before the first block, for a 32-byte digest and a key of `kk` bytes
/// (parameter block `0x0101kknn`, RFC 7693 §2.5).
pub fn init(kk: u32) -> [u32; 8] {
    let mut h = IV;
    h[0] ^= 0x0101_0000 ^ (kk << 8) ^ 32;
    h
}

/// The ten rounds of F (RFC 7693 §3.2) on the work vector `$v` and the message words `$m`, with
/// the mixing function `$g`; unrolled, so that every message index is a constant.
macro_rules! rounds {
    ($g:ident, $v:ident, $m:ident) => {
        rounds!(@ $g, $v, $m, 0 1 2 3 4 5 6 7 8 9)
    };
    (@ $g:ident, $v:ident, $m:ident, $($r:literal)*) => {$({
        let s = &SIGMA[$r];
        $g(&mut $v, [0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13, 14, 15],
           [$m[s[0]], $m[s[2]], $m[s[4]], $m[s[6]]], [$m[s[1]], $m[s[3]], $m[s[5]], $m[s[7]]]);
        $g(&mut $v, [0, 1, 2, 3], [5, 6, 7, 4], [10, 11, 8, 9], [15, 12, 13, 14],
           [$m[s[8]], $m[s[10]], $m[s[12]], $m[s[14]]], [$m[s[9]], $m[s[11]], $m[s[13]], $m[s[15]]]);
    })*};
}

/// Four indices of the work vector: the columns or the diagonals of one half-round.
type Cols = [usize; 4];

/// The mixing function G (RFC 7693 §3.1) on four columns (or diagonals) at once, step by step.
#[inline(always)]
fn g(v: &mut [u32; 16], a: Cols, b: Cols, c: Cols, d: Cols, x: [u32; 4], y: [u32; 4]) {
    for i in 0..4 { v[a[i]] = v[a[i]].wrapping_add(v[b[i]]).wrapping_add(x[i]); }
    for i in 0..4 { v[d[i]] = (v[d[i]] ^ v[a[i]]).rotate_right(16); }
    for i in 0..4 { v[c[i]] = v[c[i]].wrapping_add(v[d[i]]); }
    for i in 0..4 { v[b[i]] = (v[b[i]] ^ v[c[i]]).rotate_right(12); }
    for i in 0..4 { v[a[i]] = v[a[i]].wrapping_add(v[b[i]]).wrapping_add(y[i]); }
    for i in 0..4 { v[d[i]] = (v[d[i]] ^ v[a[i]]).rotate_right(8); }
    for i in 0..4 { v[c[i]] = v[c[i]].wrapping_add(v[d[i]]); }
    for i in 0..4 { v[b[i]] = (v[b[i]] ^ v[c[i]]).rotate_right(7); }
}

/// The compression function F (RFC 7693 §3.2): `t` counts the bytes hashed so far including this
/// block's, `last` marks the final block.
pub fn compress(h: &mut [u32; 8], block: &[u8; 64], t: u64, last: bool) {
    let mut m = [0u32; 16];
    for (i, w) in m.iter_mut().enumerate() {
        *w = u32::from_le_bytes([block[4 * i], block[4 * i + 1], block[4 * i + 2], block[4 * i + 3]]);
    }
    let mut v = [0u32; 16];
    v[..8].copy_from_slice(h);
    v[8..].copy_from_slice(&IV);
    v[12] ^= t as u32;
    v[13] ^= (t >> 32) as u32;
    if last {
        v[14] = !v[14];
    }
    rounds!(g, v, m);
    for i in 0..8 {
        h[i] ^= v[i] ^ v[i + 8];
    }
}

/// The digest bytes of a chaining value (little-endian words).
pub fn output(h: &[u32; 8]) -> Digest {
    let mut out = [0u8; 32];
    for i in 0..8 {
        out[4 * i..4 * i + 4].copy_from_slice(&h[i].to_le_bytes());
    }
    out
}

/// Incremental BLAKE2s-256. A full buffered block is compressed only when more input arrives, so
/// that `finalize` can mark the last block.
#[derive(Clone)]
pub struct Hasher {
    h: [u32; 8],
    t: u64,
    buf: [u8; 64],
    n: usize,
}

impl Hasher {
    /// Unkeyed BLAKE2s-256.
    pub fn new() -> Self {
        Hasher { h: init(0), t: 0, buf: [0; 64], n: 0 }
    }

    /// Keyed BLAKE2s-256 with a 32-byte key: the padded key is buffered as the first block.
    pub fn new_keyed(key: &[u8; 32]) -> Self {
        let mut buf = [0u8; 64];
        buf[..32].copy_from_slice(key);
        Hasher { h: init(32), t: 0, buf, n: 64 }
    }

    /// Continue from a chaining value `h` after `t` bytes were compressed (no buffered input).
    pub fn resume(h: [u32; 8], t: u64) -> Self {
        Hasher { h, t, buf: [0; 64], n: 0 }
    }

    /// Absorb `data`.
    pub fn update(&mut self, mut data: &[u8]) -> &mut Self {
        while !data.is_empty() {
            if self.n == 64 {
                self.t += 64;
                compress(&mut self.h, &self.buf, self.t, false);
                self.n = 0;
            }
            let k = (64 - self.n).min(data.len());
            self.buf[self.n..self.n + k].copy_from_slice(&data[..k]);
            self.n += k;
            data = &data[k..];
        }
        self
    }

    /// The digest.
    pub fn finalize(&self) -> Digest {
        let mut h = self.h;
        let mut buf = self.buf;
        buf[self.n..].fill(0);
        compress(&mut h, &buf, self.t + self.n as u64, true);
        output(&h)
    }
}

impl Default for Hasher {
    fn default() -> Self {
        Self::new()
    }
}

/// Unkeyed BLAKE2s-256 of `m`.
pub fn hash(m: &[u8]) -> Digest {
    Hasher::new().update(m).finalize()
}

/// A keyed BLAKE2s-256 function `q ↦ BLAKE2s-256_key(q)` with the key block compressed once:
/// `mid` is the chaining value after the (non-final) key block, used for every non-empty
/// message; the empty message, whose final block is the key block, has its answer cached.
pub struct Keyed {
    mid: [u32; 8],
    empty: Digest,
}

impl Keyed {
    /// Precompute the key block for `key`.
    pub fn new(key: &[u8; 32]) -> Self {
        let mut block = [0u8; 64];
        block[..32].copy_from_slice(key);
        let mut mid = init(32);
        compress(&mut mid, &block, 64, false);
        let mut kh = Hasher::new_keyed(key);
        let empty = kh.finalize();
        wipe(&mut kh.buf); // the key block (RF-m22)
        wipe(&mut kh.h);
        wipe(&mut block);
        Keyed { mid, empty }
    }

    /// `BLAKE2s-256_key(q)`.
    pub fn eval(&self, q: &[u8]) -> Digest {
        if q.is_empty() {
            self.empty
        } else {
            Hasher::resume(self.mid, 64).update(q).finalize()
        }
    }

    /// Answers for many messages: `out[i] = BLAKE2s-256_key(msgs[i])`, eight at a time when the
    /// CPU has AVX2 (messages sorted by length by the caller hash fastest).
    pub fn eval_many(&self, msgs: &[&[u8]], out: &mut [Digest]) {
        assert_eq!(msgs.len(), out.len());
        let mut i = 0;
        while i < msgs.len() {
            // a run of non-empty messages goes to `hash_many`; an empty one is the cached answer
            if msgs[i].is_empty() {
                out[i] = self.empty;
                i += 1;
                continue;
            }
            let mut j = i;
            while j < msgs.len() && !msgs[j].is_empty() {
                j += 1;
            }
            hash_many(&self.mid, 64, &msgs[i..j], &mut out[i..j]);
            i = j;
        }
    }

    /// Overwrite the key material.
    pub fn wipe(&mut self) {
        wipe(&mut self.mid);
        wipe(&mut self.empty);
    }
}

/// Overwrite `b` with zeros (volatile writes, one per element, so that they are not optimised
/// away).
pub fn wipe<T: Copy + Default>(b: &mut [T]) {
    for x in b.iter_mut() {
        unsafe { std::ptr::write_volatile(x, T::default()) };
    }
    std::sync::atomic::compiler_fence(std::sync::atomic::Ordering::SeqCst);
}

/// Hash many messages from the chaining value `h0` with `t0` bytes already compressed (`0` for
/// unkeyed BLAKE2s-256 from `init(0)`; `64` after a cached key block, in which case no message may
/// be empty): `out[i]` is the digest of `msgs[i]`. Uses the AVX2 eight-way compression when
/// available, otherwise the scalar one; the results are the same.
pub fn hash_many(h0: &[u32; 8], t0: u64, msgs: &[&[u8]], out: &mut [Digest]) {
    assert_eq!(msgs.len(), out.len());
    debug_assert!(t0 == 0 || msgs.iter().all(|m| !m.is_empty()));
    #[cfg(target_arch = "x86_64")]
    {
        if msgs.len() >= 2 && has_avx2() {
            for (m, o) in msgs.chunks(8).zip(out.chunks_mut(8)) {
                if m.len() == 1 {
                    o[0] = Hasher::resume(*h0, t0).update(m[0]).finalize();
                } else {
                    unsafe { avx2::hash8(h0, t0, m, o) };
                }
            }
            return;
        }
    }
    for (m, o) in msgs.iter().zip(out.iter_mut()) {
        *o = Hasher::resume(*h0, t0).update(m).finalize();
    }
}

/// Whether the AVX2 path is used (the CPU has AVX2 and `RF_ORACLE_NO_SIMD` is unset).
pub fn has_avx2() -> bool {
    use std::sync::OnceLock;
    static AVX2: OnceLock<bool> = OnceLock::new();
    *AVX2.get_or_init(|| {
        #[cfg(target_arch = "x86_64")]
        {
            std::env::var_os("RF_ORACLE_NO_SIMD").is_none() && std::is_x86_feature_detected!("avx2")
        }
        #[cfg(not(target_arch = "x86_64"))]
        {
            false
        }
    })
}

/// Eight-way BLAKE2s compression with AVX2: lane `l` of every vector belongs to message `l`.
#[cfg(target_arch = "x86_64")]
mod avx2 {
    use super::{Cols, Digest, IV, SIGMA};
    use std::arch::x86_64::*;

    #[inline(always)]
    unsafe fn add(a: __m256i, b: __m256i) -> __m256i {
        _mm256_add_epi32(a, b)
    }
    #[inline(always)]
    unsafe fn xor(a: __m256i, b: __m256i) -> __m256i {
        _mm256_xor_si256(a, b)
    }
    #[inline(always)]
    unsafe fn rot16(x: __m256i) -> __m256i {
        _mm256_or_si256(_mm256_srli_epi32(x, 16), _mm256_slli_epi32(x, 16))
    }
    #[inline(always)]
    unsafe fn rot12(x: __m256i) -> __m256i {
        _mm256_or_si256(_mm256_srli_epi32(x, 12), _mm256_slli_epi32(x, 20))
    }
    #[inline(always)]
    unsafe fn rot8(x: __m256i) -> __m256i {
        _mm256_shuffle_epi8(
            x,
            _mm256_set_epi8(
                12, 15, 14, 13, 8, 11, 10, 9, 4, 7, 6, 5, 0, 3, 2, 1, 12, 15, 14, 13, 8, 11, 10, 9, 4, 7,
                6, 5, 0, 3, 2, 1,
            ),
        )
    }
    #[inline(always)]
    unsafe fn rot7(x: __m256i) -> __m256i {
        _mm256_or_si256(_mm256_srli_epi32(x, 7), _mm256_slli_epi32(x, 25))
    }

    #[inline(always)]
    unsafe fn g(v: &mut [__m256i; 16], a: Cols, b: Cols, c: Cols, d: Cols, x: [__m256i; 4], y: [__m256i; 4]) {
        for i in 0..4 { v[a[i]] = add(add(v[a[i]], v[b[i]]), x[i]); }
        for i in 0..4 { v[d[i]] = rot16(xor(v[d[i]], v[a[i]])); }
        for i in 0..4 { v[c[i]] = add(v[c[i]], v[d[i]]); }
        for i in 0..4 { v[b[i]] = rot12(xor(v[b[i]], v[c[i]])); }
        for i in 0..4 { v[a[i]] = add(add(v[a[i]], v[b[i]]), y[i]); }
        for i in 0..4 { v[d[i]] = rot8(xor(v[d[i]], v[a[i]])); }
        for i in 0..4 { v[c[i]] = add(v[c[i]], v[d[i]]); }
        for i in 0..4 { v[b[i]] = rot7(xor(v[b[i]], v[c[i]])); }
    }

    /// 8x8 transpose of 32-bit words: row `i` of the input is column `i` of the output.
    #[inline(always)]
    unsafe fn transpose(x: &mut [__m256i; 8]) {
        let ab_0145 = _mm256_unpacklo_epi32(x[0], x[1]);
        let ab_2367 = _mm256_unpackhi_epi32(x[0], x[1]);
        let cd_0145 = _mm256_unpacklo_epi32(x[2], x[3]);
        let cd_2367 = _mm256_unpackhi_epi32(x[2], x[3]);
        let ef_0145 = _mm256_unpacklo_epi32(x[4], x[5]);
        let ef_2367 = _mm256_unpackhi_epi32(x[4], x[5]);
        let gh_0145 = _mm256_unpacklo_epi32(x[6], x[7]);
        let gh_2367 = _mm256_unpackhi_epi32(x[6], x[7]);
        let abcd_04 = _mm256_unpacklo_epi64(ab_0145, cd_0145);
        let abcd_15 = _mm256_unpackhi_epi64(ab_0145, cd_0145);
        let abcd_26 = _mm256_unpacklo_epi64(ab_2367, cd_2367);
        let abcd_37 = _mm256_unpackhi_epi64(ab_2367, cd_2367);
        let efgh_04 = _mm256_unpacklo_epi64(ef_0145, gh_0145);
        let efgh_15 = _mm256_unpackhi_epi64(ef_0145, gh_0145);
        let efgh_26 = _mm256_unpacklo_epi64(ef_2367, gh_2367);
        let efgh_37 = _mm256_unpackhi_epi64(ef_2367, gh_2367);
        x[0] = _mm256_permute2x128_si256(abcd_04, efgh_04, 0x20);
        x[1] = _mm256_permute2x128_si256(abcd_15, efgh_15, 0x20);
        x[2] = _mm256_permute2x128_si256(abcd_26, efgh_26, 0x20);
        x[3] = _mm256_permute2x128_si256(abcd_37, efgh_37, 0x20);
        x[4] = _mm256_permute2x128_si256(abcd_04, efgh_04, 0x31);
        x[5] = _mm256_permute2x128_si256(abcd_15, efgh_15, 0x31);
        x[6] = _mm256_permute2x128_si256(abcd_26, efgh_26, 0x31);
        x[7] = _mm256_permute2x128_si256(abcd_37, efgh_37, 0x31);
    }

    /// Compress one block per lane: `blocks[l]` is lane `l`'s block, `t` and `f` its counter and
    /// final flag; lanes with `active[l] == false` keep their chaining value.
    #[inline(always)]
    unsafe fn compress8(h: &mut [__m256i; 8], blocks: &[&[u8; 64]; 8], t: &[u64; 8], f: &[u32; 8], active: &[u32; 8]) {
        let ld = |p: *const u8| _mm256_loadu_si256(p as *const __m256i);
        let mut lo: [__m256i; 8] = core::array::from_fn(|l| ld(blocks[l].as_ptr()));
        let mut hi: [__m256i; 8] = core::array::from_fn(|l| ld(blocks[l][32..].as_ptr()));
        transpose(&mut lo);
        transpose(&mut hi);
        let m = [
            lo[0], lo[1], lo[2], lo[3], lo[4], lo[5], lo[6], lo[7], hi[0], hi[1], hi[2], hi[3], hi[4], hi[5],
            hi[6], hi[7],
        ];
        let tl: [u32; 8] = core::array::from_fn(|l| t[l] as u32);
        let th: [u32; 8] = core::array::from_fn(|l| (t[l] >> 32) as u32);
        let ldw = |a: &[u32; 8]| ld(a.as_ptr() as *const u8);
        let mut v = [
            h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7],
            _mm256_set1_epi32(IV[0] as i32), _mm256_set1_epi32(IV[1] as i32),
            _mm256_set1_epi32(IV[2] as i32), _mm256_set1_epi32(IV[3] as i32),
            xor(_mm256_set1_epi32(IV[4] as i32), ldw(&tl)), xor(_mm256_set1_epi32(IV[5] as i32), ldw(&th)),
            xor(_mm256_set1_epi32(IV[6] as i32), ldw(f)), _mm256_set1_epi32(IV[7] as i32),
        ];
        rounds!(g, v, m);
        let mask = ldw(active);
        for i in 0..8 {
            let new = xor(h[i], xor(v[i], v[i + 8]));
            h[i] = _mm256_blendv_epi8(h[i], new, mask);
        }
    }

    /// Hash 2 ≤ `msgs.len()` ≤ 8 messages from `h0` after `t0` bytes; lane `l` runs
    /// `max(1, ⌈|m_l| / 64⌉)` blocks and idles (keeps its value) for the rest. A full block is
    /// read in place; only a message's partial last block is copied, into the zeroed `pad[l]`.
    #[target_feature(enable = "avx2")]
    pub unsafe fn hash8(h0: &[u32; 8], t0: u64, msgs: &[&[u8]], out: &mut [Digest]) {
        let k = msgs.len();
        debug_assert!((1..=8).contains(&k));
        let nb: [usize; 8] = core::array::from_fn(|l| msgs.get(l).map_or(0, |m| m.len().div_ceil(64).max(1)));
        let mut h: [__m256i; 8] = core::array::from_fn(|i| _mm256_set1_epi32(h0[i] as i32));
        let mut pad = [[0u8; 64]; 8];
        for b in 0..nb.iter().copied().max().unwrap_or(0) {
            let s = 64 * b;
            for l in 0..k {
                let m = msgs[l];
                if b < nb[l] && m.len() < s + 64 {
                    pad[l][..m.len() - s].copy_from_slice(&m[s..]); // once per lane: its last block
                }
            }
            let blocks: [&[u8; 64]; 8] = core::array::from_fn(|l| match msgs.get(l) {
                Some(m) if m.len() >= s + 64 => m[s..s + 64].try_into().unwrap(),
                _ => &pad[l],
            });
            let len = |l: usize| msgs.get(l).map_or(0, |m| m.len() as u64);
            let t: [u64; 8] = core::array::from_fn(|l| t0 + len(l).min(s as u64 + 64));
            let f: [u32; 8] = core::array::from_fn(|l| if b + 1 == nb[l] { u32::MAX } else { 0 });
            let active: [u32; 8] = core::array::from_fn(|l| if b < nb[l] { u32::MAX } else { 0 });
            compress8(&mut h, &blocks, &t, &f, &active);
        }
        transpose(&mut h);
        for l in 0..k {
            _mm256_storeu_si256(out[l].as_mut_ptr() as *mut __m256i, h[l]);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(d: &[u8]) -> String {
        d.iter().map(|b| format!("{b:02x}")).collect()
    }

    #[test]
    fn rfc7693_abc() {
        // RFC 7693 Appendix B: BLAKE2s-256("abc")
        assert_eq!(hex(&hash(b"abc")), "508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982");
    }

    #[test]
    fn empty_message() {
        // hashlib.blake2s(b"").hexdigest()
        assert_eq!(hex(&hash(b"")), "69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9");
    }

    fn lcg(seed: &mut u64) -> u8 {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (*seed >> 33) as u8
    }

    #[test]
    fn many_equals_scalar() {
        let mut seed = 7u64;
        let lens = [0usize, 1, 31, 32, 33, 55, 63, 64, 65, 100, 127, 128, 129, 191, 192, 193, 1000, 4265, 4096, 9];
        let msgs: Vec<Vec<u8>> = lens.iter().map(|&n| (0..n).map(|_| lcg(&mut seed)).collect()).collect();
        let refs: Vec<&[u8]> = msgs.iter().map(|m| m.as_slice()).collect();
        let mut out = vec![[0u8; 32]; refs.len()];
        hash_many(&init(0), 0, &refs, &mut out);
        for (m, o) in refs.iter().zip(&out) {
            assert_eq!(*o, hash(m));
        }
        let key: [u8; 32] = core::array::from_fn(|i| i as u8);
        let kd = Keyed::new(&key);
        let mut out2 = vec![[0u8; 32]; refs.len()];
        kd.eval_many(&refs, &mut out2);
        for (m, o) in refs.iter().zip(&out2) {
            assert_eq!(*o, Hasher::new_keyed(&key).update(m).finalize());
            assert_eq!(*o, kd.eval(m));
        }
    }
}
