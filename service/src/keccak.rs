//! Keccak-256 as Ethereum uses it: the sponge of FIPS 202 over Keccak-f[1600] with rate 136 bytes
//! (capacity 512 bits), a 32-byte output and Keccak's original padding: the byte `0x01` after the
//! message, zeros to the end of the block, and `0x80` XORed into the block's last byte (one padding
//! byte is `0x81`). It is not SHA3-256, whose first padding byte is `0x06`.
//! `RecursionFast/Contract/Hash/Keccak.lean` is the normative definition.
//!
//! Written from FIPS 202 (§3.2 the step mappings, §5.1 `pad10*1`), scalar and std only. The state is
//! 25 lanes, lane `x + 5y` holding `A[x, y]` as the little-endian 64-bit word of 8 state bytes; the
//! first 17 lanes are the rate. A message of `n` bytes costs `⌊n / 136⌋ + 1` permutations.
//!
//! The keyed hash is `Keccak-256(k ‖ q)` with a 32-byte key `k`: a key prefix of fixed length, so
//! the key bytes are the first 32 bytes of the first block.

/// A 32-byte digest.
pub type Digest = [u8; 32];

/// The sponge rate in bytes.
pub const RATE: usize = 136;

/// The ι round constants (FIPS 202 §3.2.5, `RC[i_r]` for rounds `i_r = 0 … 23`).
const RC: [u64; 24] = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
];

/// The ρ rotation (left) of lane `x + 5y` (FIPS 202 §3.2.2, Table 2).
const RHO: [u32; 25] = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14];

/// Keccak-f[1600]: 24 rounds of θ, ρ, π, χ, ι (FIPS 202 §3.3).
pub fn keccak_f(a: &mut [u64; 25]) {
    for rc in RC {
        // θ: every lane is XORed with the parities of two neighbouring columns
        let c: [u64; 5] = core::array::from_fn(|x| a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20]);
        for x in 0..5 {
            let d = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
            for y in 0..5 {
                a[x + 5 * y] ^= d;
            }
        }
        // ρ and π: B[y, 2x + 3y] = rot(A[x, y], RHO[x + 5y])
        let mut b = [0u64; 25];
        for x in 0..5 {
            for y in 0..5 {
                b[y + 5 * ((2 * x + 3 * y) % 5)] = a[x + 5 * y].rotate_left(RHO[x + 5 * y]);
            }
        }
        // χ: A[x, y] = B[x, y] ⊕ (¬B[x + 1, y] ∧ B[x + 2, y])
        for y in 0..5 {
            for x in 0..5 {
                a[x + 5 * y] = b[x + 5 * y] ^ (!b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]);
            }
        }
        // ι
        a[0] ^= rc;
    }
}

/// XOR one block into the rate and permute.
fn absorb(a: &mut [u64; 25], block: &[u8; RATE]) {
    for (lane, w) in a.iter_mut().zip(block.as_chunks::<8>().0) {
        *lane ^= u64::from_le_bytes(*w);
    }
    keccak_f(a);
}

/// Incremental Keccak-256: the state after the absorbed full blocks and the bytes of the block in
/// progress (`n < RATE` of them).
#[derive(Clone)]
pub struct Hasher {
    a: [u64; 25],
    buf: [u8; RATE],
    n: usize,
}

impl Hasher {
    /// The empty message.
    pub fn new() -> Self {
        Hasher { a: [0; 25], buf: [0; RATE], n: 0 }
    }

    /// Append `data`.
    pub fn update(&mut self, mut data: &[u8]) -> &mut Self {
        while !data.is_empty() {
            if self.n == 0 && data.len() >= RATE {
                let (block, rest) = data.split_first_chunk::<RATE>().unwrap();
                absorb(&mut self.a, block);
                data = rest;
                continue;
            }
            let k = (RATE - self.n).min(data.len());
            self.buf[self.n..self.n + k].copy_from_slice(&data[..k]);
            self.n += k;
            data = &data[k..];
            if self.n == RATE {
                absorb(&mut self.a, &self.buf);
                self.n = 0;
            }
        }
        self
    }

    /// Pad the message, absorb the last block and output the digest: the first 32 state bytes.
    /// Leaves the state and the buffer zeroed (the state of a keyed hash determines its key).
    pub fn finalize(&mut self) -> Digest {
        self.buf[self.n..].fill(0);
        self.buf[self.n] ^= 0x01;
        self.buf[RATE - 1] ^= 0x80;
        absorb(&mut self.a, &self.buf);
        let mut out = [0u8; 32];
        for (o, lane) in out.as_chunks_mut::<8>().0.iter_mut().zip(&self.a) {
            *o = lane.to_le_bytes();
        }
        // one volatile store of each whole array, so that it is not optimised away
        unsafe {
            std::ptr::write_volatile(&mut self.a, [0; 25]);
            std::ptr::write_volatile(&mut self.buf, [0; RATE]);
        }
        self.n = 0;
        out
    }
}

impl Default for Hasher {
    fn default() -> Self {
        Self::new()
    }
}

/// Keccak-256 of `m`.
pub fn hash(m: &[u8]) -> Digest {
    Hasher::new().update(m).finalize()
}

/// Number of permutations of Keccak-256 on `n` bytes.
pub fn permutations(n: usize) -> usize {
    n / RATE + 1
}

/// The keyed hash `q ↦ Keccak-256(k ‖ q)` for a 32-byte key `k`, held as a hasher with the key
/// already in its first block.
pub struct Keyed {
    pre: Hasher,
}

impl Keyed {
    /// The keyed hash under `key`.
    pub fn new(key: &[u8; 32]) -> Self {
        let mut pre = Hasher::new();
        pre.update(key);
        Keyed { pre }
    }

    /// `Keccak-256(k ‖ q)`; `⌊(32 + |q|) / 136⌋ + 1` permutations.
    pub fn eval(&self, q: &[u8]) -> Digest {
        self.pre.clone().update(q).finalize()
    }

    /// `out[i] = Keccak-256(k ‖ msgs[i])`.
    pub fn eval_many(&self, msgs: &[&[u8]], out: &mut [Digest]) {
        assert_eq!(msgs.len(), out.len());
        for (m, o) in msgs.iter().zip(out.iter_mut()) {
            *o = self.eval(m);
        }
    }

    /// Overwrite the key.
    pub fn wipe(&mut self) {
        wipe(&mut self.pre.buf);
        wipe(&mut self.pre.a);
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

#[cfg(test)]
mod tests {
    use super::*;

    pub fn hex(d: &[u8]) -> String {
        d.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// leanVM's test pattern.
    fn pattern(n: usize) -> Vec<u8> {
        (0..n).map(|i| ((7 * i + 3) % 256) as u8).collect()
    }

    #[test]
    fn vectors() {
        let cases: [(&[u8], &str); 2] = [
            (b"", "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"),
            (b"abc", "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"),
        ];
        for (m, d) in cases {
            assert_eq!(hex(&hash(m)), d);
        }
        let pat = [
            (135, "00ef96af9cf4b24c7f269d922294444a197d0a33638c2e56634c57e892103a8f"),
            (136, "742061bcad767ed4c4f5883b1dcb1aad11afdcc140dc469d953759b127b9f9ed"),
            (137, "e3371f61e770abf254c34239c3b0099ad90594507415bc81dd0a10b9692bbf2a"),
            (271, "4401c4afbe16ff911bdbf2d38e556e5b861f3fdf0f9d4306b1c46f6ae4f73584"),
            (272, "ac141fd7b0a0ffcd2e967254d508da3ec616596493c36fa304425647d90e6de5"),
        ];
        for (n, d) in pat {
            assert_eq!(hex(&hash(&pattern(n))), d, "pattern({n})");
        }
        // a chain step: "C" ‖ 00 01 … 1f
        let mut step = vec![0x43u8];
        step.extend(0..32u8);
        assert_eq!(hex(&hash(&step)), "db8c51208716e57c91fc944cfa0df7336f9e784f9d3c0c04347f5fa833588e97");
    }

    #[test]
    fn incremental_equals_one_shot() {
        let m = pattern(1000);
        for split in [0, 1, 35, 103, 104, 135, 136, 137, 271, 272, 999, 1000] {
            let mut h = Hasher::new();
            h.update(&m[..split]).update(&m[split..]);
            assert_eq!(h.finalize(), hash(&m), "split at {split}");
        }
    }

    #[test]
    fn keyed() {
        // harness/rfh/keccak.py `keyed(bytes(range(32)), pattern(n))`, cross-checked with pycryptodome
        let key: [u8; 32] = core::array::from_fn(|i| i as u8);
        let kd = Keyed::new(&key);
        let cases = [
            (0, "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d"),
            (1, "c0a2a2460b6a12938ebd31825058add79257242e4479430c68dc2dea4f77e539"),
            (103, "ee17fa0bccfc9ef064b3c29cfaafeef311386ca16ac0f5ab7e63e1fa4bcb8b1e"),
            (104, "06d11ea2d8a362576c366116e23a193e62fa8cdb58dc5660a3033f780af83e4d"),
            (105, "baabd99912af774e0b5c4c4f46033cc00e68b4cf911409b481bd846ef93822d0"),
            (1000, "b3ebd3729073604285f9fe8b9ff8266ff49d5315c56aef81824e15b8942e4702"),
        ];
        for (n, d) in cases {
            assert_eq!(hex(&kd.eval(&pattern(n))), d, "keyed pattern({n})");
        }
        for n in [0, 1, 103, 104, 105, 239, 240, 241, 1000] {
            let q = pattern(n);
            let mut kq = key.to_vec();
            kq.extend_from_slice(&q);
            assert_eq!(kd.eval(&q), hash(&kq), "keyed {n}");
            assert_eq!(permutations(32 + n), (32 + n) / 136 + 1);
        }
        // after `wipe` the key bytes are zero
        let mut k2 = Keyed::new(&key);
        k2.wipe();
        assert_eq!(k2.eval(b""), hash(&[0u8; 32]));
    }
}
