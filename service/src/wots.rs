//! The contract-fixed signature (BRIEF §4.2, normative byte layouts): Winternitz one-time
//! signatures with `w = 4` (base-4 digits), `ℓ = 133` chains, under a Merkle tree of height 16,
//! all hashes BLAKE2s-256. `vk` is the Merkle root; the signer is stateful and signs at most
//! `2^16` messages, each with the next one-time key.
//!
//! * digits of a 32-byte message `m`: `d[4i + t] = (m[i] >> 2t) & 3` for byte `i < 32`, `t < 4`;
//!   checksum `C = Σ (3 − d_i)` over those 128; `d[128 + t] = (C >> 2t) & 3` for `t < 5`.
//! * chain step `F(j, i, s, x) = BLAKE2s-256(0x57 ‖ enc64 j ‖ byte i ‖ byte s ‖ x)` (43 bytes).
//! * secret chain start `sk_i` of key `j`: keyed BLAKE2s-256 under the signing seed of
//!   `0x53 ‖ enc64 j ‖ byte i` (V4-A4: tag `S`; the seed is drawn independently of the PRF key, and
//!   the tag keeps every derivation input distinct from the first byte of the other tagged inputs).
//! * signature of `m` with key `j`: `ots[i] = F` for `s = 0 … d_i − 1` applied to `sk_i`.
//! * leaf `j`: `BLAKE2s-256(0x4B ‖ enc64 j ‖ end_0 ‖ … ‖ end_132)`, `end_i` the chain's step 3.
//! * Merkle node `BLAKE2s-256(0x4D ‖ left ‖ right)`; `path[t]` is the sibling at level `t`, and
//!   the current value is the left child iff bit `t` of `j` is 0.

use crate::blake2s::{self, hash, hash_many, init, Digest, Keyed};
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};

/// Number of WOTS chains.
pub const LEN: usize = 133;
/// Height of the Merkle tree.
pub const HEIGHT: usize = 16;
/// Number of one-time keys.
pub const NKEYS: usize = 1 << HEIGHT;
/// Domain tags (V4-16): WOTS chain step, WOTS leaf, Merkle node.
pub const TAG_W: u8 = 0x57;
pub const TAG_K: u8 = 0x4B;
pub const TAG_M: u8 = 0x4D;
/// Size of a leaf preimage: `1 + 8 + 133 · 32`.
pub const LEAF_BYTES: usize = 1 + 8 + LEN * 32;

/// A signature: the one-time key index, 133 chain values, 16 Merkle siblings (leaf level first).
#[derive(Clone)]
pub struct Sig {
    pub idx: u32,
    pub ots: [Digest; LEN],
    pub path: [Digest; HEIGHT],
}

impl Sig {
    /// Wire encoding: `idx` (u32 LE) ‖ ots ‖ path (4 + 4256 + 512 bytes).
    pub const BYTES: usize = 4 + 32 * LEN + 32 * HEIGHT;

    pub fn encode(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.idx.to_le_bytes());
        for d in self.ots.iter().chain(self.path.iter()) {
            out.extend_from_slice(d);
        }
    }
}

/// The 133 base-4 digits of a message, checksum included.
pub fn digits(m: &Digest) -> [u8; LEN] {
    let mut d = [0u8; LEN];
    let mut c: u32 = 0;
    for i in 0..32 {
        for t in 0..4 {
            let x = (m[i] >> (2 * t)) & 3;
            d[4 * i + t] = x;
            c += 3 - x as u32;
        }
    }
    for t in 0..5 {
        d[128 + t] = ((c >> (2 * t)) & 3) as u8;
    }
    d
}

/// The 43-byte preimage of `F(j, i, s, x)`.
pub fn f_msg(j: u64, i: u8, s: u8, x: &Digest) -> [u8; 43] {
    let mut b = [0u8; 43];
    b[0] = TAG_W;
    b[1..9].copy_from_slice(&j.to_le_bytes());
    b[9] = i;
    b[10] = s;
    b[11..].copy_from_slice(x);
    b
}

/// Domain tag of a chain-start derivation (V4-A4, `S`).
pub const TAG_S: u8 = 0x53;

/// The 10-byte message `0x53 ‖ enc64 j ‖ byte i` whose keyed hash under the seed is `sk_i` of key `j`.
fn sk_msg(j: u64, i: u8) -> [u8; 10] {
    let mut b = [0u8; 10];
    b[0] = TAG_S;
    b[1..9].copy_from_slice(&j.to_le_bytes());
    b[9] = i;
    b
}

/// The 65-byte preimage of a Merkle node.
pub fn node_msg(l: &Digest, r: &Digest) -> [u8; 65] {
    let mut b = [0u8; 65];
    b[0] = TAG_M;
    b[1..33].copy_from_slice(l);
    b[33..].copy_from_slice(r);
    b
}

/// Apply `F(j, i, s, ·)` to `x[i]` for every chain with `from[i] ≤ s < to[i]`, vectorised across
/// chains.
fn advance(j: u64, x: &mut [Digest; LEN], from: &[u8; LEN], to: &[u8; LEN]) {
    for s in 0..3u8 {
        let idx: Vec<usize> = (0..LEN).filter(|&i| from[i] <= s && s < to[i]).collect();
        if idx.is_empty() {
            continue;
        }
        let msgs: Vec<[u8; 43]> = idx.iter().map(|&i| f_msg(j, i as u8, s, &x[i])).collect();
        let refs: Vec<&[u8]> = msgs.iter().map(|m| m.as_slice()).collect();
        let mut out = vec![[0u8; 32]; idx.len()];
        hash_many(&init(0), 0, &refs, &mut out);
        for (k, &i) in idx.iter().enumerate() {
            x[i] = out[k];
        }
    }
}

/// The leaf preimage `0x4B ‖ enc64 j ‖ end_0 ‖ … ‖ end_132`.
pub fn leaf_msg(j: u64, ends: &[Digest; LEN]) -> Vec<u8> {
    let mut b = Vec::with_capacity(LEAF_BYTES);
    b.push(TAG_K);
    b.extend_from_slice(&j.to_le_bytes());
    for e in ends {
        b.extend_from_slice(e);
    }
    b
}

/// Verify `sig` on `m` against `vk` (the specification `SigOk`; used by tests and clients).
pub fn verify(vk: &Digest, m: &Digest, sig: &Sig) -> bool {
    if sig.idx as usize >= NKEYS {
        return false;
    }
    let j = sig.idx as u64;
    let d = digits(m);
    let mut x = sig.ots;
    advance(j, &mut x, &d, &[3; LEN]);
    let mut cur = hash(&leaf_msg(j, &x));
    for t in 0..HEIGHT {
        cur = if (j >> t) & 1 == 0 { hash(&node_msg(&cur, &sig.path[t])) } else { hash(&node_msg(&sig.path[t], &cur)) };
    }
    cur == *vk
}

/// The stateful signer: the seed's keyed hash (for `sk`), the Merkle tree, the next index.
pub struct Signer {
    seed: Keyed,
    /// `levels[t]` holds the `2^(16 − t)` nodes of level `t`; `levels[0]` the leaves.
    levels: Vec<Vec<Digest>>,
    next: AtomicU32,
}

/// Error: all `2^16` one-time keys are used.
#[derive(Debug)]
pub struct Exhausted;

impl Signer {
    /// Key generation from a 32-byte seed with `threads` worker threads: all `2^16` leaves and the
    /// Merkle tree over them.
    pub fn keygen(seed: &[u8; 32], threads: usize) -> Signer {
        let seed = Keyed::new(seed);
        let mut leaves = vec![[0u8; 32]; NKEYS];
        const CHUNK: usize = 64;
        let counter = AtomicUsize::new(0);
        let chunks: Vec<&mut [Digest]> = leaves.chunks_mut(CHUNK).collect();
        let slots: Vec<std::sync::Mutex<Option<&mut [Digest]>>> =
            chunks.into_iter().map(|c| std::sync::Mutex::new(Some(c))).collect();
        std::thread::scope(|sc| {
            for _ in 0..threads.max(1) {
                sc.spawn(|| loop {
                    let c = counter.fetch_add(1, Ordering::Relaxed);
                    if c >= slots.len() {
                        break;
                    }
                    let out = slots[c].lock().unwrap().take().unwrap();
                    compute_leaves(&seed, (c * CHUNK) as u64, out);
                });
            }
        });
        drop(slots);
        let mut levels = vec![leaves];
        for _ in 0..HEIGHT {
            let prev = levels.last().unwrap();
            let msgs: Vec<[u8; 65]> = prev.chunks(2).map(|p| node_msg(&p[0], &p[1])).collect();
            let refs: Vec<&[u8]> = msgs.iter().map(|m| m.as_slice()).collect();
            let mut next = vec![[0u8; 32]; msgs.len()];
            let per = next.len().div_ceil(threads.max(1)).max(64);
            std::thread::scope(|sc| {
                for (r, o) in refs.chunks(per).zip(next.chunks_mut(per)) {
                    sc.spawn(move || hash_many(&init(0), 0, r, o));
                }
            });
            levels.push(next);
        }
        Signer { seed, levels, next: AtomicU32::new(0) }
    }

    /// The public key: the Merkle root.
    pub fn vk(&self) -> Digest {
        self.levels[HEIGHT][0]
    }

    /// Number of signatures made.
    pub fn used(&self) -> u32 {
        self.next.load(Ordering::SeqCst).min(NKEYS as u32)
    }

    /// The secret chain starts of key `j`.
    fn sks(&self, j: u64) -> [Digest; LEN] {
        let msgs: Vec<[u8; 10]> = (0..LEN).map(|i| sk_msg(j, i as u8)).collect();
        let refs: Vec<&[u8]> = msgs.iter().map(|m| m.as_slice()).collect();
        let mut out = [[0u8; 32]; LEN];
        self.seed.eval_many(&refs, &mut out);
        out
    }

    /// Sign `m` with the next one-time key; refuses once all `2^16` are used. The index is taken
    /// by one atomic read-modify-write before anything is computed, so no two signatures share a
    /// key and an index is never reused, whatever happens to the request afterwards (V4-A4).
    pub fn sign(&self, m: &Digest) -> Result<Sig, Exhausted> {
        let idx = self
            .next
            .try_update(Ordering::SeqCst, Ordering::SeqCst, |x| if (x as usize) < NKEYS { Some(x + 1) } else { None })
            .map_err(|_| Exhausted)?;
        let j = idx as u64;
        let d = digits(m);
        let mut x = self.sks(j);
        advance(j, &mut x, &[0; LEN], &d);
        let path: [Digest; HEIGHT] = core::array::from_fn(|t| self.levels[t][((j >> t) ^ 1) as usize]);
        Ok(Sig { idx, ots: x, path })
    }

    /// Overwrite the seed.
    pub fn wipe(&mut self) {
        self.seed.wipe();
    }
}

/// Leaves `j0 … j0 + out.len() − 1`. The chains of all these keys advance together, so that each
/// step is one batch of hashes, vectorised across chains.
fn compute_leaves(seed: &Keyed, j0: u64, out: &mut [Digest]) {
    let key = |c: usize| (j0 + (c / LEN) as u64, (c % LEN) as u8);
    let sk: Vec<[u8; 10]> = (0..out.len() * LEN).map(|c| sk_msg(key(c).0, key(c).1)).collect();
    let mut x = vec![[0u8; 32]; sk.len()];
    seed.eval_many(&sk.iter().map(|m| m.as_slice()).collect::<Vec<_>>(), &mut x);
    for s in 0..3 {
        let msgs: Vec<[u8; 43]> = x.iter().enumerate().map(|(c, x)| f_msg(key(c).0, key(c).1, s, x)).collect();
        hash_many(&init(0), 0, &msgs.iter().map(|m| m.as_slice()).collect::<Vec<_>>(), &mut x);
    }
    let leaves: Vec<Vec<u8>> = x.chunks(LEN).enumerate().map(|(k, e)| leaf_msg(j0 + k as u64, e.try_into().unwrap())).collect();
    hash_many(&init(0), 0, &leaves.iter().map(|m| m.as_slice()).collect::<Vec<_>>(), out);
    blake2s::wipe(&mut x);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn digits_checksum() {
        let d = digits(&[0u8; 32]);
        assert!(d[..128].iter().all(|&x| x == 0));
        // C = 384 = 0b01_10_00_00_00 → digits 0,0,0,2,1
        assert_eq!(&d[128..], &[0, 0, 0, 2, 1]);
        let d = digits(&[0xFFu8; 32]);
        assert!(d[..128].iter().all(|&x| x == 3));
        assert_eq!(&d[128..], &[0, 0, 0, 0, 0]);
        let d = digits(&[0b1110_0100; 32]);
        assert_eq!(&d[..4], &[0, 1, 2, 3]);
    }
}
