//! recursion.fast oracle service: the library shared by the service binary (`rf-oracle`, trusted
//! runtime) and the measurement client (`rf-bench`, untrusted tooling). The wire format is
//! `PROTOCOL.md` (normative); `proto` holds its constants and a client.

pub mod keccak;
pub mod proto;
pub mod wots;

use keccak::{hash, Digest, Hasher};

/// Domain tag of the trace digest (`T`).
pub const TAG_T: u8 = 0x54;
/// Domain tag of the leaf item (`H`).
pub const TAG_H: u8 = 0x48;
/// Domain tag of the leaf statement (`L`).
pub const TAG_L: u8 = 0x4C;
/// Domain tag of a node of a leaf's data tree (`D`).
pub const TAG_D: u8 = 0x44;

/// `traceDigest tr = Keccak-256(0x54 ‖ item_0 ‖ item_1 ‖ …)`, `item_i = enc64 |q_i| ‖ q_i ‖ a_i`
/// (`RecursionFast/Contract/Signature.lean`).
pub fn trace_digest(qs: &[&[u8]], answers: &[Digest]) -> Digest {
    let mut h = Hasher::new();
    h.update(&[TAG_T]);
    for (q, a) in qs.iter().zip(answers) {
        h.update(&(q.len() as u64).to_le_bytes()).update(q).update(a);
    }
    h.finalize()
}

/// `leafItem x = Keccak-256(0x48 ‖ x)` of one 32-byte block of a leaf's data (33 bytes, one
/// permutation; `RecursionFast/Contract/Relation.lean`).
pub fn leaf_item(x: &Digest) -> Digest {
    let mut m = [0u8; 33];
    m[0] = TAG_H;
    m[1..].copy_from_slice(x);
    hash(&m)
}

/// `dataNode l r = Keccak-256(0x44 ‖ l ‖ r)`, a node of a leaf's data tree (65 bytes, one permutation).
pub fn data_node(l: &Digest, r: &Digest) -> Digest {
    let mut m = [0u8; 65];
    m[0] = TAG_D;
    m[1..33].copy_from_slice(l);
    m[33..].copy_from_slice(r);
    hash(&m)
}

/// `dataLevel` until one digest is left, in place: adjacent digests paired by `data_node`, an odd
/// last one carried up unhashed; the zero digest for none.
fn reduce(ds: &mut Vec<Digest>) -> Digest {
    while ds.len() > 1 {
        let k = ds.len();
        for i in 0..k / 2 {
            ds[i] = data_node(&ds[2 * i], &ds[2 * i + 1]);
        }
        if k % 2 == 1 {
            ds[k / 2] = ds[k - 1];
        }
        ds.truncate(k.div_ceil(2));
    }
    ds.first().copied().unwrap_or([0u8; 32])
}

/// The `leafItem` of every block of `data` (its length a multiple of 32).
fn items(data: &[u8]) -> Vec<Digest> {
    data.chunks_exact(BLOCK).map(|x| leaf_item(x.try_into().unwrap())).collect()
}

/// `dataRoot xs` of the blocks `xs` (`data`, `32 · n` bytes; a trailing partial block is ignored),
/// on one thread, the reference: `dataLevel` applied to the block hashes until one digest is left
/// (`|xs|` levels reach it, and one digest is a fixed point); the zero digest for no block.
pub fn data_root(data: &[u8]) -> Digest {
    reduce(&mut items(data))
}

/// `leafStmt h n = Keccak-256(0x4C ‖ h ‖ enc64 n)` (41 bytes).
pub fn leaf_stmt(h: &Digest, n: u64) -> Digest {
    let mut m = [0u8; 41];
    m[0] = TAG_L;
    m[1..33].copy_from_slice(h);
    m[33..].copy_from_slice(&n.to_le_bytes());
    hash(&m)
}

/// Bytes per block of a leaf's data.
pub const BLOCK: usize = 32;
/// The contract's `leafCap`: the most blocks a leaf statement may cover (`2^20`).
pub const LEAF_CAP: usize = 1 << 20;
/// Blocks per unit of work of `data_roots`: a power of two, so that the level-by-level pairing never
/// crosses a chunk's boundary and the chunk roots are the tree's level `log2 CHUNK`.
const CHUNK: usize = 1 << 12;

/// `dataRoot` of every leaf's data in `leaves` (each `32 · n` bytes), in order, on `threads` threads.
/// Each leaf is cut into chunks of `CHUNK` consecutive blocks, which the threads take in order, so
/// one large tree is spread over every thread as well as many small ones. Since `CHUNK` is a power of
/// two and every chunk but a leaf's last is full, `dataLevel` never pairs digests of two chunks
/// below level `log2 CHUNK`, where the level is the list of the chunks' own roots (a last, partial
/// chunk's carry-up included): the upper levels are then reduced from the chunk roots.
pub fn data_roots(leaves: &[&[u8]], threads: usize) -> Vec<Digest> {
    data_roots_chunked(leaves, threads, CHUNK)
}

fn data_roots_chunked(leaves: &[&[u8]], threads: usize, chunk: usize) -> Vec<Digest> {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Mutex;
    assert!(chunk.is_power_of_two());
    // jobs: (leaf, first block) of every chunk, in leaf order
    let mut jobs = Vec::new();
    let mut counts = Vec::with_capacity(leaves.len());
    for (k, d) in leaves.iter().enumerate() {
        let n = d.len() / BLOCK;
        counts.push(n.div_ceil(chunk));
        jobs.extend((0..n).step_by(chunk).map(|lo| (k, lo)));
    }
    let roots: Vec<Mutex<Vec<Digest>>> = counts.iter().map(|&c| Mutex::new(vec![[0u8; 32]; c])).collect();
    let next = AtomicUsize::new(0);
    let workers = threads.max(1).min(jobs.len().max(1));
    std::thread::scope(|sc| {
        for _ in 0..workers {
            sc.spawn(|| loop {
                let g = next.fetch_add(1, Ordering::Relaxed);
                if g >= jobs.len() {
                    break;
                }
                let (k, lo) = jobs[g];
                let d = leaves[k];
                let n = d.len() / BLOCK;
                let r = data_root(&d[lo * BLOCK..(lo + chunk).min(n) * BLOCK]);
                roots[k].lock().unwrap()[lo / chunk] = r;
            });
        }
    });
    roots.into_iter().map(|r| reduce(&mut r.into_inner().unwrap())).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn unhex(s: &str) -> Digest {
        assert_eq!(s.len(), 64);
        core::array::from_fn(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
    }

    /// The data of `n` blocks of the known answers: the bytes `i mod 256`, `i < 32 n`.
    fn pattern(n: usize) -> Vec<u8> {
        (0..32 * n).map(|i| i as u8).collect()
    }

    /// A pseudo-random data file of `n` blocks (xorshift; test data only).
    fn noise(n: usize, mut x: u64) -> Vec<u8> {
        (0..32 * n)
            .map(|_| {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                x as u8
            })
            .collect()
    }

    #[test]
    fn data_roots_against_python() {
        // tests/vectors/data_root.json, computed by harness/rfh/digest.py (pure-Python Keccak-256,
        // harness/rfh/keccak.py): (n, dataRoot, leafStmt (dataRoot xs) n) of 0 … 7 and 9 blocks of
        // `pattern` (5, 6, 7 and 9 carry an odd digest up across more than one level)
        let kat: [(usize, &str, &str); 9] = [
            (0, "0000000000000000000000000000000000000000000000000000000000000000",
             "e5cccee57d4d4929ba748848efc9a66adafaade38cc37f8942d5bd5222a53b41"),
            (1, "09910f8c671ec97437b818fd5a1cb7f10ce4be81bf37778b0605b381eaabbe69",
             "949bd35e15ea565d678b0a51a067a7e8c431127c395d845d86ae2f9654978261"),
            (2, "a8886ea246bda7de84ecc698aa1cc03cf96654a74818887a43b3d042e5935020",
             "a7f68d0c19abd06304d01c284cb4f3d972eca094de930e607179037399b28e86"),
            (3, "e05b7300eecd28cd7e31a9d377deea6030b49cf9bfd08b0b47c132230812615b",
             "44f3a6c107823c2b42c86ae9f96a120d212a10a429bcd4ed64a2a0d513749050"),
            (4, "55c3ed43367f2313bd98059444f498d7ad3efb1aa34846e9543dde3a414085b1",
             "954cd3e680062826d0744b03ef59dbf53a9e7d55d694c46a5627e45d67a6e45f"),
            (5, "b2271079ecba02c30b299a5659f8b64cad48f697d2c565a754cfede0427a9420",
             "5bc0a00cd566ebca604dcafd2a36317266aa429c8bd6d24426b81af7b81ff428"),
            (6, "259aa413be633639776254e69323bc335fc8647907e6b499ddbff7b98d92d460",
             "96e3c271c4b595302742c871508c521bb02568993a17455c7355c22b6af7480f"),
            (7, "5387590c6b14b2b1cea975eeb354600cb4154a9c45a4ff17da5137526afc592b",
             "fcb369adca4122c5fc1174326ca70899296906b5172dcee56324e4b371c7d191"),
            (9, "b7c34972d370a3ea7942cc7cf246cdf40dbd585093f48144944bb6f2892a9f1c",
             "f6d213f1b8205192e8445bbbf22686a6d6ed97d214530d290572be8f6f9d400a"),
        ];
        for (n, root, stmt) in kat {
            let d = pattern(n);
            assert_eq!(data_root(&d), unhex(root), "dataRoot of {n} blocks");
            assert_eq!(leaf_stmt(&data_root(&d), n as u64), unhex(stmt), "leafStmt of {n} blocks");
            for threads in [1, 3] {
                assert_eq!(data_roots(&[&d], threads), vec![unhex(root)]);
            }
        }
        // one block: its leafItem; two: one node; three: the third digest carried up; four: a full tree
        let d = pattern(4);
        let i: Vec<Digest> = (0..4).map(|j| leaf_item(d[32 * j..32 * j + 32].try_into().unwrap())).collect();
        assert_eq!(data_root(&d[..32]), i[0]);
        assert_eq!(data_root(&d[..64]), data_node(&i[0], &i[1]));
        assert_eq!(data_root(&d[..96]), data_node(&data_node(&i[0], &i[1]), &i[2]));
        assert_eq!(data_root(&d), data_node(&data_node(&i[0], &i[1]), &data_node(&i[2], &i[3])));
        assert_eq!(data_root(&[]), [0u8; 32]);
    }

    #[test]
    fn data_roots_parallel_equal_the_reference() {
        // the chunked, threaded roots equal the one-thread reference at every chunk boundary, with
        // a small chunk (every size and carry-up case below 3 chunks) and the release chunk
        let sizes: Vec<usize> = (0..=40).collect();
        let files: Vec<Vec<u8>> = sizes.iter().map(|&n| noise(n, 7 + n as u64)).collect();
        let refs: Vec<&[u8]> = files.iter().map(|f| f.as_slice()).collect();
        let want: Vec<Digest> = refs.iter().map(|d| data_root(d)).collect();
        for chunk in [1, 2, 4, 8] {
            for threads in [1, 3, 8] {
                assert_eq!(data_roots_chunked(&refs, threads, chunk), want, "chunk {chunk}, threads {threads}");
            }
        }
        let big: Vec<Vec<u8>> = [CHUNK - 1, CHUNK, CHUNK + 1, 3 * CHUNK + 5].iter().map(|&n| noise(n, n as u64)).collect();
        let refs: Vec<&[u8]> = big.iter().map(|f| f.as_slice()).collect();
        let want: Vec<Digest> = refs.iter().map(|d| data_root(d)).collect();
        for threads in [1, 4, 16] {
            assert_eq!(data_roots(&refs, threads), want, "threads {threads}");
        }
        assert!(data_roots(&[], 4).is_empty());
    }
}
