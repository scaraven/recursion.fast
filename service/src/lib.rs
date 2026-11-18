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

/// `leafItem s j = Keccak-256(0x48 ‖ s ‖ enc64 j)` (41 bytes, one permutation;
/// `RecursionFast/Contract/Relation.lean`).
pub fn leaf_item(s: &Digest, j: u64) -> Digest {
    let mut m = [0u8; 41];
    m[0] = TAG_H;
    m[1..33].copy_from_slice(s);
    m[33..].copy_from_slice(&j.to_le_bytes());
    hash(&m)
}

/// The XOR of `leafItem s j` over `lo ≤ j < hi`.
fn leaf_xor(s: &Digest, lo: u64, hi: u64) -> Digest {
    let mut acc = [0u8; 32];
    let mut m = [0u8; 41];
    m[0] = TAG_H;
    m[1..33].copy_from_slice(s);
    for j in lo..hi {
        m[33..].copy_from_slice(&j.to_le_bytes());
        for (a, b) in acc.iter_mut().zip(hash(&m)) {
            *a ^= b;
        }
    }
    acc
}

/// `leafValue s n`: the XOR of `leafItem s j` over `j < n` (the zero digest for `n = 0`), on one thread.
pub fn leaf_value(s: &Digest, n: u64) -> Digest {
    leaf_xor(s, 0, n)
}

/// `leafStmt h n = Keccak-256(0x4C ‖ h ‖ enc64 n)` (41 bytes).
pub fn leaf_stmt(h: &Digest, n: u64) -> Digest {
    let mut m = [0u8; 41];
    m[0] = TAG_L;
    m[1..33].copy_from_slice(h);
    m[33..].copy_from_slice(&n.to_le_bytes());
    hash(&m)
}

/// One input line of `rf-oracle --leaves`, `<seed: 64 lowercase hex> <n: decimal u64>`, or `None`
/// for anything else.
pub fn parse_leaf_line(line: &str) -> Option<(Digest, u64)> {
    let (s, n) = line.split_once(' ')?;
    if s.len() != 64 || n.is_empty() || !n.bytes().all(|c| c.is_ascii_digit()) {
        return None;
    }
    let mut seed = [0u8; 32];
    for (i, b) in seed.iter_mut().enumerate() {
        let pair = s.get(2 * i..2 * i + 2)?;
        if !pair.bytes().all(|c| matches!(c, b'0'..=b'9' | b'a'..=b'f')) {
            return None;
        }
        *b = u8::from_str_radix(pair, 16).ok()?;
    }
    Some((seed, n.parse().ok()?))
}

/// The hashes per unit of work of `leaf_digests`.
const CHUNK: u64 = 1 << 14;

/// `leafStmt (leafValue s n) n` of every job `(s, n)`, in the order of `jobs`, on `threads` threads.
/// The hashes of all jobs are cut into chunks of `CHUNK` consecutive indices `j` of one job, which
/// the threads take in order, so one large leaf is spread over every thread as well as many small
/// ones; each chunk's XOR is folded into its job's accumulator (XOR is commutative, so the order
/// does not matter).
pub fn leaf_digests(jobs: &[(Digest, u64)], threads: usize) -> Vec<Digest> {
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::sync::Mutex;
    // ends[k]: the number of chunks of jobs 0 ..= k (u128: no sum of u64 counts overflows)
    let mut ends = Vec::with_capacity(jobs.len());
    let mut total: u128 = 0;
    for (_, n) in jobs {
        total += n.div_ceil(CHUNK) as u128;
        ends.push(total);
    }
    let acc: Vec<Mutex<Digest>> = jobs.iter().map(|_| Mutex::new([0u8; 32])).collect();
    let next = AtomicU64::new(0);
    let workers = (threads.max(1) as u128).min(total.max(1)) as usize;
    std::thread::scope(|sc| {
        for _ in 0..workers {
            sc.spawn(|| loop {
                let g = next.fetch_add(1, Ordering::Relaxed) as u128;
                if g >= total {
                    break;
                }
                let k = ends.partition_point(|&e| e <= g);
                let c = (g - if k == 0 { 0 } else { ends[k - 1] }) as u64;
                let (s, n) = &jobs[k];
                let lo = c * CHUNK;
                let x = leaf_xor(s, lo, (lo + CHUNK).min(*n));
                let mut a = acc[k].lock().unwrap();
                for (a, b) in a.iter_mut().zip(x) {
                    *a ^= b;
                }
            });
        }
    });
    jobs.iter().zip(acc).map(|((_, n), a)| leaf_stmt(&a.into_inner().unwrap(), *n)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn unhex(s: &str) -> Digest {
        parse_leaf_line(&format!("{s} 0")).unwrap().0
    }

    #[test]
    fn leaves_against_python() {
        // harness/rfh/digest.py (pure-Python Keccak-256, harness/rfh/keccak.py):
        // leaf_digest(s, n) = keccak256(b"L" + leaf_value(s, n) + enc64(n)),
        // leaf_value(s, n) = XOR of keccak256(b"H" + s + enc64(j)) over j < n
        let s: Digest = core::array::from_fn(|i| i as u8);
        let jobs = [(s, 0), (s, 1), (s, 2), ([0u8; 32], 5), (s, 1000), (s, 40000), ([0xffu8; 32], 16385)];
        let want = [
            "e5cccee57d4d4929ba748848efc9a66adafaade38cc37f8942d5bd5222a53b41",
            "cdc59157f61c755d1608bc845570a416c824b31517846a466e0c8f99ac63f2f6",
            "b87148cf718213fc578135218c8d778973d894d6110785ebc85cf206823aa924",
            "3cd9324ad4bafc8378ddb8293c265204f8a620a272977d78296ea5abde5b8109",
            "bf44e4a745955a2bc40189e7f698d8406e83e0ab5ad60b3339778ea693fdbf85",
            "ee5b2aa759075d4b14c7e7998474bf3711eeea075ddc6dbd00b3b1c5332c1eba",
            "e69d370af34a2eccb7f6776ec9c23c4547bcb58067a0da84cdb3f013ea1da679",
        ];
        for threads in [1, 3, 8] {
            let got = leaf_digests(&jobs, threads);
            assert_eq!(got.len(), want.len());
            for (g, w) in got.iter().zip(want) {
                assert_eq!(*g, unhex(w));
            }
            // one large leaf alone, spread over the threads
            assert_eq!(leaf_digests(&jobs[5..6], threads), vec![unhex(want[5])]);
        }
        assert!(leaf_digests(&[], 4).is_empty());
        // leafItem 00 01 … 1f 0 and leafValue of one item
        assert_eq!(leaf_item(&s, 0), unhex("da513675c495534390e0dfb57a4b2d94b8ec604af01e1cacb5bfa117e4178b11"));
        assert_eq!(leaf_value(&s, 1), leaf_item(&s, 0));
        assert_eq!(leaf_value(&s, 0), [0u8; 32]);
        assert_eq!(leaf_value(&s, 2), unhex("987811b1565b57a5360e5a6fbe442fab425363ce2a9326cf512e5aeec7eba08e"));
    }

    #[test]
    fn leaf_lines() {
        let h = "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f";
        assert_eq!(parse_leaf_line(&format!("{h} 18446744073709551615")).unwrap().1, u64::MAX);
        assert_eq!(parse_leaf_line(&format!("{h} 007")).unwrap().1, 7);
        for bad in [
            h.to_string(),
            format!("{h} "),
            format!("{h}  1"),
            format!("{h} 1 "),
            format!(" {h} 1"),
            format!("{h} +1"),
            format!("{h} 18446744073709551616"),
            format!("{} 1", h.to_uppercase()),
            format!("{} 1", &h[..62]),
            format!("{h}00 1"),
            format!("{h} 1\r"),
            "é".repeat(32) + " 1",
        ] {
            assert!(parse_leaf_line(&bad).is_none(), "{bad:?}");
        }
    }
}
