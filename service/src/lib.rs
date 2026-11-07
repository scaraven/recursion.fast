//! recursion.fast oracle service: the library shared by the service binary (`rf-oracle`, trusted
//! runtime) and the measurement client (`rf-bench`, untrusted tooling). The wire format is
//! `PROTOCOL.md` (normative); `proto` holds its constants and a client.

pub mod keccak;
pub mod proto;
pub mod wots;

use keccak::{hash, Digest, Hasher};

/// Domain tag of the trace digest (`T`).
pub const TAG_T: u8 = 0x54;
/// Domain tag of the chain step (`C`).
pub const TAG_C: u8 = 0x43;
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

/// `chainEnd s n`: `chainStep d = Keccak-256(0x43 ‖ d)` applied `n` times to `s`
/// (`RecursionFast/Contract/Relation.lean`); one permutation per step.
pub fn chain_end(s: &Digest, n: u64) -> Digest {
    let mut d = *s;
    let mut m = [0u8; 33];
    m[0] = TAG_C;
    for _ in 0..n {
        m[1..].copy_from_slice(&d);
        d = hash(&m);
    }
    d
}

/// `leafStmt h n = Keccak-256(0x4C ‖ h ‖ enc64 n)` (41 bytes).
pub fn leaf_stmt(h: &Digest, n: u64) -> Digest {
    let mut m = [0u8; 41];
    m[0] = TAG_L;
    m[1..33].copy_from_slice(h);
    m[33..].copy_from_slice(&n.to_le_bytes());
    hash(&m)
}

/// One input line of `rf-oracle --leaves`, `<start: 64 lowercase hex> <n: decimal u64>`, or `None`
/// for anything else.
pub fn parse_leaf_line(line: &str) -> Option<(Digest, u64)> {
    let (s, n) = line.split_once(' ')?;
    if s.len() != 64 || n.is_empty() || !n.bytes().all(|c| c.is_ascii_digit()) {
        return None;
    }
    let mut start = [0u8; 32];
    for (i, b) in start.iter_mut().enumerate() {
        let pair = s.get(2 * i..2 * i + 2)?;
        if !pair.bytes().all(|c| matches!(c, b'0'..=b'9' | b'a'..=b'f')) {
            return None;
        }
        *b = u8::from_str_radix(pair, 16).ok()?;
    }
    Some((start, n.parse().ok()?))
}

/// `leafStmt (chainEnd s n) n` of every job `(s, n)`, on `threads` threads, in the order of `jobs`.
pub fn leaf_digests(jobs: &[(Digest, u64)], threads: usize) -> Vec<Digest> {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Mutex;
    let out = Mutex::new(vec![[0u8; 32]; jobs.len()]);
    let next = AtomicUsize::new(0);
    std::thread::scope(|sc| {
        for _ in 0..threads.max(1).min(jobs.len()) {
            sc.spawn(|| loop {
                let k = next.fetch_add(1, Ordering::Relaxed);
                let Some((s, n)) = jobs.get(k) else { break };
                let d = leaf_stmt(&chain_end(s, *n), *n);
                out.lock().unwrap()[k] = d;
            });
        }
    });
    out.into_inner().unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn unhex(s: &str) -> Digest {
        parse_leaf_line(&format!("{s} 0")).unwrap().0
    }

    #[test]
    fn leaves_against_python() {
        // harness/rfh/keccak.py: keccak256(b"L" + chain_end(s, n) + enc64(n)), cross-checked with pycryptodome
        let s: Digest = core::array::from_fn(|i| i as u8);
        let jobs = [(s, 0), (s, 1), ([0u8; 32], 5), (s, 1000)];
        let want = [
            "dfa45c463f4943449445a7f4526e4852e4518ee35cd96340d90615dbec93bb37",
            "f468cac9daec27c9c6217949e4cc53ef58c36b162f9c31e2d63ef62c3ddb68af",
            "3c91532e5167e840763204e3c04ab41805b47c14ecf668624afadd4991f58e62",
            "cda8818d771454b85864070ae536a1e8be6b4822b4009c3a511393154b3e7ad8",
        ];
        for threads in [1, 3, 8] {
            let got = leaf_digests(&jobs, threads);
            assert_eq!(got.len(), want.len());
            for (g, w) in got.iter().zip(want) {
                assert_eq!(*g, unhex(w));
            }
        }
        // one chain step from 00 01 … 1f is the vector Keccak-256("C" ‖ 00 01 … 1f)
        assert_eq!(chain_end(&s, 1), unhex("db8c51208716e57c91fc944cfa0df7336f9e784f9d3c0c04347f5fa833588e97"));
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
