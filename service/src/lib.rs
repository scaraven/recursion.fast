//! recursion.fast v4 (SROM) oracle service: the library shared by the service binary
//! (`rf-oracle`, trusted runtime) and the measurement client (`rf-bench`, untrusted tooling).
//! The wire format is `PROTOCOL.md` (normative); `proto` holds its constants and a client.

pub mod blake2s;
pub mod proto;
pub mod wots;

use blake2s::{Digest, Hasher};

/// Domain tag of the trace digest (V4-16, `T`).
pub const TAG_T: u8 = 0x54;

/// `traceDigest tr = BLAKE2s-256(0x54 ‖ item_0 ‖ item_1 ‖ …)`, `item_i = enc64 |q_i| ‖ q_i ‖ a_i`
/// (BRIEF §4.2).
pub fn trace_digest(qs: &[&[u8]], answers: &[Digest]) -> Digest {
    let mut h = Hasher::new();
    h.update(&[TAG_T]);
    for (q, a) in qs.iter().zip(answers) {
        h.update(&(q.len() as u64).to_le_bytes()).update(q).update(a);
    }
    h.finalize()
}
