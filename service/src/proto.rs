//! Wire format constants (normative text: `PROTOCOL.md`) and a blocking client.
//!
//! Every message is a 16-byte header and a body. Request header: `op` (u8), three zero bytes,
//! `count` (u32 LE), `body_len` (u64 LE). Response header: `status` (u8), three zero bytes,
//! `count` (u32 LE), `body_len` (u64 LE). All integers little-endian.

use crate::blake2s::Digest;
use crate::wots::{Sig, HEIGHT, LEN};
use std::io::{self, Read, Write};
use std::os::unix::net::UnixStream;

/// `QUERY`: a batch of byte strings → their `PRF_k` answers.
pub const OP_QUERY: u8 = 1;
/// `SIGN`: a batch of byte strings → their answers and a signature on the trace digest.
pub const OP_SIGN: u8 = 2;
/// `VK`: the public key.
pub const OP_VK: u8 = 3;

/// Success.
pub const ST_OK: u8 = 0;
/// Malformed request (unknown op, non-zero reserved bytes, lengths that do not add up).
pub const ST_BAD: u8 = 1;
/// A cap is exceeded.
pub const ST_CAP: u8 = 2;
/// All `2^16` one-time signing keys are used.
pub const ST_EXHAUSTED: u8 = 3;

/// Largest query: 2^20 bytes (`queryCap`, V4-A3: `acc` rejects a trace with a longer query).
pub const MAX_QUERY_BYTES: u32 = 1 << 20;
/// Largest request body: 16 MiB.
pub const MAX_BODY: u64 = 1 << 24;
/// Most items in one `QUERY`.
pub const MAX_QUERY_COUNT: u32 = 1 << 18;
/// Most items in one `SIGN` (the verifier query bound `qV ≤ 2^16`).
pub const MAX_SIGN_COUNT: u32 = 1 << 16;
/// Most concurrent connections.
/// Most concurrent connections: 32. A connection holds at most a 16 MiB body, an 8 MiB response and
/// about 17 MiB of per-request temporaries (the sort of a mixed-size `QUERY`), so 32 of them fit the
/// service's 2 GiB cgroup with room for the keys (RF-m20; 64 did not).
pub const MAX_CONNS: usize = 32;

/// The 16-byte header.
pub fn header(code: u8, count: u32, body_len: u64) -> [u8; 16] {
    let mut h = [0u8; 16];
    h[0] = code;
    h[4..8].copy_from_slice(&count.to_le_bytes());
    h[8..16].copy_from_slice(&body_len.to_le_bytes());
    h
}

/// A blocking client on one connection (the measurement tool's; provers write their own).
pub struct Client {
    s: UnixStream,
    buf: Vec<u8>,
}

/// A failed call: the service's status and message, or an I/O error.
#[derive(Debug)]
pub enum CallError {
    Status(u8, String),
    Io(io::Error),
}

impl From<io::Error> for CallError {
    fn from(e: io::Error) -> Self {
        CallError::Io(e)
    }
}

impl Client {
    pub fn connect(path: &str) -> io::Result<Client> {
        Ok(Client { s: UnixStream::connect(path)?, buf: Vec::new() })
    }

    fn call(&mut self, op: u8, items: &[&[u8]]) -> Result<(u32, Vec<u8>), CallError> {
        self.buf.clear();
        let body: u64 = items.iter().map(|q| 4 + q.len() as u64).sum();
        self.buf.extend_from_slice(&header(op, items.len() as u32, body));
        for q in items {
            self.buf.extend_from_slice(&(q.len() as u32).to_le_bytes());
            self.buf.extend_from_slice(q);
        }
        self.s.write_all(&self.buf)?;
        let mut h = [0u8; 16];
        self.s.read_exact(&mut h)?;
        let count = u32::from_le_bytes(h[4..8].try_into().unwrap());
        let n = u64::from_le_bytes(h[8..16].try_into().unwrap()) as usize;
        let mut body = vec![0u8; n];
        self.s.read_exact(&mut body)?;
        if h[0] != ST_OK {
            return Err(CallError::Status(h[0], String::from_utf8_lossy(&body).into_owned()));
        }
        Ok((count, body))
    }

    /// `PRF_k` of each query.
    pub fn query(&mut self, qs: &[&[u8]]) -> Result<Vec<Digest>, CallError> {
        let (_, body) = self.call(OP_QUERY, qs)?;
        Ok(body.chunks_exact(32).map(|c| c.try_into().unwrap()).collect())
    }

    /// The answers and a signature on the trace digest.
    pub fn sign(&mut self, qs: &[&[u8]]) -> Result<(Vec<Digest>, Sig), CallError> {
        let (_, body) = self.call(OP_SIGN, qs)?;
        let n = 32 * qs.len();
        let answers = body[..n].chunks_exact(32).map(|c| c.try_into().unwrap()).collect();
        let s = &body[n..];
        let idx = u32::from_le_bytes(s[..4].try_into().unwrap());
        let d = |k: usize| -> Digest { s[4 + 32 * k..4 + 32 * k + 32].try_into().unwrap() };
        let ots: [Digest; LEN] = core::array::from_fn(d);
        let path: [Digest; HEIGHT] = core::array::from_fn(|t| d(LEN + t));
        Ok((answers, Sig { idx, ots, path }))
    }

    /// The public key.
    pub fn vk(&mut self) -> Result<Digest, CallError> {
        let (_, body) = self.call(OP_VK, &[])?;
        Ok(body[..32].try_into().unwrap())
    }

    /// Send raw bytes and read one response (tests of malformed requests).
    pub fn raw(&mut self, bytes: &[u8]) -> io::Result<(u8, Vec<u8>)> {
        self.s.write_all(bytes)?;
        let mut h = [0u8; 16];
        self.s.read_exact(&mut h)?;
        let n = u64::from_le_bytes(h[8..16].try_into().unwrap()) as usize;
        let mut body = vec![0u8; n];
        self.s.read_exact(&mut body)?;
        Ok((h[0], body))
    }
}
