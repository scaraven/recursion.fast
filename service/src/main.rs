//! `rf-oracle`: the oracle and signing service of one timed run (TRUSTED RUNTIME; `service/PROTOCOL.md`,
//! wire format `PROTOCOL.md`).
//!
//!   rf-oracle --socket PATH [--threads N]
//!   rf-oracle --leaves [--threads N]
//!
//! At start it draws a fresh 32-byte PRF key `k` and a fresh 32-byte signing seed from
//! `getrandom`, generates the `2^16` one-time keys and the Merkle tree (`vk` its root), binds the
//! Unix socket PATH, and prints `vk <hex>`, `keygen_ms <ms>` and `ready` on stdout. It serves one
//! thread per connection: `QUERY` (a batch of byte strings → `PRF_k(q) = Keccak-256(k ‖ q)` of each),
//! `SIGN` (a batch of byte strings → their answers, computed here, and a signature on the trace
//! digest with the next one-time key; refused after `2^16`), `VK`. It exits when its stdin reaches
//! end of file (the runner closes it): it then takes the key lock, overwrites the keys, prints
//! `stats …`, removes the socket and exits 0. The keys are never written anywhere; the process is
//! made non-dumpable, so a process of the same uid cannot ptrace it or read its memory through
//! /proc.
//!
//! `--insecure-test-keys PRFKEY_HEX SEED_HEX` replaces the random keys by given ones and prints
//! `INSECURE` on stdout. It exists for the known-answer tests only (`tests/service/`) and is
//! compiled only with the non-default cargo feature `insecure-test-keys`: the release
//! binary the runner uses, whose hash every result records, rejects the option. The runner also
//! refuses a service that prints `INSECURE`.
//!
//! `--leaves` is the runner's chain hasher and holds no secret: it draws no key and opens no socket.
//! It reads lines `<start: 64 lowercase hex> <n: decimal>` from stdin until end of file and writes,
//! for each, one line `leafStmt (chainEnd start n) n` (64 lowercase hex) to stdout, in input order,
//! computed on N threads; a malformed line is reported on stderr and the exit code is 2.

use rf_oracle::keccak::{self, Keyed};
use rf_oracle::proto::*;
use rf_oracle::wots::Signer;
use rf_oracle::{leaf_digests, parse_leaf_line, trace_digest};
use std::fs::File;
use std::io::{self, BufReader, Read, Write};
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::{UnixListener, UnixStream};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::RwLock;
use std::time::Instant;

extern "C" {
    fn getrandom(buf: *mut u8, buflen: usize, flags: u32) -> isize;
    fn prctl(option: i32, ...) -> i32;
}

/// Fill `b` with 32 bytes from the kernel's CSPRNG (`getrandom`, else `/dev/urandom`), in place, so
/// that no copy of a key is left on the stack.
fn random32(b: &mut [u8; 32]) {
    let mut got = 0usize;
    while got < 32 {
        let r = unsafe { getrandom(b.as_mut_ptr().add(got), 32 - got, 0) };
        if r <= 0 {
            File::open("/dev/urandom").and_then(|mut f| f.read_exact(b)).expect("rf-oracle: no randomness");
            return;
        }
        got += r as usize;
    }
}

/// The secret state: the PRF and the signer. `None` once wiped at shutdown.
struct Keys {
    prf: Keyed,
    signer: Signer,
}

struct State {
    keys: RwLock<Option<Keys>>,
    conns: AtomicUsize,
    requests: AtomicU64,
    queries: AtomicU64,
    query_bytes: AtomicU64,
    signatures: AtomicU64,
    socket: String,
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

#[cfg(feature = "insecure-test-keys")]
fn unhex32(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = u8::from_str_radix(s.get(2 * i..2 * i + 2)?, 16).ok()?;
    }
    Some(out)
}

/// An error response; the connection is closed after it.
/// Refusals so far; the first `REFUSALS_LOGGED` are written to stderr (the runner puts them in
/// the result, so a prover's failure on a cap is visible).
static REFUSALS: AtomicU64 = AtomicU64::new(0);
const REFUSALS_LOGGED: u64 = 32;

fn refuse(w: &mut UnixStream, status: u8, msg: &str) -> io::Result<()> {
    if REFUSALS.fetch_add(1, Ordering::Relaxed) < REFUSALS_LOGGED {
        eprintln!("rf-oracle: refused (status {status}): {msg}");
    }
    let mut r = header(status, 0, msg.len() as u64).to_vec();
    r.extend_from_slice(msg.as_bytes());
    w.write_all(&r)
}

/// Serve one connection until the client closes it or sends a request that is refused.
fn serve(mut w: UnixStream, st: &State) -> io::Result<()> {
    let mut rd = BufReader::with_capacity(1 << 16, w.try_clone()?);
    let mut body: Vec<u8> = Vec::new();
    let mut resp: Vec<u8> = Vec::new();
    loop {
        let mut h = [0u8; 16];
        match rd.read_exact(&mut h) {
            Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => return Ok(()),
            r => r?,
        }
        let op = h[0];
        let count = u32::from_le_bytes(h[4..8].try_into().unwrap());
        let blen = u64::from_le_bytes(h[8..16].try_into().unwrap());
        if h[1..4] != [0, 0, 0] {
            return refuse(&mut w, ST_BAD, "reserved header bytes must be zero");
        }
        match op {
            OP_QUERY if count > MAX_QUERY_COUNT => return refuse(&mut w, ST_CAP, "QUERY count above 2^18"),
            OP_SIGN if count > MAX_SIGN_COUNT => return refuse(&mut w, ST_CAP, "SIGN count above 2^16"),
            OP_QUERY | OP_SIGN if blen > MAX_BODY => return refuse(&mut w, ST_CAP, "body above 2^24 bytes"),
            OP_QUERY | OP_SIGN if blen < 4 * count as u64 => return refuse(&mut w, ST_BAD, "body shorter than its length words"),
            OP_VK if count != 0 || blen != 0 => return refuse(&mut w, ST_BAD, "VK takes no body"),
            OP_QUERY | OP_SIGN | OP_VK => {}
            _ => return refuse(&mut w, ST_BAD, "unknown op"),
        }
        body.clear();
        body.resize(blen as usize, 0);
        rd.read_exact(&mut body)?;
        let mut qs: Vec<&[u8]> = Vec::with_capacity(count as usize);
        let mut off = 0usize;
        for _ in 0..count {
            let Some(l) = body.get(off..off + 4) else { break };
            let n = u32::from_le_bytes(l.try_into().unwrap());
            if n > MAX_QUERY_BYTES {
                return refuse(&mut w, ST_CAP, "a query above 2^20 bytes");
            }
            let n = n as usize;
            let Some(q) = body.get(off + 4..off + 4 + n) else { break };
            qs.push(q);
            off += 4 + n;
        }
        if qs.len() != count as usize || off != body.len() {
            return refuse(&mut w, ST_BAD, "item lengths do not add up to the body length");
        }
        let guard = st.keys.read().unwrap();
        let Some(keys) = guard.as_ref() else { return Ok(()) };
        resp.clear();
        if op == OP_VK {
            resp.extend_from_slice(&header(ST_OK, 0, 32));
            resp.extend_from_slice(&keys.signer.vk());
        } else {
            // the answers are computed in place, after room for the header
            resp.resize(16 + 32 * qs.len(), 0);
            let (ans, _) = resp[16..].as_chunks_mut::<32>();
            keys.prf.eval_many(&qs, ans);
            let sig = if op == OP_SIGN {
                match keys.signer.sign(&trace_digest(&qs, ans)) {
                    Ok(s) => Some(s),
                    Err(_) => {
                        drop(guard);
                        return refuse(&mut w, ST_EXHAUSTED, "all 2^16 one-time keys are used");
                    }
                }
            } else {
                None
            };
            drop(guard);
            let n = 32 * qs.len() + if sig.is_some() { rf_oracle::wots::Sig::BYTES } else { 0 };
            resp[..16].copy_from_slice(&header(ST_OK, count, n as u64));
            if let Some(s) = &sig {
                s.encode(&mut resp);
                st.signatures.fetch_add(1, Ordering::Relaxed);
            }
            st.queries.fetch_add(count as u64, Ordering::Relaxed);
            st.query_bytes.fetch_add(blen - 4 * count as u64, Ordering::Relaxed);
        }
        st.requests.fetch_add(1, Ordering::Relaxed);
        w.write_all(&resp)?;
    }
}

/// Wipe the keys (after in-flight requests finish), report, remove the socket, exit.
fn shutdown(st: &State) -> ! {
    let mut g = st.keys.write().unwrap_or_else(|e| e.into_inner());
    if let Some(mut k) = g.take() {
        k.prf.wipe();
        k.signer.wipe();
    }
    let _ = std::fs::remove_file(&st.socket);
    println!(
        "stats requests={} queries={} query_bytes={} signatures={} refusals={}",
        st.requests.load(Ordering::SeqCst),
        st.queries.load(Ordering::SeqCst),
        st.query_bytes.load(Ordering::SeqCst),
        st.signatures.load(Ordering::SeqCst),
        REFUSALS.load(Ordering::SeqCst)
    );
    let _ = io::stdout().flush();
    std::process::exit(0)
}

fn usage() -> ! {
    eprintln!("usage: rf-oracle --socket PATH [--threads N] [--insecure-test-keys PRFKEY_HEX SEED_HEX (test builds only)]");
    eprintln!("       rf-oracle --leaves [--threads N]");
    std::process::exit(2)
}

/// `rf-oracle --leaves`: read every line of stdin, then write the leaf digests in input order.
fn leaves_mode(threads: usize) -> ! {
    let mut input = String::new();
    if let Err(e) = io::stdin().read_to_string(&mut input) {
        eprintln!("rf-oracle --leaves: cannot read stdin: {e}");
        std::process::exit(2)
    }
    let mut jobs = Vec::new();
    for (k, line) in input.split_terminator('\n').enumerate() {
        match parse_leaf_line(line) {
            Some(job) => jobs.push(job),
            None => {
                eprintln!("rf-oracle --leaves: line {}: expected `<64 lowercase hex> <decimal>`, got {line:?}", k + 1);
                std::process::exit(2)
            }
        }
    }
    let mut out = String::with_capacity(65 * jobs.len());
    for d in leaf_digests(&jobs, threads) {
        out.push_str(&hex(&d));
        out.push('\n');
    }
    let mut so = io::stdout().lock();
    if so.write_all(out.as_bytes()).and_then(|_| so.flush()).is_err() {
        std::process::exit(1)
    }
    std::process::exit(0)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (mut socket, mut threads, mut leaves) = (None, None, false);
    #[allow(unused_mut)]
    let mut test: Option<([u8; 32], [u8; 32])> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--socket" if i + 1 < args.len() => socket = Some(args[i + 1].clone()),
            "--threads" if i + 1 < args.len() => threads = args[i + 1].parse::<usize>().ok(),
            "--leaves" => {
                leaves = true;
                i += 1;
                continue;
            }
            #[cfg(feature = "insecure-test-keys")]
            "--insecure-test-keys" if i + 2 < args.len() => {
                test = Some((unhex32(&args[i + 1]).unwrap_or_else(|| usage()), unhex32(&args[i + 2]).unwrap_or_else(|| usage())));
                i += 1;
            }
            _ => usage(),
        }
        i += 2;
    }
    let threads = threads.unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1));
    if leaves {
        if socket.is_some() || test.is_some() {
            usage()
        }
        leaves_mode(threads)
    }
    let Some(socket) = socket else { usage() };
    // PR_SET_DUMPABLE = 4: no ptrace attach and no /proc/PID/mem for processes of the same uid.
    if unsafe { prctl(4, 0u64, 0u64, 0u64, 0u64) } != 0 {
        eprintln!("rf-oracle: prctl(PR_SET_DUMPABLE, 0) failed");
        std::process::exit(1);
    }
    let (mut prf_key, mut seed) = match test {
        Some((k, s)) => {
            println!("INSECURE fixed test keys");
            (k, s)
        }
        None => {
            let (mut k, mut s) = ([0u8; 32], [0u8; 32]);
            random32(&mut k);
            random32(&mut s);
            (k, s)
        }
    };
    let t0 = Instant::now();
    let signer = Signer::keygen(&seed, threads);
    let keygen_ms = t0.elapsed().as_secs_f64() * 1e3;
    let prf = Keyed::new(&prf_key);
    keccak::wipe(&mut prf_key);
    keccak::wipe(&mut seed);
    let listener = UnixListener::bind(&socket).unwrap_or_else(|e| {
        eprintln!("rf-oracle: cannot bind {socket}: {e}");
        std::process::exit(1)
    });
    let _ = std::fs::set_permissions(&socket, std::fs::Permissions::from_mode(0o666));
    let vk = signer.vk();
    let st: &'static State = Box::leak(Box::new(State {
        keys: RwLock::new(Some(Keys { prf, signer })),
        conns: AtomicUsize::new(0),
        requests: AtomicU64::new(0),
        queries: AtomicU64::new(0),
        query_bytes: AtomicU64::new(0),
        signatures: AtomicU64::new(0),
        socket: socket.clone(),
    }));
    println!("vk {}", hex(&vk));
    println!("keygen_ms {keygen_ms:.1}");
    println!("simd scalar");
    println!("ready");
    let _ = io::stdout().flush();
    std::thread::spawn(move || {
        let mut buf = [0u8; 256];
        let mut stdin = io::stdin().lock();
        while matches!(stdin.read(&mut buf), Ok(n) if n > 0) {}
        shutdown(st)
    });
    for conn in listener.incoming() {
        let Ok(conn) = conn else { continue };
        if st.conns.fetch_add(1, Ordering::SeqCst) >= MAX_CONNS {
            st.conns.fetch_sub(1, Ordering::SeqCst);
            let mut c = conn;
            let _ = refuse(&mut c, ST_CAP, "more than 32 connections");
            continue;
        }
        std::thread::spawn(move || {
            // the slot is released when the thread ends, by return or by panic
            struct Slot(&'static AtomicUsize);
            impl Drop for Slot {
                fn drop(&mut self) {
                    self.0.fetch_sub(1, Ordering::SeqCst);
                }
            }
            let _slot = Slot(&st.conns);
            let _ = serve(conn, st);
        });
    }
}
