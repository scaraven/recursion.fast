//! `rf-oracle`: the oracle and signing service of one timed run (TRUSTED RUNTIME; BRIEF §4.3,
//! wire format `PROTOCOL.md`).
//!
//!   rf-oracle --socket PATH [--log FILE] [--threads N]
//!
//! At start it draws a fresh 32-byte PRF key `k` and a fresh 32-byte signing seed from
//! `getrandom`, generates the `2^16` one-time keys and the Merkle tree (`vk` its root), binds the
//! Unix socket PATH, and prints `vk <hex>`, `keygen_ms <ms>` and `ready` on stdout. It serves one
//! thread per connection: `QUERY` (a batch of byte strings → `PRF_k` of each, keyed BLAKE2s-256),
//! `SIGN` (a batch of byte strings → their answers, computed here, and a signature on the trace
//! digest with the next one-time key; refused after `2^16`), `VK`. With `--log FILE` (liveness
//! mode) every query it evaluates and its answer is appended to FILE as `enc64 |q| ‖ q ‖ a`.
//! It exits when its stdin reaches end of file (the runner closes it): it then takes the key lock,
//! overwrites the keys, flushes the log, prints `stats …`, removes the socket and exits 0. The keys
//! are never written anywhere; the process is made non-dumpable, so a process of the same uid
//! cannot ptrace it or read its memory through /proc.
//!
//! `--insecure-test-keys PRFKEY_HEX SEED_HEX` replaces the random keys by given ones and prints
//! `INSECURE` on stdout; it exists for the known-answer tests only (`tests/service/`), and the
//! runner never passes it and refuses a service that prints `INSECURE`.

use rf_oracle::blake2s::{self, Digest, Keyed};
use rf_oracle::proto::*;
use rf_oracle::wots::Signer;
use rf_oracle::{push_item, trace_digest};
use std::fs::File;
use std::io::{self, BufReader, BufWriter, Read, Write};
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::{UnixListener, UnixStream};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Mutex, RwLock};
use std::time::Instant;

extern "C" {
    fn getrandom(buf: *mut u8, buflen: usize, flags: u32) -> isize;
    fn prctl(option: i32, ...) -> i32;
}

/// 32 bytes from the kernel's CSPRNG (`getrandom`, else `/dev/urandom`).
fn random32() -> [u8; 32] {
    let mut b = [0u8; 32];
    let mut got = 0usize;
    while got < 32 {
        let r = unsafe { getrandom(b.as_mut_ptr().add(got), 32 - got, 0) };
        if r <= 0 {
            File::open("/dev/urandom").and_then(|mut f| f.read_exact(&mut b)).expect("rf-oracle: no randomness");
            return b;
        }
        got += r as usize;
    }
    b
}

/// The secret state: the PRF and the signer. `None` once wiped at shutdown.
struct Keys {
    prf: Keyed,
    signer: Signer,
}

struct State {
    keys: RwLock<Option<Keys>>,
    log: Option<Mutex<BufWriter<File>>>,
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

/// `PRF_k` of every query, eight at a time; queries are grouped by block count first when their
/// sizes differ, so that the eight lanes of one compression run the same number of blocks.
fn answers(prf: &Keyed, qs: &[&[u8]]) -> Vec<Digest> {
    let mut out = vec![[0u8; 32]; qs.len()];
    let nb = |q: &[u8]| q.len().div_ceil(64);
    if qs.len() < 16 || qs.iter().all(|q| nb(q) == nb(qs[0])) {
        prf.eval_many(qs, &mut out);
        return out;
    }
    let mut order: Vec<u32> = (0..qs.len() as u32).collect();
    order.sort_unstable_by_key(|&i| nb(qs[i as usize]));
    let sorted: Vec<&[u8]> = order.iter().map(|&i| qs[i as usize]).collect();
    let mut tmp = vec![[0u8; 32]; qs.len()];
    prf.eval_many(&sorted, &mut tmp);
    for (k, &i) in order.iter().enumerate() {
        out[i as usize] = tmp[k];
    }
    out
}

/// An error response; the connection is closed after it.
fn refuse(w: &mut UnixStream, status: u8, msg: &str) -> io::Result<()> {
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
        match op {
            OP_VK => {
                resp.extend_from_slice(&header(ST_OK, 0, 32));
                resp.extend_from_slice(&keys.signer.vk());
            }
            _ => {
                let ans = answers(&keys.prf, &qs);
                let sig = if op == OP_SIGN {
                    match keys.signer.sign(&trace_digest(&qs, &ans)) {
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
                if let Some(log) = &st.log {
                    let mut buf = Vec::with_capacity(body.len() + 36 * qs.len());
                    for (q, a) in qs.iter().zip(&ans) {
                        push_item(&mut buf, q, a);
                    }
                    let mut l = log.lock().unwrap();
                    l.write_all(&buf)?;
                    l.flush()?; // the liveness check reads the log before the service exits
                }
                let n = 32 * ans.len() + if sig.is_some() { rf_oracle::wots::Sig::BYTES } else { 0 };
                resp.extend_from_slice(&header(ST_OK, count, n as u64));
                resp.extend_from_slice(ans.as_flattened());
                if let Some(s) = &sig {
                    s.encode(&mut resp);
                    st.signatures.fetch_add(1, Ordering::Relaxed);
                }
                st.queries.fetch_add(count as u64, Ordering::Relaxed);
                st.query_bytes.fetch_add(blen - 4 * count as u64, Ordering::Relaxed);
            }
        }
        st.requests.fetch_add(1, Ordering::Relaxed);
        w.write_all(&resp)?;
        if body.capacity() > 1 << 20 {
            body = Vec::new();
        }
        if resp.capacity() > 1 << 20 {
            resp = Vec::new();
        }
    }
}

/// Wipe the keys (after in-flight requests finish), flush the log, report, remove the socket, exit.
fn shutdown(st: &State) -> ! {
    let mut g = st.keys.write().unwrap_or_else(|e| e.into_inner());
    if let Some(mut k) = g.take() {
        k.prf.wipe();
        k.signer.wipe();
    }
    let mut code = 0;
    if let Some(log) = &st.log {
        let mut l = log.lock().unwrap_or_else(|e| e.into_inner());
        if l.flush().and_then(|_| l.get_ref().sync_all()).is_err() {
            code = 1;
        }
    }
    let _ = std::fs::remove_file(&st.socket);
    println!(
        "stats requests={} queries={} query_bytes={} signatures={}",
        st.requests.load(Ordering::SeqCst),
        st.queries.load(Ordering::SeqCst),
        st.query_bytes.load(Ordering::SeqCst),
        st.signatures.load(Ordering::SeqCst)
    );
    let _ = io::stdout().flush();
    std::process::exit(code)
}

fn usage() -> ! {
    eprintln!("usage: rf-oracle --socket PATH [--log FILE] [--threads N] [--insecure-test-keys PRFKEY_HEX SEED_HEX]");
    std::process::exit(2)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (mut socket, mut log, mut threads, mut test) = (None, None, None, None);
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--socket" if i + 1 < args.len() => socket = Some(args[i + 1].clone()),
            "--log" if i + 1 < args.len() => log = Some(args[i + 1].clone()),
            "--threads" if i + 1 < args.len() => threads = args[i + 1].parse::<usize>().ok(),
            "--insecure-test-keys" if i + 2 < args.len() => {
                test = Some((unhex32(&args[i + 1]).unwrap_or_else(|| usage()), unhex32(&args[i + 2]).unwrap_or_else(|| usage())));
                i += 1;
            }
            _ => usage(),
        }
        i += 2;
    }
    let Some(socket) = socket else { usage() };
    // PR_SET_DUMPABLE = 4: no ptrace attach and no /proc/PID/mem for processes of the same uid.
    if unsafe { prctl(4, 0u64, 0u64, 0u64, 0u64) } != 0 {
        eprintln!("rf-oracle: prctl(PR_SET_DUMPABLE, 0) failed");
        std::process::exit(1);
    }
    let threads = threads.unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1));
    let (mut prf_key, mut seed) = match test {
        Some((k, s)) => {
            println!("INSECURE fixed test keys");
            (k, s)
        }
        None => (random32(), random32()),
    };
    let t0 = Instant::now();
    let signer = Signer::keygen(&seed, threads);
    let keygen_ms = t0.elapsed().as_secs_f64() * 1e3;
    let prf = Keyed::new(&prf_key);
    blake2s::wipe(&mut prf_key);
    blake2s::wipe(&mut seed);
    let log = log.map(|p| {
        let f = File::options().write(true).create_new(true).open(&p).unwrap_or_else(|e| {
            eprintln!("rf-oracle: cannot create the log {p}: {e}");
            std::process::exit(1)
        });
        Mutex::new(BufWriter::with_capacity(1 << 20, f))
    });
    let listener = UnixListener::bind(&socket).unwrap_or_else(|e| {
        eprintln!("rf-oracle: cannot bind {socket}: {e}");
        std::process::exit(1)
    });
    let _ = std::fs::set_permissions(&socket, std::fs::Permissions::from_mode(0o666));
    let vk = signer.vk();
    let st: &'static State = Box::leak(Box::new(State {
        keys: RwLock::new(Some(Keys { prf, signer })),
        log,
        conns: AtomicUsize::new(0),
        requests: AtomicU64::new(0),
        queries: AtomicU64::new(0),
        query_bytes: AtomicU64::new(0),
        signatures: AtomicU64::new(0),
        socket: socket.clone(),
    }));
    println!("vk {}", hex(&vk));
    println!("keygen_ms {keygen_ms:.1}");
    println!("simd {}", if blake2s::has_avx2() { "avx2" } else { "scalar" });
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
            let _ = refuse(&mut c, ST_CAP, "more than 64 connections");
            continue;
        }
        std::thread::spawn(move || {
            let _ = serve(conn, st);
            st.conns.fetch_sub(1, Ordering::SeqCst);
        });
    }
}
