//! `rf-oracle`: the oracle and signing service of one evaluation (TRUSTED RUNTIME; the wire format
//! and the control lines are `service/PROTOCOL.md`, normative).
//!
//!   rf-oracle --socket PATH [--threads N] [--io-timeout SECS]
//!   rf-oracle --data-roots [--threads N] FILE…
//!
//! `--threads N` (default: the CPUs this process may use) must be a decimal count from 1 to 1024,
//! `--io-timeout SECS` (default 60) a decimal count of seconds from 1 to 86400; any other value is a
//! usage error (exit 2).
//!
//! At start it fixes glibc's mmap threshold and limits glibc to one malloc arena (so that no
//! request's allocation cost depends on an earlier connection's frees or threads), draws a fresh 32-byte PRF key `k` and a fresh 32-byte signing seed
//! from `getrandom`, generates the `2^16` one-time keys and the Merkle tree (`vk` its root), binds
//! the Unix socket PATH (mode 0600), and prints `vk <hex>`, `keygen_ms <ms>`, `simd scalar` and
//! `ready` on stdout. It serves each connection on one of `MAX_CONNS` = 32 worker threads started
//! with it (none is started or ends per connection, so no thread-stack cache or arena count carries
//! one request's threads into a later one's), from a listen backlog of 64: `QUERY` (a batch of byte strings →
//! `PRF_k(q) = Keccak-256(k ‖ q)` of each), `SIGN` (a batch of byte strings → their answers,
//! computed here, and a signature on the trace digest with the next one-time key; refused after
//! `2^16`), `VK`. It records the trace digest it signed at each one-time key index. A connection
//! that stays `SECS` in one read or one write (idle, a stalled body, a response not taken) is
//! closed; one that sends ancillary data (file descriptors, credentials) is refused and closed, the
//! descriptors it sent closed unused.
//!
//! Its stdin is the runner's control pipe. The line `replay` switches it to replay mode (once every
//! in-flight request is done): it resets the replay index to 0 and prints `key <hex k>` and `replay
//! ready`. In replay mode `SIGN` takes the next replay index `j` and re-issues the service run's
//! signature at `j` if the trace digest is the one signed there, else refuses with `MISMATCH`; it
//! never signs a new digest. `replay` may come again: each resets the index to 0. The line `drop`
//! closes every connection still waiting in the listen backlog (never accepted, so in no count),
//! shuts every open connection down (which also frees anything queued on it), waits up to 5 s for
//! their workers to finish them and prints `dropped live=N`; the line `stats` prints the `stats …` line. At
//! end of file (the runner closes the pipe) it takes the key lock, overwrites the keys, prints
//! `stats …`, removes the socket and exits 0. The signing seed is never written anywhere, and `k`
//! only to stdout after `replay`; the process is made non-dumpable, so a process of the same uid
//! cannot ptrace it or read its memory through /proc.
//!
//! `--insecure-test-keys PRFKEY_HEX SEED_HEX` replaces the random keys by given ones and prints
//! `INSECURE` on stdout. It exists for the known-answer tests only (`tests/service/`) and is
//! compiled only with the non-default cargo feature `insecure-test-keys`: the release
//! binary the runner uses, whose hash every result records, rejects the option. The runner also
//! refuses a service that prints `INSECURE`.
//!
//! `--data-roots` is the runner's leaf hasher and holds no secret: it draws no key and opens no
//! socket. Each FILE is one leaf's data, `n` blocks of 32 bytes; it writes, for each, one line
//! `leafStmt (dataRoot xs) n` (64 lowercase hex) to stdout, in argument order, each tree spread over
//! N threads (an empty file: `leafStmt zero 0`). A file whose size is not a multiple of 32, whose `n`
//! is above `leafCap = 2^20`, or that cannot be read is reported on stderr, nothing is written to
//! stdout, and the exit code is 2.

use rf_oracle::keccak::{self, Keyed};
use rf_oracle::proto::*;
use rf_oracle::wots::{NotSigned, Signer, NKEYS};
use rf_oracle::{data_roots, leaf_stmt, trace_digest, BLOCK, LEAF_CAP};
use std::collections::HashMap;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Read, Write};
use std::net::Shutdown;
use std::os::fd::AsRawFd;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::{UnixListener, UnixStream};
use std::sync::atomic::{AtomicU32, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Mutex, RwLock};
use std::time::{Duration, Instant};

extern "C" {
    fn getrandom(buf: *mut u8, buflen: usize, flags: u32) -> isize;
    fn prctl(option: i32, ...) -> i32;
    fn mallopt(param: i32, value: i32) -> i32;
    fn listen(fd: i32, backlog: i32) -> i32;
    fn poll(fds: *mut PollFd, nfds: u64, timeout: i32) -> i32;
    fn recvmsg(fd: i32, msg: *mut MsgHdr, flags: i32) -> isize;
    fn close(fd: i32) -> i32;
}

/// Most `--threads`.
const MAX_THREADS: u64 = 1024;
/// Most `--io-timeout` seconds (one day), and its default.
const MAX_IO_TIMEOUT: u64 = 86_400;
const DEFAULT_IO_TIMEOUT: u64 = 60;
/// How long `drop` waits for the connections' threads to end.
const DROP_WAIT: Duration = Duration::from_secs(5);
/// `M_MMAP_THRESHOLD` of glibc's `mallopt`, and the value it is fixed at (glibc's initial one).
/// Setting it turns off glibc's dynamic threshold, which a large free would raise, so that later
/// large buffers would come from memory already resident instead of fresh pages: the time of a
/// request would depend on what an earlier connection asked (review R5 LOW 2).
const M_MMAP_THRESHOLD: i32 = -3;
const MMAP_THRESHOLD: i32 = 128 << 10;
/// `M_ARENA_MAX` of glibc's `mallopt`: one arena for every thread, so that how many arenas exist,
/// and how full each is, does not depend on how many threads an earlier connection kept busy
/// (review R4b LOW 5).
const M_ARENA_MAX: i32 = -8;
/// The listen backlog: connections the kernel queues before `accept` (Rust's default is the
/// system's `somaxconn`, 4096). A connection still queued when `drop` comes is closed by it.
const BACKLOG: i32 = 2 * MAX_CONNS as i32;

#[repr(C)]
struct PollFd {
    fd: i32,
    events: i16,
    revents: i16,
}
const POLLIN: i16 = 1;

/// Wait until `fd` is readable (a connection waits in the backlog); an interrupted or failed poll
/// returns too (the caller's `accept` then decides).
fn wait_readable(fd: i32) {
    let mut p = PollFd { fd, events: POLLIN, revents: 0 };
    unsafe { poll(&mut p, 1, -1) };
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

/// The secret state: the PRF, the signer and the mode. `None` once wiped at shutdown.
struct Keys {
    prf: Keyed,
    signer: Signer,
    /// `None` in the service run; in replay mode, the next replay index (set to 0 by each
    /// `replay` line, under the write lock).
    replay: Option<AtomicU32>,
}

struct State {
    keys: RwLock<Option<Keys>>,
    /// Connections holding a slot (`live`): incremented on accept, decremented when the
    /// connection's thread ends (after its registry entry is removed and its socket closed).
    conns: AtomicUsize,
    /// A clone of every served connection's socket, by connection number, so that `drop` can shut
    /// them down; an entry is removed when its worker has finished it.
    registry: Mutex<HashMap<u64, UnixStream>>,
    /// The listening socket (non-blocking: the accept loop waits in `poll`).
    listener: UnixListener,
    /// Held from a connection's `accept` to its registration, and by `drop` while it empties the
    /// backlog and shuts the registered connections down: no connection is between the two then.
    gate: Mutex<()>,
    io_timeout: Duration,
    requests: AtomicU64,
    queries: AtomicU64,
    query_bytes: AtomicU64,
    signatures: AtomicU64,
    replays: AtomicU64,
    mismatches: AtomicU64,
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

/// Refusals so far; the first `REFUSALS_LOGGED` are written to stderr (the runner puts them in
/// the result, so a prover's failure on a cap is visible).
static REFUSALS: AtomicU64 = AtomicU64::new(0);
const REFUSALS_LOGGED: u64 = 32;

/// An error response; the connection is closed after it.
fn refuse(w: &mut UnixStream, status: u8, msg: &str) -> io::Result<()> {
    if REFUSALS.fetch_add(1, Ordering::Relaxed) < REFUSALS_LOGGED {
        eprintln!("rf-oracle: refused (status {status}): {msg}");
    }
    let mut r = header(status, 0, msg.len() as u64).to_vec();
    r.extend_from_slice(msg.as_bytes());
    w.write_all(&r)
}

/// The refusal of a connection that sent ancillary data.
const ANCILLARY: &str = "ancillary data (file descriptors, credentials) is not accepted";

// `recvmsg(2)` on x86_64 and aarch64 Linux (glibc's `struct iovec`, `struct msghdr`, `struct cmsghdr`)
#[repr(C)]
struct IoVec {
    base: *mut u8,
    len: usize,
}
#[repr(C)]
struct MsgHdr {
    name: *mut u8,
    namelen: u32,
    iov: *mut IoVec,
    iovlen: usize,
    control: *mut u8,
    controllen: usize,
    flags: i32,
}
const _: () = assert!(std::mem::size_of::<usize>() == 8 && std::mem::size_of::<MsgHdr>() == 56);
const MSG_CTRUNC: i32 = 0x8;
const MSG_CMSG_CLOEXEC: i32 = 0x4000_0000;
const SOL_SOCKET: i32 = 1;
const SCM_RIGHTS: i32 = 1;
/// `sizeof(struct cmsghdr)`: `cmsg_len: usize`, `cmsg_level: i32`, `cmsg_type: i32`.
const CMSG_HDR: usize = 16;
const CONTROL: usize = 256;

/// The read side of a connection, through `recvmsg` with a control buffer. Plain bytes pass; a
/// message that carries any control message, or whose control data was truncated (`MSG_CTRUNC`),
/// is an error, after every file descriptor it delivered (`SCM_RIGHTS`) is closed; `ancillary`
/// is then set and every later read fails too.
struct Plain {
    s: UnixStream,
    ancillary: bool,
}

impl Plain {
    fn new(s: UnixStream) -> Plain {
        Plain { s, ancillary: false }
    }
}

fn ancillary_error() -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, ANCILLARY)
}

/// Close every file descriptor of the `SCM_RIGHTS` messages in `ctl[..len]`.
fn close_rights(ctl: &[u8], len: usize) {
    let len = len.min(ctl.len());
    let mut off = 0usize;
    while off + CMSG_HDR <= len {
        let clen = usize::from_ne_bytes(ctl[off..off + 8].try_into().unwrap());
        let level = i32::from_ne_bytes(ctl[off + 8..off + 12].try_into().unwrap());
        let ty = i32::from_ne_bytes(ctl[off + 12..off + 16].try_into().unwrap());
        if clen < CMSG_HDR || off + clen > len {
            break;
        }
        if level == SOL_SOCKET && ty == SCM_RIGHTS {
            for fd in ctl[off + CMSG_HDR..off + clen].chunks_exact(4) {
                unsafe { close(i32::from_ne_bytes(fd.try_into().unwrap())) };
            }
        }
        off += (clen + 7) & !7;
    }
}

impl Read for Plain {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if self.ancillary {
            return Err(ancillary_error());
        }
        let mut ctl = [0u64; CONTROL / 8];
        let mut iov = IoVec { base: buf.as_mut_ptr(), len: buf.len() };
        loop {
            let mut m = MsgHdr {
                name: std::ptr::null_mut(),
                namelen: 0,
                iov: &mut iov,
                iovlen: 1,
                control: ctl.as_mut_ptr().cast(),
                controllen: CONTROL,
                flags: 0,
            };
            let n = unsafe { recvmsg(self.s.as_raw_fd(), &mut m, MSG_CMSG_CLOEXEC) };
            if n < 0 {
                let e = io::Error::last_os_error();
                if e.kind() == io::ErrorKind::Interrupted {
                    continue;
                }
                return Err(e);
            }
            if m.controllen > 0 || m.flags & MSG_CTRUNC != 0 {
                let bytes = unsafe { std::slice::from_raw_parts(ctl.as_ptr().cast::<u8>(), CONTROL) };
                close_rights(bytes, m.controllen);
                self.ancillary = true;
                return Err(ancillary_error());
            }
            return Ok(n as usize);
        }
    }
}

/// Serve one connection until the client closes it, sends a request that is refused, or stays a
/// whole `io_timeout` in one read or write (the socket's `SO_RCVTIMEO`/`SO_SNDTIMEO`: an error).
fn serve(mut w: UnixStream, st: &State) -> io::Result<()> {
    let mut rd = BufReader::with_capacity(1 << 16, Plain::new(w.try_clone()?));
    let mut body: Vec<u8> = Vec::new();
    let mut resp: Vec<u8> = Vec::new();
    loop {
        let mut h = [0u8; 16];
        match rd.read_exact(&mut h) {
            Err(_) if rd.get_ref().ancillary => return refuse(&mut w, ST_BAD, ANCILLARY),
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
        if let Err(e) = rd.read_exact(&mut body) {
            return if rd.get_ref().ancillary { refuse(&mut w, ST_BAD, ANCILLARY) } else { Err(e) };
        }
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
        // the response, or a refusal, under the read lock; every write comes after the lock is
        // released, so a response the client does not take never holds `replay` or the shutdown
        let refusal: Option<(u8, String)> = 'locked: {
            let guard = st.keys.read().unwrap();
            let Some(keys) = guard.as_ref() else { return Ok(()) };
            resp.clear();
            if op == OP_VK {
                resp.extend_from_slice(&header(ST_OK, 0, 32));
                resp.extend_from_slice(&keys.signer.vk());
                break 'locked None;
            }
            // the answers are computed in place, after room for the header
            resp.resize(16 + 32 * qs.len(), 0);
            let (ans, _) = resp[16..].as_chunks_mut::<32>();
            keys.prf.eval_many(&qs, ans);
            let sig = if op == OP_SIGN {
                let td = trace_digest(&qs, ans);
                match &keys.replay {
                    None => match keys.signer.sign(&td) {
                        Ok(s) => Some(s),
                        Err(_) => break 'locked Some((ST_EXHAUSTED, "all 2^16 one-time keys are used".into())),
                    },
                    Some(next) => {
                        // one atomic step, saturating at 2^16 (no digest is recorded there)
                        let j = next.try_update(Ordering::SeqCst, Ordering::SeqCst, |x| Some((x + 1).min(NKEYS as u32))).unwrap();
                        match keys.signer.resign(j, &td) {
                            Ok(s) => Some(s),
                            Err(e) => {
                                st.mismatches.fetch_add(1, Ordering::Relaxed);
                                let why = match e {
                                    NotSigned::Nothing => "no trace was signed there in the service run",
                                    NotSigned::Differs => "the trace digest differs from the one signed there in the service run",
                                };
                                break 'locked Some((ST_MISMATCH, format!("replay at one-time key index {j}: {why}")));
                            }
                        }
                    }
                }
            } else {
                None
            };
            let replaying = keys.replay.is_some();
            drop(guard);
            let n = 32 * qs.len() + if sig.is_some() { rf_oracle::wots::Sig::BYTES } else { 0 };
            resp[..16].copy_from_slice(&header(ST_OK, count, n as u64));
            if let Some(s) = &sig {
                s.encode(&mut resp);
                if replaying { &st.replays } else { &st.signatures }.fetch_add(1, Ordering::Relaxed);
            }
            st.queries.fetch_add(count as u64, Ordering::Relaxed);
            st.query_bytes.fetch_add(blen - 4 * count as u64, Ordering::Relaxed);
            None
        };
        if let Some((status, msg)) = refusal {
            return refuse(&mut w, status, &msg);
        }
        st.requests.fetch_add(1, Ordering::Relaxed);
        w.write_all(&resp)?;
    }
}

/// Write `line` and a newline on stdout and flush; a closed stdout is ignored (the runner reads
/// these lines; a failed write must not end the control thread with a panic).
fn say(line: &str) {
    let mut so = io::stdout().lock();
    let _ = writeln!(so, "{line}").and_then(|_| so.flush());
}

/// The statistics line (the `stats` control line, and the last line at shutdown).
fn stats_line(st: &State) -> String {
    format!(
        "stats requests={} queries={} query_bytes={} signatures={} refusals={} replays={} mismatches={} live={}",
        st.requests.load(Ordering::SeqCst),
        st.queries.load(Ordering::SeqCst),
        st.query_bytes.load(Ordering::SeqCst),
        st.signatures.load(Ordering::SeqCst),
        REFUSALS.load(Ordering::SeqCst),
        st.replays.load(Ordering::SeqCst),
        st.mismatches.load(Ordering::SeqCst),
        st.conns.load(Ordering::SeqCst)
    )
}

/// Accept and close every connection waiting in the listen backlog of the non-blocking `l`, until
/// none is left; how many. A queued connection was never accepted, so it is in no count (`live`)
/// and no registry: without this it would be served after the request that opened it is dead
/// (review R4b LOW 4).
fn drain_backlog(l: &UnixListener) -> usize {
    let mut n = 0;
    loop {
        match l.accept() {
            Ok((c, _)) => {
                drop(c);
                n += 1;
            }
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(_) => return n,           // WouldBlock: the backlog is empty
        }
    }
}

/// The `drop` control line: under the accept gate, close every connection still in the listen
/// backlog (`drain_backlog`) and shut every registered connection down (both directions: a blocked
/// read sees the end, a blocked write fails, so its worker finishes it and its socket is closed,
/// which frees its receive queue and any file descriptor in flight there); then wait up to
/// `DROP_WAIT` for the slots to be released, and print `dropped live=N`, `N` the connections still
/// open (returned).
fn drop_conns(st: &State) -> usize {
    {
        let _g = st.gate.lock().unwrap_or_else(|e| e.into_inner());
        drain_backlog(&st.listener);
        for s in st.registry.lock().unwrap_or_else(|e| e.into_inner()).values() {
            let _ = s.shutdown(Shutdown::Both);
        }
    }
    let t0 = Instant::now();
    while st.conns.load(Ordering::SeqCst) > 0 && t0.elapsed() < DROP_WAIT {
        std::thread::sleep(Duration::from_millis(2));
    }
    let live = st.conns.load(Ordering::SeqCst);
    say(&format!("dropped live={live}"));
    live
}

/// A connection's slot and registry entry, released when its worker has finished it (by return or
/// by panic), or at once if it is never handed to a worker.
struct Slot(&'static State, u64);
impl Drop for Slot {
    fn drop(&mut self) {
        // the registry's clone is the last descriptor of the socket: closing it frees the queue
        drop(self.0.registry.lock().unwrap_or_else(|e| e.into_inner()).remove(&self.1));
        self.0.conns.fetch_sub(1, Ordering::SeqCst);
    }
}

/// The state of a service listening on `listener` (made non-blocking, its backlog `BACKLOG`).
fn new_state(keys: Option<Keys>, listener: UnixListener, io_timeout: Duration, socket: String) -> io::Result<&'static State> {
    listener.set_nonblocking(true)?;
    if unsafe { listen(listener.as_raw_fd(), BACKLOG) } != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(Box::leak(Box::new(State {
        keys: RwLock::new(keys),
        conns: AtomicUsize::new(0),
        registry: Mutex::new(HashMap::new()),
        listener,
        gate: Mutex::new(()),
        io_timeout,
        requests: AtomicU64::new(0),
        queries: AtomicU64::new(0),
        query_bytes: AtomicU64::new(0),
        signatures: AtomicU64::new(0),
        replays: AtomicU64::new(0),
        mismatches: AtomicU64::new(0),
        socket,
    })))
}

/// Start the `MAX_CONNS` workers, then accept connections for ever: each, under the gate, takes a
/// slot (or is refused with `CAP` above `MAX_CONNS`), is registered and is handed to a worker.
fn accept_loop(st: &'static State) -> ! {
    let (tx, rx) = std::sync::mpsc::channel::<(UnixStream, Slot)>();
    let rx: &'static Mutex<std::sync::mpsc::Receiver<(UnixStream, Slot)>> = Box::leak(Box::new(Mutex::new(rx)));
    for _ in 0..MAX_CONNS {
        std::thread::Builder::new()
            .spawn(move || loop {
                let job = rx.lock().unwrap_or_else(|e| e.into_inner()).recv();
                let Ok((conn, slot)) = job else { return };
                let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| serve(conn, st)));
                drop(slot);
            })
            .expect("rf-oracle: cannot start a worker");
    }
    let mut next_id = 0u64;
    loop {
        wait_readable(st.listener.as_raw_fd());
        let g = st.gate.lock().unwrap_or_else(|e| e.into_inner());
        let conn = match st.listener.accept() {
            Ok((c, _)) => c,
            Err(e) if matches!(e.kind(), io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted) => continue,
            Err(_) => {
                drop(g);
                std::thread::sleep(Duration::from_millis(10));      // e.g. out of descriptors
                continue;
            }
        };
        if st.conns.fetch_add(1, Ordering::SeqCst) >= MAX_CONNS {
            st.conns.fetch_sub(1, Ordering::SeqCst);
            drop(g);
            let mut c = conn;
            // the refusal fits an empty socket buffer; the timeout only bounds the accept loop
            let _ = c.set_nonblocking(false);
            let _ = c.set_write_timeout(Some(Duration::from_secs(1)));
            let _ = refuse(&mut c, ST_CAP, "more than 32 connections");
            continue;
        }
        next_id += 1;
        let slot = Slot(st, next_id);
        let Ok(clone) = conn
            .set_nonblocking(false)
            .and_then(|_| conn.set_read_timeout(Some(st.io_timeout)))
            .and_then(|_| conn.set_write_timeout(Some(st.io_timeout)))
            .and_then(|_| conn.try_clone())
        else {
            continue;
        };
        st.registry.lock().unwrap_or_else(|e| e.into_inner()).insert(next_id, clone);
        drop(g);
        let _ = tx.send((conn, slot));
    }
}

/// The `replay` control line: once in-flight requests finish (the write lock), enter replay mode
/// or stay in it, reset the replay index to 0, and print `key <hex k>` and `replay ready`.
fn enter_replay(st: &State) {
    let mut g = st.keys.write().unwrap_or_else(|e| e.into_inner());
    let Some(keys) = g.as_mut() else { return };
    keys.replay = Some(AtomicU32::new(0));
    let mut k = keys.prf.key();
    let mut so = io::stdout().lock();
    let _ = writeln!(so, "key {}", hex(&k)).and_then(|_| writeln!(so, "replay ready")).and_then(|_| so.flush());
    keccak::wipe(&mut k);
}

/// Wipe the keys (after in-flight requests finish), report, remove the socket, exit.
fn shutdown(st: &State) -> ! {
    let mut g = st.keys.write().unwrap_or_else(|e| e.into_inner());
    if let Some(mut k) = g.take() {
        k.prf.wipe();
        k.signer.wipe();
    }
    let _ = std::fs::remove_file(&st.socket);
    say(&stats_line(st));
    std::process::exit(0)
}

fn usage() -> ! {
    eprintln!("usage: rf-oracle --socket PATH [--threads N] [--io-timeout SECS] [--insecure-test-keys PRFKEY_HEX SEED_HEX (test builds only)]");
    eprintln!("       rf-oracle --data-roots [--threads N] FILE…");
    eprintln!("       (N a decimal count from 1 to {MAX_THREADS}, SECS from 1 to {MAX_IO_TIMEOUT})");
    std::process::exit(2)
}

/// A decimal count from 1 to `max`, ASCII digits only (no sign, no space); `None` otherwise.
fn count_arg(s: &str, max: u64) -> Option<u64> {
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    s.parse::<u64>().ok().filter(|&n| (1..=max).contains(&n))
}

/// `rf-oracle --data-roots FILE…`: read every file (each checked before any is hashed), then write
/// the leaf statements in argument order.
fn data_roots_mode(files: &[String], threads: usize) -> ! {
    let refuse = |f: &str, why: String| -> ! {
        eprintln!("rf-oracle --data-roots: {f}: {why}");
        std::process::exit(2)
    };
    let mut data = Vec::with_capacity(files.len());
    for f in files {
        // the size first, so that a file above the cap is never read
        let size = match std::fs::metadata(f) {
            Ok(m) if m.is_file() => m.len(),
            Ok(_) => refuse(f, "not a regular file".into()),
            Err(e) => refuse(f, format!("cannot read: {e}")),
        };
        if size % BLOCK as u64 != 0 {
            refuse(f, format!("{size} bytes, not a multiple of {BLOCK}"));
        }
        if size / BLOCK as u64 > LEAF_CAP as u64 {
            refuse(f, format!("{} blocks, above leafCap = 2^20", size / BLOCK as u64));
        }
        match std::fs::read(f) {
            Ok(d) if d.len() as u64 == size => data.push(d),
            Ok(d) => refuse(f, format!("changed size while read ({size}, then {} bytes)", d.len())),
            Err(e) => refuse(f, format!("cannot read: {e}")),
        }
    }
    let leaves: Vec<&[u8]> = data.iter().map(|d| d.as_slice()).collect();
    let mut out = String::with_capacity(65 * leaves.len());
    for (d, r) in leaves.iter().zip(data_roots(&leaves, threads)) {
        out.push_str(&hex(&leaf_stmt(&r, (d.len() / BLOCK) as u64)));
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
    let (mut socket, mut threads, mut data_roots, mut files) = (None, None, false, Vec::new());
    let mut io_timeout: Option<u64> = None;
    #[allow(unused_mut)]
    let mut test: Option<([u8; 32], [u8; 32])> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--socket" if i + 1 < args.len() => socket = Some(args[i + 1].clone()),
            // a decimal count from 1 to 1024 (ASCII digits only); anything else is refused (exit 2),
            // never silently every CPU, never a panic in keygen
            "--threads" if i + 1 < args.len() => match count_arg(&args[i + 1], MAX_THREADS) {
                Some(t) => threads = Some(t as usize),
                None => usage(),
            },
            "--io-timeout" if i + 1 < args.len() => match count_arg(&args[i + 1], MAX_IO_TIMEOUT) {
                Some(t) => io_timeout = Some(t),
                None => usage(),
            },
            "--data-roots" => {
                data_roots = true;
                i += 1;
                continue;
            }
            #[cfg(feature = "insecure-test-keys")]
            "--insecure-test-keys" if i + 2 < args.len() => {
                test = Some((unhex32(&args[i + 1]).unwrap_or_else(|| usage()), unhex32(&args[i + 2]).unwrap_or_else(|| usage())));
                i += 1;
            }
            f if data_roots && !f.starts_with("--") => {
                files.push(f.to_string());
                i += 1;
                continue;
            }
            _ => usage(),
        }
        i += 2;
    }
    let threads = threads.unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1));
    // a fixed mmap threshold (glibc's dynamic one would make a request's allocation cost depend on
    // an earlier connection's frees); glibc's mallopt returns 1 on success
    if unsafe { mallopt(M_MMAP_THRESHOLD, MMAP_THRESHOLD) } != 1 || unsafe { mallopt(M_ARENA_MAX, 1) } != 1 {
        eprintln!("rf-oracle: mallopt(M_MMAP_THRESHOLD, M_ARENA_MAX) failed");
        std::process::exit(1);
    }
    if data_roots {
        if socket.is_some() || test.is_some() || io_timeout.is_some() {
            usage()
        }
        data_roots_mode(&files, threads)
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
    // the owner only: the sandboxed provers run in a user namespace that maps their uid to this
    // process's uid, so they can connect; no other uid can
    if let Err(e) = std::fs::set_permissions(&socket, std::fs::Permissions::from_mode(0o600)) {
        eprintln!("rf-oracle: cannot chmod {socket}: {e}");
        let _ = std::fs::remove_file(&socket);
        std::process::exit(1)
    }
    let vk = signer.vk();
    let io_timeout = Duration::from_secs(io_timeout.unwrap_or(DEFAULT_IO_TIMEOUT));
    let st = new_state(Some(Keys { prf, signer, replay: None }), listener, io_timeout, socket.clone()).unwrap_or_else(|e| {
        eprintln!("rf-oracle: cannot listen on {socket}: {e}");
        let _ = std::fs::remove_file(&socket);
        std::process::exit(1)
    });
    println!("vk {}", hex(&vk));
    println!("keygen_ms {keygen_ms:.1}");
    println!("simd scalar");
    println!("ready");
    let _ = io::stdout().flush();
    // the control pipe: `replay`, `drop` and `stats` lines until end of file (or a read error),
    // then shut down
    std::thread::spawn(move || {
        let mut stdin = io::stdin().lock();
        let mut line = Vec::new();
        loop {
            line.clear();
            if !matches!(stdin.read_until(b'\n', &mut line), Ok(n) if n > 0) {
                break;
            }
            match line.as_slice() {
                b"replay\n" => enter_replay(st),
                b"drop\n" => {
                    drop_conns(st);
                }
                b"stats\n" => say(&stats_line(st)),
                _ => eprintln!("rf-oracle: ignored control line {:?}", String::from_utf8_lossy(&line[..line.len().min(64)])),
            }
        }
        shutdown(st)
    });
    accept_loop(st)
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::os::fd::FromRawFd;

    extern "C" {
        fn sendmsg(fd: i32, msg: *const MsgHdr, flags: i32) -> isize;
        fn socket(domain: i32, ty: i32, protocol: i32) -> i32;
        fn connect(fd: i32, addr: *const u8, len: u32) -> i32;
    }

    /// `connect` the (non-blocking) `c` to the abstract address `a`; whether it was queued.
    fn connect_abstract(c: &UnixStream, a: &std::os::unix::net::SocketAddr) -> bool {
        use std::os::linux::net::SocketAddrExt;
        let name = a.as_abstract_name().unwrap();
        let mut sa = vec![1u8, 0, 0];             // sun_family = AF_UNIX (little-endian u16), then the 0 of an abstract name
        sa.extend_from_slice(name);
        unsafe { connect(c.as_raw_fd(), sa.as_ptr(), sa.len() as u32) == 0 }
    }

    /// Send `data` on `s` with one `SCM_RIGHTS` message carrying `fds`.
    fn send_fds(s: &UnixStream, data: &[u8], fds: &[i32]) {
        let mut ctl = [0u64; 128];
        let bytes = unsafe { std::slice::from_raw_parts_mut(ctl.as_mut_ptr().cast::<u8>(), 1024) };
        let clen = CMSG_HDR + 4 * fds.len();
        bytes[..8].copy_from_slice(&clen.to_ne_bytes());
        bytes[8..12].copy_from_slice(&SOL_SOCKET.to_ne_bytes());
        bytes[12..16].copy_from_slice(&SCM_RIGHTS.to_ne_bytes());
        for (k, fd) in fds.iter().enumerate() {
            bytes[CMSG_HDR + 4 * k..CMSG_HDR + 4 * k + 4].copy_from_slice(&fd.to_ne_bytes());
        }
        let mut iov = IoVec { base: data.as_ptr() as *mut u8, len: data.len() };
        let m = MsgHdr {
            name: std::ptr::null_mut(),
            namelen: 0,
            iov: &mut iov,
            iovlen: 1,
            control: ctl.as_mut_ptr().cast(),
            controllen: (clen + 7) & !7,
            flags: 0,
        };
        assert_eq!(unsafe { sendmsg(s.as_raw_fd(), &m, 0) }, data.len() as isize);
    }

    #[test]
    fn plain_bytes_pass() {
        let (a, b) = UnixStream::pair().unwrap();
        let mut r = BufReader::new(Plain::new(b));
        (&a).write_all(b"hello world").unwrap();
        drop(a);
        let mut got = Vec::new();
        r.read_to_end(&mut got).unwrap();
        assert_eq!(got, b"hello world");
        assert!(!r.get_ref().ancillary);
    }

    #[test]
    fn rights_are_refused_and_closed() {
        let (a, b) = UnixStream::pair().unwrap();
        // the descriptors sent: one end of another pair (and a duplicate of it), whose peer sees
        // the end only once every copy of it is closed
        let (c, mut d) = UnixStream::pair().unwrap();
        let mut r = BufReader::new(Plain::new(b));
        (&a).write_all(b"before").unwrap();
        let mut got = [0u8; 6];
        r.read_exact(&mut got).unwrap();
        assert_eq!(&got, b"before");
        send_fds(&a, b"after", &[c.as_raw_fd(), c.as_raw_fd()]);
        drop(c);
        let e = r.read_exact(&mut got).unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::InvalidData);
        assert!(r.get_ref().ancillary);
        // later reads fail too
        (&a).write_all(b"more").unwrap();
        assert!(r.read(&mut got).is_err());
        // both delivered copies were closed: `d` sees the end
        d.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
        assert_eq!(d.read(&mut got).unwrap(), 0);
    }

    #[test]
    fn too_many_rights_are_closed() {
        // more descriptors than the control buffer holds (60): MSG_CTRUNC, the kernel closes the rest
        let (a, b) = UnixStream::pair().unwrap();
        let (c, mut d) = UnixStream::pair().unwrap();
        let mut r = Plain::new(b);
        send_fds(&a, b"x", &[c.as_raw_fd(); 200]);
        drop(c);
        let mut got = [0u8; 4];
        assert!(r.read(&mut got).is_err() && r.ancillary);
        d.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
        assert_eq!(d.read(&mut got).unwrap(), 0);
    }

    /// A listener on a fresh abstract address (no file), and a client's address for it.
    fn abstract_listener(tag: &str) -> (UnixListener, std::os::unix::net::SocketAddr) {
        use std::os::linux::net::SocketAddrExt;
        let name = format!("rf-oracle-test-{tag}-{}-{:?}", std::process::id(), Instant::now());
        let a = std::os::unix::net::SocketAddr::from_abstract_name(name.as_bytes()).unwrap();
        (UnixListener::bind_addr(&a).unwrap(), a)
    }

    /// Connections never accepted (the accept loop is not running): each written to, then left.
    fn queued(a: &std::os::unix::net::SocketAddr, n: usize) -> Vec<UnixStream> {
        (0..n)
            .map(|_| {
                let c = UnixStream::connect_addr(a).unwrap();
                (&c).write_all(&[0u8; 16]).unwrap();
                c.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
                c
            })
            .collect()
    }

    /// Every client of `cs` sees its connection closed: the end of the stream, or a reset.
    fn all_closed(cs: &mut [UnixStream]) -> bool {
        cs.iter_mut().all(|c| {
            let mut b = [0u8; 1];
            match c.read(&mut b) {
                Ok(0) => true,
                Err(e) => e.kind() == io::ErrorKind::ConnectionReset,
                Ok(_) => false,
            }
        })
    }

    #[test]
    fn drain_closes_the_backlog() {
        let (l, a) = abstract_listener("drain");
        l.set_nonblocking(true).unwrap();
        let mut cs = queued(&a, 7);
        assert_eq!(drain_backlog(&l), 7);
        assert_eq!(l.accept().unwrap_err().kind(), io::ErrorKind::WouldBlock);
        assert!(all_closed(&mut cs));
        assert_eq!(drain_backlog(&l), 0);
    }

    #[test]
    fn drop_leaves_no_backlog() {
        // a service's state with no keys and no accept loop: every connection stays in the backlog
        let (l, a) = abstract_listener("drop");
        let st = new_state(None, l, Duration::from_secs(5), String::new()).unwrap();
        let mut cs = queued(&a, 40);           // more than MAX_CONNS, within BACKLOG
        assert_eq!(st.conns.load(Ordering::SeqCst), 0);   // in no count: `live=0` before the fix too
        assert_eq!(drop_conns(st), 0);
        // nothing is left to be accepted and served after the request's death
        assert_eq!(st.listener.accept().unwrap_err().kind(), io::ErrorKind::WouldBlock);
        assert!(all_closed(&mut cs));
    }

    #[test]
    fn the_backlog_is_bounded() {
        let (l, a) = abstract_listener("backlog");
        let _st = new_state(None, l, Duration::from_secs(5), String::new()).unwrap();
        // a non-blocking connect past the backlog fails (EAGAIN) instead of queueing without bound
        let mut ok = 0;
        for _ in 0..(4 * BACKLOG) {
            let s = unsafe { socket(1, 1 | 0o4000, 0) };           // AF_UNIX, SOCK_STREAM | SOCK_NONBLOCK
            assert!(s >= 0);
            let c = unsafe { UnixStream::from_raw_fd(s) };
            if connect_abstract(&c, &a) {
                ok += 1;
            }
            std::mem::forget(c);              // kept open until the test ends
        }
        assert!(ok <= BACKLOG as usize + 1 && ok >= MAX_CONNS, "{ok} connections queued");
    }

    #[test]
    fn count_args() {
        assert_eq!(count_arg("1", 1024), Some(1));
        assert_eq!(count_arg("1024", 1024), Some(1024));
        for bad in ["", "0", "1025", "+3", " 3", "-1", "1.5", "x", "99999999999999999999999"] {
            assert_eq!(count_arg(bad, 1024), None, "{bad:?}");
        }
    }
}
