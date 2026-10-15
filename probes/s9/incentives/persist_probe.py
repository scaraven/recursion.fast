#!/usr/bin/env python3
"""S9 incentives probe: is there any state a benchmark step can leave for a later step?

Run once with `write`, then (in a separate sandboxed process) with `read`. Each channel prints
`<channel>: <result>`. A channel that reads back the marker written by an earlier sandboxed step
is a cross-step (and, since the three runs of an evaluation reuse their instances, cross-run)
persistence channel: a cache of proofs keyed by the inputs would make runs 2 and 3 free.

Channels tried (all from inside `bwrap-landrun.sh --minimal-root`, as the runner starts a step):
  keyring-user     add_key("user", ..., KEY_SPEC_USER_KEYRING)   (per-uid kernel keyring)
  keyring-session  add_key on the session keyring
  sysv-shm         shmget(IPC_PRIVATE-free fixed key)            (needs --unshare-ipc to isolate)
  dev-shm          a file in /dev/shm
  tmp              a file in /tmp
"""
import ctypes, ctypes.util, os, sys

MARK = b"rf-s9-persist-marker"
libc = ctypes.CDLL(ctypes.util.find_library("c"), use_errno=True)
SYS_add_key, SYS_request_key, SYS_keyctl = 248, 249, 250          # x86-64
KEY_SPEC_SESSION_KEYRING, KEY_SPEC_USER_KEYRING = -3, -4
KEYCTL_READ = 11


def add_key(ring):
    r = libc.syscall(SYS_add_key, b"user", b"rf-s9", MARK, len(MARK), ctypes.c_int(ring))
    return r if r >= 0 else f"errno {ctypes.get_errno()}"


def find_key(ring):
    r = libc.syscall(SYS_request_key, b"user", b"rf-s9", None, ctypes.c_int(ring))
    if r < 0:
        return f"not found (errno {ctypes.get_errno()})"
    buf = ctypes.create_string_buffer(64)
    n = libc.syscall(SYS_keyctl, KEYCTL_READ, r, buf, 64)
    return f"FOUND id {r}: {buf.raw[:n]!r}"


def shm(write):
    IPC_CREAT, key = 0o1000, 0x52463953
    shmid = libc.shmget(key, 4096, (IPC_CREAT | 0o600) if write else 0o600)
    if shmid < 0:
        return f"no segment (errno {ctypes.get_errno()})"
    libc.shmat.restype = ctypes.c_void_p
    addr = libc.shmat(shmid, None, 0)
    if write:
        ctypes.memmove(addr, MARK, len(MARK))
        return f"written (shmid {shmid})"
    return f"FOUND shmid {shmid}: {ctypes.string_at(addr, len(MARK))!r}"


def file(path, write):
    try:
        if write:
            open(path, "wb").write(MARK)
            return "written"
        return f"FOUND: {open(path, 'rb').read()!r}"
    except OSError as e:
        return f"{type(e).__name__}: {e.strerror}"


mode = sys.argv[1]
w = mode == "write"
print("keyring-user:", add_key(KEY_SPEC_USER_KEYRING) if w else find_key(KEY_SPEC_USER_KEYRING))
print("keyring-session:", add_key(KEY_SPEC_SESSION_KEYRING) if w else find_key(KEY_SPEC_SESSION_KEYRING))
print("sysv-shm:", shm(w))
print("dev-shm:", file("/dev/shm/rf-s9", w))
print("tmp:", file("/tmp/rf-s9", w))
