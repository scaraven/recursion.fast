"""The oracle service's lifecycle, and a Python client of its wire protocol (`service/PROTOCOL.md`).

TRUSTED RUNTIME (`Service`): one service process per timed run. `start` launches `rf-oracle` with
its socket in a fresh directory, under its own memory cap, and waits for `ready`; `stop` closes its
stdin, which makes it wipe its keys and exit, and returns its statistics. The client (`Client`) is
used by tests and by the smoke's deliberately broken provers, not by the benchmark.
"""
import os
import select
import socket
import struct
import subprocess
import time

OP_QUERY, OP_SIGN, OP_VK = 1, 2, 3
SOCKET_NAME = "oracle.sock"


class ServiceError(RuntimeError):
    pass


class Service:
    """One `rf-oracle` process. `wrap` is the command prefix that applies the memory cap
    (`sandbox.memcap`); `log` the liveness log path (liveness mode)."""

    def __init__(self, binary, sock_dir, log=None, wrap=(), stderr_path=None):
        self.binary, self.sock_dir, self.log, self.wrap = binary, sock_dir, log, list(wrap)
        self.stderr_path = stderr_path or os.path.join(sock_dir + ".service.log")
        self.proc, self.vk, self.info = None, None, {}

    @property
    def socket_path(self):
        return os.path.join(self.sock_dir, SOCKET_NAME)

    def start(self, timeout=600):
        os.makedirs(self.sock_dir, exist_ok=False)
        cmd = self.wrap + [self.binary, "--socket", SOCKET_NAME] + (["--log", self.log] if self.log else [])
        self._err = open(self.stderr_path, "ab")
        # the socket is bound relative to the service's cwd: Unix socket paths are capped at 108 bytes
        self.proc = subprocess.Popen(cmd, cwd=self.sock_dir, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     stderr=self._err, close_fds=True)
        deadline = time.monotonic() + timeout
        buf = b""
        while b"ready\n" not in buf:
            left = deadline - time.monotonic()
            if left <= 0 or not select.select([self.proc.stdout], [], [], left)[0]:
                self.kill()
                raise ServiceError("service did not become ready")
            chunk = os.read(self.proc.stdout.fileno(), 4096)
            if not chunk:
                raise ServiceError(f"service exited before ready (code {self.proc.wait()})")
            buf += chunk
        for line in buf.decode().splitlines():
            k, _, v = line.partition(" ")
            if k == "INSECURE":
                self.kill()
                raise ServiceError("service runs with fixed test keys")
            if k in ("vk", "keygen_ms", "simd"):
                self.info[k] = v
        vk = bytes.fromhex(self.info.get("vk", ""))
        if len(vk) != 32 or not os.path.exists(self.socket_path):
            self.kill()
            raise ServiceError("service printed no public key or bound no socket")
        self.vk = vk
        return self

    def stop(self, timeout=120):
        """Close stdin (the service wipes its keys and exits); its `stats` as a dict."""
        if self.proc is None:
            return {}
        self.proc.stdin.close()
        try:
            out, _ = self.proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            self.kill()
            raise ServiceError("service did not exit")
        self._err.close()
        stats = {}
        for line in out.decode().splitlines():
            if line.startswith("stats "):
                stats = {k: int(v) for k, v in (kv.split("=") for kv in line.split()[1:])}
        code, self.proc = self.proc.returncode, None
        if code != 0:
            raise ServiceError(f"service exited with code {code}")
        return stats

    def kill(self):
        if self.proc is not None:
            self.proc.kill()
            self.proc.wait()
            self.proc = None


class Client:
    """A blocking client on one connection."""

    def __init__(self, path):
        self.s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        d, name = os.path.split(os.path.abspath(path))
        cwd = os.getcwd()
        try:                                   # connect by a short relative path (108-byte limit)
            os.chdir(d)
            self.s.connect(name)
        finally:
            os.chdir(cwd)

    def _recv(self, n):
        out = bytearray()
        while len(out) < n:
            c = self.s.recv(min(n - len(out), 1 << 20))
            if not c:
                raise ServiceError("connection closed")
            out += c
        return bytes(out)

    def call(self, op, items=(), raw=None):
        """(status, count, body) of one request with the given items."""
        if raw is None:
            body = b"".join(struct.pack("<I", len(q)) + q for q in items)
            raw = struct.pack("<B3xIQ", op, len(items), len(body)) + body
        self.s.sendall(raw)
        st, count, n = struct.unpack("<B3xIQ", self._recv(16))
        return st, count, self._recv(n)

    def query(self, qs):
        st, _, body = self.call(OP_QUERY, qs)
        if st:
            raise ServiceError(f"QUERY refused ({st}): {body.decode(errors='replace')}")
        return [body[32 * i:32 * i + 32] for i in range(len(qs))]

    def sign(self, qs):
        """The raw `SIGN` response body: answers ‖ idx:u32 ‖ ots ‖ path."""
        st, _, body = self.call(OP_SIGN, qs)
        if st:
            raise ServiceError(f"SIGN refused ({st}): {body.decode(errors='replace')}")
        return body

    def vk(self):
        st, _, body = self.call(OP_VK)
        if st:
            raise ServiceError(f"VK refused ({st})")
        return body

    def close(self):
        self.s.close()
