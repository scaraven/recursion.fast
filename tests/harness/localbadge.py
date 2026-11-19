"""The runner's badge runner (`rfh.checks.Badge`) without the sandbox, for the core CI's tests that run
where bubblewrap is not set up (`tests/harness/accprobe/run.py`, `tests/harness/test_serve.py`):
the same warm-up, start-up cap, request loop and clocks, the process started directly (pinned to
the same core) and the store and warm-up directory seen at their own paths."""
import os
import subprocess
import time

from rfh.checks import Badge


class LocalBadge(Badge):
    def __init__(self, cmd, scratch, start_s=None):
        super().__init__(os.path.dirname(cmd[0]), None, scratch, start_s)
        self.cmd = list(cmd)

    def start(self, store, warm_dir):
        p = subprocess.Popen(["taskset", "-c", str(self.core)] + self.cmd + ["--serve"], stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)

        def stop():
            if p.poll() is None:
                p.kill()
            p.wait()
        return p, stop, time.monotonic(), store, warm_dir or ""
