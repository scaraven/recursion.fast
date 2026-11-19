"""The runner's badge runner (`rfh.checks.Badge`) without the sandbox, for the core CI's tests that run
where bubblewrap is not set up (`tests/harness/accprobe/run.py`, `tests/harness/test_serve.py`):
the same warm-up, start-up cap, request loop and clocks, the process started directly (pinned to
the same core) and the store and warm-up directory seen at their own paths."""
import os
import subprocess
import time

from rfh.checks import Badge, copy_bytes, warm_file
from rfh.sandbox import runner_path


class LocalBadge(Badge):
    def __init__(self, cmd, scratch, start_s=None):
        super().__init__(os.path.dirname(cmd[0]), None, scratch, start_s)
        self.cmd = list(cmd)

    def view(self, items, store, warm):
        """Each run's store and warm-up file, fresh (as `Badge.view`); no copy of the executable or
        of what it loads, which run from the host."""
        root = runner_path("local")
        binds = [("ro", self.stage(items, store, os.path.join(root, "store")), "/store")]
        if warm:
            os.mkdir(os.path.join(root, "warm"), 0o700)
            copy_bytes(os.path.join(root, "warm", "warm.bin"), warm_file())
            binds.append(("ro", os.path.join(root, "warm"), "/warm"))
        return root, binds

    def start(self, binds):
        at = {inside: host for _, host, inside in binds}
        p = subprocess.Popen(["taskset", "-c", str(self.core)] + self.cmd + ["--serve"], stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)

        def stop():
            if p.poll() is None:
                p.kill()
            p.wait()
        return p, stop, time.monotonic(), at["/store"], at.get("/warm", "")
