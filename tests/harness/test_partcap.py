#!/usr/bin/env python3
"""A benchmark part that runs past `PART_S` after the prover's build has started is the entry's
REJECT, never a missing part (review M-3 of stage F-ivc).

  python3 tests/harness/test_partcap.py

A prover whose `setup` sleeps runs through `harness/evaluate.py`'s `bench_job` with `PART_S`
lowered to 20 s and the mock badge: the result is `benchmark: fail`, verdict REJECT, its reason
names `PART_S` and the stage the runner's checkpoint reached (`prover setup`).
"""
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))


def main():
    tmp = tempfile.mkdtemp(prefix="rf-partcap-", dir=os.environ.get("RF_TEST_TMP"))
    badge = os.path.join(tmp, "badge")
    os.makedirs(badge)
    for f in os.listdir(os.path.join(HERE, "mock_badge")):
        shutil.copy(os.path.join(HERE, "mock_badge", f), badge)
    shutil.copy(os.path.join(ROOT, "tests", "service", "wots_ref.py"), badge)
    shutil.copy(os.path.join(ROOT, "harness", "rfh", "signed.py"), badge)
    entry = os.path.join(tmp, "entry")
    os.makedirs(os.path.join(entry, "prover"))
    c = os.path.join(tmp, "p.c")
    open(c, "w").write('#include <string.h>\n#include <unistd.h>\n'
                       'int main(int c, char **v){if(c>1&&!strcmp(v[1],"setup"))sleep(600);return 0;}\n')
    subprocess.run(["gcc", "-S", "-O1", "-o", os.path.join(entry, "prover", "p.s"), c], check=True)
    spec = importlib.util.spec_from_file_location("evaluate", os.path.join(ROOT, "harness", "evaluate.py"))
    ev = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ev)
    ev.PART_S = 20
    out = os.path.join(tmp, "result.json")
    a = SimpleNamespace(season=os.path.join(ROOT, "harness", "smoke.toml"), entry=entry, work=os.path.join(tmp, "work"),
                        out=out, parts=None, service=os.path.join(ROOT, "service", "target", "release", "rf-oracle"),
                        bench=os.path.join(ROOT, "service", "target", "release", "rf-bench"))
    res = ev.bench_job(a, {"status": "ok", "badge_dir": badge})
    why = " ".join(res.get("reasons", []))
    ok = res.get("benchmark") == "fail" and res.get("verdict") == "REJECT" and "PART_S" in why and "prover setup" in why
    print(("ok   " if ok else "FAIL ") + f"a part past PART_S during the prover's setup: {res.get('verdict')}: {why}")
    json.dump(res, open(out, "w"), indent=1)
    print(f"{0 if ok else 1} failure(s)")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
