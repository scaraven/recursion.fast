#!/usr/bin/env python3
"""measure-noise.py: repeat one timed process of the benchmark runner and report its spread
(harness/reference-machine.md, DESIGN §6.4, O-6). Each repetition is a fresh step directory with
copies of the inputs, the runner's sandbox and timer (harness/run-benchmark.py `Runner.run`).

  python3 -I harness/measure-noise.py --repeats 10 [--sandbox scripts/bwrap-landrun.sh] \\
      --input NAME=PATH ... -- CMD ARGS...

Prints one line per repetition and `median / min / max / (max - min) / median` in seconds; with
--json OUT also writes them. CMD runs in the step directory (inputs under their NAMEs)."""
import argparse, importlib.util, json, os, shutil, statistics, sys, tempfile

def runner_module():
    here = os.path.dirname(os.path.realpath(__file__))
    spec = importlib.util.spec_from_file_location("run_benchmark", os.path.join(here, "run-benchmark.py"))
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
    return m

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repeats", type=int, default=10)
    ap.add_argument("--sandbox")
    ap.add_argument("--input", action="append", default=[])
    ap.add_argument("--budget", type=float, default=600)
    ap.add_argument("--json")
    ap.add_argument("--label", default="")
    ap.add_argument("cmd", nargs="+")
    a = ap.parse_args()
    rb = runner_module()
    work = os.path.realpath(tempfile.mkdtemp(prefix="rf-noise-"))
    sandbox = a.sandbox and os.path.realpath(a.sandbox)        # steps run in their own directory
    cfg = {"sandbox": sandbox, "budgets": {"eval_s": 1e9, "mem_kb": 10 ** 12},
           "verify": [a.cmd[0]], "index": [a.cmd[0]], "prover": a.cmd}   # the argv's files readable
    secrets = os.path.join(work, ".none"); open(secrets, "w").close()
    R = rb.Runner(cfg, work, secrets, print)
    walls, rss = [], []
    try:
        for i in range(a.repeats):
            d = R.fresh("noise")
            for spec in a.input:
                name, _, path = spec.partition("=")
                shutil.copyfile(path, os.path.join(d, name))
            rc, wall, m = R.run(a.cmd, d, a.budget, f"repetition {i}")
            if rc != 0:
                raise SystemExit(f"measure-noise: repetition {i} exited {rc}")
            walls.append(wall); rss.append(m)
            print(f"{a.label} {i}: {wall:.4f} s, {m} KB")
    finally:
        shutil.rmtree(work, ignore_errors=True)
    med = statistics.median(walls)
    out = {"label": a.label, "repeats": a.repeats, "sandbox": bool(a.sandbox), "median_s": med, "min_s": min(walls),
           "max_s": max(walls), "spread": (max(walls) - min(walls)) / med, "walls_s": walls, "maxrss_kb": max(rss)}
    print(f"{a.label}: median {med:.4f} s, min {min(walls):.4f} s, max {max(walls):.4f} s, "
          f"(max - min) / median {out['spread']:.1%}, peak {max(rss)} KB")
    if a.json:
        json.dump(out, open(a.json, "w"), indent=1)

if __name__ == "__main__":
    sys.exit(main())
