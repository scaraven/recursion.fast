#!/usr/bin/env python3
"""The end-to-end smoke (`harness/smoke.toml`: one IVC stream of M = 4 steps of one leaf of 6 blocks, its service
run and its three timed passes; the season's size caps and size_ref, its own verifier and time caps).

  python3 tests/harness/smoke.py --org ORG [--work DIR] [--nanoda]     the whole evaluation
  python3 tests/harness/smoke.py --mock [--work DIR]                   the runner alone

With `--org` (ORG prepared by `harness/org-setup.sh`; the comparator from `scripts/tools.env`):
0. the witness-sending entry (`tests/harness/ws-entry/`: the library's submission, its claim) with
   the toy prover (`harness/toy-prover/honest/prover.s`, C compiled to x86-64 assembly) goes
   through `harness/evaluate.py cert` (source rule, comparator, gate, badge build) and must be
   certified;
1. `evaluate.py bench` of that entry through every part (the calibration, the stream: its service run
   with its interleaved samples, its checks (each checked proof judged in three fresh badge runs, the
   median counting) and its statement canaries on π_1, π_2 and π_M, then three timed passes against
   the service's replay mode, every output byte-identical; the score, the median pass) with the
   compiled `accF` badge: verdict ACCEPT in both tracks (`S` and `S_every`) under the smoke's
   `v_cap_ms = 128` (an exception to the season's caps, whose `v_cap_ms` is 64; `badge_start_s` and the
   certificate's `build_s` are the others), and REJECT
   under `v_cap_ms = 8`, below the toy's final verifier time (it grows with the stream's history),
   the final output's V above the cap; then the organiser's canaries
   (`tests/harness/canaries.py`: the file parser, the trace digest and the signature check, core CI
   only) on the first and the last step's outputs through the same badge: the files
   accepted, every mutation rejected;
2. seven deliberately broken provers, built from the same C source with one option each, through
   the stream with the same badge: a leaf of other data (`BROKEN_LEAF`, one bit flipped), an unsigned trace
   (`BROKEN_UNSIGNED`), a signature made by another run's service (`BROKEN_STALE`, the signature
   compiled into the binary): each REJECT, the final output rejected by `acc`; a query above
   the service's cap (`BROKEN_CAP`): REJECT naming the service's refusal; unbounded allocation
   under a 256 MiB cap (`BROKEN_OOM`): REJECT as killed out of memory; an output that changes in
   the timed passes (`BROKEN_NONDET`): REJECT naming the first differing byte; a SIGN that differs
   in the timed passes (`BROKEN_PROBE`, a replay MISMATCH read as a bit): REJECT; and one variant
   that is not broken, intermediate outputs that are not signed proofs (`FINAL_ONLY=4`): ACCEPT in
   the track `final` only, the reason recorded; each REJECT names its `reject_stage` (`check` for
   the final output rejected and for the verifier cap, `request` for the service's cap and the
   memory cap, `timed-pass` for the byte and replay mismatches, `certificate` for the source rule);
3. the same entry with `certified := sorry`: PROVISIONAL, not comparable;
4. an entry with `#eval` in its Lean source: REJECT by the source rule, nothing built;
5. the entry's module that `Solution` does not import is never built, and a Lean-kernel run
   over a 400 MiB budget is its own outcome, PROVISIONAL, not a failed certificate.
With `--mock`: steps 1 and 2 with the Python stand-in badge (`tests/harness/mock_badge/`), which
tests the runner without Lean, and 6. one evaluation through `evaluate.py bench` and
`aggregate.py` with a machine fingerprint file (`RF_MACHINE_FINGERPRINT`, AGENTS.md §6): ACCEPT, the
fingerprint's hash recorded and no CPU model or flags; comparable under a season naming that hash,
an organiser ERROR under one naming another, which also stops `run-benchmark.py` before the
prover's build.
"""
import argparse
import json
import re
import os
import shutil
import subprocess
import sys
import tempfile
import tomllib

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "harness"))
sys.path.insert(0, HERE)
from rfh.checks import Badge  # noqa: E402
from rfh.bench import fingerprint  # noqa: E402
from rfh.sandbox import memcap_method  # noqa: E402
from rfh.service import Client, Service  # noqa: E402
from canaries import organiser_canaries  # noqa: E402

SERVICE = os.path.join(ROOT, "service", "target", "release", "rf-oracle")
BENCH = os.path.join(ROOT, "service", "target", "release", "rf-bench")
TOY = os.path.join(ROOT, "harness", "toy-prover")


def run_bench(entry, badge, work, out, parts=None, season=None):
    cmd = [sys.executable, "-I", os.path.join(ROOT, "harness", "run-benchmark.py"), "--season",
           season or os.path.join(ROOT, "harness", "smoke.toml"), "--entry", entry, "--badge", badge, "--service", SERVICE,
           "--bench", BENCH, "--work", work, "--out", out]
    if parts:
        cmd += ["--parts", parts]
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=3600)
    print(p.stdout[-3000:], p.stderr[-2000:], sep="\n", flush=True)
    return load(out)


def entry_from(src_s, d):
    os.makedirs(os.path.join(d, "prover"))
    shutil.copy(src_s, os.path.join(d, "prover", "prover.s"))
    return d


def broken(tmp, flag, extra_header=None):
    """An entry of the toy prover built with `-D{flag}` (`NAME` or `NAME=VALUE`)."""
    name = flag.split("=")[0]
    d = os.path.join(tmp, f"src-{name}")
    os.makedirs(d)
    if extra_header:
        with open(os.path.join(d, "stale_sig.h"), "w") as f:
            f.write(extra_header)
    s, raw = os.path.join(d, "prover.s"), os.path.join(d, "raw.s")
    subprocess.run(["gcc", "-S", "-O2", f"-D{flag}", "-I", d, "-o", raw, os.path.join(TOY, "toy.c")], check=True)
    # as the committed honest prover: accepted by the reference image's binutils 2.42
    subprocess.run([sys.executable, "-I", os.path.join(ROOT, "harness", "tools", "asm-compat.py"), raw, s], check=True)
    return entry_from(s, os.path.join(tmp, f"entry-{name}"))


def load(path):
    """A JSON result, or {} if it is missing or unreadable (the check that reads it then fails)."""
    try:
        return json.load(open(path))
    except (OSError, ValueError):
        return {}


def evaluate(*args, env=None):
    p = subprocess.run([sys.executable, "-I", os.path.join(ROOT, "harness", "evaluate.py"), *args],
                       capture_output=True, text=True, timeout=7200, env=env)
    print(p.stdout[-2500:], p.stderr[-1500:], sep="\n", flush=True)


def ws_entry(tmp, name, prover_s, solution_patch=None):
    d = os.path.join(tmp, name)
    shutil.copytree(os.path.join(HERE, "ws-entry"), d)
    os.makedirs(os.path.join(d, "prover"))
    shutil.copy(prover_s, os.path.join(d, "prover", "prover.s"))
    if solution_patch:
        sol = os.path.join(d, "lean", "Solution.lean")
        src = open(sol).read()
        for old, new in solution_patch:
            assert old in src
            src = src.replace(old, new)
        open(sol, "w").write(src)
    return d


def organiser_check(badge_dir, work, r):
    """The organiser's canaries (core CI only) on the honest run's first and last stream
    outputs, through the entry's compiled badge: (number of mutations, the answers that were wrong);
    each file must be accepted and each mutation rejected."""
    store = os.path.join(work, "store")
    os.makedirs(os.path.join(store, "organiser-canaries"))
    badge = Badge(badge_dir, "4G", os.path.join(work, "organiser-canaries-scratch"))
    os.makedirs(badge.scratch)
    st = r["stream"]
    vk = bytes.fromhex(st["vk"])
    targets = [(vk, bytes.fromhex(st["statements"][0]), st["steps"][0]["file"]),
               (vk, bytes.fromhex(st["last_stmt"]), st["last_file"])]
    items, want = [], []
    for vk, c, rel in targets:
        items.append((vk, c, rel))
        want.append((rel, True))
        for name, data in organiser_canaries(open(os.path.join(store, rel), "rb").read()):
            m = f"organiser-canaries/{rel.replace('/', '_')}.{name}"
            open(os.path.join(store, m), "wb").write(data)
            items.append((vk, c, m))
            want.append((f"{rel} {name}", False))
    res = badge.verify(items, store, timeout=60 * len(items) + 60)
    return len(items) - len(targets), [what for (what, ok), (got, _) in zip(want, res) if got != ok]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--org", default=None)
    ap.add_argument("--work", default=None)
    ap.add_argument("--mock", action="store_true")
    ap.add_argument("--nanoda", action="store_true")
    a = ap.parse_args()
    if memcap_method() == "prlimit":
        # the test-only override: without a systemd user manager a benchmark is an organiser ERROR
        # (`run-benchmark.py`); the smoke still runs every path under the fallback, recorded
        os.environ["RF_ALLOW_PRLIMIT"] = "1"
        print("memory caps: the prlimit fallback (RF_ALLOW_PRLIMIT=1 for this smoke)", flush=True)
    if a.mock:
        # the Python stand-in badge needs the host's Python library: its sandbox binds the host's
        # /usr (test-only, refused without RF_TEST_OVERRIDES=1; the real badge gets a tmpfs tree of
        # what it loads, `rfh.checks.lib_view`)
        os.environ["RF_TEST_BADGE_HOST_ROOT"] = "1"
        os.environ["RF_TEST_OVERRIDES"] = "1"
    # a part run under a test-only override is an organiser ERROR in the aggregation unless the
    # tests' flag says otherwise (it records them; the workflow never passes it)
    agg_test = ["--allow-test-overrides"] if a.mock or memcap_method() == "prlimit" else []
    tmp = a.work or tempfile.mkdtemp(prefix="rf-smoke-", dir=os.environ.get("RF_TEST_TMP"))
    os.makedirs(tmp, exist_ok=True)
    fails = []

    def check(cond, what):
        print(("ok   " if cond else "FAIL ") + what, flush=True)
        if not cond:
            fails.append(what)

    def step(name, fn):
        """Run one step; a crash is a failed check, and the smoke continues."""
        try:
            fn()
        except Exception as e:  # noqa: BLE001
            check(False, f"{name}: crashed: {e!r}")

    # a signature of the empty trace from another service (another run's key)
    other = Service(SERVICE, os.path.join(tmp, "other-service")).start()
    c = Client(other.socket_path)
    body = c.sign([])
    c.close()
    other.stop()
    header = "static const unsigned char stale_sig[4772] = {" + ",".join(str(b) for b in body) + "};\n"
    smoke_M = tomllib.load(open(os.path.join(ROOT, "harness", "smoke.toml"), "rb"))["stream"]["M"]
    broken_entries = [(flag.split("=")[0], broken(tmp, flag, hdr)) for flag, hdr in
                      (("BROKEN_LEAF", None), ("BROKEN_UNSIGNED", None), ("BROKEN_STALE", header),
                       ("BROKEN_CAP", None), ("BROKEN_OOM", None), ("BROKEN_NONDET", None), ("BROKEN_PROBE", None),
                       (f"FINAL_ONLY={smoke_M}", None))]
    # what each broken prover's rejection must say (FINAL_ONLY is not broken: its check is below)
    final_rejected = f"the final output (step {smoke_M}) is rejected by acc"
    expect = {"BROKEN_LEAF": final_rejected, "BROKEN_UNSIGNED": final_rejected, "BROKEN_STALE": final_rejected,
              "BROKEN_CAP": "refused (status 2): a query above 2^20 bytes",            # named
              # the cgroup kills it; under the prlimit fallback the allocation fails, exit 1
              # (`oom_label`: "killed: out of memory (cap 256M, …" once the scope's memory events or its
              # peak show the cap's OOM, else "killed by the OOM killer (cap 256M, …")
              "BROKEN_OOM": "(cap 256M" if memcap_method() == "systemd" else "service1: exit 1",
              "BROKEN_NONDET": "timed pass 1, step 1: the output differs from the service run's output of the step, "
                               "first at byte offset",
              "BROKEN_PROBE": "timed pass 1: a SIGN in a timed pass differed from the service run's"}
    # where each is rejected (the result's `reject_stage`)
    expect_stage = {"BROKEN_LEAF": "check", "BROKEN_UNSIGNED": "check", "BROKEN_STALE": "check", "BROKEN_CAP": "request",
                    "BROKEN_OOM": "request", "BROKEN_NONDET": "timed-pass", "BROKEN_PROBE": "timed-pass"}
    lowmem = os.path.join(tmp, "smoke-256M.toml")    # the OOM prover runs under a 256 MiB cap
    smoke_text = open(os.path.join(ROOT, "harness", "smoke.toml")).read()
    assert 'prover = "8G"' in smoke_text
    open(lowmem, "w").write(smoke_text.replace('prover = "8G"', 'prover = "256M"'))
    season_of = lambda flag: lowmem if flag == "BROKEN_OOM" else os.path.join(ROOT, "harness", "smoke.toml")  # noqa: E731
    honest_s = os.path.join(TOY, "honest", "prover.s")

    if a.mock:
        badge = os.path.join(tmp, "badge")
        os.makedirs(badge)
        for f in sorted(x for x in os.listdir(os.path.join(HERE, "mock_badge")) if os.path.isfile(os.path.join(HERE, "mock_badge", x))):
            shutil.copy(os.path.join(HERE, "mock_badge", f), badge)
        shutil.copy(os.path.join(ROOT, "tests", "service", "wots_ref.py"), badge)
        shutil.copy(os.path.join(ROOT, "harness", "rfh", "signed.py"), badge)
        shutil.copy(os.path.join(ROOT, "tests", "service", "keccak_ref.c"), badge)
        os.makedirs(os.path.join(badge, "rfh"))                # wots_ref's `from rfh import keccak`
        shutil.copy(os.path.join(ROOT, "harness", "rfh", "keccak.py"), os.path.join(badge, "rfh"))
        honest = entry_from(honest_s, os.path.join(tmp, "entry-honest"))
        r = run_bench(honest, badge, os.path.join(tmp, "work-honest"), os.path.join(tmp, "result-honest.json"))
        check(r["benchmark"] == "pass", f"honest toy prover: {r['benchmark']} {r['reasons']}")
        results = {"honest": r}
        for flag, e in broken_entries:
            results[flag] = run_bench(e, badge, os.path.join(tmp, f"work-{flag}"), os.path.join(tmp, f"result-{flag}.json"),
                                      "calibrate,stream", season_of(flag))

        def single():
            """6. one evaluation, its part aggregated, with a machine fingerprint (AGENTS.md §6)."""
            smoke = os.path.join(ROOT, "harness", "smoke.toml")
            cj = os.path.join(tmp, "cert-single.json")
            json.dump({"status": "ok", "reasons": [], "badge_dir": badge}, open(cj, "w"))
            fpf = os.path.join(tmp, "fingerprint.json")
            json.dump({"cpu_model": "smoke", "vm_shape": {"vcpus": 4, "memory": "16G"}, "frequency_policy": "smoke",
                       "image_id": "smoke", "host_kernel": "smoke-kernel", "microcode": "0x0"}, open(fpf, "w"))
            fp = fingerprint(fpf)["hash"]
            env = dict(os.environ, RF_MACHINE_FINGERPRINT=fpf, RUNNER_NAME="rf-bench-smoke",
                       RF_RUNNER_ENVIRONMENT="self-hosted", RF_RUNNER_LABELS="rf-bench")
            out = os.path.join(tmp, "single-part.json")
            evaluate("bench", "--entry", honest, "--cert", cj, "--work", os.path.join(tmp, "work-single"), "--out", out,
                     "--season", smoke, env=env)
            m = load(out).get("machine") or {}
            check(load(out).get("verdict") == "ACCEPT" and m.get("fingerprint") == fp and len(fp or "") == 64
                  and "cpu_model" not in m and "simd" not in m and "microcode" not in m and m.get("host_kernel") == "smoke-kernel"
                  and m.get("runner_labels") == ["rf-bench"] and "ksm_run" in m and "thp_shmem_enabled" in m,
                  f"one evaluation: {load(out).get('verdict')}, the fingerprint's hash {m.get('fingerprint')} and host kernel "
                  f"recorded (no microcode), no CPU model or flags, the runner {m.get('runner_name')} {m.get('runner_labels')}")
            seasons = {}
            for name, want_fp in (("same", fp), ("other", "e" * 64)):
                seasons[name] = os.path.join(tmp, f"smoke-{name}.toml")
                open(seasons[name], "w").write(open(smoke).read().replace('fingerprint = "any"', f'fingerprint = "{want_fp}"'))
            for name, verdict in (("same", "ACCEPT"), ("other", "ERROR")):
                agg = os.path.join(tmp, f"single-{name}.json")
                subprocess.run([sys.executable, "-I", os.path.join(ROOT, "harness", "aggregate.py"), "--plan", "single",
                                "--season", seasons[name], "--cert", cj, "--out", agg, *agg_test, out], check=True,
                               capture_output=True)
                g = load(agg)
                check(g.get("verdict") == verdict and g.get("comparable") is (verdict == "ACCEPT")
                      and (g.get("runner") or {}).get("name") == "rf-bench-smoke"
                      and (verdict == "ACCEPT" or any("fingerprint is mismatched" in r for r in g.get("reasons", []))),
                      f"aggregated under a season naming the {name} fingerprint: {g.get('verdict')}, comparable "
                      f"{g.get('comparable')}, {(g.get('reasons') or [''])[-1][:90]}")
            early = os.path.join(tmp, "single-early.json")
            evaluate("bench", "--entry", honest, "--cert", cj, "--work", os.path.join(tmp, "work-early"), "--out", early,
                     "--season", seasons["other"], env=env)
            e = load(early)
            check(e.get("benchmark") == "error" and "prover" not in e and any("fingerprint is mismatched" in r for r in e.get("reasons", [])),
                  f"on another machine the run stops before the prover's build, an organiser ERROR: {e.get('benchmark')}, "
                  f"{(e.get('reasons') or [''])[0][:90]}")
        step("one evaluation with a machine fingerprint", single)
    else:
        if not a.org:
            raise SystemExit("smoke: --org ORG or --mock")
        entry = ws_entry(tmp, "entry-ws", honest_s)
        cert = os.path.join(tmp, "cert.json")
        results = {}
        try:
            evaluate("cert", "--entry", entry, "--org", a.org, "--work", os.path.join(tmp, "cert"), "--out", cert,
                     *(["--nanoda"] if a.nanoda else []))
        except Exception as e:  # noqa: BLE001 (every step reports and the smoke continues)
            print(f"evaluate cert crashed: {e!r}")
        cj = load(cert)
        check(cj.get("status") == "ok", f"witness-sending entry certified: {cj.get('status')} {cj.get('reasons')} "
                                        f"kernels {cj.get('kernels')}")
        check("Solution" in (cj.get("built_modules") or []) and "RfSmokeUnused" not in (cj.get("built_modules") or []),
              f"an entry module Solution does not import is never built: built {cj.get('built_modules')}")
        steps_s = {k: cj.get(k) for k in ("build_s", "comparator_s", "gate_s", "badge_s")}
        lean_peak = ((cj.get("kernel_runs") or {}).get("lean") or {}).get("peak_bytes")
        check(all(isinstance(v, (int, float)) for v in steps_s.values())
              and (memcap_method() != "systemd" or cj.get("status") != "ok" or bool(lean_peak)),
              f"cert.json records each capped step's seconds {steps_s} and the Lean kernel's peak {lean_peak} B")
        if cj.get("status") in ("ok", "provisional"):
            out = os.path.join(tmp, "result-honest.json")
            step("honest benchmark", lambda: evaluate("bench", "--entry", entry, "--cert", cert, "--work",
                                                      os.path.join(tmp, "work-honest"), "--out", out,
                                                      "--season", os.path.join(ROOT, "harness", "smoke.toml")))
            r = load(out)
            check(r.get("verdict") == "ACCEPT", f"honest toy prover with the compiled accF badge: {r.get('verdict')} {r.get('reasons')}")
            results["honest"] = r
            def vcap():      # a verifier cap below the toy's final check (about 64 ms): REJECT
                vc = os.path.join(tmp, "smoke-vcap.toml")
                text = open(os.path.join(ROOT, "harness", "smoke.toml")).read()
                new = re.sub(r"(?m)^v_cap_ms = \d+ ", "v_cap_ms = 8 ", text, count=1)
                assert new != text
                open(vc, "w").write(new)
                out = os.path.join(tmp, "result-vcap.json")
                evaluate("bench", "--entry", entry, "--cert", cert, "--work", os.path.join(tmp, "work-vcap"), "--out", out,
                         "--season", vc, "--parts", "calibrate,stream")
                rv = load(out)
                why = " ".join(rv.get("reasons", []))
                check(rv.get("verdict") == "REJECT" and "above v_cap = 8 ms" in why and "the final output" in why
                      and rv.get("reject_stage") == "check",
                      f"the honest toy under v_cap = 8 ms (below its final V): {rv.get('verdict')} at "
                      f"{rv.get('reject_stage')}: {why[:200]}")
            step("the season's verifier cap", vcap)

            def organiser():
                n, wrong = organiser_check(cj["badge_dir"], os.path.join(tmp, "work-honest"), r)
                check(n > 0 and not wrong, f"organiser canaries (core CI only): {n} mutations of π_1 and π_M "
                                           f"rejected, both files accepted; wrong answers: {wrong}")
            if r.get("verdict") == "ACCEPT":
                step("organiser canaries", organiser)
            for flag, e in broken_entries:
                out = os.path.join(tmp, f"result-{flag}.json")
                step(flag, lambda e=e, flag=flag, out=out: evaluate(
                    "bench", "--entry", e, "--cert", cert, "--work", os.path.join(tmp, f"work-{flag}"), "--out", out,
                    "--season", season_of(flag), "--parts", "calibrate,stream"))
                results[flag] = load(out)
        else:
            check(False, f"the benchmarks need a certified entry; skipped (certificate {cj.get('status')})")

        def over_budget():   # a kernel over its memory budget is its own outcome, never a failed certificate
            oc = os.path.join(tmp, "cert-overbudget.json")
            evaluate("cert", "--entry", entry, "--org", a.org, "--work", os.path.join(tmp, "cert-overbudget"), "--out", oc,
                     "--cert-mem", "400M")
            ob = load(oc)
            if memcap_method() == "systemd":
                check(ob.get("status") == "provisional" and any("over its memory budget" in x for x in ob.get("provisional_reasons", []))
                      and (ob.get("kernel_runs") or {}).get("lean", {}).get("outcome") == "over budget",
                      f"the Lean kernel over a 400M budget: {ob.get('status')}, {ob.get('provisional_reasons')}")
            else:      # an address-space limit cannot tell a kernel over budget from a failure
                check(ob.get("status") not in ("ok", None), f"the Lean kernel over a 400M address-space limit is not certified: {ob.get('status')}")
        step("kernel over budget", over_budget)

        def provisional():   # 3. the same entry, its certificate left open
            pe = ws_entry(tmp, "entry-provisional", honest_s, [(
                "theorem certified : CertificateR declared submission :=\n", "theorem certified : CertificateR declared submission := by\n  sorry\n\nexample : CertificateR declared submission :=\n")])
            pc = os.path.join(tmp, "cert-provisional.json")
            evaluate("all", "--entry", pe, "--org", a.org, "--work", os.path.join(tmp, "provisional"), "--out", pc,
                     "--season", os.path.join(ROOT, "harness", "smoke.toml"), "--parts", "calibrate,stream")
            pr = load(pc)
            check(pr.get("verdict") == "PROVISIONAL" and pr.get("comparable") is False,
                  f"an open certificate is PROVISIONAL and not comparable: {pr.get('verdict')} "
                  f"{(pr.get('certificate') or {}).get('provisional_reasons')}")
        step("provisional", provisional)

        def source_rule():   # 4. the source rule
            se = ws_entry(tmp, "entry-eval", honest_s, [("end RecursionFast.Challenge", "#eval 1\n\nend RecursionFast.Challenge")])
            sc = os.path.join(tmp, "cert-eval.json")
            evaluate("all", "--entry", se, "--org", a.org, "--work", os.path.join(tmp, "eval"), "--out", sc)
            sr = load(sc)
            why = " ".join((sr.get("certificate") or {}).get("reasons", []))
            check(sr.get("verdict") == "REJECT" and "source rule" in why and sr.get("reject_stage") == "certificate",
                  f"`#eval` in the entry: {sr.get('verdict')} at {sr.get('reject_stage')} {why[:120]}")
        step("source rule", source_rule)

    r = results.get("honest", {})
    # the aggregation of this evaluation's one part ACCEPTs (or matches the certificate),
    # and with the part dropped it is ERROR, never ACCEPT
    cert_file = cert if not a.mock else os.path.join(tmp, "cert-mock.json")
    if a.mock:
        json.dump({"status": "ok", "reasons": []}, open(cert_file, "w"))

    def aggregate_check():
        agg = lambda files, out, flag=agg_test: (subprocess.run(  # noqa: E731
            [sys.executable, "-I", os.path.join(ROOT, "harness", "aggregate.py"), "--plan", "single", "--season",
             os.path.join(ROOT, "harness", "smoke.toml"), "--cert", cert_file, "--out", out, *flag, *files], check=True,
            capture_output=True), load(out))[1]
        whole = agg([os.path.join(tmp, "result-honest.json")], os.path.join(tmp, "agg-whole.json"))
        if agg_test:            # the same part without the tests' flag: an organiser ERROR (review LR5 L2)
            strict = agg([os.path.join(tmp, "result-honest.json")], os.path.join(tmp, "agg-strict.json"), [])
            check(strict.get("verdict") == "ERROR" and strict.get("organiser_error") == "fingerprint"
                  and whole.get("test_overrides"),
                  f"aggregate: a part run under test-only overrides {whole.get('test_overrides')} is an organiser ERROR "
                  f"without --allow-test-overrides: {strict.get('verdict')} ({strict.get('organiser_error')})")
        dropped = agg([], os.path.join(tmp, "agg-dropped.json"))
        check(whole.get("verdict") == "ACCEPT" and dropped.get("verdict") == "ERROR" and not dropped.get("comparable"),
              f"aggregate: the planned part gives {whole.get('verdict')}; the part dropped gives {dropped.get('verdict')}")
        mine, agg_sc = r.get("score") or {}, whole.get("score") or {}
        check("S" in mine and "S_every" in mine and agg_sc.get("S") == mine["S"] and agg_sc.get("S_every") == mine["S_every"]
              and agg_sc.get("tracks") == mine.get("tracks") and agg_sc.get("median_pass") == mine.get("median_pass"),
              f"aggregate recomputes the scores and the tracks exactly as the runner did: S {agg_sc.get('S')} = {mine.get('S')}, "
              f"S_every {agg_sc.get('S_every')} = {mine.get('S_every')}, tracks {agg_sc.get('tracks')}")
    step("aggregate", aggregate_check)
    if r.get("benchmark") == "pass":
        sc, st = r["score"], r["stream"]
        smoke_stream = tomllib.load(open(os.path.join(ROOT, "harness", "smoke.toml"), "rb"))["stream"]
        check(all(k in sc for k in ("S", "S_every", "P_total_s", "size_factor", "size_factor_every", "final_pi_bytes",
                                    "max_pi_bytes", "pass_totals_s", "median_pass", "tracks", "c_P", "M"))
              and sc.get("tracks") == {"final": "S", "every": "S_every"} and "tracks_reason" not in sc
              and len(sc["pass_totals_s"]) == smoke_stream["timed_runs"] == 3
              and sc["P_total_s"] == sorted(sc["pass_totals_s"])[1] == sc["pass_totals_s"][sc["median_pass"] - 1]
              and sc["max_pi_bytes"] == max(s["pi_bytes"] for s in st["steps"])
              and sc["M"] == st["M"] == smoke_stream["M"] and not st["truncated"],
              f"score components: S {sc.get('S')}, S_every {sc.get('S_every')}, P_total {sc.get('P_total_s')} s (the median of "
              f"{sc.get('pass_totals_s')}, pass {sc.get('median_pass')}), size factors {sc.get('size_factor')} at |π_M| "
              f"{sc.get('final_pi_bytes')} B and {sc.get('size_factor_every')} at max |π_i| {sc.get('max_pi_bytes')} B, "
              f"tracks {sc.get('tracks')}, M {sc.get('M')}")
        check(st["shape"] == {k: smoke_stream[k] for k in ("M", "n")} and len(set(st["seeds"])) == smoke_stream["M"]
              and st.get("leaf_data") == {"xof": "shake256", "domain": "recursion.fast/leaf-data/v1"},
              f"the stream ran the smoke's shape {st['shape']} with M fresh seeds, their expansion published")
        check(all(all(k in s for k in ("P_s", "P_service_s", "P_timed_s", "V_ns", "V_runs_ns", "pi_bytes", "accepted",
                                       "startup_s", "kill_s"))
                  and len(s["P_timed_s"]) == smoke_stream["timed_runs"] and s["P_s"] == s["P_timed_s"][sc["median_pass"] - 1]
                  and len(s["V_runs_ns"]) == 3 and s["V_ns"] == sorted(s["V_runs_ns"])[1] and s["accepted"]
                  for s in st["steps"]),
              f"every step records its service-run time, its timed times (P = its time in the median pass), its three "
              f"judged V times (V = their median), |π|, acceptance, start-up and kill latency: {sorted(st['steps'][0])}")
        check(st["canaries"] >= 5 and len(st["calibration"]["samples"]) >= 2 + smoke_stream["timed_runs"],
              f"statement canaries on π_1, π_2, π_M rejected ({st['canaries']}); calibration sampled "
              f"{len(st['calibration']['samples'])} times")
    fo = results.get("FINAL_ONLY", {})
    fsc = fo.get("score") or {}
    check(fo.get("benchmark") == "pass" and fo.get("verdict", "ACCEPT") == "ACCEPT" and fsc.get("tracks") == {"final": "S"}
          and "output 1 rejected by acc" in (fsc.get("tracks_reason") or {}).get("every", ""),
          f"FINAL_ONLY: intermediate outputs that are not proofs: {fo.get('verdict', fo.get('benchmark'))}, tracks "
          f"{fsc.get('tracks')}, {(fsc.get('tracks_reason') or {}).get('every', '')[:200]} {fo.get('reasons')}")
    for flag, _ in broken_entries:
        if flag not in expect:
            continue
        rb = results.get(flag, {})
        why = " ".join(rb.get("reasons", []))
        check(rb.get("benchmark") == "fail" and rb.get("verdict", "REJECT") == "REJECT" and expect[flag] in why
              and rb.get("reject_stage") == expect_stage[flag],
              f"{flag}: {rb.get('verdict', rb.get('benchmark'))} at {rb.get('reject_stage')}: {why[:400]}")
    print(f"\n{len(fails)} failure(s); results in {tmp}")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
