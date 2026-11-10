#!/usr/bin/env python3
"""The end-to-end smoke (`harness/smoke.toml`: one IVC stream of M = 6 steps with the smoke's own fixed chain lengths
in [16, 128]).

  python3 tests/harness/smoke.py --org ORG [--work DIR] [--nanoda]     the whole evaluation
  python3 tests/harness/smoke.py --mock [--work DIR]                   the runner alone

With `--org` (ORG prepared by `harness/org-setup.sh`; the comparator from `scripts/tools.env`):
0. the witness-sending entry (`tests/harness/ws-entry/`: the library's submission, its claim) with
   the toy prover (`harness/toy-prover/honest/prover.s`, C compiled to x86-64 assembly) goes
   through `harness/evaluate.py cert` (source rule, comparator, gate, badge build) and must be
   certified;
1. `evaluate.py bench` of that entry through every part (the calibration, the stream with its
   interleaved samples, its statement canaries on π_1, π_2 and π_M and its re-timing, the score)
   with the compiled `accF` badge: verdict ACCEPT; then the organiser's canaries
   (`tests/harness/canaries.py`: the file parser, the trace digest and the signature check, core CI
   only) on the first and the last step's outputs through the same badge: the files
   accepted, every mutation rejected;
2. five deliberately broken provers, built from the same C source with one option each, through
   the stream with the same badge: a wrong chain end (`BROKEN_CHAIN`), an unsigned trace
   (`BROKEN_UNSIGNED`), a signature made by another run's service (`BROKEN_STALE`, the signature
   compiled into the binary): each REJECT, the first step's output rejected by `acc`; a query above
   the service's cap (`BROKEN_CAP`): REJECT naming the service's refusal; unbounded allocation
   under a 256 MiB cap (`BROKEN_OOM`): REJECT as killed out of memory;
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
    d = os.path.join(tmp, f"src-{flag}")
    os.makedirs(d)
    if extra_header:
        with open(os.path.join(d, "stale_sig.h"), "w") as f:
            f.write(extra_header)
    s, raw = os.path.join(d, "prover.s"), os.path.join(d, "raw.s")
    subprocess.run(["gcc", "-S", "-O2", f"-D{flag}", "-I", d, "-o", raw, os.path.join(TOY, "toy.c")], check=True)
    # as the committed honest prover: accepted by the reference image's binutils 2.42
    subprocess.run([sys.executable, "-I", os.path.join(ROOT, "harness", "tools", "asm-compat.py"), raw, s], check=True)
    return entry_from(s, os.path.join(tmp, f"entry-{flag}"))


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
    broken_entries = [(flag, broken(tmp, flag, hdr)) for flag, hdr in
                      (("BROKEN_CHAIN", None), ("BROKEN_UNSIGNED", None), ("BROKEN_STALE", header),
                       ("BROKEN_CAP", None), ("BROKEN_OOM", None))]
    # what each broken prover's rejection must say
    expect = {"BROKEN_CHAIN": "step 1 rejected by acc", "BROKEN_UNSIGNED": "step 1 rejected by acc",
              "BROKEN_STALE": "step 1 rejected by acc",
              "BROKEN_CAP": "refused (status 2): a query above 2^20 bytes",            # named
              # the cgroup kills it; under the prlimit fallback the allocation fails, exit 1
              "BROKEN_OOM": "killed: out of memory (cap 256M" if memcap_method() == "systemd" else "step1: exit 1"}
    lowmem = os.path.join(tmp, "smoke-256M.toml")    # the OOM prover runs under a 256 MiB cap
    open(lowmem, "w").write(open(os.path.join(ROOT, "harness", "smoke.toml")).read().replace('prover = "11G"', 'prover = "256M"'))
    season_of = lambda flag: lowmem if flag == "BROKEN_OOM" else os.path.join(ROOT, "harness", "smoke.toml")  # noqa: E731
    honest_s = os.path.join(TOY, "honest", "prover.s")

    if a.mock:
        badge = os.path.join(tmp, "badge")
        os.makedirs(badge)
        for f in os.listdir(os.path.join(HERE, "mock_badge")):
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
                  and m.get("runner_labels") == ["rf-bench"],
                  f"one evaluation: {load(out).get('verdict')}, the fingerprint's hash {m.get('fingerprint')} and host kernel "
                  f"recorded (no microcode), no CPU model or flags, the runner {m.get('runner_name')} {m.get('runner_labels')}")
            seasons = {}
            for name, want_fp in (("same", fp), ("other", "e" * 64)):
                seasons[name] = os.path.join(tmp, f"smoke-{name}.toml")
                open(seasons[name], "w").write(open(smoke).read().replace('fingerprint = "any"', f'fingerprint = "{want_fp}"'))
            for name, verdict in (("same", "ACCEPT"), ("other", "ERROR")):
                agg = os.path.join(tmp, f"single-{name}.json")
                subprocess.run([sys.executable, "-I", os.path.join(ROOT, "harness", "aggregate.py"), "--plan", "single",
                                "--season", seasons[name], "--cert", cj, "--out", agg, out], check=True, capture_output=True)
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
            check(sr.get("verdict") == "REJECT" and "source rule" in why, f"`#eval` in the entry: {sr.get('verdict')} {why[:120]}")
        step("source rule", source_rule)

    r = results.get("honest", {})
    # the aggregation of this evaluation's one part ACCEPTs (or matches the certificate),
    # and with the part dropped it is ERROR, never ACCEPT
    cert_file = cert if not a.mock else os.path.join(tmp, "cert-mock.json")
    if a.mock:
        json.dump({"status": "ok", "reasons": []}, open(cert_file, "w"))

    def aggregate_check():
        agg = lambda files, out: (subprocess.run([sys.executable, "-I", os.path.join(ROOT, "harness", "aggregate.py"),  # noqa: E731
                                                  "--plan", "single", "--season", os.path.join(ROOT, "harness", "smoke.toml"),
                                                  "--cert", cert_file, "--out", out, *files], check=True,
                                                 capture_output=True), load(out))[1]
        whole = agg([os.path.join(tmp, "result-honest.json")], os.path.join(tmp, "agg-whole.json"))
        dropped = agg([], os.path.join(tmp, "agg-dropped.json"))
        check(whole.get("verdict") == "ACCEPT" and dropped.get("verdict") == "ERROR" and not dropped.get("comparable"),
              f"aggregate: the planned part gives {whole.get('verdict')}; the part dropped gives {dropped.get('verdict')}")
        mine, agg_sc = r.get("score") or {}, whole.get("score") or {}
        check(all(k in mine and abs(agg_sc.get(k, -1) - mine[k]) <= 1e-12 * max(1.0, abs(mine[k])) for k in ("S", "S_product")),
              f"aggregate recomputes both scores as the runner did: S {agg_sc.get('S')} = {mine.get('S')}, "
              f"S× {agg_sc.get('S_product')} = {mine.get('S_product')}")
    step("aggregate", aggregate_check)
    if r.get("benchmark") == "pass":
        sc, st = r["score"], r["stream"]
        check(all(k in sc for k in ("S", "P_bar", "V_bar", "S_product", "g", "V_mean_s", "x_bar", "pi_mean_bytes", "c_P",
                                    "v_ref_ns", "M", "marginal", "fit"))
              and sc.get("tracks") == {"sum": "S", "product": "S_product"} and sc["M"] == st["M"]
              and not st["truncated"],
              f"score components: S {sc.get('S')}, P̄ {sc.get('P_bar')}, V̄ {sc.get('V_bar')}, S× {sc.get('S_product')}, "
              f"g {sc.get('g')}, M {sc.get('M')} of {st.get('M_drawn')}")
        smoke_stream = tomllib.load(open(os.path.join(ROOT, "harness", "smoke.toml"), "rb"))["stream"]
        fixed = smoke_stream["lengths"]
        check(st["M_drawn"] == smoke_stream["M"] and len(fixed) == smoke_stream["M"] + 1 and st["lengths"] == fixed,
              f"the stream ran the smoke's M = {smoke_stream['M']} steps over its fixed list of M + 1 = {len(fixed)} "
              f"lengths: {st['lengths']}")
        check(all(all(k in s for k in ("P_s", "V_ns", "pi_bytes", "x", "startup_s", "kill_s")) for s in st["steps"]),
              f"every step records P, V, |π|, x, start-up and kill latency: {sorted(st['steps'][0])}")
        check(st["canaries"] >= 4, f"statement canaries on π_1, π_2, π_M rejected: {st['canaries']}")
        check("retime" in st and len(st["calibration"]["samples"]) >= 2,
              f"re-timing ran ({st.get('retime', {}).get('rerun')}) and calibration was sampled "
              f"{len(st['calibration']['samples'])} times")
    for flag, _ in broken_entries:
        rb = results.get(flag, {})
        why = " ".join(rb.get("reasons", []))
        check(rb.get("benchmark") == "fail" and rb.get("verdict", "REJECT") == "REJECT" and expect[flag] in why,
              f"{flag}: {rb.get('verdict', rb.get('benchmark'))}: {why[:400]}")
    print(f"\n{len(fails)} failure(s); results in {tmp}")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
